# Memory safety of the base64 encoders and decoders

This Lean 4 development proves that no access of the base64 code in
`ext/standard/base64.c` leaves its buffer, on any input, and that the bounds
it proves are the best possible. It covers:

- the decoder template `PHP_BASE64_DECODE_SIMD` for SSSE3, AVX2,
  AVX-512 VBMI and NEON, in strict and non-strict mode, including the
  hand-over to the scalar decoder (`php_base64_decode_resume`);
- every encoder: scalar, NEON, SSSE3, AVX2, AVX-512 and AVX-512 VBMI;
- stores and loads: the output, the decoder's stack buffers, and the input.

```sh
source "$HOME/.elan/env"
cd formal/base64_safety
lake build
```

`lean-toolchain` pins Lean 4.35. There is no mathlib, no `sorry` and no
`native_decide`; the witnesses use `decide`, checked by the kernel. The
theorems use only the axioms `propext`, `Quot.sound` and `Classical.choice`.
About 1300 lines; a clean build takes 3 seconds on an Apple M4 Max.

## Files

| file | content |
|---|---|
| `Base64Safety/Basic.lean` | accesses, `php_base64_copy_short`, the scalar decoder (`php_base64_decode_put`) |
| `Base64Safety/Decode.lean` | the helpers of each instruction set, the decoder, `decode_tight`, `decode_ok` |
| `Base64Safety/Encode.lean` | the encoders, with their loop tests as parameters, and their theorems |
| `Base64Safety/Tight.lean` | witnesses: every bound is reached, and every encoder loop test is the least that works |

## Model

An **access** reads or writes `len` bytes at offset `off` of a buffer: `out`
(the result's characters), `pending` (the decoder's array of pending values),
`last` (the decoder's 64-byte tail) or `input`. A vector store writes the
vector's full width, whatever its lanes hold. A masked AVX-512 load or store
touches the bytes its mask selects, because the other bytes do not fault. A
`memcpy` or `memset` of `n` bytes is one access of `n` bytes.

**Buffer sizes.**

| buffer | size | source |
|---|---|---|
| decoder `out` | `n + 1` | `zend_string_alloc(n, 0)`: `_ZSTR_STRUCT_SIZE(len)` is `header + len + 1` |
| encoder `out` | `4 * ⌈n / 3⌉ + 1` | `zend_string_safe_alloc((n + 2) / 3, 4, 0, 0)` |
| `pending` | 640 | `php_base64_<isa>_block pending[512 / 64 + 2]` |
| `last` | 64 | `unsigned char last[64]` |
| input | `n` | |

**Decoder input.** The block loops advance by 64 bytes, so they see `⌊n / 64⌋`
blocks followed by a tail of `t = n % 64` bytes. A block is reduced to the
number of alphabet characters in each of its 16-byte quarters. That number
fixes every store offset in the helpers: `compress` stores each quarter at
"values kept so far", and AVX2 stores its second half at
`16 - popcount(bad & 0xffff)`. A block also carries `esc`, an arbitrary
boolean that stands for "strict mode, and a byte that is neither alphabet nor
whitespace", which triggers `php_base64_decode_resume`. The input also leaves
free how many 16-byte `step16` decodes the tail gets, and how many alphabet
characters the scalar loop sees. Each is capped only by the bytes the code
reads. The theorems hold for every choice. A failing run (`goto fail`, or
`php_base64_decode_loop` returning 0) only stops early, so its accesses are a
prefix of those of a run that does not fail.

**Helpers** (`Isa`), relative to their destination pointer:

| | `pack` | `compress` | `step16` | slack |
|---|---|---|---|---|
| SSSE3 | 16 at 0, 12, 24, 36 | 16 at 0, `q0`, `q0+q1`, `q0+q1+q2` (single bad byte: at `16i - (j < i)`) | 16 | 4 |
| AVX2 | 32 at 0, 24 | per half: 32, or 16 at 0 and 16 at `q`; single bad byte as SSSE3 | 16 | 8 |
| AVX-512 VBMI | 64 | 64 | 16 | 16 |
| NEON | 48 (`vst3q_u8`) | as SSSE3 | 16 | 4 |

The slack is how far `pack` writes past the 48 bytes it decodes, or 4 (the
overhang of `step16`), whichever is larger.

## Theorems

- `decode_tight`: every access of the decoder ends within
  `min(n + 1, ⌊3n/4⌋ + slack)` bytes of `out`, 638 bytes of `pending`, 64 of
  `last` and the `n` bytes of the input. `decode_ok` restates it with the
  buffer sizes, and `decode_ssse3_ok`, `decode_avx2_ok`,
  `decode_avx512vbmi_ok` and `decode_neon_ok` apply it to each instruction set.
- `encScalar_ok`, `encNeon_ok`, `encSsse3_ok`, `encAvx2_ok`, `encAvx512_ok`,
  `encVbmi_ok`: the same for each encoder, with or without padding. The
  `...G_ok` versions take the loop test as a parameter.
- `vbmi_lengths`: in the VBMI encoder tail, `2 ≤ data_len ≤ out_len ≤ 64`, so
  the shifts `UINT64_MAX >> (64 - x)` are defined.
- `wloop_out`: the stores of the encoders' vector loops are exact, so they
  would stay in the buffer with no margin at all.

**Invariants.** In the decoder, let `o` be the bytes written to `out`, `c`
the bytes read and `buf` the pending values. Then `4 * o + 3 * buf ≤ 3 * c`
and `buf < 512`. Four 6-bit values make three bytes: a block of 64 bytes adds
at most 192 to each side, and decoding 64 pending values into 48 bytes leaves
the left side unchanged. A store of `48 + slack` bytes at `o`, issued while a
whole block is still unread, therefore ends by `3(n - 64)/4 + 48 + slack`. In
the scalar decoder, the `i`-th alphabet character is stored below
`j0 + i + 1` and below `j0 + (3(i + 1) + 3) / 4`. In the encoders,
`3 * o = 4 * c`.

## Tightness (`Tight.lean`)

Every bound is reached, so none can be lowered:

| bound | witness |
|---|---|
| `pending`: 638 of 640 bytes, all instruction sets | 575 bytes: one block with a byte outside the alphabet, seven clean blocks, then 63 alphabet characters. That leaves 511 pending values, the last `compress` writes up to byte 575, and the `memset` up to byte 638. Nine blocks (576 bytes) would overflow. |
| `out`: `⌊3n/4⌋ + 4` (SSSE3, NEON) | 16 alphabet characters: `step16` writes 16 bytes, which is also all of `n` |
| `out`: `⌊3n/4⌋ + 8` (AVX2), `+ 16` (VBMI), `+ 4` via `pack` (SSSE3) | 64 alphabet characters: `pack` writes up to byte 56, 64 (all of `n`) and 52 |

Each loop of the decoder tests for exactly the bytes it loads: 64 per block,
128 per pair, 16 per step. Its margin is zero, and the stores fit.

The encoders' vector stores are exact (`wloop_out`), so the loads set the loop
tests. Each test is the least that keeps the loads in the input: with one
less, some input makes a load read past its end.

| loop | test | consumed | margin | witness of one less |
|---|---|---|---|---|
| SSSE3 | `length > 15` | 12 | 4 | `ssse3_tight`: 15 bytes, 16-byte load |
| AVX2, first | `length > 31` | 24 | 8 | `avx2_first_tight`: 31 bytes, 32-byte load |
| AVX2, loop | `length >= 28` | 24 | 4 | `avx2_loop_tight`: 51 bytes, the load at `c - 4` ends at byte 52 |
| AVX-512 | `length > 63` | 48 | 16 | `avx512_tight`: 63 bytes, 64-byte load |
| VBMI, loop | `length >= 64` | 48 | 16 | `vbmi_tight`: 63 bytes, 64-byte load |
| VBMI, masked step | `length >= 48` | 48 | 0 | `vbmi_masked_tight`: 47 bytes, 48-byte masked load |
| NEON | `inl >= 48` | 48 | 0 | `neon_tight`: 47 bytes, `vld3q_u8` of 48 |

**What the bounds say about the code.** The decoder allocates `n + 1` bytes,
but it never writes past `⌊3n/4⌋ + 16` (`+ 4` with NEON), so it could allocate
about a quarter less. The AVX-512 encoder could drop its margin of 16 by using
the masked step of the VBMI encoder.

## What is assumed

- The model is a hand transcription of the C code: the control flow of
  `PHP_BASE64_DECODE_SIMD` and of the encoders, and the offset and width of
  each access in the helpers. Comments in the Lean files quote the C they
  model.
- The width of each intrinsic's access, and masked AVX-512 accesses touching
  only the bytes their mask selects.
- Lookup-table reads (`php_base64_thintable`, `php_base64_combine[kept]` with
  `kept ≤ 8`, `base64_reverse_table`) are indexed by a byte or a count and are
  not modelled.
- Lengths are natural numbers. `size_t` overflow is not modelled; allocation
  fails before it matters.
