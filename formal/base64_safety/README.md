# Store safety of the base64 encoders and decoders

This Lean 4 development proves that no store of the base64 code in
`ext/standard/base64.c` goes past its buffer, on any input. It covers:

- the decoder template `PHP_BASE64_DECODE_SIMD` for SSSE3, AVX2,
  AVX-512 VBMI and NEON, in strict and non-strict mode, including the
  hand-over to the scalar decoder (`php_base64_decode_resume`);
- every encoder: scalar, NEON, SSSE3, AVX2, AVX-512 and AVX-512 VBMI.

```sh
source "$HOME/.elan/env"
cd formal/base64_safety
lake build
```

`lean-toolchain` pins Lean 4.35. There is no mathlib, no `sorry` and no
`native_decide`. The theorems use only the axioms `propext`, `Quot.sound` and
`Classical.choice`.

## Files

| file | content |
|---|---|
| `Base64Safety/Basic.lean` | stores, `php_base64_copy_short`, the scalar decoder (`php_base64_decode_put`) |
| `Base64Safety/Decode.lean` | the store helpers of each instruction set, the decoder, `decode_ok` |
| `Base64Safety/Encode.lean` | the encoders and their theorems |

## Model

A **store** writes `len` bytes at offset `off` of a buffer: `out` (the
result's characters), `pending` (the decoder's array of pending values) or
`last` (the decoder's 64-byte tail). A vector store writes the vector's full
width, whatever its lanes hold. A masked AVX-512 store writes the bytes its mask
selects, because masked-out bytes do not fault. A `memcpy` or `memset` of
`n` bytes is one store of `n` bytes.

**Buffer sizes.**

| buffer | size | source |
|---|---|---|
| decoder `out` | `n + 1` | `zend_string_alloc(n, 0)`: `_ZSTR_STRUCT_SIZE(len)` is `header + len + 1` |
| encoder `out` | `4 * ⌈n / 3⌉ + 1` | `zend_string_safe_alloc((n + 2) / 3, 4, 0, 0)` |
| `pending` | 640 | `php_base64_<isa>_block pending[512 / 64 + 2]` |
| `last` | 64 | `unsigned char last[64]` |

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
reads. The theorems hold for every choice.

A failing run (`goto fail`, or `php_base64_decode_loop` returning 0) only stops
writing. Its stores are a prefix of the stores of a run that does not fail, so
the model covers it.

**Helpers** (`Isa`), relative to their destination pointer:

| | `pack` | `compress` | `step16` |
|---|---|---|---|
| SSSE3 | 16 at 0, 12, 24, 36 | 16 at 0, `q0`, `q0+q1`, `q0+q1+q2` (single bad byte: at `16i - (j < i)`) | 16 |
| AVX2 | 32 at 0, 24 | per half: 32, or 16 at 0 and 16 at `q`; single bad byte as SSSE3 | 16 |
| AVX-512 VBMI | 64 | 64 | 16 |
| NEON | 48 (`vst3q_u8`) | as SSSE3 | 16 |

`Isa.Good` requires each helper to stay within 64 bytes of its pointer (16 for
`step16`), and the four instruction sets are proved to satisfy it.

## Theorems

- `decode_ok`: for any `Isa.Good` instruction set and any input, every store of
  the decoder stays inside `out`, `pending` and `last`.
  `decode_ssse3_ok`, `decode_avx2_ok`, `decode_avx512vbmi_ok` and
  `decode_neon_ok` apply it to each instruction set.
- `encScalar_ok`, `encNeon_ok`, `encSsse3_ok`, `encAvx2_ok`, `encAvx512_ok`,
  `encVbmi_ok`: the same for each encoder, with or without padding.
- `vbmi_lengths`: in the VBMI encoder tail, `2 ≤ data_len ≤ out_len ≤ 64`, so
  the shifts `UINT64_MAX >> (64 - x)` are defined.

**Invariants.** In the decoder's block loops, let `o` be the bytes written to
`out`, `c` the bytes read and `buf` the pending values. Then `o + buf ≤ c` and
`buf < 512`. A block adds at most 64 to `o + buf`, and turning 64 pending
values into 48 bytes lowers it by 16. A store of at most 64 bytes at `o`,
issued while a whole block is still unread, therefore ends by `c + 64 ≤ n`.
This is the argument in the comment above `php_base64_ws_set`. In the scalar
decoder, the `i`-th alphabet character is stored below `j0 + i + 1`. In the
encoders, `3 * o + 4 * len = 4 * n`, and every vector store of `w` bytes runs
with at least `3 * w / 4` bytes left.

## Margins

The proofs leave little slack, so each bound is checked against the model:

- `pending`: the stores end at most at byte 638 of 640. A 575-byte input
  reaches 638: one block with 63 alphabet characters, seven clean blocks, then
  a tail of 63 alphabet characters. That leaves 511 pending values, the last
  compress writes up to byte 575, and the `memset` writes up to byte 638. With
  a 637-byte array the proof fails.
- Mutants that the proofs reject: a 65-byte NEON `pack`, the AVX2 second
  16-byte store one byte later, `step16` advancing `o` by 13, the `put` case 1
  store at `j + 2`, the AVX2 encoder breaking at `length < 20` instead of 28,
  the SSSE3 encoder loop running at 15 bytes left, and the VBMI tail with
  `(len + 3) / 3` groups.

## What is assumed

- The model is a hand transcription of the C code: the control flow of
  `PHP_BASE64_DECODE_SIMD` and of the encoders, and the offset and width of
  each store in the helpers. Comments in the Lean files quote the C they model.
- The store width of each intrinsic, and masked AVX-512 stores writing only
  the bytes their mask selects.
- Loads are not modelled: this development is about writes only.
- Lengths are natural numbers. `size_t` overflow is not modelled; allocation
  fails before it matters.
