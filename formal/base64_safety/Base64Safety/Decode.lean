import Base64Safety.Basic

/-
The vectorized decoders: `PHP_BASE64_DECODE_SIMD(isa, pairs)` in
`ext/standard/base64.c`, instantiated for SSSE3, AVX2, AVX-512 VBMI and NEON.

**Input.** The decoder reads `n` bytes. Its three block loops advance `c` by
64 (or 128), so they see the input as `⌊n / 64⌋` blocks of 64 bytes, followed
by a tail of `t = n % 64` bytes, which the code copies into `last[64]`
completed with zero bytes (outside the alphabet). A block is abstracted to the
number of its alphabet characters in each of its four 16-byte quarters, which
determines every store offset of the code, and to `esc`: in strict mode, the
block holds a byte that is neither in the alphabet nor whitespace, so that the
decoder hands over to the scalar code (`php_base64_decode_resume`).

The other choices made by the input are left free:
* `steps`: how many 16-byte steps `php_base64_decode_<isa>_step16` decodes in
  the tail (capped at `t / 16`, the steps that the loop test allows);
* `vals`: how many alphabet characters the scalar loop meets (capped at the
  number of bytes it reads).

A run that fails (`goto fail`, or the scalar loop returning 0) stops writing
except for `zend_string_efree`; its stores are a prefix of the stores of the
run that does not fail, with the same choices or a smaller `vals`, so the
model covers it.

**Buffers.** `out` is `ZSTR_VAL(zend_string_alloc(n, 0))`: `n` bytes and the
terminating byte (`_ZSTR_STRUCT_SIZE(len)` is `header + len + 1`). `pending`
is `php_base64_<isa>_block pending[512 / 64 + 2]`, 640 bytes, and `last` is
64 bytes.
-/

namespace Base64Safety

/-- The number of alphabet characters in each 16-byte quarter of a block. -/
structure Quarters where
  q0 : Nat
  q1 : Nat
  q2 : Nat
  q3 : Nat
  h0 : q0 ≤ 16
  h1 : q1 ≤ 16
  h2 : q2 ≤ 16
  h3 : q3 ≤ 16

/-- `64 - popcount(bad)`: the values `compress` keeps. -/
def Quarters.total (q : Quarters) : Nat := q.q0 + q.q1 + q.q2 + q.q3

theorem Quarters.total_le (q : Quarters) : q.total ≤ 64 := by
  have := q.h0; have := q.h1; have := q.h2; have := q.h3
  unfold Quarters.total; omega

/-- The stores of the per-instruction-set helpers, relative to their
destination pointer. -/
structure Isa where
  /-- The `pairs` argument of the macro. -/
  pairs : Bool
  /-- `php_base64_decode_<isa>_pack(b, out)`. -/
  pack : List (Nat × Nat)
  /-- `php_base64_decode_<isa>_compress(b, bad, out)`. -/
  compress : Quarters → List (Nat × Nat)
  /-- `php_base64_decode_<isa>_step16(in, out)`, when it decodes. -/
  step16 : List (Nat × Nat)
  /-- How far `pack` writes past the 48 bytes it decodes, or 4 (the overhang
  of `step16`), whichever is larger. -/
  slack : Nat

def b2n (p : Prop) [Decidable p] : Nat := if p then 1 else 0

/-- The quarter `pos >> 4` of the single byte outside the alphabet. -/
def badQuarter (q : Quarters) : Nat :=
  if q.q0 < 16 then 0 else if q.q1 < 16 then 1 else if q.q2 < 16 then 2 else 3

/-- `php_base64_decode_remove1` (x86) and the single-byte branch of
`php_base64_decode_neon_compress`: the `i`-th vector goes to
`out + 16 * i - (j < i)`. -/
def remove1 (j : Nat) : List (Nat × Nat) :=
  [(0, 16), (16 - b2n (j < 1), 16), (32 - b2n (j < 2), 16), (48 - b2n (j < 3), 16)]

/-- `php_base64_decode_compress64` (x86) and the general branch of
`php_base64_decode_neon_compress`: each quarter is stored as 16 bytes at
`out + n`, where `n` counts the values kept so far. -/
def store16s (q : Quarters) : List (Nat × Nat) :=
  [(0, 16), (q.q0, 16), (q.q0 + q.q1, 16), (q.q0 + q.q1 + q.q2, 16)]

/-- `php_base64_decode_compress32(v, bad, out + base)`, with `a` and `b` the
values kept in its two quarters: one 32-byte store if `bad == 0`, else a
16-byte store at `out` and one at `out + 16 - popcount(bad & 0xffff)`. -/
def compress32 (base a b : Nat) : List (Nat × Nat) :=
  if a + b = 32 then [(base, 32)] else [(base, 16), (base + a, 16)]

/-- `bad && !(bad & (bad - 1))`, that is a single byte outside the alphabet. -/
def single (q : Quarters) : Prop := q.total = 63

instance (q : Quarters) : Decidable (single q) := inferInstanceAs (Decidable (_ = _))

/-- SSSE3: four 16-byte stores at `out`, `out + 12`, `out + 24`, `out + 36`. -/
def ssse3 : Isa where
  pairs := true
  pack := [(0, 16), (12, 16), (24, 16), (36, 16)]
  compress q := if single q then remove1 (badQuarter q) else store16s q
  step16 := [(0, 16)]
  slack := 4

/-- AVX2: two 32-byte stores at `out` and `out + 24`. -/
def avx2 : Isa where
  pairs := true
  pack := [(0, 32), (24, 32)]
  compress q := if single q then remove1 (badQuarter q)
    else compress32 0 q.q0 q.q1 ++ compress32 (q.q0 + q.q1) q.q2 q.q3
  step16 := [(0, 16)]
  slack := 8

/-- AVX-512 VBMI: one 64-byte store; `compress` stores 64 bytes
(`_mm512_maskz_compress_epi8` then `_mm512_storeu_si512`). -/
def avx512vbmi : Isa where
  pairs := false
  pack := [(0, 64)]
  compress _ := [(0, 64)]
  step16 := [(0, 16)]
  slack := 16

/-- NEON: `vst3q_u8` stores 48 bytes. -/
def neon : Isa where
  pairs := true
  pack := [(0, 48)]
  compress q := if single q then remove1 (badQuarter q) else store16s q
  step16 := [(0, 16)]
  slack := 4

/-- `pack` writes at most `48 + slack` bytes, `compress` 64 and `step16` 16
past their pointer, and the slack is between 4 and 16. -/
structure Isa.Good (isa : Isa) : Prop where
  pack : ∀ p ∈ isa.pack, p.1 + p.2 ≤ 48 + isa.slack
  compress : ∀ q, ∀ p ∈ isa.compress q, p.1 + p.2 ≤ 64
  step16 : ∀ p ∈ isa.step16, p.1 + p.2 ≤ 16
  slack_ge : 4 ≤ isa.slack
  slack_le : isa.slack ≤ 16

theorem b2n_le (p : Prop) [Decidable p] : b2n p ≤ 1 := by
  unfold b2n; split <;> omega

theorem remove1_le (j : Nat) : ∀ p ∈ remove1 j, p.1 + p.2 ≤ 64 := by
  intro p hp
  have := b2n_le (j < 1); have := b2n_le (j < 2); have := b2n_le (j < 3)
  simp only [remove1, List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl <;> simp only <;> omega

theorem store16s_le (q : Quarters) : ∀ p ∈ store16s q, p.1 + p.2 ≤ 64 := by
  have := q.h0; have := q.h1; have := q.h2
  intro p hp
  simp only [store16s, List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl <;> simp only <;> omega

theorem compress32_le (base a b : Nat) (ha : a ≤ 16) :
    ∀ p ∈ compress32 base a b, p.1 + p.2 ≤ base + 32 := by
  intro p hp
  unfold compress32 at hp
  split at hp
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
    subst hp; simp only; omega
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl <;> simp only <;> omega

theorem ssse3_good : ssse3.Good where
  pack := by
    intro p hp
    simp only [ssse3, List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl | rfl | rfl <;> decide
  compress := by
    intro q p hp
    simp only [ssse3] at hp
    split at hp
    · exact remove1_le _ p hp
    · exact store16s_le q p hp
  step16 := by
    intro p hp
    simp only [ssse3, List.mem_cons, List.not_mem_nil, or_false] at hp
    subst hp; decide
  slack_ge := by decide
  slack_le := by decide

theorem avx2_good : avx2.Good where
  pack := by
    intro p hp
    simp only [avx2, List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl <;> decide
  compress := by
    intro q p hp
    simp only [avx2] at hp
    split at hp
    · exact remove1_le _ p hp
    · have := q.h0; have := q.h1; have := q.h2
      rcases List.mem_append.mp hp with h | h
      · have := compress32_le 0 q.q0 q.q1 q.h0 p h; omega
      · have := compress32_le (q.q0 + q.q1) q.q2 q.q3 q.h2 p h; omega
  step16 := by
    intro p hp
    simp only [avx2, List.mem_cons, List.not_mem_nil, or_false] at hp
    subst hp; decide
  slack_ge := by decide
  slack_le := by decide

theorem avx512vbmi_good : avx512vbmi.Good where
  pack := by
    intro p hp
    simp only [avx512vbmi, List.mem_cons, List.not_mem_nil, or_false] at hp
    subst hp; decide
  compress := by
    intro q p hp
    simp only [avx512vbmi, List.mem_cons, List.not_mem_nil, or_false] at hp
    subst hp; decide
  step16 := by
    intro p hp
    simp only [avx512vbmi, List.mem_cons, List.not_mem_nil, or_false] at hp
    subst hp; decide
  slack_ge := by decide
  slack_le := by decide

theorem neon_good : neon.Good where
  pack := by
    intro p hp
    simp only [neon, List.mem_cons, List.not_mem_nil, or_false] at hp
    subst hp; decide
  compress := by
    intro q p hp
    simp only [neon] at hp
    split at hp
    · exact remove1_le _ p hp
    · exact store16s_le q p hp
  step16 := by
    intro p hp
    simp only [neon, List.mem_cons, List.not_mem_nil, or_false] at hp
    subst hp; decide
  slack_ge := by decide
  slack_le := by decide

/-! ## The input -/

structure Block where
  q : Quarters
  /-- Strict mode, and a byte that is neither alphabet nor whitespace. -/
  esc : Bool

structure DecIn where
  blocks : List Block
  /-- `n % 64`, the bytes after the last full block. -/
  t : Nat
  /-- The tail completed with zero bytes, as a block. -/
  tail : Quarters
  steps : Nat
  vals : Nat

/-- The input length. -/
def DecIn.len (d : DecIn) : Nat := 64 * d.blocks.length + d.t

/-- The tail is shorter than a block, and its alphabet characters are among
its `t` bytes. -/
def DecIn.Valid (d : DecIn) : Prop := d.t < 64 ∧ d.tail.total ≤ d.t


/-- The sizes of the buffers: `out` is `zend_string_alloc(n, 0)`, `n` bytes and
the terminating byte; `pending` is 640 bytes; `last` 64; the input `n`. -/
def decBuf (n : Nat) : Buf → Nat
  | .out => n + 1
  | .pending => 640
  | .last => 64
  | .input => n

/-- The bound on `out` proved below: `⌊3n/4⌋ + slack`, and never past `n + 1`. -/
def outCap (isa : Isa) (n : Nat) : Nat := min (n + 1) ((3 * n + 4 * isa.slack) / 4)

/-- The tight bounds: `out` as above, 638 bytes of `pending`. -/
def decCap (isa : Isa) (n : Nat) : Buf → Nat
  | .out => outCap isa n
  | .pending => 638
  | .last => 64
  | .input => n

theorem decCap_le (isa : Isa) (n : Nat) (b : Buf) : decCap isa n b ≤ decBuf n b := by
  cases b <;> simp [decCap, decBuf, outCap]
  exact Nat.min_le_left _ _

theorem outFit {isa : Isa} {n e : Nat} (h1 : e ≤ n + 1) (h2 : 4 * e ≤ 3 * n + 4 * isa.slack) :
    e ≤ decCap isa n .out := by
  simp only [decCap, outCap]
  exact Nat.le_min.mpr ⟨h1, by omega⟩

/-! ## The code

Loads are accesses to `input`, and reads of `pending` and `last`. -/

/-- `for (k = 0; k + 64 <= buffered; k += 64) { pack(&pending[k / 64], o); o += 48; }`,
running `k` times, from block `i` of `pending`. -/
def flush (isa : Isa) (o i : Nat) : Nat → List Store
  | 0 => []
  | k + 1 => ⟨.pending, 64 * i, 64⟩ :: place .out o isa.pack ++ flush isa (o + 48) (i + 1) k

/-- `php_base64_decode_resume(result, o, buffer, buffered, c, end - c)`: the
`buffered` pending values, then the scalar loop on the rest of the input, then
`out[outl] = '\0'` in `php_base64_decode_finish`. -/
def resume (inp : DecIn) (o buf c : Nat) : List Store :=
  let r1 := scalar o 0 buf
  let r2 := scalar r1.2 buf (min inp.vals (inp.len - c))
  [⟨.pending, 0, buf⟩, ⟨.input, c, inp.len - c⟩] ++ r1.1 ++ r2.1 ++ [⟨.out, r2.2, 1⟩]

/-- `while (end - c >= 16 && step16(c, o)) { c += 16; o += 12; }`, `s` steps
that decode, each loading 16 bytes. -/
def stepLoop (isa : Isa) (o c : Nat) : Nat → List Store
  | 0 => []
  | s + 1 => ⟨.input, c, 16⟩ :: place .out o isa.step16 ++ stepLoop isa (o + 12) (c + 16) s

/-- Everything after the block loops, from `if (buffered == 0)` on. -/
def decTail (isa : Isa) (inp : DecIn) (o c buf : Nat) : List Store :=
  if buf = 0 then
    let s := min inp.steps (inp.t / 16)
    let c1 := c + 16 * s
    let rest := inp.t - 16 * s
    let r := scalar (o + 12 * s) 0 (min inp.vals rest)
    stepLoop isa o c s
      -- the step that does not decode loads its 16 bytes
      ++ (if 16 ≤ rest then [⟨.input, c1, 16⟩] else [])
      -- php_base64_decode_loop(c, end - c, ...)
      ++ [⟨.input, c1, rest⟩] ++ r.1 ++ [⟨.out, r.2, 1⟩]
  else
    let buf1 := buf + inp.tail.total
    let k := buf1 / 64
    let r := buf1 % 64
    let o1 := o + 48 * k
    let kk := (r / 4) * 3 + (r % 4 - 1)
    -- memset(last, 0, 64); php_base64_copy_short(last, c, end - c);
    [⟨.last, 0, 64⟩] ++ copyShort .last 0 inp.t ++ copyShort .input c inp.t
      -- translate(&b, last) and match(last, ...)
      ++ [⟨.last, 0, 64⟩]
      -- buffered += compress(&b, ~good, buffer + buffered);
      ++ place .pending buf (isa.compress inp.tail)
      -- the flush loop
      ++ flush isa o 0 k
      -- memset(buffer + k + buffered, 0, 64);
      ++ [⟨.pending, 64 * k + r, 64⟩]
      -- pack(&pending[k / 64], last);
      ++ [⟨.pending, 64 * k, 64⟩] ++ place .last 0 isa.pack
      -- php_base64_copy_short(o, last, k); o += k;
      ++ copyShort .last 0 kk ++ copyShort .out o1 kk
      -- out[outl] = '\0' in php_base64_decode_finish
      ++ [⟨.out, o1 + kk, 1⟩]

/-- `while (end - c >= 64) { ... }`, the loop with pending values. -/
def mainLoop (isa : Isa) (inp : DecIn) : List Block → Nat → Nat → Nat → List Store
  | [], o, c, buf => decTail isa inp o c buf
  | b :: bs, o, c, buf =>
    -- bad = translate(&b, c);
    ⟨.input, c, 64⟩ ::
    if b.q.total = 64 ∧ buf = 0 then
      place .out o isa.pack ++ mainLoop isa inp bs (o + 48) (c + 64) buf
    else
      -- match(c, php_base64_ws_set), in strict mode
      ⟨.input, c, 64⟩ ::
      if b.esc ∧ b.q.total < 64 then
        resume inp o buf c
      else
        let buf1 := buf + b.q.total
        if 512 ≤ buf1 then
          place .pending buf (isa.compress b.q) ++ flush isa o 0 (buf1 / 64)
            -- pending[0] = pending[k / 64];
            ++ [⟨.pending, 64 * (buf1 / 64), 64⟩, ⟨.pending, 0, 64⟩]
            ++ mainLoop isa inp bs (o + 48 * (buf1 / 64)) (c + 64) (buf1 % 64)
        else
          place .pending buf (isa.compress b.q) ++ mainLoop isa inp bs o (c + 64) buf1

/-- `while (end - c >= 64 && !translate(&b, c)) { pack(&b, o); ... }` -/
def cleanLoop (isa : Isa) (inp : DecIn) : List Block → Nat → Nat → List Store
  | [], o, c => mainLoop isa inp [] o c 0
  | b :: bs, o, c =>
    ⟨.input, c, 64⟩ ::
    if b.q.total = 64 then place .out o isa.pack ++ cleanLoop isa inp bs (o + 48) (c + 64)
    else mainLoop isa inp (b :: bs) o c 0

/-- `while (pairs && end - c >= 128 && !(translate(&b, c) | translate(&b2, c + 64))) { ... }` -/
def pairLoop (isa : Isa) (inp : DecIn) : List Block → Nat → Nat → List Store
  | b1 :: b2 :: bs, o, c =>
    if isa.pairs then
      ⟨.input, c, 64⟩ :: ⟨.input, c + 64, 64⟩ ::
      if b1.q.total = 64 ∧ b2.q.total = 64 then
        place .out o isa.pack ++ place .out (o + 48) isa.pack
          ++ pairLoop isa inp bs (o + 96) (c + 128)
      else cleanLoop isa inp (b1 :: b2 :: bs) o c
    else cleanLoop isa inp (b1 :: b2 :: bs) o c
  | bs, o, c => cleanLoop isa inp bs o c

/-- All the accesses of one call of the decoder. -/
def decode (isa : Isa) (inp : DecIn) : List Store :=
  pairLoop isa inp inp.blocks 0 0

/-! ## Proofs

The invariant of the block loops: with `o` the bytes written to `out`, `c` the
bytes read, and `buf` the pending values, `4 * o + 3 * buf ≤ 3 * c` and
`buf < 512`. Each value is 6 bits, so 4 values give 3 bytes: a block of 64
bytes adds at most 192 to `4 * o + 3 * buf` and 192 to `3 * c`, and turning 64
pending values into 48 bytes leaves `4 * o + 3 * buf` unchanged. A store of
`48 + slack` bytes at `o`, made while a full block is still unread, then ends
at most at `3 * (n - 64) / 4 + 48 + slack`, that is `⌊3n/4⌋ + slack`. -/

theorem scalar_ok (isa : Isa) (n j0 m i : Nat) (h1 : j0 + i + m ≤ n + 1)
    (h2 : 4 * j0 + 3 * (i + m) + 3 ≤ 3 * n + 4 * isa.slack) :
    AllOk (decCap isa n) (scalar (jOf j0 i) i m).1 := by
  intro s hs
  obtain ⟨hb, ha, hc⟩ := (scalar_spec j0 m i).1 s hs
  rw [hb]
  exact outFit (by omega) (by omega)

theorem flush_ok {isa : Isa} (hg : isa.Good) (n : Nat) :
    ∀ k o i, 4 * o + 192 * k ≤ 3 * n → 64 * (i + k) ≤ 576 →
      AllOk (decCap isa n) (flush isa o i k) := by
  intro k
  induction k with
  | zero => intro _ _ _ _; exact AllOk.nil _
  | succ k ih =>
    intro o i h hi
    have := hg.slack_le
    refine AllOk.cons (by simp only [decCap]; omega)
      (AllOk.append (place_ok hg.pack (outFit (by omega) (by omega)))
        (ih (o + 48) (i + 1) (by omega) (by omega)))

theorem stepLoop_ok {isa : Isa} (hg : isa.Good) (n : Nat) :
    ∀ s o c, 4 * o ≤ 3 * c → c + 16 * s ≤ n → AllOk (decCap isa n) (stepLoop isa o c s) := by
  intro s
  induction s with
  | zero => intro _ _ _ _; exact AllOk.nil _
  | succ s ih =>
    intro o c h hc
    have := hg.slack_ge
    refine AllOk.cons (by simp only [decCap]; omega)
      (AllOk.append (place_ok hg.step16 (outFit (by omega) (by omega)))
        (ih (o + 12) (c + 16) (by omega) (by omega)))

theorem resume_ok {isa : Isa} (hg : isa.Good) (inp : DecIn) (o buf c : Nat)
    (h : 4 * o + 3 * buf ≤ 3 * c) (hc : c ≤ inp.len) (hb : buf < 512) :
    AllOk (decCap isa inp.len) (resume inp o buf c) := by
  have := hg.slack_ge
  unfold resume
  have hm : min inp.vals (inp.len - c) ≤ inp.len - c := Nat.min_le_right _ _
  have h1 := scalar_ok isa inp.len o buf 0 (by omega) (by omega)
  rw [jOf_zero] at h1
  have h1b := (scalar_spec o buf 0).2
  rw [jOf_zero] at h1b
  simp only [Nat.zero_add] at h1b
  simp only
  rw [h1b]
  have h2 := scalar_ok isa inp.len o (min inp.vals (inp.len - c)) buf (by omega) (by omega)
  have h2b := (scalar_spec o (min inp.vals (inp.len - c)) buf).2
  rw [h2b]
  have hj := jOf_le o (buf + min inp.vals (inp.len - c))
  refine AllOk.append (AllOk.append (AllOk.append ?_ h1) h2) (AllOk.single ?_)
  · refine AllOk.cons (by simp only [decCap]; omega) (AllOk.single ?_)
    simp only [decCap]; omega
  · exact outFit (by omega) (by omega)

theorem decTail_ok {isa : Isa} (hg : isa.Good) (inp : DecIn) (hv : inp.Valid)
    (o c buf : Nat) (h : 4 * o + 3 * buf ≤ 3 * c) (hc : c + inp.t = inp.len) (hb : buf < 512) :
    AllOk (decCap isa inp.len) (decTail isa inp o c buf) := by
  obtain ⟨ht, htail⟩ := hv
  have := hg.slack_ge
  have := hg.slack_le
  unfold decTail
  split
  · -- no pending values: 16-byte steps, then the scalar loop
    rename_i hb0
    simp only
    have hs : min inp.steps (inp.t / 16) ≤ inp.t / 16 := Nat.min_le_right _ _
    have hs' : 16 * min inp.steps (inp.t / 16) ≤ inp.t := by omega
    have hm : min inp.vals (inp.t - 16 * min inp.steps (inp.t / 16))
        ≤ inp.t - 16 * min inp.steps (inp.t / 16) := Nat.min_le_right _ _
    have h1 := scalar_ok isa inp.len (o + 12 * min inp.steps (inp.t / 16))
      (min inp.vals (inp.t - 16 * min inp.steps (inp.t / 16))) 0 (by omega) (by omega)
    rw [jOf_zero] at h1
    have h1b := (scalar_spec (o + 12 * min inp.steps (inp.t / 16))
      (min inp.vals (inp.t - 16 * min inp.steps (inp.t / 16))) 0).2
    rw [jOf_zero] at h1b
    simp only [Nat.zero_add] at h1b
    rw [h1b]
    have hj := jOf_le (o + 12 * min inp.steps (inp.t / 16))
      (min inp.vals (inp.t - 16 * min inp.steps (inp.t / 16)))
    refine AllOk.append (AllOk.append (AllOk.append (AllOk.append
      (stepLoop_ok hg _ _ _ _ (by omega) (by omega)) ?_) (AllOk.single ?_)) h1)
      (AllOk.single ?_)
    · split
      · exact AllOk.single (by simp only [decCap]; omega)
      · exact AllOk.nil _
    · simp only [decCap]; omega
    · exact outFit (by omega) (by omega)
  · -- pending values: the tail goes through `last`
    have hq := inp.tail.total_le
    have hk := Nat.div_add_mod (buf + inp.tail.total) 64
    have hr := Nat.mod_lt (buf + inp.tail.total) (show 64 > 0 by decide)
    have hkk : 4 * (((buf + inp.tail.total) % 64 / 4) * 3
        + ((buf + inp.tail.total) % 64 % 4 - 1)) ≤ 3 * ((buf + inp.tail.total) % 64) := by
      omega
    refine AllOk.append (AllOk.append (AllOk.append (AllOk.append (AllOk.append
      (AllOk.append (AllOk.append (AllOk.append (AllOk.append (AllOk.append (AllOk.append
      (AllOk.single ?_) ?_) ?_) (AllOk.single ?_)) ?_) ?_) (AllOk.single ?_))
      (AllOk.single ?_)) ?_) ?_) ?_) (AllOk.single ?_)
    · simp [decCap]
    · exact copyShort_ok (by simp [decCap]; omega)
    · exact copyShort_ok (by simp [decCap]; omega)
    · simp [decCap]
    · exact place_ok (hg.compress inp.tail) (by simp [decCap]; omega)
    · exact flush_ok hg _ _ _ _ (by omega) (by omega)
    · simp [decCap]; omega
    · simp [decCap]; omega
    · exact place_ok hg.pack (by simp [decCap]; omega)
    · exact copyShort_ok (by simp [decCap]; omega)
    · exact copyShort_ok (outFit (by omega) (by omega))
    · exact outFit (by omega) (by omega)

theorem mainLoop_ok {isa : Isa} (hg : isa.Good) (inp : DecIn) (hv : inp.Valid) :
    ∀ (bs : List Block) (o c buf : Nat), 4 * o + 3 * buf ≤ 3 * c →
      c + 64 * bs.length + inp.t = inp.len → buf < 512 →
      AllOk (decCap isa inp.len) (mainLoop isa inp bs o c buf) := by
  have := hg.slack_le
  intro bs
  induction bs with
  | nil =>
    intro o c buf h hc hb
    exact decTail_ok hg inp hv o c buf h (by simpa using hc) hb
  | cons b bs ih =>
    intro o c buf h hc hb
    simp only [List.length_cons] at hc
    have hq := b.q.total_le
    unfold mainLoop
    refine AllOk.cons (by simp only [decCap]; omega) ?_
    split
    · exact AllOk.append (place_ok hg.pack (outFit (by omega) (by omega)))
        (ih _ _ _ (by omega) (by omega) hb)
    · refine AllOk.cons (by simp only [decCap]; omega) ?_
      split
      · exact resume_ok hg inp o buf c h (by omega) hb
      · simp only
        have hk := Nat.div_add_mod (buf + b.q.total) 64
        have hr := Nat.mod_lt (buf + b.q.total) (show 64 > 0 by decide)
        split
        · refine AllOk.append (AllOk.append (AllOk.append ?_ ?_) ?_) ?_
          · exact place_ok (hg.compress b.q) (by simp [decCap]; omega)
          · exact flush_ok hg _ _ _ _ (by omega) (by omega)
          · refine AllOk.cons (by simp only [decCap]; omega) (AllOk.single ?_)
            simp [decCap]
          · exact ih _ _ _ (by omega) (by omega) (by omega)
        · exact AllOk.append (place_ok (hg.compress b.q) (by simp [decCap]; omega))
            (ih _ _ _ (by omega) (by omega) (by omega))

theorem cleanLoop_ok {isa : Isa} (hg : isa.Good) (inp : DecIn) (hv : inp.Valid) :
    ∀ (bs : List Block) (o c : Nat), 4 * o ≤ 3 * c → c + 64 * bs.length + inp.t = inp.len →
      AllOk (decCap isa inp.len) (cleanLoop isa inp bs o c) := by
  have := hg.slack_le
  intro bs
  induction bs with
  | nil =>
    intro o c h hc
    exact mainLoop_ok hg inp hv [] o c 0 (by omega) hc (by decide)
  | cons b bs ih =>
    intro o c h hc
    simp only [List.length_cons] at hc
    unfold cleanLoop
    refine AllOk.cons (by simp only [decCap]; omega) ?_
    split
    · exact AllOk.append (place_ok hg.pack (outFit (by omega) (by omega)))
        (ih _ _ (by omega) (by omega))
    · exact mainLoop_ok hg inp hv (b :: bs) o c 0 (by omega) (by simp; omega) (by decide)

theorem pairLoop_ok {isa : Isa} (hg : isa.Good) (inp : DecIn) (hv : inp.Valid) :
    ∀ (n : Nat) (bs : List Block) (o c : Nat), bs.length ≤ n → 4 * o ≤ 3 * c →
      c + 64 * bs.length + inp.t = inp.len →
      AllOk (decCap isa inp.len) (pairLoop isa inp bs o c) := by
  have := hg.slack_le
  intro n
  induction n using Nat.strongRecOn with
  | _ n ih =>
    intro bs o c hn h hc
    match bs with
    | b1 :: b2 :: bs =>
      simp only [List.length_cons] at hc hn
      unfold pairLoop
      split
      · refine AllOk.cons (by simp only [decCap]; omega)
          (AllOk.cons (by simp only [decCap]; omega) ?_)
        split
        · refine AllOk.append (AllOk.append ?_ ?_) ?_
          · exact place_ok hg.pack (outFit (by omega) (by omega))
          · exact place_ok hg.pack (outFit (by omega) (by omega))
          · exact ih bs.length (by omega) bs _ _ (Nat.le_refl _) (by omega) (by omega)
        · exact cleanLoop_ok hg inp hv _ o c h (by simp; omega)
      · exact cleanLoop_ok hg inp hv _ o c h (by simp; omega)
    | [] =>
      unfold pairLoop
      exact cleanLoop_ok hg inp hv _ o c h hc
    | [b] =>
      unfold pairLoop
      exact cleanLoop_ok hg inp hv _ o c h hc

/-- **Tight bounds.** Every access of the decoder stays within `⌊3n/4⌋ + slack`
bytes of `out` (and `n + 1`), 638 bytes of `pending`, 64 of `last`, and the
`n` bytes of the input. -/
theorem decode_tight {isa : Isa} (hg : isa.Good) (inp : DecIn) (hv : inp.Valid) :
    AllOk (decCap isa inp.len) (decode isa inp) :=
  pairLoop_ok hg inp hv _ inp.blocks 0 0 (Nat.le_refl _) (Nat.le_refl _) (by simp [DecIn.len])

/-- **Main theorem.** Every access of the decoder stays inside its buffer:
`out` (`n + 1` bytes), `pending` (640), `last` (64) and the input (`n`). -/
theorem decode_ok {isa : Isa} (hg : isa.Good) (inp : DecIn) (hv : inp.Valid) :
    AllOk (decBuf inp.len) (decode isa inp) :=
  (decode_tight hg inp hv).mono (decCap_le isa inp.len)

theorem decode_ssse3_ok (inp : DecIn) (hv : inp.Valid) :
    AllOk (decBuf inp.len) (decode ssse3 inp) := decode_ok ssse3_good inp hv

theorem decode_avx2_ok (inp : DecIn) (hv : inp.Valid) :
    AllOk (decBuf inp.len) (decode avx2 inp) := decode_ok avx2_good inp hv

theorem decode_avx512vbmi_ok (inp : DecIn) (hv : inp.Valid) :
    AllOk (decBuf inp.len) (decode avx512vbmi inp) := decode_ok avx512vbmi_good inp hv

theorem decode_neon_ok (inp : DecIn) (hv : inp.Valid) :
    AllOk (decBuf inp.len) (decode neon inp) := decode_ok neon_good inp hv

end Base64Safety
