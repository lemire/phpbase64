import Base64Safety.Basic

/-
The encoders of `ext/standard/base64.c`. Each allocates
`zend_string_safe_alloc((length + 2) / 3, 4, 0, 0)`: `4 * ⌈n / 3⌉` bytes and
the terminating byte. Every vector iteration consumes `adv` input bytes and
stores exactly the `4 * adv / 3` characters they encode, so
`3 * o = 4 * c` holds throughout, with `o` the bytes written and `c` the bytes
read; `len = n - c` is the bytes left.

The loop tests are parameters (`lim`, the least `len` for which an iteration
runs), so that `Tight.lean` can show that one less fails. The code uses the
instances `encSsse3`, `encAvx2`, ... below.
-/

namespace Base64Safety

/-- The sizes of the encoder's buffers. -/
def encCap (n : Nat) : Buf → Nat
  | .out => 4 * ((n + 2) / 3) + 1
  | .input => n
  | _ => 0

def one (j : Nat) : Store := ⟨.out, j, 1⟩

/-- `while (inl > 2) { *out++ = ...; (4 times) in += 3; inl -= 3; }` in
`php_base64_encode_impl`: the accesses, the final `out` and `inl`. -/
def implLoop (o c inl : Nat) : List Store × Nat × Nat :=
  if _h : inl > 2 then
    let r := implLoop (o + 4) (c + 3) (inl - 3)
    ([⟨.input, c, 3⟩, one o, one (o + 1), one (o + 2), one (o + 3)] ++ r.1, r.2)
  else ([], o, inl)
termination_by inl
decreasing_by omega

/-- `php_base64_encode_impl` after its NEON prefix: the loop, the last one or
two bytes with their padding, and `*out = '\0'`. -/
def encodeImpl (o c inl : Nat) (nopad : Bool) : List Store :=
  let r := implLoop o c inl
  let o1 := r.2.1
  let rest := r.2.2
  let tail : List Store :=
    if rest = 0 then []
    else if rest > 1 then
      [⟨.input, c + 3 * (inl / 3), 2⟩, one o1, one (o1 + 1), one (o1 + 2)]
        ++ (if nopad then [] else [one (o1 + 3)])
    else
      [⟨.input, c + 3 * (inl / 3), 1⟩, one o1, one (o1 + 1)]
        ++ (if nopad then [] else [one (o1 + 2), one (o1 + 3)])
  let o2 := o1 + (if rest = 0 then 0 else if rest > 1 then (if nopad then 3 else 4)
    else (if nopad then 2 else 4))
  r.1 ++ tail ++ [one o2]

/-- `while (len >= lim) { load ld bytes at c; store w bytes at o; o += w; c += adv; len -= adv; }`:
the SSSE3 loop (`len > 15`: `lim = 16`, `adv = 12`, `w = 16`, `ld = 16`), the
AVX-512 loop (`len > 63`) and the main AVX-512 VBMI loop (`len >= 64`), both
`64`, `48`, `64`, `64`, and the NEON loop (`48`, `48`, `64`, `48`), whose
`do { } while` runs behind an equivalent `if`. Returns the accesses, `o`, `c`
and `len`. If `len < adv` after the test (possible only with `lim < adv`),
`length -= adv` wraps around in C; the model stops there, after the
iteration's accesses. -/
def wloop (lim adv w ld : Nat) (h1 : 0 < adv) (o c len : Nat) : List Store × Nat × Nat × Nat :=
  if lim ≤ len then
    if _h : adv ≤ len then
      let r := wloop lim adv w ld h1 (o + w) (c + adv) (len - adv)
      (⟨.input, c, ld⟩ :: ⟨.out, o, w⟩ :: r.1, r.2)
    else ([⟨.input, c, ld⟩, ⟨.out, o, w⟩], o + w, c + adv, 0)
  else ([], o, c, len)
termination_by len
decreasing_by omega

/-- The AVX2 loop, entered with 32 bytes loaded at `c`:
`for (;;) { store 32 bytes; c += 24; o += 32; length -= 24; if (length < lim) break;
s = load 32 bytes at c - 4; }`; the code has `lim = 28`. -/
def avx2Loop (lim : Nat) (o c len : Nat) : List Store × Nat × Nat × Nat :=
  if _h : len - 24 < lim ∨ len < 24 then ([⟨.out, o, 32⟩], o + 32, c + 24, len - 24)
  else
    let r := avx2Loop lim (o + 32) (c + 24) (len - 24)
    (⟨.out, o, 32⟩ :: ⟨.input, c + 24 - 4, 32⟩ :: r.1, r.2)
termination_by len
decreasing_by omega

/-! ## The encoders -/

/-- `php_base64_encode_impl` on aarch64: the NEON loop when `inl >= lim`. -/
def neonImplG (lim : Nat) (o c inl : Nat) (nopad : Bool) : List Store :=
  if lim ≤ inl then
    let r := wloop lim 48 64 48 (by decide) o c inl
    r.1 ++ encodeImpl r.2.1 r.2.2.1 r.2.2.2 nopad
  else encodeImpl o c inl nopad

/-- Without SIMD (x86 fallback). -/
def encScalar (n : Nat) (nopad : Bool) : List Store := encodeImpl 0 0 n nopad

def encNeonG (lim n : Nat) (nopad : Bool) : List Store := neonImplG lim 0 0 n nopad

def encSsse3G (lim n : Nat) (nopad : Bool) : List Store :=
  let r := wloop lim 12 16 16 (by decide) 0 0 n
  r.1 ++ encodeImpl r.2.1 r.2.2.1 r.2.2.2 nopad

/-- `if (length >= first) { s = load 32 bytes; the loop }`; the code has
`length > 31`, that is `first = 32`. -/
def encAvx2G (first lim n : Nat) (nopad : Bool) : List Store :=
  if first ≤ n ∧ 24 ≤ n then
    let r := avx2Loop lim 0 0 n
    ⟨.input, 0, 32⟩ :: r.1 ++ encodeImpl r.2.1 r.2.2.1 r.2.2.2 nopad
  else encodeImpl 0 0 n nopad

def encAvx512G (lim n : Nat) (nopad : Bool) : List Store :=
  let r := wloop lim 48 64 64 (by decide) 0 0 n
  r.1 ++ encodeImpl r.2.1 r.2.2.1 r.2.2.2 nopad

/-- The lengths of the AVX-512 VBMI tail, for `0 < len < 48` bytes left. -/
def vbmiFull (len : Nat) : Nat := ((len + 2) / 3) * 4
def vbmiData (len : Nat) : Nat := vbmiFull len - (3 - len % 3) % 3
def vbmiOut (len : Nat) (nopad : Bool) : Nat := if nopad then vbmiData len else vbmiFull len

/-- `php_base64_encode_avx512_vbmi`: the main loop (`length >= lim`, 64 in the
code), one more step with a masked load of 48 bytes if `length >= lim2` (48 in
the code), then a masked load of the `len` bytes left, a masked store of
`out_len` bytes, and the terminating byte. -/
def encVbmiG (lim lim2 n : Nat) (nopad : Bool) : List Store :=
  let r := wloop lim 48 64 64 (by decide) 0 0 n
  let o := r.2.1
  let c := r.2.2.1
  let len := r.2.2.2
  let s : List Store × Nat × Nat × Nat :=
    if lim2 ≤ len then ([⟨.input, c, 48⟩, ⟨.out, o, 64⟩], o + 64, c + 48, len - 48)
    else ([], o, c, len)
  let o2 := s.2.1
  let c2 := s.2.2.1
  let len2 := s.2.2.2
  let t : List Store × Nat :=
    if len2 > 0 then
      ([⟨.input, c2, len2⟩, ⟨.out, o2, vbmiOut len2 nopad⟩], o2 + vbmiOut len2 nopad)
    else ([], o2)
  r.1 ++ s.1 ++ t.1 ++ [one t.2]

/-- The encoders as in the code. -/
def encNeon := encNeonG 48
def encSsse3 := encSsse3G 16
def encAvx2 := encAvx2G 32 28
def encAvx512 := encAvx512G 64
def encVbmi := encVbmiG 64 48

/-! ## Proofs -/

theorem implLoop_spec (o c : Nat) : ∀ inl,
    (∀ s ∈ (implLoop o c inl).1,
      (s.buf = .out ∧ s.off + s.len ≤ o + 4 * (inl / 3)) ∨
      (s.buf = .input ∧ s.off + s.len ≤ c + 3 * (inl / 3))) ∧
    (implLoop o c inl).2.1 = o + 4 * (inl / 3) ∧ (implLoop o c inl).2.2 = inl % 3 := by
  intro inl
  induction inl using Nat.strongRecOn generalizing o c with
  | _ inl ih =>
    unfold implLoop
    split
    · rename_i h
      obtain ⟨ha, hb, hc⟩ := ih (inl - 3) (by omega) (o + 4) (c + 3)
      refine ⟨?_, ?_, ?_⟩
      · intro s hs
        rcases List.mem_append.mp hs with hs | hs
        · simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
          rcases hs with rfl | rfl | rfl | rfl | rfl
          · exact Or.inr ⟨rfl, by simp only; omega⟩
          all_goals exact Or.inl ⟨rfl, by simp only [one]; omega⟩
        · rcases ha s hs with ⟨h1, h2⟩ | ⟨h1, h2⟩
          · exact Or.inl ⟨h1, by omega⟩
          · exact Or.inr ⟨h1, by omega⟩
      · simp only; rw [hb]; omega
      · simp only; rw [hc]; omega
    · refine ⟨by simp, ?_, ?_⟩ <;> simp only <;> omega

/-- The scalar encoder, from `o` and `c` with `inl` bytes left, stays in the
buffers when `3 * o = 4 * c` and `c + inl = n`. -/
theorem encodeImpl_ok (n o c inl : Nat) (nopad : Bool) (h : 3 * o = 4 * c)
    (hc : c + inl = n) : AllOk (encCap n) (encodeImpl o c inl nopad) := by
  obtain ⟨ha, hb, hc'⟩ := implLoop_spec o c inl
  have key0 : o + 4 * (inl / 3) ≤ 4 * ((n + 2) / 3) := by omega
  have key1 : inl % 3 ≠ 0 → o + 4 * (inl / 3) + 4 ≤ 4 * ((n + 2) / 3) := by omega
  unfold encodeImpl
  simp only
  rw [hb, hc']
  refine AllOk.append (AllOk.append ?_ ?_) ?_
  · intro s hs
    rcases ha s hs with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · rw [h1]; simp only [encCap]; omega
    · rw [h1]; simp only [encCap]; omega
  · unfold AllOk
    split
    · simp
    · rename_i hr
      have := key1 hr
      split <;> cases nopad <;> simp [one, encCap] <;> omega
  · apply AllOk.single
    simp only [encCap]
    split
    · omega
    · rename_i hr
      have := key1 hr
      split <;> split <;> omega

theorem wloop_spec (n lim adv w ld : Nat) (h1 : 0 < adv) (hld : ld ≤ lim) (hadv : adv ≤ lim)
    (hw : 3 * w = 4 * adv) : ∀ len o c, 3 * o = 4 * c → c + len = n →
      AllOk (encCap n) (wloop lim adv w ld h1 o c len).1 ∧
      3 * (wloop lim adv w ld h1 o c len).2.1 = 4 * (wloop lim adv w ld h1 o c len).2.2.1 ∧
      (wloop lim adv w ld h1 o c len).2.2.1 + (wloop lim adv w ld h1 o c len).2.2.2 = n ∧
      (wloop lim adv w ld h1 o c len).2.2.2 < lim := by
  intro len
  induction len using Nat.strongRecOn with
  | _ len ih =>
    intro o c h hc
    unfold wloop
    split
    · rename_i hl
      simp only [show adv ≤ len by omega, ↓reduceDIte]
      obtain ⟨ha, hb, hc', hd⟩ := ih (len - adv) (by omega) (o + w) (c + adv) (by omega) (by omega)
      refine ⟨?_, hb, hc', hd⟩
      refine AllOk.cons (by simp only [encCap]; omega)
        (AllOk.cons (by simp only [encCap]; omega) ha)
    · refine ⟨AllOk.nil _, by simp only; omega, by simp only; omega, by simp only; omega⟩

theorem avx2Loop_spec (n lim : Nat) (hlim : 28 ≤ lim) : ∀ len o c, 3 * o = 4 * c →
    c + len = n → 24 ≤ len →
    AllOk (encCap n) (avx2Loop lim o c len).1 ∧
    3 * (avx2Loop lim o c len).2.1 = 4 * (avx2Loop lim o c len).2.2.1 ∧
    (avx2Loop lim o c len).2.2.1 + (avx2Loop lim o c len).2.2.2 = n := by
  intro len
  induction len using Nat.strongRecOn with
  | _ len ih =>
    intro o c h hc h24
    unfold avx2Loop
    split
    · exact ⟨AllOk.single (by simp only [encCap]; omega), by simp only; omega,
        by simp only; omega⟩
    · rename_i hl
      obtain ⟨ha, hb, hc'⟩ := ih (len - 24) (by omega) (o + 32) (c + 24) (by omega) (by omega)
        (by omega)
      exact ⟨AllOk.cons (by simp only [encCap]; omega)
        (AllOk.cons (by simp only [encCap]; omega) ha), hb, hc'⟩

theorem encScalar_ok (n : Nat) (nopad : Bool) : AllOk (encCap n) (encScalar n nopad) :=
  encodeImpl_ok n 0 0 n nopad (by omega) (by omega)

theorem neonImplG_ok (lim n o c inl : Nat) (nopad : Bool) (hlim : 48 ≤ lim) (h : 3 * o = 4 * c)
    (hc : c + inl = n) : AllOk (encCap n) (neonImplG lim o c inl nopad) := by
  unfold neonImplG
  split
  · obtain ⟨ha, hb, hc', _⟩ := wloop_spec n lim 48 64 48 (by decide) hlim (by omega) (by decide) inl o c h hc
    exact AllOk.append ha (encodeImpl_ok n _ _ _ nopad hb hc')
  · exact encodeImpl_ok n o c inl nopad h hc

theorem encNeonG_ok (lim n : Nat) (nopad : Bool) (hlim : 48 ≤ lim) :
    AllOk (encCap n) (encNeonG lim n nopad) :=
  neonImplG_ok lim n 0 0 n nopad hlim (by omega) (by omega)

theorem encSsse3G_ok (lim n : Nat) (nopad : Bool) (hlim : 16 ≤ lim) :
    AllOk (encCap n) (encSsse3G lim n nopad) := by
  obtain ⟨ha, hb, hc, _⟩ :=
    wloop_spec n lim 12 16 16 (by decide) hlim (by omega) (by decide) n 0 0 (by omega) (by omega)
  exact AllOk.append ha (encodeImpl_ok n _ _ _ nopad hb hc)

theorem encAvx2G_ok (first lim n : Nat) (nopad : Bool) (hf : 32 ≤ first) (hlim : 28 ≤ lim) :
    AllOk (encCap n) (encAvx2G first lim n nopad) := by
  unfold encAvx2G
  split
  · rename_i hn
    obtain ⟨ha, hb, hc⟩ := avx2Loop_spec n lim hlim n 0 0 (by omega) (by omega) (by omega)
    exact AllOk.append (AllOk.cons (by simp only [encCap]; omega) ha)
      (encodeImpl_ok n _ _ _ nopad hb hc)
  · exact encodeImpl_ok n 0 0 n nopad (by omega) (by omega)

theorem encAvx512G_ok (lim n : Nat) (nopad : Bool) (hlim : 64 ≤ lim) :
    AllOk (encCap n) (encAvx512G lim n nopad) := by
  obtain ⟨ha, hb, hc, _⟩ :=
    wloop_spec n lim 48 64 64 (by decide) hlim (by omega) (by decide) n 0 0 (by omega) (by omega)
  exact AllOk.append ha (encodeImpl_ok n _ _ _ nopad hb hc)

/-- The VBMI tail lengths are 2 to 64, so the shifts `UINT64_MAX >> (64 - x)`
are defined, and `out_len` bytes end within the `4 * ⌈len / 3⌉` left. -/
theorem vbmi_lengths (len : Nat) (nopad : Bool) (h0 : 0 < len) (h48 : len < 48) :
    2 ≤ vbmiData len ∧ vbmiData len ≤ vbmiOut len nopad ∧ vbmiOut len nopad ≤ vbmiFull len ∧
      vbmiFull len ≤ 64 := by
  unfold vbmiOut vbmiData vbmiFull
  cases nopad <;> simp only [Bool.false_eq_true, ite_true, ite_false] <;> omega

theorem encVbmiG_ok (lim lim2 n : Nat) (nopad : Bool) (hlim : lim = 64) (hlim2 : lim2 = 48) :
    AllOk (encCap n) (encVbmiG lim lim2 n nopad) := by
  obtain ⟨ha, hb, hc, hd⟩ :=
    wloop_spec n lim 48 64 64 (by decide) (by omega) (by omega) (by decide) n 0 0 (by omega) (by omega)
  unfold encVbmiG
  simp only
  generalize (wloop lim 48 64 64 _ 0 0 n).2.1 = o at hb hc hd ⊢
  generalize (wloop lim 48 64 64 _ 0 0 n).2.2.1 = c at hb hc hd ⊢
  generalize (wloop lim 48 64 64 _ 0 0 n).2.2.2 = len at hb hc hd ⊢
  -- after the optional masked step: 3 * o2 = 4 * c2, c2 + len2 = n, len2 < 48
  have hs : ∀ s : List Store × Nat × Nat × Nat,
      s = (if lim2 ≤ len then
        (([⟨.input, c, 48⟩, ⟨.out, o, 64⟩] : List Store), o + 64, c + 48, len - 48)
        else ([], o, c, len)) →
      AllOk (encCap n) s.1 ∧ 3 * s.2.1 = 4 * s.2.2.1 ∧ s.2.2.1 + s.2.2.2 = n ∧
        (s.2.2.2 < 48) := by
    intro s hs
    subst hs
    split
    · exact ⟨AllOk.cons (by simp only [encCap]; omega)
        (AllOk.single (by simp only [encCap]; omega)), by simp only; omega, by simp only; omega,
        by simp only; omega⟩
    · exact ⟨AllOk.nil _, by simp only; omega, by simp only; omega, by simp only; omega⟩
  obtain ⟨hs1, hs2, hs3, hs4⟩ := hs _ rfl
  generalize (if lim2 ≤ len then
    (([⟨.input, c, 48⟩, ⟨.out, o, 64⟩] : List Store), o + 64, c + 48, len - 48)
    else ([], o, c, len)) = s at hs1 hs2 hs3 hs4 ⊢
  refine AllOk.append (AllOk.append (AllOk.append ha hs1) ?_) ?_
  · split
    · rename_i hpos
      have := vbmi_lengths s.2.2.2 nopad hpos hs4
      refine AllOk.cons (by simp only [encCap]; omega) (AllOk.single ?_)
      simp only [encCap, vbmiFull] at this ⊢
      omega
    · exact AllOk.nil _
  · apply AllOk.single
    simp only [encCap]
    split
    · rename_i hpos
      have := vbmi_lengths s.2.2.2 nopad hpos hs4
      simp only [vbmiFull] at this ⊢
      omega
    · simp only; omega

theorem encNeon_ok (n : Nat) (nopad : Bool) : AllOk (encCap n) (encNeon n nopad) :=
  encNeonG_ok 48 n nopad (by decide)
theorem encSsse3_ok (n : Nat) (nopad : Bool) : AllOk (encCap n) (encSsse3 n nopad) :=
  encSsse3G_ok 16 n nopad (by decide)
theorem encAvx2_ok (n : Nat) (nopad : Bool) : AllOk (encCap n) (encAvx2 n nopad) :=
  encAvx2G_ok 32 28 n nopad (by decide) (by decide)
theorem encAvx512_ok (n : Nat) (nopad : Bool) : AllOk (encCap n) (encAvx512 n nopad) :=
  encAvx512G_ok 64 n nopad (by decide)
theorem encVbmi_ok (n : Nat) (nopad : Bool) : AllOk (encCap n) (encVbmi n nopad) :=
  encVbmiG_ok 64 48 n nopad rfl rfl

/-- The stores alone need no margin: every vector store is exact, so the
`out` accesses of a vector loop stay in the buffer for any `lim`, even
`lim = adv`. Only the loads set the loop tests. -/
theorem wloop_out (n lim adv w ld : Nat) (h1 : 0 < adv) (hadv : adv ≤ lim)
    (hw : 3 * w = 4 * adv) :
    ∀ len o c, 3 * o = 4 * c → c + len = n →
      ∀ s ∈ (wloop lim adv w ld h1 o c len).1, s.buf = .out →
        s.off + s.len ≤ 4 * ((n + 2) / 3) := by
  intro len
  induction len using Nat.strongRecOn with
  | _ len ih =>
    intro o c h hc s hs hb
    unfold wloop at hs
    split at hs
    · rename_i hl
      simp only [show adv ≤ len by omega, ↓reduceDIte] at hs
      simp only [List.mem_cons] at hs
      rcases hs with rfl | rfl | hs
      · simp at hb
      · simp only; omega
      · exact ih (len - adv) (by omega) (o + w) (c + adv) (by omega) (by omega) s hs hb
    · simp at hs

end Base64Safety
