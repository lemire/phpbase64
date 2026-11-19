import Base64Safety.Basic

/-
The encoders of `ext/standard/base64.c`. Each allocates
`zend_string_safe_alloc((length + 2) / 3, 4, 0, 0)`: `4 * ⌈n / 3⌉` bytes and
the terminating byte. Every vector loop stores `w` bytes for `3 * w / 4` input
bytes, so `3 * o + 4 * len = 4 * n` holds throughout, with `o` the bytes
written and `len` the bytes left.
-/

namespace Base64Safety

/-- The size of the encoder's output buffer. Only `out` is written. -/
def encCap (n : Nat) : Buf → Nat
  | .out => 4 * ((n + 2) / 3) + 1
  | _ => 0

def one (j : Nat) : Store := ⟨.out, j, 1⟩

/-- `while (inl > 2) { *out++ = ...; (4 times) in += 3; inl -= 3; }` in
`php_base64_encode_impl`: the stores, the final `out` and `inl`. -/
def implLoop (o inl : Nat) : List Store × Nat × Nat :=
  if _h : inl > 2 then
    let r := implLoop (o + 4) (inl - 3)
    ([one o, one (o + 1), one (o + 2), one (o + 3)] ++ r.1, r.2)
  else ([], o, inl)
termination_by inl
decreasing_by omega

/-- `php_base64_encode_impl` after its NEON prefix: the loop, the last one or
two bytes with their padding, and `*out = '\0'`. -/
def encodeImpl (o inl : Nat) (nopad : Bool) : List Store :=
  let r := implLoop o inl
  let o1 := r.2.1
  let rest := r.2.2
  let tail : List Store :=
    if rest = 0 then []
    else if rest > 1 then
      [one o1, one (o1 + 1), one (o1 + 2)] ++ (if nopad then [] else [one (o1 + 3)])
    else
      [one o1, one (o1 + 1)] ++ (if nopad then [] else [one (o1 + 2), one (o1 + 3)])
  let o2 := o1 + (if rest = 0 then 0 else if rest > 1 then (if nopad then 3 else 4)
    else (if nopad then 2 else 4))
  r.1 ++ tail ++ [one o2]

/-- `while (len >= lim) { store w bytes at o; o += w; len -= adv; }`: the
SSSE3 loop (`lim = 16`, `adv = 12`, `w = 16`), the AVX-512 loop and the main
AVX-512 VBMI loop (`64`, `48`, `64`), and the NEON loop (`48`, `48`, `64`),
whose `do { } while` runs behind an equivalent `if`. -/
def wloop (lim adv w : Nat) (h1 : 0 < adv) (h2 : adv ≤ lim) (o len : Nat) :
    List Store × Nat × Nat :=
  if _h : lim ≤ len then
    let r := wloop lim adv w h1 h2 (o + w) (len - adv)
    (⟨.out, o, w⟩ :: r.1, r.2)
  else ([], o, len)
termination_by len
decreasing_by omega

/-- The AVX2 loop, entered when `length > 31`:
`for (;;) { store 32 bytes; c += 24; o += 32; length -= 24; if (length < 28) break; }` -/
def avx2Loop (o len : Nat) : List Store × Nat × Nat :=
  if h : len - 24 < 28 then ([⟨.out, o, 32⟩], o + 32, len - 24)
  else
    let r := avx2Loop (o + 32) (len - 24)
    (⟨.out, o, 32⟩ :: r.1, r.2)
termination_by len
decreasing_by omega

/-! ## The encoders -/

/-- `php_base64_encode_impl` on aarch64: the NEON loop when `inl >= 48`. -/
def neonImpl (o inl : Nat) (nopad : Bool) : List Store :=
  if inl ≥ 48 then
    let r := wloop 48 48 64 (by decide) (by decide) o inl
    r.1 ++ encodeImpl r.2.1 r.2.2 nopad
  else encodeImpl o inl nopad

/-- Without SIMD (x86 fallback). -/
def encScalar (n : Nat) (nopad : Bool) : List Store := encodeImpl 0 n nopad

/-- The default encoder on aarch64. -/
def encNeon (n : Nat) (nopad : Bool) : List Store := neonImpl 0 n nopad

def encSsse3 (n : Nat) (nopad : Bool) : List Store :=
  let r := wloop 16 12 16 (by decide) (by decide) 0 n
  r.1 ++ encodeImpl r.2.1 r.2.2 nopad

def encAvx2 (n : Nat) (nopad : Bool) : List Store :=
  if n > 31 then
    let r := avx2Loop 0 n
    r.1 ++ encodeImpl r.2.1 r.2.2 nopad
  else encodeImpl 0 n nopad

def encAvx512 (n : Nat) (nopad : Bool) : List Store :=
  let r := wloop 64 48 64 (by decide) (by decide) 0 n
  r.1 ++ encodeImpl r.2.1 r.2.2 nopad

/-- The lengths of the AVX-512 VBMI tail, for `0 < len < 48` bytes left. -/
def vbmiFull (len : Nat) : Nat := ((len + 2) / 3) * 4
def vbmiData (len : Nat) : Nat := vbmiFull len - (3 - len % 3) % 3
def vbmiOut (len : Nat) (nopad : Bool) : Nat := if nopad then vbmiData len else vbmiFull len

/-- `php_base64_encode_avx512_vbmi`: the main loop, one more 64-byte step if
48 bytes are left, then a masked store of `out_len` bytes, then the
terminating byte. -/
def encVbmi (n : Nat) (nopad : Bool) : List Store :=
  let r := wloop 64 48 64 (by decide) (by decide) 0 n
  let o := r.2.1
  let len := r.2.2
  let s : List Store × Nat × Nat :=
    if len ≥ 48 then ([⟨.out, o, 64⟩], o + 64, len - 48) else ([], o, len)
  let o2 := s.2.1
  let len2 := s.2.2
  let t : List Store × Nat :=
    if len2 > 0 then ([⟨.out, o2, vbmiOut len2 nopad⟩], o2 + vbmiOut len2 nopad) else ([], o2)
  r.1 ++ s.1 ++ t.1 ++ [one t.2]

/-! ## Proofs -/

theorem implLoop_spec (o : Nat) : ∀ inl,
    (∀ s ∈ (implLoop o inl).1, s.buf = .out ∧ s.off + s.len ≤ o + 4 * (inl / 3)) ∧
    (implLoop o inl).2.1 = o + 4 * (inl / 3) ∧ (implLoop o inl).2.2 = inl % 3 := by
  intro inl
  induction inl using Nat.strongRecOn generalizing o with
  | _ inl ih =>
    unfold implLoop
    split
    · rename_i h
      obtain ⟨ha, hb, hc⟩ := ih (inl - 3) (by omega) (o + 4)
      refine ⟨?_, ?_, ?_⟩
      · intro s hs
        rcases List.mem_append.mp hs with hs | hs
        · simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
          rcases hs with rfl | rfl | rfl | rfl <;> exact ⟨rfl, by simp only [one]; omega⟩
        · obtain ⟨h1, h2⟩ := ha s hs
          exact ⟨h1, by omega⟩
      · simp only; rw [hb]; omega
      · simp only; rw [hc]; omega
    · refine ⟨by simp, ?_, ?_⟩ <;> simp only <;> omega

theorem encodeImpl_ok (n o inl : Nat) (nopad : Bool) (h : 3 * o + 4 * inl = 4 * n) :
    AllOk (encCap n) (encodeImpl o inl nopad) := by
  obtain ⟨ha, hb, hc⟩ := implLoop_spec o inl
  have key0 : o + 4 * (inl / 3) ≤ 4 * ((n + 2) / 3) := by omega
  have key1 : inl % 3 ≠ 0 → o + 4 * (inl / 3) + 4 ≤ 4 * ((n + 2) / 3) := by omega
  unfold encodeImpl
  simp only
  rw [hb, hc]
  refine AllOk.append (AllOk.append ?_ ?_) ?_
  · intro s hs
    obtain ⟨h1, h2⟩ := ha s hs
    rw [h1]; simp only [encCap]; omega
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

theorem wloop_spec (n lim adv w : Nat) (h1 : 0 < adv) (h2 : adv ≤ lim)
    (hw : 3 * w = 4 * adv) : ∀ len o, 3 * o + 4 * len = 4 * n →
      AllOk (encCap n) (wloop lim adv w h1 h2 o len).1 ∧
      3 * (wloop lim adv w h1 h2 o len).2.1 + 4 * (wloop lim adv w h1 h2 o len).2.2 = 4 * n ∧
      (wloop lim adv w h1 h2 o len).2.2 < lim := by
  intro len
  induction len using Nat.strongRecOn with
  | _ len ih =>
    intro o h
    unfold wloop
    split
    · rename_i hl
      obtain ⟨ha, hb, hc⟩ := ih (len - adv) (by omega) (o + w) (by omega)
      refine ⟨?_, hb, hc⟩
      intro s hs
      simp only [List.mem_cons] at hs
      rcases hs with rfl | hs
      · simp only [encCap]; omega
      · exact ha s hs
    · refine ⟨AllOk.nil _, by simp only; omega, by simp only; omega⟩

theorem avx2Loop_spec (n : Nat) : ∀ len o, 3 * o + 4 * len = 4 * n → 24 ≤ len →
    AllOk (encCap n) (avx2Loop o len).1 ∧
    3 * (avx2Loop o len).2.1 + 4 * (avx2Loop o len).2.2 = 4 * n := by
  intro len
  induction len using Nat.strongRecOn with
  | _ len ih =>
    intro o h h24
    unfold avx2Loop
    split
    · refine ⟨AllOk.single (by simp only [encCap]; omega), by simp only; omega⟩
    · rename_i hl
      obtain ⟨ha, hb⟩ := ih (len - 24) (by omega) (o + 32) (by omega) (by omega)
      refine ⟨?_, hb⟩
      intro s hs
      simp only [List.mem_cons] at hs
      rcases hs with rfl | hs
      · simp only [encCap]; omega
      · exact ha s hs

theorem encScalar_ok (n : Nat) (nopad : Bool) : AllOk (encCap n) (encScalar n nopad) :=
  encodeImpl_ok n 0 n nopad (by omega)

theorem neonImpl_ok (n o inl : Nat) (nopad : Bool) (h : 3 * o + 4 * inl = 4 * n) :
    AllOk (encCap n) (neonImpl o inl nopad) := by
  unfold neonImpl
  split
  · obtain ⟨ha, hb, _⟩ := wloop_spec n 48 48 64 (by decide) (by decide) (by decide) inl o h
    exact AllOk.append ha (encodeImpl_ok n _ _ nopad hb)
  · exact encodeImpl_ok n o inl nopad h

theorem encNeon_ok (n : Nat) (nopad : Bool) : AllOk (encCap n) (encNeon n nopad) :=
  neonImpl_ok n 0 n nopad (by omega)

theorem encSsse3_ok (n : Nat) (nopad : Bool) : AllOk (encCap n) (encSsse3 n nopad) := by
  obtain ⟨ha, hb, _⟩ := wloop_spec n 16 12 16 (by decide) (by decide) (by decide) n 0 (by omega)
  exact AllOk.append ha (encodeImpl_ok n _ _ nopad hb)

theorem encAvx2_ok (n : Nat) (nopad : Bool) : AllOk (encCap n) (encAvx2 n nopad) := by
  unfold encAvx2
  split
  · obtain ⟨ha, hb⟩ := avx2Loop_spec n n 0 (by omega) (by omega)
    exact AllOk.append ha (encodeImpl_ok n _ _ nopad hb)
  · exact encodeImpl_ok n 0 n nopad (by omega)

theorem encAvx512_ok (n : Nat) (nopad : Bool) : AllOk (encCap n) (encAvx512 n nopad) := by
  obtain ⟨ha, hb, _⟩ := wloop_spec n 64 48 64 (by decide) (by decide) (by decide) n 0 (by omega)
  exact AllOk.append ha (encodeImpl_ok n _ _ nopad hb)

/-- The VBMI tail lengths are 2 to 64, so the shifts `UINT64_MAX >> (64 - x)`
are defined, and `out_len` bytes end within the `4 * ⌈len / 3⌉` left. -/
theorem vbmi_lengths (len : Nat) (nopad : Bool) (h0 : 0 < len) (h48 : len < 48) :
    2 ≤ vbmiData len ∧ vbmiData len ≤ vbmiOut len nopad ∧ vbmiOut len nopad ≤ vbmiFull len ∧
      vbmiFull len ≤ 64 := by
  unfold vbmiOut vbmiData vbmiFull
  cases nopad <;> simp only [Bool.false_eq_true, ite_true, ite_false] <;> omega

theorem encVbmi_ok (n : Nat) (nopad : Bool) : AllOk (encCap n) (encVbmi n nopad) := by
  obtain ⟨ha, hb, hc⟩ := wloop_spec n 64 48 64 (by decide) (by decide) (by decide) n 0 (by omega)
  unfold encVbmi
  simp only
  generalize (wloop 64 48 64 _ _ 0 n).2.1 = o at hb hc ⊢
  generalize (wloop 64 48 64 _ _ 0 n).2.2 = len at hb hc ⊢
  -- after the optional 64-byte step: 3 * o2 + 4 * len2 = 4 * n, len2 < 48
  have hs : AllOk (encCap n)
      (if len ≥ 48 then (([⟨.out, o, 64⟩] : List Store), o + 64, len - 48) else ([], o, len)).1 ∧
      3 * (if len ≥ 48 then (([⟨.out, o, 64⟩] : List Store), o + 64, len - 48)
        else ([], o, len)).2.1
        + 4 * (if len ≥ 48 then (([⟨.out, o, 64⟩] : List Store), o + 64, len - 48)
          else ([], o, len)).2.2 = 4 * n ∧
      (if len ≥ 48 then (([⟨.out, o, 64⟩] : List Store), o + 64, len - 48)
        else ([], o, len)).2.2 < 48 := by
    split
    · exact ⟨AllOk.single (by simp only [encCap]; omega), by simp only; omega,
        by simp only; omega⟩
    · exact ⟨AllOk.nil _, by simp only; omega, by simp only; omega⟩
  obtain ⟨hs1, hs2, hs3⟩ := hs
  generalize (if len ≥ 48 then (([⟨.out, o, 64⟩] : List Store), o + 64, len - 48)
    else ([], o, len)) = s at hs1 hs2 hs3 ⊢
  refine AllOk.append (AllOk.append (AllOk.append ha hs1) ?_) ?_
  · split
    · rename_i hpos
      have := vbmi_lengths s.2.2 nopad hpos hs3
      apply AllOk.single
      simp only [encCap, vbmiFull] at this ⊢
      omega
    · exact AllOk.nil _
  · apply AllOk.single
    simp only [encCap]
    split
    · rename_i hpos
      have := vbmi_lengths s.2.2 nopad hpos hs3
      simp only [vbmiFull] at this ⊢
      omega
    · simp only; omega

end Base64Safety
