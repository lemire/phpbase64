/-
The store model shared by the decoder and the encoder.

An access reads or writes `len` consecutive bytes at offset `off` of a
buffer. Loads are the accesses to `input` and the reads of `pending` and
`last`; the model does not need to tell them apart from stores, since the
bound is the same. A vector store (`_mm_storeu_si128`, `vst1q_u8`, `vst3q_u8`, ...) is one store of the
vector's width, whatever its lanes hold; a masked AVX-512 store is a store of
the bytes its mask selects, and a `memcpy` or `memset` of `n` bytes is a store
of `n` bytes. A masked AVX-512 load reads the bytes its mask selects. An
access is in bounds when it ends at or before the buffer size.
-/

namespace Base64Safety

/-- The buffers the code writes to. -/
inductive Buf where
  /-- The character array of the result `zend_string`. -/
  | out
  /-- The decoder's stack array `pending`, seen as bytes (`buffer`). -/
  | pending
  /-- The decoder's stack array `last[64]`. -/
  | last
  /-- The input string, which is only read. -/
  | input
deriving DecidableEq, Repr

structure Store where
  buf : Buf
  off : Nat
  len : Nat
deriving Repr

/-- Every store of `l` ends inside its buffer, whose size is given by `cap`. -/
def AllOk (cap : Buf → Nat) (l : List Store) : Prop :=
  ∀ s ∈ l, s.off + s.len ≤ cap s.buf

theorem AllOk.nil (cap : Buf → Nat) : AllOk cap [] := by
  simp [AllOk]

theorem AllOk.append {cap : Buf → Nat} {l₁ l₂ : List Store}
    (h₁ : AllOk cap l₁) (h₂ : AllOk cap l₂) : AllOk cap (l₁ ++ l₂) := by
  intro s hs
  rcases List.mem_append.mp hs with h | h
  · exact h₁ s h
  · exact h₂ s h

theorem AllOk.single {cap : Buf → Nat} {b : Buf} {off len : Nat}
    (h : off + len ≤ cap b) : AllOk cap [⟨b, off, len⟩] := by
  intro s hs
  simp at hs
  subst hs
  exact h

theorem AllOk.mono {cap cap' : Buf → Nat} {l : List Store} (h : AllOk cap l)
    (hc : ∀ b, cap b ≤ cap' b) : AllOk cap' l :=
  fun s hs => Nat.le_trans (h s hs) (hc s.buf)

theorem AllOk.cons {cap : Buf → Nat} {s : Store} {l : List Store}
    (h : s.off + s.len ≤ cap s.buf) (hl : AllOk cap l) : AllOk cap (s :: l) := by
  intro x hx
  rcases List.mem_cons.mp hx with rfl | hx
  · exact h
  · exact hl x hx

/-- The stores of a helper, given as (offset, width) pairs relative to its
destination pointer `base`. -/
def place (b : Buf) (base : Nat) (l : List (Nat × Nat)) : List Store :=
  l.map fun p => ⟨b, base + p.1, p.2⟩

/-- If every store of a helper ends within `w` bytes of its destination, and
`w` bytes fit at `base`, the helper's stores are in bounds. -/
theorem place_ok {cap : Buf → Nat} {b : Buf} {base w : Nat} {l : List (Nat × Nat)}
    (hl : ∀ p ∈ l, p.1 + p.2 ≤ w) (hb : base + w ≤ cap b) :
    AllOk cap (place b base l) := by
  intro s hs
  simp only [place, List.mem_map] at hs
  obtain ⟨p, hp, rfl⟩ := hs
  have := hl p hp
  simp only
  omega

/-- `php_base64_copy_short(dst, src, n)`: overlapping copies of fixed size. -/
def copyShort (b : Buf) (base n : Nat) : List Store :=
  if n ≥ 32 then [⟨b, base, 32⟩, ⟨b, base + n - 32, 32⟩]
  else if n ≥ 16 then [⟨b, base, 16⟩, ⟨b, base + n - 16, 16⟩]
  else if n ≥ 8 then [⟨b, base, 8⟩, ⟨b, base + n - 8, 8⟩]
  else if n ≥ 4 then [⟨b, base, 4⟩, ⟨b, base + n - 4, 4⟩]
  else if n > 0 then [⟨b, base, 1⟩, ⟨b, base + n / 2, 1⟩, ⟨b, base + n - 1, 1⟩]
  else []

/-- `copy_short` writes only inside `[base, base + n)`. -/
theorem copyShort_ok {cap : Buf → Nat} {b : Buf} {base n : Nat}
    (h : base + n ≤ cap b) : AllOk cap (copyShort b base n) := by
  intro s hs
  unfold copyShort at hs
  split at hs
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl <;> simp only <;> omega
  split at hs
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl <;> simp only <;> omega
  split at hs
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl <;> simp only <;> omega
  split at hs
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl <;> simp only <;> omega
  split at hs
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl | rfl <;> simp only <;> omega
  · simp at hs

/-! ## The scalar decoder

`php_base64_decode_put` and `php_base64_decode_loop`: the `i`-th alphabet
character (counting from 0) is stored at `out[j]`, and for `i % 4` equal to 1
or 2 also at `out[j + 1]`, after which `j` moves on. Characters outside the
alphabet store nothing, so only the alphabet characters are modelled. -/

/-- One call of `php_base64_decode_put(out, &j, i, ch)`: its stores and the
new `j`. -/
def put (j i : Nat) : List Store × Nat :=
  if i % 4 = 0 then ([⟨.out, j, 1⟩], j)
  else if i % 4 = 1 then ([⟨.out, j, 1⟩, ⟨.out, j + 1, 1⟩], j + 1)
  else if i % 4 = 2 then ([⟨.out, j, 1⟩, ⟨.out, j + 1, 1⟩], j + 1)
  else ([⟨.out, j, 1⟩], j + 1)

/-- `m` successive calls of `put`, for the characters `i`, ..., `i + m - 1`. -/
def scalar (j i : Nat) : Nat → List Store × Nat
  | 0 => ([], j)
  | m + 1 =>
    let r := put j i
    let r' := scalar r.2 (i + 1) m
    (r.1 ++ r'.1, r'.2)

/-- The value of `j` before character `i`, when it was `j0` before character 0. -/
def jOf (j0 i : Nat) : Nat := j0 + 3 * (i / 4) + (i % 4 - 1)

/-- Every store of `put` at character `i`, with `j` in step, writes `out` and
ends at most at `j0 + i + 1`, and within `(3 * (i + 1) + 3) / 4` of `j0`. -/
def PutBound (j0 i : Nat) (s : Store) : Prop :=
  s.buf = .out ∧ s.off + s.len ≤ j0 + i + 1 ∧ 4 * (s.off + s.len) ≤ 4 * j0 + 3 * (i + 1) + 3

theorem put_spec (j0 i : Nat) :
    (∀ s ∈ (put (jOf j0 i) i).1, PutBound j0 i s) ∧ (put (jOf j0 i) i).2 = jOf j0 (i + 1) := by
  unfold put jOf PutBound
  have h4 : i % 4 < 4 := Nat.mod_lt _ (by decide)
  have hd : i = 4 * (i / 4) + i % 4 := (Nat.div_add_mod i 4).symm
  have hd' : i + 1 = 4 * ((i + 1) / 4) + (i + 1) % 4 := (Nat.div_add_mod (i + 1) 4).symm
  split
  · refine ⟨?_, by omega⟩
    intro s hs
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
    subst hs; exact ⟨rfl, by simp only; omega, by simp only; omega⟩
  · split
    · refine ⟨?_, by omega⟩
      intro s hs
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
      rcases hs with rfl | rfl <;> exact ⟨rfl, by simp only; omega, by simp only; omega⟩
    · split
      · refine ⟨?_, by omega⟩
        intro s hs
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
        rcases hs with rfl | rfl <;> exact ⟨rfl, by simp only; omega, by simp only; omega⟩
      · refine ⟨?_, by omega⟩
        intro s hs
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
        subst hs; exact ⟨rfl, by simp only; omega, by simp only; omega⟩

/-- The scalar decoder, from character `i` on, writes only `out`, ends below
`j0 + i + m` and below `3/4` of the characters plus 3/4, where `j0` is the value
of `j` before character 0, and ends with `j` in step. -/
theorem scalar_spec (j0 : Nat) : ∀ m i,
    (∀ s ∈ (scalar (jOf j0 i) i m).1,
      s.buf = .out ∧ s.off + s.len ≤ j0 + i + m ∧ 4 * (s.off + s.len) ≤ 4 * j0 + 3 * (i + m) + 3) ∧
    (scalar (jOf j0 i) i m).2 = jOf j0 (i + m) := by
  intro m
  induction m with
  | zero => intro i; exact ⟨by simp [scalar], rfl⟩
  | succ m ih =>
    intro i
    obtain ⟨hp, hj⟩ := put_spec j0 i
    simp only [scalar]
    rw [hj]
    obtain ⟨hs, hj'⟩ := ih (i + 1)
    refine ⟨?_, ?_⟩
    · intro s hs'
      rcases List.mem_append.mp hs' with h | h
      · obtain ⟨h1, h2, h3⟩ := hp s h
        exact ⟨h1, by omega, by omega⟩
      · obtain ⟨h1, h2, h3⟩ := hs s h
        exact ⟨h1, by omega, by omega⟩
    · rw [hj']; congr 1; omega

theorem jOf_le (j0 i : Nat) : jOf j0 i ≤ j0 + i ∧ 4 * jOf j0 i ≤ 4 * j0 + 3 * i := by
  unfold jOf
  have := Nat.div_add_mod i 4
  have : i % 4 < 4 := Nat.mod_lt _ (by decide)
  omega

theorem jOf_zero (j0 : Nat) : jOf j0 0 = j0 := by
  simp [jOf]

end Base64Safety
