import Base64Safety.Decode
import Base64Safety.Encode

/-
Tightness: every bound of `decode_tight` is reached, and every loop test of
the encoders is the smallest that keeps the loads inside the input.
-/

namespace Base64Safety

/-- An access that ends past its buffer. -/
def Over (cap : Buf → Nat) (l : List Store) : Prop := ∃ s ∈ l, cap s.buf < s.off + s.len

theorem not_allOk {cap : Buf → Nat} {l : List Store} (h : Over cap l) : ¬ AllOk cap l := by
  intro ha
  obtain ⟨s, hs, hlt⟩ := h
  have := ha s hs
  omega

/-! ## The decoder: each bound is reached -/

def q16 : Quarters := ⟨16, 16, 16, 16, by decide, by decide, by decide, by decide⟩
def q63 : Quarters := ⟨15, 16, 16, 16, by decide, by decide, by decide, by decide⟩
def qTail : Quarters := ⟨16, 16, 16, 15, by decide, by decide, by decide, by decide⟩
def qStep : Quarters := ⟨16, 0, 0, 0, by decide, by decide, by decide, by decide⟩

/-- 575 bytes: a block with one byte outside the alphabet, seven blocks of
alphabet characters, and 63 alphabet characters. 511 values are pending
after the blocks. -/
def pendingWitness : DecIn :=
  ⟨⟨q63, false⟩ :: List.replicate 7 ⟨q16, false⟩, 63, qTail, 0, 0⟩

/-- 64 alphabet characters. -/
def cleanBlock : DecIn := ⟨[⟨q16, false⟩], 0, ⟨0, 0, 0, 0, by decide, by decide, by decide, by decide⟩, 0, 0⟩

/-- 16 alphabet characters, decoded by one `step16`. -/
def cleanStep : DecIn := ⟨[], 16, qStep, 1, 0⟩

theorem pendingWitness_valid : pendingWitness.Valid := by unfold DecIn.Valid; decide
theorem cleanBlock_valid : cleanBlock.Valid := by unfold DecIn.Valid; decide
theorem cleanStep_valid : cleanStep.Valid := by unfold DecIn.Valid; decide

/-- `pending` is written up to byte 638 on every instruction set: an array of
nine blocks (576 bytes) would not do, and the bound 638 cannot be lowered. -/
theorem pending_reached (isa : Isa) (h : isa ∈ [ssse3, avx2, avx512vbmi, neon]) :
    ∃ s ∈ decode isa pendingWitness, s.buf = .pending ∧ s.off + s.len = 638 := by
  simp only [List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with rfl | rfl | rfl | rfl <;> decide

/-- `pack` reaches `⌊3n/4⌋ + slack` with `n = 64`: 52 bytes for SSSE3, 56 for
AVX2, 64 for AVX-512 VBMI (that is, all of `n`). -/
theorem out_reached_ssse3 :
    ∃ s ∈ decode ssse3 cleanBlock, s.buf = .out ∧ s.off + s.len = outCap ssse3 cleanBlock.len := by
  decide
theorem out_reached_avx2 :
    ∃ s ∈ decode avx2 cleanBlock, s.buf = .out ∧ s.off + s.len = outCap avx2 cleanBlock.len := by
  decide
theorem out_reached_avx512vbmi :
    ∃ s ∈ decode avx512vbmi cleanBlock, s.buf = .out ∧
      s.off + s.len = outCap avx512vbmi cleanBlock.len ∧ s.off + s.len = cleanBlock.len := by
  decide

/-- `step16` reaches `⌊3n/4⌋ + 4` with `n = 16`, the bound for SSSE3 and NEON,
and all of `n`, on every instruction set. -/
theorem out_reached_step (isa : Isa) (h : isa ∈ [ssse3, avx2, avx512vbmi, neon]) :
    ∃ s ∈ decode isa cleanStep, s.buf = .out ∧ 4 * (s.off + s.len) = 3 * cleanStep.len + 4 * 4 ∧
      s.off + s.len = cleanStep.len := by
  simp only [List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with rfl | rfl | rfl | rfl <;> decide

theorem out_reached_neon :
    ∃ s ∈ decode neon cleanStep, s.buf = .out ∧ s.off + s.len = outCap neon cleanStep.len := by
  decide

/-! ## The encoders: one less reads past the input

Each witness is the smallest input for which the loop with its test lowered
by one runs an iteration whose load ends past the input. The stores never set
the test (`wloop_out`): each vector iteration writes exactly what it encodes.
-/

theorem ssse3_tight : Over (encCap 15) (encSsse3G 15 15 false) :=
  ⟨⟨.input, 0, 16⟩, by simp [encSsse3G, wloop], by simp [encCap]⟩

theorem avx512_tight : Over (encCap 63) (encAvx512G 63 63 false) :=
  ⟨⟨.input, 0, 64⟩, by simp [encAvx512G, wloop], by simp [encCap]⟩

theorem neon_tight : Over (encCap 47) (encNeonG 47 47 false) :=
  ⟨⟨.input, 0, 48⟩, by simp [encNeonG, neonImplG, wloop], by simp [encCap]⟩

theorem vbmi_tight : Over (encCap 63) (encVbmiG 63 48 63 false) :=
  ⟨⟨.input, 0, 64⟩, by simp [encVbmiG, wloop], by simp [encCap]⟩

theorem vbmi_masked_tight : Over (encCap 47) (encVbmiG 64 47 47 false) :=
  ⟨⟨.input, 0, 48⟩, by simp [encVbmiG, wloop], by simp [encCap]⟩

theorem avx2_first_tight : Over (encCap 31) (encAvx2G 31 28 31 false) :=
  ⟨⟨.input, 0, 32⟩, by simp [encAvx2G], by simp [encCap]⟩

/-- With `length < 27` as the AVX2 break test, a 51-byte input runs a second
iteration whose load at `c - 4` ends one byte past the input. -/
theorem avx2_loop_tight : Over (encCap 51) (encAvx2G 32 27 51 false) :=
  ⟨⟨.input, 20, 32⟩, by simp [encAvx2G, avx2Loop], by simp [encCap]⟩

end Base64Safety
