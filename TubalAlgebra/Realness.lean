import TubalAlgebra.Defs

/-!
# Realness of the `⋆_M` product (Lemma 2, Lemma 7, Lemmas 63, 64, 65)

The proofs of Lemma 2 and Lemma 7 are delegated in the paper to Section 10; Lemma 2 is
restated there as Lemma 65.

We introduce the auxiliary notion `ConjPattern M y` ("the complex vector `y` respects the
conjugation pattern of `M`"): `y_j` is real whenever row `j` of `M` is real, and
`y_j = conj(y_k)` whenever row `j` of `M` is the conjugate of row `k`. For admissible `M`,
the vectors respecting the pattern are exactly the transforms `M a` of real vectors `a`.
-/

open Matrix Complex

noncomputable section

namespace Tubal

variable {n : ℕ}

/-- The complex vector `y` respects the conjugation pattern of the rows of `M`. -/
def ConjPattern (M : Matrix (Fin n) (Fin n) ℂ) (y : Fin n → ℂ) : Prop :=
  (∀ j, RowReal M j → (y j).im = 0) ∧ (∀ j k, RowConjOf M j k → y j = starRingEnd ℂ (y k))

/-! ### Section 10 -/

/-- **Lemma 63.** Suppose `M ∈ ℂ^{n×n}` is an invertible matrix for which every row is either
real, or is conjugate to exactly one other row. If row `j` in `M` is real, then column `j` of
`M⁻¹` is real as well. On the other hand, if row `j` is complex and conjugate to row `k`, then
columns `j` and `k` in `M⁻¹` are complex and conjugate to each other. -/
theorem lemma63 (M : Matrix (Fin n) (Fin n) ℂ) (hM : IsUnit M) (hrow : ConjRowCondition M) :
    (∀ j, RowReal M j → ∀ i, starRingEnd ℂ (M⁻¹ i j) = M⁻¹ i j) ∧
    (∀ j k, ¬ RowReal M j → RowConjOf M j k →
      (∀ i, M⁻¹ i j = starRingEnd ℂ (M⁻¹ i k)) ∧
      (∃ i, starRingEnd ℂ (M⁻¹ i j) ≠ M⁻¹ i j) ∧
      (∃ i, starRingEnd ℂ (M⁻¹ i k) ≠ M⁻¹ i k)) := by
  sorry

/-- **Lemma 64.** Suppose `M ∈ ℂ^{n×n}` is an invertible matrix for which every row is either
real, or is conjugate to exactly one other row. Then `M⁻¹ M̄` is real. -/
theorem lemma64 (M : Matrix (Fin n) (Fin n) ℂ) (hM : IsUnit M) (hrow : ConjRowCondition M) :
    ∃ R : Matrix (Fin n) (Fin n) ℝ, M⁻¹ * M.map (starRingEnd ℂ) = R.map (↑) := by
  sorry

/-- **Lemma 65** (= **Lemma 2**). Let `M ∈ ℂ^{n×n}` be an invertible matrix. The result of
Eq. (5) is real for every `a, b ∈ ℝⁿ`, if and only if every row of `M` is either real, or is
conjugate to exactly one other row of `M`. -/
theorem lemma65 (M : Matrix (Fin n) (Fin n) ℂ) (hM : IsUnit M) :
    (∀ a b : Fin n → ℝ, starMC M (toC a) (toC b) ∈ Set.range toC) ↔ ConjRowCondition M := by
  sorry

/-- **Lemma 2.** Let `M ∈ ℂ^{n×n}` be an invertible matrix. Then `a ⋆_M b ∈ ℝⁿ` for all
`a, b ∈ ℝⁿ`, if and only if every row of `M` is either real, or obtained by entry-wise complex
conjugation of exactly one other row of `M`. -/
theorem lemma2 (M : Matrix (Fin n) (Fin n) ℂ) (hM : IsUnit M) :
    (∀ a b : Fin n → ℝ, starMC M (toC a) (toC b) ∈ Set.range toC) ↔ ConjRowCondition M :=
  lemma65 M hM

/-- **Lemma 7.** Let `M ∈ ℂ^{n×n}` be an invertible matrix. Suppose that every row of `M` is
either real, or is conjugate to exactly one other row of `M`. Then `x⁻ = M⁻¹ (M x)⁺` is real,
for every `x ∈ ℝⁿ`. -/
theorem lemma7 (M : Matrix (Fin n) (Fin n) ℂ) (hM : IsUnit M) (hrow : ConjRowCondition M)
    (x : Fin n → ℝ) : M⁻¹ *ᵥ pinvVec (M *ᵥ toC x) ∈ Set.range toC := by
  sorry

/-! ### The conjugation pattern (auxiliary) -/

theorem conjPattern_mulVec_toC (M : Matrix (Fin n) (Fin n) ℂ) (a : Fin n → ℝ) :
    ConjPattern M (M *ᵥ toC a) := by
  sorry

/-- For admissible `M`, `M⁻¹ y` is real whenever `y` respects the conjugation pattern. -/
theorem inv_mulVec_mem_range_of_conjPattern (M : Matrix (Fin n) (Fin n) ℂ) (hM : IsUnit M)
    (hrow : ConjRowCondition M) {y : Fin n → ℂ} (hy : ConjPattern M y) :
    M⁻¹ *ᵥ y ∈ Set.range toC := by
  sorry

/-- For admissible `M`, the vectors respecting the conjugation pattern are exactly the
transforms `M a` of real vectors. -/
theorem conjPattern_iff_mem_range (M : Matrix (Fin n) (Fin n) ℂ) (hM : IsUnit M)
    (hrow : ConjRowCondition M) (y : Fin n → ℂ) :
    ConjPattern M y ↔ ∃ a : Fin n → ℝ, y = M *ᵥ toC a := by
  sorry

theorem ConjPattern.mul {M : Matrix (Fin n) (Fin n) ℂ} {y z : Fin n → ℂ}
    (hy : ConjPattern M y) (hz : ConjPattern M z) : ConjPattern M (y * z) := by
  sorry

theorem ConjPattern.add {M : Matrix (Fin n) (Fin n) ℂ} {y z : Fin n → ℂ}
    (hy : ConjPattern M y) (hz : ConjPattern M z) : ConjPattern M (y + z) := by
  sorry

theorem ConjPattern.neg {M : Matrix (Fin n) (Fin n) ℂ} {y : Fin n → ℂ}
    (hy : ConjPattern M y) : ConjPattern M (-y) := by
  sorry

theorem ConjPattern.real_smul {M : Matrix (Fin n) (Fin n) ℂ} {y : Fin n → ℂ} (r : ℝ)
    (hy : ConjPattern M y) : ConjPattern M ((r : ℂ) • y) := by
  sorry

theorem ConjPattern.one (M : Matrix (Fin n) (Fin n) ℂ) : ConjPattern M 1 := by
  sorry

theorem ConjPattern.zero (M : Matrix (Fin n) (Fin n) ℂ) : ConjPattern M 0 := by
  sorry

theorem ConjPattern.star {M : Matrix (Fin n) (Fin n) ℂ} {y : Fin n → ℂ}
    (hy : ConjPattern M y) : ConjPattern M (star y) := by
  sorry

theorem ConjPattern.pinvVec {M : Matrix (Fin n) (Fin n) ℂ} {y : Fin n → ℂ}
    (hy : ConjPattern M y) : ConjPattern M (Tubal.pinvVec y) := by
  sorry

end Tubal
