import TubalAlgebra.Transform
import TubalAlgebra.MatrixSVD

/-!
# Tubal SVD (Section 7: Definitions 28, 29, Theorem 30, Definition 31, Lemma 32)
-/

open Matrix Complex

noncomputable section

namespace Tubal

variable {n : ℕ} {M : Matrix (Fin n) (Fin n) ℂ}

/-- **Definition 28.** A tensor `𝒰 ∈ 𝕂_M^{m×m}` is `⋆_M`-unitary if
`𝒰ᴴ ⋆_M 𝒰 = 𝒰 ⋆_M 𝒰ᴴ = ℐ_m`. -/
def IsStarMUnitary [Fact (Admissible M)] {m : ℕ} (U : Matrix (Fin m) (Fin m) (KM M)) : Prop :=
  Uᴴ * U = identityTensor m ∧ U * Uᴴ = identityTensor m

/-- "A tensor `𝒰` is `⋆_M`-unitary if and only if its transformed tensor `𝒰̂` is facewise
unitary (in the usual sense)." -/
theorem isStarMUnitary_iff_facewise [Fact (Admissible M)] {m : ℕ}
    (U : Matrix (Fin m) (Fin m) (KM M)) :
    IsStarMUnitary U ↔ ∀ j, (tHat U j)ᴴ * tHat U j = 1 ∧ tHat U j * (tHat U j)ᴴ = 1 := by
  sorry

/-- The `j`-th frontal slice `𝒜_{::j} ∈ ℝ^{m×p}` of a tensor. -/
def frontal {m p : ℕ} (A : Matrix (Fin m) (Fin p) (KM M)) (j : Fin n) :
    Matrix (Fin m) (Fin p) ℝ :=
  fun i k => (A i k).vec j

/-- **Definition 29.** A tensor is f-diagonal if all its frontal slices are diagonal
(an `m × p` matrix `D` is diagonal if `D_{ik} = 0` whenever `i ≠ k`). -/
def IsFDiagonal {m p : ℕ} (A : Matrix (Fin m) (Fin p) (KM M)) : Prop :=
  ∀ j (i : Fin m) (k : Fin p), (i : ℕ) ≠ k → frontal A j i k = 0

/-- The diagonal elements `σ₁, …, σ_{min(m,p)}` of a tensor `𝒮 ∈ 𝕂_M^{m×p}`
(indexed from `0`). -/
def sigma {m p : ℕ} (S : Matrix (Fin m) (Fin p) (KM M)) (i : Fin (min m p)) : KM M :=
  S (Fin.castLE (min_le_left m p) i) (Fin.castLE (min_le_right m p) i)

/-- `𝒜 = 𝒰 ⋆_M 𝒮 ⋆_M 𝒱ᴴ` is a `⋆_M`-SVD of `𝒜` (Theorem 30): `𝒰, 𝒱` are `⋆_M`-unitary,
`𝒮` is f-diagonal and `σ₁ ≥_M σ₂ ≥_M ⋯ ≥_M σ_{min(m,p)} ≥_M 0`. -/
def IsTSVD [Fact (Admissible M)] {m p : ℕ} (A : Matrix (Fin m) (Fin p) (KM M))
    (U : Matrix (Fin m) (Fin m) (KM M)) (S : Matrix (Fin m) (Fin p) (KM M))
    (V : Matrix (Fin p) (Fin p) (KM M)) : Prop :=
  IsStarMUnitary U ∧ IsStarMUnitary V ∧ IsFDiagonal S ∧ A = U * S * Vᴴ ∧
    (∀ i j : Fin (min m p), i ≤ j → sigma S j ≤ sigma S i) ∧ (∀ i, 0 ≤ sigma S i)

/-- **Theorem 30** (Theorem 5.1 in [14]). Let `𝒜 ∈ 𝕂_M^{m×p}` be a tensor. Then there exist
`⋆_M`-unitary tensors `𝒰 ∈ 𝕂_M^{m×m}` and `𝒱 ∈ 𝕂_M^{p×p}` and an f-diagonal tensor
`𝒮 ∈ 𝕂_M^{m×p}` such that `𝒜 = 𝒰 ⋆_M 𝒮 ⋆_M 𝒱ᴴ`. Furthermore, if we denote by
`σ₁, …, σ_{min(m,p)}` the diagonal elements of `𝒮`, then
`σ₁ ≥_M σ₂ ≥_M ⋯ ≥_M σ_{min(m,p)} ≥_M 0`. -/
theorem theorem30 [Fact (Admissible M)] {m p : ℕ} (A : Matrix (Fin m) (Fin p) (KM M)) :
    ∃ U S V, IsTSVD A U S V := by
  sorry

open Classical in
/-- The largest (`1`-based) index `r` with `σ_r ≠ 0`, or `0` if there is none. -/
def tsvdRank {m p : ℕ} (S : Matrix (Fin m) (Fin p) (KM M)) : ℕ :=
  Finset.univ.sup fun i : Fin (min m p) => if sigma S i ≠ 0 then (i : ℕ) + 1 else 0

/-- **Definition 31.** The `⋆_M`-rank of a tensor `𝒜`, `⋆_M-rank(𝒜)`, is the maximal `r` such
that `σ_r ≠ 0` (for the `⋆_M`-SVD of `𝒜`; by Lemma 32 this does not depend on the chosen
`⋆_M`-SVD, see `lemma32_any`). -/
def starMRank [Fact (Admissible M)] {m p : ℕ} (A : Matrix (Fin m) (Fin p) (KM M)) : ℕ :=
  tsvdRank (theorem30 A).choose_spec.choose

/-- **Lemma 32.** The `⋆_M`-rank of a tensor is the maximal rank of the frontal slices of its
transformed tensor: `⋆_M-rank(𝒜) = maxⱼ rank(𝒜̂ⱼ)`. -/
theorem lemma32 [Fact (Admissible M)] {m p : ℕ} (A : Matrix (Fin m) (Fin p) (KM M)) :
    starMRank A = Finset.univ.sup fun j => (tHat A j).rank := by
  sorry

/-- Lemma 32 holds for every `⋆_M`-SVD of `𝒜` (so Definition 31 is independent of the
choice of `⋆_M`-SVD). -/
theorem lemma32_any [Fact (Admissible M)] {m p : ℕ} (A : Matrix (Fin m) (Fin p) (KM M))
    (U : Matrix (Fin m) (Fin m) (KM M)) (S : Matrix (Fin m) (Fin p) (KM M))
    (V : Matrix (Fin p) (Fin p) (KM M)) (h : IsTSVD A U S V) :
    tsvdRank S = Finset.univ.sup fun j => (tHat A j).rank := by
  sorry

theorem starMRank_le_min [Fact (Admissible M)] {m p : ℕ}
    (A : Matrix (Fin m) (Fin p) (KM M)) : starMRank A ≤ min m p := by
  sorry

end Tubal
