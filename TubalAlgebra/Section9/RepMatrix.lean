import TubalAlgebra.TubalRing

/-!
# Sub-algebra of matrices (Section 9.1: Definitions 39, 45, Example 40, Lemmas 41–43,
Corollary 44, Lemma 46)

Throughout Section 9, `(ℝⁿ, +, ·)` is a tubal ring `T`.
-/

open Matrix Complex

noncomputable section

namespace Tubal

variable {n : ℕ}

/-- The matrix of the map `x ↦ mul a x` (with respect to the standard basis). -/
def repMatOf (mul : (Fin n → ℝ) → (Fin n → ℝ) → (Fin n → ℝ)) (a : Fin n → ℝ) :
    Matrix (Fin n) (Fin n) ℝ :=
  fun i j => mul a (Pi.single j 1) i

namespace TubalRing

variable (T : TubalRing n)

/-- **Definition 39.** Given `a ∈ ℝⁿ`, the unique matrix `R_a ∈ ℝ^{n×n}` for which
`R_a x = a · x` for all `x` is called the representation matrix of `a`. -/
def repMat (a : Fin n → ℝ) : Matrix (Fin n) (Fin n) ℝ := repMatOf T.mul a

/-- **Definition 39**: `R_a x = a · x` for all `x` … -/
theorem repMat_mulVec (a x : Fin n → ℝ) : T.repMat a *ᵥ x = T.mul a x := by
  sorry

/-- **Definition 39**: … and `R_a` is the unique such matrix. -/
theorem repMat_unique (a : Fin n → ℝ) (R : Matrix (Fin n) (Fin n) ℝ)
    (hR : ∀ x, R *ᵥ x = T.mul a x) : R = T.repMat a := by
  sorry

/-- **Definition 39**: `Rep(S) := {R_a : a ∈ S}`. -/
def Rep (S : Set (Fin n → ℝ)) : Set (Matrix (Fin n) (Fin n) ℝ) := T.repMat '' S

/-- **Lemma 41.** `R_{0_n} = 0_{n×n}`. There is no non-zero `x` for which `R_x = 0_{n×n}`. -/
theorem lemma41 : T.repMat 0 = 0 ∧ ∀ x, T.repMat x = 0 → x = 0 := by
  sorry

/-- **Lemma 42.** The map `a ↦ R_a` is injective. -/
theorem lemma42 : Function.Injective T.repMat := by
  sorry

/-- **Lemma 43.** For any `α ∈ ℝ` and `x, y ∈ ℝⁿ`:
1. `R_{-x} = -R_x`; 2. `R_{x+y} = R_x + R_y`; 3. `R_{αx} = α R_x`;
4. if `e` denotes the multiplicative identity element in the ring, `R_e = I_n`;
5. `R_{x·y} = R_x R_y`. -/
theorem lemma43 (α : ℝ) (x y : Fin n → ℝ) :
    T.repMat (-x) = -T.repMat x ∧
    T.repMat (x + y) = T.repMat x + T.repMat y ∧
    T.repMat (α • x) = α • T.repMat x ∧
    (∀ e, (∀ a, T.mul e a = a ∧ T.mul a e = a) → T.repMat e = 1) ∧
    T.repMat (T.mul x y) = T.repMat x * T.repMat y := by
  sorry

/-- **Corollary 44.** `Rep(ℝⁿ)` is a linear subspace of `ℝ^{n×n}`, and also an algebra (so is a
sub-algebra of `ℝ^{n×n}`). -/
theorem cor44 :
    (∃ V : Submodule ℝ (Matrix (Fin n) (Fin n) ℝ), (V : Set _) = T.Rep Set.univ) ∧
    (∃ A : Subalgebra ℝ (Matrix (Fin n) (Fin n) ℝ), (A : Set _) = T.Rep Set.univ) := by
  sorry

/-- **Definition 45.** An element `a ∈ ℝⁿ` is called idempotent if `a · a = a`. -/
def IsIdempotent (a : Fin n → ℝ) : Prop := T.mul a a = a

/-- **Lemma 46.** `a ∈ ℝⁿ` is idempotent if and only if the matrix `R_a` is idempotent. -/
theorem lemma46 (a : Fin n → ℝ) : T.IsIdempotent a ↔ IsIdempotentElem (T.repMat a) := by
  sorry

end TubalRing

/-- **Example 40** (Representation matrix for `⋆_M`). Consider the `·` defined by Eq. (5) for
some `M ∈ ℂ^{n×n}` (admissible, so that `(ℝⁿ, +, ⋆_M)` is a tubal ring). Then
`R_a = M⁻¹ diag(M a) M`. -/
theorem example40 (M : Matrix (Fin n) (Fin n) ℂ) [Fact (Admissible M)] (a : Fin n → ℝ) :
    ((KM.toTubalRing M).repMat a).map (↑) = M⁻¹ * diagonal (M *ᵥ toC a) * M := by
  sorry

end Tubal
