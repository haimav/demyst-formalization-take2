import TubalAlgebra.Section9.Main
import TubalAlgebra.Examples.Section3

/-!
# Appendix B: additional discussion of Theorem 11 (Example 69, Algorithm 1, nilpotents)
-/

open Matrix Complex

noncomputable section

namespace Tubal

variable {n : ℕ}

/-- **Example 69** (Dual numbers are not a tubal ring — revisited). The representative matrix
associated with `x = [x₁, x₂]ᵀ` is `R_x = [[x₁, 0], [x₂, x₁]]`, which is not diagonalizable
for `x₂ ≠ 0`. This also proves that the dual numbers are not a tubal ring. -/
theorem example69 :
    (∀ x : Fin 2 → ℝ, repMatOf dualMul x = !![x 0, 0; x 1, x 0]) ∧
    (∀ x : Fin 2 → ℝ, x 1 ≠ 0 → ¬ IsDiagonalizableMat ((repMatOf dualMul x).map (↑))) ∧
    ¬ ∃ T : TubalRing 2, T.mul = dualMul := by
  sorry

/-- **Algorithm 1** (Find matrix `M` for tubal ring product), given the eigendecomposition
`R_x = S Λ_x S⁻¹` of line 7: `y ← S e`, and the `i`-th column of `M` is `S⁻¹ R_{e_i} y`.

(The paper's "Ensure: Matrix `M ∈ ℝ^{n×n}`" and line 9 "Initialize `M ∈ ℝ^{n×n}`" are a typo:
the eigenvector matrix `S` of line 7 is complex in general, hence so is `M`; indeed no real `M`
exists for the complex numbers, see `theorem11_not_real`. So `M ∈ ℂ^{n×n}` here.) -/
def algorithm1 (T : TubalRing n) (S : Matrix (Fin n) (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ :=
  Matrix.of fun j i =>
    (S⁻¹ *ᵥ ((T.repMat (Pi.single i 1)).map (↑) *ᵥ (S *ᵥ fun _ => (1 : ℂ)))) j

/-- **Algorithm 1** correctness: "If we are dealing with a tubal ring, Algorithm 1 will find
`M`" — whenever the (random) vector `x` of line 1 has a representation matrix with distinct
eigenvalues, the output `M` is invertible and `op(x, y) = M⁻¹ ((M x) • (M y))`. -/
theorem algorithm1_correct (T : TubalRing n) (x : Fin n → ℝ) (S : Matrix (Fin n) (Fin n) ℂ)
    (hS : IsUnit S) (Λ : Fin n → ℂ) (hΛ : Function.Injective Λ)
    (hx : (T.repMat x).map (↑) = S * diagonal Λ * S⁻¹) :
    IsUnit (algorithm1 T S) ∧
      ∀ a b : Fin n → ℝ, toC (T.mul a b) = starMC (algorithm1 T S) (toC a) (toC b) := by
  sorry

/-- In a tubal ring, there is a vector `x` as required by `algorithm1_correct` (an `x` whose
representation matrix has `n` distinct eigenvalues), so Algorithm 1 can succeed. -/
theorem algorithm1_exists_good_x (T : TubalRing n) :
    ∃ (x : Fin n → ℝ) (S : Matrix (Fin n) (Fin n) ℂ) (Λ : Fin n → ℂ), IsUnit S ∧
      Function.Injective Λ ∧ (T.repMat x).map (↑) = S * diagonal Λ * S⁻¹ := by
  sorry

/-- **Algorithm 1**: "If we are dealing with a tubal ring, Algorithm 1 will find `M`", with
`x` drawn at random in line 1: for almost every `x ∈ ℝⁿ` (Lebesgue measure), the
eigendecomposition of line 7 exists, and whatever eigendecomposition `R_x = S Λ_x S⁻¹` line 7
returns, the output `M` is invertible and `op(a, b) = M⁻¹ ((M a) • (M b))`. -/
theorem algorithm1_ae (T : TubalRing n) :
    ∀ᵐ x : Fin n → ℝ ∂MeasureTheory.volume,
      (∃ (S : Matrix (Fin n) (Fin n) ℂ) (Λ : Fin n → ℂ), IsUnit S ∧
        (T.repMat x).map (↑) = S * diagonal Λ * S⁻¹) ∧
      ∀ (S : Matrix (Fin n) (Fin n) ℂ) (Λ : Fin n → ℂ), IsUnit S →
        (T.repMat x).map (↑) = S * diagonal Λ * S⁻¹ →
        IsUnit (algorithm1 T S) ∧
          ∀ a b : Fin n → ℝ, toC (T.mul a b) = starMC (algorithm1 T S) (toC a) (toC b) := by
  sorry

/-- Appendix B ("Importance of existence of weak inverses", also announced in Section 3.5):
a commutative ring over `ℝⁿ` which is not von Neumann regular must have nilpotent elements,
i.e. elements `ν ≠ 0` with `ν² = 0`. (The paper's sentence "a commutative ring over `ℝⁿ`
which is not tubal will be reduced, i.e., has an element `n` such that `n² = 0`" has a typo:
"reduced" should read "non-reduced", as the "i.e." clause shows.) -/
theorem not_vonNeumann_has_nilpotent (R : CommAlgOn n)
    (h : ¬ ∀ a, ∃ x, a = R.mul (R.mul a x) a) : ∃ ν : Fin n → ℝ, ν ≠ 0 ∧ R.mul ν ν = 0 := by
  sorry

end Tubal
