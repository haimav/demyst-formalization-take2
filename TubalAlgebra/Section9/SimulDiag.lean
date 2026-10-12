import Mathlib

/-!
# Simultaneous diagonalization (Lemma 38 = Fact 5.17.8 in Bernstein, *Matrix Mathematics*)
-/

open Matrix

noncomputable section

namespace Tubal

variable {n : ℕ}

/-- A matrix `A ∈ ℂ^{n×n}` is diagonalizable (over `ℂ`): there is a nonsingular `S` such that
`S A S⁻¹` is diagonal. -/
def IsDiagonalizableMat (A : Matrix (Fin n) (Fin n) ℂ) : Prop :=
  ∃ S : Matrix (Fin n) (Fin n) ℂ, IsUnit S ∧ (S * A * S⁻¹).IsDiag

/-- A set of matrices is jointly diagonalizable: there is a nonsingular `S` such that `S A S⁻¹`
is diagonal for all `A` in the set. -/
def IsJointlyDiagonalizableMat (𝒮 : Set (Matrix (Fin n) (Fin n) ℂ)) : Prop :=
  ∃ S : Matrix (Fin n) (Fin n) ℂ, IsUnit S ∧ ∀ A ∈ 𝒮, (S * A * S⁻¹).IsDiag

/-- `x` is an eigenvector of the matrix `A` (with some eigenvalue `λ ∈ ℂ`). -/
def IsEigenvectorMat (A : Matrix (Fin n) (Fin n) ℂ) (x : Fin n → ℂ) : Prop :=
  x ≠ 0 ∧ ∃ μ : ℂ, A *ᵥ x = μ • x

/-- A matrix is diagonalizable iff it has `n` linearly independent eigenvectors. -/
theorem isDiagonalizableMat_iff_eigenvectors (A : Matrix (Fin n) (Fin n) ℂ) :
    IsDiagonalizableMat A ↔
      ∃ v : Fin n → Fin n → ℂ, LinearIndependent ℂ v ∧ ∀ i, IsEigenvectorMat A (v i) := by
  sorry

/-- A set of matrices is jointly diagonalizable iff there are `n` linearly independent vectors
which are eigenvectors of all the matrices in the set. -/
theorem isJointlyDiagonalizableMat_iff_eigenvectors (𝒮 : Set (Matrix (Fin n) (Fin n) ℂ)) :
    IsJointlyDiagonalizableMat 𝒮 ↔
      ∃ v : Fin n → Fin n → ℂ, LinearIndependent ℂ v ∧ ∀ A ∈ 𝒮, ∀ i, IsEigenvectorMat A (v i) := by
  sorry

/-- **Lemma 38** (Fact 5.17.8 in [2]). Let `S ⊆ ℂ^{n×n}`, and assume every matrix `A ∈ S` is
diagonalizable over `ℂ`. Then `AB = BA` for all `A, B ∈ S` if and only if there exists a
nonsingular `S ∈ ℂ^{n×n}` such that, for all `A ∈ S`, `S A S⁻¹` is diagonal.

(The paper writes "for all `A ∈ ℂ^{n×n}`", an evident typo for "for all `A ∈ S`".) -/
theorem lemma38 (𝒮 : Set (Matrix (Fin n) (Fin n) ℂ)) (hdiag : ∀ A ∈ 𝒮, IsDiagonalizableMat A) :
    (∀ A ∈ 𝒮, ∀ B ∈ 𝒮, A * B = B * A) ↔
      ∃ S : Matrix (Fin n) (Fin n) ℂ, IsUnit S ∧ ∀ A ∈ 𝒮, (S * A * S⁻¹).IsDiag := by
  sorry

/-- A matrix annihilated by a polynomial with distinct roots (here: a squarefree polynomial)
is diagonalizable over `ℂ`. -/
theorem isDiagonalizableMat_of_squarefree (A : Matrix (Fin n) (Fin n) ℂ)
    (P : Polynomial ℂ) (hP : Squarefree P) (hPA : Polynomial.aeval A P = 0) :
    IsDiagonalizableMat A := by
  sorry

end Tubal
