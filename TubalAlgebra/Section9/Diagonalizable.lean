import TubalAlgebra.Section9.RepMatrix
import TubalAlgebra.Section9.SimulDiag

/-!
# Diagonalizability of tubal rings (Section 9.2: Definitions 47, 48, 50, Lemmas 49, 51, 52, 53,
Proposition 54)
-/

open Matrix Complex

noncomputable section

namespace Tubal

variable {n : ℕ}

namespace TubalRing

variable (T : TubalRing n)

/-- For `a ∈ ℝⁿ` and `b ∈ ℂⁿ`: `a · b := a · Re b + i (a · Im b)`. -/
def mulC (a : Fin n → ℝ) (b : Fin n → ℂ) : Fin n → ℂ :=
  fun i => ⟨T.mul a (fun j => (b j).re) i, T.mul a (fun j => (b j).im) i⟩

/-- "We still have `a · b = R_a b`." -/
theorem mulC_eq_repMat_mulVec (a : Fin n → ℝ) (b : Fin n → ℂ) :
    T.mulC a b = (T.repMat a).map (↑) *ᵥ b := by
  sorry

/-- **Definition 47.** A non-zero `x ∈ ℂⁿ` is an eigenvector of `a` if there exists a
corresponding eigenvalue `λ ∈ ℂ` such that `a · x = λ x`. -/
def IsEigenvector (a : Fin n → ℝ) (x : Fin n → ℂ) : Prop :=
  x ≠ 0 ∧ ∃ μ : ℂ, T.mulC a x = μ • x

/-- **Definition 48.** `a` is diagonalizable if there exists a set of `n` linearly independent
eigenvectors of `a`. -/
def IsDiagonalizable (a : Fin n → ℝ) : Prop :=
  ∃ v : Fin n → Fin n → ℂ, LinearIndependent ℂ v ∧ ∀ i, T.IsEigenvector a (v i)

/-- **Lemma 49.** `a` is diagonalizable if and only if `R_a` is diagonalizable over `ℂ`. The
set of eigenvectors of `a` is exactly the set of eigenvectors of `R_a`. -/
theorem lemma49 (a : Fin n → ℝ) :
    (T.IsDiagonalizable a ↔ IsDiagonalizableMat ((T.repMat a).map (↑))) ∧
    (∀ x, T.IsEigenvector a x ↔ IsEigenvectorMat ((T.repMat a).map (↑)) x) := by
  sorry

/-- **Definition 50** (first part). `S ⊆ ℝⁿ` is diagonalizable if every `a ∈ S` is
diagonalizable. -/
def IsDiagonalizableSet (S : Set (Fin n → ℝ)) : Prop := ∀ a ∈ S, T.IsDiagonalizable a

/-- **Definition 50**: the tubal ring is diagonalizable if `ℝⁿ` is diagonalizable. -/
def IsDiagonalizableRing : Prop := T.IsDiagonalizableSet Set.univ

/-- **Definition 50** (second part). `S ⊆ ℝⁿ` is jointly diagonalizable if there exists a set
of `n` linearly independent vectors which are eigenvectors for all `a ∈ S`. -/
def IsJointlyDiagonalizable (S : Set (Fin n → ℝ)) : Prop :=
  ∃ v : Fin n → Fin n → ℂ, LinearIndependent ℂ v ∧ ∀ a ∈ S, ∀ i, T.IsEigenvector a (v i)

/-- **Definition 50**: the tubal ring is jointly diagonalizable if `ℝⁿ` is. -/
def IsJointlyDiagonalizableRing : Prop := T.IsJointlyDiagonalizable Set.univ

/-- `Rep(S)` viewed as a set of complex matrices. -/
def RepC (S : Set (Fin n → ℝ)) : Set (Matrix (Fin n) (Fin n) ℂ) :=
  (fun a => (T.repMat a).map (↑)) '' S

/-- **Lemma 51.** `S ⊆ ℝⁿ` is jointly diagonalizable if and only if the set of matrices
`Rep(S)` is jointly diagonalizable. -/
theorem lemma51 (S : Set (Fin n → ℝ)) :
    T.IsJointlyDiagonalizable S ↔ IsJointlyDiagonalizableMat (T.RepC S) := by
  sorry

/-- **Lemma 52.** In a tubal ring, if a set of elements `S` is diagonalizable then it is
jointly diagonalizable. -/
theorem lemma52 (S : Set (Fin n → ℝ)) (hS : T.IsDiagonalizableSet S) :
    T.IsJointlyDiagonalizable S := by
  sorry

/-- **Lemma 53.** If `S ⊆ ℝⁿ` is diagonalizable, then `span(S)` is diagonalizable. -/
theorem lemma53 (S : Set (Fin n → ℝ)) (hS : T.IsDiagonalizableSet S) :
    T.IsDiagonalizableSet (Submodule.span ℝ S) := by
  sorry

/-- **Proposition 54.** A tubal ring is diagonalizable if and only if there exists an
invertible `M ∈ ℂ^{n×n}` such that for all `a, b ∈ ℝⁿ`, `a · b = M⁻¹ (M a • M b)`. -/
theorem prop54 :
    T.IsDiagonalizableRing ↔
      ∃ M : Matrix (Fin n) (Fin n) ℂ, IsUnit M ∧
        ∀ a b : Fin n → ℝ, toC (T.mul a b) = starMC M (toC a) (toC b) := by
  sorry

end TubalRing

end Tubal
