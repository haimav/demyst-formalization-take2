import TubalAlgebra.Section9.Ideals
import TubalAlgebra.Section9.Diagonalizable
import TubalAlgebra.Frobenius

/-!
# Diagonalizability of tubal sub-fields (Section 9.5: Proposition 62)
-/

open Matrix Complex

noncomputable section

namespace Tubal

variable {n : ℕ}

namespace TubalRing

variable (T : TubalRing n)

instance Elem.finiteDimensional : FiniteDimensional ℝ T.Elem :=
  LinearEquiv.finiteDimensional Elem.linearEquivVec.symm

/-- A tubal ring is reduced: von Neumann regularity rules out non-zero nilpotents. -/
theorem Elem.isReduced : IsReduced T.Elem := by
  have hsq : ∀ x : T.Elem, x * x = 0 → x = 0 := by
    intro x hx
    obtain ⟨y, hy⟩ := Elem.isVonNeumannRegularRing x
    rw [hy, _root_.mul_comm x y, _root_.mul_assoc, hx, MulZeroClass.mul_zero]
  have key : ∀ k (x : T.Elem), x ^ k = 0 → x = 0 := by
    intro k
    induction k using Nat.strong_induction_on with
    | _ k ih =>
      intro x hk
      rcases Nat.lt_or_ge k 2 with hk2 | hk2
      · interval_cases k
        · simp only [pow_zero] at hk
          rw [← _root_.one_mul x, hk, MulZeroClass.zero_mul]
        · simpa using hk
      · have : x ^ (k - 1) = 0 := by
          apply hsq
          rw [← pow_add]
          have : k - 1 + (k - 1) = k + (k - 2) := by omega
          rw [this, pow_add, hk, MulZeroClass.zero_mul]
        exact ih (k - 1) (by omega) x this
  exact ⟨fun x ⟨k, hk⟩ => key k x hk⟩

/-- The representation `a ↦ R_a` as an `ℝ`-algebra homomorphism `T.Elem → ℝ^{n×n}`. -/
def repAlgHom : T.Elem →ₐ[ℝ] Matrix (Fin n) (Fin n) ℝ where
  toFun x := T.repMat x.vec
  map_one' := (T.lemma43 0 0 0).2.2.2.1 T.one fun a => ⟨T.one_mul a, T.mul_one a⟩
  map_mul' x y := (T.lemma43 0 x.vec y.vec).2.2.2.2
  map_zero' := T.lemma41.1
  map_add' x y := (T.lemma43 0 x.vec y.vec).2.1
  commutes' r := by
    change T.repMat (r • (1 : T.Elem)).vec = algebraMap ℝ (Matrix (Fin n) (Fin n) ℝ) r
    rw [Elem.vec_smul, Elem.vec_one, (T.lemma43 r T.one T.one).2.2.1,
      (T.lemma43 0 0 0).2.2.2.1 T.one fun a => ⟨T.one_mul a, T.mul_one a⟩,
      Algebra.algebraMap_eq_smul_one]

/-- In a tubal ring every element is diagonalizable: its minimal polynomial is squarefree
(the ring is reduced), hence `R_a` is annihilated by a squarefree polynomial. -/
theorem isDiagonalizable_of_mem (a : Fin n → ℝ) : T.IsDiagonalizable a := by
  have := Elem.isReduced T
  set x : T.Elem := ⟨a⟩
  set P := minpoly ℝ x
  have hint : IsIntegral ℝ x := IsIntegral.of_finite ℝ x
  have hP0 : P ≠ 0 := minpoly.ne_zero hint
  have hsq : Squarefree P := (minpoly.isRadical ℝ x).squarefree hP0
  have hsep : P.Separable := PerfectField.separable_iff_squarefree.mpr hsq
  have hsqC : Squarefree (P.map (algebraMap ℝ ℂ)) := (hsep.map).squarefree
  have hR : Polynomial.aeval (T.repMat a) P = 0 := by
    have := Polynomial.aeval_algHom_apply (T.repAlgHom) x P
    rw [minpoly.aeval, map_zero] at this
    exact this
  have hRC : Polynomial.aeval ((T.repMat a).map ((↑) : ℝ → ℂ)) (P.map (algebraMap ℝ ℂ)) = 0 := by
    rw [Polynomial.aeval_map_algebraMap]
    have := Polynomial.aeval_algHom_apply (Complex.ofRealAm.mapMatrix (m := Fin n)) (T.repMat a) P
    rw [hR, map_zero] at this
    exact this
  exact (T.lemma49 a).1.2 (isDiagonalizableMat_of_squarefree _ _ hsqC hRC)

/-- **Proposition 62.** A tubal sub-field is diagonalizable. -/
theorem prop62 (V : Submodule ℝ (Fin n → ℝ)) (hV : T.IsTubalSubfield V) :
    T.IsDiagonalizableSet V := by
  -- every element of a tubal ring is diagonalizable (`isDiagonalizable_of_mem`)
  have _ := hV
  exact fun a _ => T.isDiagonalizable_of_mem a

end TubalRing

end Tubal
