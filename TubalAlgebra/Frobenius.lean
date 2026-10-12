import Mathlib

/-!
# Theorem 1 (Frobenius Theorem)

Every finite dimensional associative division algebra over the real numbers is isomorphic to
`ℝ`, `ℂ` or `ℍ` (the quaternions).

In Mathlib, an `Algebra ℝ D` on a `DivisionRing D` is precisely an associative unital
division algebra over `ℝ`.
-/

noncomputable section

namespace Tubal

/-- **Theorem 1** (Frobenius Theorem). Every finite dimensional associative division algebra
over the real numbers is isomorphic to `ℝ`, `ℂ` or `ℍ` (the quaternions). -/
theorem theorem1_frobenius (D : Type*) [DivisionRing D] [Algebra ℝ D] [FiniteDimensional ℝ D] :
    Nonempty (D ≃ₐ[ℝ] ℝ) ∨ Nonempty (D ≃ₐ[ℝ] ℂ) ∨ Nonempty (D ≃ₐ[ℝ] Quaternion ℝ) := by
  sorry

/-- The commutative case of Theorem 1 (used in Proposition 5 and Proposition 62): a finite
dimensional field extension of `ℝ` has dimension `1` or `2`. -/
theorem finrank_field_over_real (K : Type*) [Field K] [Algebra ℝ K] [FiniteDimensional ℝ K] :
    Module.finrank ℝ K = 1 ∨ Module.finrank ℝ K = 2 := by
  sorry

end Tubal
