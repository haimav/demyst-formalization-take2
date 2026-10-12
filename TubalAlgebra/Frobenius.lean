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

/-! ### Auxiliary lemmas for the elementary proof of the Frobenius theorem -/

namespace Frobenius

variable {D : Type*} [DivisionRing D] [Algebra ℝ D]

/-- If `z * z = r` with `r ≥ 0` real, then `z` is real (it equals `±√r`). -/
lemma eq_smul_one_of_mul_self (z : D) (r : ℝ) (hr : 0 ≤ r) (h : z * z = r • (1 : D)) :
    ∃ t : ℝ, z = t • (1 : D) := by
  have hs : Real.sqrt r * Real.sqrt r = r := Real.mul_self_sqrt hr
  have : (z - Real.sqrt r • 1) * (z + Real.sqrt r • 1) = 0 := by
    rw [← hs] at h
    simp only [sub_mul, mul_add, smul_mul_assoc, mul_smul_comm, one_mul, mul_one, h]
    module
  rcases mul_eq_zero.mp this with h1 | h1
  · exact ⟨_, sub_eq_zero.mp h1⟩
  · exact ⟨-Real.sqrt r, by rw [neg_smul]; exact eq_neg_of_add_eq_zero_left h1⟩

/-- If `z * z = r` with `r < 0` real, then a positive real multiple of `z` squares to `-1`. -/
lemma exists_unit_of_mul_self_neg (z : D) (r : ℝ) (hr : r < 0) (h : z * z = r • (1 : D)) :
    ∃ s : ℝ, 0 < s ∧ (s • z) * (s • z) = -1 := by
  refine ⟨(Real.sqrt (-r))⁻¹, by have := Real.sqrt_pos.mpr (neg_pos.mpr hr); positivity, ?_⟩
  rw [smul_mul_smul_comm, h, smul_smul]
  have : (Real.sqrt (-r))⁻¹ * (Real.sqrt (-r))⁻¹ * r = -1 := by
    have : r ≠ 0 := hr.ne
    rw [← mul_inv, Real.mul_self_sqrt (by linarith)]
    field_simp
  rw [this, neg_one_smul]

/-- Every element of a finite dimensional real division algebra satisfies a real quadratic
equation `x * x = a • x + b`, since its minimal polynomial is irreducible over `ℝ`. -/
lemma exists_sq [FiniteDimensional ℝ D] (x : D) :
    ∃ a b : ℝ, x * x = a • x + b • (1 : D) := by
  have hx : IsIntegral ℝ x := IsIntegral.of_finite ℝ x
  have hdeg := (minpoly.irreducible hx).natDegree_le_two
  have hmon := minpoly.monic hx
  have hpos := minpoly.natDegree_pos hx
  have hev := minpoly.aeval ℝ x
  rw [Polynomial.aeval_eq_sum_range' (n := 3) (by omega)] at hev
  simp only [Finset.sum_range_succ, Finset.range_zero, Finset.sum_empty, pow_zero, pow_one,
    zero_add, pow_two] at hev
  have hlc := hmon.leadingCoeff
  rw [Polynomial.leadingCoeff] at hlc
  have key : (minpoly ℝ x).coeff 2 = 1 ∨
      ((minpoly ℝ x).coeff 2 = 0 ∧ (minpoly ℝ x).coeff 1 = 1) := by
    rcases (by omega : (minpoly ℝ x).natDegree = 1 ∨ (minpoly ℝ x).natDegree = 2) with h | h
    · right
      rw [h] at hlc
      exact ⟨Polynomial.coeff_eq_zero_of_natDegree_lt (by omega), hlc⟩
    · left; rw [h] at hlc; exact hlc
  generalize (minpoly ℝ x).coeff 0 = c0 at hev key
  generalize (minpoly ℝ x).coeff 1 = c1 at hev key
  generalize (minpoly ℝ x).coeff 2 = c2 at hev key
  rcases key with rfl | ⟨rfl, rfl⟩
  · refine ⟨-c1, -c0, ?_⟩
    rw [one_smul] at hev
    rw [neg_smul, neg_smul, eq_neg_add_iff_add_eq, eq_neg_iff_add_eq_zero, ← hev]
    abel
  · refine ⟨0, c0 * c0, ?_⟩
    have : x = -(c0 • (1 : D)) := by
      rw [eq_neg_iff_add_eq_zero, ← hev]; simp [add_comm]
    rw [this]; simp [smul_smul]


/-- Completing the square: every `x` has a real shift `x - α` whose square is real. -/
lemma exists_sq_real [FiniteDimensional ℝ D] (x : D) :
    ∃ α r : ℝ, (x - α • 1) * (x - α • 1) = r • (1 : D) := by
  obtain ⟨a, b, h⟩ := exists_sq x
  refine ⟨a / 2, b + a * a / 4, ?_⟩
  simp only [sub_mul, mul_sub, smul_mul_assoc, mul_smul_comm, one_mul, mul_one, h]
  module

/-- If `i * i = -1`, then every element commuting with `i` lies in `ℝ + ℝ i`. -/
lemma commute_mem_span [FiniteDimensional ℝ D] {i : D} (hi : i * i = -1) (x : D)
    (hx : x * i = i * x) : ∃ a b : ℝ, x = a • 1 + b • i := by
  obtain ⟨α, r, h⟩ := exists_sq_real x
  rcases le_or_gt 0 r with hr | hr
  · obtain ⟨t, ht⟩ := eq_smul_one_of_mul_self _ r hr h
    exact ⟨α + t, 0, by rw [zero_smul, add_zero, add_smul, ← ht]; abel⟩
  · obtain ⟨s, hs, hw⟩ := exists_unit_of_mul_self_neg _ r hr h
    set w := s • (x - α • 1) with hw_def
    have hwi : w * i = i * w := by
      simp only [hw_def, smul_mul_assoc, mul_smul_comm, sub_mul, mul_sub, one_mul, mul_one, hx]
    have : (w - i) * (w + i) = 0 := by
      linear_combination (norm := noncomm_ring) hw - hi + hwi
    have hx' : x = α • 1 + s⁻¹ • w := by
      rw [hw_def, smul_smul, inv_mul_cancel₀ hs.ne', one_smul]; abel
    rcases mul_eq_zero.mp this with h1 | h1
    · exact ⟨α, s⁻¹, by rw [hx', sub_eq_zero.mp h1]⟩
    · exact ⟨α, -s⁻¹, by rw [hx', eq_neg_of_add_eq_zero_left h1, neg_smul, smul_neg]⟩

/-- If some element is not real, there is an `i` with `i * i = -1`. -/
lemma exists_i [FiniteDimensional ℝ D] (x : D) (hx : ∀ t : ℝ, x ≠ t • 1) :
    ∃ i : D, i * i = -1 := by
  obtain ⟨α, r, h⟩ := exists_sq_real x
  rcases le_or_gt 0 r with hr | hr
  · obtain ⟨t, ht⟩ := eq_smul_one_of_mul_self _ r hr h
    exact absurd (by rw [add_smul, ← ht]; abel) (hx (α + t))
  · obtain ⟨s, -, hw⟩ := exists_unit_of_mul_self_neg _ r hr h
    exact ⟨_, hw⟩

/-- If some element does not commute with `i` (where `i * i = -1`), there is a `j` with
`j * j = -1` anticommuting with `i`. -/
lemma exists_j [FiniteDimensional ℝ D] {i : D} (hi : i * i = -1) (x : D) (hx : x * i ≠ i * x) :
    ∃ j : D, j * j = -1 ∧ j * i = -(i * j) := by
  set y := x + i * x * i with hy
  have hyi : y * i = x * i - i * x := by
    rw [hy]; linear_combination (norm := noncomm_ring) (i * x) * hi
  have hiy : i * y = i * x - x * i := by
    rw [hy]; linear_combination (norm := noncomm_ring) hi * (x * i)
  have hanti : i * y = -(y * i) := by rw [hiy, hyi, neg_sub]
  have hi0 : i ≠ 0 := by rintro rfl; simp at hi
  have hy0 : y ≠ 0 := by
    intro h0; apply hx; rw [← sub_eq_zero, ← hyi, h0, zero_mul]
  have hyi0 : y * i ≠ 0 := mul_ne_zero hy0 hi0
  obtain ⟨a, b, hab⟩ := exists_sq y
  have hcomm : (y * y) * i = i * (y * y) := by
    linear_combination (norm := noncomm_ring) y * hanti - hanti * y
  have ha : a = 0 := by
    rw [hab] at hcomm
    simp only [add_mul, mul_add, smul_mul_assoc, mul_smul_comm, one_mul, mul_one, hanti,
      add_left_inj, smul_neg] at hcomm
    have : (a + a) • (y * i) = 0 := by rw [add_smul]; nth_rw 1 [hcomm]; abel
    rcases smul_eq_zero.mp this with h | h
    · linarith
    · exact absurd h hyi0
  subst ha
  rw [zero_smul, zero_add] at hab
  rcases le_or_gt 0 b with hb | hb
  · obtain ⟨t, ht⟩ := eq_smul_one_of_mul_self _ b hb hab
    exfalso
    apply hyi0
    have : i * y = y * i := by rw [ht, smul_mul_assoc, mul_smul_comm, one_mul, mul_one]
    rw [hanti] at this
    have h2 : (2 : ℝ) • (y * i) = 0 := by rw [two_smul]; nth_rw 1 [← this]; abel
    rcases smul_eq_zero.mp h2 with h | h
    · norm_num at h
    · exact h
  · obtain ⟨s, -, hw⟩ := exists_unit_of_mul_self_neg _ b hb hab
    refine ⟨s • y, hw, ?_⟩
    rw [smul_mul_assoc, mul_smul_comm, hanti, smul_neg, neg_neg]


/-- Given `i, j` with `i² = j² = -1` and `j i = -(i j)`, every element is a real linear
combination of `1, i, j, i j`. -/
lemma decomp [FiniteDimensional ℝ D] {i j : D} (hi : i * i = -1) (hj : j * j = -1)
    (hij : j * i = -(i * j)) (x : D) :
    ∃ a b c d : ℝ, x = a • 1 + b • i + c • j + d • (i * j) := by
  have hp : (x - i * x * i) * i = i * (x - i * x * i) := by
    linear_combination (norm := noncomm_ring) (-(i * x)) * hi + hi * (x * i)
  have hm : ((x + i * x * i) * j) * i = i * ((x + i * x * i) * j) := by
    linear_combination (norm := noncomm_ring) (x + i * x * i) * hij - (i * x) * hi * j - hi * (x * i * j)
  obtain ⟨a, b, hab⟩ := commute_mem_span hi _ hp
  obtain ⟨c, d, hcd⟩ := commute_mem_span hi _ hm
  have hm' : x + i * x * i = -(c • j + d • (i * j)) := by
    have : x + i * x * i = -(((x + i * x * i) * j) * j) := by
      rw [mul_assoc _ j j, hj, mul_neg_one, neg_neg]
    rw [this, hcd]; simp [add_mul]
  have hx : x = (1 / 2 : ℝ) • ((x - i * x * i) + (x + i * x * i)) := by
    rw [sub_add_add_cancel, ← two_smul ℝ x, smul_smul]; norm_num
  refine ⟨a / 2, b / 2, -c / 2, -d / 2, ?_⟩
  rw [hx, hab, hm']
  module


end Frobenius

/-- **Theorem 1** (Frobenius Theorem). Every finite dimensional associative division algebra
over the real numbers is isomorphic to `ℝ`, `ℂ` or `ℍ` (the quaternions). -/
theorem theorem1_frobenius (D : Type*) [DivisionRing D] [Algebra ℝ D] [FiniteDimensional ℝ D] :
    Nonempty (D ≃ₐ[ℝ] ℝ) ∨ Nonempty (D ≃ₐ[ℝ] ℂ) ∨ Nonempty (D ≃ₐ[ℝ] Quaternion ℝ) := by
  by_cases hR : ∀ x : D, ∃ t : ℝ, x = t • 1
  · left
    have hbij : Function.Bijective (Algebra.ofId ℝ D) := by
      refine ⟨(algebraMap ℝ D).injective, fun x => ?_⟩
      obtain ⟨t, rfl⟩ := hR x
      exact ⟨t, by rw [Algebra.ofId_apply, Algebra.algebraMap_eq_smul_one]⟩
    exact ⟨(AlgEquiv.ofBijective _ hbij).symm⟩
  push Not at hR
  obtain ⟨x0, hx0⟩ := hR
  obtain ⟨i, hi⟩ := Frobenius.exists_i x0 hx0
  by_cases hC : ∀ x : D, x * i = i * x
  · right; left
    let f : ℂ →ₐ[ℝ] D := Complex.liftAux i hi
    have hbij : Function.Bijective f := by
      refine ⟨f.toRingHom.injective, fun x => ?_⟩
      obtain ⟨a, b, rfl⟩ := Frobenius.commute_mem_span hi x (hC x)
      exact ⟨⟨a, b⟩, by simp [f, Complex.liftAux_apply, Algebra.algebraMap_eq_smul_one]⟩
    exact ⟨(AlgEquiv.ofBijective f hbij).symm⟩
  · right; right
    push Not at hC
    obtain ⟨x1, hx1⟩ := hC
    obtain ⟨j, hj, hij⟩ := Frobenius.exists_j hi x1 hx1
    let q : QuaternionAlgebra.Basis D (-1 : ℝ) 0 (-1) :=
      { i := i, j := j, k := i * j
        i_mul_i := by rw [hi, zero_smul, add_zero, neg_one_smul]
        j_mul_j := by rw [hj, neg_one_smul]
        i_mul_j := rfl
        j_mul_i := by rw [hij, zero_smul, zero_sub] }
    let f : Quaternion ℝ →ₐ[ℝ] D := q.liftHom
    have hbij : Function.Bijective f := by
      refine ⟨f.toRingHom.injective, fun x => ?_⟩
      obtain ⟨a, b, c, d, rfl⟩ := Frobenius.decomp hi hj hij x
      exact ⟨⟨a, b, c, d⟩, by
        simp [f, q, QuaternionAlgebra.Basis.lift, Algebra.algebraMap_eq_smul_one]⟩
    exact ⟨(AlgEquiv.ofBijective f hbij).symm⟩

/-- The commutative case of Theorem 1 (used in Proposition 5 and Proposition 62): a finite
dimensional field extension of `ℝ` has dimension `1` or `2`. -/
theorem finrank_field_over_real (K : Type*) [Field K] [Algebra ℝ K] [FiniteDimensional ℝ K] :
    Module.finrank ℝ K = 1 ∨ Module.finrank ℝ K = 2 := by
  have : Algebra.IsAlgebraic ℝ K := Algebra.IsAlgebraic.of_finite ℝ K
  let f : K →ₐ[ℝ] ℂ := IsAlgClosed.lift
  have h1 := LinearMap.finrank_le_finrank_of_injective (f := f.toLinearMap) f.toRingHom.injective
  rw [Complex.finrank_real_complex] at h1
  have h2 := Module.finrank_pos (R := ℝ) (M := K)
  omega

end Tubal
