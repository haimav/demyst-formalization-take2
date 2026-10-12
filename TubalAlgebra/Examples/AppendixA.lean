import TubalAlgebra.EckartYoung
import TubalAlgebra.Examples.Section3

/-!
# Appendix A: worked examples (Examples 67, 68)

`M = F₂ = [[1, 1], [1, -1]]` (the DFT matrix for `n = 2`), so the tubal product is the
t-product `⋆_t`. Tensors in `ℝ^{2×2×2}` are matrices of tubes `𝕂_{F₂}^{2×2}`; the tube at
`(i, k)` is `((𝐀₁)_{ik}, (𝐀₂)_{ik})`.
-/

open Matrix Complex

noncomputable section

namespace Tubal

namespace AppendixA

theorem hadamard2_admissible : Admissible hadamard2 := by
  refine ⟨?_, ?_⟩
  · rw [Matrix.isUnit_iff_isUnit_det, isUnit_iff_ne_zero]
    simp [Matrix.det_fin_two, hadamard2]
    norm_num
  · intro i
    left
    intro k
    fin_cases i <;> fin_cases k <;> simp [hadamard2]

instance : Fact (Admissible hadamard2) := ⟨hadamard2_admissible⟩

/-- Build a tensor in `𝕂_M^{2×2}` from its two frontal slices. -/
def ofSlices (X₁ X₂ : Matrix (Fin 2) (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) (KM hadamard2) :=
  fun i k => ⟨![X₁ i k, X₂ i k]⟩

/-- The input tensor `𝒜`: `𝐀₁ = [[3, 1], [1, 3]]`, `𝐀₂ = [[1, 1], [1, 1]]`. -/
def A : Matrix (Fin 2) (Fin 2) (KM hadamard2) := ofSlices !![3, 1; 1, 3] !![1, 1; 1, 1]

/-- `𝐐 := (1/√2) [[1, 1], [1, -1]]`. -/
def Q : Matrix (Fin 2) (Fin 2) ℝ :=
  !![1 / Real.sqrt 2, 1 / Real.sqrt 2; 1 / Real.sqrt 2, -1 / Real.sqrt 2]

/-- `𝒰 = 𝒱` with frontal slices `𝐔₁ = 𝐐`, `𝐔₂ = 0`. -/
def U : Matrix (Fin 2) (Fin 2) (KM hadamard2) := ofSlices Q 0

/-- `𝒮` with frontal slices `𝐒₁ = diag(4, 2)`, `𝐒₂ = diag(2, 0)`. -/
def S : Matrix (Fin 2) (Fin 2) (KM hadamard2) := ofSlices !![4, 0; 0, 2] !![2, 0; 0, 0]

/-! ### Auxiliary computations -/

private lemma hadamard2_inv : hadamard2⁻¹ = (1 / 2 : ℂ) • hadamard2 := by
  apply Matrix.inv_eq_left_inv
  ext i j
  fin_cases i <;> fin_cases j <;> simp [hadamard2, Matrix.mul_apply, Fin.sum_univ_two] <;> norm_num

private lemma tHat_ofSlices_zero (X₁ X₂ : Matrix (Fin 2) (Fin 2) ℝ) :
    tHat (ofSlices X₁ X₂) 0 = (X₁ + X₂).map (↑) := by
  ext i k
  simp [tHat, ofSlices, KM.hat, hadamard2, mulVec, dotProduct, Fin.sum_univ_two]

private lemma tHat_ofSlices_one (X₁ X₂ : Matrix (Fin 2) (Fin 2) ℝ) :
    tHat (ofSlices X₁ X₂) 1 = (X₁ - X₂).map (↑) := by
  ext i k
  simp [tHat, ofSlices, KM.hat, hadamard2, mulVec, dotProduct, Fin.sum_univ_two]
  ring

private lemma sqrt2_sq : ((Real.sqrt 2 : ℝ) : ℂ) ^ 2 = 2 := by
  rw [← Complex.ofReal_pow, Real.sq_sqrt (by norm_num)]
  norm_num

private lemma sqrt2_ne : ((Real.sqrt 2 : ℝ) : ℂ) ≠ 0 := by
  rw [Complex.ofReal_ne_zero]
  exact Real.sqrt_ne_zero'.2 (by norm_num)

private lemma sqrt2_inv_sq : (((Real.sqrt 2 : ℝ) : ℂ))⁻¹ ^ 2 = 1 / 2 := by
  rw [inv_pow, sqrt2_sq]; norm_num

local macro "sqrt_two_tac" : tactic =>
  `(tactic| (ring_nf <;> (try simp only [sqrt2_inv_sq, sqrt2_sq]) <;> norm_num))

private lemma Qc_mul_self : Q.map ((↑) : ℝ → ℂ) * Q.map ((↑) : ℝ → ℂ) = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Q, Matrix.mul_apply, Fin.sum_univ_two] <;> sqrt_two_tac

private lemma Qc_conjTranspose : (Q.map ((↑) : ℝ → ℂ))ᴴ = Q.map ((↑) : ℝ → ℂ) := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Q]

private lemma Qc_unitary : Q.map ((↑) : ℝ → ℂ) ∈ unitaryGroup (Fin 2) ℂ := by
  rw [mem_unitaryGroup_iff, star_eq_conjTranspose, Qc_conjTranspose, Qc_mul_self]

private lemma tHat_A0 : tHat A 0 = !![4, 2; 2, 4] := by
  rw [A, tHat_ofSlices_zero]
  ext i k
  fin_cases i <;> fin_cases k <;> simp <;> norm_num

private lemma tHat_A1 : tHat A 1 = !![2, 0; 0, 2] := by
  rw [A, tHat_ofSlices_one]
  ext i k
  fin_cases i <;> fin_cases k <;> simp <;> norm_num

private lemma tHat_U (j : Fin 2) : tHat U j = Q.map (↑) := by
  fin_cases j
  · simp [U, tHat_ofSlices_zero]
  · simp [U, tHat_ofSlices_one]

private lemma tHat_S0 : tHat S 0 = !![6, 0; 0, 2] := by
  rw [S, tHat_ofSlices_zero]
  ext i k
  fin_cases i <;> fin_cases k <;> norm_num

private lemma tHat_S1 : tHat S 1 = !![2, 0; 0, 2] := by
  rw [S, tHat_ofSlices_one]
  ext i k
  fin_cases i <;> fin_cases k <;> norm_num

private lemma isSingularDiag_62 : IsSingularDiag (!![6, 0; 0, 2] : Matrix (Fin 2) (Fin 2) ℂ) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro i k hik
    fin_cases i <;> fin_cases k <;> simp_all
  · intro i
    fin_cases i <;> simp [diagEntry]
  · intro i
    fin_cases i <;> simp [diagEntry]
  · intro i j hij
    fin_cases i <;> fin_cases j <;> simp_all [diagEntry]
    norm_num

private lemma isSingularDiag_22 : IsSingularDiag (!![2, 0; 0, 2] : Matrix (Fin 2) (Fin 2) ℂ) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro i k hik
    fin_cases i <;> fin_cases k <;> simp_all
  · intro i
    fin_cases i <;> simp [diagEntry]
  · intro i
    fin_cases i <;> simp [diagEntry]
  · intro i j hij
    fin_cases i <;> fin_cases j <;> simp_all [diagEntry]

private lemma svd_slices (j : Fin 2) : IsSVD (tHat A j) (tHat U j) (tHat S j) (tHat U j) := by
  rw [tHat_U]
  refine ⟨Qc_unitary, Qc_unitary, ?_, ?_⟩
  · fin_cases j
    · rw [show ((⟨0, by decide⟩ : Fin 2)) = 0 from rfl, tHat_S0]; exact isSingularDiag_62
    · rw [show ((⟨1, by decide⟩ : Fin 2)) = 1 from rfl, tHat_S1]; exact isSingularDiag_22
  · rw [Qc_conjTranspose]
    fin_cases j
    · rw [show ((⟨0, by decide⟩ : Fin 2)) = 0 from rfl, tHat_A0, tHat_S0]
      ext i k
      fin_cases i <;> fin_cases k <;> simp [Q, Matrix.mul_apply, Fin.sum_univ_two] <;> sqrt_two_tac
    · rw [show ((⟨1, by decide⟩ : Fin 2)) = 1 from rfl, tHat_A1, tHat_S1]
      ext i k
      fin_cases i <;> fin_cases k <;> simp [Q, Matrix.mul_apply, Fin.sum_univ_two] <;> sqrt_two_tac

private lemma rank_A (j : Fin 2) : (tHat A j).rank = 2 := by
  have key : IsUnit (tHat A j) := by
    rw [Matrix.isUnit_iff_isUnit_det, isUnit_iff_ne_zero]
    fin_cases j
    · rw [show ((⟨0, by decide⟩ : Fin 2)) = 0 from rfl, tHat_A0, Matrix.det_fin_two_of]; norm_num
    · rw [show ((⟨1, by decide⟩ : Fin 2)) = 1 from rfl, tHat_A1, Matrix.det_fin_two_of]; norm_num
  rw [Matrix.rank_of_isUnit _ key, Fintype.card_fin]

private lemma sigma_hat (i : Fin (min 2 2)) (l : Fin 2) :
    (sigma S i).hat l = diagEntry (tHat S l) i := rfl

private lemma sum_min22 (f : Fin (min 2 2) → ℝ) :
    ∑ i, f i = f ⟨0, by decide⟩ + f ⟨1, by decide⟩ := Fin.sum_univ_two f

/-- **Example 67** (Worked example: t-SVD of a `2 × 2 × 2` tensor).
* `F₂⁻¹ = ½ F₂`;
* Step 2: `𝐀̂₁ = 𝐀₁ + 𝐀₂ = [[4, 2], [2, 4]]`, `𝐀̂₂ = 𝐀₁ - 𝐀₂ = 2𝐈`;
* Steps 3–4: `𝐔̂₁ = 𝐕̂₁ = 𝐔̂₂ = 𝐕̂₂ = 𝐐`, `𝐒̂₁ = diag(6, 2)`, `𝐒̂₂ = 2𝐈`; these are SVDs of
  `𝐀̂₁`, `𝐀̂₂`; the transformed singular tubes are `σ̂₁ = (6, 2)`, `σ̂₂ = (2, 2)` and
  `σ̂₁ ≥ σ̂₂` entry-wise;
* Step 5: `𝐔₁ = 𝐐`, `𝐔₂ = 0`, `𝐒₁ = diag(4, 2)`, `𝐒₂ = diag(2, 0)` (by definition of `U, S`),
  so `σ₁ = (4, 2)`, `σ₂ = (2, 0)`, both non-zero, and `𝒜` has `⋆_t`-rank 2;
* Step 6: `𝒜 = 𝒰 ⋆_t 𝒮 ⋆_t 𝒱ᵀ` is a `⋆_t`-SVD (in particular `𝒰` is `⋆_t`-unitary although
  its frontal slices are not individually unitary). -/
theorem example67 :
    hadamard2⁻¹ = (1 / 2 : ℂ) • hadamard2 ∧
    tHat A 0 = !![4, 2; 2, 4] ∧ tHat A 1 = !![2, 0; 0, 2] ∧
    (∀ j, tHat U j = Q.map (↑)) ∧
    tHat S 0 = !![6, 0; 0, 2] ∧ tHat S 1 = !![2, 0; 0, 2] ∧
    (∀ j, IsSVD (tHat A j) (tHat U j) (tHat S j) (tHat U j)) ∧
    (sigma S ⟨0, by decide⟩).hat = ![6, 2] ∧ (sigma S ⟨1, by decide⟩).hat = ![2, 2] ∧
    (sigma S ⟨0, by decide⟩).vec = ![4, 2] ∧ (sigma S ⟨1, by decide⟩).vec = ![2, 0] ∧
    sigma S ⟨0, by decide⟩ ≠ 0 ∧ sigma S ⟨1, by decide⟩ ≠ 0 ∧
    starMRank A = 2 ∧
    IsTSVD A U S U ∧
    ¬ (frontal U 1)ᵀ * frontal U 1 = 1 := by
  have hv0 : (sigma S ⟨0, by decide⟩).vec = ![4, 2] := by
    funext l
    fin_cases l <;> simp [sigma, S, ofSlices]
  have hv1 : (sigma S ⟨1, by decide⟩).vec = ![2, 0] := by
    funext l
    fin_cases l <;> simp [sigma, S, ofSlices]
  have hU : IsStarMUnitary U := by
    rw [isStarMUnitary_iff_facewise]
    intro j
    rw [tHat_U, Qc_conjTranspose, Qc_mul_self]
    exact ⟨rfl, rfl⟩
  refine ⟨hadamard2_inv, tHat_A0, tHat_A1, tHat_U, tHat_S0, tHat_S1, svd_slices, ?_, ?_, hv0, hv1,
    ?_, ?_, ?_, ⟨hU, hU, ?_, ?_, ?_, ?_⟩, ?_⟩
  · funext l
    rw [sigma_hat]
    fin_cases l
    · simp [diagEntry, tHat_S0]
    · simp [diagEntry, tHat_S1]
  · funext l
    rw [sigma_hat]
    fin_cases l
    · simp [diagEntry, tHat_S0]
    · simp [diagEntry, tHat_S1]
  · intro h
    have h' := congrFun hv0 0
    rw [h] at h'
    simp at h'
  · intro h
    have h' := congrFun hv1 0
    rw [h] at h'
    simp at h'
  · rw [lemma32]
    simp only [rank_A]
    exact Finset.sup_const Finset.univ_nonempty 2
  · intro j i k hik
    fin_cases j <;> fin_cases i <;> fin_cases k <;> simp_all [frontal, S, ofSlices]
  · apply tHat_injective
    rw [tHat_mul, tHat_mul, example27]
    funext j
    exact (svd_slices j).2.2.2
  · intro i j hij
    rw [KM.le_def]
    intro l
    rw [KM.hat_sub, Pi.sub_apply, sigma_hat, sigma_hat]
    fin_cases l
    · fin_cases i <;> fin_cases j <;> simp_all [diagEntry, tHat_S0]
      norm_num
    · fin_cases i <;> fin_cases j <;> simp_all [diagEntry, tHat_S1]
  · intro i
    rw [KM.le_def]
    intro l
    rw [KM.hat_sub, KM.hat_zero, sub_zero, sigma_hat]
    fin_cases l
    · fin_cases i <;> simp [diagEntry, tHat_S0]
    · fin_cases i <;> simp [diagEntry, tHat_S1]
  · have : frontal U 1 = 0 := by
      ext i k
      simp [frontal, U, ofSlices]
    rw [this]
    simp

/-- **Example 67**, Step 3 side claims: "The matrix `Â₁` is symmetric with eigenvalues 6 and 2
(eigenvectors `(1/√2)[1, 1]` and `(1/√2)[1, -1]`)", and "The matrix `Â₂ = 2I` has both singular
values equal to 2, so its SVD is not unique. We are free to choose any orthogonal factors". -/
theorem example67_step3 :
    (tHat A 0)ᴴ = tHat A 0 ∧
    tHat A 0 *ᵥ (fun i => ((Q i 0 : ℝ) : ℂ)) = (6 : ℂ) • (fun i => ((Q i 0 : ℝ) : ℂ)) ∧
    tHat A 0 *ᵥ (fun i => ((Q i 1 : ℝ) : ℂ)) = (2 : ℂ) • (fun i => ((Q i 1 : ℝ) : ℂ)) ∧
    tHat S 1 = !![2, 0; 0, 2] ∧
    (∀ W ∈ unitaryGroup (Fin 2) ℂ, IsSVD (tHat A 1) W (tHat S 1) W) ∧
    IsSVD (tHat A 1) 1 (tHat S 1) 1 ∧ (1 : Matrix (Fin 2) (Fin 2) ℂ) ≠ tHat U 1 := by
  have hall : ∀ W ∈ unitaryGroup (Fin 2) ℂ, IsSVD (tHat A 1) W (tHat S 1) W := by
    intro W hW
    rw [tHat_A1, tHat_S1]
    refine ⟨hW, hW, isSingularDiag_22, ?_⟩
    have h2 : (!![2, 0; 0, 2] : Matrix (Fin 2) (Fin 2) ℂ) = (2 : ℂ) • 1 := by
      ext i k
      fin_cases i <;> fin_cases k <;> simp
    rw [h2, Matrix.mul_smul, Matrix.mul_one, Matrix.smul_mul, ← star_eq_conjTranspose,
      mem_unitaryGroup_iff.1 hW]
  refine ⟨?_, ?_, ?_, tHat_S1, hall, hall 1 (one_mem _), ?_⟩
  · rw [tHat_A0]
    ext i k
    fin_cases i <;> fin_cases k <;> simp
  · rw [tHat_A0]
    funext i
    fin_cases i <;> simp [Q, mulVec, dotProduct, Fin.sum_univ_two] <;> sqrt_two_tac
  · rw [tHat_A0]
    funext i
    fin_cases i <;> simp [Q, mulVec, dotProduct, Fin.sum_univ_two] <;> sqrt_two_tac
  · rw [tHat_U]
    intro h
    have := congrFun (congrFun h 0) 1
    simp [Q] at this
    exact sqrt2_ne this.symm

/-- The rank-`(1, 1)` multirank truncation `ℬ = [𝒜]_r` of Example 68:
`𝐁₁ = [[2, 2], [2, 2]]`, `𝐁₂ = [[1, 1], [1, 1]]`. -/
def B : Matrix (Fin 2) (Fin 2) (KM hadamard2) := ofSlices !![2, 2; 2, 2] !![1, 1; 1, 1]

/-- `F₂ = c W` with `c = √2` and `W = F₂/√2` unitary. -/
theorem hadamard2_eq_smul_unitary :
    ∃ W ∈ unitaryGroup (Fin 2) ℂ, hadamard2 = ((Real.sqrt 2 : ℝ) : ℂ) • W := by
  refine ⟨Q.map (↑), Qc_unitary, ?_⟩
  ext i k
  fin_cases i <;> fin_cases k <;> simp [Q, hadamard2]
  field_simp

private lemma tnorm_A_sub_B_sq : tnorm (A - B) ^ 2 = 4 := by
  rw [tnorm, Real.sq_sqrt (by positivity)]
  simp [Fin.sum_univ_two, A, B, ofSlices]
  norm_num

/-- **Example 68** (Worked example: multirank truncation). Continuing Example 67, we truncate
`𝒜` to `⋆_t`-multirank `r = (1, 1)`: in the transform domain
`([𝒜]_r)^₁ = 6 · (1/√2)[1, 1]ᵀ (1/√2)[1, 1] = [[3, 3], [3, 3]]` and
`([𝒜]_r)^₂ = [[1, 1], [1, 1]]`; moving back, `[𝒜]_r = ℬ` with `𝐁₁ = [[2, 2], [2, 2]]`,
`𝐁₂ = [[1, 1], [1, 1]]`. The approximation error is `‖𝒜 - ℬ‖_F² = 4`, which equals the sum
of the squared dropped singular values scaled by `|c|⁻²`: `(2² + 2²)/2 = 4`. -/
theorem example68 :
    multirank A = ![2, 2] ∧
    ∀ hr : (![1, 1] : Fin 2 → ℕ) ≤ multirank A,
      truncSlices A U S U ![1, 1] hr 0 = !![3, 3; 3, 3] ∧
      truncSlices A U S U ![1, 1] hr 1 = !![1, 1; 1, 1] ∧
      tInv (truncSlices A U S U ![1, 1] hr) = B ∧
      tnorm (A - B) ^ 2 = 4 ∧
      (∑ j : Fin 2, ∑ i : Fin (min 2 2),
        (if (![1, 1] : Fin 2 → ℕ) j ≤ (i : ℕ) ∧ (i : ℕ) < (tHat A j).rank then
          (RCLike.re (diagEntry (tHat S j) i)) ^ 2 else 0)) = 2 ^ 2 + 2 ^ 2 ∧
      tnorm (A - B) ^ 2 = (‖((Real.sqrt 2 : ℝ) : ℂ)‖ ^ 2)⁻¹ * (2 ^ 2 + 2 ^ 2) := by
  refine ⟨?_, fun hr => ?_⟩
  · funext j
    rw [multirank, rank_A]
    fin_cases j <;> rfl
  have h0 : truncSlices A U S U ![1, 1] hr 0 = !![3, 3; 3, 3] := by
    simp only [truncSlices]
    rw [truncSub_eq_truncProd, tHat_U, tHat_S0]
    ext i l
    fin_cases i <;> fin_cases l <;> simp [truncProd, Fin.sum_univ_two, Q] <;> sqrt_two_tac
  have h1 : truncSlices A U S U ![1, 1] hr 1 = !![1, 1; 1, 1] := by
    simp only [truncSlices]
    rw [truncSub_eq_truncProd, tHat_U, tHat_S1]
    ext i l
    fin_cases i <;> fin_cases l <;> simp [truncProd, Fin.sum_univ_two, Q] <;> sqrt_two_tac
  refine ⟨h0, h1, ?_, tnorm_A_sub_B_sq, ?_, ?_⟩
  · have hB : truncSlices A U S U ![1, 1] hr = tHat B := by
      funext j
      fin_cases j
      · rw [show ((⟨0, by decide⟩ : Fin 2)) = 0 from rfl, h0, B, tHat_ofSlices_zero]
        ext i k
        fin_cases i <;> fin_cases k <;> simp <;> norm_num
      · rw [show ((⟨1, by decide⟩ : Fin 2)) = 1 from rfl, h1, B, tHat_ofSlices_one]
        ext i k
        fin_cases i <;> fin_cases k <;> simp <;> norm_num
    rw [hB, tInv_tHat]
  · simp only [rank_A, sum_min22, Fin.sum_univ_two]
    simp [diagEntry, tHat_S0, tHat_S1]
  · rw [tnorm_A_sub_B_sq, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _),
      Real.sq_sqrt (by norm_num)]
    norm_num

/-- The error formula of Theorem 37 as literally printed, with the factor `|c|⁻¹`, is false
on Example 68 (`c = √2`): `(2² + 2²)/√2 ≠ 4`. This justifies reading `|c|⁻¹` as `|c|⁻²`. -/
theorem example68_literal_false :
    tnorm (A - B) ^ 2 ≠ (‖((Real.sqrt 2 : ℝ) : ℂ)‖)⁻¹ * (2 ^ 2 + 2 ^ 2) := by
  rw [tnorm_A_sub_B_sq, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _)]
  intro h
  have hs : Real.sqrt 2 * Real.sqrt 2 = 2 := Real.mul_self_sqrt (by norm_num)
  have hpos : 0 < Real.sqrt 2 := Real.sqrt_pos.2 (by norm_num)
  field_simp at h
  have h2 : Real.sqrt 2 = 2 := by linarith
  rw [h2] at hs
  norm_num at hs

end AppendixA

end Tubal
