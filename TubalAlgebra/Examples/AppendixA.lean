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
  sorry

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
  sorry

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
  sorry

/-- The rank-`(1, 1)` multirank truncation `ℬ = [𝒜]_r` of Example 68:
`𝐁₁ = [[2, 2], [2, 2]]`, `𝐁₂ = [[1, 1], [1, 1]]`. -/
def B : Matrix (Fin 2) (Fin 2) (KM hadamard2) := ofSlices !![2, 2; 2, 2] !![1, 1; 1, 1]

/-- `F₂ = c W` with `c = √2` and `W = F₂/√2` unitary. -/
theorem hadamard2_eq_smul_unitary :
    ∃ W ∈ unitaryGroup (Fin 2) ℂ, hadamard2 = ((Real.sqrt 2 : ℝ) : ℂ) • W := by
  sorry

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
  sorry

/-- The error formula of Theorem 37 as literally printed, with the factor `|c|⁻¹`, is false
on Example 68 (`c = √2`): `(2² + 2²)/√2 ≠ 4`. This justifies reading `|c|⁻¹` as `|c|⁻²`. -/
theorem example68_literal_false :
    tnorm (A - B) ^ 2 ≠ (‖((Real.sqrt 2 : ℝ) : ℂ)‖)⁻¹ * (2 ^ 2 + 2 ^ 2) := by
  sorry

end AppendixA

end Tubal
