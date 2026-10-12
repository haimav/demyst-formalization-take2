import TubalAlgebra.Tensor

/-!
# Practical tubal algebra: the transform domain (Section 6: Fact 25, Examples 26, 27)

Given a tensor `𝒜 ∈ ℝ^{m×p×n}` (a matrix of tubes), the transformed tensor is
`𝒜̂ := 𝒜 ×₃ M ∈ ℂ^{m×p×n}`, i.e. `𝒜̂_{ikj} = ∑ₗ M_{jl} 𝒜_{ikl}`; we represent it by its
frontal slices `𝒜̂_j ∈ ℂ^{m×p}` (`tHat A j`).
The facewise product `𝒜 Δ ℬ` multiplies corresponding frontal slices.
-/

open Matrix Complex

noncomputable section

namespace Tubal

variable {n : ℕ} {M : Matrix (Fin n) (Fin n) ℂ}

/-- The mode-3 product `𝒳 ×₃ M` of a (complex) third-order tensor with a matrix:
`(𝒳 ×₃ M)_{ikj} = ∑ₗ 𝒳_{ikl} M_{jl}`. -/
def mode3 {m p : ℕ} (X : Fin m → Fin p → Fin n → ℂ) (M : Matrix (Fin n) (Fin n) ℂ) :
    Fin m → Fin p → Fin n → ℂ :=
  fun i k j => ∑ l, X i k l * M j l

/-- The frontal slices `𝒜̂_j` of the transformed tensor `𝒜̂ := 𝒜 ×₃ M`. -/
def tHat {m p : ℕ} (A : Matrix (Fin m) (Fin p) (KM M)) : Fin n → Matrix (Fin m) (Fin p) ℂ :=
  fun j i k => (A i k).hat j

/-- `tHat` is indeed `𝒜 ×₃ M` (sliced frontally). -/
theorem tHat_eq_mode3 {m p : ℕ} (A : Matrix (Fin m) (Fin p) (KM M)) (i : Fin m) (k : Fin p)
    (j : Fin n) :
    tHat A j i k = mode3 (fun i k l => ((toTensor A i k l : ℝ) : ℂ)) M i k j := by
  simp only [tHat, KM.hat, mode3, toTensor, mulVec, dotProduct, toC_apply]
  exact Finset.sum_congr rfl fun l _ => mul_comm _ _

/-- The facewise product `𝒳 Δ 𝒴`: its `j`-th frontal slice is `𝒳_j 𝒴_j`. -/
def facewise {m p l : ℕ} (X : Fin n → Matrix (Fin m) (Fin p) ℂ)
    (Y : Fin n → Matrix (Fin p) (Fin l) ℂ) : Fin n → Matrix (Fin m) (Fin l) ℂ :=
  fun j => X j * Y j

/-- The facewise product of two real tensors (`ℝ^{m×p×n}` and `ℝ^{p×l×n}`). -/
def facewiseReal {m p l : ℕ} (A : Fin m → Fin p → Fin n → ℝ) (B : Fin p → Fin l → Fin n → ℝ) :
    Fin m → Fin l → Fin n → ℝ :=
  fun i k j => ∑ q, A i q j * B q k j

/-- The transform is injective on tensors. -/
theorem tHat_injective [Fact (Admissible M)] {m p : ℕ} :
    Function.Injective (tHat : Matrix (Fin m) (Fin p) (KM M) → Fin n → Matrix (Fin m) (Fin p) ℂ) := by
  intro A B h
  funext i k
  apply KM.hat_injective
  funext j
  exact congrFun (congrFun (congrFun h j) i) k

/-- **Fact 25.** For tensors `𝒜, ℬ, 𝒞` of compatible sizes: `𝒞 = 𝒜 ⋆_M ℬ ⟺ 𝒞̂ = 𝒜̂ Δ ℬ̂`. -/
theorem fact25 [Fact (Admissible M)] {m p l : ℕ} (A : Matrix (Fin m) (Fin p) (KM M))
    (B : Matrix (Fin p) (Fin l) (KM M)) (C : Matrix (Fin m) (Fin l) (KM M)) :
    C = A * B ↔ tHat C = facewise (tHat A) (tHat B) := by
  have hmul : tHat (A * B) = facewise (tHat A) (tHat B) := by
    funext j i k
    simp only [tHat, facewise, Matrix.mul_apply, KM.hat_sum, Finset.sum_apply, KM.hat_mul,
      Pi.mul_apply]
  constructor
  · rintro rfl
    exact hmul
  · intro h
    exact tHat_injective (h.trans hmul.symm)

@[simp] theorem tHat_add {m p : ℕ} (A B : Matrix (Fin m) (Fin p) (KM M)) :
    tHat (A + B) = tHat A + tHat B := by
  funext j i k
  simp [tHat]

@[simp] theorem tHat_sub {m p : ℕ} (A B : Matrix (Fin m) (Fin p) (KM M)) :
    tHat (A - B) = tHat A - tHat B := by
  funext j i k
  simp [tHat]

theorem tHat_mul [Fact (Admissible M)] {m p l : ℕ} (A : Matrix (Fin m) (Fin p) (KM M))
    (B : Matrix (Fin p) (Fin l) (KM M)) : tHat (A * B) = facewise (tHat A) (tHat B) :=
  (fact25 A B (A * B)).1 rfl

/-- The identity tensor `ℐ_m` (diagonal with `e_M` on the diagonal). -/
def identityTensor [Fact (Admissible M)] (m : ℕ) : Matrix (Fin m) (Fin m) (KM M) :=
  diagonal (fun _ => 1)

/-- **Example 26** (Identity tensor). `ℐ_m` is the identity tensor of size `m`:
`ℐ_m ⋆_M 𝒜 = 𝒜` and `ℬ ⋆_M ℐ_m = ℬ`; the frontal slices of the transformed tensor `ℐ̂_m` are
the identity matrices of size `m`; and `ê_M = M e_M = 1`. -/
theorem example26 [Fact (Admissible M)] (m : ℕ) :
    (∀ {p : ℕ} (A : Matrix (Fin m) (Fin p) (KM M)), identityTensor m * A = A) ∧
    (∀ {p : ℕ} (B : Matrix (Fin p) (Fin m) (KM M)), B * identityTensor m = B) ∧
    (∀ j, tHat (identityTensor m : Matrix (Fin m) (Fin m) (KM M)) j = 1) ∧
    (1 : KM M).hat = fun _ => 1 := by
  have hI : (identityTensor m : Matrix (Fin m) (Fin m) (KM M)) = 1 := diagonal_one
  refine ⟨fun A => by rw [hI]; exact Matrix.one_mul A, fun B => by rw [hI]; exact Matrix.mul_one B,
    fun j => ?_,
    KM.hat_one⟩
  rw [hI]
  funext i k
  by_cases hik : i = k
  · subst hik; simp [tHat]
  · simp [tHat, hik]

/-- **Example 27** (Hermitian transpose in the transform domain). For a tensor `𝒳`,
`(𝒳ᴴ)^ = 𝒳̂^{HΔ}`, the tensor obtained by the Hermitian conjugate of the frontal slices of
`𝒳̂`. -/
theorem example27 [Fact (Admissible M)] {m p : ℕ} (X : Matrix (Fin m) (Fin p) (KM M)) :
    tHat Xᴴ = fun j => (tHat X j)ᴴ := by
  funext j i k
  simp [tHat, conjTranspose_apply]

/-! ### Inverse transform -/

/-- The inverse transform of a family of complex frontal slices: the tensor whose tubes are
the real parts of `M⁻¹` applied to the tubes. For slices coming from a real tensor (or more
generally respecting the conjugation pattern of `M`), this is exact (`tHat_tInv`). -/
def tInv {m p : ℕ} (X : Fin n → Matrix (Fin m) (Fin p) ℂ) : Matrix (Fin m) (Fin p) (KM M) :=
  fun i k => ⟨fun l => ((M⁻¹ *ᵥ fun j => X j i k) l).re⟩

/-- Slices respecting the conjugation pattern of `M`. -/
def SlicesConjPattern (M : Matrix (Fin n) (Fin n) ℂ) {m p : ℕ}
    (X : Fin n → Matrix (Fin m) (Fin p) ℂ) : Prop :=
  ∀ i k, ConjPattern M (fun j => X j i k)

theorem tHat_conjPattern {m p : ℕ} (A : Matrix (Fin m) (Fin p) (KM M)) :
    SlicesConjPattern M (tHat A) := by
  intro i k
  exact KM.hat_conjPattern (A i k)

theorem tHat_tInv [Fact (Admissible M)] {m p : ℕ} (X : Fin n → Matrix (Fin m) (Fin p) ℂ)
    (hX : SlicesConjPattern M X) : tHat (tInv X : Matrix (Fin m) (Fin p) (KM M)) = X := by
  funext j i k
  have hM := (Fact.out : Admissible M)
  have hr := inv_mulVec_mem_realVectors_of_conjPattern M hM.1 hM.2 (hX i k)
  simp only [tHat, tInv, KM.hat, KM.vec_mk]
  rw [toC_re_of_mem_realVectors hr, mulVec_inv_mulVec' hM.1]

theorem tInv_tHat [Fact (Admissible M)] {m p : ℕ} (A : Matrix (Fin m) (Fin p) (KM M)) :
    tInv (tHat A) = A := by
  funext i k
  have hM := (Fact.out : Admissible M)
  apply KM.ext
  funext l
  simp only [tInv, tHat, KM.hat, KM.vec_mk]
  rw [show (fun j => (M *ᵥ toC (A i k).vec) j) = M *ᵥ toC (A i k).vec from rfl,
    inv_mulVec_mulVec' hM.1]
  simp [toC]

end Tubal
