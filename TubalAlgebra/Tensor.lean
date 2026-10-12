import TubalAlgebra.Module

/-!
# Tensors as matrices over `𝕂_M` (Section 5: Definition 21, Remark 22, Definition 23,
Proposition 24)

A tensor `𝒜 ∈ ℝ^{m×p×n}` is identified with a matrix of tubes `𝒜 ∈ 𝕂_M^{m×p}`, i.e. a term of
`Matrix (Fin m) (Fin p) (KM M)`, the tube `𝒜_{ik}` being `(𝒜_{ik1}, …, 𝒜_{ikn})`.
The `⋆_M`-product of two tensors is the usual matrix product over `𝕂_M`:
`(𝒜 ⋆_M ℬ)_{ij} = ∑ₖ 𝒜_{ik} ⋆_M ℬ_{kj}` (this is Mathlib's `Matrix` multiplication `*`), and
the action of a tensor on an oriented matrix is `Matrix.mulVec` (`*ᵥ`).
The `⋆_M`-Hermitian transpose `(𝒜ᴴ)_{ij} := 𝒜*_{ji}` is Mathlib's `Matrix.conjTranspose`
with respect to the `⋆_M`-conjugate.
-/

open Matrix Complex

noncomputable section

namespace Tubal

variable {n : ℕ} {M : Matrix (Fin n) (Fin n) ℂ}

/-- The real third-order tensor `ℝ^{m×p×n}` underlying a matrix of tubes. -/
def toTensor {m p : ℕ} (A : Matrix (Fin m) (Fin p) (KM M)) : Fin m → Fin p → Fin n → ℝ :=
  fun i k j => (A i k).vec j

/-- A real third-order tensor viewed as a matrix of tubes. -/
def ofTensor {m p : ℕ} (X : Fin m → Fin p → Fin n → ℝ) : Matrix (Fin m) (Fin p) (KM M) :=
  fun i k => ⟨X i k⟩

/-- The `⋆_M`-product of tensors is the usual matrix multiplication with `⋆_M` instead of the
usual product: `(𝒜 ⋆_M ℬ)_{ij} = ∑ₖ 𝒜_{ik} ⋆_M ℬ_{kj}`. -/
theorem tensor_mul_apply {m p l : ℕ} (A : Matrix (Fin m) (Fin p) (KM M))
    (B : Matrix (Fin p) (Fin l) (KM M)) (i : Fin m) (j : Fin l) :
    (A * B) i j = ∑ k, A i k * B k j := rfl

/-- **Definition 21** (first part). A function `T : 𝕂_M^p → 𝕂_M^m` is `⋆_M`-linear if for all
`U, V ∈ 𝕂_M^p` and `r, s ∈ 𝕂_M`, `T(r ⋆_M U + s ⋆_M V) = r ⋆_M T(U) + s ⋆_M T(V)`. -/
def IsStarMLinear [Fact (Admissible M)] {m p : ℕ} (T : (Fin p → KM M) → (Fin m → KM M)) :
    Prop :=
  ∀ (U V : Fin p → KM M) (r s : KM M), T (r • U + s • V) = r • T U + s • T V

/-- **Definition 21** (second part). A function `S : ℝ^{p×n} → ℝ^{m×n}` is `⋆_M`-linear if
`twist ∘ S ∘ squeeze` is `⋆_M`-linear. -/
def IsStarMLinearMat (M : Matrix (Fin n) (Fin n) ℂ) [Fact (Admissible M)] {m p : ℕ}
    (S : Matrix (Fin p) (Fin n) ℝ → Matrix (Fin m) (Fin n) ℝ) : Prop :=
  IsStarMLinear ((twist : Matrix (Fin m) (Fin n) ℝ → Fin m → KM M) ∘ S ∘ squeeze)


/-! ### Auxiliary lemmas -/

lemma smul_vec_eq_tube_smul [Fact (Admissible M)] {p : ℕ} (α : ℝ) (U : Fin p → KM M) :
    α • U = (α • (1 : KM M)) • U := by
  funext i
  simp only [Pi.smul_apply, smul_eq_mul]
  rw [KM.smul_mul_assoc', one_mul]

lemma IsStarMLinear.map_zero' [Fact (Admissible M)] {m p : ℕ}
    {T : (Fin p → KM M) → (Fin m → KM M)} (hT : IsStarMLinear T) : T 0 = 0 := by
  have h := hT 0 0 0 0
  simp only [zero_smul, add_zero] at h
  exact h

lemma IsStarMLinear.map_add' [Fact (Admissible M)] {m p : ℕ}
    {T : (Fin p → KM M) → (Fin m → KM M)} (hT : IsStarMLinear T) (U V : Fin p → KM M) :
    T (U + V) = T U + T V := by
  have h := hT U V 1 1
  simp only [one_smul] at h
  exact h

lemma IsStarMLinear.map_smul' [Fact (Admissible M)] {m p : ℕ}
    {T : (Fin p → KM M) → (Fin m → KM M)} (hT : IsStarMLinear T) (r : KM M)
    (U : Fin p → KM M) : T (r • U) = r • T U := by
  have h := hT U 0 r 0
  simp only [zero_smul, add_zero, smul_zero] at h
  exact h

lemma IsStarMLinear.map_sum' [Fact (Admissible M)] {m p : ℕ}
    {T : (Fin p → KM M) → (Fin m → KM M)} (hT : IsStarMLinear T) {ι : Type*} (s : Finset ι)
    (f : ι → Fin p → KM M) : T (∑ i ∈ s, f i) = ∑ i ∈ s, T (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using hT.map_zero'
  | insert a s ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, hT.map_add', ih]

/-- Every `⋆_M`-linear operator is multiplication by a tensor. -/
lemma IsStarMLinear.exists_tensor [Fact (Admissible M)] {m p : ℕ}
    {T : (Fin p → KM M) → (Fin m → KM M)} (hT : IsStarMLinear T) :
    ∃ A : Matrix (Fin m) (Fin p) (KM M), ∀ U, T U = A *ᵥ U := by
  refine ⟨Matrix.of fun i k => T (Pi.single k 1) i, fun U => ?_⟩
  have hU : U = ∑ k, U k • (Pi.single k 1 : Fin p → KM M) := by
    funext i
    simp [Finset.sum_apply, Pi.single_apply]
  conv_lhs => rw [hU]
  rw [hT.map_sum']
  funext i
  simp only [Finset.sum_apply, hT.map_smul', Pi.smul_apply, smul_eq_mul, mulVec, dotProduct,
    Matrix.of_apply]
  exact Finset.sum_congr rfl fun k _ => mul_comm _ _

lemma dotM_sub_right [Fact (Admissible M)] {m : ℕ} (X Y Z : Fin m → KM M) :
    dotM X (Y - Z) = dotM X Y - dotM X Z := by
  simp only [dotM, Pi.sub_apply, mul_sub, Finset.sum_sub_distrib]

/-- **Remark 22** (first part). For any `u ∈ ℝⁿ` and scalar `α ∈ ℝ`, `α u = (α e_M) ⋆_M u`. -/
theorem remark22_smul_eq [Fact (Admissible M)] (u : KM M) (α : ℝ) :
    α • u = (α • (1 : KM M)) * u := by
  rw [KM.smul_mul_assoc', one_mul]

/-- **Remark 22** (second part). Every `⋆_M`-linear function is also linear. -/
theorem remark22_linear [Fact (Admissible M)] {m p : ℕ}
    (T : (Fin p → KM M) → (Fin m → KM M)) (hT : IsStarMLinear T) :
    ∀ (U V : Fin p → KM M) (α β : ℝ), T (α • U + β • V) = α • T U + β • T V := by
  intro U V α β
  rw [smul_vec_eq_tube_smul α U, smul_vec_eq_tube_smul β V, hT,
    ← smul_vec_eq_tube_smul, ← smul_vec_eq_tube_smul]

/-- **Remark 22** (second part, for functions `ℝ^{p×n} → ℝ^{m×n}`). Every `⋆_M`-linear
function is also linear. -/
theorem remark22_linear_mat (M : Matrix (Fin n) (Fin n) ℂ) [Fact (Admissible M)] {m p : ℕ}
    (S : Matrix (Fin p) (Fin n) ℝ → Matrix (Fin m) (Fin n) ℝ) (hS : IsStarMLinearMat M S) :
    IsLinearMap ℝ S := by
  have hT := remark22_linear _ hS
  refine ⟨fun X Y => ?_, fun c X => ?_⟩
  · have h := hT (twist X) (twist Y) 1 1
    simp only [one_smul] at h
    have := congrArg squeeze h
    exact this
  · have h := hT (twist X) 0 c 0
    simp only [zero_smul, add_zero] at h
    have := congrArg squeeze h
    exact this

/-- A sharper form of Remark 22 (third part): whenever `n ≥ 2`, for every admissible `M`
there is a linear `T : 𝕂_M^1 → 𝕂_M^1` which is not `⋆_M`-linear. (For `n = 1` every linear
map is `⋆_M`-linear, so `n ≥ 2` is needed.) -/
theorem remark22_converse_false' (M : Matrix (Fin n) (Fin n) ℂ) [Fact (Admissible M)]
    (hn : 2 ≤ n) :
    ∃ T : (Fin 1 → KM M) → (Fin 1 → KM M),
      (∀ (U V : Fin 1 → KM M) (α β : ℝ), T (α • U + β • V) = α • T U + β • T V) ∧
      ¬ IsStarMLinear T := by
  by_contra hcon
  push Not at hcon
  -- every linear map `𝕂_M → 𝕂_M` would be `⋆_M`-linear, hence all such maps would commute
  have key : ∀ L : (Fin n → ℝ) →ₗ[ℝ] (Fin n → ℝ), ∀ u : KM M,
      (⟨L u.vec⟩ : KM M) = u * ⟨L (1 : KM M).vec⟩ := by
    intro L u
    let T : (Fin 1 → KM M) → (Fin 1 → KM M) := fun U i => ⟨L (U i).vec⟩
    have hlin : ∀ (U V : Fin 1 → KM M) (α β : ℝ), T (α • U + β • V) = α • T U + β • T V := by
      intro U V α β
      funext i
      simp only [T, Pi.add_apply, Pi.smul_apply]
      apply KM.ext
      simp
    have hstar := (hcon T hlin).map_smul' u (fun _ => 1)
    have := congrFun hstar 0
    simpa [T] using this
  let A : (Fin n → ℝ) →ₗ[ℝ] (Fin n → ℝ) := LinearMap.single ℝ (fun _ => ℝ) ⟨0, by omega⟩ ∘ₗ
    LinearMap.proj ⟨1, by omega⟩
  let B : (Fin n → ℝ) →ₗ[ℝ] (Fin n → ℝ) := LinearMap.single ℝ (fun _ => ℝ) ⟨1, by omega⟩ ∘ₗ
    LinearMap.proj ⟨0, by omega⟩
  have hcomm : ∀ v : Fin n → ℝ, A (B v) = B (A v) := by
    intro v
    have h1 := key A ⟨B v⟩
    have h2 := key B ⟨A v⟩
    have hB := key B ⟨v⟩
    have hA := key A ⟨v⟩
    -- A (B v) = (B v) * a = (v * b) * a and B (A v) = (v * a) * b
    have e1 : (⟨A (B v)⟩ : KM M) = (⟨v⟩ : KM M) * ⟨B (1 : KM M).vec⟩ * ⟨A (1 : KM M).vec⟩ := by
      rw [h1]; congr 1
    have e2 : (⟨B (A v)⟩ : KM M) = (⟨v⟩ : KM M) * ⟨A (1 : KM M).vec⟩ * ⟨B (1 : KM M).vec⟩ := by
      rw [h2]; congr 1
    have : (⟨A (B v)⟩ : KM M) = ⟨B (A v)⟩ := by rw [e1, e2, mul_right_comm]
    exact congrArg KM.vec this
  have := congrFun (hcomm (Pi.single ⟨1, by omega⟩ 1)) ⟨1, by omega⟩
  simp [A, B] at this

/-- **Remark 22** (third part). "However, the converse is not true": there is a tubal ring
`𝕂_M` and a linear function which is not `⋆_M`-linear. -/
theorem remark22_converse_false :
    ¬ ∀ (n : ℕ) (M : Matrix (Fin n) (Fin n) ℂ) [Fact (Admissible M)] (m p : ℕ)
      (T : (Fin p → KM M) → (Fin m → KM M)),
      (∀ (U V : Fin p → KM M) (α β : ℝ), T (α • U + β • V) = α • T U + β • T V) →
      IsStarMLinear T := by
  intro h
  have hadm : Admissible (1 : Matrix (Fin 2) (Fin 2) ℂ) := by
    refine ⟨isUnit_one, fun i => Or.inl fun k => ?_⟩
    by_cases hik : i = k <;> simp [Matrix.one_apply, hik]
  have : Fact (Admissible (1 : Matrix (Fin 2) (Fin 2) ℂ)) := ⟨hadm⟩
  obtain ⟨T, hT, hnot⟩ := remark22_converse_false' (1 : Matrix (Fin 2) (Fin 2) ℂ) le_rfl
  exact hnot (h 2 1 1 1 T hT)

/-- "Let `𝒜 ∈ 𝕂_M^{m×p}` and consider `T(X) = squeeze(𝒜 ⋆_M twist(X))`. We easily see that
`T` is `⋆_M`-linear." -/
theorem isStarMLinearMat_of_tensor (M : Matrix (Fin n) (Fin n) ℂ) [Fact (Admissible M)]
    {m p : ℕ} (A : Matrix (Fin m) (Fin p) (KM M)) :
    IsStarMLinearMat M (fun X => squeeze (A *ᵥ (twist X : Fin p → KM M))) := by
  intro U V r s
  change A *ᵥ (r • U + s • V) = r • (A *ᵥ U) + s • (A *ᵥ V)
  rw [mulVec_add, mulVec_smul, mulVec_smul]

/-- "Furthermore, every `⋆_M`-linear function can be represented in this way." -/
theorem exists_tensor_of_isStarMLinearMat (M : Matrix (Fin n) (Fin n) ℂ) [Fact (Admissible M)]
    {m p : ℕ} (S : Matrix (Fin p) (Fin n) ℝ → Matrix (Fin m) (Fin n) ℝ)
    (hS : IsStarMLinearMat M S) :
    ∃ A : Matrix (Fin m) (Fin p) (KM M), ∀ X, S X = squeeze (A *ᵥ (twist X : Fin p → KM M)) := by
  obtain ⟨A, hA⟩ := IsStarMLinear.exists_tensor hS
  refine ⟨A, fun X => ?_⟩
  have := congrArg squeeze (hA (twist X))
  exact this

/-- "Composition of `⋆_M`-linear functions is `⋆_M`-linear, and the representing tensor is the
`⋆_M`-product of the representing tensors." -/
theorem tensor_comp (M : Matrix (Fin n) (Fin n) ℂ) [Fact (Admissible M)] {m p l : ℕ}
    (A : Matrix (Fin m) (Fin p) (KM M)) (B : Matrix (Fin p) (Fin l) (KM M)) :
    (fun X => squeeze (A *ᵥ (twist (squeeze (B *ᵥ (twist X : Fin l → KM M))) : Fin p → KM M)))
      = fun X => squeeze ((A * B) *ᵥ (twist X : Fin l → KM M)) := by
  funext X
  simp only [twist_squeeze, mulVec_mulVec]

/-- "Composition of `⋆_M`-linear functions is `⋆_M`-linear" (for operators on oriented
matrices). -/
theorem isStarMLinear_comp [Fact (Admissible M)] {m p l : ℕ}
    (T : (Fin p → KM M) → (Fin m → KM M)) (S : (Fin l → KM M) → (Fin p → KM M))
    (hT : IsStarMLinear T) (hS : IsStarMLinear S) : IsStarMLinear (T ∘ S) := by
  intro U V r s
  simp only [Function.comp_apply]
  rw [hS, hT]

/-- "Composition of `⋆_M`-linear functions is `⋆_M`-linear" (for functions between matrices
`ℝ^{l×n} → ℝ^{p×n} → ℝ^{m×n}`). -/
theorem isStarMLinearMat_comp (M : Matrix (Fin n) (Fin n) ℂ) [Fact (Admissible M)] {m p l : ℕ}
    (S₁ : Matrix (Fin p) (Fin n) ℝ → Matrix (Fin m) (Fin n) ℝ)
    (S₂ : Matrix (Fin l) (Fin n) ℝ → Matrix (Fin p) (Fin n) ℝ)
    (h₁ : IsStarMLinearMat M S₁) (h₂ : IsStarMLinearMat M S₂) : IsStarMLinearMat M (S₁ ∘ S₂) := by
  have h : ((twist : Matrix (Fin m) (Fin n) ℝ → Fin m → KM M) ∘ (S₁ ∘ S₂) ∘
        (squeeze : (Fin l → KM M) → Matrix (Fin l) (Fin n) ℝ)) =
      ((twist : Matrix (Fin m) (Fin n) ℝ → Fin m → KM M) ∘ S₁ ∘
        (squeeze : (Fin p → KM M) → Matrix (Fin p) (Fin n) ℝ)) ∘
        ((twist : Matrix (Fin p) (Fin n) ℝ → Fin p → KM M) ∘ S₂ ∘
          (squeeze : (Fin l → KM M) → Matrix (Fin l) (Fin n) ℝ)) := by
    funext U
    simp only [Function.comp_apply, squeeze_twist]
  unfold IsStarMLinearMat
  rw [h]
  exact isStarMLinear_comp _ _ h₁ h₂

/-- Section 5.1: with scalar multiplication by tubes (element-wise) and the `⋆_M`-Hermitian
transpose, the tensors `𝕂_M^{m×m}` form a `*`-algebra over `𝕂_M`: the `*`-algebra axioms
(the `⋆_M`-Hermitian transpose is an involutive, additive, anti-multiplicative map, compatible
with tube scalars `(r 𝒜)ᴴ = r* 𝒜ᴴ`), and scalar multiplication is entry-wise. -/
theorem tensor_starAlgebra [Fact (Admissible M)] (m : ℕ) :
    (∀ A : Matrix (Fin m) (Fin m) (KM M), Aᴴᴴ = A) ∧
    (∀ A B : Matrix (Fin m) (Fin m) (KM M), (A + B)ᴴ = Aᴴ + Bᴴ) ∧
    (∀ A B : Matrix (Fin m) (Fin m) (KM M), (A * B)ᴴ = Bᴴ * Aᴴ) ∧
    (1 : Matrix (Fin m) (Fin m) (KM M))ᴴ = 1 ∧
    (∀ (r : KM M) (A : Matrix (Fin m) (Fin m) (KM M)), (r • A)ᴴ = star r • Aᴴ) ∧
    (∀ (r : KM M) (A : Matrix (Fin m) (Fin m) (KM M)) i j, (r • A) i j = r * A i j) ∧
    (∀ (r : KM M) (A B : Matrix (Fin m) (Fin m) (KM M)), r • (A * B) = (r • A) * B ∧
      r • (A * B) = A * (r • B)) := by
  refine ⟨fun A => conjTranspose_conjTranspose A, fun A B => conjTranspose_add A B,
    fun A B => conjTranspose_mul A B, conjTranspose_one, fun r A => ?_, fun r A i j => rfl,
    fun r A B => ⟨(Matrix.smul_mul r A B).symm, (Matrix.mul_smul A r B).symm⟩⟩
  refine Matrix.ext fun i j => ?_
  change star (r * A j i) = star r * star (A j i)
  rw [star_mul, mul_comm]

/-- "For every compatibly sized `𝒜` and `ℬ` we have `(𝒜 ⋆_M ℬ)ᴴ = ℬᴴ ⋆_M 𝒜ᴴ`." -/
theorem conjTranspose_tensor_mul [Fact (Admissible M)] {m p l : ℕ}
    (A : Matrix (Fin m) (Fin p) (KM M)) (B : Matrix (Fin p) (Fin l) (KM M)) :
    (A * B)ᴴ = Bᴴ * Aᴴ :=
  Matrix.conjTranspose_mul A B

/-- `𝒰ᴴ` as in the paper: `(𝒜ᴴ)_{ij} = 𝒜*_{ji}`. -/
theorem conjTranspose_tensor_apply {m p : ℕ} (A : Matrix (Fin m) (Fin p) (KM M))
    (i : Fin p) (j : Fin m) : Aᴴ i j = star (A j i) := rfl

/-- **Definition 23.** `T* : 𝕂_M^m → 𝕂_M^p` is the `⋆_M`-adjoint of a `⋆_M`-linear operator
`T : 𝕂_M^p → 𝕂_M^m` with respect to the `⋆_M`-dot product if for all `X ∈ 𝕂_M^p` and
`Y ∈ 𝕂_M^m` we have `T(X) ·_M Y = X ·_M T*(Y)`.

(The paper writes `X ∈ 𝕂_M^m`, `Y ∈ 𝕂_M^p`, which is a typo: `T(X)` requires `X ∈ 𝕂_M^p`.) -/
def IsStarMAdjoint [Fact (Admissible M)] {m p : ℕ} (T : (Fin p → KM M) → (Fin m → KM M))
    (T' : (Fin m → KM M) → (Fin p → KM M)) : Prop :=
  ∀ (X : Fin p → KM M) (Y : Fin m → KM M), dotM (T X) Y = dotM X (T' Y)

/-- The `⋆_M`-adjoint is unique (Definition 23: "the unique operator"). -/
theorem isStarMAdjoint_unique [Fact (Admissible M)] {m p : ℕ}
    (T : (Fin p → KM M) → (Fin m → KM M)) (T₁ T₂ : (Fin m → KM M) → (Fin p → KM M))
    (h₁ : IsStarMAdjoint T T₁) (h₂ : IsStarMAdjoint T T₂) : T₁ = T₂ := by
  funext Y
  have h : ∀ X, dotM X (T₁ Y - T₂ Y) = 0 := by
    intro X
    rw [dotM_sub_right, ← h₁ X Y, ← h₂ X Y, sub_self]
  have := ((theorem20 M (T₁ Y - T₂ Y) 0 0 0 0).2.2.2).mp (h _)
  exact sub_eq_zero.mp this

/-- **Proposition 24.** Suppose that `T(X) = 𝒜 ⋆_M X`. Then `T*(Y) = 𝒜ᴴ ⋆_M Y`. -/
theorem prop24 [Fact (Admissible M)] {m p : ℕ} (A : Matrix (Fin m) (Fin p) (KM M)) :
    IsStarMAdjoint (fun X => A *ᵥ X) (fun Y => Aᴴ *ᵥ Y) ∧
    ∀ T' : (Fin m → KM M) → (Fin p → KM M), IsStarMAdjoint (fun X => A *ᵥ X) T' →
      T' = fun Y => Aᴴ *ᵥ Y := by
  have hadj : IsStarMAdjoint (fun X => A *ᵥ X) (fun Y => Aᴴ *ᵥ Y) := by
    intro X Y
    simp only [dotM, mulVec, dotProduct, star_sum, star_mul, Finset.sum_mul, Finset.mul_sum,
      conjTranspose_apply]
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun i _ => by ring
  exact ⟨hadj, fun T' hT' => isStarMAdjoint_unique _ _ _ hT' hadj⟩

/-- Every `⋆_M`-linear operator has a `⋆_M`-adjoint (so Definition 23 makes sense). -/
theorem exists_isStarMAdjoint [Fact (Admissible M)] {m p : ℕ}
    (T : (Fin p → KM M) → (Fin m → KM M)) (hT : IsStarMLinear T) :
    ∃ T' : (Fin m → KM M) → (Fin p → KM M), IsStarMAdjoint T T' := by
  obtain ⟨A, hA⟩ := hT.exists_tensor
  refine ⟨fun Y => Aᴴ *ᵥ Y, fun X Y => ?_⟩
  rw [hA]
  exact (prop24 A).1 X Y

end Tubal
