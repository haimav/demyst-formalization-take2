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

/-- **Remark 22** (first part). For any `u ∈ ℝⁿ` and scalar `α ∈ ℝ`, `α u = (α e_M) ⋆_M u`. -/
theorem remark22_smul_eq [Fact (Admissible M)] (u : KM M) (α : ℝ) :
    α • u = (α • (1 : KM M)) * u := by
  sorry

/-- **Remark 22** (second part). Every `⋆_M`-linear function is also linear. -/
theorem remark22_linear [Fact (Admissible M)] {m p : ℕ}
    (T : (Fin p → KM M) → (Fin m → KM M)) (hT : IsStarMLinear T) :
    ∀ (U V : Fin p → KM M) (α β : ℝ), T (α • U + β • V) = α • T U + β • T V := by
  sorry

/-- **Remark 22** (second part, for functions `ℝ^{p×n} → ℝ^{m×n}`). Every `⋆_M`-linear
function is also linear. -/
theorem remark22_linear_mat (M : Matrix (Fin n) (Fin n) ℂ) [Fact (Admissible M)] {m p : ℕ}
    (S : Matrix (Fin p) (Fin n) ℝ → Matrix (Fin m) (Fin n) ℝ) (hS : IsStarMLinearMat M S) :
    IsLinearMap ℝ S := by
  sorry

/-- **Remark 22** (third part). "However, the converse is not true": there is a tubal ring
`𝕂_M` and a linear function which is not `⋆_M`-linear. -/
theorem remark22_converse_false :
    ¬ ∀ (n : ℕ) (M : Matrix (Fin n) (Fin n) ℂ) [Fact (Admissible M)] (m p : ℕ)
      (T : (Fin p → KM M) → (Fin m → KM M)),
      (∀ (U V : Fin p → KM M) (α β : ℝ), T (α • U + β • V) = α • T U + β • T V) →
      IsStarMLinear T := by
  sorry

/-- A sharper form of Remark 22 (third part): whenever `n ≥ 2`, for every admissible `M`
there is a linear `T : 𝕂_M^1 → 𝕂_M^1` which is not `⋆_M`-linear. (For `n = 1` every linear
map is `⋆_M`-linear, so `n ≥ 2` is needed.) -/
theorem remark22_converse_false' (M : Matrix (Fin n) (Fin n) ℂ) [Fact (Admissible M)]
    (hn : 2 ≤ n) :
    ∃ T : (Fin 1 → KM M) → (Fin 1 → KM M),
      (∀ (U V : Fin 1 → KM M) (α β : ℝ), T (α • U + β • V) = α • T U + β • T V) ∧
      ¬ IsStarMLinear T := by
  sorry

/-- "Let `𝒜 ∈ 𝕂_M^{m×p}` and consider `T(X) = squeeze(𝒜 ⋆_M twist(X))`. We easily see that
`T` is `⋆_M`-linear." -/
theorem isStarMLinearMat_of_tensor (M : Matrix (Fin n) (Fin n) ℂ) [Fact (Admissible M)]
    {m p : ℕ} (A : Matrix (Fin m) (Fin p) (KM M)) :
    IsStarMLinearMat M (fun X => squeeze (A *ᵥ (twist X : Fin p → KM M))) := by
  sorry

/-- "Furthermore, every `⋆_M`-linear function can be represented in this way." -/
theorem exists_tensor_of_isStarMLinearMat (M : Matrix (Fin n) (Fin n) ℂ) [Fact (Admissible M)]
    {m p : ℕ} (S : Matrix (Fin p) (Fin n) ℝ → Matrix (Fin m) (Fin n) ℝ)
    (hS : IsStarMLinearMat M S) :
    ∃ A : Matrix (Fin m) (Fin p) (KM M), ∀ X, S X = squeeze (A *ᵥ (twist X : Fin p → KM M)) := by
  sorry

/-- "Composition of `⋆_M`-linear functions is `⋆_M`-linear, and the representing tensor is the
`⋆_M`-product of the representing tensors." -/
theorem tensor_comp (M : Matrix (Fin n) (Fin n) ℂ) [Fact (Admissible M)] {m p l : ℕ}
    (A : Matrix (Fin m) (Fin p) (KM M)) (B : Matrix (Fin p) (Fin l) (KM M)) :
    (fun X => squeeze (A *ᵥ (twist (squeeze (B *ᵥ (twist X : Fin l → KM M))) : Fin p → KM M)))
      = fun X => squeeze ((A * B) *ᵥ (twist X : Fin l → KM M)) := by
  sorry

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
  sorry

/-- Every `⋆_M`-linear operator has a `⋆_M`-adjoint (so Definition 23 makes sense). -/
theorem exists_isStarMAdjoint [Fact (Admissible M)] {m p : ℕ}
    (T : (Fin p → KM M) → (Fin m → KM M)) (hT : IsStarMLinear T) :
    ∃ T' : (Fin m → KM M) → (Fin p → KM M), IsStarMAdjoint T T' := by
  sorry

/-- **Proposition 24.** Suppose that `T(X) = 𝒜 ⋆_M X`. Then `T*(Y) = 𝒜ᴴ ⋆_M Y`. -/
theorem prop24 [Fact (Admissible M)] {m p : ℕ} (A : Matrix (Fin m) (Fin p) (KM M)) :
    IsStarMAdjoint (fun X => A *ᵥ X) (fun Y => Aᴴ *ᵥ Y) ∧
    ∀ T' : (Fin m → KM M) → (Fin p → KM M), IsStarMAdjoint (fun X => A *ᵥ X) T' →
      T' = fun Y => Aᴴ *ᵥ Y := by
  sorry

end Tubal
