import Mathlib

/-!
# Matrix SVD and the Eckart–Young theorem (classical background for Section 7)

Over `𝕜 = ℝ` or `ℂ` (`RCLike`), a singular value decomposition of `X ∈ 𝕜^{m×p}` is
`X = U S Vᴴ` with `U, V` unitary and `S` rectangular diagonal with real, non-negative,
non-increasing diagonal entries (the singular values).

The rank-`r` truncation is `U_{:,1:r} S_{1:r,1:r} (V_{:,1:r})ᴴ`. The Eckart–Young theorem says
that it is an optimal rank-`r` approximation in the Frobenius norm.
-/

open Matrix

noncomputable section

namespace Tubal

variable {𝕜 : Type*} [RCLike 𝕜] {m p : ℕ}

/-- The `i`-th diagonal entry of a rectangular `m × p` matrix, `i < min m p`. -/
def diagEntry (S : Matrix (Fin m) (Fin p) 𝕜) (i : Fin (min m p)) : 𝕜 :=
  S (Fin.castLE (min_le_left m p) i) (Fin.castLE (min_le_right m p) i)

/-- `S` is rectangular diagonal with real, non-negative and non-increasing diagonal. -/
def IsSingularDiag (S : Matrix (Fin m) (Fin p) 𝕜) : Prop :=
  (∀ (i : Fin m) (k : Fin p), (i : ℕ) ≠ k → S i k = 0) ∧
  (∀ i, RCLike.im (diagEntry S i) = 0) ∧
  (∀ i, 0 ≤ RCLike.re (diagEntry S i)) ∧
  (∀ i j, i ≤ j → RCLike.re (diagEntry S j) ≤ RCLike.re (diagEntry S i))

/-- `X = U S Vᴴ` is a singular value decomposition. -/
def IsSVD (X : Matrix (Fin m) (Fin p) 𝕜) (U : Matrix (Fin m) (Fin m) 𝕜)
    (S : Matrix (Fin m) (Fin p) 𝕜) (V : Matrix (Fin p) (Fin p) 𝕜) : Prop :=
  U ∈ unitaryGroup (Fin m) 𝕜 ∧ V ∈ unitaryGroup (Fin p) 𝕜 ∧ IsSingularDiag S ∧
    X = U * S * Vᴴ

/-- Existence of the SVD (classical). -/
theorem exists_svd (X : Matrix (Fin m) (Fin p) 𝕜) :
    ∃ U S V, IsSVD X U S V := by
  sorry

/-- The SVD of the complexification of a real matrix. -/
theorem IsSVD.map_ofReal {X : Matrix (Fin m) (Fin p) ℝ} {U S V} (h : IsSVD X U S V) :
    IsSVD (X.map (↑)) (U.map ((↑) : ℝ → ℂ)) (S.map (↑)) (V.map (↑)) := by
  sorry

/-- The SVD of the entry-wise conjugate. -/
theorem IsSVD.map_conj {X : Matrix (Fin m) (Fin p) ℂ} {U S V} (h : IsSVD X U S V) :
    IsSVD (X.map (starRingEnd ℂ)) (U.map (starRingEnd ℂ)) S (V.map (starRingEnd ℂ)) := by
  sorry

/-- The rank of `X` is the number of non-zero singular values. -/
theorem IsSVD.rank_eq {X : Matrix (Fin m) (Fin p) 𝕜} {U S V} (h : IsSVD X U S V) :
    X.rank = Fintype.card {i : Fin (min m p) // diagEntry S i ≠ 0} := by
  sorry

/-- The squared Frobenius norm `‖X‖_F² = ∑ |X_{ik}|²`. -/
def frobSq (X : Matrix (Fin m) (Fin p) 𝕜) : ℝ := ∑ i, ∑ k, ‖X i k‖ ^ 2

/-- The rank-`r` truncation `U_{:,1:r} S_{1:r,1:r} (V_{:,1:r})ᴴ`, written with explicit sums. -/
def truncProd (U : Matrix (Fin m) (Fin m) 𝕜) (S : Matrix (Fin m) (Fin p) 𝕜)
    (V : Matrix (Fin p) (Fin p) 𝕜) (r : ℕ) : Matrix (Fin m) (Fin p) 𝕜 :=
  fun i l => ∑ a : Fin m, ∑ b : Fin p,
    if (a : ℕ) < r ∧ (b : ℕ) < r then U i a * S a b * star (V l b) else 0

/-- The rank-`r` truncation in submatrix form `U_{:,1:r} S_{1:r,1:r} (V_{:,1:r})ᴴ`. -/
def truncSub (U : Matrix (Fin m) (Fin m) 𝕜) (S : Matrix (Fin m) (Fin p) 𝕜)
    (V : Matrix (Fin p) (Fin p) 𝕜) (r : ℕ) (hrm : r ≤ m) (hrp : r ≤ p) :
    Matrix (Fin m) (Fin p) 𝕜 :=
  U.submatrix id (Fin.castLE hrm) * S.submatrix (Fin.castLE hrm) (Fin.castLE hrp) *
    (V.submatrix id (Fin.castLE hrp))ᴴ

theorem truncSub_eq_truncProd (U : Matrix (Fin m) (Fin m) 𝕜) (S : Matrix (Fin m) (Fin p) 𝕜)
    (V : Matrix (Fin p) (Fin p) 𝕜) (r : ℕ) (hrm : r ≤ m) (hrp : r ≤ p) :
    truncSub U S V r hrm hrp = truncProd U S V r := by
  sorry

theorem rank_truncProd_le (U : Matrix (Fin m) (Fin m) 𝕜) (S : Matrix (Fin m) (Fin p) 𝕜)
    (V : Matrix (Fin p) (Fin p) 𝕜) (r : ℕ) : (truncProd U S V r).rank ≤ r := by
  sorry

/-- The truncation error: `‖X - X_r‖_F² = ∑_{i > r} σᵢ²`. -/
theorem IsSVD.frobSq_sub_truncProd {X : Matrix (Fin m) (Fin p) 𝕜} {U S V} (h : IsSVD X U S V)
    (r : ℕ) :
    frobSq (X - truncProd U S V r) =
      ∑ i : Fin (min m p), if r ≤ (i : ℕ) then ‖diagEntry S i‖ ^ 2 else 0 := by
  sorry

/-- **Eckart–Young theorem** (Frobenius norm): the truncated SVD is an optimal rank-`r`
approximation. -/
theorem eckart_young {X : Matrix (Fin m) (Fin p) 𝕜} {U S V} (h : IsSVD X U S V) (r : ℕ)
    (Y : Matrix (Fin m) (Fin p) 𝕜) (hY : Y.rank ≤ r) :
    frobSq (X - truncProd U S V r) ≤ frobSq (X - Y) := by
  sorry

end Tubal
