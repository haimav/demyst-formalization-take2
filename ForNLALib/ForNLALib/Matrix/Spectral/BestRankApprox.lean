/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Matrix.Spectral.BestRankApprox

/-!
# Truncating an arbitrary thin SVD

Proposed additions to NLAlib's `NLAlib.Matrix.Spectral.BestRankApprox`. For any thin SVD
$\mathbf{A} = \mathbf{U} \operatorname{diag}(\boldsymbol{\sigma}) \mathbf{V}^{\mathsf{H}}$ with
$k$ columns (`NLAlib.IsSVD`), not only the chosen one behind `NLAlib.truncatedSVD`, keeping the
entries $\boldsymbol{\sigma}_i$ with $i < j$ gives the squared Frobenius error
$\sum_{i \ge j} \boldsymbol{\sigma}_i^2$, sorted or not; when $\boldsymbol{\sigma}$ is
non-increasing, the truncation is a best approximation of rank at most $j$
(`NLAlib.IsBestRankApprox`). This is the form in which a specific SVD, such as one built slice by
slice, enters the Eckart–Young theorem.

## Main results

* `NLAlib.IsSVD.frobNorm_sub_mul_diagonal_mul_conjTranspose_sq`: the error of truncating any thin
  SVD.
* `NLAlib.IsSVD.isBestRankApprox_mul_diagonal_mul_conjTranspose`: Eckart–Young for any thin SVD
  with non-increasing $\boldsymbol{\sigma}$.
-/

@[expose] public section

open scoped Matrix

namespace NLAlib

variable {𝕜 : Type*} [RCLike 𝕜] {m n : Type*} [Fintype m] [Fintype n]

namespace IsSVD

variable {k : ℕ} {A : Matrix m n 𝕜} {U : Matrix m (Fin k) 𝕜} {σ : Fin k → ℝ}
  {V : Matrix n (Fin k) 𝕜}

/-- The truncation of an SVD is an SVD of the truncated matrix, with the entries
$\boldsymbol{\sigma}_i$, $i \ge j$, set to zero. -/
private theorem truncation (h : IsSVD A U σ V) (j : ℕ) :
    IsSVD (U * Matrix.diagonal (fun i : Fin k => if (i : ℕ) < j then ((σ i : ℝ) : 𝕜) else 0) *
      Vᴴ) U (fun i => if (i : ℕ) < j then σ i else 0) V := by
  refine ⟨h.hasOrthonormalCols_left, h.hasOrthonormalCols_right, fun i => ?_, ?_⟩
  · split_ifs
    exacts [h.nonneg i, le_rfl]
  · have hd : (fun i : Fin k => (((if (i : ℕ) < j then σ i else 0 : ℝ)) : 𝕜)) =
        fun i : Fin k => if (i : ℕ) < j then ((σ i : ℝ) : 𝕜) else 0 := by
      funext i
      split_ifs
      exacts [rfl, RCLike.ofReal_zero]
    rw [hd]

/-- The error of truncating an SVD is an SVD of the error, with the entries
$\boldsymbol{\sigma}_i$, $i < j$, set to zero. -/
private theorem sub_truncation (h : IsSVD A U σ V) (j : ℕ) :
    IsSVD (A - U * Matrix.diagonal (fun i : Fin k => if (i : ℕ) < j then ((σ i : ℝ) : 𝕜) else 0) *
      Vᴴ) U (fun i => if j ≤ (i : ℕ) then σ i else 0) V := by
  refine ⟨h.hasOrthonormalCols_left, h.hasOrthonormalCols_right, fun i => ?_, ?_⟩
  · split_ifs
    exacts [h.nonneg i, le_rfl]
  · have hd : Matrix.diagonal (fun i => ((σ i : ℝ) : 𝕜)) -
        Matrix.diagonal (fun i : Fin k => if (i : ℕ) < j then ((σ i : ℝ) : 𝕜) else 0) =
        Matrix.diagonal fun i : Fin k => (((if j ≤ (i : ℕ) then σ i else 0 : ℝ)) : 𝕜) := by
      rw [Matrix.diagonal_sub]
      congr 1
      funext i
      by_cases hi : (i : ℕ) < j
      · rw [if_pos hi, if_neg (not_le.mpr hi), sub_self, RCLike.ofReal_zero]
      · rw [if_neg hi, if_pos (not_lt.mp hi), sub_zero]
    rw [← hd, Matrix.mul_sub, Matrix.sub_mul, ← h.eq]

/-- The truncation of an SVD after $j$ entries has rank at most $j$. -/
private theorem rank_truncation_le (h : IsSVD A U σ V) (j : ℕ) :
    (U * Matrix.diagonal (fun i : Fin k => if (i : ℕ) < j then ((σ i : ℝ) : 𝕜) else 0) *
      Vᴴ).rank ≤ j := by
  rw [(h.truncation j).rank_eq]
  refine (Finset.card_le_card_of_injOn (fun i : Fin k => (i : ℕ)) (fun i hi => ?_)
    Fin.val_injective.injOn).trans_eq (Finset.card_range j)
  rw [Finset.mem_coe, Finset.mem_filter] at hi
  rw [Finset.mem_coe, Finset.mem_range]
  by_contra hij
  exact hi.2 (if_neg hij)

/-- **The error of truncating any thin SVD.** If
$\mathbf{A} = \mathbf{U} \operatorname{diag}(\boldsymbol{\sigma}) \mathbf{V}^{\mathsf{H}}$ is an
SVD with $k$ columns, sorted or not, then keeping the entries $\boldsymbol{\sigma}_i$ with $i < j$
leaves the squared Frobenius error
$$\bigl\|\mathbf{A} - \mathbf{U} \operatorname{diag}(\boldsymbol{\sigma}_0, \dots,
  \boldsymbol{\sigma}_{j-1}, 0, \dots, 0) \mathbf{V}^{\mathsf{H}}\bigr\|_{\mathsf{F}}^2
  = \sum_{j \le i < k} \boldsymbol{\sigma}_i^2\,.$$
[GolubVanLoan2013, §2.4]; there for the SVD with sorted singular values.
Port of `Tubal.IsSVD.frobSq_sub_truncProd` (haimav/demyst-formalization-take2, commit
`7d69f60`), there for a full SVD with square `Fin` factors and a sorted rectangular
diagonal. -/
theorem frobNorm_sub_mul_diagonal_mul_conjTranspose_sq (h : IsSVD A U σ V) (j : ℕ) :
    frobNorm (A - U *
        Matrix.diagonal (fun i : Fin k => if (i : ℕ) < j then ((σ i : ℝ) : 𝕜) else 0) * Vᴴ) ^ 2 =
      ∑ i : Fin k with j ≤ i.val, σ i ^ 2 := by
  rw [(h.sub_truncation j).frobNorm_sq_eq, Finset.sum_filter]
  refine Finset.sum_congr rfl fun i _ => ?_
  split_ifs
  · rfl
  · exact zero_pow two_ne_zero

/-- For an SVD with $k$ columns and non-increasing $\boldsymbol{\sigma}$, the tail sum of
$\boldsymbol{\sigma}_i^2$ is the tail sum of the squared singular values:
$\sum_{j \le i < k} \boldsymbol{\sigma}_i^2 =
\sum_{j \le i < \min(\lvert m \rvert, \lvert n \rvert)} \sigma_i(\mathbf{A})^2$. -/
private theorem sum_filter_sq_eq_sum_Ico (h : IsSVD A U σ V) (hσ : Antitone σ) (j : ℕ) :
    ∑ i : Fin k with j ≤ i.val, σ i ^ 2 =
      ∑ i ∈ Finset.Ico j (min (Fintype.card m) (Fintype.card n)), singularValues A i ^ 2 := by
  have hkm : k ≤ Fintype.card m := by
    simpa only [Fintype.card_fin] using h.hasOrthonormalCols_left.card_le
  have hkn : k ≤ Fintype.card n := by
    simpa only [Fintype.card_fin] using h.hasOrthonormalCols_right.card_le
  calc ∑ i : Fin k with j ≤ i.val, σ i ^ 2
      = ∑ i ∈ Finset.range k, if j ≤ i then singularValues A i ^ 2 else 0 := by
        rw [Finset.sum_filter,
          ← Fin.sum_univ_eq_sum_range (fun i => if j ≤ i then singularValues A i ^ 2 else 0)]
        exact Finset.sum_congr rfl fun i _ => by simp only [h.singularValues_eq hσ i]
    _ = ∑ i ∈ Finset.range (min (Fintype.card m) (Fintype.card n)),
          if j ≤ i then singularValues A i ^ 2 else 0 := by
        refine Finset.sum_subset (Finset.range_mono (le_min hkm hkn)) fun i _ hi => ?_
        rw [h.singularValues_of_le (not_lt.mp fun hik => hi (Finset.mem_range.mpr hik)),
          zero_pow two_ne_zero, ite_self]
    _ = ∑ i ∈ Finset.Ico j (min (Fintype.card m) (Fintype.card n)), singularValues A i ^ 2 := by
        rw [← Finset.sum_filter, Finset.range_eq_Ico, Finset.Ico_filter_le,
          max_eq_right (Nat.zero_le j)]

/-- **Eckart–Young for any thin SVD** with non-increasing singular values. If
$\mathbf{A} = \mathbf{U} \operatorname{diag}(\boldsymbol{\sigma}) \mathbf{V}^{\mathsf{H}}$ is an
SVD with $k$ columns and $\boldsymbol{\sigma}_0 \ge \dots \ge \boldsymbol{\sigma}_{k-1}$, then for
every $j$ the truncation
$\mathbf{U} \operatorname{diag}(\boldsymbol{\sigma}_0, \dots, \boldsymbol{\sigma}_{j-1}, 0, \dots,
0) \mathbf{V}^{\mathsf{H}}$ is a best approximation of $\mathbf{A}$ of rank at most $j$. This
holds for every such SVD, not only the chosen one behind
$\llbracket \mathbf{A} \rrbracket_j$, and for every $k$, not only
$k = \min(\lvert m \rvert, \lvert n \rvert)$.
[GolubVanLoan2013, Theorem 2.4.8]; [HornJohnson2013, §7.4.9]; there for the truncation of an SVD
with square unitary factors, here for any thin SVD with sorted $\boldsymbol{\sigma}$.
Port of `Tubal.eckart_young` (haimav/demyst-formalization-take2, commit `7d69f60`), there for a
full SVD with square `Fin` factors and a sorted rectangular diagonal, through the squared
Frobenius norm.
Result: eckart-young-frobenius -/
theorem isBestRankApprox_mul_diagonal_mul_conjTranspose (h : IsSVD A U σ V) (hσ : Antitone σ)
    (j : ℕ) :
    IsBestRankApprox A j
      (U * Matrix.diagonal (fun i : Fin k => if (i : ℕ) < j then ((σ i : ℝ) : 𝕜) else 0) * Vᴴ) := by
  refine isBestRankApprox_iff.mpr ⟨h.rank_truncation_le j, le_of_eq ?_⟩
  refine (sq_eq_sq₀ (frobNorm_nonneg _) (frobNorm_nonneg _)).mp ?_
  rw [h.frobNorm_sub_mul_diagonal_mul_conjTranspose_sq, frobNorm_sub_truncatedSVD_sq]
  exact h.sum_filter_sq_eq_sum_Ico hσ j

end IsSVD

end NLAlib
