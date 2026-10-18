/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Matrix.Spectral.SVD

/-!
# Full singular value decompositions in block form

Proposed additions to NLAlib's `NLAlib.Matrix.Spectral.SVD`. A thin SVD
$\mathbf{A} = \mathbf{U} \operatorname{diag}(\boldsymbol{\sigma}) \mathbf{V}^{\mathsf{H}}$
(`NLAlib.IsSVD`) and a full SVD carry the same information. Completing $\mathbf{U}$ and
$\mathbf{V}$ by orthonormal columns (`NLAlib.HasOrthonormalCols.exists_fromCols`) to matrices
$\begin{bmatrix} \mathbf{U} & \mathbf{U}' \end{bmatrix}$ and
$\begin{bmatrix} \mathbf{V} & \mathbf{V}' \end{bmatrix}$ with as many columns as rows gives
$$\mathbf{A} = \begin{bmatrix} \mathbf{U} & \mathbf{U}' \end{bmatrix}
  \begin{bmatrix} \operatorname{diag}(\boldsymbol{\sigma}) & \mathbf{0} \\
    \mathbf{0} & \mathbf{0} \end{bmatrix}
  \begin{bmatrix} \mathbf{V} & \mathbf{V}' \end{bmatrix}^{\mathsf{H}},$$
and conversely the leading blocks of such a factorization are a thin SVD. The completed factors
are unitary up to relabelling of their columns
(`NLAlib.HasOrthonormalCols.mul_conjTranspose_self_of_card_eq`). The rectangular diagonal middle
factor of the classical statement is the block matrix
`Matrix.fromBlocks (Matrix.diagonal _) 0 0 0`; no new definition is introduced.

## Main results

* `NLAlib.IsSVD.exists_eq_fromCols_mul_fromBlocks_mul_conjTranspose`: a thin SVD extends to a
  full SVD in block form.
* `NLAlib.isSVD_of_eq_fromCols_mul_fromBlocks_mul_conjTranspose`: a full SVD in block form
  restricts to a thin SVD.
* `NLAlib.exists_eq_fromCols_mul_fromBlocks_mul_conjTranspose`: every matrix has a full SVD in
  block form, with the singular values in non-increasing order.
-/

@[expose] public section

open scoped Matrix

namespace NLAlib

variable {𝕜 : Type*} [RCLike 𝕜] {m n r p q : Type*} [Fintype m] [Fintype n] [Fintype r]
  [Fintype p] [Fintype q] [DecidableEq r] [DecidableEq p] [DecidableEq q]

omit [Fintype m] [Fintype n] [DecidableEq r] [DecidableEq p] [DecidableEq q] in
/-- A product through a block matrix whose only nonzero block is the leading one involves only
the leading column blocks of the outer factors:
$\begin{bmatrix} \mathbf{U} & \mathbf{U}' \end{bmatrix}
\begin{bmatrix} \mathbf{D} & \mathbf{0} \\ \mathbf{0} & \mathbf{0} \end{bmatrix}
\begin{bmatrix} \mathbf{V} & \mathbf{V}' \end{bmatrix}^{\mathsf{H}} =
\mathbf{U}\mathbf{D}\mathbf{V}^{\mathsf{H}}$. -/
private theorem fromCols_mul_fromBlocks_zero_mul_conjTranspose (U : Matrix m r 𝕜)
    (U' : Matrix m p 𝕜) (D : Matrix r r 𝕜) (V : Matrix n r 𝕜) (V' : Matrix n q 𝕜) :
    Matrix.fromCols U U' * Matrix.fromBlocks D 0 0 0 * (Matrix.fromCols V V')ᴴ = U * D * Vᴴ := by
  rw [Matrix.fromCols_mul_fromBlocks, Matrix.conjTranspose_fromCols_eq_fromRows_conjTranspose,
    Matrix.fromCols_mul_fromRows]
  simp only [Matrix.mul_zero, Matrix.zero_mul, add_zero]

/-- **A thin SVD extends to a full SVD in block form.** If
$\mathbf{A} = \mathbf{U} \operatorname{diag}(\boldsymbol{\sigma}) \mathbf{V}^{\mathsf{H}}$ is an
SVD with columns indexed by $r$, then for any index types $p$, $q$ with
$\lvert r \rvert + \lvert p \rvert = \lvert m \rvert$ and
$\lvert r \rvert + \lvert q \rvert = \lvert n \rvert$ there are $\mathbf{U}'$ and $\mathbf{V}'$
such that $\begin{bmatrix} \mathbf{U} & \mathbf{U}' \end{bmatrix}$ and
$\begin{bmatrix} \mathbf{V} & \mathbf{V}' \end{bmatrix}$ have orthonormal columns, so are unitary
up to relabelling, and
$$\mathbf{A} = \begin{bmatrix} \mathbf{U} & \mathbf{U}' \end{bmatrix}
  \begin{bmatrix} \operatorname{diag}(\boldsymbol{\sigma}) & \mathbf{0} \\
    \mathbf{0} & \mathbf{0} \end{bmatrix}
  \begin{bmatrix} \mathbf{V} & \mathbf{V}' \end{bmatrix}^{\mathsf{H}}.$$
[GolubVanLoan2013, §2.4]; there the full SVD has square unitary factors and a rectangular
diagonal middle factor, here the factors are in block form and $\boldsymbol{\sigma}$ is in any
order.
Port of `Tubal.IsSVD` (haimav/demyst-formalization-take2, commit `7d69f60`), there a definition
with square `Fin` factors and a sorted rectangular diagonal; this lemma gives its block-form
counterpart from `NLAlib.IsSVD`. -/
theorem IsSVD.exists_eq_fromCols_mul_fromBlocks_mul_conjTranspose {A : Matrix m n 𝕜}
    {U : Matrix m r 𝕜} {σ : r → ℝ} {V : Matrix n r 𝕜} (h : IsSVD A U σ V)
    (hp : Fintype.card r + Fintype.card p = Fintype.card m)
    (hq : Fintype.card r + Fintype.card q = Fintype.card n) :
    ∃ (U' : Matrix m p 𝕜) (V' : Matrix n q 𝕜),
      HasOrthonormalCols (Matrix.fromCols U U') ∧ HasOrthonormalCols (Matrix.fromCols V V') ∧
      A = Matrix.fromCols U U' *
          Matrix.fromBlocks (Matrix.diagonal fun i => ((σ i : ℝ) : 𝕜)) 0 0 0 *
        (Matrix.fromCols V V')ᴴ := by
  obtain ⟨U', hU'⟩ := h.hasOrthonormalCols_left.exists_fromCols hp
  obtain ⟨V', hV'⟩ := h.hasOrthonormalCols_right.exists_fromCols hq
  refine ⟨U', V', hU', hV', ?_⟩
  rw [fromCols_mul_fromBlocks_zero_mul_conjTranspose]
  exact h.eq

/-- **A full SVD in block form restricts to a thin SVD.** If
$\begin{bmatrix} \mathbf{U} & \mathbf{U}' \end{bmatrix}$ and
$\begin{bmatrix} \mathbf{V} & \mathbf{V}' \end{bmatrix}$ have orthonormal columns,
$\boldsymbol{\sigma}$ is nonnegative and
$$\mathbf{A} = \begin{bmatrix} \mathbf{U} & \mathbf{U}' \end{bmatrix}
  \begin{bmatrix} \operatorname{diag}(\boldsymbol{\sigma}) & \mathbf{0} \\
    \mathbf{0} & \mathbf{0} \end{bmatrix}
  \begin{bmatrix} \mathbf{V} & \mathbf{V}' \end{bmatrix}^{\mathsf{H}},$$
then $\mathbf{A} = \mathbf{U} \operatorname{diag}(\boldsymbol{\sigma}) \mathbf{V}^{\mathsf{H}}$ is
a thin SVD. No cardinality hypothesis is needed.
[GolubVanLoan2013, §2.4]; there the thin SVD is read off a full SVD with square factors.
Port of `Tubal.IsSVD` (haimav/demyst-formalization-take2, commit `7d69f60`), there a definition
with square `Fin` factors and a sorted rectangular diagonal; this lemma converts its block-form
counterpart to `NLAlib.IsSVD`. -/
theorem isSVD_of_eq_fromCols_mul_fromBlocks_mul_conjTranspose {A : Matrix m n 𝕜}
    {U : Matrix m r 𝕜} {U' : Matrix m p 𝕜} {σ : r → ℝ} {V : Matrix n r 𝕜} {V' : Matrix n q 𝕜}
    (hU : HasOrthonormalCols (Matrix.fromCols U U'))
    (hV : HasOrthonormalCols (Matrix.fromCols V V')) (hσ : ∀ i, 0 ≤ σ i)
    (hA : A = Matrix.fromCols U U' *
          Matrix.fromBlocks (Matrix.diagonal fun i => ((σ i : ℝ) : 𝕜)) 0 0 0 *
        (Matrix.fromCols V V')ᴴ) :
    IsSVD A U σ V := by
  refine ⟨(hasOrthonormalCols_fromCols_iff.mp hU).1, (hasOrthonormalCols_fromCols_iff.mp hV).1,
    hσ, ?_⟩
  rw [hA, fromCols_mul_fromBlocks_zero_mul_conjTranspose]

/-- **Existence of the full singular value decomposition**, in block form. Every matrix
$\mathbf{A}$ with rows indexed by $m$ and columns by $n$ is
$$\mathbf{A} = \begin{bmatrix} \mathbf{U} & \mathbf{U}' \end{bmatrix}
  \begin{bmatrix} \operatorname{diag}\bigl(\sigma_0(\mathbf{A}), \dots,
    \sigma_{r-1}(\mathbf{A})\bigr) & \mathbf{0} \\ \mathbf{0} & \mathbf{0} \end{bmatrix}
  \begin{bmatrix} \mathbf{V} & \mathbf{V}' \end{bmatrix}^{\mathsf{H}}$$
with $r = \min(\lvert m \rvert, \lvert n \rvert)$, the singular values in non-increasing order,
$\mathbf{U}$, $\mathbf{V}$ having $r$ columns, $\mathbf{U}'$ having $\lvert m \rvert - r$ and
$\mathbf{V}'$ having $\lvert n \rvert - r$ columns, and
$\begin{bmatrix} \mathbf{U} & \mathbf{U}' \end{bmatrix}$,
$\begin{bmatrix} \mathbf{V} & \mathbf{V}' \end{bmatrix}$ with orthonormal columns, hence unitary
up to relabelling.
[HornJohnson2013, Theorem 2.6.3]; [GolubVanLoan2013, Theorem 2.4.1]; there with square unitary
factors and a rectangular diagonal middle factor, here in block form.
Port of `Tubal.exists_svd` (haimav/demyst-formalization-take2, commit `7d69f60`), there with
square `Fin` factors and a rectangular diagonal; the proof here completes the chosen thin SVD
(`NLAlib.isSVD_svdU_svdV`).
Result: svd-existence -/
theorem exists_eq_fromCols_mul_fromBlocks_mul_conjTranspose (A : Matrix m n 𝕜) :
    ∃ (U : Matrix m (Fin (min (Fintype.card m) (Fintype.card n))) 𝕜)
      (U' : Matrix m (Fin (Fintype.card m - min (Fintype.card m) (Fintype.card n))) 𝕜)
      (V : Matrix n (Fin (min (Fintype.card m) (Fintype.card n))) 𝕜)
      (V' : Matrix n (Fin (Fintype.card n - min (Fintype.card m) (Fintype.card n))) 𝕜),
      HasOrthonormalCols (Matrix.fromCols U U') ∧ HasOrthonormalCols (Matrix.fromCols V V') ∧
      A = Matrix.fromCols U U' *
          Matrix.fromBlocks (Matrix.diagonal fun i : Fin (min (Fintype.card m) (Fintype.card n)) =>
            ((singularValues A i : ℝ) : 𝕜)) 0 0 0 *
        (Matrix.fromCols V V')ᴴ := by
  obtain ⟨U', V', hU, hV, hA⟩ :=
    (isSVD_svdU_svdV A).exists_eq_fromCols_mul_fromBlocks_mul_conjTranspose
      (p := Fin (Fintype.card m - min (Fintype.card m) (Fintype.card n)))
      (q := Fin (Fintype.card n - min (Fintype.card m) (Fintype.card n)))
      (by simp only [Fintype.card_fin]; omega) (by simp only [Fintype.card_fin]; omega)
  exact ⟨svdU A, U', svdV A, V', hU, hV, hA⟩

end NLAlib
