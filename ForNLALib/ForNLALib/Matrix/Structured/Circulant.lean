/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Matrix.Structured.Circulant

/-!
# The convolution theorem for the discrete Fourier transform

Proposed addition to NLAlib's `NLAlib.Matrix.Structured.Circulant`. Multiplying by the circulant
matrix of $\mathbf{a}$ is circular convolution with $\mathbf{a}$; the Fourier diagonalisation of
circulant matrices turns it into an entrywise product of discrete Fourier transforms.

## Main results

* `NLAlib.conjTranspose_fourierMatrix_mulVec_circulant_mulVec`: the convolution theorem,
  $\mathbf{F}^{\mathsf{H}}(\mathbf{C}\mathbf{b})
  = \sqrt{n}\,(\mathbf{F}^{\mathsf{H}}\mathbf{a}) \odot (\mathbf{F}^{\mathsf{H}}\mathbf{b})$
  for $\mathbf{C}$ the circulant matrix of $\mathbf{a}$ and $\mathbf{F}$ the Fourier matrix.
-/

@[expose] public section

open scoped Matrix

namespace NLAlib

variable {n : ℕ}

/-- **Convolution theorem** for the discrete Fourier transform: circular convolution becomes an
entrywise product in the Fourier basis. For $\mathbf{a}, \mathbf{b} \in \mathbb{C}^n$, with
$\mathbf{C}$ the circulant matrix of $\mathbf{a}$, so that
$(\mathbf{C}\mathbf{b})_i = \sum_j \mathbf{a}_{i-j} \mathbf{b}_j$ with indices modulo $n$, and
$\mathbf{F}$ the Fourier matrix,
$$\mathbf{F}^{\mathsf{H}}(\mathbf{C}\mathbf{b})
  = \sqrt{n}\,(\mathbf{F}^{\mathsf{H}}\mathbf{a}) \odot (\mathbf{F}^{\mathsf{H}}\mathbf{b}) \,,$$
where $\odot$ is the entrywise product. In terms of the discrete Fourier transform
$\hat{\mathbf{v}} = \sqrt{n}\,\mathbf{F}^{\mathsf{H}}\mathbf{v}$, this reads
$\widehat{\mathbf{C}\mathbf{b}} = \hat{\mathbf{a}} \odot \hat{\mathbf{b}}$. It follows from the
Fourier diagonalisation `NLAlib.circulant_eq_fourierMatrix_mul_diagonal_mul_conjTranspose`.
Port of `Tubal.dft_cconv`, used for `Tubal.example16` (haimav/demyst-formalization-take2, commit
`7d69f60`), there for real vectors and the unnormalised DFT matrix
$\sqrt{n}\,\mathbf{F}^{\mathsf{H}}$.
Result: convolution-theorem -/
theorem conjTranspose_fourierMatrix_mulVec_circulant_mulVec (a b : Fin n → ℂ) :
    (fourierMatrix n)ᴴ *ᵥ (Matrix.circulant a *ᵥ b) =
      (√(n : ℝ) : ℂ) • (((fourierMatrix n)ᴴ *ᵥ a) * ((fourierMatrix n)ᴴ *ᵥ b)) := by
  rw [circulant_eq_fourierMatrix_mul_diagonal_mul_conjTranspose, Matrix.mulVec_mulVec,
    ← Matrix.mul_assoc, ← Matrix.mul_assoc,
    (hasOrthonormalCols_fourierMatrix n).conjTranspose_mul_self, Matrix.one_mul,
    ← Matrix.mulVec_mulVec]
  funext k
  simp only [Matrix.mulVec_diagonal, Pi.smul_apply, Pi.mul_apply, smul_eq_mul, mul_assoc]

end NLAlib
