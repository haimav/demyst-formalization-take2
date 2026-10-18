/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import Mathlib.LinearAlgebra.Matrix.Charpoly.Minpoly
public import NLAlib.Matrix.Spectral.Diagonalizable
public import ForNLALib.ForMathlib.LinearAlgebra.Matrix.IsDiag

/-!
# Diagonalisability through the minimal polynomial, and simple spectra

Proposed additions to NLAlib's `NLAlib.Matrix.Spectral.Diagonalizable`. Over an algebraically
closed field a square matrix is diagonalisable exactly when its minimal polynomial is squarefree,
and it suffices that some squarefree polynomial annihilates it. An eigenbasis of a matrix with
simple spectrum diagonalises every matrix that commutes with it.

## Main results

* `NLAlib.IsDiagonalizable.squarefree_minpoly`: the minimal polynomial of a diagonalisable matrix
  is squarefree.
* `NLAlib.isDiagonalizable_of_squarefree_aeval_eq_zero`: a matrix annihilated by a squarefree
  polynomial is diagonalisable.
* `NLAlib.isDiagonalizable_iff_squarefree_minpoly`: the two together, as an `iff`.
* `NLAlib.isDiag_inv_mul_mul_of_commute`: an eigenbasis of a matrix with simple spectrum
  diagonalises everything commuting with it.
-/

@[expose] public section

open scoped Matrix
open Polynomial

namespace NLAlib

variable {K : Type*} [Field K] {n : Type*} [Fintype n] [DecidableEq n]

/-- The **minimal polynomial of a diagonalisable matrix is squarefree**: if $\mathbf{A}$ is
diagonalisable, its minimal polynomial has no repeated factor. -/
theorem IsDiagonalizable.squarefree_minpoly {A : Matrix n n K}
    (hA : IsDiagonalizable A) : Squarefree (minpoly K A) := by
  rw [← Matrix.minpoly_toLin']
  exact hA.isSemisimple.minpoly_squarefree

/-- **A matrix annihilated by a squarefree polynomial is diagonalisable**: over an algebraically
closed field, if $p$ is squarefree and $p(\mathbf{A}) = \mathbf{0}$, then $\mathbf{A}$ is
diagonalisable.
Port of `Tubal.isDiagonalizableMat_of_squarefree` (haimav/demyst-formalization-take2, commit
`7d69f60`), there over $\mathbb{C}$ and `Fin n`. -/
theorem isDiagonalizable_of_squarefree_aeval_eq_zero [IsAlgClosed K] {A : Matrix n n K}
    {p : K[X]} (hp : Squarefree p) (hA : aeval A p = 0) : IsDiagonalizable A := by
  refine isDiagonalizable_of_isSemisimple
    (Module.End.isSemisimple_of_squarefree_aeval_eq_zero hp ?_)
  change aeval (Matrix.toLinAlgEquiv' A) p = 0
  rw [Polynomial.aeval_algHom_apply, hA, map_zero]

/-- Over an algebraically closed field, a matrix $\mathbf{A}$ is diagonalisable **if and only
if** its minimal polynomial is squarefree. -/
theorem isDiagonalizable_iff_squarefree_minpoly [IsAlgClosed K] {A : Matrix n n K} :
    IsDiagonalizable A ↔ Squarefree (minpoly K A) :=
  ⟨IsDiagonalizable.squarefree_minpoly, fun h =>
    isDiagonalizable_of_squarefree_aeval_eq_zero h (minpoly.aeval K A)⟩

/-- **An eigenbasis of a matrix with simple spectrum diagonalises everything commuting with it.**
If $\mathbf{V}$ is invertible, $\mathbf{A}\mathbf{V} = \mathbf{V} \operatorname{diag}(\mathbf{d})$
with the entries of $\mathbf{d}$ pairwise distinct, and $\mathbf{B}$ commutes with $\mathbf{A}$,
then $\mathbf{V}^{-1}\mathbf{B}\mathbf{V}$ is diagonal: it commutes with
$\mathbf{V}^{-1}\mathbf{A}\mathbf{V} = \operatorname{diag}(\mathbf{d})$.
Port of the diagonalisation step of `Tubal.algorithm1_correct`
(haimav/demyst-formalization-take2, commit `7d69f60`), there over $\mathbb{C}$ and `Fin n`. -/
theorem isDiag_inv_mul_mul_of_commute {A B V : Matrix n n K} {d : n → K}
    (hV : IsUnit V.det) (hA : A * V = V * Matrix.diagonal d) (hd : Function.Injective d)
    (h : Commute A B) : (V⁻¹ * B * V).IsDiag := by
  have hd' : V⁻¹ * A * V = Matrix.diagonal d := by
    rw [Matrix.mul_assoc, hA, Matrix.nonsing_inv_mul_cancel_left _ _ hV]
  refine Matrix.isDiag_of_commute_diagonal hd ?_
  rw [← hd']
  change V⁻¹ * B * V * (V⁻¹ * A * V) = V⁻¹ * A * V * (V⁻¹ * B * V)
  simp only [Matrix.mul_assoc, Matrix.mul_nonsing_inv_cancel_left _ _ hV]
  rw [← Matrix.mul_assoc B A V, ← h.eq, Matrix.mul_assoc]

end NLAlib
