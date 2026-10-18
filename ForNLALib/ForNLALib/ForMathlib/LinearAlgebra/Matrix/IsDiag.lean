/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import Mathlib.LinearAlgebra.Matrix.IsDiag

/-!
# Matrices commuting with a diagonal matrix with distinct entries

A matrix that commutes with a diagonal matrix $\operatorname{diag}(\mathbf{d})$ whose entries are
pairwise distinct is itself diagonal. This is the step that turns "commutes with a matrix with
simple spectrum" into "is diagonal in its eigenbasis".

Upstream candidate for `Mathlib.LinearAlgebra.Matrix.IsDiag`.

## Main results

* `Matrix.isDiag_of_commute_diagonal`: commuting with $\operatorname{diag}(\mathbf{d})$,
  $\mathbf{d}$ injective, forces diagonality.
* `Matrix.commute_diagonal_iff_isDiag`: the converse, as an `iff`.
-/

@[expose] public section

namespace Matrix

variable {α n : Type*} [Fintype n] [DecidableEq n] [CommRing α] [NoZeroDivisors α]

/-- **A matrix commuting with a diagonal matrix with distinct entries is diagonal.** If
$\mathbf{A} \operatorname{diag}(\mathbf{d}) = \operatorname{diag}(\mathbf{d}) \mathbf{A}$ and the
entries of $\mathbf{d}$ are pairwise distinct, then $\mathbf{A}_{i,j} = 0$ for $i \ne j$: the
$(i,j)$ entry of the commutator is $\mathbf{A}_{i,j}(\mathbf{d}_j - \mathbf{d}_i)$.
Port of `Tubal.AppB.isDiag_of_commute_diagonal` (haimav/demyst-formalization-take2, commit
`7d69f60`), there over $\mathbb{C}$ and `Fin n`. -/
theorem isDiag_of_commute_diagonal {A : Matrix n n α} {d : n → α} (hd : Function.Injective d)
    (h : Commute A (diagonal d)) : A.IsDiag := by
  intro i j hij
  have hij' := congrFun (congrFun h.eq i) j
  rw [mul_diagonal, diagonal_mul] at hij'
  have hne : d j - d i ≠ 0 := sub_ne_zero.mpr fun e => hij (hd e).symm
  have hzero : A i j * (d j - d i) = 0 := by rw [mul_sub, hij', mul_comm]; exact sub_self _
  exact (mul_eq_zero.mp hzero).resolve_right hne

/-- For a diagonal matrix $\operatorname{diag}(\mathbf{d})$ with pairwise distinct entries, a
matrix commutes with it **if and only if** it is diagonal. -/
theorem commute_diagonal_iff_isDiag {A : Matrix n n α} {d : n → α} (hd : Function.Injective d) :
    Commute A (diagonal d) ↔ A.IsDiag := by
  refine ⟨isDiag_of_commute_diagonal hd, fun hA => ?_⟩
  rw [← hA.diagonal_diag]
  exact commute_diagonal _ _

end Matrix
