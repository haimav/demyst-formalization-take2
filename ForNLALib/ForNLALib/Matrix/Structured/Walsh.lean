/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Matrix.Structured.Walsh

/-!
# Dyadic convolution and the Walsh–Hadamard transform

Proposed addition to NLAlib's `NLAlib.Matrix.Structured.Walsh`. The dyadic (XOR) convolution of
two functions on bit strings, $x \mapsto \sum_y \mathbf{a}_y \mathbf{c}_{x+y}$ with addition in
$(\mathbb{Z}/2\mathbb{Z})^b$, becomes an entrywise product under the Walsh–Hadamard transform,
because the rows of the Walsh–Hadamard matrix are characters of $(\mathbb{Z}/2\mathbb{Z})^b$.

## Main results

* `NLAlib.walshHadamard_mulVec_sum_mul_add`: the Walsh–Hadamard transform of a dyadic convolution
  is the entrywise product of the transforms.
-/

@[expose] public section

open scoped Matrix

namespace NLAlib

variable {R : Type*} [Ring R] {b : ℕ}

/-- The Walsh–Hadamard transform turns dyadic (XOR) convolution into an entrywise product: for
$\mathbf{a}, \mathbf{c}$ with entries in any ring, indexed by bit strings
$(\mathbb{Z}/2\mathbb{Z})^b$, with $\mathbf{H}$ the Walsh–Hadamard matrix and $\odot$ the
entrywise product,
$$\mathbf{H}\Bigl(x \mapsto \sum_y \mathbf{a}_y \mathbf{c}_{x+y}\Bigr)
  = (\mathbf{H}\mathbf{a}) \odot (\mathbf{H}\mathbf{c}) \,,$$
the sum $x + y$ taken in $(\mathbb{Z}/2\mathbb{Z})^b$, that is, bitwise exclusive or.
Port of `Tubal.example18_xor` (haimav/demyst-formalization-take2, commit `7d69f60`), there for
real vectors on `Fin (2 ^ k)` with bitwise xor, transformed over $\mathbb{C}$. -/
theorem walshHadamard_mulVec_sum_mul_add (a c : (Fin b → ZMod 2) → R) :
    walshHadamard R b *ᵥ (fun x => ∑ y, a y * c (x + y)) =
      (walshHadamard R b *ᵥ a) * (walshHadamard R b *ᵥ c) := by
  have hcomm : ∀ x y : Fin b → ZMod 2, walshHadamard R b x y = walshHadamard R b y x :=
    fun x y => congrFun (congrFun (transpose_walshHadamard (R := R) b) y) x
  -- the entries are `±1`, hence central: no commutativity of `R` is needed
  have hcen : ∀ (x y : Fin b → ZMod 2) (r : R), Commute (walshHadamard R b x y) r := by
    intro x y r
    rw [walshHadamard_apply]
    split_ifs
    · exact Commute.one_left r
    · exact (Commute.one_left r).neg_left
  have hcancel : ∀ x y : Fin b → ZMod 2, x + y + y = x := fun x y => by
    funext i
    simp only [Pi.add_apply, add_assoc, CharTwo.add_self_eq_zero, add_zero]
  funext z
  simp only [Matrix.mulVec, dotProduct, Pi.mul_apply]
  rw [Finset.sum_mul_sum]
  simp only [Finset.mul_sum]
  refine Finset.sum_comm.trans (Finset.sum_congr rfl fun y _ => ?_)
  rw [← Equiv.sum_comp (Equiv.addRight y)]
  refine Finset.sum_congr rfl fun w _ => ?_
  rw [Equiv.coe_addRight, hcancel, hcomm z (w + y), walshHadamard_add_apply, hcomm w z,
    hcomm y z, ← mul_assoc, ← mul_assoc, (hcen z y _).eq, mul_assoc (a y), (hcen z w _).eq,
    mul_assoc, mul_assoc, mul_assoc]
  rw [← mul_assoc (walshHadamard R b z y), ← mul_assoc,
    ((hcen z y (a y)).mul_left (hcen z w (a y))).eq, mul_assoc]

end NLAlib
