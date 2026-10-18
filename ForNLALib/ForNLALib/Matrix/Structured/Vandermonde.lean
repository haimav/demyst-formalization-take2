/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import Mathlib.Algebra.Polynomial.FieldDivision
public import Mathlib.Algebra.Polynomial.OfFn
public import Mathlib.LinearAlgebra.Vandermonde
public import Mathlib.RingTheory.Coprime.Lemmas

/-!
# Vandermonde matrices and multiplication modulo a polynomial

Proposed new file for NLAlib, `NLAlib.Matrix.Structured.Vandermonde`, next to
`NLAlib.Matrix.Structured.Circulant` and `NLAlib.Matrix.Structured.Cauchy`. The Vandermonde
matrix $\mathbf{V}$ of nodes $r_0, \dots, r_{n-1}$ maps the coefficient vector $\mathbf{v}$ of a
polynomial $p_{\mathbf{v}}$ of degree less than $n$ to its values $p_{\mathbf{v}}(r_i)$ at the
nodes. When the nodes are the $n$ distinct roots of a polynomial $Q$ of degree $n$, this turns
multiplication modulo $Q$ into an entrywise product: the structured-matrix fact behind fast
polynomial multiplication. The case $Q = X^n - 1$, whose roots $e^{-2 \pi \mathrm{i} j / n}$ have
Vandermonde matrix $\sqrt{n}\,\mathbf{F}^{\mathsf{H}}$, gives the convolution theorem for
circulant matrices.

## Main results

* `NLAlib.vandermonde_mulVec_apply`: $(\mathbf{V}\mathbf{v})_i = p_{\mathbf{v}}(r_i)$.
* `NLAlib.dvd_sub_mul_iff_vandermonde_mulVec_eq_mul`: $Q$ divides
  $p_{\mathbf{c}} - p_{\mathbf{a}} p_{\mathbf{b}}$ if and only if
  $\mathbf{V}\mathbf{c} = (\mathbf{V}\mathbf{a}) \odot (\mathbf{V}\mathbf{b})$.
-/

@[expose] public section

open Polynomial
open scoped Matrix

namespace NLAlib

/-- The Vandermonde matrix evaluates the coefficient polynomial at the nodes: for nodes
$r_0, \dots, r_{n-1}$ and a vector $\mathbf{v}$, with
$p_{\mathbf{v}} = \sum_{j < n} \mathbf{v}_j X^j$ the polynomial `Polynomial.ofFn n v`,
$$(\mathbf{V}\mathbf{v})_i = \sum_{j < n} r_i^j \, \mathbf{v}_j = p_{\mathbf{v}}(r_i) \,,$$
where $\mathbf{V}_{i,j} = r_i^j$ is the Vandermonde matrix `Matrix.vandermonde r`.
Port of a step of `Tubal.example17` (haimav/demyst-formalization-take2, commit `7d69f60`), there
over $\mathbb{C}$ with a hand-rolled coefficient polynomial in place of `Polynomial.ofFn`. -/
theorem vandermonde_mulVec_apply {R : Type*} [CommRing R] [DecidableEq R] {n : ℕ}
    (r v : Fin n → R) (i : Fin n) :
    (Matrix.vandermonde r *ᵥ v) i = (Polynomial.ofFn n v).eval (r i) := by
  rw [ofFn_eq_sum_monomial, eval_finsetSum]
  simp only [Matrix.mulVec, dotProduct, Matrix.vandermonde_apply, eval_monomial]
  exact Finset.sum_congr rfl fun j _ => mul_comm _ _

variable {K L : Type*} [Field K] [Field L] [Algebra K L] [DecidableEq K] {n : ℕ}

/-- The Vandermonde matrix over an extension field $L$, applied to a vector with entries in $K$,
evaluates the coefficient polynomial over $K$ at the nodes. A bridge for
`dvd_sub_mul_iff_vandermonde_mulVec_eq_mul`. -/
private theorem vandermonde_mulVec_algebraMap_comp_apply (r : Fin n → L) (v : Fin n → K)
    (i : Fin n) :
    (Matrix.vandermonde r *ᵥ (algebraMap K L ∘ v)) i = aeval (r i) (Polynomial.ofFn n v) := by
  rw [ofFn_eq_sum_monomial, map_sum]
  simp only [Matrix.mulVec, dotProduct, Matrix.vandermonde_apply, aeval_monomial,
    Function.comp_apply]
  exact Finset.sum_congr rfl fun j _ => mul_comm _ _

omit [DecidableEq K] in
/-- A nonzero polynomial over $K$ of degree $n$ with $n$ distinct roots $r_i$ in $L$ divides a
polynomial $F$ over $K$ if and only if every $r_i$ is a root of $F$. Over $L$ the polynomial is a
nonzero multiple of $\prod_i (X - r_i)$. -/
private theorem dvd_iff_forall_aeval_eq_zero {Q : K[X]} (hQ : Q.natDegree = n) (hQ0 : Q ≠ 0)
    {r : Fin n → L} (hr : Function.Injective r) (hroot : ∀ i, aeval (r i) Q = 0) (F : K[X]) :
    Q ∣ F ↔ ∀ i, aeval (r i) F = 0 := by
  have hdvd : ∀ G : L[X], (∀ i, G.IsRoot (r i)) → (∏ i, (X - C (r i))) ∣ G := fun G hG =>
    Fintype.prod_dvd_of_coprime (pairwise_coprime_X_sub_C hr) fun i => dvd_iff_isRoot.mpr (hG i)
  have hroot' : ∀ i, (Q.map (algebraMap K L)).IsRoot (r i) := fun i => by
    rw [IsRoot.def, eval_map, ← aeval_def]
    exact hroot i
  have hQL : Q.map (algebraMap K L) =
      C (Q.map (algebraMap K L)).leadingCoeff * ∏ i, (X - C (r i)) := by
    refine eq_leadingCoeff_mul_of_monic_of_dvd_of_natDegree_le
      (monic_prod_X_sub_C r Finset.univ) (hdvd _ hroot') ?_
    rw [natDegree_map, natDegree_finsetProd_X_sub_C_eq_card, Finset.card_univ, Fintype.card_fin,
      hQ]
  have hlc : (Q.map (algebraMap K L)).leadingCoeff ≠ 0 :=
    leadingCoeff_ne_zero.mpr ((Polynomial.map_ne_zero_iff (algebraMap K L).injective).mpr hQ0)
  constructor
  · rintro ⟨g, rfl⟩ i
    rw [map_mul, hroot i, zero_mul]
  · intro hF
    rw [← map_dvd_map' (algebraMap K L), hQL, C_mul_dvd hlc]
    refine hdvd _ fun i => ?_
    rw [IsRoot.def, eval_map, ← aeval_def]
    exact hF i

/-- Multiplication modulo $Q$ is the entrywise product at the roots of $Q$. Let $Q$ be a
polynomial of degree $n$ over a field $K$ with $n$ distinct roots $r_0, \dots, r_{n-1}$ in an
extension field $L$, and let $\mathbf{V}_{i,j} = r_i^j$ be their Vandermonde matrix. For
$\mathbf{a}, \mathbf{b}, \mathbf{c} \in K^n$ with coefficient polynomials
$p_{\mathbf{v}} = \sum_{j < n} \mathbf{v}_j X^j$,
$$Q \mid p_{\mathbf{c}} - p_{\mathbf{a}} p_{\mathbf{b}} \iff
  \mathbf{V}\mathbf{c} = (\mathbf{V}\mathbf{a}) \odot (\mathbf{V}\mathbf{b}) \,,$$
where $\odot$ is the entrywise product, so $p_{\mathbf{c}} \equiv p_{\mathbf{a}} p_{\mathbf{b}}$
modulo $Q$ exactly when the values at the roots multiply. The case $Q = X^n - 1$ over
$\mathbb{C}$, with nodes $e^{-2 \pi \mathrm{i} j / n}$ and so
$\mathbf{V} = \sqrt{n}\,\mathbf{F}^{\mathsf{H}}$, gives the convolution theorem
`NLAlib.conjTranspose_fourierMatrix_mulVec_circulant_mulVec`, since multiplication modulo
$X^n - 1$ is circular convolution: $p_{\mathbf{C}\mathbf{b}} \equiv p_{\mathbf{a}} p_{\mathbf{b}}$
modulo $X^n - 1$ for $\mathbf{C}$ the circulant matrix of $\mathbf{a}$.
Port of `Tubal.example17` and of its case $Q = X^n - 1$, `Tubal.eq3`
(haimav/demyst-formalization-take2, commit `7d69f60`), there with $K = \mathbb{R}$,
$L = \mathbb{C}$ and a hand-rolled coefficient polynomial in place of `Polynomial.ofFn`. -/
theorem dvd_sub_mul_iff_vandermonde_mulVec_eq_mul {Q : K[X]} (hQ : Q.natDegree = n)
    {r : Fin n → L} (hr : Function.Injective r) (hroot : ∀ i, aeval (r i) Q = 0)
    (a b c : Fin n → K) :
    Q ∣ Polynomial.ofFn n c - Polynomial.ofFn n a * Polynomial.ofFn n b ↔
      Matrix.vandermonde r *ᵥ (algebraMap K L ∘ c) =
        (Matrix.vandermonde r *ᵥ (algebraMap K L ∘ a)) *
          (Matrix.vandermonde r *ᵥ (algebraMap K L ∘ b)) := by
  rcases eq_or_ne n 0 with rfl | hn
  · simp only [ofFn_zero', mul_zero, sub_zero, dvd_zero, true_iff]
    funext i
    exact i.elim0
  have hQ0 : Q ≠ 0 := by
    rintro rfl
    exact hn (hQ.symm.trans natDegree_zero)
  rw [dvd_iff_forall_aeval_eq_zero hQ hQ0 hr hroot, funext_iff]
  simp only [Pi.mul_apply, vandermonde_mulVec_algebraMap_comp_apply, map_sub, map_mul,
    sub_eq_zero]

end NLAlib
