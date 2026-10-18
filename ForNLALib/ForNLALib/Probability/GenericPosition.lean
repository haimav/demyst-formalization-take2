/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
public import NLAlib.Matrix.Spectral.EigenvalueListing
public import ForNLALib.Matrix.Spectral.Diagonalizable

/-!
# Generic position of random real vectors

A new file proposed for NLAlib, `NLAlib.Probability.GenericPosition`. For a matrix
$\mathbf{W}$ with pairwise distinct rows, the vector $\mathbf{W}\mathbf{x}$ has pairwise distinct
entries for almost every real $\mathbf{x}$, for Lebesgue measure and any law absolutely
continuous with respect to it: each coincidence
$(\mathbf{W}\mathbf{x})_i = (\mathbf{W}\mathbf{x})_j$ cuts out a proper subspace. Consequently a
random member $\mathbf{V}\operatorname{diag}(\mathbf{W}\mathbf{x})\mathbf{V}^{-1}$ of the
commutative family diagonalised by $\mathbf{V}$ has simple spectrum, and any eigenbasis of it
diagonalises the whole family.

## Main results

* `NLAlib.ae_injective_mulVec_ofReal_of_absolutelyContinuous`: distinct entries almost surely,
  for any law absolutely continuous with respect to Lebesgue measure.
* `NLAlib.ae_injective_mulVec_ofReal`: the same for Lebesgue measure.
* `NLAlib.ae_injective_of_mul_eq_mul_diagonal`: a random member of the family diagonalised by
  $\mathbf{V}$ has simple spectrum.
* `NLAlib.ae_isDiag_inv_mul_mul_of_mul_eq_mul_diagonal`: randomized simultaneous
  diagonalisation.
-/

@[expose] public section

open scoped Matrix
open MeasureTheory

namespace NLAlib

variable {𝕜 : Type*} [RCLike 𝕜] {n p : Type*} [Fintype p]

/-- If rows $i$ and $j$ of $\mathbf{W}$ differ, the entries $(\mathbf{W}\mathbf{x})_i$ and
$(\mathbf{W}\mathbf{x})_j$ differ for Lebesgue-almost every real $\mathbf{x}$: they agree only on
the kernel of a nonzero real-linear functional, a proper subspace. -/
private theorem ae_mulVec_ofReal_apply_ne {W : Matrix n p 𝕜} {i j : n} (hij : W i ≠ W j) :
    ∀ᵐ x : p → ℝ ∂volume, (W *ᵥ fun k => (x k : 𝕜)) i ≠ (W *ᵥ fun k => (x k : 𝕜)) j := by
  let π : n → (n → 𝕜) →ₗ[ℝ] 𝕜 := fun l => LinearMap.proj (R := ℝ) (φ := fun _ => 𝕜) l
  let L : (p → ℝ) →ₗ[ℝ] 𝕜 := (π i - π j) ∘ₗ
    (W.mulVecLin.restrictScalars ℝ) ∘ₗ LinearMap.compLeft (Algebra.linearMap ℝ 𝕜) p
  have hL : ∀ x : p → ℝ, L x = (W *ᵥ fun k => (x k : 𝕜)) i - (W *ᵥ fun k => (x k : 𝕜)) j :=
    fun _ => rfl
  have hker : LinearMap.ker L ≠ ⊤ := by
    classical
    obtain ⟨k, hk⟩ := Function.ne_iff.mp hij
    intro htop
    have hmem : (Pi.single k 1 : p → ℝ) ∈ LinearMap.ker L := htop ▸ Submodule.mem_top
    rw [LinearMap.mem_ker, hL] at hmem
    have hsingle : (fun l => (((Pi.single k 1 : p → ℝ) l : ℝ) : 𝕜)) = Pi.single k 1 := by
      ext l
      rw [Pi.single_apply, Pi.single_apply]
      split_ifs <;> simp only [RCLike.ofReal_one, RCLike.ofReal_zero]
    rw [hsingle, Matrix.mulVec_single_one, Matrix.col_apply, Matrix.col_apply, sub_eq_zero] at hmem
    exact hk hmem
  have h0 := measure_eq_zero_iff_ae_notMem.mp
    (Measure.addHaar_submodule volume (LinearMap.ker L) hker)
  filter_upwards [h0] with x hx he
  refine hx ?_
  rw [SetLike.mem_coe, LinearMap.mem_ker, hL, he, sub_self]

/-- For a matrix $\mathbf{W}$ with pairwise distinct rows, almost every real vector has an image
with pairwise distinct entries, for any law $\nu$ absolutely continuous with respect to
Lebesgue measure: for $\nu$-almost every $\mathbf{x}$,
$(\mathbf{W}\mathbf{x})_i \ne (\mathbf{W}\mathbf{x})_j$ whenever $i \ne j$.
Port of `Tubal.AppB.ae_injective_mulVec` (haimav/demyst-formalization-take2, commit `7d69f60`),
there for Lebesgue measure and an invertible $\mathbf{W}$ over $\mathbb{C}$ on `Fin n`. -/
theorem ae_injective_mulVec_ofReal_of_absolutelyContinuous [Finite n] {W : Matrix n p 𝕜}
    (hW : Function.Injective W) {ν : Measure (p → ℝ)} (hν : ν ≪ volume) :
    ∀ᵐ x ∂ν, Function.Injective (W *ᵥ fun j => (x j : 𝕜)) := by
  have key : ∀ i j : n, ∀ᵐ x ∂ν,
      (W *ᵥ fun k => (x k : 𝕜)) i = (W *ᵥ fun k => (x k : 𝕜)) j → i = j := by
    intro i j
    by_cases hij : i = j
    · exact Filter.Eventually.of_forall fun _ _ => hij
    · filter_upwards [hν.ae_le (ae_mulVec_ofReal_apply_ne (hW.ne hij))] with x hx he
      exact absurd he hx
  filter_upwards [ae_all_iff.mpr fun i => ae_all_iff.mpr (key i)] with x hx i j hxij
  exact hx i j hxij

/-- For a matrix $\mathbf{W}$ with pairwise distinct rows, $\mathbf{W}\mathbf{x}$ has pairwise
distinct entries for Lebesgue-almost every real vector $\mathbf{x}$.
Port of `Tubal.AppB.ae_injective_mulVec` (haimav/demyst-formalization-take2, commit `7d69f60`),
there for an invertible $\mathbf{W}$ over $\mathbb{C}$ on `Fin n`. -/
theorem ae_injective_mulVec_ofReal [Finite n] {W : Matrix n p 𝕜}
    (hW : Function.Injective W) :
    ∀ᵐ x : p → ℝ ∂volume, Function.Injective (W *ᵥ fun j => (x j : 𝕜)) :=
  ae_injective_mulVec_ofReal_of_absolutelyContinuous hW Measure.AbsolutelyContinuous.rfl

variable [Fintype n] [DecidableEq n]

/-- A random member of the family diagonalised by $\mathbf{V}$ has simple spectrum. For
$\mathbf{V}$ invertible and $\mathbf{W}$ with pairwise distinct rows, for Lebesgue-almost every
real $\mathbf{x}$: whenever $\mathbf{S}$ is invertible and
$\mathbf{V}\operatorname{diag}(\mathbf{W}\mathbf{x})\mathbf{V}^{-1}\mathbf{S} =
\mathbf{S}\operatorname{diag}(\mathbf{\Lambda})$, the entries of $\mathbf{\Lambda}$ are pairwise
distinct, since $\mathbf{\Lambda}$ and $\mathbf{W}\mathbf{x}$ list the same eigenvalues.
Port of `Tubal.AppB.injective_of_similar_diagonal` and the simple-spectrum step of
`Tubal.algorithm1_ae` (haimav/demyst-formalization-take2, commit `7d69f60`), there for the
representation matrices of a tubal ring, with $\mathbf{W} = \mathbf{V}^{-1}$, over $\mathbb{C}$
on `Fin n`. -/
theorem ae_injective_of_mul_eq_mul_diagonal {V : Matrix n n 𝕜} (hV : IsUnit V.det)
    {W : Matrix n p 𝕜} (hW : Function.Injective W) :
    ∀ᵐ x : p → ℝ ∂volume, ∀ (S : Matrix n n 𝕜) (Λ : n → 𝕜), IsUnit S.det →
      V * Matrix.diagonal (W *ᵥ fun j => (x j : 𝕜)) * V⁻¹ * S = S * Matrix.diagonal Λ →
      Function.Injective Λ := by
  filter_upwards [ae_injective_mulVec_ofReal hW] with x hx S Λ hS h
  have hd : IsEigenvalueListing (V * Matrix.diagonal (W *ᵥ fun j => (x j : 𝕜)) * V⁻¹)
      (W *ᵥ fun j => (x j : 𝕜)) :=
    isEigenvalueListing_of_mul_eq_mul_diagonal hV (Matrix.nonsing_inv_mul_cancel_right _ _ hV)
  obtain ⟨e, he⟩ := (isEigenvalueListing_of_mul_eq_mul_diagonal hS h).exists_equiv_eq hd
  rw [he]
  exact hx.comp e.injective

/-- **Randomized simultaneous diagonalisation.** For $\mathbf{V}$ invertible and $\mathbf{W}$
with pairwise distinct rows, for Lebesgue-almost every real $\mathbf{x}$, any eigenbasis of the
random member $\mathbf{V}\operatorname{diag}(\mathbf{W}\mathbf{x})\mathbf{V}^{-1}$ diagonalises
the whole family: if $\mathbf{S}$ is invertible and
$\mathbf{V}\operatorname{diag}(\mathbf{W}\mathbf{x})\mathbf{V}^{-1}\mathbf{S} =
\mathbf{S}\operatorname{diag}(\mathbf{\Lambda})$, then
$\mathbf{S}^{-1}\mathbf{V}\operatorname{diag}(\mathbf{d})\mathbf{V}^{-1}\mathbf{S}$ is diagonal
for every $\mathbf{d}$.
Port of `Tubal.algorithm1_ae` and the diagonalisation step of `Tubal.algorithm1_correct`
(haimav/demyst-formalization-take2, commit `7d69f60`), there for the representation matrices of a
tubal ring, with $\mathbf{W} = \mathbf{V}^{-1}$, over $\mathbb{C}$ on `Fin n`.
Result: randomized-simultaneous-diagonalization -/
theorem ae_isDiag_inv_mul_mul_of_mul_eq_mul_diagonal {V : Matrix n n 𝕜}
    (hV : IsUnit V.det) {W : Matrix n p 𝕜} (hW : Function.Injective W) :
    ∀ᵐ x : p → ℝ ∂volume, ∀ (S : Matrix n n 𝕜) (Λ : n → 𝕜), IsUnit S.det →
      V * Matrix.diagonal (W *ᵥ fun j => (x j : 𝕜)) * V⁻¹ * S = S * Matrix.diagonal Λ →
      ∀ d : n → 𝕜, (S⁻¹ * (V * Matrix.diagonal d * V⁻¹) * S).IsDiag := by
  filter_upwards [ae_injective_of_mul_eq_mul_diagonal hV hW] with x hx S Λ hS h d
  exact isDiag_inv_mul_mul_of_commute hS h (hx S Λ hS h)
    (commute_of_mul_eq_mul_diagonal hV (Matrix.nonsing_inv_mul_cancel_right _ _ hV)
      (Matrix.nonsing_inv_mul_cancel_right _ _ hV))

end NLAlib
