import TubalAlgebra.KMRing

/-!
# Module of oriented matrices (Section 4: Theorem 19, Eq. (8), Theorem 20)

`𝕂_M^m := 𝕂_M ⊕ ⋯ ⊕ 𝕂_M` (`m` copies) is modelled by `Fin m → KM M`: addition is element
addition and multiplication by a tube is element-wise multiplication. It is isomorphic to
`ℝ^{m×n}` via "squeeze"/"twist".
-/

open Matrix Complex

noncomputable section

namespace Tubal

variable {n : ℕ} {M : Matrix (Fin n) (Fin n) ℂ}

/-- "squeeze": `𝕂_M^m → ℝ^{m×n}`, the tube entries are laid flat back into matrix rows. -/
def squeeze {m : ℕ} (U : Fin m → KM M) : Matrix (Fin m) (Fin n) ℝ := fun i j => (U i).vec j

/-- "twist": `ℝ^{m×n} → 𝕂_M^m`, each row is lifted into the third dimension to become a tube. -/
def twist {m : ℕ} (X : Matrix (Fin m) (Fin n) ℝ) : Fin m → KM M := fun i => ⟨X i⟩

theorem twist_squeeze {m : ℕ} (U : Fin m → KM M) : twist (squeeze U) = U := rfl

theorem squeeze_twist {m : ℕ} (X : Matrix (Fin m) (Fin n) ℝ) :
    squeeze (twist X : Fin m → KM M) = X := rfl

/-- `𝕂_M^m ≅ ℝ^{m×n}` (as real vector spaces). -/
def orientedEquiv (m : ℕ) : (Fin m → KM M) ≃ₗ[ℝ] Matrix (Fin m) (Fin n) ℝ where
  toFun := squeeze
  invFun := twist
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  left_inv _ := rfl
  right_inv _ := rfl

/-- The natural basis `E_1, …, E_m` of `𝕂_M^m`: `E_i` is all zeros except for the `i`-th tube,
which is the unit element of `𝕂_M`. -/
def stdOriented [Fact (Admissible M)] (m : ℕ) (i : Fin m) : Fin m → KM M := Pi.single i 1

/-- **Theorem 19** (Theorem 4.1 in [14]). `𝕂_M^m` is a free module over `𝕂_M` of rank `m`:
it has the basis `E_1, …, E_m`, and (since `𝕂_M` has invariant basis number, which needs
`𝕂_M ≠ 0`, i.e. `n ≠ 0`) every basis has `m` elements. -/
theorem theorem19 (M : Matrix (Fin n) (Fin n) ℂ) [Fact (Admissible M)] (m : ℕ) :
    Module.Free (KM M) (Fin m → KM M) ∧
    (∃ b : Module.Basis (Fin m) (KM M) (Fin m → KM M), ∀ i, b i = stdOriented m i) ∧
    (n ≠ 0 → ∀ (ι : Type) (b : Module.Basis ι (KM M) (Fin m → KM M)), Cardinal.mk ι = m) ∧
    (n ≠ 0 → Module.finrank (KM M) (Fin m → KM M) = m) := by
  have hfree : Module.Free (KM M) (Fin m → KM M) := inferInstance
  refine ⟨hfree, ⟨Pi.basisFun (KM M) (Fin m), fun i => Pi.basisFun_apply _ _ i⟩, ?_, ?_⟩
  · intro hn ι b
    have : Nontrivial (KM M) := by
      refine ⟨⟨1, 0, fun h => ?_⟩⟩
      have := congrFun (congrArg KM.hat h) ⟨0, Nat.pos_of_ne_zero hn⟩
      simp at this
    rw [b.mk_eq_rank'', rank_fin_fun]
  · intro hn
    have : Nontrivial (KM M) := by
      refine ⟨⟨1, 0, fun h => ?_⟩⟩
      have := congrFun (congrArg KM.hat h) ⟨0, Nat.pos_of_ne_zero hn⟩
      simp at this
    exact Module.finrank_fin_fun (KM M)

/-- **Eq. (8)**: the `⋆_M`-dot product `U ·_M V := ∑ᵢ uᵢ* ⋆_M vᵢ ∈ 𝕂_M`. -/
def dotM {m : ℕ} (U V : Fin m → KM M) : KM M := ∑ i, star (U i) * V i

/-- The key step in the proof of Theorem 20: for all `u ∈ 𝕂_M`, `u* ⋆_M u ≥_M 0`, and
`u* ⋆_M u = 0` iff `u = 0`. -/
theorem star_mul_self_nonneg (M : Matrix (Fin n) (Fin n) ℂ) [Fact (Admissible M)]
    (u : KM M) : 0 ≤ star u * u ∧ (star u * u = 0 ↔ u = 0) := by
  have hz : ∀ j, (star u * u).hat j = ((Complex.normSq (u.hat j) : ℝ) : ℂ) := by
    intro j
    rw [KM.hat_mul, KM.hat_star, Pi.mul_apply, Pi.star_apply, mul_comm]
    exact Complex.mul_conj _
  refine ⟨fun j => ?_, ⟨fun h => ?_, fun h => by rw [h, star_zero, zero_mul]⟩⟩
  · rw [sub_zero, hz j]
    exact ⟨Complex.ofReal_im _, by simpa using Complex.normSq_nonneg _⟩
  · apply KM.hat_injective
    funext j
    have := congrFun (congrArg KM.hat h) j
    rw [hz j, KM.hat_zero, Pi.zero_apply, Complex.ofReal_eq_zero, Complex.normSq_eq_zero] at this
    rw [this, KM.hat_zero, Pi.zero_apply]

/-- **Theorem 20.** For all `U, V, W ∈ 𝕂_M^m` and `r, s ∈ 𝕂_M`, the `·_M` product satisfies:
* `⋆_M`-conjugate symmetry: `U ·_M V = (V ·_M U)*`;
* `⋆_M`-linearity in the second argument:
  `U ·_M (r ⋆_M V + s ⋆_M W) = r ⋆_M (U ·_M V) + s ⋆_M (U ·_M W)`;
* `⋆_M`-positive definiteness: `U ·_M U ≥_M 0` and `U ·_M U = 0` if and only if `U = 0`. -/
theorem theorem20 (M : Matrix (Fin n) (Fin n) ℂ) [Fact (Admissible M)] {m : ℕ}
    (U V W : Fin m → KM M) (r s : KM M) :
    dotM U V = star (dotM V U) ∧
    dotM U (r • V + s • W) = r * dotM U V + s * dotM U W ∧
    (0 ≤ dotM U U ∧ (dotM U U = 0 ↔ U = 0)) := by
  refine ⟨?_, ?_, ?_⟩
  · simp only [dotM, star_sum, star_mul, star_star]
  · simp only [dotM, Pi.add_apply, Pi.smul_apply, smul_eq_mul, mul_add, Finset.mul_sum,
      Finset.sum_add_distrib]
    congr 1 <;> exact Finset.sum_congr rfl fun i _ => by ring
  · have hnn : ∀ i, 0 ≤ star (U i) * U i := fun i => (star_mul_self_nonneg M (U i)).1
    have hsum : ∀ j, (dotM U U).hat j = ∑ i, (star (U i) * U i).hat j := by
      intro j
      simp only [dotM]
      rw [show (∑ i, star (U i) * U i).hat = ∑ i, (star (U i) * U i).hat from
        map_sum (⟨⟨KM.hat, KM.hat_zero⟩, KM.hat_add⟩ : KM M →+ (Fin n → ℂ)) _ _]
      simp
    refine ⟨fun j => ?_, ⟨fun h => ?_, fun h => by simp [dotM, h]⟩⟩
    · rw [sub_zero, hsum j, Complex.im_sum, Complex.re_sum]
      refine ⟨Finset.sum_eq_zero fun i _ => ?_, Finset.sum_nonneg fun i _ => ?_⟩
      · simpa using (hnn i j).1
      · simpa using (hnn i j).2
    · funext i
      apply ((star_mul_self_nonneg M (U i)).2).mp
      apply KM.hat_injective
      funext j
      have h0 := congrFun (congrArg KM.hat h) j
      rw [hsum j, KM.hat_zero, Pi.zero_apply] at h0
      have hre := congrArg Complex.re h0
      rw [Complex.re_sum, Complex.zero_re] at hre
      have hnn' : ∀ k ∈ Finset.univ, 0 ≤ ((star (U k) * U k).hat j).re := fun k _ => by
        simpa using (hnn k j).2
      have hk := (Finset.sum_eq_zero_iff_of_nonneg hnn').mp hre i (Finset.mem_univ _)
      have him : ((star (U i) * U i).hat j).im = 0 := by simpa using (hnn i j).1
      rw [KM.hat_zero, Pi.zero_apply]
      exact Complex.ext hk him

end Tubal
