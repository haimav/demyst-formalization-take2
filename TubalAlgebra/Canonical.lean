import TubalAlgebra.KMRing

/-!
# Realness and canonical tubal rings (Definition 12, Proposition 13, Section 10.1, Prop. 66)

Given `n` and `m ≤ n` of the same parity, `M_{n,m}` is the block-diagonal matrix with `m`
leading `1`'s followed by `(n - m)/2` blocks `[[1/√2, -i/√2], [1/√2, i/√2]]`, and
`𝕂_{n,m} := 𝕂_{M_{n,m}}` are the canonical tubal rings.
-/

open Matrix Complex

noncomputable section

namespace Tubal

variable {n : ℕ}

/-- The canonical matrix `M_{n,m}` of Section 10.1: `m` leading `1`'s on the diagonal, followed
by the `2 × 2` blocks `[[1/√2, -i/√2], [1/√2, i/√2]]` on the diagonal. -/
def canonicalM (n m : ℕ) : Matrix (Fin n) (Fin n) ℂ := fun i j =>
  if (i : ℕ) < m ∨ (j : ℕ) < m then (if i = j then 1 else 0)
  else if ((i : ℕ) - m) / 2 = ((j : ℕ) - m) / 2 then
    (if ((j : ℕ) - m) % 2 = 0 then ((1 / Real.sqrt 2 : ℝ) : ℂ)
     else if ((i : ℕ) - m) % 2 = 0 then -I / (Real.sqrt 2 : ℂ) else I / (Real.sqrt 2 : ℂ))
  else 0

/-- The inverse of `M_{n,m}` as displayed in the proof of Proposition 66: `m` leading `1`'s
followed by the blocks `[[1/√2, 1/√2], [i/√2, -i/√2]]`. -/
def canonicalMInv (n m : ℕ) : Matrix (Fin n) (Fin n) ℂ := fun i j =>
  if (i : ℕ) < m ∨ (j : ℕ) < m then (if i = j then 1 else 0)
  else if ((i : ℕ) - m) / 2 = ((j : ℕ) - m) / 2 then
    (if ((i : ℕ) - m) % 2 = 0 then ((1 / Real.sqrt 2 : ℝ) : ℂ)
     else if ((j : ℕ) - m) % 2 = 0 then I / (Real.sqrt 2 : ℂ) else -I / (Real.sqrt 2 : ℂ))
  else 0

/-! ### Auxiliary lemmas -/

namespace Canonical

/-! #### Entries of `M_{n,m}` and `M_{n,m}⁻¹` -/


lemma inv_sqrt2_sq : ((Real.sqrt 2 : ℝ) : ℂ)⁻¹ ^ 2 = 1 / 2 := by
  rw [inv_pow, ← Complex.ofReal_pow, Real.sq_sqrt (by norm_num)]
  norm_num

lemma canonicalM_apply (n m : ℕ) (i j : Fin n) : canonicalM n m i j =
    if (i : ℕ) < m ∨ (j : ℕ) < m then (if (i : ℕ) = j then 1 else 0)
    else if ((i : ℕ) - m) / 2 = ((j : ℕ) - m) / 2 then
      (if ((j : ℕ) - m) % 2 = 0 then (((Real.sqrt 2 : ℝ) : ℂ))⁻¹
       else if ((i : ℕ) - m) % 2 = 0 then -I * ((Real.sqrt 2 : ℝ) : ℂ)⁻¹
       else I * ((Real.sqrt 2 : ℝ) : ℂ)⁻¹)
    else 0 := by
  unfold canonicalM
  simp only [Fin.ext_iff, div_eq_mul_inv, one_mul, Complex.ofReal_inv]

lemma canonicalMInv_apply (n m : ℕ) (i j : Fin n) : canonicalMInv n m i j =
    if (i : ℕ) < m ∨ (j : ℕ) < m then (if (i : ℕ) = j then 1 else 0)
    else if ((i : ℕ) - m) / 2 = ((j : ℕ) - m) / 2 then
      (if ((i : ℕ) - m) % 2 = 0 then (((Real.sqrt 2 : ℝ) : ℂ))⁻¹
       else if ((j : ℕ) - m) % 2 = 0 then I * ((Real.sqrt 2 : ℝ) : ℂ)⁻¹
       else -I * ((Real.sqrt 2 : ℝ) : ℂ)⁻¹)
    else 0 := by
  unfold canonicalMInv
  simp only [Fin.ext_iff, div_eq_mul_inv, one_mul, Complex.ofReal_inv]

lemma canonicalMInv_mul (n m : ℕ) (hpar : m % 2 = n % 2) :
    canonicalMInv n m * canonicalM n m = 1 := by
  ext i j
  rw [Matrix.mul_apply, Matrix.one_apply]
  by_cases hi : (i : ℕ) < m
  · have : ∀ k, canonicalMInv n m i k = if i = k then 1 else 0 := by
      intro k; simp [canonicalMInv, hi]
    simp only [this, ite_mul, one_mul, zero_mul, Finset.sum_ite_eq, Finset.mem_univ, ite_true]
    simp [canonicalM, hi]
  by_cases hj : (j : ℕ) < m
  · have : ∀ k, canonicalM n m k j = if k = j then 1 else 0 := by
      intro k; simp [canonicalM, hj]
    simp only [this, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, ite_true]
    simp [canonicalMInv, hj]
  push Not at hi hj
  obtain ⟨t, ht⟩ : ∃ t, t = ((i : ℕ) - m) / 2 := ⟨_, rfl⟩
  obtain ⟨k1, hk1⟩ : ∃ k : Fin n, (k : ℕ) = m + 2 * t := ⟨⟨m + 2 * t, by omega⟩, rfl⟩
  obtain ⟨k2, hk2⟩ : ∃ k : Fin n, (k : ℕ) = m + 2 * t + 1 := ⟨⟨m + 2 * t + 1, by omega⟩, rfl⟩
  rw [Fintype.sum_eq_add k1 k2 (fun h => by rw [h] at hk1; omega) ?_]
  · rw [canonicalMInv_apply, canonicalMInv_apply, canonicalM_apply, canonicalM_apply]
    rw [hk1, hk2, show (if i = j then (1 : ℂ) else 0) = if (i : ℕ) = j then 1 else 0 from by
      simp only [Fin.ext_iff]]
    have e1 : ¬((i : ℕ) < m ∨ m + 2 * t < m) := by omega
    have e2 : ¬(m + 2 * t < m ∨ (j : ℕ) < m) := by omega
    have e3 : ¬((i : ℕ) < m ∨ m + 2 * t + 1 < m) := by omega
    have e4 : ¬(m + 2 * t + 1 < m ∨ (j : ℕ) < m) := by omega
    have e5 : (m + 2 * t - m) / 2 = t := by omega
    have e6 : (m + 2 * t + 1 - m) / 2 = t := by omega
    have e7 : (m + 2 * t - m) % 2 = 0 := by omega
    have e8 : ¬ (m + 2 * t + 1 - m) % 2 = 0 := by omega
    have e9 : ((i : ℕ) - m) / 2 = t := ht.symm
    simp only [e1, e2, e3, e4, e5, e6, e7, e8, e9, ↓reduceIte]
    split_ifs <;> first | omega | (ring_nf; done) |
      (ring_nf; simp only [Complex.I_sq, inv_sqrt2_sq]; norm_num)
  · rintro x ⟨hx1, hx2⟩
    have hx1' : (x : ℕ) ≠ m + 2 * t := fun h => hx1 (Fin.ext (h.trans hk1.symm))
    have hx2' : (x : ℕ) ≠ m + 2 * t + 1 := fun h => hx2 (Fin.ext (h.trans hk2.symm))
    have : canonicalMInv n m i x = 0 := by
      rw [canonicalMInv_apply]
      split_ifs <;> first | rfl | omega
    rw [this, zero_mul]

lemma canonicalM_isUnit (n m : ℕ) (hpar : m % 2 = n % 2) : IsUnit (canonicalM n m) :=
  (Matrix.isUnit_iff_isUnit_det _).mpr
    (Matrix.isUnit_det_of_left_inverse (canonicalMInv_mul n m hpar))

lemma canonicalM_rowReal_of_lt {n m : ℕ} {i : Fin n} (hi : (i : ℕ) < m) :
    RowReal (canonicalM n m) i := by
  intro k
  rw [canonicalM_apply]
  simp only [hi, true_or, ↓reduceIte]
  split_ifs <;> simp

lemma canonicalM_not_rowReal {n m : ℕ} (hpar : m % 2 = n % 2) {i : Fin n} (hi : m ≤ (i : ℕ)) :
    ¬ RowReal (canonicalM n m) i := by
  intro h
  obtain ⟨t, ht⟩ : ∃ t, t = ((i : ℕ) - m) / 2 := ⟨_, rfl⟩
  obtain ⟨k, hk⟩ : ∃ k : Fin n, (k : ℕ) = m + 2 * t + 1 := ⟨⟨m + 2 * t + 1, by omega⟩, rfl⟩
  have := h k
  rw [canonicalM_apply, hk] at this
  have e1 : ¬ ((i : ℕ) < m ∨ m + 2 * t + 1 < m) := by omega
  have e2 : ((i : ℕ) - m) / 2 = (m + 2 * t + 1 - m) / 2 := by omega
  have e3 : ¬ (m + 2 * t + 1 - m) % 2 = 0 := by omega
  simp only [e1, e2, e3, ↓reduceIte] at this
  split_ifs at this
  · have h2 : (2 : ℂ) * (I * ((Real.sqrt 2 : ℝ) : ℂ)⁻¹) = 0 := by
      simp at this; linear_combination this
    simp at h2
  · have h2 : (2 : ℂ) * (I * ((Real.sqrt 2 : ℝ) : ℂ)⁻¹) = 0 := by
      simp at this; linear_combination -this
    simp at h2

lemma canonicalM_rowConjOf {n m : ℕ} (hpar : m % 2 = n % 2) {i : Fin n} (hi : m ≤ (i : ℕ)) :
    ∃ j : Fin n, j ≠ i ∧ RowConjOf (canonicalM n m) i j := by
  obtain ⟨t, ht⟩ : ∃ t, t = ((i : ℕ) - m) / 2 := ⟨_, rfl⟩
  have e0 : ¬ (i : ℕ) < m := by omega
  rcases Nat.mod_two_eq_zero_or_one ((i : ℕ) - m) with h | h
  · obtain ⟨p, hp⟩ : ∃ p : Fin n, (p : ℕ) = i + 1 := ⟨⟨(i : ℕ) + 1, by omega⟩, rfl⟩
    refine ⟨p, fun h' => by rw [h'] at hp; omega, fun k => ?_⟩
    rw [canonicalM_apply, canonicalM_apply, hp]
    have e1 : ¬ ((i : ℕ) + 1 < m) := by omega
    have e2 : ((i : ℕ) + 1 - m) / 2 = t := by omega
    have e3 : ((i : ℕ) - m) / 2 = t := ht.symm
    have e4 : ¬ ((i : ℕ) + 1 - m) % 2 = 0 := by omega
    simp only [e0, e1, e2, e3, e4, h, false_or, ↓reduceIte]
    split_ifs <;> first | omega | simp
  · obtain ⟨p, hp⟩ : ∃ p : Fin n, (p : ℕ) = i - 1 := ⟨⟨(i : ℕ) - 1, by omega⟩, rfl⟩
    refine ⟨p, fun h' => by rw [h'] at hp; omega, fun k => ?_⟩
    rw [canonicalM_apply, canonicalM_apply, hp]
    have e1 : ¬ ((i : ℕ) - 1 < m) := by omega
    have e2 : ((i : ℕ) - 1 - m) / 2 = t := by omega
    have e3 : ((i : ℕ) - m) / 2 = t := ht.symm
    have e4 : ((i : ℕ) - 1 - m) % 2 = 0 := by omega
    have e5 : ¬ ((i : ℕ) - m) % 2 = 0 := by omega
    simp only [e0, e1, e2, e3, e4, e5, false_or, ↓reduceIte]
    split_ifs <;> first | omega | simp

/-! #### The conjugation involution and the isomorphism criterion -/


open Classical in
/-- The conjugation partner of row `i`. -/
def partner (M : Matrix (Fin n) (Fin n) ℂ) (i : Fin n) : Fin n :=
  if h : ∃ j, RowConjOf M i j then h.choose else i

lemma exists_rowConjOf {M : Matrix (Fin n) (Fin n) ℂ} (hM : Admissible M) (i : Fin n) :
    ∃ j, RowConjOf M i j := by
  rcases hM.2 i with hi | ⟨j, ⟨_, hj⟩, _⟩
  · exact ⟨i, fun k => (hi k).symm⟩
  · exact ⟨j, hj⟩

lemma partner_spec {M : Matrix (Fin n) (Fin n) ℂ} (hM : Admissible M) (i : Fin n) :
    RowConjOf M i (partner M i) := by
  unfold partner
  split_ifs with h
  · exact h.choose_spec
  · exact absurd (exists_rowConjOf hM i) h

lemma rowConjOf_iff {M : Matrix (Fin n) (Fin n) ℂ} (hM : Admissible M) (i j : Fin n) :
    RowConjOf M i j ↔ j = partner M i := by
  constructor
  · intro h; exact rowConjOf_unique' hM.1 h (partner_spec hM i)
  · rintro rfl; exact partner_spec hM i

lemma partner_partner {M : Matrix (Fin n) (Fin n) ℂ} (hM : Admissible M) (i : Fin n) :
    partner M (partner M i) = i :=
  ((rowConjOf_iff hM _ _).1 (rowConjOf_symm (partner_spec hM i))).symm

lemma rowReal_iff {M : Matrix (Fin n) (Fin n) ℂ} (hM : Admissible M) (i : Fin n) :
    RowReal M i ↔ partner M i = i := by
  constructor
  · intro h; exact ((rowConjOf_iff hM i i).1 (fun k => (h k).symm)).symm
  · intro h
    have := partner_spec hM i
    rw [h] at this
    exact rowReal_of_rowConjOf_self this

/-- The conjugation involution `τ_M` as a permutation. -/
def partnerPerm {M : Matrix (Fin n) (Fin n) ℂ} (hM : Admissible M) : Equiv.Perm (Fin n) :=
  Function.Involutive.toPerm (partner M) (partner_partner hM)

@[simp] lemma partnerPerm_apply {M : Matrix (Fin n) (Fin n) ℂ} (hM : Admissible M) (i : Fin n) :
    partnerPerm hM i = partner M i := rfl

lemma partnerPerm_sq {M : Matrix (Fin n) (Fin n) ℂ} (hM : Admissible M) :
    partnerPerm hM ^ 2 = 1 := by
  ext i
  simp [pow_two, partner_partner hM]

lemma realness_eq {M : Matrix (Fin n) (Fin n) ℂ} (hM : Admissible M) :
    realness M = (partnerPerm hM).supportᶜ.card := by
  classical
  rw [realness, Nat.card_eq_fintype_card, Fintype.card_subtype]
  congr 1
  ext i
  simp [Equiv.Perm.mem_support, rowReal_iff hM]

/-- Cycle type of an involution. -/
lemma cycleType_of_sq_eq_one {σ : Equiv.Perm (Fin n)} (h : σ ^ 2 = 1) :
    σ.cycleType = Multiset.replicate (σ.support.card / 2) 2 := by
  have hall : ∀ b ∈ σ.cycleType, b = 2 := by
    intro b hb
    have h1 := Equiv.Perm.dvd_of_mem_cycleType hb
    have h2 : orderOf σ ∣ 2 := orderOf_dvd_of_pow_eq_one h
    have h3 := Equiv.Perm.two_le_of_mem_cycleType hb
    have h4 := Nat.le_of_dvd (by norm_num) (h1.trans h2)
    omega
  have hrep := Multiset.eq_replicate_card.mpr hall
  have hsum := Equiv.Perm.sum_cycleType σ
  rw [hrep, Multiset.sum_replicate, smul_eq_mul] at hsum
  rw [hrep]
  congr 1
  omega

lemma exists_conj_partnerPerm {M M' : Matrix (Fin n) (Fin n) ℂ} (hM : Admissible M)
    (hM' : Admissible M') (h : realness M = realness M') :
    ∃ c : Equiv.Perm (Fin n), ∀ i, partner M (c i) = c (partner M' i) := by
  classical
  have hc : IsConj (partnerPerm hM') (partnerPerm hM) := by
    rw [Equiv.Perm.isConj_iff_cycleType_eq, cycleType_of_sq_eq_one (partnerPerm_sq hM),
      cycleType_of_sq_eq_one (partnerPerm_sq hM')]
    rw [realness_eq hM, realness_eq hM', Finset.card_compl, Finset.card_compl] at h
    have h1 := Finset.card_le_univ (partnerPerm hM).support
    have h2 := Finset.card_le_univ (partnerPerm hM').support
    congr 2
    omega
  obtain ⟨c, hc⟩ := isConj_iff.mp hc
  refine ⟨c, fun i => ?_⟩
  rw [← partnerPerm_apply hM, ← partnerPerm_apply hM', ← hc]
  simp

lemma conjPattern_comp {M M' : Matrix (Fin n) (Fin n) ℂ} (σ : Fin n ≃ Fin n)
    (hR : ∀ i, RowReal M' i → RowReal M (σ i))
    (hC : ∀ i j, RowConjOf M' i j → RowConjOf M (σ i) (σ j)) {y : Fin n → ℂ}
    (hy : ConjPattern M y) : ConjPattern M' (y ∘ σ) :=
  ⟨fun j hj => hy.1 _ (hR j hj), fun j k hjk => hy.2 _ _ (hC j k hjk)⟩

/-- Isomorphism criterion. -/
theorem iso_of_perm {M M' : Matrix (Fin n) (Fin n) ℂ} (hM : Admissible M)
    (hM' : Admissible M') (σ : Fin n ≃ Fin n) (hR : ∀ i, RowReal M' i ↔ RowReal M (σ i))
    (hC : ∀ i j, RowConjOf M' i j ↔ RowConjOf M (σ i) (σ j)) :
    ∃ e : KM M ≃+* KM M', ∀ x, e (star x) = star (e x) := by
  have : Fact (Admissible M) := ⟨hM⟩
  have : Fact (Admissible M') := ⟨hM'⟩
  have h1 : ∀ a : KM M, ∃ b : KM M', b.hat = a.hat ∘ σ := fun a =>
    KM.exists_hat_eq (conjPattern_comp σ (fun i => (hR i).1) (fun i j => (hC i j).1)
      a.hat_conjPattern)
  have h2 : ∀ b : KM M', ∃ a : KM M, a.hat = b.hat ∘ σ.symm := fun b =>
    KM.exists_hat_eq (conjPattern_comp σ.symm
      (fun i hi => (hR _).2 (by simpa using hi))
      (fun i j hij => (hC _ _).2 (by simpa using hij)) b.hat_conjPattern)
  choose f hf using h1
  choose g hg using h2
  refine ⟨
    { toFun := f
      invFun := g
      left_inv := ?_
      right_inv := ?_
      map_mul' := ?_
      map_add' := ?_ }, ?_⟩
  · intro a; apply KM.hat_injective; rw [hg, hf]; funext i; simp
  · intro b; apply KM.hat_injective; rw [hf, hg]; funext i; simp
  · intro a b; apply KM.hat_injective; rw [KM.hat_mul, hf, hf, hf, KM.hat_mul]; rfl
  · intro a b; apply KM.hat_injective; rw [KM.hat_add, hf, hf, hf, KM.hat_add]; rfl
  · intro x; apply KM.hat_injective
    change (f (star x)).hat = (star (f x)).hat
    rw [KM.hat_star, hf, hf, KM.hat_star]; rfl

/-- Main iso theorem. -/
theorem iso_of_realness_eq {M M' : Matrix (Fin n) (Fin n) ℂ} (hM : Admissible M)
    (hM' : Admissible M') (h : realness M = realness M') :
    ∃ e : KM M ≃+* KM M', ∀ x, e (star x) = star (e x) := by
  obtain ⟨c, hc⟩ := exists_conj_partnerPerm hM hM' h
  refine iso_of_perm hM hM' c (fun i => ?_) (fun i j => ?_)
  · rw [rowReal_iff hM, rowReal_iff hM', hc, c.injective.eq_iff]
  · rw [rowConjOf_iff hM, rowConjOf_iff hM', hc, c.injective.eq_iff]

end Canonical

/-- `M_{n,m}⁻¹` is the displayed matrix (for `m ≤ n` of the same parity as `n`). -/
theorem canonicalM_inv (n m : ℕ) (hmn : m ≤ n) (hpar : m % 2 = n % 2) :
    (canonicalM n m)⁻¹ = canonicalMInv n m := by
  have _ := hmn
  exact Matrix.inv_eq_left_inv (Canonical.canonicalMInv_mul n m hpar)

/-- For `m ≤ n` of the same parity, `M_{n,m}` is admissible, so `𝕂_{n,m}` is a tubal ring. -/
theorem canonicalM_admissible (n m : ℕ) (hmn : m ≤ n) (hpar : m % 2 = n % 2) :
    Admissible (canonicalM n m) := by
  have _ := hmn
  refine ⟨Canonical.canonicalM_isUnit n m hpar, fun i => ?_⟩
  by_cases hi : (i : ℕ) < m
  · exact Or.inl (Canonical.canonicalM_rowReal_of_lt hi)
  · right
    obtain ⟨j, hji, hj⟩ := Canonical.canonicalM_rowConjOf hpar (not_lt.mp hi)
    exact ⟨j, ⟨hji, hj⟩, fun j' hj' =>
      rowConjOf_unique' (Canonical.canonicalM_isUnit n m hpar) hj'.2 hj⟩

/-- The realness of `M_{n,m}` is `m`. -/
theorem realness_canonicalM (n m : ℕ) (hmn : m ≤ n) (hpar : m % 2 = n % 2) :
    realness (canonicalM n m) = m := by
  have hiff : ∀ i : Fin n, RowReal (canonicalM n m) i ↔ (i : ℕ) < m := fun i =>
    ⟨fun h => by
      by_contra h'
      exact Canonical.canonicalM_not_rowReal hpar (not_lt.mp h') h,
     Canonical.canonicalM_rowReal_of_lt⟩
  classical
  rw [realness, Nat.card_congr (Equiv.subtypeEquivRight hiff), Nat.card_eq_fintype_card,
    Fintype.card_subtype, Fin.card_filter_val_lt]
  omega

/-- The realness `r` of an admissible `M` satisfies `r ≤ n` and `r ≡ n (mod 2)`. -/
theorem realness_le_and_parity (M : Matrix (Fin n) (Fin n) ℂ) (hM : Admissible M) :
    realness M ≤ n ∧ realness M % 2 = n % 2 := by
  classical
  rw [Canonical.realness_eq hM]
  refine ⟨?_, ?_⟩
  · simpa using Finset.card_le_univ (Canonical.partnerPerm hM).supportᶜ
  · have := Equiv.Perm.card_compl_support_modEq (p := 2) (n := 1)
      (σ := Canonical.partnerPerm hM) (by simpa using Canonical.partnerPerm_sq hM)
    simpa [Nat.ModEq] using this

/-- **Proposition 66.** Consider the tubal ring defined by `M ∈ ℂ^{n×n}`. Let `m` be the
realness of `M`. Then `𝕂_M` is isomorphic as a ring to `𝕂_{n,m}`. -/
theorem prop66 (M : Matrix (Fin n) (Fin n) ℂ) (hM : Admissible M) :
    Nonempty (KM M ≃+* KM (canonicalM n (realness M))) := by
  have h := realness_le_and_parity M hM
  obtain ⟨e, -⟩ := Canonical.iso_of_realness_eq hM (canonicalM_admissible n _ h.1 h.2)
    (realness_canonicalM n _ h.1 h.2).symm
  exact ⟨e⟩

/-- The isomorphism of Proposition 66 also respects the `⋆_M`-conjugation (as shown in its
proof). -/
theorem prop66_star (M : Matrix (Fin n) (Fin n) ℂ) (hM : Admissible M) :
    ∃ e : KM M ≃+* KM (canonicalM n (realness M)), ∀ x, e (star x) = star (e x) := by
  have h := realness_le_and_parity M hM
  exact Canonical.iso_of_realness_eq hM (canonicalM_admissible n _ h.1 h.2)
    (realness_canonicalM n _ h.1 h.2).symm

/-- **Proposition 13.** Let `M` and `M'` be of equal size. The rings `𝕂_M` and `𝕂_{M'}` are
isomorphic as rings if their realness is the same. -/
theorem prop13 (M M' : Matrix (Fin n) (Fin n) ℂ) (hM : Admissible M) (hM' : Admissible M')
    (h : realness M = realness M') : Nonempty (KM M ≃+* KM M') := by
  obtain ⟨e, -⟩ := Canonical.iso_of_realness_eq hM hM' h
  exact ⟨e⟩

/-- "For real-like tubal rings we have `a* = a` for all `a`." -/
theorem star_eq_self_of_realLike (M : Matrix (Fin n) (Fin n) ℂ) [Fact (Admissible M)]
    (h : IsRealLike M) (a : KM M) : star a = a := by
  have hall : ∀ i, RowReal M i := by
    classical
    intro i
    by_contra hi
    have := Finite.card_subtype_lt (p := fun i => RowReal M i) hi
    rw [Nat.card_eq_fintype_card (α := Fin n), Fintype.card_fin] at this
    exact absurd h (ne_of_lt this)
  apply KM.hat_injective
  rw [KM.hat_star]
  funext i
  exact Complex.conj_eq_iff_im.mpr (a.hat_conjPattern.1 i (hall i))

end Tubal
