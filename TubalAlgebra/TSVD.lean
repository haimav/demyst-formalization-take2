import TubalAlgebra.Transform
import TubalAlgebra.MatrixSVD

/-!
# Tubal SVD (Section 7: Definitions 28, 29, Theorem 30, Definition 31, Lemma 32)
-/

open Matrix Complex

noncomputable section

namespace Tubal

variable {n : ℕ} {M : Matrix (Fin n) (Fin n) ℂ}

/-- **Definition 28.** A tensor `𝒰 ∈ 𝕂_M^{m×m}` is `⋆_M`-unitary if
`𝒰ᴴ ⋆_M 𝒰 = 𝒰 ⋆_M 𝒰ᴴ = ℐ_m`. -/
def IsStarMUnitary [Fact (Admissible M)] {m : ℕ} (U : Matrix (Fin m) (Fin m) (KM M)) : Prop :=
  Uᴴ * U = identityTensor m ∧ U * Uᴴ = identityTensor m

/-! ### Auxiliary lemmas -/

private lemma tsvd_eq_identity_iff [Fact (Admissible M)] {m : ℕ}
    (X : Matrix (Fin m) (Fin m) (KM M)) : X = identityTensor m ↔ ∀ j, tHat X j = 1 := by
  constructor
  · rintro rfl j
    exact (example26 (M := M) m).2.2.1 j
  · intro h
    apply tHat_injective
    funext j
    rw [h j, (example26 (M := M) m).2.2.1 j]

/-- "A tensor `𝒰` is `⋆_M`-unitary if and only if its transformed tensor `𝒰̂` is facewise
unitary (in the usual sense)." -/
theorem isStarMUnitary_iff_facewise [Fact (Admissible M)] {m : ℕ}
    (U : Matrix (Fin m) (Fin m) (KM M)) :
    IsStarMUnitary U ↔ ∀ j, (tHat U j)ᴴ * tHat U j = 1 ∧ tHat U j * (tHat U j)ᴴ = 1 := by
  unfold IsStarMUnitary
  rw [tsvd_eq_identity_iff, tsvd_eq_identity_iff, tHat_mul, tHat_mul, example27]
  simp only [facewise]
  exact ⟨fun h j => ⟨h.1 j, h.2 j⟩, fun h => ⟨fun j => (h j).1, fun j => (h j).2⟩⟩

/-- The `j`-th frontal slice `𝒜_{::j} ∈ ℝ^{m×p}` of a tensor. -/
def frontal {m p : ℕ} (A : Matrix (Fin m) (Fin p) (KM M)) (j : Fin n) :
    Matrix (Fin m) (Fin p) ℝ :=
  fun i k => (A i k).vec j

/-- **Definition 29.** A tensor is f-diagonal if all its frontal slices are diagonal
(an `m × p` matrix `D` is diagonal if `D_{ik} = 0` whenever `i ≠ k`). -/
def IsFDiagonal {m p : ℕ} (A : Matrix (Fin m) (Fin p) (KM M)) : Prop :=
  ∀ j (i : Fin m) (k : Fin p), (i : ℕ) ≠ k → frontal A j i k = 0

/-- The diagonal elements `σ₁, …, σ_{min(m,p)}` of a tensor `𝒮 ∈ 𝕂_M^{m×p}`
(indexed from `0`). -/
def sigma {m p : ℕ} (S : Matrix (Fin m) (Fin p) (KM M)) (i : Fin (min m p)) : KM M :=
  S (Fin.castLE (min_le_left m p) i) (Fin.castLE (min_le_right m p) i)

/-- `𝒜 = 𝒰 ⋆_M 𝒮 ⋆_M 𝒱ᴴ` is a `⋆_M`-SVD of `𝒜` (Theorem 30): `𝒰, 𝒱` are `⋆_M`-unitary,
`𝒮` is f-diagonal and `σ₁ ≥_M σ₂ ≥_M ⋯ ≥_M σ_{min(m,p)} ≥_M 0`. -/
def IsTSVD [Fact (Admissible M)] {m p : ℕ} (A : Matrix (Fin m) (Fin p) (KM M))
    (U : Matrix (Fin m) (Fin m) (KM M)) (S : Matrix (Fin m) (Fin p) (KM M))
    (V : Matrix (Fin p) (Fin p) (KM M)) : Prop :=
  IsStarMUnitary U ∧ IsStarMUnitary V ∧ IsFDiagonal S ∧ A = U * S * Vᴴ ∧
    (∀ i j : Fin (min m p), i ≤ j → sigma S j ≤ sigma S i) ∧ (∀ i, 0 ≤ sigma S i)

/-! ### Auxiliary lemmas for Theorem 30 -/

private lemma tsvd_unitary_iff {m : ℕ} (X : Matrix (Fin m) (Fin m) ℂ) :
    X ∈ unitaryGroup (Fin m) ℂ ↔ Xᴴ * X = 1 ∧ X * Xᴴ = 1 :=
  ⟨fun h => ⟨mem_unitaryGroup_iff'.1 h, mem_unitaryGroup_iff.1 h⟩,
    fun h => mem_unitaryGroup_iff.2 h.2⟩

private lemma tsvd_sigma_hat {m p : ℕ} (S : Matrix (Fin m) (Fin p) (KM M))
    (i : Fin (min m p)) (j : Fin n) : (sigma S i).hat j = diagEntry (tHat S j) i := rfl

private lemma isSingularDiag_im {m p : ℕ} {S : Matrix (Fin m) (Fin p) ℂ}
    (h : IsSingularDiag S) (i : Fin m) (k : Fin p) : (S i k).im = 0 := by
  by_cases hik : (i : ℕ) = k
  · have hi : (i : ℕ) < min m p := lt_min i.2 (hik ▸ k.2)
    have := h.2.1 ⟨i, hi⟩
    have e1 : Fin.castLE (min_le_left m p) ⟨i, hi⟩ = i := Fin.ext rfl
    have e2 : Fin.castLE (min_le_right m p) ⟨i, hi⟩ = k := Fin.ext hik
    simpa [diagEntry, e1, e2] using this
  · rw [h.1 i k hik, Complex.zero_im]

private lemma tsvd_diag_iff [Fact (Admissible M)] {m p : ℕ}
    (S : Matrix (Fin m) (Fin p) (KM M)) :
    (IsFDiagonal S ∧ (∀ i j : Fin (min m p), i ≤ j → sigma S j ≤ sigma S i) ∧
      (∀ i, 0 ≤ sigma S i)) ↔ ∀ j, IsSingularDiag (tHat S j) := by
  constructor
  · rintro ⟨hd, hle, hnn⟩ j
    refine ⟨fun i k hik => ?_, fun i => ?_, fun i => ?_, fun i i' hii' => ?_⟩
    · have : S i k = 0 := KM.ext (funext fun l => hd l i k hik)
      simp [tHat, this]
    · have := ((KM.le_def _ _).1 (hnn i) j).1
      simpa [tsvd_sigma_hat] using this
    · have := ((KM.le_def _ _).1 (hnn i) j).2
      simpa [tsvd_sigma_hat] using this
    · have := ((KM.le_def _ _).1 (hle i i' hii') j).2
      rw [KM.hat_sub, Pi.sub_apply, tsvd_sigma_hat, tsvd_sigma_hat, Complex.sub_re] at this
      change (diagEntry (tHat S j) i').re ≤ (diagEntry (tHat S j) i).re
      linarith
  · intro h
    refine ⟨fun l i k hik => ?_, fun i i' hii' => ?_, fun i => ?_⟩
    · have : S i k = 0 := KM.hat_injective (by
        funext j
        simpa [tHat] using (h j).1 i k hik)
      simp [frontal, this]
    · rw [KM.le_def]
      intro l
      rw [KM.hat_sub, Pi.sub_apply, tsvd_sigma_hat, tsvd_sigma_hat, Complex.sub_re,
        Complex.sub_im]
      have h1 := (h l).2.1 i
      have h2 := (h l).2.1 i'
      have h3 := (h l).2.2.2 i i' hii'
      change (diagEntry (tHat S l) i).im = 0 at h1
      change (diagEntry (tHat S l) i').im = 0 at h2
      change (diagEntry (tHat S l) i').re ≤ (diagEntry (tHat S l) i).re at h3
      constructor
      · rw [h1, h2, sub_zero]
      · linarith
    · rw [KM.le_def]
      intro l
      rw [KM.hat_sub, KM.hat_zero, sub_zero, tsvd_sigma_hat]
      exact ⟨(h l).2.1 i, (h l).2.2.1 i⟩

open Classical in
private def tsvdAssemble (M : Matrix (Fin n) (Fin n) ℂ) (partner : Fin n → Fin n) {m p : ℕ}
    (R B : Fin n → Matrix (Fin m) (Fin p) ℂ) : Fin n → Matrix (Fin m) (Fin p) ℂ :=
  fun j => if RowReal M j then R j else if j < partner j then B j
    else (B (partner j)).map (starRingEnd ℂ)

private lemma tsvdAssemble_conjPattern (hM : IsUnit M) (partner : Fin n → Fin n)
    (hp : ∀ j, ¬ RowReal M j → RowConjOf M j (partner j)) {m p : ℕ}
    (R B : Fin n → Matrix (Fin m) (Fin p) ℂ) (hR : ∀ j i k, (R j i k).im = 0) :
    SlicesConjPattern M (tsvdAssemble M partner R B) := by
  intro i k
  refine ⟨fun j hj => ?_, fun j k' hjk => ?_⟩
  · simp [tsvdAssemble, hj, hR]
  · by_cases hj : RowReal M j
    · obtain rfl := eq_of_rowReal_of_rowConjOf hM hj hjk
      simp only [tsvdAssemble, ite_eq_left hj]
      exact (Complex.conj_eq_iff_im.mpr (hR j i k)).symm
    · have hk' : k' = partner j := rowConjOf_unique' hM hjk (hp j hj)
      subst hk'
      have hpj : partner j ≠ j := by
        intro h
        have := hp j hj
        rw [h] at this
        exact hj (rowReal_of_rowConjOf_self this)
      have hpr : ¬ RowReal M (partner j) := fun h =>
        hpj (eq_of_rowReal_of_rowConjOf hM h (rowConjOf_symm (hp j hj)))
      have hpp : partner (partner j) = j :=
        rowConjOf_unique' hM (hp _ hpr) (rowConjOf_symm (hp j hj))
      by_cases hlt : j < partner j
      · have : ¬ partner j < partner (partner j) := by rw [hpp]; exact lt_asymm hlt
        have e1 : tsvdAssemble M partner R B j = B j := by
          simp only [tsvdAssemble, ite_eq_right hj, ite_eq_left hlt]
        have e2 : tsvdAssemble M partner R B (partner j) = (B j).map (starRingEnd ℂ) := by
          simp only [tsvdAssemble, ite_eq_right hpr, ite_eq_right this]
          rw [hpp]
        simp [e1, e2]
      · have : partner j < partner (partner j) := by
          rw [hpp]; exact lt_of_le_of_ne (not_lt.1 hlt) hpj
        simp [tsvdAssemble, hj, hpr, hlt, this]

/-- **Theorem 30** (Theorem 5.1 in [14]). Let `𝒜 ∈ 𝕂_M^{m×p}` be a tensor. Then there exist
`⋆_M`-unitary tensors `𝒰 ∈ 𝕂_M^{m×m}` and `𝒱 ∈ 𝕂_M^{p×p}` and an f-diagonal tensor
`𝒮 ∈ 𝕂_M^{m×p}` such that `𝒜 = 𝒰 ⋆_M 𝒮 ⋆_M 𝒱ᴴ`. Furthermore, if we denote by
`σ₁, …, σ_{min(m,p)}` the diagonal elements of `𝒮`, then
`σ₁ ≥_M σ₂ ≥_M ⋯ ≥_M σ_{min(m,p)} ≥_M 0`. -/
theorem theorem30 [Fact (Admissible M)] {m p : ℕ} (A : Matrix (Fin m) (Fin p) (KM M)) :
    ∃ U S V, IsTSVD A U S V := by
  classical
  have hM := (Fact.out : Admissible M)
  have hpart : ∀ j : Fin n, ∃ k, ¬ RowReal M j → RowConjOf M j k := by
    intro j
    by_cases hj : RowReal M j
    · exact ⟨j, fun h => absurd hj h⟩
    · rcases hM.2 j with h | ⟨k, ⟨_, hk⟩, _⟩
      · exact absurd h hj
      · exact ⟨k, fun _ => hk⟩
  choose partner hp using hpart
  choose Ub Sb Vb hb using fun j => exists_svd (tHat A j)
  choose Ur Sr Vr hr using fun j => exists_svd ((tHat A j).map Complex.re)
  set Uh := tsvdAssemble M partner (fun j => (Ur j).map ((↑) : ℝ → ℂ)) Ub
  set Sh := tsvdAssemble M partner (fun j => (Sr j).map ((↑) : ℝ → ℂ)) Sb
  set Vh := tsvdAssemble M partner (fun j => (Vr j).map ((↑) : ℝ → ℂ)) Vb
  have hsvd : ∀ j, IsSVD (tHat A j) (Uh j) (Sh j) (Vh j) := by
    intro j
    by_cases hj : RowReal M j
    · have e : ((tHat A j).map Complex.re).map ((↑) : ℝ → ℂ) = tHat A j := by
        ext i k
        exact Complex.ext rfl (by simpa using ((tHat_conjPattern A i k).1 j hj).symm)
      simp only [Uh, Sh, Vh, tsvdAssemble, ite_eq_left hj]
      have := (hr j).map_ofReal
      rwa [e] at this
    · by_cases hlt : j < partner j
      · simp only [Uh, Sh, Vh, tsvdAssemble, ite_eq_right hj, ite_eq_left hlt]
        exact hb j
      · have e : (tHat A (partner j)).map (starRingEnd ℂ) = tHat A j := by
          ext i k
          exact ((tHat_conjPattern A i k).2 j (partner j) (hp j hj)).symm
        have eS : (Sb (partner j)).map (starRingEnd ℂ) = Sb (partner j) := by
          ext i k
          exact Complex.conj_eq_iff_im.mpr (isSingularDiag_im (hb _).2.2.1 i k)
        simp only [Uh, Sh, Vh, tsvdAssemble, ite_eq_right hj, ite_eq_right hlt]
        have := (hb (partner j)).map_conj
        rw [eS]
        rwa [e] at this
  have hreal : ∀ {q r : ℕ} (X : Fin n → Matrix (Fin q) (Fin r) ℝ) (j i k),
      ((fun j => (X j).map ((↑) : ℝ → ℂ)) j i k).im = 0 := by
    intro q r X j i k
    simp
  have hU := tHat_tInv (M := M) Uh (tsvdAssemble_conjPattern hM.1 partner hp _ _ (hreal Ur))
  have hS := tHat_tInv (M := M) Sh (tsvdAssemble_conjPattern hM.1 partner hp _ _ (hreal Sr))
  have hV := tHat_tInv (M := M) Vh (tsvdAssemble_conjPattern hM.1 partner hp _ _ (hreal Vr))
  obtain ⟨hd, hle, hnn⟩ := (tsvd_diag_iff (tInv Sh : Matrix (Fin m) (Fin p) (KM M))).2
    (fun j => by rw [hS]; exact (hsvd j).2.2.1)
  refine ⟨tInv Uh, tInv Sh, tInv Vh, ?_, ?_, hd, ?_, hle, hnn⟩
  · rw [isStarMUnitary_iff_facewise, hU]
    exact fun j => (tsvd_unitary_iff _).1 (hsvd j).1
  · rw [isStarMUnitary_iff_facewise, hV]
    exact fun j => (tsvd_unitary_iff _).1 (hsvd j).2.1
  · apply tHat_injective
    rw [tHat_mul, tHat_mul, example27, hU, hS, hV]
    funext j
    exact (hsvd j).2.2.2

open Classical in
/-- The largest (`1`-based) index `r` with `σ_r ≠ 0`, or `0` if there is none. -/
def tsvdRank {m p : ℕ} (S : Matrix (Fin m) (Fin p) (KM M)) : ℕ :=
  Finset.univ.sup fun i : Fin (min m p) => if sigma S i ≠ 0 then (i : ℕ) + 1 else 0

/-- **Definition 31.** The `⋆_M`-rank of a tensor `𝒜`, `⋆_M-rank(𝒜)`, is the maximal `r` such
that `σ_r ≠ 0` (for the `⋆_M`-SVD of `𝒜`; by Lemma 32 this does not depend on the chosen
`⋆_M`-SVD, see `lemma32_any`). -/
def starMRank [Fact (Admissible M)] {m p : ℕ} (A : Matrix (Fin m) (Fin p) (KM M)) : ℕ :=
  tsvdRank (theorem30 A).choose_spec.choose

/-! ### Auxiliary lemmas for Lemma 32 -/

private lemma tsvd_card_eq_sup {N : ℕ} (P : Fin N → Prop) [DecidablePred P]
    (hP : ∀ i i', i' ≤ i → P i → P i') :
    Fintype.card {i // P i} = Finset.univ.sup fun i => if P i then (i : ℕ) + 1 else 0 := by
  set r := Finset.univ.sup fun i : Fin N => if P i then (i : ℕ) + 1 else 0
  have hrN : r ≤ N := Finset.sup_le fun i _ => by
    have := i.isLt
    split_ifs <;> omega
  have hfilter : Finset.univ.filter P = Finset.univ.filter (fun i : Fin N => (i : ℕ) < r) := by
    ext i
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · intro hi
      have : (if P i then (i : ℕ) + 1 else 0) ≤ r :=
        Finset.le_sup (f := fun i : Fin N => if P i then (i : ℕ) + 1 else 0) (Finset.mem_univ i)
      rw [ite_eq_left hi] at this
      omega
    · intro hi
      obtain ⟨i', _, hi'⟩ := (Finset.lt_sup_iff).1 hi
      by_cases h : P i'
      · rw [ite_eq_left h] at hi'
        exact hP i' i (by rw [Fin.le_iff_val_le_val]; omega) h
      · rw [ite_eq_right h] at hi'
        omega
  rw [Fintype.card_subtype, hfilter, Fin.card_filter_val_lt, min_eq_right hrN]

private theorem tsvdRank_eq_sup_rank [Fact (Admissible M)] {m p : ℕ}
    (A : Matrix (Fin m) (Fin p) (KM M))
    (U : Matrix (Fin m) (Fin m) (KM M)) (S : Matrix (Fin m) (Fin p) (KM M))
    (V : Matrix (Fin p) (Fin p) (KM M)) (h : IsTSVD A U S V) :
    tsvdRank S = Finset.univ.sup fun j => (tHat A j).rank := by
  classical
  obtain ⟨hU, hV, hd, hA, hle, hnn⟩ := h
  have hSd : ∀ j, IsSingularDiag (tHat S j) := (tsvd_diag_iff S).1 ⟨hd, hle, hnn⟩
  have hsvd : ∀ j, IsSVD (tHat A j) (tHat U j) (tHat S j) (tHat V j) := by
    intro j
    refine ⟨(tsvd_unitary_iff _).2 ((isStarMUnitary_iff_facewise U).1 hU j),
      (tsvd_unitary_iff _).2 ((isStarMUnitary_iff_facewise V).1 hV j), hSd j, ?_⟩
    rw [hA, tHat_mul, tHat_mul, example27]
    rfl
  have hrank : ∀ j, (tHat A j).rank = Finset.univ.sup fun i : Fin (min m p) =>
      if diagEntry (tHat S j) i ≠ 0 then (i : ℕ) + 1 else 0 := by
    intro j
    rw [(hsvd j).rank_eq]
    apply tsvd_card_eq_sup
    intro i i' hii' hi hzero
    apply hi
    have h1 : (diagEntry (tHat S j) i).im = 0 := (hSd j).2.1 i
    have h2 : 0 ≤ (diagEntry (tHat S j) i).re := (hSd j).2.2.1 i
    have h3 : (diagEntry (tHat S j) i).re ≤ (diagEntry (tHat S j) i').re := (hSd j).2.2.2 i' i hii'
    rw [hzero, Complex.zero_re] at h3
    exact Complex.ext (by rw [Complex.zero_re]; linarith) h1
  rw [Finset.sup_congr rfl fun j _ => hrank j, Finset.sup_comm]
  unfold tsvdRank
  apply Finset.sup_congr rfl
  intro i _
  by_cases hs : sigma S i = 0
  · rw [ite_eq_right (not_not.2 hs)]
    symm
    apply le_antisymm _ (Nat.zero_le _)
    apply Finset.sup_le
    intro j _
    have : diagEntry (tHat S j) i = 0 := by
      rw [← tsvd_sigma_hat, hs, KM.hat_zero, Pi.zero_apply]
    rw [ite_eq_right (not_not.2 this)]
  · rw [ite_eq_left hs]
    apply le_antisymm
    · obtain ⟨j, hj⟩ : ∃ j, diagEntry (tHat S j) i ≠ 0 := by
        by_contra hcon
        simp only [not_exists, not_not] at hcon
        apply hs
        apply KM.hat_injective
        funext j
        rw [KM.hat_zero, tsvd_sigma_hat, hcon j, Pi.zero_apply]
      have := Finset.le_sup (f := fun j => if diagEntry (tHat S j) i ≠ 0 then (i : ℕ) + 1 else 0)
        (Finset.mem_univ j)
      simp only [ite_eq_left hj] at this
      exact this
    · exact Finset.sup_le fun j _ => by split_ifs <;> omega

/-- **Lemma 32.** The `⋆_M`-rank of a tensor is the maximal rank of the frontal slices of its
transformed tensor: `⋆_M-rank(𝒜) = maxⱼ rank(𝒜̂ⱼ)`. -/
theorem lemma32 [Fact (Admissible M)] {m p : ℕ} (A : Matrix (Fin m) (Fin p) (KM M)) :
    starMRank A = Finset.univ.sup fun j => (tHat A j).rank :=
  tsvdRank_eq_sup_rank A _ _ _ (theorem30 A).choose_spec.choose_spec.choose_spec

/-- Lemma 32 holds for every `⋆_M`-SVD of `𝒜` (so Definition 31 is independent of the
choice of `⋆_M`-SVD). -/
theorem lemma32_any [Fact (Admissible M)] {m p : ℕ} (A : Matrix (Fin m) (Fin p) (KM M))
    (U : Matrix (Fin m) (Fin m) (KM M)) (S : Matrix (Fin m) (Fin p) (KM M))
    (V : Matrix (Fin p) (Fin p) (KM M)) (h : IsTSVD A U S V) :
    tsvdRank S = Finset.univ.sup fun j => (tHat A j).rank :=
  tsvdRank_eq_sup_rank A U S V h

theorem starMRank_le_min [Fact (Admissible M)] {m p : ℕ}
    (A : Matrix (Fin m) (Fin p) (KM M)) : starMRank A ≤ min m p := by
  unfold starMRank tsvdRank
  apply Finset.sup_le
  intro i _
  have := i.isLt
  split_ifs <;> omega

end Tubal
