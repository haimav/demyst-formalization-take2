import TubalAlgebra.Defs

/-!
# Realness of the `⋆_M` product (Lemma 2, Lemma 7, Lemmas 63, 64, 65)

The proofs of Lemma 2 and Lemma 7 are delegated in the paper to Section 10; Lemma 2 is
restated there as Lemma 65.

We introduce the auxiliary notion `ConjPattern M y` ("the complex vector `y` respects the
conjugation pattern of `M`"): `y_j` is real whenever row `j` of `M` is real, and
`y_j = conj(y_k)` whenever row `j` of `M` is the conjugate of row `k`. For admissible `M`,
the vectors respecting the pattern are exactly the transforms `M a` of real vectors `a`.
-/

open Matrix Complex

noncomputable section

namespace Tubal

variable {n : ℕ}

/-- The complex vector `y` respects the conjugation pattern of the rows of `M`. -/
def ConjPattern (M : Matrix (Fin n) (Fin n) ℂ) (y : Fin n → ℂ) : Prop :=
  (∀ j, RowReal M j → (y j).im = 0) ∧ (∀ j k, RowConjOf M j k → y j = starRingEnd ℂ (y k))


/-! ### Auxiliary facts -/

lemma mulVec_inv_mulVec' {M : Matrix (Fin n) (Fin n) ℂ} (hM : IsUnit M) (y : Fin n → ℂ) :
    M *ᵥ (M⁻¹ *ᵥ y) = y := by
  rw [mulVec_mulVec, Matrix.mul_nonsing_inv _ ((Matrix.isUnit_iff_isUnit_det M).mp hM),
    one_mulVec]

lemma inv_mulVec_mulVec' {M : Matrix (Fin n) (Fin n) ℂ} (hM : IsUnit M) (y : Fin n → ℂ) :
    M⁻¹ *ᵥ (M *ᵥ y) = y := by
  rw [mulVec_mulVec, Matrix.nonsing_inv_mul _ ((Matrix.isUnit_iff_isUnit_det M).mp hM),
    one_mulVec]

lemma mulVec_injective_of_isUnit {M : Matrix (Fin n) (Fin n) ℂ} (hM : IsUnit M) :
    Function.Injective (M *ᵥ ·) := by
  intro x y h
  have := congrArg (M⁻¹ *ᵥ ·) h
  simpa only [inv_mulVec_mulVec' hM] using this

/-- Rows of an invertible matrix are pairwise distinct. -/
lemma rows_eq_of_isUnit {M : Matrix (Fin n) (Fin n) ℂ} (hM : IsUnit M) {i j : Fin n}
    (h : ∀ k, M i k = M j k) : i = j := by
  by_contra hij
  have hdet : M.det ≠ 0 := ((Matrix.isUnit_iff_isUnit_det M).mp hM).ne_zero
  exact hdet (Matrix.det_zero_of_row_eq hij (funext h))

/-- Columns of an invertible matrix are pairwise distinct. -/
lemma cols_eq_of_isUnit {M : Matrix (Fin n) (Fin n) ℂ} (hM : IsUnit M) {i j : Fin n}
    (h : ∀ k, M k i = M k j) : i = j := by
  by_contra hij
  have hdet : M.det ≠ 0 := ((Matrix.isUnit_iff_isUnit_det M).mp hM).ne_zero
  exact hdet (Matrix.det_zero_of_column_eq hij h)

lemma mulVec_star_eq_of_rowConj (M : Matrix (Fin n) (Fin n) ℂ) (x : Fin n → ℂ) (i k : Fin n)
    (h : ∀ l, M i l = (starRingEnd ℂ) (M k l)) :
    (M *ᵥ star x) i = starRingEnd ℂ ((M *ᵥ x) k) := by
  simp only [mulVec, dotProduct, map_sum, map_mul, Pi.star_apply, h]
  rfl

lemma rowConjOf_symm {M : Matrix (Fin n) (Fin n) ℂ} {i j : Fin n} (h : RowConjOf M i j) :
    RowConjOf M j i := by
  intro k; rw [h k, Complex.conj_conj]

lemma rowReal_of_rowConjOf_self {M : Matrix (Fin n) (Fin n) ℂ} {i : Fin n}
    (h : RowConjOf M i i) : RowReal M i := fun k => (h k).symm

/-- Two rows conjugate to the same row are equal. -/
lemma rowConjOf_unique {M : Matrix (Fin n) (Fin n) ℂ} (hM : IsUnit M) {i j k : Fin n}
    (h₁ : RowConjOf M i k) (h₂ : RowConjOf M j k) : i = j :=
  rows_eq_of_isUnit hM fun l => by rw [h₁ l, h₂ l]

lemma rowConjOf_unique' {M : Matrix (Fin n) (Fin n) ℂ} (hM : IsUnit M) {i j k : Fin n}
    (h₁ : RowConjOf M k i) (h₂ : RowConjOf M k j) : i = j :=
  rowConjOf_unique hM (rowConjOf_symm h₁) (rowConjOf_symm h₂)

/-- A real row is only conjugate to itself. -/
lemma eq_of_rowReal_of_rowConjOf {M : Matrix (Fin n) (Fin n) ℂ} (hM : IsUnit M) {i k : Fin n}
    (hi : RowReal M i) (h : RowConjOf M i k) : i = k :=
  rows_eq_of_isUnit hM fun l => by
    have := congrArg (starRingEnd ℂ) (h l)
    rw [Complex.conj_conj, hi l] at this
    exact this

/-! ### The conjugation pattern (auxiliary) -/

theorem conjPattern_mulVec_toC (M : Matrix (Fin n) (Fin n) ℂ) (a : Fin n → ℝ) :
    ConjPattern M (M *ᵥ toC a) := by
  constructor
  · intro j hj
    have hj' : ∀ k, (starRingEnd ℂ) (M j k) = M j k := hj
    have h : starRingEnd ℂ ((M *ᵥ toC a) j) = (M *ᵥ toC a) j := by
      simp only [mulVec, dotProduct, map_sum, map_mul, toC_apply, Complex.conj_ofReal, hj']
    exact Complex.conj_eq_iff_im.mp h
  · intro j k hjk
    have hjk' : ∀ l, M j l = (starRingEnd ℂ) (M k l) := hjk
    simp only [mulVec, dotProduct, map_sum, map_mul, toC_apply, Complex.conj_ofReal, hjk']

/-- For admissible `M`, `M⁻¹ y` is real whenever `y` respects the conjugation pattern. -/
theorem inv_mulVec_mem_range_of_conjPattern (M : Matrix (Fin n) (Fin n) ℂ) (hM : IsUnit M)
    (hrow : ConjRowCondition M) {y : Fin n → ℂ} (hy : ConjPattern M y) :
    M⁻¹ *ᵥ y ∈ Set.range toC := by
  set x := M⁻¹ *ᵥ y with hx
  have hMx : M *ᵥ x = y := mulVec_inv_mulVec' hM y
  have hconj : M *ᵥ (star x) = y := by
    funext i
    rcases hrow i with hi | ⟨k, ⟨_, hik⟩, _⟩
    · have hi' : ∀ l, M i l = (starRingEnd ℂ) (M i l) := fun l => (hi l).symm
      rw [mulVec_star_eq_of_rowConj M x i i hi', hMx]
      exact Complex.conj_eq_iff_im.mpr (hy.1 i hi)
    · rw [mulVec_star_eq_of_rowConj M x i k hik, hMx, hy.2 i k hik]
  have : star x = x := mulVec_injective_of_isUnit hM (hconj.trans hMx.symm)
  refine ⟨fun i => (x i).re, ?_⟩
  funext i
  have hi : starRingEnd ℂ (x i) = x i := congrFun this i
  simp only [toC_apply]
  exact (Complex.conj_eq_iff_re.mp hi)

/-- For admissible `M`, the vectors respecting the conjugation pattern are exactly the
transforms `M a` of real vectors. -/
theorem conjPattern_iff_mem_range (M : Matrix (Fin n) (Fin n) ℂ) (hM : IsUnit M)
    (hrow : ConjRowCondition M) (y : Fin n → ℂ) :
    ConjPattern M y ↔ ∃ a : Fin n → ℝ, y = M *ᵥ toC a := by
  constructor
  · intro hy
    obtain ⟨a, ha⟩ := inv_mulVec_mem_range_of_conjPattern M hM hrow hy
    exact ⟨a, by rw [ha, mulVec_inv_mulVec' hM]⟩
  · rintro ⟨a, rfl⟩
    exact conjPattern_mulVec_toC M a

theorem ConjPattern.mul {M : Matrix (Fin n) (Fin n) ℂ} {y z : Fin n → ℂ}
    (hy : ConjPattern M y) (hz : ConjPattern M z) : ConjPattern M (y * z) := by
  constructor
  · intro j hj
    simp [Pi.mul_apply, Complex.mul_im, hy.1 j hj, hz.1 j hj]
  · intro j k hjk
    simp [Pi.mul_apply, hy.2 j k hjk, hz.2 j k hjk]

theorem ConjPattern.add {M : Matrix (Fin n) (Fin n) ℂ} {y z : Fin n → ℂ}
    (hy : ConjPattern M y) (hz : ConjPattern M z) : ConjPattern M (y + z) := by
  constructor
  · intro j hj
    simp [hy.1 j hj, hz.1 j hj]
  · intro j k hjk
    simp [hy.2 j k hjk, hz.2 j k hjk]

theorem ConjPattern.neg {M : Matrix (Fin n) (Fin n) ℂ} {y : Fin n → ℂ}
    (hy : ConjPattern M y) : ConjPattern M (-y) := by
  constructor
  · intro j hj
    simp [hy.1 j hj]
  · intro j k hjk
    simp [hy.2 j k hjk]

theorem ConjPattern.real_smul {M : Matrix (Fin n) (Fin n) ℂ} {y : Fin n → ℂ} (r : ℝ)
    (hy : ConjPattern M y) : ConjPattern M ((r : ℂ) • y) := by
  constructor
  · intro j hj
    simp [hy.1 j hj]
  · intro j k hjk
    simp [hy.2 j k hjk]

theorem ConjPattern.one (M : Matrix (Fin n) (Fin n) ℂ) : ConjPattern M 1 := by
  constructor
  · intro j _
    simp
  · intro j k _
    simp

theorem ConjPattern.zero (M : Matrix (Fin n) (Fin n) ℂ) : ConjPattern M 0 := by
  constructor
  · intro j _
    simp
  · intro j k _
    simp

theorem ConjPattern.star {M : Matrix (Fin n) (Fin n) ℂ} {y : Fin n → ℂ}
    (hy : ConjPattern M y) : ConjPattern M (star y) := by
  constructor
  · intro j hj
    simp [hy.1 j hj]
  · intro j k hjk
    simp [hy.2 j k hjk]

theorem ConjPattern.pinvVec {M : Matrix (Fin n) (Fin n) ℂ} {y : Fin n → ℂ}
    (hy : ConjPattern M y) : ConjPattern M (Tubal.pinvVec y) := by
  constructor
  · intro j hj
    have h := hy.1 j hj
    simp only [Tubal.pinvVec]
    split_ifs
    · simp
    · simp [Complex.inv_im, h]
  · intro j k hjk
    have h := hy.2 j k hjk
    simp only [Tubal.pinvVec]
    rw [h]
    by_cases hk : y k = 0
    · simp [hk]
    · have : (starRingEnd ℂ) (y k) ≠ 0 := by simpa using hk
      simp [hk, this, map_inv₀]

lemma toC_single (l : Fin n) : toC (Pi.single l (1 : ℝ)) = Pi.single l (1 : ℂ) := by
  funext k
  by_cases h : k = l
  · subst h; simp [toC]
  · simp [toC, h]

lemma conjPattern_pair {M : Matrix (Fin n) (Fin n) ℂ} (hM : IsUnit M) {j k : Fin n}
    (hj : ¬ RowReal M j) (hjk : RowConjOf M j k) (z : ℂ) :
    ConjPattern M (Pi.single j z + Pi.single k (starRingEnd ℂ z)) := by
  have hne : j ≠ k := fun h => hj (rowReal_of_rowConjOf_self (h ▸ hjk))
  have hk : ¬ RowReal M k := fun hk =>
    hne (eq_of_rowReal_of_rowConjOf hM hk (rowConjOf_symm hjk)).symm
  constructor
  · intro i hi
    have h1 : i ≠ j := fun h => hj (h ▸ hi)
    have h2 : i ≠ k := fun h => hk (h ▸ hi)
    simp [Pi.single_apply, h1, h2]
  · intro i l hil
    by_cases h1 : i = j
    · subst h1
      have : l = k := rowConjOf_unique' hM hil hjk
      subst this
      simp [Pi.single_apply, hne, hne.symm]
    · by_cases h2 : i = k
      · subst h2
        have : l = j := rowConjOf_unique' hM hil (rowConjOf_symm hjk)
        subst this
        simp [Pi.single_apply, hne, hne.symm]
      · have h3 : l ≠ j := fun h => h2 (rowConjOf_unique hM (h ▸ hil) (rowConjOf_symm hjk))
        have h4 : l ≠ k := fun h => h1 (rowConjOf_unique hM (h ▸ hil) hjk)
        simp [Pi.single_apply, h1, h2, h3, h4]

/-! ### Section 10 -/

/-- **Lemma 63.** Suppose `M ∈ ℂ^{n×n}` is an invertible matrix for which every row is either
real, or is conjugate to exactly one other row. If row `j` in `M` is real, then column `j` of
`M⁻¹` is real as well. On the other hand, if row `j` is complex and conjugate to row `k`, then
columns `j` and `k` in `M⁻¹` are complex and conjugate to each other. -/
theorem lemma63 (M : Matrix (Fin n) (Fin n) ℂ) (hM : IsUnit M) (hrow : ConjRowCondition M) :
    (∀ j, RowReal M j → ∀ i, starRingEnd ℂ (M⁻¹ i j) = M⁻¹ i j) ∧
    (∀ j k, ¬ RowReal M j → RowConjOf M j k →
      (∀ i, M⁻¹ i j = starRingEnd ℂ (M⁻¹ i k)) ∧
      (∃ i, starRingEnd ℂ (M⁻¹ i j) ≠ M⁻¹ i j) ∧
      (∃ i, starRingEnd ℂ (M⁻¹ i k) ≠ M⁻¹ i k)) := by
  have colj : ∀ j i, (M⁻¹ *ᵥ Pi.single j 1) i = M⁻¹ i j := by
    intro j i; rw [mulVec_single_one]; rfl
  have hinv : IsUnit M⁻¹ := (Matrix.isUnit_nonsing_inv_iff).mpr hM
  refine ⟨?_, ?_⟩
  · intro j hj i
    have hpat : ConjPattern M (Pi.single j 1) := by
      constructor
      · intro i' _
        by_cases h : i' = j
        · subst h; simp
        · simp [h]
      · intro i' k hik
        by_cases h1 : i' = j
        · subst h1
          have := eq_of_rowReal_of_rowConjOf hM hj hik
          subst this; simp
        · by_cases h2 : k = j
          · subst h2
            exact absurd (eq_of_rowReal_of_rowConjOf hM hj (rowConjOf_symm hik)).symm h1
          · simp [h1, h2]
    obtain ⟨c, hc⟩ := inv_mulVec_mem_range_of_conjPattern M hM hrow hpat
    have := congrFun hc i
    rw [colj] at this
    rw [← this]; simp [toC]
  · intro j k hj hjk
    have hne : j ≠ k := fun h => hj (rowReal_of_rowConjOf_self (h ▸ hjk))
    obtain ⟨c1, hc1⟩ := inv_mulVec_mem_range_of_conjPattern M hM hrow (conjPattern_pair hM hj hjk 1)
    obtain ⟨c2, hc2⟩ := inv_mulVec_mem_range_of_conjPattern M hM hrow (conjPattern_pair hM hj hjk I)
    have key : ∀ i, M⁻¹ i j = starRingEnd ℂ (M⁻¹ i k) := by
      intro i
      have e1 := congrFun hc1 i
      have e2 := congrFun hc2 i
      simp only [mulVec_add, Pi.add_apply, mulVec_single, map_one, Complex.conj_I, mul_one,
        toC_apply] at e1 e2
      apply Complex.ext
      · have := congrArg Complex.im e2
        simp at this
        simp; linarith
      · have := congrArg Complex.im e1
        simp at this
        simp; linarith
    refine ⟨key, ?_, ?_⟩
    · by_contra hcon
      push Not at hcon
      apply hne
      apply cols_eq_of_isUnit hinv
      intro i
      have h1 := hcon i
      rw [key i, Complex.conj_conj] at h1
      rw [key i]
      exact h1.symm
    · by_contra hcon
      push Not at hcon
      apply hne
      apply cols_eq_of_isUnit hinv
      intro i
      rw [key i, hcon i]

/-- **Lemma 64.** Suppose `M ∈ ℂ^{n×n}` is an invertible matrix for which every row is either
real, or is conjugate to exactly one other row. Then `M⁻¹ M̄` is real. -/
theorem lemma64 (M : Matrix (Fin n) (Fin n) ℂ) (hM : IsUnit M) (hrow : ConjRowCondition M) :
    ∃ R : Matrix (Fin n) (Fin n) ℝ, M⁻¹ * M.map (starRingEnd ℂ) = R.map (↑) := by
  have hcol : ∀ l : Fin n, ∃ r : Fin n → ℝ,
      M⁻¹ *ᵥ star (M *ᵥ toC (Pi.single l 1)) = toC r := by
    intro l
    obtain ⟨r, hr⟩ := inv_mulVec_mem_range_of_conjPattern M hM hrow
      (conjPattern_mulVec_toC M (Pi.single l 1)).star
    exact ⟨r, hr.symm⟩
  choose r hr using hcol
  refine ⟨Matrix.of fun i l => r l i, ?_⟩
  ext i l
  have h := congrFun (hr l) i
  have hs : star (M *ᵥ toC (Pi.single l 1)) = fun k => (starRingEnd ℂ) (M k l) := by
    funext k
    rw [toC_single, mulVec_single_one]
    rfl
  rw [hs] at h
  simp only [mulVec, dotProduct, toC_apply] at h
  simp only [Matrix.mul_apply, Matrix.map_apply, Matrix.of_apply]
  exact h

/-- **Lemma 65** (= **Lemma 2**). Let `M ∈ ℂ^{n×n}` be an invertible matrix. The result of
Eq. (5) is real for every `a, b ∈ ℝⁿ`, if and only if every row of `M` is either real, or is
conjugate to exactly one other row of `M`. -/
theorem lemma65 (M : Matrix (Fin n) (Fin n) ℂ) (hM : IsUnit M) :
    (∀ a b : Fin n → ℝ, starMC M (toC a) (toC b) ∈ Set.range toC) ↔ ConjRowCondition M := by
  constructor
  · intro h
    have hdet : IsUnit M.det := (Matrix.isUnit_iff_isUnit_det M).mp hM
    set Mc := M.map (starRingEnd ℂ) with hMc
    set N := Mc * M⁻¹ with hN
    have hconjvec : ∀ a : Fin n → ℝ, (fun i => starRingEnd ℂ ((M *ᵥ toC a) i)) = Mc *ᵥ toC a := by
      intro a; funext i
      simp [Mc, mulVec, dotProduct, map_sum]
    have key : ∀ a : Fin n → ℝ, N * diagonal (M *ᵥ toC a) = diagonal (Mc *ᵥ toC a) * N := by
      intro a
      set R := M⁻¹ * diagonal (M *ᵥ toC a) * M with hR
      have hRreal : R.map (starRingEnd ℂ) = R := by
        ext i k
        obtain ⟨c, hc⟩ := h a (Pi.single k 1)
        have hRik : R i k = starMC M (toC a) (toC (Pi.single k 1)) i := by
          have e : R i k = (R *ᵥ Pi.single k 1) i := by rw [mulVec_single_one]; rfl
          rw [e, toC_single, starMC, hR, ← mulVec_mulVec, ← mulVec_mulVec]
          congr 2
          funext l
          simp [mulVec_diagonal]
        rw [Matrix.map_apply, hRik, ← hc]
        simp [toC]
      have e1 : Mc * R * M⁻¹ = N * diagonal (M *ᵥ toC a) := by
        rw [hR, hN]
        simp only [Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hdet, Matrix.mul_one]
      have hMcinv : Mc * (M⁻¹).map (starRingEnd ℂ) = 1 := by
        rw [hMc, ← Matrix.map_mul, Matrix.mul_nonsing_inv _ hdet, Matrix.map_one] <;> simp
      have e2 : Mc * R.map (starRingEnd ℂ) * M⁻¹ = diagonal (Mc *ᵥ toC a) * N := by
        rw [hR, Matrix.map_mul, Matrix.map_mul, Matrix.diagonal_map (map_zero _), hconjvec, hN]
        rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, hMcinv, Matrix.one_mul, Matrix.mul_assoc]
      rw [← e1, ← e2, hRreal]
    -- entries
    have hent : ∀ i j, N i j ≠ 0 → RowConjOf M i j := by
      intro i j hij k
      have := congrFun (congrFun (key (Pi.single k 1)) i) j
      rw [Matrix.mul_diagonal, Matrix.diagonal_mul, toC_single, mulVec_single_one,
        mulVec_single_one] at this
      simp only [transpose_apply, Mc, Matrix.map_apply] at this
      have h2 : M j k = (starRingEnd ℂ) (M i k) := by
        have := mul_left_cancel₀ hij (this.trans (mul_comm _ _))
        exact this
      rw [h2, Complex.conj_conj]
    have hNdet : N.det ≠ 0 := by
      rw [hN, Matrix.det_mul, Matrix.det_nonsing_inv, hMc]
      have : (M.map (starRingEnd ℂ)).det = starRingEnd ℂ M.det := by
        rw [RingHom.map_det]; rfl
      rw [this]
      have h0 : M.det ≠ 0 := hdet.ne_zero
      simp [h0, Ring.inverse_eq_inv']
    intro i
    have : ∃ j, N i j ≠ 0 := by
      by_contra hcon
      push Not at hcon
      exact hNdet (Matrix.det_eq_zero_of_row_eq_zero i hcon)
    obtain ⟨j, hj⟩ := this
    have hc := hent i j hj
    by_cases hji : j = i
    · left
      subst hji
      exact rowReal_of_rowConjOf_self hc
    · right
      refine ⟨j, ⟨hji, hc⟩, ?_⟩
      rintro j' ⟨_, hc'⟩
      exact rowConjOf_unique' hM hc' hc
  · intro hrow a b
    exact inv_mulVec_mem_range_of_conjPattern M hM hrow
      ((conjPattern_mulVec_toC M a).mul (conjPattern_mulVec_toC M b))

/-- **Lemma 2.** Let `M ∈ ℂ^{n×n}` be an invertible matrix. Then `a ⋆_M b ∈ ℝⁿ` for all
`a, b ∈ ℝⁿ`, if and only if every row of `M` is either real, or obtained by entry-wise complex
conjugation of exactly one other row of `M`. -/
theorem lemma2 (M : Matrix (Fin n) (Fin n) ℂ) (hM : IsUnit M) :
    (∀ a b : Fin n → ℝ, starMC M (toC a) (toC b) ∈ Set.range toC) ↔ ConjRowCondition M :=
  lemma65 M hM

/-- **Lemma 7.** Let `M ∈ ℂ^{n×n}` be an invertible matrix. Suppose that every row of `M` is
either real, or is conjugate to exactly one other row of `M`. Then `x⁻ = M⁻¹ (M x)⁺` is real,
for every `x ∈ ℝⁿ`. -/
theorem lemma7 (M : Matrix (Fin n) (Fin n) ℂ) (hM : IsUnit M) (hrow : ConjRowCondition M)
    (x : Fin n → ℝ) : M⁻¹ *ᵥ pinvVec (M *ᵥ toC x) ∈ Set.range toC :=
  inv_mulVec_mem_range_of_conjPattern M hM hrow (conjPattern_mulVec_toC M x).pinvVec

end Tubal
