import TubalAlgebra.TSVD

/-!
# Low-rank tensor approximations via truncated tubal SVD (Section 7.1: Lemma 33,
Corollary 34, Theorem 35, Definition 36, Theorem 37)
-/

open Matrix Complex

noncomputable section

namespace Tubal

variable {n : ℕ} {M : Matrix (Fin n) (Fin n) ℂ}

/-- The Frobenius norm `‖𝒜‖_F` of a real tensor `𝒜 ∈ ℝ^{m×p×n}`. -/
def tnorm {m p : ℕ} (A : Matrix (Fin m) (Fin p) (KM M)) : ℝ :=
  Real.sqrt (∑ i, ∑ k, ∑ j, ((A i k).vec j) ^ 2)

/-- The Frobenius (Euclidean) norm `‖a‖_F` of a tube `a ∈ ℝⁿ`. -/
def tubeNorm (a : KM M) : ℝ := Real.sqrt (∑ j, (a.vec j) ^ 2)

/-! ### Auxiliary norm identities -/

private lemma ey_ofReal_sum_normSq {ι : Type*} [Fintype ι] (y : ι → ℂ) :
    ((∑ i, ‖y i‖ ^ 2 : ℝ) : ℂ) = star y ⬝ᵥ y := by
  simp only [dotProduct, Pi.star_apply, Complex.star_def, Complex.conj_mul']
  push_cast
  rfl

private lemma ey_sum_norm_sq_mulVec {ι : Type*} [Fintype ι] [DecidableEq ι]
    {W : Matrix ι ι ℂ} (hW : W ∈ unitaryGroup ι ℂ) (v : ι → ℂ) :
    ∑ i, ‖(W *ᵥ v) i‖ ^ 2 = ∑ i, ‖v i‖ ^ 2 := by
  apply Complex.ofReal_injective
  rw [ey_ofReal_sum_normSq, ey_ofReal_sum_normSq, star_mulVec, ← dotProduct_mulVec,
    mulVec_mulVec]
  have : Wᴴ * W = 1 := (mem_unitaryGroup_iff'.mp hW)
  rw [this, one_mulVec]

/-- The key norm identity for a tube: `∑ⱼ |âⱼ|² = |c|² ∑ⱼ aⱼ²`. -/
private lemma ey_sum_norm_sq_hat (W : Matrix (Fin n) (Fin n) ℂ)
    (hW : W ∈ unitaryGroup (Fin n) ℂ) (c : ℂ) (hMW : M = c • W) (a : KM M) :
    ∑ j, ‖a.hat j‖ ^ 2 = ‖c‖ ^ 2 * ∑ j, (a.vec j) ^ 2 := by
  have hx : ∀ x : Fin n → ℂ, M *ᵥ x = c • (W *ᵥ x) := by
    intro x; rw [hMW, smul_mulVec]
  have h1 : a.hat = c • (W *ᵥ toC a.vec) := hx _
  have h2 : ∑ j, ‖(W *ᵥ toC a.vec) j‖ ^ 2 = ∑ j, (a.vec j) ^ 2 := by
    rw [ey_sum_norm_sq_mulVec hW]
    simp [toC_apply, Complex.norm_real, sq_abs]
  rw [h1, ← h2, Finset.mul_sum]
  simp [Pi.smul_apply, mul_pow]


private lemma ey_frobSq_conjTranspose {m p : ℕ} (X : Matrix (Fin m) (Fin p) ℂ) :
    frobSq Xᴴ = frobSq X := by
  unfold frobSq
  rw [Finset.sum_comm]
  simp [conjTranspose_apply]

private lemma ey_frobSq_unitary_mul {m p : ℕ} {U : Matrix (Fin m) (Fin m) ℂ}
    (hU : U ∈ unitaryGroup (Fin m) ℂ) (X : Matrix (Fin m) (Fin p) ℂ) :
    frobSq (U * X) = frobSq X := by
  unfold frobSq
  rw [Finset.sum_comm, Finset.sum_comm (f := fun i k => ‖X i k‖ ^ 2)]
  refine Finset.sum_congr rfl fun k _ => ?_
  exact ey_sum_norm_sq_mulVec hU (fun j => X j k)

private lemma ey_frobSq_mul_unitary {m p : ℕ} {V : Matrix (Fin p) (Fin p) ℂ}
    (hV : V ∈ unitaryGroup (Fin p) ℂ) (X : Matrix (Fin m) (Fin p) ℂ) :
    frobSq (X * V) = frobSq X := by
  rw [← ey_frobSq_conjTranspose, conjTranspose_mul,
    ey_frobSq_unitary_mul (U := Vᴴ) (Unitary.star_mem hV), ey_frobSq_conjTranspose]

private lemma ey_tnorm_sq (W : Matrix (Fin n) (Fin n) ℂ)
    (hW : W ∈ unitaryGroup (Fin n) ℂ) (c : ℂ) (hc : c ≠ 0) (hMW : M = c • W) {m p : ℕ}
    (A : Matrix (Fin m) (Fin p) (KM M)) :
    tnorm A ^ 2 = (‖c‖ ^ 2)⁻¹ * ∑ j, frobSq (tHat A j) := by
  have hpos : (0 : ℝ) < ‖c‖ ^ 2 := by positivity
  have hsum : ∑ j, frobSq (tHat A j) = ‖c‖ ^ 2 * ∑ i, ∑ k, ∑ j, ((A i k).vec j) ^ 2 := by
    unfold frobSq tHat
    rw [Finset.sum_comm, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.sum_comm, Finset.mul_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    exact ey_sum_norm_sq_hat W hW c hMW (A i k)
  rw [hsum, tnorm, Real.sq_sqrt (by positivity), ← mul_assoc, inv_mul_cancel₀ hpos.ne',
    one_mul]

private lemma ey_tubeNorm_sq (W : Matrix (Fin n) (Fin n) ℂ)
    (hW : W ∈ unitaryGroup (Fin n) ℂ) (c : ℂ) (hc : c ≠ 0) (hMW : M = c • W) (a : KM M) :
    tubeNorm a ^ 2 = (‖c‖ ^ 2)⁻¹ * ∑ j, ‖a.hat j‖ ^ 2 := by
  have hpos : (0 : ℝ) < ‖c‖ ^ 2 := by positivity
  rw [ey_sum_norm_sq_hat W hW c hMW, tubeNorm, Real.sq_sqrt (by positivity), ← mul_assoc,
    inv_mul_cancel₀ hpos.ne', one_mul]

private lemma ey_tnorm_eq_of_sq {m p m' p' : ℕ} (A : Matrix (Fin m) (Fin p) (KM M))
    (B : Matrix (Fin m') (Fin p') (KM M)) (h : tnorm A ^ 2 = tnorm B ^ 2) :
    tnorm A = tnorm B := by
  have hA : 0 ≤ tnorm A := Real.sqrt_nonneg _
  have hB : 0 ≤ tnorm B := Real.sqrt_nonneg _
  exact (sq_eq_sq₀ hA hB).mp h



private lemma ey_sum_diag {R : Type*} [AddCommMonoid R] {m p : ℕ} (g : Fin m → Fin p → R)
    (hg : ∀ (i : Fin m) (k : Fin p), (i : ℕ) ≠ k → g i k = 0) :
    ∑ i, ∑ k, g i k = ∑ d : Fin (min m p),
      g (Fin.castLE (min_le_left m p) d) (Fin.castLE (min_le_right m p) d) := by
  have h1 : ∀ d : Fin (min m p),
      g (Fin.castLE (min_le_left m p) d) (Fin.castLE (min_le_right m p) d) =
        ∑ k, g (Fin.castLE (min_le_left m p) d) k := by
    intro d
    rw [Finset.sum_eq_single (Fin.castLE (min_le_right m p) d)]
    · intro k _ hk
      apply hg
      intro h
      apply hk
      ext
      simp [← h]
    · simp
  have h2 : ∑ d : Fin (min m p), ∑ k, g (Fin.castLE (min_le_left m p) d) k =
      ∑ i ∈ Finset.univ.map (Fin.castLEEmb (min_le_left m p)), ∑ k, g i k := by
    rw [Finset.sum_map]; rfl
  rw [Finset.sum_congr rfl fun d _ => h1 d, h2]
  symm
  apply Finset.sum_subset (Finset.subset_univ _)
  intro i _ hi
  apply Finset.sum_eq_zero
  intro k _
  apply hg
  intro hik
  apply hi
  simp only [Finset.mem_map, Finset.mem_univ, true_and]
  have hi' : (i : ℕ) < min m p := by
    have := k.isLt; have := i.isLt; omega
  exact ⟨⟨i, hi'⟩, by ext; simp⟩

private lemma ey_norm_eq_re {z : ℂ} (him : z.im = 0) (hre : 0 ≤ z.re) : ‖z‖ = z.re := by
  have hz : z = (z.re : ℂ) := Complex.ext rfl (by simp [him])
  conv_lhs => rw [hz]
  rw [Complex.norm_real, Real.norm_of_nonneg hre]

private lemma ey_tubeNorm_mono [Fact (Admissible M)] (W : Matrix (Fin n) (Fin n) ℂ)
    (hW : W ∈ unitaryGroup (Fin n) ℂ) (c : ℂ) (hc : c ≠ 0) (hMW : M = c • W) {a b : KM M}
    (hba : b ≤ a) (hb : 0 ≤ b) : tubeNorm b ≤ tubeNorm a := by
  have hpos : (0 : ℝ) < ‖c‖ ^ 2 := by positivity
  have key : ∀ l, ‖b.hat l‖ ≤ ‖a.hat l‖ := by
    intro l
    obtain ⟨h1, h2⟩ := (KM.le_def _ _).mp hba l
    obtain ⟨h3, h4⟩ := (KM.le_def _ _).mp hb l
    simp only [sub_zero, KM.hat_sub, Pi.sub_apply, Complex.sub_im, Complex.sub_re] at h1 h2 h3 h4
    rw [ey_norm_eq_re h3 h4, ey_norm_eq_re (by linarith) (by linarith)]
    linarith
  have hsq : ∑ j, (b.vec j) ^ 2 ≤ ∑ j, (a.vec j) ^ 2 := by
    have e1 := ey_sum_norm_sq_hat W hW c hMW a
    have e2 := ey_sum_norm_sq_hat W hW c hMW b
    have : ∑ j, ‖b.hat j‖ ^ 2 ≤ ∑ j, ‖a.hat j‖ ^ 2 :=
      Finset.sum_le_sum fun l _ => pow_le_pow_left₀ (norm_nonneg _) (key l) 2
    rw [e1, e2] at this
    exact le_of_mul_le_mul_left this hpos
  exact Real.sqrt_le_sqrt hsq

private lemma ey_sigma_eq_zero {m p : ℕ} (S : Matrix (Fin m) (Fin p) (KM M))
    (i : Fin (min m p)) (hi : tsvdRank S ≤ i) : sigma S i = 0 := by
  classical
  by_contra hne
  have hle : (if sigma S i ≠ 0 then (i : ℕ) + 1 else 0) ≤ tsvdRank S := by
    unfold tsvdRank
    convert Finset.le_sup (f := fun i : Fin (min m p) =>
      if sigma S i ≠ 0 then (i : ℕ) + 1 else 0) (Finset.mem_univ i)
  simp only [ne_eq, hne, not_false_eq_true, ↓reduceIte] at hle
  omega

private lemma ey_starMRank_eq [Fact (Admissible M)] {m p : ℕ}
    {A : Matrix (Fin m) (Fin p) (KM M)} {U : Matrix (Fin m) (Fin m) (KM M)}
    {S : Matrix (Fin m) (Fin p) (KM M)} {V : Matrix (Fin p) (Fin p) (KM M)}
    (h : IsTSVD A U S V) : starMRank A = tsvdRank S :=
  (lemma32 A).trans (lemma32_any A U S V h).symm

private lemma ey_slice_unitary [Fact (Admissible M)] {m : ℕ}
    {U : Matrix (Fin m) (Fin m) (KM M)} (hU : IsStarMUnitary U) (j : Fin n) :
    tHat U j ∈ unitaryGroup (Fin m) ℂ := by
  rw [mem_unitaryGroup_iff', star_eq_conjTranspose]
  exact ((isStarMUnitary_iff_facewise U).mp hU j).1

private lemma ey_isStarMUnitary_conjTranspose [Fact (Admissible M)] {m : ℕ}
    {U : Matrix (Fin m) (Fin m) (KM M)} (hU : IsStarMUnitary U) : IsStarMUnitary Uᴴ := by
  unfold IsStarMUnitary at hU ⊢
  rw [conjTranspose_conjTranspose]
  exact ⟨hU.2, hU.1⟩

/-- **Lemma 33** (Theorem 3.1 in [16]). Suppose `M = c W` for some unitary matrix `W` and
non-zero scalar `c`. Let `𝒰 ∈ 𝕂_M^{m×m}` be a `⋆_M`-unitary tensor. Then for any tensors `ℬ`
and `𝒞` of compatible sizes, we have `‖𝒰 ⋆_M ℬ‖_F = ‖ℬ‖_F` and `‖𝒞 ⋆_M 𝒰‖_F = ‖𝒞‖_F`. -/
theorem lemma33 [Fact (Admissible M)] (W : Matrix (Fin n) (Fin n) ℂ)
    (hW : W ∈ unitaryGroup (Fin n) ℂ) (c : ℂ) (hc : c ≠ 0) (hMW : M = c • W) {m : ℕ}
    (U : Matrix (Fin m) (Fin m) (KM M)) (hU : IsStarMUnitary U) :
    (∀ {l : ℕ} (B : Matrix (Fin m) (Fin l) (KM M)), tnorm (U * B) = tnorm B) ∧
    (∀ {l : ℕ} (C : Matrix (Fin l) (Fin m) (KM M)), tnorm (C * U) = tnorm C) := by
  have hsl := ey_slice_unitary hU
  refine ⟨fun B => ?_, fun C => ?_⟩
  · apply ey_tnorm_eq_of_sq
    rw [ey_tnorm_sq W hW c hc hMW, ey_tnorm_sq W hW c hc hMW, tHat_mul]
    simp only [facewise, ey_frobSq_unitary_mul (hsl _)]
  · apply ey_tnorm_eq_of_sq
    rw [ey_tnorm_sq W hW c hc hMW, ey_tnorm_sq W hW c hc hMW, tHat_mul]
    simp only [facewise, ey_frobSq_mul_unitary (hsl _)]

/-- **Corollary 34** (Corollary 3.3 in [16]). Consider the `⋆_M`-SVD of a tensor
`𝒜 ∈ 𝕂_M^{m×p}` given by `𝒜 = 𝒰 ⋆_M 𝒮 ⋆_M 𝒱ᴴ`. If `M = c W` for some unitary matrix `W` and
non-zero scalar `c` then `‖𝒜‖_F² = ‖𝒮‖_F² = ∑_{i=1}^{⋆_M-rank(𝒜)} ‖σᵢ‖_F²`. Moreover,
`‖σ₁‖_F ≥ ‖σ₂‖_F ≥ ⋯`. -/
theorem cor34 [Fact (Admissible M)] (W : Matrix (Fin n) (Fin n) ℂ)
    (hW : W ∈ unitaryGroup (Fin n) ℂ) (c : ℂ) (hc : c ≠ 0) (hMW : M = c • W) {m p : ℕ}
    (A : Matrix (Fin m) (Fin p) (KM M)) (U : Matrix (Fin m) (Fin m) (KM M))
    (S : Matrix (Fin m) (Fin p) (KM M)) (V : Matrix (Fin p) (Fin p) (KM M))
    (h : IsTSVD A U S V) :
    tnorm A ^ 2 = tnorm S ^ 2 ∧
    tnorm S ^ 2 = ∑ i : Fin (min m p), (if (i : ℕ) < starMRank A then tubeNorm (sigma S i) ^ 2
      else 0) ∧
    (∀ i j : Fin (min m p), i ≤ j → tubeNorm (sigma S j) ≤ tubeNorm (sigma S i)) := by
  have hrank := ey_starMRank_eq h
  obtain ⟨hU, hV, hS, hA, hord, hnn⟩ := h
  have h1 : tnorm A = tnorm S := by
    rw [hA, Matrix.mul_assoc, (lemma33 W hW c hc hMW U hU).1,
      (lemma33 W hW c hc hMW _ (ey_isStarMUnitary_conjTranspose hV)).2]
  refine ⟨by rw [h1], ?_, fun i j hij => ey_tubeNorm_mono W hW c hc hMW (hord i j hij) (hnn j)⟩
  rw [tnorm, Real.sq_sqrt (by positivity), ey_sum_diag]
  · refine Finset.sum_congr rfl fun d _ => ?_
    split_ifs with hd
    · rw [tubeNorm, Real.sq_sqrt (by positivity)]
      rfl
    · rw [hrank] at hd
      have := ey_sigma_eq_zero S d (not_lt.mp hd)
      unfold sigma at this
      simp [this]
  · intro i k hik
    exact Finset.sum_eq_zero fun j _ => by
      have := hS j i k hik
      simp only [frontal] at this
      simp [this]

/-- The truncation `[𝒜]_k := 𝒰_{:,1:k,:} ⋆_M 𝒮_{1:k,1:k,:} ⋆_M (𝒱_{:,1:k,:})ᴴ`
(for `k ≤ m`, `k ≤ p`). -/
def truncT [Fact (Admissible M)] {m p : ℕ} (U : Matrix (Fin m) (Fin m) (KM M))
    (S : Matrix (Fin m) (Fin p) (KM M)) (V : Matrix (Fin p) (Fin p) (KM M)) (k : ℕ)
    (hkm : k ≤ m) (hkp : k ≤ p) : Matrix (Fin m) (Fin p) (KM M) :=
  U.submatrix id (Fin.castLE hkm) * S.submatrix (Fin.castLE hkm) (Fin.castLE hkp) *
    (V.submatrix id (Fin.castLE hkp))ᴴ


private lemma ey_diagEntry_tHat {m p : ℕ} (S : Matrix (Fin m) (Fin p) (KM M)) (j : Fin n)
    (i : Fin (min m p)) : diagEntry (tHat S j) i = (sigma S i).hat j := rfl

private lemma ey_tHat_mul_mul_conjTranspose [Fact (Admissible M)] {m p q r : ℕ}
    (X : Matrix (Fin m) (Fin q) (KM M)) (Y : Matrix (Fin q) (Fin r) (KM M))
    (Z : Matrix (Fin p) (Fin r) (KM M)) (j : Fin n) :
    tHat (X * Y * Zᴴ) j = tHat X j * tHat Y j * (tHat Z j)ᴴ := by
  rw [tHat_mul, tHat_mul, example27]
  rfl

/-- Each frontal slice of the transformed `⋆_M`-SVD is a matrix SVD. -/
private lemma ey_slice_svd [Fact (Admissible M)] {m p : ℕ}
    {A : Matrix (Fin m) (Fin p) (KM M)} {U : Matrix (Fin m) (Fin m) (KM M)}
    {S : Matrix (Fin m) (Fin p) (KM M)} {V : Matrix (Fin p) (Fin p) (KM M)}
    (h : IsTSVD A U S V) (j : Fin n) :
    IsSVD (tHat A j) (tHat U j) (tHat S j) (tHat V j) := by
  obtain ⟨hU, hV, hS, hA, hord, hnn⟩ := h
  refine ⟨ey_slice_unitary hU j, ey_slice_unitary hV j, ⟨?_, ?_, ?_, ?_⟩, ?_⟩
  · intro i k hik
    have : S i k = 0 := KM.ext (funext fun l => hS l i k hik)
    simp [tHat, this]
  · intro i
    have := ((KM.le_def _ _).mp (hnn i) j).1
    simpa [ey_diagEntry_tHat] using this
  · intro i
    have := ((KM.le_def _ _).mp (hnn i) j).2
    simpa [ey_diagEntry_tHat] using this
  · intro i i' hii'
    have := ((KM.le_def _ _).mp (hord i i' hii') j).2
    simp only [KM.hat_sub, Pi.sub_apply, Complex.sub_re] at this
    simp only [ey_diagEntry_tHat, RCLike.re_to_complex]
    linarith
  · rw [hA, ey_tHat_mul_mul_conjTranspose]

private lemma ey_tHat_truncT [Fact (Admissible M)] {m p : ℕ}
    (U : Matrix (Fin m) (Fin m) (KM M)) (S : Matrix (Fin m) (Fin p) (KM M))
    (V : Matrix (Fin p) (Fin p) (KM M)) (k : ℕ) (hkm : k ≤ m) (hkp : k ≤ p) (j : Fin n) :
    tHat (truncT U S V k hkm hkp) j = truncProd (tHat U j) (tHat S j) (tHat V j) k := by
  rw [truncT, ey_tHat_mul_mul_conjTranspose, ← truncSub_eq_truncProd _ _ _ k hkm hkp]
  rfl

private lemma ey_rank_le_starMRank [Fact (Admissible M)] {m p : ℕ}
    (B : Matrix (Fin m) (Fin p) (KM M)) (j : Fin n) : (tHat B j).rank ≤ starMRank B := by
  rw [lemma32]
  exact Finset.le_sup (f := fun j => (tHat B j).rank) (Finset.mem_univ j)

/-- **Theorem 35** (Theorem 3.7 in [16]). Assume that `M = c W` for some unitary matrix `W`
and non-zero scalar `c`. Let `𝒜 ∈ 𝕂_M^{m×p}` be a tensor and let `𝒜 = 𝒰 ⋆_M 𝒮 ⋆_M 𝒱ᴴ` be
its `⋆_M`-SVD. For any `k ≤ ⋆_M-rank(𝒜)`, the tensor
`[𝒜]_k := 𝒰_{:,1:k,:} ⋆_M 𝒮_{1:k,1:k,:} ⋆_M 𝒱ᴴ_{:,1:k,:}` is the optimal `⋆_M`-rank-`k`
approximation of `𝒜` in the Frobenius norm: `[𝒜]_k` has `⋆_M`-rank at most `k`, and for any
tensor `ℬ` of the same size as `𝒜` with `⋆_M-rank(ℬ) ≤ k`, `‖𝒜 - [𝒜]_k‖_F² ≤ ‖𝒜 - ℬ‖_F²`. Moreover,
`‖𝒜 - [𝒜]_k‖_F² = ∑_{i=k+1}^{⋆_M-rank(𝒜)} ‖σᵢ‖_F²`.

(The paper's subscripts `1:r` are a typo for `1:k`, and `𝒱ᴴ_{:,1:k,:}` denotes
`(𝒱_{:,1:k,:})ᴴ`, the only reading for which the product is defined.) -/
theorem theorem35 [Fact (Admissible M)] (W : Matrix (Fin n) (Fin n) ℂ)
    (hW : W ∈ unitaryGroup (Fin n) ℂ) (c : ℂ) (hc : c ≠ 0) (hMW : M = c • W) {m p : ℕ}
    (A : Matrix (Fin m) (Fin p) (KM M)) (U : Matrix (Fin m) (Fin m) (KM M))
    (S : Matrix (Fin m) (Fin p) (KM M)) (V : Matrix (Fin p) (Fin p) (KM M))
    (h : IsTSVD A U S V) (k : ℕ) (hk : k ≤ starMRank A) :
    let Ak := truncT U S V k (hk.trans ((starMRank_le_min A).trans (min_le_left m p)))
      (hk.trans ((starMRank_le_min A).trans (min_le_right m p)))
    starMRank Ak ≤ k ∧
    (∀ B : Matrix (Fin m) (Fin p) (KM M), starMRank B ≤ k →
      tnorm (A - Ak) ^ 2 ≤ tnorm (A - B) ^ 2) ∧
    tnorm (A - Ak) ^ 2 = ∑ i : Fin (min m p),
      (if k ≤ (i : ℕ) ∧ (i : ℕ) < starMRank A then tubeNorm (sigma S i) ^ 2 else 0) := by
  intro Ak
  have hrank := ey_starMRank_eq h
  have hsvd := ey_slice_svd h
  have hAk : ∀ j, tHat Ak j = truncProd (tHat U j) (tHat S j) (tHat V j) k :=
    fun j => ey_tHat_truncT U S V k _ _ j
  have herr : ∀ j, tHat (A - Ak) j = tHat A j - truncProd (tHat U j) (tHat S j) (tHat V j) k := by
    intro j; rw [tHat_sub, Pi.sub_apply, hAk]
  have hpos : (0 : ℝ) < ‖c‖ ^ 2 := by positivity
  refine ⟨?_, ?_, ?_⟩
  · rw [lemma32]
    refine Finset.sup_le fun j _ => ?_
    rw [hAk]
    exact rank_truncProd_le _ _ _ _
  · intro B hB
    rw [ey_tnorm_sq W hW c hc hMW, ey_tnorm_sq W hW c hc hMW]
    refine mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun j _ => ?_) (by positivity)
    rw [herr, tHat_sub, Pi.sub_apply]
    exact eckart_young (hsvd j) k _ ((ey_rank_le_starMRank B j).trans hB)
  · rw [ey_tnorm_sq W hW c hc hMW]
    simp_rw [herr, (hsvd _).frobSq_sub_truncProd]
    rw [Finset.sum_comm, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    by_cases hki : k ≤ (i : ℕ)
    · simp only [hki, ↓reduceIte, true_and]
      split_ifs with hi
      · rw [ey_tubeNorm_sq W hW c hc hMW]
        rfl
      · rw [hrank] at hi
        have h0 := ey_sigma_eq_zero S i (not_lt.mp hi)
        simp [ey_diagEntry_tHat, h0]
    · simp [hki]

/-- **Definition 36** (first part). The `⋆_M`-multirank of a tensor `𝒜` is the `n`-tuple of
non-negative integers whose `j`-th entry is the rank of `𝒜̂_j`. -/
def multirank [Fact (Admissible M)] {m p : ℕ} (A : Matrix (Fin m) (Fin p) (KM M)) :
    Fin n → ℕ :=
  fun j => (tHat A j).rank

/-- **Definition 36** (second part). A tuple `r` respects the conjugation pattern of `M` if
`rᵢ = rⱼ` for every conjugate pair of rows `i, j` in `M`. -/
def RespectsConjPattern (M : Matrix (Fin n) (Fin n) ℂ) (r : Fin n → ℕ) : Prop :=
  ∀ i j, i ≠ j → RowConjOf M i j → r i = r j


open scoped ComplexOrder in
private lemma ey_rank_map_conj {m p : ℕ} (X : Matrix (Fin m) (Fin p) ℂ) :
    (X.map (starRingEnd ℂ)).rank = X.rank := by
  have : X.map (starRingEnd ℂ) = (Xᴴ)ᵀ := by
    ext i k; simp [conjTranspose_apply]
  rw [this, rank_transpose, rank_conjTranspose]

private lemma ey_tHat_conj {i j : Fin n} (hij : RowConjOf M i j) {m p : ℕ}
    (A : Matrix (Fin m) (Fin p) (KM M)) : tHat A i = (tHat A j).map (starRingEnd ℂ) := by
  funext a b
  exact (KM.hat_conjPattern (A a b)).2 i j hij

/-- **Definition 36** (remark). `⋆_M-multirank(𝒜)` respects the conjugation pattern of `M`. -/
theorem multirank_respectsConjPattern [Fact (Admissible M)] {m p : ℕ}
    (A : Matrix (Fin m) (Fin p) (KM M)) : RespectsConjPattern M (multirank A) := by
  intro i j _ hij
  unfold multirank
  rw [ey_tHat_conj hij A, ey_rank_map_conj]

theorem multirank_le_min [Fact (Admissible M)] {m p : ℕ} (A : Matrix (Fin m) (Fin p) (KM M))
    (j : Fin n) : multirank A j ≤ min m p := by
  have h1 := (tHat A j).rank_le_card_width
  have h2 := (tHat A j).rank_le_card_height
  simp only [Fintype.card_fin] at h1 h2
  exact le_min h2 h1

/-- The slice-wise truncation `[𝒜̂_j]_{r_j} = Û_{:,1:r_j,j} Ŝ_{1:r_j,1:r_j,j} V̂ᴴ_{:,1:r_j,j}`
of Theorem 37, for a `⋆_M`-SVD `(𝒰, 𝒮, 𝒱)` and a tuple `r ≤ ⋆_M-multirank(𝒜)`. -/
def truncSlices [Fact (Admissible M)] {m p : ℕ} (A : Matrix (Fin m) (Fin p) (KM M))
    (U : Matrix (Fin m) (Fin m) (KM M)) (S : Matrix (Fin m) (Fin p) (KM M))
    (V : Matrix (Fin p) (Fin p) (KM M)) (r : Fin n → ℕ) (hr : r ≤ multirank A) :
    Fin n → Matrix (Fin m) (Fin p) ℂ :=
  fun j => truncSub (tHat U j) (tHat S j) (tHat V j) (r j)
    ((hr j).trans ((multirank_le_min A j).trans (min_le_left m p)))
    ((hr j).trans ((multirank_le_min A j).trans (min_le_right m p)))


private lemma ey_truncProd_map_conj {m p : ℕ} (U' : Matrix (Fin m) (Fin m) ℂ)
    (S' : Matrix (Fin m) (Fin p) ℂ) (V' : Matrix (Fin p) (Fin p) ℂ) (r : ℕ) :
    truncProd (U'.map (starRingEnd ℂ)) (S'.map (starRingEnd ℂ)) (V'.map (starRingEnd ℂ)) r =
      (truncProd U' S' V' r).map (starRingEnd ℂ) := by
  ext i l
  simp only [truncProd, map_apply, map_sum]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
  split_ifs <;> simp

private lemma ey_diagEntry_eq_zero_of_rank_le {m p : ℕ} {X : Matrix (Fin m) (Fin p) ℂ}
    {U : Matrix (Fin m) (Fin m) ℂ} {S : Matrix (Fin m) (Fin p) ℂ} {V : Matrix (Fin p) (Fin p) ℂ}
    (h : IsSVD X U S V) (i : Fin (min m p)) (hi : X.rank ≤ i) : diagEntry S i = 0 := by
  by_contra hne
  have him := h.2.2.1.2.1
  have hre := h.2.2.1.2.2.1
  have hmono := h.2.2.1.2.2.2
  simp only [RCLike.im_to_complex, RCLike.re_to_complex] at him hre hmono
  have hpos : 0 < (diagEntry S i).re := by
    rcases (hre i).lt_or_eq with h2 | h2
    · exact h2
    · exact absurd (Complex.ext h2.symm (him i)) hne
  have hall : ∀ t : Fin ((i : ℕ) + 1), diagEntry S ⟨t, by omega⟩ ≠ 0 := by
    intro t hzero
    have := hmono ⟨t, by omega⟩ i (by show (t : ℕ) ≤ i; omega)
    rw [hzero] at this
    simp only [Complex.zero_re] at this
    linarith
  have hinj := Fintype.card_le_of_injective
    (fun t : Fin ((i : ℕ) + 1) =>
      (⟨⟨t, by omega⟩, hall t⟩ : {i' : Fin (min m p) // diagEntry S i' ≠ 0}))
    (by
      intro a b hab
      simp only [Subtype.mk.injEq, Fin.mk.injEq] at hab
      exact Fin.ext hab)
  rw [Fintype.card_fin, ← h.rank_eq] at hinj
  omega

/-- **Theorem 37** (Theorem 3.8 in [16]). Assume that `M = c W` for some unitary matrix `W`
and non-zero scalar `c`. Let `𝒜 ∈ 𝕂_M^{m×p}` be a tensor and let `𝒜 = 𝒰 ⋆_M 𝒮 ⋆_M 𝒱ᴴ` be its
`⋆_M`-SVD. For any `n`-size tuple of non-negative integers `r ≤ ⋆_M-multirank(𝒜)` which
respects the conjugation pattern of `M`, we define the tensor `[𝒜]_r` as the tensor in which
the frontal slice `j` in the transformed space is the `r_j` truncated SVD of the `j`th frontal
face of the transformed `𝒜`:
`([𝒜]_r)^_{::j} := [𝒜̂_j]_{r_j} = Û_{:,1:r_j,j} Ŝ_{1:r_j,1:r_j,j} V̂ᴴ_{:,1:r_j,j}`.
`[𝒜]_r` is the optimal `⋆_M`-multirank-`r` approximation of `𝒜` in the Frobenius norm. That
is, for any tensor `ℬ` of the same size as `𝒜` and `⋆_M`-multirank at most `r`, we have
`‖𝒜 - [𝒜]_r‖_F² ≤ ‖𝒜 - ℬ‖_F²`. Moreover,
`‖𝒜 - [𝒜]_r‖_F² = |c|⁻² · ∑_{j=1}^n ∑_{i=r_j+1}^{rank(𝒜̂_j)} σ̂²_{ij}`.

Here `[𝒜]_r := tInv (truncSlices …)`; the first conjunct states that this real tensor indeed
has the prescribed transformed frontal slices, and the second that it has `⋆_M`-multirank at
most `r`.

(The paper's factor `|c|⁻¹` is a typo for `|c|⁻²`, as confirmed by its Example 68;
see `example68_literal_false` in `TubalAlgebra.Examples.AppendixA`. Also "multirank-k" is a
typo for "multirank-r".) -/
theorem theorem37 [Fact (Admissible M)] (W : Matrix (Fin n) (Fin n) ℂ)
    (hW : W ∈ unitaryGroup (Fin n) ℂ) (c : ℂ) (hc : c ≠ 0) (hMW : M = c • W) {m p : ℕ}
    (A : Matrix (Fin m) (Fin p) (KM M)) (U : Matrix (Fin m) (Fin m) (KM M))
    (S : Matrix (Fin m) (Fin p) (KM M)) (V : Matrix (Fin p) (Fin p) (KM M))
    (h : IsTSVD A U S V) (r : Fin n → ℕ) (hr : r ≤ multirank A)
    (hpat : RespectsConjPattern M r) :
    let Ar : Matrix (Fin m) (Fin p) (KM M) := tInv (truncSlices A U S V r hr)
    tHat Ar = truncSlices A U S V r hr ∧
    multirank Ar ≤ r ∧
    (∀ B : Matrix (Fin m) (Fin p) (KM M), multirank B ≤ r →
      tnorm (A - Ar) ^ 2 ≤ tnorm (A - B) ^ 2) ∧
    tnorm (A - Ar) ^ 2 = (‖c‖ ^ 2)⁻¹ * ∑ j, ∑ i : Fin (min m p),
      (if r j ≤ (i : ℕ) ∧ (i : ℕ) < (tHat A j).rank then
        (RCLike.re (diagEntry (tHat S j) i)) ^ 2 else 0) := by
  intro Ar
  have hsvd := ey_slice_svd h
  set X := truncSlices A U S V r hr with hXdef
  have hX : ∀ j, X j = truncProd (tHat U j) (tHat S j) (tHat V j) (r j) :=
    fun j => truncSub_eq_truncProd _ _ _ _ _ _
  have hconj : ∀ j k, RowConjOf M j k → X j = (X k).map (starRingEnd ℂ) := by
    intro j k hjk
    have hrjk : r j = r k := by
      by_cases hj : j = k
      · rw [hj]
      · exact hpat j k hj hjk
    rw [hX, hX, hrjk, ey_tHat_conj hjk U, ey_tHat_conj hjk S, ey_tHat_conj hjk V,
      ey_truncProd_map_conj]
  have hpatX : SlicesConjPattern M X := by
    intro a b
    refine ⟨fun j hj => ?_, fun j k hjk => congrFun (congrFun (hconj j k hjk) a) b⟩
    have := congrFun (congrFun (hconj j j (fun l => (hj l).symm)) a) b
    exact Complex.conj_eq_iff_im.mp this.symm
  have htHat : tHat Ar = X := tHat_tInv X hpatX
  have herr : ∀ j, tHat (A - Ar) j =
      tHat A j - truncProd (tHat U j) (tHat S j) (tHat V j) (r j) := by
    intro j; rw [tHat_sub, Pi.sub_apply, htHat, hX]
  refine ⟨htHat, ?_, ?_, ?_⟩
  · intro j
    show (tHat Ar j).rank ≤ r j
    rw [htHat, hX]
    exact rank_truncProd_le _ _ _ _
  · intro B hB
    rw [ey_tnorm_sq W hW c hc hMW, ey_tnorm_sq W hW c hc hMW]
    refine mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun j _ => ?_) (by positivity)
    rw [herr, tHat_sub, Pi.sub_apply]
    exact eckart_young (hsvd j) (r j) _ (hB j)
  · rw [ey_tnorm_sq W hW c hc hMW]
    simp_rw [herr, (hsvd _).frobSq_sub_truncProd]
    congr 1
    refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun i _ => ?_
    have him := (hsvd j).2.2.1.2.1 i
    have hre := (hsvd j).2.2.1.2.2.1 i
    simp only [RCLike.im_to_complex, RCLike.re_to_complex] at him hre ⊢
    by_cases hri : r j ≤ (i : ℕ)
    · simp only [hri, ↓reduceIte, true_and]
      split_ifs with hi
      · rw [ey_norm_eq_re him hre]
      · have h0 := ey_diagEntry_eq_zero_of_rank_le (hsvd j) i (not_lt.mp hi)
        simp [h0]
    · simp [hri]

end Tubal
