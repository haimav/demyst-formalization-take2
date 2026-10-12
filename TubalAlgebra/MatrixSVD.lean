import Mathlib

/-!
# Matrix SVD and the Eckart–Young theorem (classical background for Section 7)

Over `𝕜 = ℝ` or `ℂ` (`RCLike`), a singular value decomposition of `X ∈ 𝕜^{m×p}` is
`X = U S Vᴴ` with `U, V` unitary and `S` rectangular diagonal with real, non-negative,
non-increasing diagonal entries (the singular values).

The rank-`r` truncation is `U_{:,1:r} S_{1:r,1:r} (V_{:,1:r})ᴴ`. The Eckart–Young theorem says
that it is an optimal rank-`r` approximation in the Frobenius norm.
-/

open Matrix

noncomputable section

namespace Tubal

variable {𝕜 : Type*} [RCLike 𝕜] {m p : ℕ}

/-- The `i`-th diagonal entry of a rectangular `m × p` matrix, `i < min m p`. -/
def diagEntry (S : Matrix (Fin m) (Fin p) 𝕜) (i : Fin (min m p)) : 𝕜 :=
  S (Fin.castLE (min_le_left m p) i) (Fin.castLE (min_le_right m p) i)

/-- `S` is rectangular diagonal with real, non-negative and non-increasing diagonal. -/
def IsSingularDiag (S : Matrix (Fin m) (Fin p) 𝕜) : Prop :=
  (∀ (i : Fin m) (k : Fin p), (i : ℕ) ≠ k → S i k = 0) ∧
  (∀ i, RCLike.im (diagEntry S i) = 0) ∧
  (∀ i, 0 ≤ RCLike.re (diagEntry S i)) ∧
  (∀ i j, i ≤ j → RCLike.re (diagEntry S j) ≤ RCLike.re (diagEntry S i))

/-- `X = U S Vᴴ` is a singular value decomposition. -/
def IsSVD (X : Matrix (Fin m) (Fin p) 𝕜) (U : Matrix (Fin m) (Fin m) 𝕜)
    (S : Matrix (Fin m) (Fin p) 𝕜) (V : Matrix (Fin p) (Fin p) 𝕜) : Prop :=
  U ∈ unitaryGroup (Fin m) 𝕜 ∧ V ∈ unitaryGroup (Fin p) 𝕜 ∧ IsSingularDiag S ∧
    X = U * S * Vᴴ

/-- matrix of an orthonormal basis (columns are the basis vectors). -/
def SVD.obMat {q : ℕ} (b : OrthonormalBasis (Fin q) 𝕜 (EuclideanSpace 𝕜 (Fin q))) :
    Matrix (Fin q) (Fin q) 𝕜 :=
  Matrix.of fun i j => b j i

theorem SVD.obMat_mem_unitary {q : ℕ} (b : OrthonormalBasis (Fin q) 𝕜 (EuclideanSpace 𝕜 (Fin q))) :
    SVD.obMat b ∈ unitaryGroup (Fin q) 𝕜 :=
  (EuclideanSpace.basisFun (Fin q) 𝕜).toMatrix_orthonormalBasis_mem_unitary b

theorem SVD.exists_sorted_eigen {A : Matrix (Fin p) (Fin p) 𝕜} (hA : A.IsHermitian) :
    ∃ (v : OrthonormalBasis (Fin p) 𝕜 (EuclideanSpace 𝕜 (Fin p))) (μ : Fin p → ℝ),
      Antitone μ ∧ (∀ k, A *ᵥ ⇑(v k) = μ k • ⇑(v k)) ∧ (∀ k, ∃ j, μ k = hA.eigenvalues j) := by
  let e₀ : Fin (Fintype.card (Fin p)) ≃ Fin p := Fintype.equivOfCardEq (Fintype.card_fin _)
  let τ : Fin p ≃ Fin p := (finCongr (Fintype.card_fin p).symm).trans e₀
  refine ⟨hA.eigenvectorBasis.reindex τ.symm, fun k => hA.eigenvalues (τ k), ?_, ?_, ?_⟩
  · intro k k' hkk'
    have h1 : ∀ k, hA.eigenvalues (τ k) = hA.eigenvalues₀ (finCongr (Fintype.card_fin p).symm k) := by
      intro k
      show hA.eigenvalues₀ (e₀.symm (e₀ _)) = _
      rw [Equiv.symm_apply_apply]
    show hA.eigenvalues (τ k') ≤ hA.eigenvalues (τ k)
    rw [h1, h1]
    apply hA.eigenvalues₀_antitone
    exact hkk'
  · intro k
    rw [OrthonormalBasis.reindex_apply, Equiv.symm_symm]
    exact hA.mulVec_eigenvectorBasis _
  · intro k
    exact ⟨_, rfl⟩

theorem SVD.gram (X : Matrix (Fin m) (Fin p) 𝕜)
    (v : OrthonormalBasis (Fin p) 𝕜 (EuclideanSpace 𝕜 (Fin p))) (μ : Fin p → ℝ)
    (hv : ∀ k, (Xᴴ * X) *ᵥ ⇑(v k) = μ k • ⇑(v k)) (k k' : Fin p) :
    star (X *ᵥ ⇑(v k)) ⬝ᵥ (X *ᵥ ⇑(v k')) = if k = k' then (μ k : 𝕜) else 0 := by
  rw [star_mulVec, ← dotProduct_mulVec, mulVec_mulVec, hv, dotProduct_smul]
  have h1 : star ⇑(v k) ⬝ᵥ ⇑(v k') = if k = k' then 1 else 0 := by
    have := (orthonormal_iff_ite.mp v.orthonormal) k k'
    rw [EuclideanSpace.inner_eq_star_dotProduct, dotProduct_comm] at this
    exact this
  rw [h1]
  split_ifs with h
  · subst h; simp [RCLike.real_smul_eq_coe_mul]
  · simp


open scoped ComplexOrder in
theorem SVD.eq_zero_of_star_dotProduct_self {n : Type*} [Fintype n] {x : n → 𝕜}
    (h : star x ⬝ᵥ x = 0) : x = 0 :=
  dotProduct_star_self_eq_zero.mp h

/-- Existence of the SVD (classical). -/
theorem exists_svd (X : Matrix (Fin m) (Fin p) 𝕜) :
    ∃ U S V, IsSVD X U S V := by
  classical
  have hH : (Xᴴ * X).IsHermitian := isHermitian_conjTranspose_mul_self X
  obtain ⟨v, μ, hμanti, hv, hμe⟩ := SVD.exists_sorted_eigen hH
  have hμ0 : ∀ k, 0 ≤ μ k := by
    intro k; obtain ⟨j, hj⟩ := hμe k; rw [hj]; exact eigenvalues_conjTranspose_mul_self_nonneg X j
  have hgram := SVD.gram X v μ hv
  let σ : Fin p → ℝ := fun k => Real.sqrt (μ k)
  have hσsq : ∀ k, σ k * σ k = μ k := fun k => Real.mul_self_sqrt (hμ0 k)
  have hσ0 : ∀ k, σ k = 0 ↔ μ k = 0 := fun k => Real.sqrt_eq_zero (hμ0 k)
  let w : Fin p → EuclideanSpace 𝕜 (Fin m) :=
    fun k => WithLp.toLp 2 (((σ k)⁻¹ : 𝕜) • (X *ᵥ ⇑(v k)))
  have hw : ∀ k k', μ k ≠ 0 → μ k' ≠ 0 →
      inner 𝕜 (w k) (w k') = if k = k' then (1 : 𝕜) else 0 := by
    intro k k' hk hk'
    rw [EuclideanSpace.inner_eq_star_dotProduct, dotProduct_comm]
    simp only [w, star_smul, smul_dotProduct, dotProduct_smul, hgram]
    split_ifs with h
    · subst h
      have hσ : (σ k : 𝕜) ≠ 0 := by
        simp only [ne_eq, RCLike.ofReal_eq_zero]
        rw [hσ0]; exact hk
      rw [← hσsq k]
      simp only [smul_eq_mul, RCLike.star_def, map_inv₀, RCLike.conj_ofReal, RCLike.ofReal_mul]
      field_simp
    · simp
  let T : Set (Fin p) := {k | μ k ≠ 0}
  have hT : Orthonormal 𝕜 (T.domRestrict w) := by
    rw [orthonormal_iff_ite]
    rintro ⟨k, hk⟩ ⟨k', hk'⟩
    simp only [Set.domRestrict, hw k k' hk hk', Subtype.mk.injEq]
  have hlt : ∀ k : Fin p, μ k ≠ 0 → (k : ℕ) < m := by
    intro k hk
    by_contra hkm
    push Not at hkm
    have hpos : 0 < μ k := lt_of_le_of_ne (hμ0 k) (Ne.symm hk)
    let f : Fin ((k : ℕ) + 1) → T := fun c => ⟨⟨c, by omega⟩, by
      show μ _ ≠ 0
      have : μ k ≤ μ ⟨c, by omega⟩ := hμanti (show (⟨c, _⟩ : Fin p) ≤ k from by
        rw [Fin.le_def]; simp only; omega)
      exact ne_of_gt (lt_of_lt_of_le hpos this)⟩
    have hf : Function.Injective f := by
      intro a b hab
      simp only [f, Subtype.mk.injEq, Fin.mk.injEq] at hab
      exact Fin.ext hab
    have := (hT.comp f hf).linearIndependent.fintype_card_le_finrank
    rw [Fintype.card_fin, finrank_euclideanSpace, Fintype.card_fin] at this
    omega
  let uvec : Fin m → EuclideanSpace 𝕜 (Fin m) :=
    fun j => if h : (j : ℕ) < p then w ⟨j, h⟩ else 0
  let s : Set (Fin m) := {j | ∃ h : (j : ℕ) < p, μ ⟨j, h⟩ ≠ 0}
  have hs : Orthonormal 𝕜 (s.domRestrict uvec) := by
    let g : s → T := fun j => ⟨⟨j.1, j.2.1⟩, j.2.2⟩
    have hg : s.domRestrict uvec = T.domRestrict w ∘ g := by
      funext j
      simp only [Set.domRestrict, Function.comp_apply, uvec, g, dite_eq_left j.2.1]
    rw [hg]
    refine hT.comp g ?_
    intro a b hab
    simp only [g, Subtype.mk.injEq, Fin.mk.injEq] at hab
    exact Subtype.ext (Fin.ext hab)
  obtain ⟨b, hb⟩ := hs.exists_orthonormalBasis_extension_of_card_eq
    (by rw [finrank_euclideanSpace])
  let S : Matrix (Fin m) (Fin p) 𝕜 := Matrix.of fun a k => if (a : ℕ) = k then (σ k : 𝕜) else 0
  have hV := SVD.obMat_mem_unitary v
  refine ⟨SVD.obMat b, S, SVD.obMat v, SVD.obMat_mem_unitary b, hV, ?_, ?_⟩
  · refine ⟨?_, ?_, ?_, ?_⟩
    · intro i k hik
      simp [S, hik]
    · intro i
      simp [diagEntry, S]
    · intro i
      simp only [diagEntry, S, Matrix.of_apply, Fin.val_castLE, ite_true, RCLike.ofReal_re]
      exact Real.sqrt_nonneg _
    · intro i j hij
      simp only [diagEntry, S, Matrix.of_apply, Fin.val_castLE, ite_true, RCLike.ofReal_re]
      exact Real.sqrt_le_sqrt (hμanti (by rw [Fin.le_def, Fin.val_castLE, Fin.val_castLE]; exact Fin.le_def.mp hij))
  · have hXV : X * SVD.obMat v = SVD.obMat b * S := by
      ext a k
      have lhs : (X * SVD.obMat v) a k = (X *ᵥ ⇑(v k)) a := by
        simp [Matrix.mul_apply, Matrix.mulVec, dotProduct, SVD.obMat]
      rw [lhs]
      by_cases hk : μ k = 0
      · have hXv : X *ᵥ ⇑(v k) = 0 := by
          have := hgram k k
          rw [ite_eq_left rfl, hk, RCLike.ofReal_zero] at this
          exact SVD.eq_zero_of_star_dotProduct_self this
        rw [hXv]
        simp [Matrix.mul_apply, S, (hσ0 k).mpr hk]
      · have hkm := hlt k hk
        have hj : (⟨k, hkm⟩ : Fin m) ∈ s := ⟨k.2, hk⟩
        have hbj := hb _ hj
        rw [Matrix.mul_apply, Finset.sum_eq_single (⟨k, hkm⟩ : Fin m)]
        · simp only [SVD.obMat, Matrix.of_apply, hbj, uvec, dite_eq_left k.2, S, ite_true, w]
          simp only [Fin.eta, Pi.smul_apply, smul_eq_mul]
          have hσ : (σ k : 𝕜) ≠ 0 := by
            simp only [ne_eq, RCLike.ofReal_eq_zero]
            rw [hσ0]; exact hk
          field_simp
        · intro j _ hjk
          have : (j : ℕ) ≠ k := fun h => hjk (Fin.ext h)
          simp [S, this]
        · simp
    have hVV : SVD.obMat v * (SVD.obMat v)ᴴ = 1 := by
      rw [← star_eq_conjTranspose]; exact mem_unitaryGroup_iff.mp hV
    calc X = X * (SVD.obMat v * (SVD.obMat v)ᴴ) := by rw [hVV, Matrix.mul_one]
      _ = SVD.obMat b * S * (SVD.obMat v)ᴴ := by rw [← Matrix.mul_assoc, hXV]


theorem SVD.map_mem_unitaryGroup {α β : Type*} [CommRing α] [StarRing α] [CommRing β] [StarRing β]
    {q : ℕ} (f : α →+* β) (hf : ∀ x, f (star x) = star (f x)) {A : Matrix (Fin q) (Fin q) α}
    (hA : A ∈ unitaryGroup (Fin q) α) : A.map f ∈ unitaryGroup (Fin q) β := by
  rw [mem_unitaryGroup_iff'] at hA ⊢
  rw [star_eq_conjTranspose, ← conjTranspose_map f (fun x => hf x), ← Matrix.map_mul,
    ← star_eq_conjTranspose, hA, Matrix.map_one f f.map_zero f.map_one]

/-- The SVD of the complexification of a real matrix. -/
theorem IsSVD.map_ofReal {X : Matrix (Fin m) (Fin p) ℝ} {U S V} (h : IsSVD X U S V) :
    IsSVD (X.map (↑)) (U.map ((↑) : ℝ → ℂ)) (S.map (↑)) (V.map (↑)) := by
  obtain ⟨hU, hV, ⟨hS1, hS2, hS3, hS4⟩, hX⟩ := h
  have hf : ∀ x : ℝ, Complex.ofRealHom (star x) = star (Complex.ofRealHom x) := fun x => by
    simp
  have hde : ∀ i, diagEntry (S.map ((↑) : ℝ → ℂ)) i = ((diagEntry S i : ℝ) : ℂ) := fun i => rfl
  refine ⟨SVD.map_mem_unitaryGroup Complex.ofRealHom hf hU,
    SVD.map_mem_unitaryGroup Complex.ofRealHom hf hV, ⟨?_, ?_, ?_, ?_⟩, ?_⟩
  · intro i k hik
    simp [hS1 i k hik]
  · intro i
    rw [hde]; simp
  · intro i
    rw [hde]; simpa using hS3 i
  · intro i j hij
    rw [hde, hde]; simpa using hS4 i j hij
  · rw [hX]
    change (U * S * Vᴴ).map Complex.ofRealHom =
      U.map Complex.ofRealHom * S.map Complex.ofRealHom * (V.map Complex.ofRealHom)ᴴ
    rw [Matrix.map_mul, Matrix.map_mul, conjTranspose_map _ (fun x => hf x)]

/-- The SVD of the entry-wise conjugate. -/
theorem IsSVD.map_conj {X : Matrix (Fin m) (Fin p) ℂ} {U S V} (h : IsSVD X U S V) :
    IsSVD (X.map (starRingEnd ℂ)) (U.map (starRingEnd ℂ)) S (V.map (starRingEnd ℂ)) := by
  obtain ⟨hU, hV, hS, hX⟩ := h
  have hf : ∀ x : ℂ, (starRingEnd ℂ) (star x) = star ((starRingEnd ℂ) x) := fun x => rfl
  have hSc : S.map (starRingEnd ℂ) = S := by
    ext i k
    simp only [Matrix.map_apply]
    by_cases hik : (i : ℕ) = k
    · have hi : (i : ℕ) < min m p := lt_min i.2 (hik ▸ k.2)
      have h1 : S i k = diagEntry S ⟨i, hi⟩ := by
        simp only [diagEntry]
        congr 1; ext; simp [hik]
      rw [h1, Complex.conj_eq_iff_im]
      simpa using hS.2.1 ⟨i, hi⟩
    · rw [hS.1 i k hik, map_zero]
  refine ⟨SVD.map_mem_unitaryGroup (starRingEnd ℂ) hf hU,
    SVD.map_mem_unitaryGroup (starRingEnd ℂ) hf hV, hS, ?_⟩
  rw [hX, Matrix.map_mul, Matrix.map_mul, hSc, conjTranspose_map _ (fun x => hf x)]

variable (𝕜) in
/-- The partial identity matrix `(δ_{ij})` of size `a × b`. -/
def SVD.inc (a b : ℕ) : Matrix (Fin a) (Fin b) 𝕜 :=
  Matrix.of fun i j => if (i : ℕ) = j then 1 else 0

theorem SVD.inc_conjTranspose (a b : ℕ) : (SVD.inc 𝕜 a b)ᴴ = SVD.inc 𝕜 b a := by
  ext i j
  by_cases h : (i : ℕ) = j
  · simp [SVD.inc, h]
  · simp [SVD.inc, h, Ne.symm h]

theorem SVD.inc_mul_inc {a b : ℕ} (h : b ≤ a) :
    SVD.inc 𝕜 b a * SVD.inc 𝕜 a b = 1 := by
  ext i j
  rw [Matrix.mul_apply, Finset.sum_eq_single (⟨i, by omega⟩ : Fin a)]
  · by_cases hij : i = j
    · subst hij; simp [SVD.inc]
    · have : (i : ℕ) ≠ j := fun h => hij (Fin.ext h)
      simp [SVD.inc, this, Matrix.one_apply_ne hij]
  · intro c _ hc
    have : (i : ℕ) ≠ c := fun h => hc (Fin.ext h.symm)
    simp [SVD.inc, this]
  · simp

theorem SVD.mul_inc_apply {ι : Type*} {a b : ℕ} (h : b ≤ a) (M : Matrix ι (Fin a) 𝕜) (x : ι)
    (i : Fin b) : (M * SVD.inc 𝕜 a b) x i = M x (Fin.castLE h i) := by
  rw [Matrix.mul_apply, Finset.sum_eq_single (Fin.castLE h i)]
  · simp [SVD.inc]
  · intro c _ hc
    have : (c : ℕ) ≠ i := fun h' => hc (Fin.ext (by simp [h']))
    simp [SVD.inc, this]
  · simp

/-- A rectangular diagonal matrix factors as `inc * diagonal * inc`. -/
theorem SVD.diag_factor (S : Matrix (Fin m) (Fin p) 𝕜)
    (hS : ∀ (i : Fin m) (k : Fin p), (i : ℕ) ≠ k → S i k = 0) :
    S = SVD.inc 𝕜 m (min m p) * diagonal (diagEntry S) * SVD.inc 𝕜 (min m p) p := by
  ext a b
  rw [Matrix.mul_apply]
  simp only [Matrix.mul_diagonal]
  by_cases hab : (a : ℕ) = b
  · have ha : (a : ℕ) < min m p := lt_min a.2 (hab ▸ b.2)
    rw [Finset.sum_eq_single (⟨a, ha⟩ : Fin (min m p))]
    · simp only [SVD.inc, Matrix.of_apply, ite_true, hab, one_mul, mul_one]
      simp only [diagEntry]
      congr 1; ext; simp [hab]
    · intro c _ hc
      have : (a : ℕ) ≠ c := fun h => hc (Fin.ext h.symm)
      simp [SVD.inc, this]
    · simp
  · rw [hS a b hab]
    symm
    apply Finset.sum_eq_zero
    intro c _
    by_cases h1 : (a : ℕ) = c
    · have h2 : (c : ℕ) ≠ b := by omega
      simp [SVD.inc, h2]
    · simp [SVD.inc, h1]

theorem SVD.unitary_star_mul {q : ℕ} {U : Matrix (Fin q) (Fin q) 𝕜}
    (hU : U ∈ unitaryGroup (Fin q) 𝕜) : Uᴴ * U = 1 := by
  rw [← star_eq_conjTranspose]; exact mem_unitaryGroup_iff'.mp hU

theorem SVD.unitary_mul_star {q : ℕ} {U : Matrix (Fin q) (Fin q) 𝕜}
    (hU : U ∈ unitaryGroup (Fin q) 𝕜) : U * Uᴴ = 1 := by
  rw [← star_eq_conjTranspose]; exact mem_unitaryGroup_iff.mp hU

/-- Rank is invariant under multiplication by matrices with one-sided inverses. -/
theorem SVD.rank_sandwich {ι ι' κ κ' : Type*} [Fintype ι] [Fintype ι'] [Fintype κ] [Fintype κ']
    [DecidableEq ι'] [DecidableEq κ']
    (A : Matrix ι ι' 𝕜) (A' : Matrix ι' ι 𝕜) (hA : A' * A = 1)
    (M : Matrix ι' κ' 𝕜) (B : Matrix κ' κ 𝕜) (B' : Matrix κ κ' 𝕜) (hB : B * B' = 1) :
    (A * M * B).rank = M.rank := by
  apply le_antisymm
  · exact (rank_mul_le_left _ _).trans (rank_mul_le_right _ _)
  · calc M.rank = (A' * (A * M * B) * B').rank := by
          rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, hA, Matrix.one_mul, Matrix.mul_assoc, hB,
            Matrix.mul_one]
      _ ≤ (A * M * B).rank := (rank_mul_le_left _ _).trans (rank_mul_le_right _ _)

theorem SVD.rank_of_offdiag (S : Matrix (Fin m) (Fin p) 𝕜)
    (hS : ∀ (i : Fin m) (k : Fin p), (i : ℕ) ≠ k → S i k = 0) :
    S.rank = Fintype.card {i : Fin (min m p) // diagEntry S i ≠ 0} := by
  classical
  have h := SVD.diag_factor S hS
  rw [h, SVD.rank_sandwich _ (SVD.inc 𝕜 (min m p) m) (SVD.inc_mul_inc (min_le_left m p)) _ _
    (SVD.inc 𝕜 p (min m p)) (SVD.inc_mul_inc (min_le_right m p)), rank_diagonal]
  rw [← h]

/-- The rank of `X` is the number of non-zero singular values. -/
theorem IsSVD.rank_eq {X : Matrix (Fin m) (Fin p) 𝕜} {U S V} (h : IsSVD X U S V) :
    X.rank = Fintype.card {i : Fin (min m p) // diagEntry S i ≠ 0} := by
  obtain ⟨hU, hV, hS, hX⟩ := h
  rw [hX, SVD.rank_sandwich U Uᴴ (SVD.unitary_star_mul hU) S Vᴴ V (SVD.unitary_star_mul hV),
    SVD.rank_of_offdiag S hS.1]

/-- The squared Frobenius norm `‖X‖_F² = ∑ |X_{ik}|²`. -/
def frobSq (X : Matrix (Fin m) (Fin p) 𝕜) : ℝ := ∑ i, ∑ k, ‖X i k‖ ^ 2

/-- The rank-`r` truncation `U_{:,1:r} S_{1:r,1:r} (V_{:,1:r})ᴴ`, written with explicit sums. -/
def truncProd (U : Matrix (Fin m) (Fin m) 𝕜) (S : Matrix (Fin m) (Fin p) 𝕜)
    (V : Matrix (Fin p) (Fin p) 𝕜) (r : ℕ) : Matrix (Fin m) (Fin p) 𝕜 :=
  fun i l => ∑ a : Fin m, ∑ b : Fin p,
    if (a : ℕ) < r ∧ (b : ℕ) < r then U i a * S a b * star (V l b) else 0

/-- The rank-`r` truncation in submatrix form `U_{:,1:r} S_{1:r,1:r} (V_{:,1:r})ᴴ`. -/
def truncSub (U : Matrix (Fin m) (Fin m) 𝕜) (S : Matrix (Fin m) (Fin p) 𝕜)
    (V : Matrix (Fin p) (Fin p) 𝕜) (r : ℕ) (hrm : r ≤ m) (hrp : r ≤ p) :
    Matrix (Fin m) (Fin p) 𝕜 :=
  U.submatrix id (Fin.castLE hrm) * S.submatrix (Fin.castLE hrm) (Fin.castLE hrp) *
    (V.submatrix id (Fin.castLE hrp))ᴴ

/-- General squared Frobenius norm on arbitrary finite index types. -/
def SVD.fsq {ι κ : Type*} [Fintype ι] [Fintype κ] (X : Matrix ι κ 𝕜) : ℝ :=
  ∑ i, ∑ k, ‖X i k‖ ^ 2

theorem SVD.frobSq_eq_fsq (X : Matrix (Fin m) (Fin p) 𝕜) : frobSq X = SVD.fsq X := rfl

theorem SVD.fsq_ofReal {ι κ : Type*} [Fintype ι] [Fintype κ] (X : Matrix ι κ 𝕜) :
    ((SVD.fsq X : ℝ) : 𝕜) = trace (Xᴴ * X) := by
  simp only [SVD.fsq, trace, diag, mul_apply, conjTranspose_apply, RCLike.star_def,
    RCLike.conj_mul, RCLike.ofReal_sum, RCLike.ofReal_pow]
  exact Finset.sum_comm

theorem SVD.fsq_nonneg {ι κ : Type*} [Fintype ι] [Fintype κ] (X : Matrix ι κ 𝕜) :
    0 ≤ SVD.fsq X := by
  unfold SVD.fsq; positivity

theorem SVD.fsq_mul_left {ι ι' κ : Type*} [Fintype ι] [Fintype ι'] [Fintype κ]
    [DecidableEq κ] [DecidableEq ι']
    (U : Matrix ι ι' 𝕜) (hU : Uᴴ * U = 1) (M : Matrix ι' κ 𝕜) :
    SVD.fsq (U * M) = SVD.fsq M := by
  apply RCLike.ofReal_injective (K := 𝕜)
  rw [SVD.fsq_ofReal, SVD.fsq_ofReal, conjTranspose_mul, Matrix.mul_assoc,
    ← Matrix.mul_assoc Uᴴ, hU, Matrix.one_mul]

theorem SVD.fsq_mul_right {ι κ κ' : Type*} [Fintype ι] [Fintype κ] [Fintype κ']
    [DecidableEq κ] [DecidableEq κ']
    (M : Matrix ι κ 𝕜) (V : Matrix κ κ' 𝕜) (hV : V * Vᴴ = 1) :
    SVD.fsq (M * V) = SVD.fsq M := by
  apply RCLike.ofReal_injective (K := 𝕜)
  rw [SVD.fsq_ofReal, SVD.fsq_ofReal, conjTranspose_mul, Matrix.mul_assoc, trace_mul_comm,
    Matrix.mul_assoc, Matrix.mul_assoc, hV, Matrix.mul_one]

theorem SVD.fsq_diagonal {n : ℕ} (d : Fin n → 𝕜) : SVD.fsq (diagonal d) = ∑ i, ‖d i‖ ^ 2 := by
  unfold SVD.fsq
  apply Finset.sum_congr rfl
  intro i _
  rw [Finset.sum_eq_single i]
  · simp
  · intro j _ hj
    simp [diagonal_apply_ne _ (Ne.symm hj)]
  · simp

theorem SVD.frobSq_of_offdiag (S : Matrix (Fin m) (Fin p) 𝕜)
    (hS : ∀ (i : Fin m) (k : Fin p), (i : ℕ) ≠ k → S i k = 0) :
    frobSq S = ∑ i, ‖diagEntry S i‖ ^ 2 := by
  have h := SVD.diag_factor S hS
  rw [SVD.frobSq_eq_fsq, h, SVD.fsq_mul_right _ _ (by
      rw [SVD.inc_conjTranspose, SVD.inc_mul_inc (min_le_right m p)]),
    SVD.fsq_mul_left _ (by rw [SVD.inc_conjTranspose, SVD.inc_mul_inc (min_le_left m p)]),
    SVD.fsq_diagonal, ← h]

theorem SVD.sum_ite_lt {M : Type*} [AddCommMonoid M] {r q : ℕ} (h : r ≤ q) (f : Fin q → M) :
    ∑ a : Fin q, (if (a : ℕ) < r then f a else 0) = ∑ a : Fin r, f (Fin.castLE h a) := by
  rw [← Finset.sum_filter]
  symm
  apply Finset.sum_nbij (Fin.castLE h)
  · intro a _
    simp [a.2]
  · intro a _ b _ hab
    exact Fin.castLE_injective h hab
  · intro b hb
    simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_ofPred_eq] at hb
    exact ⟨⟨b, hb⟩, by simp, rfl⟩
  · intro a _
    rfl

/-- The truncated middle factor. -/
def SVD.trunc (S : Matrix (Fin m) (Fin p) 𝕜) (r : ℕ) : Matrix (Fin m) (Fin p) 𝕜 :=
  Matrix.of fun a b => if (a : ℕ) < r ∧ (b : ℕ) < r then S a b else 0

theorem SVD.truncProd_eq (U : Matrix (Fin m) (Fin m) 𝕜) (S : Matrix (Fin m) (Fin p) 𝕜)
    (V : Matrix (Fin p) (Fin p) 𝕜) (r : ℕ) :
    truncProd U S V r = U * SVD.trunc S r * Vᴴ := by
  ext i l
  simp only [truncProd, Matrix.mul_apply, SVD.trunc, Matrix.of_apply, conjTranspose_apply,
    Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro a _
  apply Finset.sum_congr rfl
  intro b _
  split_ifs <;> simp

theorem truncSub_eq_truncProd (U : Matrix (Fin m) (Fin m) 𝕜) (S : Matrix (Fin m) (Fin p) 𝕜)
    (V : Matrix (Fin p) (Fin p) 𝕜) (r : ℕ) (hrm : r ≤ m) (hrp : r ≤ p) :
    truncSub U S V r hrm hrp = truncProd U S V r := by
  ext i l
  simp only [truncSub, truncProd, Matrix.mul_apply, Matrix.submatrix_apply, id_eq,
    conjTranspose_apply, Finset.sum_mul, ite_and, Finset.sum_ite_irrel, Finset.sum_const_zero]
  rw [SVD.sum_ite_lt hrm, Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro a _
  rw [SVD.sum_ite_lt hrp]

theorem rank_truncProd_le (U : Matrix (Fin m) (Fin m) 𝕜) (S : Matrix (Fin m) (Fin p) 𝕜)
    (V : Matrix (Fin p) (Fin p) 𝕜) (r : ℕ) : (truncProd U S V r).rank ≤ r := by
  rw [SVD.truncProd_eq]
  refine ((rank_mul_le_left _ _).trans (rank_mul_le_right _ _)).trans ?_
  classical
  refine (rank_le_card_of_support_subset _ (Finset.univ.filter (fun a : Fin m => (a : ℕ) < r))
    ?_).trans ?_
  · intro a ha
    simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_ofPred_eq]
    by_contra hr
    apply ha
    funext b
    simp [SVD.trunc, hr]
  · calc (Finset.univ.filter (fun a : Fin m => (a : ℕ) < r)).card
        ≤ (Finset.range r).card := by
          apply Finset.card_le_card_of_injOn (fun a : Fin m => (a : ℕ))
          · intro a ha
            simpa using ha
          · intro a _ b _ hab
            exact Fin.ext hab
      _ = r := Finset.card_range r

/-- The truncation error: `‖X - X_r‖_F² = ∑_{i > r} σᵢ²`. -/
theorem IsSVD.frobSq_sub_truncProd {X : Matrix (Fin m) (Fin p) 𝕜} {U S V} (h : IsSVD X U S V)
    (r : ℕ) :
    frobSq (X - truncProd U S V r) =
      ∑ i : Fin (min m p), if r ≤ (i : ℕ) then ‖diagEntry S i‖ ^ 2 else 0 := by
  obtain ⟨hU, hV, hS, hX⟩ := h
  have hsub : X - truncProd U S V r = U * (S - SVD.trunc S r) * Vᴴ := by
    rw [SVD.truncProd_eq, hX, Matrix.mul_sub, Matrix.sub_mul]
  have hoff : ∀ (i : Fin m) (k : Fin p), (i : ℕ) ≠ k → (S - SVD.trunc S r) i k = 0 := by
    intro i k hik
    simp [SVD.trunc, hS.1 i k hik]
  rw [hsub, SVD.frobSq_eq_fsq, SVD.fsq_mul_right _ _ (by
      rw [conjTranspose_conjTranspose]; exact SVD.unitary_star_mul hV),
    SVD.fsq_mul_left _ (SVD.unitary_star_mul hU), ← SVD.frobSq_eq_fsq,
    SVD.frobSq_of_offdiag _ hoff]
  apply Finset.sum_congr rfl
  intro i _
  simp only [diagEntry, Matrix.sub_apply, SVD.trunc, Matrix.of_apply, Fin.val_castLE]
  by_cases hi : r ≤ (i : ℕ)
  · simp [hi, show ¬ ((i : ℕ) < r) by omega]
  · simp [hi, show ((i : ℕ) < r) by omega]

theorem SVD.fsq_proj_split {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι]
    (P : Matrix ι ι 𝕜) (hPh : Pᴴ = P) (hPP : P * P = P) (M : Matrix ι κ 𝕜) :
    SVD.fsq M = SVD.fsq (P * M) + SVD.fsq ((1 - P) * M) := by
  apply RCLike.ofReal_injective (K := 𝕜)
  rw [RCLike.ofReal_add, SVD.fsq_ofReal, SVD.fsq_ofReal, SVD.fsq_ofReal, ← trace_add]
  congr 1
  have e2 : (1 - P) * (1 - P) = 1 - P := by
    rw [Matrix.sub_mul, Matrix.one_mul, Matrix.mul_sub, Matrix.mul_one, hPP, sub_self, sub_zero]
  have e1 : Mᴴ * P * (P * M) = Mᴴ * P * M := by
    rw [Matrix.mul_assoc, ← Matrix.mul_assoc P P M, hPP, ← Matrix.mul_assoc]
  have e3 : Mᴴ * (1 - P) * ((1 - P) * M) = Mᴴ * (1 - P) * M := by
    rw [Matrix.mul_assoc, ← Matrix.mul_assoc (1 - P) (1 - P) M, e2, ← Matrix.mul_assoc]
  rw [conjTranspose_mul, conjTranspose_mul, conjTranspose_sub, conjTranspose_one, hPh, e1, e3,
    ← Matrix.add_mul, ← Matrix.mul_add, add_sub_cancel, Matrix.mul_one]

theorem SVD.proj_diag {ι : Type*} [Fintype ι] (Q : Matrix ι ι 𝕜) (hQh : Qᴴ = Q)
    (hQQ : Q * Q = Q) (c : ι) : Q c c = ((∑ a, ‖Q a c‖ ^ 2 : ℝ) : 𝕜) := by
  conv_lhs => rw [← hQQ]
  rw [Matrix.mul_apply]
  push_cast
  apply Finset.sum_congr rfl
  intro a _
  have h1 : Q c a = star (Q a c) := by
    have := congrFun (congrFun hQh c) a
    rw [conjTranspose_apply] at this
    exact this.symm
  rw [h1, RCLike.star_def, RCLike.conj_mul]

theorem SVD.proj_diag_le_one {ι : Type*} [Fintype ι] (Q : Matrix ι ι 𝕜) (hQh : Qᴴ = Q)
    (hQQ : Q * Q = Q) (c : ι) : ∑ a, ‖Q a c‖ ^ 2 ≤ 1 := by
  have h0 : 0 ≤ ∑ a, ‖Q a c‖ ^ 2 := by positivity
  have h1 : ‖Q c c‖ ^ 2 ≤ ∑ a, ‖Q a c‖ ^ 2 :=
    Finset.single_le_sum (f := fun a => ‖Q a c‖ ^ 2) (fun a _ => by positivity)
      (Finset.mem_univ c)
  rw [SVD.proj_diag Q hQh hQQ c, RCLike.norm_ofReal, abs_of_nonneg h0] at h1
  nlinarith

theorem SVD.sum_castLE_le {n q : ℕ} (h : n ≤ q) (f : Fin q → ℝ) (hf : ∀ c, 0 ≤ f c) :
    ∑ i : Fin n, f (Fin.castLE h i) ≤ ∑ c, f c := by
  rw [← SVD.sum_ite_lt h]
  apply Finset.sum_le_sum
  intro c _
  split_ifs
  · exact le_rfl
  · exact hf c

/-- The elementary weight inequality behind Eckart–Young. -/
theorem SVD.weights_ineq {n : ℕ} (r : ℕ) (s w : Fin n → ℝ) (hs : Antitone s)
    (hs0 : ∀ i, 0 ≤ s i) (hw0 : ∀ i, 0 ≤ w i) (hw1 : ∀ i, w i ≤ 1) (hsum : ∑ i, w i ≤ r) :
    (∑ i : Fin n, if r ≤ (i : ℕ) then s i else 0) ≤ ∑ i, s i * (1 - w i) := by
  by_cases hrn : n ≤ r
  · have : ∀ i : Fin n, ¬ (r ≤ (i : ℕ)) := fun i h => by omega
    simp only [this, ite_false, Finset.sum_const_zero]
    exact Finset.sum_nonneg (fun i _ => mul_nonneg (hs0 i) (by linarith [hw1 i]))
  · push Not at hrn
    have hc0 : 0 ≤ s ⟨r, hrn⟩ := hs0 _
    have key : ∀ i : Fin n, s ⟨r, hrn⟩ * ((if (i : ℕ) < r then 1 else 0) - w i) ≤
        s i * (1 - w i) - (if r ≤ (i : ℕ) then s i else 0) := by
      intro i
      by_cases hi : (i : ℕ) < r
      · have : s ⟨r, hrn⟩ ≤ s i := hs (show i ≤ ⟨r, hrn⟩ by rw [Fin.le_def]; simp only; omega)
        simp only [hi, ite_true, show ¬ r ≤ (i : ℕ) by omega, ite_false, sub_zero]
        nlinarith [hw1 i]
      · have : s i ≤ s ⟨r, hrn⟩ := hs (show (⟨r, hrn⟩ : Fin n) ≤ i by
          rw [Fin.le_def]; simp only; omega)
        simp only [hi, ite_false, show r ≤ (i : ℕ) by omega, ite_true, zero_sub]
        nlinarith [hw0 i]
    have hcnt : ∑ i : Fin n, (if (i : ℕ) < r then (1 : ℝ) else 0) = r := by
      rw [SVD.sum_ite_lt hrn.le]
      simp
    have hsum' := Finset.sum_le_sum (fun i (_ : i ∈ Finset.univ) => key i)
    rw [← Finset.mul_sum, Finset.sum_sub_distrib, hcnt, Finset.sum_sub_distrib] at hsum'
    nlinarith

/-- Core of the Eckart–Young argument, in the coordinates of the SVD. -/
theorem SVD.core {S : Matrix (Fin m) (Fin p) 𝕜} (hS : IsSingularDiag S) (r : ℕ)
    (Q : Matrix (Fin m) (Fin m) 𝕜) (hQh : Qᴴ = Q) (hQQ : Q * Q = Q)
    (htr : RCLike.re (trace Q) ≤ r) (Z : Matrix (Fin m) (Fin p) 𝕜) (hZ : Q * Z = Z) :
    (∑ i : Fin (min m p), if r ≤ (i : ℕ) then ‖diagEntry S i‖ ^ 2 else 0) ≤
      SVD.fsq (S - Z) := by
  let w : Fin (min m p) → ℝ := fun i => ∑ a, ‖Q a (Fin.castLE (min_le_left m p) i)‖ ^ 2
  have hfS : SVD.fsq S = ∑ i, ‖diagEntry S i‖ ^ 2 := SVD.frobSq_of_offdiag S hS.1
  have hfQS : SVD.fsq (Q * S) = ∑ i, ‖diagEntry S i‖ ^ 2 * w i := by
    have h := SVD.diag_factor S hS.1
    conv_lhs => rw [h]
    rw [← Matrix.mul_assoc, SVD.fsq_mul_right _ _ (by
      rw [SVD.inc_conjTranspose, SVD.inc_mul_inc (min_le_right m p)]), ← Matrix.mul_assoc]
    unfold SVD.fsq
    simp only [Matrix.mul_diagonal, SVD.mul_inc_apply (min_le_left m p), norm_mul, mul_pow]
    rw [Finset.sum_comm]
    simp only [w, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro a _
    ring
  have hZ' : (1 - Q) * (S - Z) = (1 - Q) * S := by
    rw [Matrix.mul_sub, Matrix.sub_mul 1 Q Z, Matrix.one_mul, hZ, sub_self, sub_zero]
  have hsplit1 := SVD.fsq_proj_split Q hQh hQQ (S - Z)
  have hsplit2 := SVD.fsq_proj_split Q hQh hQQ S
  rw [hZ'] at hsplit1
  have hnn := SVD.fsq_nonneg (Q * (S - Z))
  have hmain : ∑ i, ‖diagEntry S i‖ ^ 2 * (1 - w i) ≤ SVD.fsq (S - Z) := by
    have : ∑ i, ‖diagEntry S i‖ ^ 2 * (1 - w i) =
        ∑ i, ‖diagEntry S i‖ ^ 2 - ∑ i, ‖diagEntry S i‖ ^ 2 * w i := by
      rw [← Finset.sum_sub_distrib]
      apply Finset.sum_congr rfl
      intro i _
      ring
    rw [this, ← hfS, ← hfQS]
    linarith
  refine le_trans ?_ hmain
  apply SVD.weights_ineq r (fun i => ‖diagEntry S i‖ ^ 2) w
  · intro i j hij
    have h1 : ∀ k, ‖diagEntry S k‖ ^ 2 = RCLike.re (diagEntry S k) ^ 2 := by
      intro k
      rw [RCLike.norm_sq_eq_def, hS.2.1 k]
      ring
    simp only [h1]
    exact pow_le_pow_left₀ (hS.2.2.1 j) (hS.2.2.2 i j hij) 2
  · intro i
    positivity
  · intro i
    positivity
  · intro i
    exact SVD.proj_diag_le_one Q hQh hQQ _
  · refine le_trans ?_ htr
    have htrace : RCLike.re (trace Q) = ∑ c, ∑ a, ‖Q a c‖ ^ 2 := by
      rw [trace, map_sum]
      apply Finset.sum_congr rfl
      intro c _
      rw [diag_apply, SVD.proj_diag Q hQh hQQ c, RCLike.ofReal_re]
    rw [htrace]
    exact SVD.sum_castLE_le (min_le_left m p) (fun c => ∑ a, ‖Q a c‖ ^ 2)
      (fun c => by positivity)

/-- An orthogonal projector onto (a space containing) the column space of `Y`, with trace equal
to the rank of `Y`. -/
theorem SVD.exists_proj (Y : Matrix (Fin m) (Fin p) 𝕜) :
    ∃ P : Matrix (Fin m) (Fin m) 𝕜, Pᴴ = P ∧ P * P = P ∧ P * Y = Y ∧
      RCLike.re (trace P) = Y.rank := by
  classical
  obtain ⟨U, S, V, hsvd⟩ := exists_svd Y
  have hrank := hsvd.rank_eq
  obtain ⟨hU, hV, hS, hY⟩ := hsvd
  let e : Fin (min m p) → 𝕜 := fun i => if diagEntry S i = 0 then 0 else 1
  let A := SVD.inc 𝕜 m (min m p)
  have hA : Aᴴ * A = 1 := by rw [SVD.inc_conjTranspose, SVD.inc_mul_inc (min_le_left m p)]
  have hUU : Uᴴ * U = 1 := SVD.unitary_star_mul hU
  have hEh : (diagonal e)ᴴ = diagonal e := by
    rw [diagonal_conjTranspose]
    congr 1
    funext i
    simp only [e, Pi.star_apply]
    split_ifs <;> simp
  have hEE : diagonal e * diagonal e = diagonal e := by
    rw [diagonal_mul_diagonal]
    congr 1
    funext i
    simp only [e]
    split_ifs <;> simp
  have hED : diagonal e * diagonal (diagEntry S) = diagonal (diagEntry S) := by
    rw [diagonal_mul_diagonal]
    congr 1
    funext i
    simp only [e]
    split_ifs with h <;> simp [h]
  refine ⟨U * (A * diagonal e * Aᴴ) * Uᴴ, ?_, ?_, ?_, ?_⟩
  · simp only [conjTranspose_mul, conjTranspose_conjTranspose, hEh, Matrix.mul_assoc]
  · simp only [Matrix.mul_assoc]
    rw [← Matrix.mul_assoc Uᴴ U, hUU, Matrix.one_mul, ← Matrix.mul_assoc Aᴴ A, hA,
      Matrix.one_mul, ← Matrix.mul_assoc (diagonal e) (diagonal e), hEE]
  · have hS' := SVD.diag_factor S hS.1
    rw [hY, hS']
    simp only [Matrix.mul_assoc]
    rw [← Matrix.mul_assoc Uᴴ U, hUU, Matrix.one_mul, ← Matrix.mul_assoc Aᴴ A, hA,
      Matrix.one_mul, ← Matrix.mul_assoc (diagonal e) (diagonal _), hED]
  · rw [trace_mul_comm, ← Matrix.mul_assoc, hUU, Matrix.one_mul, trace_mul_comm,
      ← Matrix.mul_assoc, hA, Matrix.one_mul, trace_diagonal, hrank, map_sum]
    have : ∀ i, RCLike.re (e i) = if diagEntry S i ≠ 0 then (1 : ℝ) else 0 := by
      intro i
      simp only [e]
      split_ifs <;> simp_all
    simp only [this]
    rw [Finset.sum_boole, Fintype.card_subtype]

/-- **Eckart–Young theorem** (Frobenius norm): the truncated SVD is an optimal rank-`r`
approximation. -/
theorem eckart_young {X : Matrix (Fin m) (Fin p) 𝕜} {U S V} (h : IsSVD X U S V) (r : ℕ)
    (Y : Matrix (Fin m) (Fin p) 𝕜) (hY : Y.rank ≤ r) :
    frobSq (X - truncProd U S V r) ≤ frobSq (X - Y) := by
  have hsvd := h
  obtain ⟨hU, hV, hS, hX⟩ := h
  obtain ⟨P, hPh, hPP, hPY, hPtr⟩ := SVD.exists_proj Y
  have hUU := SVD.unitary_star_mul hU
  have hUU' := SVD.unitary_mul_star hU
  have hVV := SVD.unitary_star_mul hV
  have hVV' := SVD.unitary_mul_star hV
  rw [hsvd.frobSq_sub_truncProd r]
  have key : frobSq (X - Y) = SVD.fsq (S - Uᴴ * Y * V) := by
    rw [SVD.frobSq_eq_fsq,
      ← SVD.fsq_mul_left Uᴴ (by rw [conjTranspose_conjTranspose]; exact hUU') (X - Y),
      ← SVD.fsq_mul_right (Uᴴ * (X - Y)) V hVV']
    congr 1
    rw [hX, Matrix.mul_sub, Matrix.sub_mul]
    congr 1
    simp only [Matrix.mul_assoc]
    rw [hVV, Matrix.mul_one, ← Matrix.mul_assoc, hUU, Matrix.one_mul]
  rw [key]
  apply SVD.core hS r (Uᴴ * P * U) ?_ ?_ ?_ (Uᴴ * Y * V) ?_
  · simp only [conjTranspose_mul, conjTranspose_conjTranspose, hPh, Matrix.mul_assoc]
  · simp only [Matrix.mul_assoc]
    rw [← Matrix.mul_assoc U Uᴴ, hUU', Matrix.one_mul, ← Matrix.mul_assoc P P, hPP]
  · rw [trace_mul_comm, ← Matrix.mul_assoc, hUU', Matrix.one_mul, hPtr]
    exact_mod_cast hY
  · simp only [Matrix.mul_assoc]
    rw [← Matrix.mul_assoc U Uᴴ, hUU', Matrix.one_mul, ← Matrix.mul_assoc P Y, hPY]

end Tubal
