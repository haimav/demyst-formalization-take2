import TubalAlgebra.Examples.Section3

/-!
# Examples of Section 3, continued: Eq. (3), Example 17, Example 18
-/

open Matrix Complex Polynomial

noncomputable section

namespace Tubal

variable {n : ℕ}

/-! ### Eq. (3) and Example 17 (polynomial products modulo `Q`) -/

/-- The polynomial `P_a := a₁ + a₂ X + ⋯ + aₙ X^{n-1}` associated with a vector `a`. -/
def polyOf {R : Type*} [CommRing R] (a : Fin n → R) : R[X] := ∑ k, C (a k) * X ^ (k : ℕ)

private lemma s3b_polyOf_map (a : Fin n → ℝ) :
    (polyOf a).map (algebraMap ℝ ℂ) = polyOf (toC a) := by
  simp [polyOf, Polynomial.map_sum, toC]

private lemma s3b_vandermonde_mulVec (r : Fin n → ℂ) (a : Fin n → ℂ) (j : Fin n) :
    (vandermonde r *ᵥ a) j = (polyOf a).eval (r j) := by
  simp only [mulVec, dotProduct, vandermonde_apply, polyOf, eval_finsetSum, eval_mul, eval_C,
    eval_pow, eval_X]
  exact Finset.sum_congr rfl fun k _ => mul_comm _ _

/-- Over `ℂ`, divisibility by a degree-`n` polynomial with `n` distinct known roots. -/
private lemma s3b_dvd_iff_roots (Qc : ℂ[X]) (hQ : Qc.natDegree = n) (r : Fin n → ℂ)
    (hr : Function.Injective r) (hroot : ∀ j, Qc.IsRoot (r j)) (hn : n ≠ 0) (F : ℂ[X]) :
    Qc ∣ F ↔ ∀ j, F.IsRoot (r j) := by
  constructor
  · rintro ⟨g, rfl⟩ j
    simp [IsRoot, (hroot j).eq_zero]
  · intro hF
    have hP : ∀ G : ℂ[X], (∀ j, G.IsRoot (r j)) → (∏ j, (X - C (r j))) ∣ G := fun G hG =>
      Fintype.prod_dvd_of_coprime (pairwise_coprime_X_sub_C hr)
        (fun j => dvd_iff_isRoot.mpr (hG j))
    obtain ⟨u, hu⟩ := hP Qc hroot
    have hQ0 : Qc ≠ 0 := by
      rintro rfl
      simp at hQ
      exact hn hQ.symm
    have hP0 : (∏ j, (X - C (r j))) ≠ 0 := (monic_prod_X_sub_C r Finset.univ).ne_zero
    have hu0 : u ≠ 0 := by
      rintro rfl
      rw [mul_zero] at hu
      exact hQ0 hu
    have hdu : u.natDegree = 0 := by
      have := natDegree_mul hP0 hu0
      rw [← hu, hQ, natDegree_finsetProd_X_sub_C_eq_card, Finset.card_univ,
        Fintype.card_fin] at this
      omega
    rw [eq_C_of_natDegree_eq_zero hdu] at hu
    have hc : u.coeff 0 ≠ 0 := by
      intro h
      rw [h, C_0, mul_zero] at hu
      exact hQ0 hu
    obtain ⟨w, hw⟩ := hP F hF
    refine ⟨C (u.coeff 0)⁻¹ * w, ?_⟩
    rw [hw, hu, mul_assoc, ← mul_assoc (C _), ← C_mul, mul_inv_cancel₀ hc, C_1, one_mul]

/-- **Example 17.** Let `Q` be a polynomial of degree `n` all of whose roots `r₀, …, r_{n-1}`
are distinct, and let `M` be the Vandermonde matrix at the roots of `Q`. Then
`P_c = P_a · P_b mod Q ⟺ M c = M a • M b`. -/
theorem example17 (Q : ℝ[X]) (hQ : Q.natDegree = n) (r : Fin n → ℂ) (hr : Function.Injective r)
    (hroot : ∀ j, (Q.map (algebraMap ℝ ℂ)).IsRoot (r j)) (a b c : Fin n → ℝ) :
    Q ∣ polyOf c - polyOf a * polyOf b ↔
      vandermonde r *ᵥ toC c = (vandermonde r *ᵥ toC a) * (vandermonde r *ᵥ toC b) := by
  rcases Nat.eq_zero_or_pos n with hn | hn
  · subst hn
    simp only [polyOf, Finset.univ_eq_empty, Finset.sum_empty, mul_zero, sub_zero, dvd_zero,
      true_iff]
    funext j; exact j.elim0
  rw [← map_dvd_map' (algebraMap ℝ ℂ), s3b_dvd_iff_roots _ (by rw [natDegree_map, hQ]) r hr hroot
    hn.ne']
  simp only [Polynomial.map_sub, Polynomial.map_mul, s3b_polyOf_map, IsRoot, eval_sub, eval_mul,
    ← s3b_vandermonde_mulVec, sub_eq_zero]
  constructor
  · intro h; funext j; exact h j
  · intro h j; exact congrFun h j

/-- The product of Section 3.2 / Example 17: `a · b` is the tube associated with the remainder
`P_a · P_b mod Q` (whose degree is `< n` when `Q` has degree `n`). -/
def polyModMul (Q : ℝ[X]) (a b : Fin n → ℝ) : Fin n → ℝ :=
  fun k => ((polyOf a * polyOf b) % Q).coeff (k : ℕ)

/-- Helper: a product diagonalized by an invertible `M` is `⋆_M` and gives a tubal ring. -/
private lemma s3b_tubal_of_diag (M : Matrix (Fin n) (Fin n) ℂ) (hM : IsUnit M)
    (p : (Fin n → ℝ) → (Fin n → ℝ) → (Fin n → ℝ))
    (h : ∀ a b, M *ᵥ toC (p a b) = (M *ᵥ toC a) * (M *ᵥ toC b)) :
    (∀ a b, toC (p a b) = starMC M (toC a) (toC b)) ∧ ∃ T : TubalRing n, T.mul = p := by
  have h1 : ∀ a b, toC (p a b) = starMC M (toC a) (toC b) := by
    intro a b
    rw [starMC, ← h, inv_mulVec_mulVec' hM]
  refine ⟨h1, ?_⟩
  obtain ⟨T, hT⟩ := exists_tubalRing_of_starM M hM (fun a b => ⟨p a b, h1 a b⟩)
  refine ⟨T, ?_⟩
  funext a b
  exact toC_injective ((hT a b).trans (h1 a b).symm)

/-- Section 3.2 / **Example 17**: "we can choose some other polynomial `Q`, as long as its degree
is `n` (for a ring over `ℝⁿ`) and all its roots are distinct … polynomial product modulo `Q` is
essentially `⋆_M` with this `M`": the Vandermonde matrix at the roots is admissible, the mod-`Q`
product is `⋆_M`, and it makes `ℝⁿ` a tubal ring. -/
theorem example17_tubal (Q : ℝ[X]) (hQ : Q.natDegree = n) (r : Fin n → ℂ)
    (hr : Function.Injective r) (hroot : ∀ j, (Q.map (algebraMap ℝ ℂ)).IsRoot (r j)) :
    Admissible (vandermonde r) ∧
    (∀ a b : Fin n → ℝ, toC (polyModMul Q a b) = starMC (vandermonde r) (toC a) (toC b)) ∧
    ∃ T : TubalRing n, T.mul = polyModMul Q := by
  have hU : IsUnit (vandermonde r) := by
    rw [Matrix.isUnit_iff_isUnit_det]
    exact isUnit_iff_ne_zero.mpr (det_vandermonde_ne_zero_iff.mpr hr)
  have hdiag : ∀ a b, vandermonde r *ᵥ toC (polyModMul Q a b) =
      (vandermonde r *ᵥ toC a) * (vandermonde r *ᵥ toC b) := by
    intro a b
    rcases Nat.eq_zero_or_pos n with hn | hn
    · subst hn
      funext j
      exact j.elim0
    refine (example17 Q hQ r hr hroot a b _).mp ?_
    have hpoly : polyOf (polyModMul Q a b) = (polyOf a * polyOf b) % Q := by
      have hlt : ((polyOf a * polyOf b) % Q).natDegree < n :=
        hQ ▸ natDegree_mod_lt _ (by omega)
      show ∑ k : Fin n, C (((polyOf a * polyOf b) % Q).coeff k) * X ^ (k : ℕ) = _
      rw [Fin.sum_univ_eq_sum_range (fun k => C (((polyOf a * polyOf b) % Q).coeff k) * X ^ k) n]
      simp only [C_mul_X_pow_eq_monomial]
      exact (as_sum_range' _ n hlt).symm
    rw [hpoly]
    have := EuclideanDomain.div_add_mod (polyOf a * polyOf b) Q
    exact ⟨-(polyOf a * polyOf b / Q), by linear_combination this⟩
  obtain ⟨h1, h2⟩ := s3b_tubal_of_diag _ hU _ hdiag
  exact ⟨⟨hU, (lemma2 _ hU).mp fun a b => ⟨_, h1 a b⟩⟩, h1, h2⟩

/-- `ω = e^{-2πi/n}`. -/
private def s3bOmega (n : ℕ) : ℂ := Complex.exp (-2 * Real.pi * I / n)

private lemma s3bOmega_prim (hn : n ≠ 0) : IsPrimitiveRoot (s3bOmega n) n := by
  have h := (Complex.isPrimitiveRoot_exp n hn).inv
  rw [← Complex.exp_neg] at h
  rw [s3bOmega]
  convert h using 2
  ring

private lemma s3b_dftMatrix_eq (j k : Fin n) :
    dftMatrix n j k = s3bOmega n ^ ((j : ℕ) * (k : ℕ)) := by
  rw [s3bOmega, ← Complex.exp_nat_mul, dftMatrix]
  congr 1
  push_cast
  ring

private lemma s3b_dftMatrix_eq_vandermonde :
    dftMatrix n = vandermonde (fun j : Fin n => s3bOmega n ^ (j : ℕ)) := by
  ext j k
  rw [s3b_dftMatrix_eq, vandermonde_apply, ← pow_mul]

private lemma s3b_omega_pow_inj : Function.Injective (fun j : Fin n => s3bOmega n ^ (j : ℕ)) := by
  intro i j h
  exact Fin.ext ((s3bOmega_prim (Fin.pos i).ne').pow_inj i.isLt j.isLt h)

/-- **Eq. (3)**: `P_c = P_a · P_b mod (Xⁿ - 1) ⟺ F_n c = F_n a • F_n b`
(the paper writes `X^p - 1`, a typo for `Xⁿ - 1`). -/
theorem eq3 (a b c : Fin n → ℝ) :
    (X ^ n - 1 : ℝ[X]) ∣ polyOf c - polyOf a * polyOf b ↔
      dftMatrix n *ᵥ toC c = (dftMatrix n *ᵥ toC a) * (dftMatrix n *ᵥ toC b) := by
  rw [s3b_dftMatrix_eq_vandermonde]
  refine example17 _ ?_ _ s3b_omega_pow_inj ?_ a b c
  · rw [← C_1, natDegree_X_pow_sub_C]
  · intro j
    have h2 : s3bOmega n ^ n = 1 := (s3bOmega_prim (Fin.pos j).ne').pow_eq_one
    simp only [Polynomial.map_sub, Polynomial.map_pow, map_X, Polynomial.map_one, IsRoot.def,
      eval_sub, eval_pow, eval_X, eval_one]
    rw [← pow_mul, mul_comm, pow_mul, h2, one_pow, sub_self]

/-- The skew-Fourier matrix `F_n diag(1, e^{πi/n}, e^{2πi/n}, …, e^{(n-1)πi/n})`. -/
def skewFourier (n : ℕ) : Matrix (Fin n) (Fin n) ℂ :=
  dftMatrix n * diagonal (fun k : Fin n => Complex.exp (Real.pi * I * (k : ℂ) / (n : ℂ)))

/-- **Example 17**: for `Q = Xⁿ + 1`, `M` (the Vandermonde matrix at the roots of `Q`) is the
skew-Fourier matrix. -/
theorem example17_skewFourier :
    ∃ r : Fin n → ℂ, Function.Injective r ∧ (∀ j, ((X ^ n + 1 : ℝ[X]).map (algebraMap ℝ ℂ)).IsRoot (r j)) ∧
      skewFourier n = vandermonde r := by
  set θ : ℂ := Complex.exp (Real.pi * I / n) with hθ
  refine ⟨fun j => θ * s3bOmega n ^ (j : ℕ), ?_, ?_, ?_⟩
  · intro i j h
    exact s3b_omega_pow_inj (mul_left_cancel₀ (Complex.exp_ne_zero _) h)
  · intro j
    have hn : n ≠ 0 := (Fin.pos j).ne'
    have h1 : θ ^ n = -1 := by
      rw [hθ, ← Complex.exp_nat_mul, show (n : ℂ) * (Real.pi * I / n) = Real.pi * I by
        field_simp, Complex.exp_pi_mul_I]
    have h2 : s3bOmega n ^ n = 1 := (s3bOmega_prim hn).pow_eq_one
    simp only [Polynomial.map_add, Polynomial.map_pow, map_X, Polynomial.map_one, IsRoot.def,
      eval_add, eval_pow, eval_X, eval_one]
    rw [mul_pow, ← pow_mul, mul_comm (j : ℕ) n, pow_mul, h1, h2, one_pow]
    ring
  · ext j k
    rw [skewFourier, Matrix.mul_diagonal, s3b_dftMatrix_eq, vandermonde_apply, mul_pow, ← pow_mul,
      hθ, ← Complex.exp_nat_mul, mul_comm]
    congr 2
    ring

/-- **Example 17**: when `n = 2`, `M` is the same matrix as in Example 4 … -/
theorem example17_two : skewFourier 2 = M4 := by
  have e1 : Complex.exp (-(2 * Real.pi * I) / 2) = -1 := by
    rw [show -(2 * (Real.pi : ℂ) * I) / 2 = -(Real.pi * I) by ring, Complex.exp_neg,
      Complex.exp_pi_mul_I]; norm_num
  have e2 : Complex.exp (Real.pi * I / 2) = I := by
    rw [show (Real.pi : ℂ) * I / 2 = (Real.pi / 2 : ℝ) * I by push_cast; ring,
      Complex.exp_mul_I]
    simp
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [skewFourier, dftMatrix, M4, Matrix.mul_diagonal, e1, e2]

/-- **Example 17**: … so the ring we obtain is isomorphic to `ℂ` and is a field. -/
theorem example17_field :
    haveI : Fact (Admissible (skewFourier 2)) := ⟨example17_two ▸ M4_admissible⟩
    IsField (KM (skewFourier 2)) ∧ Nonempty (KM (skewFourier 2) ≃+* ℂ) := by
  have : Fact (Admissible (skewFourier 2)) := ⟨example17_two ▸ M4_admissible⟩
  have hval : ∀ a : KM (skewFourier 2), a.hat 0 = (a.vec 0 : ℂ) + (a.vec 1 : ℂ) * I := by
    intro a
    simp [KM.hat, example17_two, M4, mulVec, dotProduct, Fin.sum_univ_two]
    ring
  let φ : KM (skewFourier 2) →+* ℂ :=
    { toFun := fun a => a.hat 0
      map_one' := by rw [KM.hat_one]; rfl
      map_mul' := fun a b => by rw [KM.hat_mul]; rfl
      map_zero' := by rw [KM.hat_zero]; rfl
      map_add' := fun a b => by rw [KM.hat_add]; rfl }
  have hφ : Function.Bijective φ := by
    constructor
    · intro a b h
      have h' : (a.vec 0 : ℂ) + (a.vec 1 : ℂ) * I = (b.vec 0 : ℂ) + (b.vec 1 : ℂ) * I := by
        rw [← hval, ← hval]; exact h
      have h0 := congrArg Complex.re h'
      have h1 := congrArg Complex.im h'
      simp at h0 h1
      ext i
      fin_cases i
      · exact h0
      · exact h1
    · intro z
      refine ⟨⟨![z.re, z.im]⟩, ?_⟩
      show KM.hat _ 0 = z
      rw [hval]
      simp [Complex.re_add_im]
  let e := RingEquiv.ofBijective φ hφ
  exact ⟨MulEquiv.isField (Field.toIsField ℂ) e.toMulEquiv, ⟨e⟩⟩

/-- **Example 17**: `ℂ` is isomorphic as a field to `ℝ[x]/(x² + 1)` ([7, Section 9.4,
Exercise 7]). -/
theorem example17_complex_quotient : Nonempty (ℂ ≃+* AdjoinRoot (X ^ 2 + 1 : ℝ[X])) := by
  have hmon : (X ^ 2 + 1 : ℝ[X]).Monic := by monicity!
  have hdeg : (X ^ 2 + 1 : ℝ[X]).natDegree = 2 := by compute_degree!
  let φ := AdjoinRoot.liftAlgHom (X ^ 2 + 1 : ℝ[X]) (Algebra.ofId ℝ ℂ) I (by simp)
  have := hmon.finite_adjoinRoot
  have hsurj : Function.Surjective φ := by
    intro z
    refine ⟨AdjoinRoot.of _ z.re + AdjoinRoot.of _ z.im * AdjoinRoot.root _, ?_⟩
    simp [φ]
  have hfr : Module.finrank ℝ (AdjoinRoot (X ^ 2 + 1 : ℝ[X])) = Module.finrank ℝ ℂ := by
    rw [(AdjoinRoot.powerBasis' hmon).finrank, AdjoinRoot.powerBasis'_dim, hdeg,
      Complex.finrank_real_complex]
  have hinj : Function.Injective φ :=
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank hfr (f := φ.toLinearMap)).mpr hsurj
  exact ⟨(RingEquiv.ofBijective φ ⟨hinj, hsurj⟩).symm⟩

/-! ### Example 18 (group rings) -/

/-- The convolution product of the group ring `ℝ[G]`: `(f · g)(x) = ∑_{u · v = x} f(u) g(v)`. -/
def groupConv {G : Type*} [CommGroup G] [Fintype G] [DecidableEq G] (f g : G → ℝ) : G → ℝ :=
  fun x => ∑ u, ∑ v, if u * v = x then f u * g v else 0

/-- A matrix whose rows are characters of `G` diagonalizes the group convolution. -/
private lemma s3b_groupConv_diag {G : Type*} [CommGroup G] [Fintype G] [DecidableEq G]
    (e : G ≃ Fin n) (M : Matrix (Fin n) (Fin n) ℂ)
    (hM : ∀ i u v, M i (e (u * v)) = M i (e u) * M i (e v)) (a b : Fin n → ℝ) :
    M *ᵥ toC (fun i => groupConv (a ∘ e) (b ∘ e) (e.symm i)) = (M *ᵥ toC a) * (M *ᵥ toC b) := by
  funext i
  show ∑ x, M i x * ((groupConv (a ∘ e) (b ∘ e) (e.symm x) : ℝ) : ℂ) =
    (∑ x, M i x * (a x : ℂ)) * (∑ x, M i x * (b x : ℂ))
  rw [← e.sum_comp, ← e.sum_comp (fun x => M i x * (a x : ℂ)),
    ← e.sum_comp (fun x => M i x * (b x : ℂ)), Finset.sum_mul_sum]
  simp only [Equiv.symm_apply_apply, groupConv, Function.comp_apply]
  simp only [Complex.ofReal_sum, apply_ite (fun r : ℝ => (r : ℂ)), Complex.ofReal_mul,
    Complex.ofReal_zero, Finset.mul_sum, mul_ite, mul_zero]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun u _ => ?_
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun v _ => ?_
  simp only [Finset.sum_ite_eq, Finset.mem_univ, ite_true, hM]
  ring

/-- **Example 18.** Let `G` be a finite abelian group of size `n`. The group ring `ℝ[G]`
(functions `G → ℝ` with point-wise addition and convolution as product) is a commutative von
Neumann regular ring; identifying each group element with an index in `{1, …, n}` makes it a
tubal ring. -/
theorem example18 {G : Type*} [CommGroup G] [Fintype G] [DecidableEq G] (e : G ≃ Fin n) :
    ∃ T : TubalRing n, ∀ a b : Fin n → ℝ,
      T.mul a b = fun i => groupConv (a ∘ e) (b ∘ e) (e.symm i) := by
  have hcard : Fintype.card (AddChar (Additive G) ℂ) = n := by
    rw [AddChar.card_eq]
    exact (Fintype.card_congr (Additive.ofMul.symm.trans e)).trans (Fintype.card_fin n)
  let φ : AddChar (Additive G) ℂ ≃ Fin n := Fintype.equivFinOfCardEq hcard
  let M : Matrix (Fin n) (Fin n) ℂ := fun i j => φ.symm i (Additive.ofMul (e.symm j))
  have hM : ∀ i u v, M i (e (u * v)) = M i (e u) * M i (e v) := by
    intro i u v
    simp only [M, Equiv.symm_apply_apply, ofMul_mul, AddChar.map_add_eq_mul]
  have hU : IsUnit M := by
    rw [← linearIndependent_rows_iff_isUnit]
    let e' : Fin n ≃ Additive G := e.symm.trans Additive.ofMul
    have := ((AddChar.linearIndependent (Additive G) ℂ).comp φ.symm φ.symm.injective).map'
      (LinearEquiv.funCongrLeft ℂ ℂ e').toLinearMap (LinearEquiv.ker _)
    convert this using 1
    funext i j
    simp [M, e', Matrix.row, LinearEquiv.funCongrLeft_apply]
  obtain ⟨-, T, hT⟩ := s3b_tubal_of_diag M hU _ (s3b_groupConv_diag e M hM)
  exact ⟨T, fun a b => by rw [hT]⟩

private lemma s3b_omega_pow_mod (hn : n ≠ 0) (i p q : ℕ) :
    s3bOmega n ^ (i * ((p + q) % n)) = s3bOmega n ^ (i * p) * s3bOmega n ^ (i * q) := by
  have h1 : s3bOmega n ^ n = 1 := (s3bOmega_prim hn).pow_eq_one
  rw [← pow_add, pow_eq_pow_mod _ h1, pow_eq_pow_mod (i * p + i * q) h1, Nat.mul_mod, Nat.mod_mod,
    ← Nat.mul_mod, mul_add]

/-- **Example 18**: the t-product is obtained by using the cyclic group `G = ℤ_n`. -/
theorem example18_tProduct [NeZero n] (a b : Fin n → ℝ) :
    toC (fun i => groupConv (G := Multiplicative (Fin n)) (a ∘ Multiplicative.toAdd)
        (b ∘ Multiplicative.toAdd) (Multiplicative.ofAdd i)) =
      starMC (dftMatrix n) (toC a) (toC b) := by
  have hM : ∀ i (u v : Multiplicative (Fin n)), dftMatrix n i (Multiplicative.toAdd (u * v)) =
      dftMatrix n i (Multiplicative.toAdd u) * dftMatrix n i (Multiplicative.toAdd v) := by
    intro i u v
    rw [s3b_dftMatrix_eq, s3b_dftMatrix_eq, s3b_dftMatrix_eq, toAdd_mul, Fin.val_add,
      s3b_omega_pow_mod (NeZero.ne n)]
  have := s3b_groupConv_diag Multiplicative.toAdd (dftMatrix n) hM a b
  rw [starMC, ← this, inv_mulVec_mulVec' (dftMatrix_admissible n).1]
  rfl

/-- The XOR-convolution on `ℝ^{2^k}` (vectors indexed by `0, …, 2^k - 1`):
`(a · b)_i = ∑_{j=0}^{n-1} a_j b_{i ⊕ j}`.

(The paper prints `a_i b_{i⊕j}`; this is a typo for `a_j b_{i⊕j}` — the printed formula is not
even commutative, see `example18_literal_not_comm`.) -/
def xorConv (k : ℕ) (a b : Fin (2 ^ k) → ℝ) : Fin (2 ^ k) → ℝ :=
  fun i => ∑ j : Fin (2 ^ k), a j * b ⟨(i : ℕ) ^^^ (j : ℕ), Nat.xor_lt_two_pow i.isLt j.isLt⟩

/-- The literally printed product `(a · b)_i = ∑_j a_i b_{i⊕j}`. -/
def xorConvLiteral (k : ℕ) (a b : Fin (2 ^ k) → ℝ) : Fin (2 ^ k) → ℝ :=
  fun i => ∑ j : Fin (2 ^ k), a i * b ⟨(i : ℕ) ^^^ (j : ℕ), Nat.xor_lt_two_pow i.isLt j.isLt⟩

theorem example18_literal_not_comm :
    ∃ a b : Fin (2 ^ 1) → ℝ, xorConvLiteral 1 a b ≠ xorConvLiteral 1 b a := by
  refine ⟨fun i => if (i : ℕ) = 0 then 1 else 0, fun _ => 1, fun h => ?_⟩
  have h0 := congrFun h ⟨0, by norm_num⟩
  simp only [xorConvLiteral] at h0
  rw [Fin.sum_univ_eq_sum_range (fun x => (1:ℝ) * if 0 ^^^ x = 0 then 1 else 0)] at h0
  simp at h0

/-- The (Sylvester) Walsh–Hadamard matrix `WHT_{ij} = (-1)^{∑_b i_b j_b}` (`i_b` the bits). -/
def walshHadamard (k : ℕ) : Matrix (Fin (2 ^ k)) (Fin (2 ^ k)) ℂ :=
  fun i j => ∏ b : Fin k, if (i : ℕ).testBit b && (j : ℕ).testBit b then -1 else 1

/-- Bitwise xor on `Fin (2 ^ k)`. -/
private def s3bXor {k : ℕ} (i j : Fin (2 ^ k)) : Fin (2 ^ k) :=
  ⟨(i : ℕ) ^^^ (j : ℕ), Nat.xor_lt_two_pow i.isLt j.isLt⟩

private lemma s3bXor_xor_cancel {k : ℕ} (i j : Fin (2 ^ k)) : s3bXor (s3bXor i j) j = i := by
  ext
  simp [s3bXor]

/-- `l ↦ l ⊕ j` as a permutation. -/
private def s3bXorPerm {k : ℕ} (j : Fin (2 ^ k)) : Equiv.Perm (Fin (2 ^ k)) :=
  Function.Involutive.toPerm (fun l => s3bXor l j) (fun l => s3bXor_xor_cancel l j)

private lemma s3b_wht_symm (k : ℕ) (i j : Fin (2 ^ k)) : walshHadamard k i j = walshHadamard k j i := by
  simp only [walshHadamard, Bool.and_comm]

private lemma s3b_wht_xor (k : ℕ) (i j l : Fin (2 ^ k)) :
    walshHadamard k i (s3bXor j l) = walshHadamard k i j * walshHadamard k i l := by
  simp only [walshHadamard, s3bXor, ← Finset.prod_mul_distrib, Nat.testBit_xor]
  refine Finset.prod_congr rfl fun b _ => ?_
  cases (i : ℕ).testBit b <;> cases (j : ℕ).testBit b <;> cases (l : ℕ).testBit b <;> simp

private lemma s3b_wht_sum (k : ℕ) (m : Fin (2 ^ k)) :
    ∑ j, walshHadamard k m j = if m = 0 then (2 ^ k : ℂ) else 0 := by
  split_ifs with hm
  · subst hm
    simp [walshHadamard]
  · have hm' : (m : ℕ) ≠ 0 := fun h => hm (Fin.ext h)
    obtain ⟨c, hc⟩ := Nat.exists_testBit_of_ne_zero hm'
    have hck : c < k := by
      by_contra h
      push Not at h
      have := Nat.testBit_lt_two_pow (lt_of_lt_of_le m.isLt (Nat.pow_le_pow_right (by norm_num) h))
      rw [this] at hc
      exact Bool.false_ne_true hc
    let t : Fin (2 ^ k) := ⟨2 ^ c, Nat.pow_lt_pow_right (by norm_num) hck⟩
    have ht : walshHadamard k m t = -1 := by
      simp only [walshHadamard, t]
      rw [Finset.prod_eq_single (⟨c, hck⟩ : Fin k)]
      · simp [hc, Nat.testBit_two_pow_self]
      · intro b _ hb
        have : c ≠ (b : ℕ) := fun h => hb (Fin.ext h.symm)
        simp [Nat.testBit_two_pow_of_ne this]
      · intro h; exact absurd (Finset.mem_univ _) h
    have hS := Equiv.sum_comp (s3bXorPerm t) (fun j => walshHadamard k m j)
    have hneg : ∀ j, walshHadamard k m (s3bXorPerm t j) = -walshHadamard k m j := fun j => by
      rw [show s3bXorPerm t j = s3bXor j t from rfl, s3b_wht_xor, ht, mul_neg_one]
    simp only [hneg, Finset.sum_neg_distrib] at hS
    linear_combination -hS / 2

private lemma s3b_wht_mul_self (k : ℕ) :
    walshHadamard k * walshHadamard k = (2 ^ k : ℂ) • (1 : Matrix _ _ ℂ) := by
  ext i l
  rw [Matrix.mul_apply, Matrix.smul_apply, Matrix.one_apply]
  have : ∀ j, walshHadamard k i j * walshHadamard k j l = walshHadamard k j (s3bXor i l) := by
    intro j
    rw [s3b_wht_xor, s3b_wht_symm k i j]
  simp_rw [this]
  rw [Finset.sum_congr rfl fun j _ => s3b_wht_symm k j (s3bXor i l), s3b_wht_sum]
  have : s3bXor i l = 0 ↔ i = l := by
    constructor
    · intro h
      have := s3bXor_xor_cancel i l
      rw [h] at this
      ext
      rw [← this]
      simp [s3bXor]
    · rintro rfl
      ext
      simp [s3bXor]
  by_cases h : i = l
  · rw [this.mpr h]
    simp [h]
  · have h0 : ¬ s3bXor i l = 0 := mt this.mp h
    simp [h0, h]

/-- **Example 18**: the XOR-convolution `(a · b)_i = ∑_j a_j b_{i⊕j}` (convolution over the
group `ℤ₂^k`) diagonalizes under the Walsh–Hadamard transform: it is a tubal ring with
`M = WHT`. -/
theorem example18_xor (k : ℕ) :
    IsUnit (walshHadamard k) ∧
    (∀ a b : Fin (2 ^ k) → ℝ, toC (xorConv k a b) = starMC (walshHadamard k) (toC a) (toC b)) ∧
    ∃ T : TubalRing (2 ^ k), T.mul = xorConv k := by
  have hU : IsUnit (walshHadamard k) := by
    rw [Matrix.isUnit_iff_isUnit_det]
    refine Matrix.isUnit_det_of_right_inverse (B := ((2 ^ k : ℂ)⁻¹) • walshHadamard k) ?_
    rw [Matrix.mul_smul, s3b_wht_mul_self, smul_smul, inv_mul_cancel₀ (by norm_num), one_smul]
  have hdiag : ∀ a b, walshHadamard k *ᵥ toC (xorConv k a b) =
      (walshHadamard k *ᵥ toC a) * (walshHadamard k *ᵥ toC b) := by
    intro a b
    funext i
    simp only [mulVec, dotProduct, toC_apply, Pi.mul_apply, xorConv, Complex.ofReal_sum,
      Complex.ofReal_mul, Finset.mul_sum, Finset.sum_mul]
    rw [Finset.sum_comm]
    conv_rhs => rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [← Equiv.sum_comp (s3bXorPerm j)]
    refine Finset.sum_congr rfl fun m _ => ?_
    have h2 : (s3bXorPerm j m) = s3bXor m j := rfl
    have h1 : (⟨((s3bXor m j : Fin (2 ^ k)) : ℕ) ^^^ (j : ℕ),
        Nat.xor_lt_two_pow (s3bXor m j).isLt j.isLt⟩ : Fin (2 ^ k)) = m :=
      s3bXor_xor_cancel m j
    rw [h2, h1, s3b_wht_xor]
    ring
  exact ⟨hU, s3b_tubal_of_diag _ hU _ hdiag⟩

end Tubal
