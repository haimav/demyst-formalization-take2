import TubalAlgebra.TubalRing

/-!
# Examples of Section 3 (Examples 4, 14, 15, 16, 17, 18) and Eq. (3)

We use the DFT matrix `F_n` with entries `(F_n)_{jk} = ω^{jk}`, `ω = e^{-2πi/n}`.
-/

open Matrix Complex Polynomial

noncomputable section

namespace Tubal

variable {n : ℕ}

/-! ### Commutative unital algebra structures on `ℝⁿ` -/

/-- A commutative ring over `ℝⁿ` (with the usual vector addition), which is unital and an
associative algebra over `ℝ` with respect to the usual scalar-vector product. This is a tubal
ring (Definition 10) without the von Neumann regularity requirement. -/
structure CommAlgOn (n : ℕ) where
  /-- The product. -/
  mul : (Fin n → ℝ) → (Fin n → ℝ) → (Fin n → ℝ)
  mul_assoc : ∀ a b c, mul (mul a b) c = mul a (mul b c)
  left_distrib : ∀ a b c, mul a (b + c) = mul a b + mul a c
  right_distrib : ∀ a b c, mul (a + b) c = mul a c + mul b c
  mul_comm : ∀ a b, mul a b = mul b a
  exists_one : ∃ e, ∀ a, mul e a = a ∧ mul a e = a
  smul_mul : ∀ (r : ℝ) a b, mul (r • a) b = r • mul a b
  mul_smul : ∀ (r : ℝ) a b, mul a (r • b) = r • mul a b

/-- The product of complex numbers on `ℝ²`: `(a, b)·(c, d) = (ac - bd, ad + bc)`. -/
def complexMul (x y : Fin 2 → ℝ) : Fin 2 → ℝ :=
  ![x 0 * y 0 - x 1 * y 1, x 0 * y 1 + x 1 * y 0]

/-- The product of split-complex numbers on `ℝ²`: `(a, b)·(c, d) = (ac + bd, ad + bc)`. -/
def splitMul (x y : Fin 2 → ℝ) : Fin 2 → ℝ :=
  ![x 0 * y 0 + x 1 * y 1, x 0 * y 1 + x 1 * y 0]

/-- The product of dual numbers on `ℝ²`: `(a, b)·(c, d) = (ac, ad + bc)`. -/
def dualMul (x y : Fin 2 → ℝ) : Fin 2 → ℝ :=
  ![x 0 * y 0, x 0 * y 1 + x 1 * y 0]

/-! ### Example 4 -/

/-- The matrix `M = [[1, i], [1, -i]]` of Example 4. -/
def M4 : Matrix (Fin 2) (Fin 2) ℂ := !![1, I; 1, -I]

/-- The inverse of `M4`: `M4⁻¹ = ½ [[1, 1], [-i, i]]`. -/
private lemma M4_inv : M4⁻¹ = !![1 / 2, 1 / 2; -I / 2, I / 2] := by
  apply Matrix.inv_eq_left_inv
  ext i j
  fin_cases i <;> fin_cases j <;> simp [M4, Matrix.mul_apply, Fin.sum_univ_two] <;> ring_nf <;>
    simp [Complex.I_sq]

/-- **Example 4** (Complex numbers as a tubal ring). The multiplication of complex numbers on
`ℝ² ≅ ℂ`, `[a, b]·[c, d] = [ac - bd, ad + bc]`, is `⋆_M` with `M = [[1, i], [1, -i]]`. -/
theorem example4 (x y : Fin 2 → ℝ) : toC (complexMul x y) = starMC M4 (toC x) (toC y) := by
  rw [starMC, M4_inv]
  funext i
  fin_cases i <;> simp [complexMul, M4, mulVec, dotProduct, Fin.sum_univ_two] <;> ring_nf <;>
    simp [Complex.I_sq] <;> ring

theorem M4_admissible : Admissible M4 := by
  refine ⟨?_, ?_⟩
  · rw [Matrix.isUnit_iff_isUnit_det]
    simp only [M4, Matrix.det_fin_two_of]
    rw [show (1 : ℂ) * -I - I * 1 = -2 * I by ring]
    simp
  · intro i
    right
    fin_cases i
    · refine ⟨1, ⟨by decide, fun k => ?_⟩, fun j ⟨hj, _⟩ => ?_⟩
      · fin_cases k <;> simp [M4]
      · fin_cases j
        · exact absurd rfl hj
        · rfl
    · refine ⟨0, ⟨by decide, fun k => ?_⟩, fun j ⟨hj, _⟩ => ?_⟩
      · fin_cases k <;> simp [M4]
      · fin_cases j
        · rfl
        · exact absurd rfl hj

/-- **Example 4**: "we can use the multiplication defined by complex numbers to get a field":
`𝕂_M` for this `M` is a field. -/
theorem example4_isField : haveI : Fact (Admissible M4) := ⟨M4_admissible⟩; IsField (KM M4) := by
  have : Fact (Admissible M4) := ⟨M4_admissible⟩
  -- `â = (a₀ + i a₁, a₀ - i a₁)`
  have hhat : ∀ a : KM M4,
      a.hat = ![(a.vec 0 : ℂ) + I * a.vec 1, (a.vec 0 : ℂ) - I * a.vec 1] := by
    intro a
    funext i
    fin_cases i <;> simp [KM.hat, M4, mulVec, dotProduct, Fin.sum_univ_two] <;> ring
  -- for `a ≠ 0` all entries of `â` are non-zero
  have hne : ∀ a : KM M4, a ≠ 0 → ∀ j, a.hat j ≠ 0 := by
    intro a ha j hj
    apply ha
    have key : a.vec 0 = 0 ∧ a.vec 1 = 0 := by
      rw [hhat] at hj
      fin_cases j
      · have := Complex.ext_iff.mp hj
        simp at this
        exact this
      · have := Complex.ext_iff.mp hj
        simp at this
        exact ⟨this.1, this.2⟩
    apply KM.ext
    funext i
    fin_cases i
    · exact key.1
    · exact key.2
  -- the weak inverse of a non-zero element is its inverse
  refine ⟨⟨0, 1, fun h => ?_⟩, mul_comm, fun {a} ha => ⟨KM.weakInv a, ?_⟩⟩
  · have := congrFun (congrArg KM.hat h) 0
    simp at this
  · apply KM.hat_injective
    rw [KM.hat_mul, KM.hat_weakInv, KM.hat_one]
    funext j
    simp [pinvVec, hne a ha j]

/-- The complex product has no zero divisors. -/
private lemma complexMul_eq_zero {x y : Fin 2 → ℝ} (h : complexMul x y = 0) :
    x = 0 ∨ y = 0 := by
  have h0 : x 0 * y 0 - x 1 * y 1 = 0 := by simpa [complexMul] using congrFun h 0
  have h1 : x 0 * y 1 + x 1 * y 0 = 0 := by simpa [complexMul] using congrFun h 1
  by_cases hx : x 0 ^ 2 + x 1 ^ 2 = 0
  · left
    have a0 : x 0 = 0 := by nlinarith [sq_nonneg (x 0), sq_nonneg (x 1)]
    have a1 : x 1 = 0 := by nlinarith [sq_nonneg (x 0), sq_nonneg (x 1)]
    funext i; fin_cases i <;> simp [a0, a1]
  · right
    have e0 : (x 0 ^ 2 + x 1 ^ 2) * y 0 = 0 := by linear_combination x 0 * h0 + x 1 * h1
    have e1 : (x 0 ^ 2 + x 1 ^ 2) * y 1 = 0 := by linear_combination x 0 * h1 - x 1 * h0
    have b0 := (mul_eq_zero.mp e0).resolve_left hx
    have b1 := (mul_eq_zero.mp e1).resolve_left hx
    funext i; fin_cases i <;> simp [b0, b1]

private lemma map_ofReal_mulVec_toC (M : Matrix (Fin n) (Fin n) ℝ) (v : Fin n → ℝ) :
    M.map (↑) *ᵥ toC v = toC (M *ᵥ v) := by
  funext i
  simp [mulVec, dotProduct, toC]

/-- **Example 4**: "The use of complex numbers in `M` for building a `⋆_M` which corresponds to
complex product is unavoidable. It can be shown that no such real `M` exists." -/
theorem example4_no_real_M :
    ¬ ∃ M : Matrix (Fin 2) (Fin 2) ℝ, IsUnit M ∧
      ∀ x y : Fin 2 → ℝ, toC (complexMul x y) = starMC (M.map (↑)) (toC x) (toC y) := by
  rintro ⟨M, hM, h⟩
  have hdet : IsUnit M.det := (Matrix.isUnit_iff_isUnit_det M).mp hM
  have hMM : ∀ v, M *ᵥ (M⁻¹ *ᵥ v) = v := fun v => by
    rw [mulVec_mulVec, Matrix.mul_nonsing_inv _ hdet, one_mulVec]
  -- `x = M⁻¹ e₀`, `y = M⁻¹ e₁` are real and non-zero, but `x ⋆_M y = M⁻¹ (e₀ • e₁) = 0`
  set x := M⁻¹ *ᵥ Pi.single 0 1 with hx
  set y := M⁻¹ *ᵥ Pi.single 1 1 with hy
  have hxy : complexMul x y = 0 := by
    apply toC_injective
    rw [h, starMC, map_ofReal_mulVec_toC, map_ofReal_mulVec_toC, hx, hy, hMM, hMM, toC_zero]
    have : toC (Pi.single 0 1 : Fin 2 → ℝ) * toC (Pi.single 1 1) = 0 := by
      funext i; fin_cases i <;> simp
    rw [this, mulVec_zero]
  rcases complexMul_eq_zero hxy with h0 | h0
  · have := hMM (Pi.single 0 1)
    rw [← hx, h0, mulVec_zero] at this
    have := congrFun this 0
    simp at this
  · have := hMM (Pi.single 1 1)
    rw [← hy, h0, mulVec_zero] at this
    have := congrFun this 1
    simp at this

/-- The complex numbers as a tubal ring on `ℝ²`. -/
def complexTubal : TubalRing 2 where
  mul := complexMul
  mul_assoc := by
    intro a b c; funext i; fin_cases i <;> simp [complexMul] <;> ring
  left_distrib := by
    intro a b c; funext i; fin_cases i <;> simp [complexMul] <;> ring
  right_distrib := by
    intro a b c; funext i; fin_cases i <;> simp [complexMul] <;> ring
  mul_comm := by
    intro a b; funext i; fin_cases i <;> simp [complexMul] <;> ring
  exists_one := by
    refine ⟨![1, 0], fun a => ⟨?_, ?_⟩⟩ <;> funext i <;> fin_cases i <;> simp [complexMul]
  vonNeumann := by
    intro a
    by_cases h : a 0 ^ 2 + a 1 ^ 2 = 0
    · refine ⟨0, ?_⟩
      have h0 : a 0 = 0 := by nlinarith [sq_nonneg (a 0), sq_nonneg (a 1)]
      have h1 : a 1 = 0 := by nlinarith [sq_nonneg (a 0), sq_nonneg (a 1)]
      funext i; fin_cases i <;> simp [complexMul, h0, h1]
    · refine ⟨![a 0 / (a 0 ^ 2 + a 1 ^ 2), -a 1 / (a 0 ^ 2 + a 1 ^ 2)], ?_⟩
      funext i; fin_cases i <;> simp [complexMul] <;> field_simp <;> ring
  smul_mul := by
    intro r a b; funext i; fin_cases i <;> simp [complexMul] <;> ring
  mul_smul := by
    intro r a b; funext i; fin_cases i <;> simp [complexMul] <;> ring

/-! ### Example 14 (split-complex numbers) -/

/-- Given a unit `u` and an element `z` with `z² = κ u` such that `{u, z}` is linearly
independent, the coordinates w.r.t. `{u, z}` give a linear isomorphism onto `ℝ²` which turns the
product into `(a, b)·(c, d) = (ac + κ bd, ad + bc)`. -/
private lemma classify_aux (R : CommAlgOn 2) (u z : Fin 2 → ℝ) (κ : ℝ)
    (hu : ∀ a, R.mul u a = a) (hz : R.mul z z = κ • u)
    (hind : ∀ p q : ℝ, p • u + q • z = 0 → p = 0 ∧ q = 0) :
    ∃ e : (Fin 2 → ℝ) ≃ₗ[ℝ] (Fin 2 → ℝ), ∀ x y,
      e (R.mul x y) = ![e x 0 * e y 0 + κ * (e x 1 * e y 1), e x 0 * e y 1 + e x 1 * e y 0] := by
  let Φ : (Fin 2 → ℝ) →ₗ[ℝ] (Fin 2 → ℝ) :=
    { toFun := fun c => c 0 • u + c 1 • z
      map_add' := fun c d => by simp only [Pi.add_apply, add_smul]; abel
      map_smul' := fun r c => by
        simp only [Pi.smul_apply, smul_eq_mul, mul_smul, RingHom.id_apply, smul_add] }
  have hΦ : ∀ c, Φ c = c 0 • u + c 1 • z := fun c => rfl
  have hinj : Function.Injective Φ := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro c hc
    rw [hΦ] at hc
    obtain ⟨h0, h1⟩ := hind _ _ hc
    funext i; fin_cases i
    · exact h0
    · exact h1
  have hbij : Function.Bijective Φ := ⟨hinj, LinearMap.injective_iff_surjective.mp hinj⟩
  let E := LinearEquiv.ofBijective Φ hbij
  have hmul : ∀ c d, R.mul (Φ c) (Φ d) =
      Φ ![c 0 * d 0 + κ * (c 1 * d 1), c 0 * d 1 + c 1 * d 0] := by
    intro c d
    have hzu : R.mul z u = z := by rw [R.mul_comm]; exact hu z
    simp only [hΦ, R.left_distrib, R.right_distrib, R.smul_mul, R.mul_smul, hu, hzu, hz,
      Matrix.cons_val_zero, Matrix.cons_val_one]
    module
  refine ⟨E.symm, fun x y => ?_⟩
  apply E.injective
  rw [LinearEquiv.apply_symm_apply]
  have hE : ∀ w, Φ (E.symm w) = w := fun w => LinearEquiv.apply_ofBijective_symm_apply Φ w
  calc R.mul x y = R.mul (Φ (E.symm x)) (Φ (E.symm y)) := by rw [hE, hE]
    _ = Φ _ := hmul _ _
    _ = E _ := rfl

/-- **Example 14** (first claim, [30]): up to isomorphism, every commutative ring over `ℝ²`
(commutative unital `ℝ`-algebra structure on `ℝ²`) is isomorphic to one of three possible
rings: complex numbers, split-complex numbers and dual numbers. -/
theorem example14_classification (R : CommAlgOn 2) :
    ∃ e : (Fin 2 → ℝ) ≃ₗ[ℝ] (Fin 2 → ℝ),
      (∀ x y, e (R.mul x y) = complexMul (e x) (e y)) ∨
      (∀ x y, e (R.mul x y) = splitMul (e x) (e y)) ∨
      (∀ x y, e (R.mul x y) = dualMul (e x) (e y)) := by
  obtain ⟨u, hu⟩ := R.exists_one
  have hu' : ∀ a, R.mul u a = a := fun a => (hu a).1
  -- the unit `u` is non-zero
  have hD : u 0 ^ 2 + u 1 ^ 2 ≠ 0 := by
    intro hD
    have a0 : u 0 = 0 := by nlinarith [sq_nonneg (u 0), sq_nonneg (u 1)]
    have a1 : u 1 = 0 := by nlinarith [sq_nonneg (u 0), sq_nonneg (u 1)]
    have hu0 : u = (0 : ℝ) • u := by funext i; fin_cases i <;> simp [a0, a1]
    have h := hu' ![1, 0]
    rw [hu0, R.smul_mul, zero_smul] at h
    have := congrFun h 0
    simp at this
  set D := u 0 ^ 2 + u 1 ^ 2 with hDdef
  -- `v ∉ span {u}`, so `{u, v}` is a basis
  set v : Fin 2 → ℝ := ![-u 1, u 0] with hv
  have hind : ∀ p q : ℝ, p • u + q • v = 0 → p = 0 ∧ q = 0 := by
    intro p q h
    have h0 : p * u 0 - q * u 1 = 0 := by simpa [hv, sub_eq_add_neg] using congrFun h 0
    have h1 : p * u 1 + q * u 0 = 0 := by simpa [hv] using congrFun h 1
    have e0 : p * D = 0 := by rw [hDdef]; linear_combination u 0 * h0 + u 1 * h1
    have e1 : q * D = 0 := by rw [hDdef]; linear_combination u 0 * h1 - u 1 * h0
    exact ⟨(mul_eq_zero.mp e0).resolve_right hD, (mul_eq_zero.mp e1).resolve_right hD⟩
  -- `v² = α u + β v`
  set w := R.mul v v with hw
  set α := (w 0 * u 0 + w 1 * u 1) / D with hα
  set β := (u 0 * w 1 - u 1 * w 0) / D with hβ
  have hvv : R.mul v v = α • u + β • v := by
    rw [← hw]
    funext i; fin_cases i <;> simp [hv, hα, hβ] <;> field_simp <;> ring
  -- completing the square: `y = v - (β/2) u` has `y² = γ u`
  set y := v + (-(β / 2)) • u with hy
  set γ := α + β ^ 2 / 4 with hγ
  have hyy : R.mul y y = γ • u := by
    have huv : R.mul v u = v := by rw [R.mul_comm]; exact hu' v
    simp only [hy, R.left_distrib, R.right_distrib, R.smul_mul, R.mul_smul, hu', huv, hvv]
    module
  -- rescaling `y`
  have key : ∀ s : ℝ, s ≠ 0 → R.mul (s • y) (s • y) = (s ^ 2 * γ) • u ∧
      ∀ p q : ℝ, p • u + q • (s • y) = 0 → p = 0 ∧ q = 0 := by
    intro s hs
    refine ⟨?_, fun p q h => ?_⟩
    · rw [R.smul_mul, R.mul_smul, hyy, smul_smul, smul_smul]; ring_nf
    · have h' : (p - q * s * (β / 2)) • u + (q * s) • v = 0 := by
        rw [← h, hy]; module
      obtain ⟨h1, h2⟩ := hind _ _ h'
      have hq : q = 0 := by
        rcases mul_eq_zero.mp h2 with h | h
        · exact h
        · exact absurd h hs
      refine ⟨?_, hq⟩
      rw [hq] at h1; simpa using h1
  rcases lt_trichotomy γ 0 with hγn | hγ0 | hγp
  · -- `γ < 0`: complex numbers
    have hs : (1 / Real.sqrt (-γ)) ≠ 0 := by
      have := Real.sqrt_pos.mpr (neg_pos.mpr hγn); positivity
    obtain ⟨hzz, hzi⟩ := key _ hs
    have hκ : (1 / Real.sqrt (-γ)) ^ 2 * γ = -1 := by
      have := hγn.ne
      rw [div_pow, Real.sq_sqrt (by linarith)]; field_simp
    rw [hκ] at hzz
    obtain ⟨e, he⟩ := classify_aux R u _ (-1) hu' hzz hzi
    refine ⟨e, Or.inl fun x y => ?_⟩
    rw [he]; funext i; fin_cases i <;> simp [complexMul] <;> ring
  · -- `γ = 0`: dual numbers
    obtain ⟨hzz, hzi⟩ := key 1 one_ne_zero
    rw [hγ0, mul_zero] at hzz
    obtain ⟨e, he⟩ := classify_aux R u _ 0 hu' hzz hzi
    refine ⟨e, Or.inr (Or.inr fun x y => ?_)⟩
    rw [he]; funext i; fin_cases i <;> simp [dualMul]
  · -- `γ > 0`: split-complex numbers
    have hs : (1 / Real.sqrt γ) ≠ 0 := by
      have := Real.sqrt_pos.mpr hγp; positivity
    obtain ⟨hzz, hzi⟩ := key _ hs
    have hκ : (1 / Real.sqrt γ) ^ 2 * γ = 1 := by
      rw [div_pow, Real.sq_sqrt hγp.le]; field_simp
    rw [hκ] at hzz
    obtain ⟨e, he⟩ := classify_aux R u _ 1 hu' hzz hzi
    refine ⟨e, Or.inr (Or.inl fun x y => ?_)⟩
    rw [he]; funext i; fin_cases i <;> simp [splitMul]

/-- **Example 14**: the split-complex product defines a commutative ring over `ℝ²`. -/
def splitCommAlg : CommAlgOn 2 where
  mul := splitMul
  mul_assoc := by
    intro a b c; funext i; fin_cases i <;> simp [splitMul] <;> ring
  left_distrib := by
    intro a b c; funext i; fin_cases i <;> simp [splitMul] <;> ring
  right_distrib := by
    intro a b c; funext i; fin_cases i <;> simp [splitMul] <;> ring
  mul_comm := by
    intro a b; funext i; fin_cases i <;> simp [splitMul] <;> ring
  exists_one := by
    refine ⟨![1, 0], fun a => ⟨?_, ?_⟩⟩ <;> funext i <;> fin_cases i <;> simp [splitMul]
  smul_mul := by
    intro r a b; funext i; fin_cases i <;> simp [splitMul] <;> ring
  mul_smul := by
    intro r a b; funext i; fin_cases i <;> simp [splitMul] <;> ring

/-- **Example 14**: weak inverses for non-zero elements are given by
`[a, b]⁻ = [a/(a²-b²), -b/(a²-b²)]` (for `a² ≠ b²`), `[a, a]⁻ = [1/(4a), 1/(4a)]`,
`[a, -a]⁻ = [1/(4a), -1/(4a)]` (here a weak inverse `y` of `x` is the unique element with
`x = x·y·x` and `y = y·x·y`). -/
theorem example14_weakInv :
    (∀ a b : ℝ, a ^ 2 ≠ b ^ 2 →
      let x := ![a, b]; let y := ![a / (a ^ 2 - b ^ 2), -b / (a ^ 2 - b ^ 2)]
      splitMul (splitMul x y) x = x ∧ splitMul (splitMul y x) y = y) ∧
    (∀ a : ℝ, a ≠ 0 →
      let x := ![a, a]; let y := ![1 / (4 * a), 1 / (4 * a)]
      splitMul (splitMul x y) x = x ∧ splitMul (splitMul y x) y = y) ∧
    (∀ a : ℝ, a ≠ 0 →
      let x := ![a, -a]; let y := ![1 / (4 * a), -1 / (4 * a)]
      splitMul (splitMul x y) x = x ∧ splitMul (splitMul y x) y = y) := by
  refine ⟨fun a b h => ?_, fun a h => ?_, fun a h => ?_⟩
  · have h' : a ^ 2 - b ^ 2 ≠ 0 := sub_ne_zero.mpr h
    constructor <;> funext i <;> fin_cases i <;> simp [splitMul] <;> field_simp <;> ring
  · constructor <;> funext i <;> fin_cases i <;> simp [splitMul] <;> field_simp <;> ring
  · constructor <;> funext i <;> fin_cases i <;> simp [splitMul] <;> field_simp <;> ring

/-- **Example 14**: "So, this is a tubal ring." -/
def splitTubal : TubalRing 2 where
  mul := splitMul
  mul_assoc := splitCommAlg.mul_assoc
  left_distrib := splitCommAlg.left_distrib
  right_distrib := splitCommAlg.right_distrib
  mul_comm := splitCommAlg.mul_comm
  exists_one := splitCommAlg.exists_one
  vonNeumann := by
    intro a
    by_cases h0 : a = 0
    · refine ⟨0, ?_⟩
      subst h0; funext i; fin_cases i <;> simp [splitMul]
    by_cases h : a 0 ^ 2 = a 1 ^ 2
    · have hne : a 0 ≠ 0 := by
        intro h'
        rw [h', eq_comm] at h
        apply h0; funext i; fin_cases i
        · exact h'
        · simpa using h
      rcases sq_eq_sq_iff_eq_or_eq_neg.mp h with h' | h'
      · -- `a = [c, c]`
        refine ⟨![1 / (4 * a 0), 1 / (4 * a 0)], ?_⟩
        funext i; fin_cases i <;> simp [splitMul, ← h'] <;> field_simp <;> ring
      · -- `a = [c, -c]`
        refine ⟨![1 / (4 * a 0), -1 / (4 * a 0)], ?_⟩
        funext i; fin_cases i <;> simp [splitMul, h'] <;> field_simp <;> ring
    · have h' : a 0 ^ 2 - a 1 ^ 2 ≠ 0 := sub_ne_zero.mpr h
      refine ⟨![a 0 / (a 0 ^ 2 - a 1 ^ 2), -a 1 / (a 0 ^ 2 - a 1 ^ 2)], ?_⟩
      funext i; fin_cases i <;> simp [splitMul] <;> field_simp <;> ring
  smul_mul := splitCommAlg.smul_mul
  mul_smul := splitCommAlg.mul_smul

/-- The `2 × 2` Hadamard matrix `[[1, 1], [1, -1]]`. -/
def hadamard2 : Matrix (Fin 2) (Fin 2) ℂ := !![1, 1; 1, -1]

/-- `hadamard2⁻¹ = ½ hadamard2`. -/
private lemma hadamard2_inv : hadamard2⁻¹ = !![1 / 2, 1 / 2; 1 / 2, -1 / 2] := by
  apply Matrix.inv_eq_left_inv
  ext i j
  fin_cases i <;> fin_cases j <;> simp [hadamard2, Matrix.mul_apply, Fin.sum_univ_two] <;> norm_num

/-- **Example 14**: the split-complex product is `⋆_M` with `M = [[1, 1], [1, -1]]`. -/
theorem example14 (x y : Fin 2 → ℝ) : toC (splitMul x y) = starMC hadamard2 (toC x) (toC y) := by
  rw [starMC, hadamard2_inv]
  funext i
  fin_cases i <;> simp [splitMul, hadamard2, mulVec, dotProduct, Fin.sum_univ_two] <;> ring

/-- The DFT matrix `F_n`, `(F_n)_{jk} = e^{-2πi jk/n}`. -/
def dftMatrix (n : ℕ) : Matrix (Fin n) (Fin n) ℂ :=
  fun j k => Complex.exp (-2 * Real.pi * I * (j : ℂ) * (k : ℂ) / (n : ℂ))

/-- **Example 14**: `[[1, 1], [1, -1]]` coincides with the unscaled DFT matrix for `n = 2`;
hence the split-complex product is the t-product for `n = 2`. -/
theorem example14_dft : dftMatrix 2 = hadamard2 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [dftMatrix, hadamard2]
  rw [show -(2 * ↑Real.pi * I) / 2 = -(Real.pi * I) by ring, Complex.exp_neg,
    Complex.exp_pi_mul_I]
  norm_num

/-! ### Example 15 (dual numbers) -/

/-- **Example 15**: the dual number product defines a commutative ring over `ℝ²`. -/
def dualCommAlg : CommAlgOn 2 where
  mul := dualMul
  mul_assoc := by
    intro a b c; funext i; fin_cases i <;> simp [dualMul] <;> ring
  left_distrib := by
    intro a b c; funext i; fin_cases i <;> simp [dualMul] <;> ring
  right_distrib := by
    intro a b c; funext i; fin_cases i <;> simp [dualMul] <;> ring
  mul_comm := by
    intro a b; funext i; fin_cases i <;> simp [dualMul] <;> ring
  exists_one := by
    refine ⟨![1, 0], fun a => ⟨?_, ?_⟩⟩ <;> funext i <;> fin_cases i <;> simp [dualMul]
  smul_mul := by
    intro r a b; funext i; fin_cases i <;> simp [dualMul] <;> ring
  mul_smul := by
    intro r a b; funext i; fin_cases i <;> simp [dualMul] <;> ring

/-- **Example 15**: for any dual number `x + yε`, `ε · (x + yε) · ε = 0`, so `ε` does not have
a weak inverse. -/
theorem example15_eps (x : Fin 2 → ℝ) : dualMul (dualMul ![0, 1] x) ![0, 1] = 0 := by
  funext i; fin_cases i <;> simp [dualMul]

/-- **Example 15**: the dual numbers are *not* a tubal ring. -/
theorem example15_not_tubal : ¬ ∃ T : TubalRing 2, T.mul = dualMul := by
  rintro ⟨T, hT⟩
  obtain ⟨x, hx⟩ := T.vonNeumann ![0, 1]
  rw [hT, example15_eps] at hx
  have := congrFun hx 1
  simp at this

/-- **Example 15**: "Indeed, no invertible `M` exists that makes dual numbers isomorphic to
`ℝ²`", i.e. the dual product is not `⋆_M` for any invertible `M`. -/
theorem example15_no_M :
    ¬ ∃ M : Matrix (Fin 2) (Fin 2) ℂ, IsUnit M ∧
      ∀ x y : Fin 2 → ℝ, toC (dualMul x y) = starMC M (toC x) (toC y) := by
  rintro ⟨M, hM, h⟩
  have h1 := h ![0, 1] ![0, 1]
  have h0 : dualMul ![0, 1] ![0, 1] = 0 := by funext i; fin_cases i <;> simp [dualMul]
  rw [h0, toC_zero, starMC] at h1
  -- `(M ε) • (M ε) = M (ε ⋆ ε) = 0`
  have h2 : (M *ᵥ toC ![0, 1]) * (M *ᵥ toC ![0, 1]) = 0 := by
    have := congrArg (M *ᵥ ·) h1
    simp only [mulVec_inv_mulVec' hM, mulVec_zero] at this
    exact this.symm
  have h3 : M *ᵥ toC ![0, 1] = 0 := by
    funext i
    have := congrFun h2 i
    simpa using this
  have h4 : toC (![0, 1] : Fin 2 → ℝ) = 0 :=
    mulVec_injective_of_isUnit hM (by show M *ᵥ _ = M *ᵥ _; rw [h3, mulVec_zero])
  have := congrFun h4 1
  simp at this

/-- **Example 15** (in the sense of ring isomorphism): the ring of dual numbers is not
isomorphic (as a ring) to any `𝕂_M`. -/
theorem example15_not_iso (M : Matrix (Fin 2) (Fin 2) ℂ) [Fact (Admissible M)] :
    IsEmpty (DualNumber ℝ ≃+* KM M) := by
  refine ⟨fun f => ?_⟩
  -- `ε² = 0`, while `𝕂_M` is reduced
  have h1 : f DualNumber.eps * f DualNumber.eps = 0 := by
    rw [← map_mul, DualNumber.eps_mul_eps, map_zero]
  have h2 : (f DualNumber.eps).hat = 0 := by
    have := congrArg KM.hat h1
    rw [KM.hat_mul, KM.hat_zero] at this
    funext i
    have := congrFun this i
    simpa using this
  have h3 : f DualNumber.eps = 0 := KM.hat_injective (by rw [h2, KM.hat_zero])
  have h4 : (DualNumber.eps : DualNumber ℝ) = 0 := by
    rw [← map_zero f] at h3; exact f.injective h3
  have := congrArg TrivSqZeroExt.snd h4
  simp [DualNumber.snd_eps] at this

/-! ### Example 16 (t-product via circulant matrices) -/

/-- The circulant matrix whose first column is `x`: `circ(x)_{ij} = x_{(i - j) mod n}`. -/
def circ (x : Fin n → ℝ) : Matrix (Fin n) (Fin n) ℝ := fun i j => x (i - j)

/-- The t-product `x ⋆_t y := F_n⁻¹ (F_n x • F_n y)` (real part; it is real). -/
def tProd (x y : Fin n → ℝ) : Fin n → ℝ := fun i => (starMC (dftMatrix n) (toC x) (toC y) i).re

/-- The root of unity `ω = e^{-2πi/n}`. -/
private def dftRoot (n : ℕ) : ℂ := Complex.exp (-2 * Real.pi * I / (n : ℂ))

private lemma dftMatrix_eq_pow (j k : Fin n) :
    dftMatrix n j k = dftRoot n ^ ((j : ℕ) * (k : ℕ)) := by
  rw [dftRoot, ← Complex.exp_nat_mul, dftMatrix]
  congr 1
  push_cast
  ring

private lemma dftRoot_isPrimitiveRoot (hn : n ≠ 0) : IsPrimitiveRoot (dftRoot n) n := by
  have h := (Complex.isPrimitiveRoot_exp n hn).inv
  rw [← Complex.exp_neg] at h
  have e : dftRoot n = Complex.exp (-(2 * Real.pi * I / n)) := by rw [dftRoot]; congr 1; ring
  rw [e]; exact h

private lemma dftRoot_pow_self : dftRoot n ^ n = 1 := by
  rw [dftRoot, ← Complex.exp_nat_mul]
  rcases Nat.eq_zero_or_pos n with h | h
  · subst h; simp
  · have : (n : ℂ) ≠ 0 := by exact_mod_cast h.ne'
    rw [show (n : ℂ) * (-2 * Real.pi * I / n) = -(2 * Real.pi * I) by field_simp]
    rw [Complex.exp_neg, Complex.exp_two_pi_mul_I, inv_one]

private lemma pow_eq_pow_mod {ζ : ℂ} (hζ : ζ ^ n = 1) (m : ℕ) : ζ ^ m = ζ ^ (m % n) := by
  conv_lhs => rw [← Nat.div_add_mod m n, pow_add, pow_mul, hζ, one_pow, one_mul]

private lemma conj_dftRoot : starRingEnd ℂ (dftRoot n) = (dftRoot n)⁻¹ := by
  rw [dftRoot, ← Complex.exp_conj, ← Complex.exp_neg]
  congr 1
  simp [map_div₀, show (starRingEnd ℂ) 2 = 2 from map_ofNat _ 2]
  ring

/-- `F_n` has the left inverse `(1/n) conj(F_n)` (orthogonality of the characters). -/
private lemma dft_left_inv :
    ((n : ℂ)⁻¹ • (dftMatrix n).map (starRingEnd ℂ)) * dftMatrix n = 1 := by
  ext j l
  have hn : n ≠ 0 := (Fin.pos j).ne'
  have hn' : (n : ℂ) ≠ 0 := by exact_mod_cast hn
  have hω := dftRoot_isPrimitiveRoot hn
  rw [Matrix.mul_apply]
  simp only [Matrix.smul_apply, Matrix.map_apply, dftMatrix_eq_pow, map_pow, conj_dftRoot,
    smul_eq_mul]
  set ζ := (dftRoot n)⁻¹ ^ (j : ℕ) * dftRoot n ^ (l : ℕ) with hζ
  have hterm : ∀ k : Fin n, (n : ℂ)⁻¹ * (dftRoot n)⁻¹ ^ ((j : ℕ) * (k : ℕ)) *
      dftRoot n ^ ((k : ℕ) * (l : ℕ)) = (n : ℂ)⁻¹ * ζ ^ (k : ℕ) := by
    intro k
    rw [hζ, mul_pow, ← pow_mul, ← pow_mul, mul_assoc, mul_comm (l : ℕ) (k : ℕ),
      mul_comm (j : ℕ) (k : ℕ)]
  rw [Finset.sum_congr rfl (fun k _ => hterm k), ← Finset.mul_sum,
    Fin.sum_univ_eq_sum_range (fun k => ζ ^ k) n]
  by_cases hjl : j = l
  · subst hjl
    have : ζ = 1 := by rw [hζ, inv_pow, inv_mul_cancel₀ (pow_ne_zero _ (hω.ne_zero hn))]
    rw [this]
    simp [hn']
  · have hζ1 : ζ ≠ 1 := by
      intro h1
      apply hjl
      have : dftRoot n ^ (l : ℕ) = dftRoot n ^ (j : ℕ) := by
        rw [hζ, inv_pow, inv_mul_eq_one₀ (pow_ne_zero _ (hω.ne_zero hn))] at h1
        exact h1.symm
      exact Fin.ext (hω.pow_inj j.isLt l.isLt this.symm)
    have hζn : ζ ^ n = 1 := by
      rw [hζ, mul_pow, ← pow_mul, ← pow_mul, mul_comm (j : ℕ) n, mul_comm (l : ℕ) n, pow_mul,
        pow_mul, inv_pow, dftRoot_pow_self, inv_one, one_pow, one_pow, one_mul]
    rw [geom_sum_eq hζ1, hζn, sub_self, zero_div, mul_zero]
    simp [hjl]

private lemma dftMatrix_isUnit : IsUnit (dftMatrix n) :=
  (Matrix.isUnit_iff_isUnit_det _).mpr (Matrix.isUnit_det_of_left_inverse dft_left_inv)

theorem dftMatrix_admissible (n : ℕ) : Admissible (dftMatrix n) := by
  refine ⟨dftMatrix_isUnit, fun i => ?_⟩
  have hn : 0 < n := Fin.pos i
  -- row `i` is the conjugate of row `(n - i) mod n`
  set i' : Fin n := ⟨(n - i) % n, Nat.mod_lt _ hn⟩ with hi'
  have hdvd : n ∣ (i : ℕ) + (i' : ℕ) := by
    rw [Nat.dvd_iff_mod_eq_zero, hi', Nat.add_mod_mod, Nat.add_sub_cancel' i.isLt.le,
      Nat.mod_self]
  have hconj : RowConjOf (dftMatrix n) i i' := by
    intro k
    rw [dftMatrix_eq_pow, dftMatrix_eq_pow, map_pow, conj_dftRoot, inv_pow]
    obtain ⟨q, hq⟩ := hdvd
    have h1 : dftRoot n ^ ((i : ℕ) * (k : ℕ)) * dftRoot n ^ ((i' : ℕ) * (k : ℕ)) = 1 := by
      rw [← pow_add, ← add_mul, hq, mul_assoc, pow_mul, dftRoot_pow_self, one_pow]
    exact eq_inv_of_mul_eq_one_left h1
  by_cases h : i' = i
  · left
    rw [h] at hconj
    exact rowReal_of_rowConjOf_self hconj
  · right
    exact ⟨i', ⟨h, hconj⟩, fun j hj => rowConjOf_unique' dftMatrix_isUnit hj.2 hconj⟩

/-- The cyclic convolution `(x ∗ y)_i = ∑_k x_{i-k} y_k`. -/
private def cconv (x y : Fin n → ℝ) : Fin n → ℝ := fun i => ∑ k, x (i - k) * y k

private lemma circ_mul_circ (x y : Fin n → ℝ) : circ x * circ y = circ (cconv x y) := by
  ext i j
  have : NeZero n := ⟨(Fin.pos i).ne'⟩
  simp only [circ, cconv, Matrix.mul_apply]
  symm
  refine Fintype.sum_equiv (Equiv.addRight j) _ _ fun l => ?_
  simp only [Equiv.coe_addRight, add_sub_cancel_right]
  congr 2
  abel

private lemma cconv_comm (x y : Fin n → ℝ) : cconv x y = cconv y x := by
  funext i
  have : NeZero n := ⟨(Fin.pos i).ne'⟩
  simp only [cconv]
  refine Fintype.sum_equiv (Equiv.subLeft i) _ _ fun k => ?_
  simp only [Equiv.subLeft_apply, sub_sub_cancel]
  ring

private lemma circ_single [NeZero n] : circ (Pi.single 0 1 : Fin n → ℝ) = 1 := by
  ext i j
  simp [circ, Matrix.one_apply, Pi.single_apply, sub_eq_zero]

private lemma exists_circ_eq_one : ∃ z : Fin n → ℝ, circ z = 1 := by
  rcases Nat.eq_zero_or_pos n with h | h
  · subst h
    exact ⟨0, Subsingleton.elim _ _⟩
  · have : NeZero n := ⟨h.ne'⟩
    exact ⟨_, circ_single⟩

private lemma dftMatrix_add (j a b : Fin n) :
    dftMatrix n j (a + b) = dftMatrix n j a * dftMatrix n j b := by
  have hj : (dftRoot n ^ (j : ℕ)) ^ n = 1 := by
    rw [← pow_mul, mul_comm, pow_mul, dftRoot_pow_self, one_pow]
  rw [dftMatrix_eq_pow, dftMatrix_eq_pow, dftMatrix_eq_pow, pow_mul, pow_mul, pow_mul,
    Fin.val_add, ← pow_eq_pow_mod hj, pow_add]

/-- The DFT turns cyclic convolution into the Hadamard product. -/
private lemma dft_cconv (x y : Fin n → ℝ) :
    dftMatrix n *ᵥ toC (cconv x y) = (dftMatrix n *ᵥ toC x) * (dftMatrix n *ᵥ toC y) := by
  funext j
  have : NeZero n := ⟨(Fin.pos j).ne'⟩
  simp only [mulVec, dotProduct, toC_apply, cconv, Pi.mul_apply, Complex.ofReal_sum,
    Complex.ofReal_mul, Finset.mul_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun b _ => ?_
  symm
  refine Fintype.sum_equiv (Equiv.addRight b) _ _ fun a => ?_
  simp only [Equiv.coe_addRight, add_sub_cancel_right, dftMatrix_add]
  ring

private lemma starMC_dft (x y : Fin n → ℝ) :
    starMC (dftMatrix n) (toC x) (toC y) = toC (cconv x y) := by
  rw [starMC, ← dft_cconv, inv_mulVec_mulVec' dftMatrix_isUnit]

private lemma tProd_eq (x y : Fin n → ℝ) : tProd x y = cconv x y := by
  funext i
  simp [tProd, starMC_dft]

/-- **Example 16**: the sum of circulant matrices is circulant, the product of circulant
matrices is also circulant, any two circulant matrices commute, and the identity matrix is a
circulant matrix. -/
theorem example16_circ_algebra :
    (∀ x y : Fin n → ℝ, circ x + circ y = circ (x + y)) ∧
    (∀ x y : Fin n → ℝ, ∃ z, circ x * circ y = circ z) ∧
    (∀ x y : Fin n → ℝ, circ x * circ y = circ y * circ x) ∧
    (∃ z : Fin n → ℝ, circ z = 1) := by
  refine ⟨fun x y => ?_, fun x y => ⟨_, circ_mul_circ x y⟩, fun x y => ?_, exists_circ_eq_one⟩
  · ext i j; simp [circ]
  · rw [circ_mul_circ, circ_mul_circ, cconv_comm]

/-- **Example 16**: `x ⋆_t y` is real and `circ(x ⋆_t y) = circ(x) · circ(y)`; i.e. the ring
obtained by identifying `x` with `circ(x)` is exactly the t-product (`⋆_M` with `M = F_n`). -/
theorem example16 (x y : Fin n → ℝ) :
    starMC (dftMatrix n) (toC x) (toC y) = toC (tProd x y) ∧
    circ (tProd x y) = circ x * circ y := by
  rw [tProd_eq, circ_mul_circ]
  exact ⟨starMC_dft x y, rfl⟩

end Tubal
