import TubalAlgebra.Realness

/-!
# The ring of tubes `𝕂_M` (Theorem 3, Proposition 6, Lemma 8)

For an admissible `M` (invertible, every row real or conjugate to exactly one other row)
we endow `KM M` (i.e. `ℝⁿ`) with the structure of a commutative ring (Theorem 3), of an
associative `ℝ`-algebra, and of a `*`-ring (Proposition 6). The weak inverse `a⁻` is the
Moore–Penrose-like inverse of Lemma 8.

All structure is obtained by transport along the injective map `a ↦ â = M a ∈ ℂⁿ`, which turns
`⋆_M` into the Hadamard product.
-/

open Matrix Complex

noncomputable section

namespace Tubal

variable {n : ℕ}

namespace KM

variable {M : Matrix (Fin n) (Fin n) ℂ}

/-! ### Linear behaviour of the transform (no hypothesis on `M`) -/

@[simp] lemma _root_.Tubal.toC_zero : toC (0 : Fin n → ℝ) = 0 := by
  funext i; simp [toC]

@[simp] lemma _root_.Tubal.toC_add (a b : Fin n → ℝ) : toC (a + b) = toC a + toC b := by
  funext i; simp [toC]

@[simp] lemma _root_.Tubal.toC_neg (a : Fin n → ℝ) : toC (-a) = -toC a := by
  funext i; simp [toC]

@[simp] lemma _root_.Tubal.toC_sub (a b : Fin n → ℝ) : toC (a - b) = toC a - toC b := by
  funext i; simp [toC]

@[simp] lemma _root_.Tubal.toC_smul (r : ℝ) (a : Fin n → ℝ) : toC (r • a) = (r : ℂ) • toC a := by
  funext i; simp [toC]

@[simp] lemma _root_.Tubal.toC_nsmul (k : ℕ) (a : Fin n → ℝ) : toC (k • a) = k • toC a := by
  funext i; simp [toC]

@[simp] lemma _root_.Tubal.toC_zsmul (k : ℤ) (a : Fin n → ℝ) : toC (k • a) = k • toC a := by
  funext i; simp [toC]

/-- If a complex vector is real, then it is the embedding of its real part. -/
lemma _root_.Tubal.toC_re_of_mem_range {v : Fin n → ℂ} (hv : v ∈ Set.range toC) :
    toC (fun i => (v i).re) = v := by
  obtain ⟨c, rfl⟩ := hv
  funext i; simp [toC]

@[simp] theorem hat_zero : (0 : KM M).hat = 0 := by
  simp [hat]

@[simp] theorem hat_add (a b : KM M) : (a + b).hat = a.hat + b.hat := by
  simp [hat, mulVec_add]

@[simp] theorem hat_neg (a : KM M) : (-a).hat = -a.hat := by
  simp [hat, mulVec_neg]

@[simp] theorem hat_sub (a b : KM M) : (a - b).hat = a.hat - b.hat := by
  simp [hat, mulVec_sub]

@[simp] theorem hat_nsmul (k : ℕ) (a : KM M) : (k • a).hat = k • a.hat := by
  rw [hat, hat, vec_nsmul, toC_nsmul, mulVec_smul]

@[simp] theorem hat_zsmul (k : ℤ) (a : KM M) : (k • a).hat = k • a.hat := by
  rw [hat, hat, vec_zsmul, toC_zsmul, mulVec_smul]

@[simp] theorem hat_smul (r : ℝ) (a : KM M) : (r • a).hat = (r : ℂ) • a.hat := by
  simp [hat, mulVec_smul]

/-- The transform as an additive map. -/
def hatAddHom : KM M →+ (Fin n → ℂ) where
  toFun := KM.hat
  map_zero' := hat_zero
  map_add' := hat_add

@[simp] theorem hat_sum {ι : Type*} (s : Finset ι) (f : ι → KM M) :
    (∑ i ∈ s, f i).hat = ∑ i ∈ s, (f i).hat :=
  map_sum hatAddHom f s

theorem hat_conjPattern (a : KM M) : ConjPattern M a.hat :=
  conjPattern_mulVec_toC M a.vec

/-! ### Under admissibility -/

section Admissible

variable [hM : Fact (Admissible M)]

theorem hat_injective : Function.Injective (KM.hat : KM M → Fin n → ℂ) := by
  intro a b h
  exact KM.ext (toC_injective (mulVec_injective_of_isUnit hM.out.1 h))

/-- Every vector respecting the conjugation pattern is the transform of a tube. -/
theorem exists_hat_eq {y : Fin n → ℂ} (hy : ConjPattern M y) : ∃ a : KM M, a.hat = y := by
  obtain ⟨a, rfl⟩ := (conjPattern_iff_mem_range M hM.out.1 hM.out.2 y).mp hy
  exact ⟨⟨a⟩, rfl⟩

/-- The product of `KM M` is exactly `⋆_M` (Eq. (5)). -/
theorem toC_vec_mul (a b : KM M) : toC (a * b).vec = starMC M (toC a.vec) (toC b.vec) := by
  exact toC_re_of_mem_range ((lemma65 M hM.out.1).mpr hM.out.2 a.vec b.vec)

theorem toC_vec_one : toC (1 : KM M).vec = M⁻¹ *ᵥ (1 : Fin n → ℂ) := by
  exact toC_re_of_mem_range (inv_mulVec_mem_range_of_conjPattern M hM.out.1 hM.out.2
    (ConjPattern.one M))

/-- The conjugate of `KM M` is exactly Eq. (6). -/
theorem toC_vec_star (a : KM M) : toC (star a).vec = M⁻¹ *ᵥ star (M *ᵥ toC a.vec) := by
  exact toC_re_of_mem_range (inv_mulVec_mem_range_of_conjPattern M hM.out.1 hM.out.2
    (conjPattern_mulVec_toC M a.vec).star)

/-- The weak inverse is exactly Eq. (7). -/
theorem toC_vec_weakInv (a : KM M) :
    toC (weakInv a).vec = M⁻¹ *ᵥ pinvVec (M *ᵥ toC a.vec) := by
  exact toC_re_of_mem_range (lemma7 M hM.out.1 hM.out.2 a.vec)

@[simp] theorem hat_mul (a b : KM M) : (a * b).hat = a.hat * b.hat := by
  rw [hat, toC_vec_mul, starMC, mulVec_inv_mulVec' hM.out.1]
  rfl

@[simp] theorem hat_one : (1 : KM M).hat = 1 := by
  rw [hat, toC_vec_one, mulVec_inv_mulVec' hM.out.1]

@[simp] theorem hat_star (a : KM M) : (star a).hat = star a.hat := by
  rw [hat, toC_vec_star, mulVec_inv_mulVec' hM.out.1]
  rfl

@[simp] theorem hat_weakInv (a : KM M) : (weakInv a).hat = pinvVec a.hat := by
  rw [hat, toC_vec_weakInv, mulVec_inv_mulVec' hM.out.1]
  rfl

theorem hat_natCast (k : ℕ) : ((k : KM M)).hat = (k : Fin n → ℂ) := by
  change (k • (1 : KM M)).hat = _
  rw [hat_nsmul, hat_one]
  funext i
  simp

theorem hat_intCast (k : ℤ) : ((k : KM M)).hat = (k : Fin n → ℂ) := by
  change (k • (1 : KM M)).hat = _
  rw [hat_zsmul, hat_one]
  funext i
  simp

theorem hat_pow (a : KM M) (k : ℕ) : (a ^ k).hat = a.hat ^ k := by
  induction k with
  | zero => exact hat_one
  | succ k ih =>
    change (npowRec k a * a).hat = _
    rw [hat_mul, pow_succ]
    change (a ^ k).hat * a.hat = _
    rw [ih]

/-- The commutative ring `𝕂_M` (Theorem 3). -/
instance instCommRing : CommRing (KM M) :=
  hat_injective.commRing KM.hat hat_zero hat_one hat_add hat_mul hat_neg hat_sub
    hat_nsmul hat_zsmul hat_pow hat_natCast hat_intCast

theorem smul_mul_assoc' (r : ℝ) (a b : KM M) : r • a * b = r • (a * b) := by
  apply hat_injective
  rw [hat_mul, hat_smul, hat_smul, hat_mul, smul_mul_assoc]

theorem mul_smul_comm' (r : ℝ) (a b : KM M) : a * r • b = r • (a * b) := by
  apply hat_injective
  rw [hat_mul, hat_smul, hat_smul, hat_mul, mul_smul_comm]

/-- `𝕂_M` is an associative algebra over `ℝ` with respect to the usual scalar-vector product. -/
instance instAlgebra : Algebra ℝ (KM M) := Algebra.ofModule smul_mul_assoc' mul_smul_comm'

theorem star_star' (a : KM M) : star (star a) = a := by
  apply hat_injective
  rw [hat_star, hat_star, star_star]

theorem star_add' (a b : KM M) : star (a + b) = star a + star b := by
  apply hat_injective
  rw [hat_star, hat_add, hat_add, hat_star, hat_star, star_add]

theorem star_mul' (a b : KM M) : star (a * b) = star b * star a := by
  apply hat_injective
  rw [hat_star, hat_mul, hat_mul, hat_star, hat_star, star_mul, mul_comm]

/-- `𝕂_M` is a `*`-ring with the `⋆_M`-conjugate (Proposition 6). -/
instance instStarRing : StarRing (KM M) where
  star_involutive := star_star'
  star_mul := star_mul'
  star_add := star_add'

end Admissible

end KM

/-! ### Theorem 3 -/

/-- **Theorem 3** (Proposition 4.2 in [14]). Let `M ∈ ℂ^{n×n}` be an invertible matrix in which
every row is either real, or is conjugate to exactly one other row of `M`. The set `ℝⁿ` equipped
with the binary composition `⋆_M` defined in Eq. (5) and the usual vector addition `+` is a
commutative ring with a unit. -/
theorem theorem3 (M : Matrix (Fin n) (Fin n) ℂ) (hM : IsUnit M) (hrow : ConjRowCondition M) :
    ∃ R : CommRing (Fin n → ℝ),
      (∀ a b : Fin n → ℝ, R.add a b = a + b) ∧
      (∀ a b : Fin n → ℝ, toC (R.mul a b) = starMC M (toC a) (toC b)) := by
  have : Fact (Admissible M) := ⟨⟨hM, hrow⟩⟩
  refine ⟨(KM.equivVec (M := M)).symm.commRing, fun a b => rfl, fun a b => ?_⟩
  exact KM.toC_vec_mul (KM.mk a) (KM.mk b)

/-- **Theorem 3**, phrased on the type `KM M` (`= 𝕂_M`): its addition is the usual vector
addition and its product is `⋆_M`. -/
theorem theorem3_KM (M : Matrix (Fin n) (Fin n) ℂ) [Fact (Admissible M)] :
    (∀ a b : KM M, (a + b).vec = a.vec + b.vec) ∧
    (∀ a b : KM M, toC (a * b).vec = starMC M (toC a.vec) (toC b.vec)) ∧
    toC (1 : KM M).vec = M⁻¹ *ᵥ (1 : Fin n → ℂ) :=
  ⟨fun _ _ => rfl, KM.toC_vec_mul, KM.toC_vec_one⟩

/-! ### Proposition 6 -/

/-- **Proposition 6.** `𝕂_M` is a `*`-ring with respect to the `⋆_M`-conjugate operation:
the involutive, additive, anti-multiplicative and unit-preserving axioms hold. -/
theorem prop6 (M : Matrix (Fin n) (Fin n) ℂ) [Fact (Admissible M)] :
    (∀ a : KM M, star (star a) = a) ∧
    (∀ a b : KM M, star (a + b) = star a + star b) ∧
    (∀ a b : KM M, star (a * b) = star b * star a) ∧
    star (1 : KM M) = 1 := by
  refine ⟨KM.star_star', KM.star_add', KM.star_mul', ?_⟩
  apply KM.hat_injective
  rw [KM.hat_star, KM.hat_one, star_one]

/-! ### The partial order `≤_M` -/

/-- "It is easy to verify that this is a partial order." -/
theorem le_isPartialOrder (M : Matrix (Fin n) (Fin n) ℂ) [Fact (Admissible M)] :
    (∀ a : KM M, a ≤ a) ∧ (∀ a b c : KM M, a ≤ b → b ≤ c → a ≤ c) ∧
    (∀ a b : KM M, a ≤ b → b ≤ a → a = b) := by
  refine ⟨fun a j => ?_, fun a b c hab hbc j => ?_, fun a b hab hba => ?_⟩
  · simp
  · have e : (c - a).hat = (c - b).hat + (b - a).hat := by
      rw [← KM.hat_add]; congr 1; abel
    rw [e]
    simp only [Pi.add_apply, Complex.add_im, Complex.add_re]
    exact ⟨by rw [(hbc j).1, (hab j).1]; simp, add_nonneg (hbc j).2 (hab j).2⟩
  · have hz : (b - a).hat = 0 := by
      funext j
      have e : (a - b).hat j = -((b - a).hat j) := by
        rw [← neg_sub, KM.hat_neg]; rfl
      have h1 := hab j
      have h2 := hba j
      rw [e] at h2
      simp only [Complex.neg_re, Complex.neg_im] at h2
      apply Complex.ext
      · simp only [Pi.zero_apply, Complex.zero_re]; linarith [h1.2, h2.2]
      · simpa using h1.1
    have : b - a = 0 := KM.hat_injective (by rw [hz, KM.hat_zero])
    exact (sub_eq_zero.mp this).symm

/-! ### Lemma 8 -/

/-- **Lemma 8.** For all `a ∈ 𝕂_M`, `a⁻ ∈ 𝕂_M` is the unique element of `𝕂_M` for which the
following four properties hold: `a ⋆ a⁻ ⋆ a = a`, `a⁻ ⋆ a ⋆ a⁻ = a⁻`, `(a ⋆ a⁻)* = a ⋆ a⁻`,
`(a⁻ ⋆ a)* = a⁻ ⋆ a`. -/
theorem lemma8 (M : Matrix (Fin n) (Fin n) ℂ) [Fact (Admissible M)] (a : KM M) :
    (a * KM.weakInv a * a = a ∧ KM.weakInv a * a * KM.weakInv a = KM.weakInv a ∧
      star (a * KM.weakInv a) = a * KM.weakInv a ∧
      star (KM.weakInv a * a) = KM.weakInv a * a) ∧
    ∀ y : KM M, (a * y * a = a ∧ y * a * y = y ∧ star (a * y) = a * y ∧ star (y * a) = y * a) →
      y = KM.weakInv a := by
  have key1 : ∀ z : ℂ, z * (if z = 0 then 0 else z⁻¹) * z = z := by
    intro z; split_ifs with h
    · simp [h]
    · field_simp
  have key2 : ∀ z : ℂ, (if z = 0 then 0 else z⁻¹) * z * (if z = 0 then 0 else z⁻¹) =
      (if z = 0 then 0 else z⁻¹) := by
    intro z; split_ifs with h
    · simp
    · field_simp
  have key3 : ∀ z : ℂ, starRingEnd ℂ (z * (if z = 0 then 0 else z⁻¹)) =
      z * (if z = 0 then 0 else z⁻¹) := by
    intro z; split_ifs with h
    · simp
    · rw [mul_inv_cancel₀ h, map_one]
  refine ⟨⟨?_, ?_, ?_, ?_⟩, ?_⟩
  · apply KM.hat_injective
    funext j
    simp only [KM.hat_mul, KM.hat_weakInv, Pi.mul_apply, pinvVec]
    exact key1 _
  · apply KM.hat_injective
    funext j
    simp only [KM.hat_mul, KM.hat_weakInv, Pi.mul_apply, pinvVec]
    exact key2 _
  · apply KM.hat_injective
    funext j
    simp only [KM.hat_star, KM.hat_mul, KM.hat_weakInv, Pi.mul_apply, Pi.star_apply, pinvVec]
    exact key3 _
  · apply KM.hat_injective
    funext j
    simp only [KM.hat_star, KM.hat_mul, KM.hat_weakInv, Pi.mul_apply, Pi.star_apply, pinvVec]
    rw [mul_comm]
    exact key3 _
  · rintro y ⟨h1, h2, -, -⟩
    apply KM.hat_injective
    funext j
    have e1 := congrFun (congrArg KM.hat h1) j
    have e2 := congrFun (congrArg KM.hat h2) j
    simp only [KM.hat_mul, Pi.mul_apply] at e1 e2
    simp only [KM.hat_weakInv, pinvVec]
    split_ifs with h
    · rw [h] at e2; simpa using e2.symm
    · have : y.hat j * a.hat j = 1 := by
        have := e1
        field_simp at this
        rw [mul_comm]; exact this
      field_simp
      exact this

/-- `𝕂_M` is von Neumann regular (Definition 9; "the first property makes the ring a von
Neumann regular ring"). -/
theorem KM.isVonNeumannRegularRing (M : Matrix (Fin n) (Fin n) ℂ) [Fact (Admissible M)] :
    IsVonNeumannRegularRing (KM M) := by
  intro a
  exact ⟨KM.weakInv a, ((lemma8 M a).1.1).symm⟩

/-- "If `a` has a multiplicative inverse, then `a⁻` is that inverse." -/
theorem KM.weakInv_eq_inverse (M : Matrix (Fin n) (Fin n) ℂ) [Fact (Admissible M)]
    (a b : KM M) (hab : a * b = 1) : KM.weakInv a = b := by
  apply KM.hat_injective
  funext j
  have e := congrFun (congrArg KM.hat hab) j
  simp only [KM.hat_mul, KM.hat_one, Pi.mul_apply, Pi.one_apply] at e
  have ha : a.hat j ≠ 0 := left_ne_zero_of_mul_eq_one e
  simp only [KM.hat_weakInv, pinvVec, ha, ite_false]
  exact (eq_inv_of_mul_eq_one_right e).symm

/-- `dim_ℝ 𝕂_M = n`. -/
theorem KM.finrank_eq (M : Matrix (Fin n) (Fin n) ℂ) : Module.finrank ℝ (KM M) = n := by
  rw [LinearEquiv.finrank_eq (KM.linearEquivVec (M := M)), Module.finrank_fin_fun]

end Tubal
