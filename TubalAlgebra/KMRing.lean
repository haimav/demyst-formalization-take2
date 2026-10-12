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

@[simp] theorem hat_zero : (0 : KM M).hat = 0 := by
  sorry

@[simp] theorem hat_add (a b : KM M) : (a + b).hat = a.hat + b.hat := by
  sorry

@[simp] theorem hat_neg (a : KM M) : (-a).hat = -a.hat := by
  sorry

@[simp] theorem hat_sub (a b : KM M) : (a - b).hat = a.hat - b.hat := by
  sorry

@[simp] theorem hat_nsmul (k : ℕ) (a : KM M) : (k • a).hat = k • a.hat := by
  sorry

@[simp] theorem hat_zsmul (k : ℤ) (a : KM M) : (k • a).hat = k • a.hat := by
  sorry

@[simp] theorem hat_smul (r : ℝ) (a : KM M) : (r • a).hat = (r : ℂ) • a.hat := by
  sorry

theorem hat_conjPattern (a : KM M) : ConjPattern M a.hat :=
  conjPattern_mulVec_toC M a.vec

/-! ### Under admissibility -/

section Admissible

variable [hM : Fact (Admissible M)]

theorem hat_injective : Function.Injective (KM.hat : KM M → Fin n → ℂ) := by
  sorry

/-- Every vector respecting the conjugation pattern is the transform of a tube. -/
theorem exists_hat_eq {y : Fin n → ℂ} (hy : ConjPattern M y) : ∃ a : KM M, a.hat = y := by
  sorry

/-- The product of `KM M` is exactly `⋆_M` (Eq. (5)). -/
theorem toC_vec_mul (a b : KM M) : toC (a * b).vec = starMC M (toC a.vec) (toC b.vec) := by
  sorry

theorem toC_vec_one : toC (1 : KM M).vec = M⁻¹ *ᵥ (1 : Fin n → ℂ) := by
  sorry

/-- The conjugate of `KM M` is exactly Eq. (6). -/
theorem toC_vec_star (a : KM M) : toC (star a).vec = M⁻¹ *ᵥ star (M *ᵥ toC a.vec) := by
  sorry

/-- The weak inverse is exactly Eq. (7). -/
theorem toC_vec_weakInv (a : KM M) :
    toC (weakInv a).vec = M⁻¹ *ᵥ pinvVec (M *ᵥ toC a.vec) := by
  sorry

@[simp] theorem hat_mul (a b : KM M) : (a * b).hat = a.hat * b.hat := by
  sorry

@[simp] theorem hat_one : (1 : KM M).hat = 1 := by
  sorry

@[simp] theorem hat_star (a : KM M) : (star a).hat = star a.hat := by
  sorry

@[simp] theorem hat_weakInv (a : KM M) : (weakInv a).hat = pinvVec a.hat := by
  sorry

theorem hat_natCast (k : ℕ) : ((k : KM M)).hat = (k : Fin n → ℂ) := by
  sorry

theorem hat_intCast (k : ℤ) : ((k : KM M)).hat = (k : Fin n → ℂ) := by
  sorry

theorem hat_pow (a : KM M) (k : ℕ) : (a ^ k).hat = a.hat ^ k := by
  sorry

/-- The commutative ring `𝕂_M` (Theorem 3). -/
instance instCommRing : CommRing (KM M) :=
  hat_injective.commRing KM.hat hat_zero hat_one hat_add hat_mul hat_neg hat_sub
    hat_nsmul hat_zsmul hat_pow hat_natCast hat_intCast

theorem smul_mul_assoc' (r : ℝ) (a b : KM M) : r • a * b = r • (a * b) := by
  sorry

theorem mul_smul_comm' (r : ℝ) (a b : KM M) : a * r • b = r • (a * b) := by
  sorry

/-- `𝕂_M` is an associative algebra over `ℝ` with respect to the usual scalar-vector product. -/
instance instAlgebra : Algebra ℝ (KM M) := Algebra.ofModule smul_mul_assoc' mul_smul_comm'

theorem star_star' (a : KM M) : star (star a) = a := by
  sorry

theorem star_add' (a b : KM M) : star (a + b) = star a + star b := by
  sorry

theorem star_mul' (a b : KM M) : star (a * b) = star b * star a := by
  sorry

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
  sorry

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
  sorry

/-! ### The partial order `≤_M` -/

/-- "It is easy to verify that this is a partial order." -/
theorem le_isPartialOrder (M : Matrix (Fin n) (Fin n) ℂ) [Fact (Admissible M)] :
    (∀ a : KM M, a ≤ a) ∧ (∀ a b c : KM M, a ≤ b → b ≤ c → a ≤ c) ∧
    (∀ a b : KM M, a ≤ b → b ≤ a → a = b) := by
  sorry

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
  sorry

/-- `𝕂_M` is von Neumann regular (Definition 9; "the first property makes the ring a von
Neumann regular ring"). -/
theorem KM.isVonNeumannRegularRing (M : Matrix (Fin n) (Fin n) ℂ) [Fact (Admissible M)] :
    IsVonNeumannRegularRing (KM M) := by
  sorry

/-- "If `a` has a multiplicative inverse, then `a⁻` is that inverse." -/
theorem KM.weakInv_eq_inverse (M : Matrix (Fin n) (Fin n) ℂ) [Fact (Admissible M)]
    (a b : KM M) (hab : a * b = 1) : KM.weakInv a = b := by
  sorry

/-- `dim_ℝ 𝕂_M = n`. -/
theorem KM.finrank_eq (M : Matrix (Fin n) (Fin n) ℂ) : Module.finrank ℝ (KM M) = n := by
  sorry

end Tubal
