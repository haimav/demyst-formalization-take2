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

/-- **Example 4** (Complex numbers as a tubal ring). The multiplication of complex numbers on
`ℝ² ≅ ℂ`, `[a, b]·[c, d] = [ac - bd, ad + bc]`, is `⋆_M` with `M = [[1, i], [1, -i]]`. -/
theorem example4 (x y : Fin 2 → ℝ) : toC (complexMul x y) = starMC M4 (toC x) (toC y) := by
  sorry

theorem M4_admissible : Admissible M4 := by
  sorry

/-- **Example 4**: "we can use the multiplication defined by complex numbers to get a field":
`𝕂_M` for this `M` is a field. -/
theorem example4_isField : haveI : Fact (Admissible M4) := ⟨M4_admissible⟩; IsField (KM M4) := by
  sorry

/-- **Example 4**: "The use of complex numbers in `M` for building a `⋆_M` which corresponds to
complex product is unavoidable. It can be shown that no such real `M` exists." -/
theorem example4_no_real_M :
    ¬ ∃ M : Matrix (Fin 2) (Fin 2) ℝ, IsUnit M ∧
      ∀ x y : Fin 2 → ℝ, toC (complexMul x y) = starMC (M.map (↑)) (toC x) (toC y) := by
  sorry

/-- The complex numbers as a tubal ring on `ℝ²`. -/
def complexTubal : TubalRing 2 where
  mul := complexMul
  mul_assoc := by sorry
  left_distrib := by sorry
  right_distrib := by sorry
  mul_comm := by sorry
  exists_one := by sorry
  vonNeumann := by sorry
  smul_mul := by sorry
  mul_smul := by sorry

/-! ### Example 14 (split-complex numbers) -/

/-- **Example 14** (first claim, [30]): up to isomorphism, every commutative ring over `ℝ²`
(commutative unital `ℝ`-algebra structure on `ℝ²`) is isomorphic to one of three possible
rings: complex numbers, split-complex numbers and dual numbers. -/
theorem example14_classification (R : CommAlgOn 2) :
    ∃ e : (Fin 2 → ℝ) ≃ₗ[ℝ] (Fin 2 → ℝ),
      (∀ x y, e (R.mul x y) = complexMul (e x) (e y)) ∨
      (∀ x y, e (R.mul x y) = splitMul (e x) (e y)) ∨
      (∀ x y, e (R.mul x y) = dualMul (e x) (e y)) := by
  sorry

/-- **Example 14**: the split-complex product defines a commutative ring over `ℝ²`. -/
def splitCommAlg : CommAlgOn 2 where
  mul := splitMul
  mul_assoc := by sorry
  left_distrib := by sorry
  right_distrib := by sorry
  mul_comm := by sorry
  exists_one := by sorry
  smul_mul := by sorry
  mul_smul := by sorry

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
  sorry

/-- **Example 14**: "So, this is a tubal ring." -/
def splitTubal : TubalRing 2 where
  mul := splitMul
  mul_assoc := splitCommAlg.mul_assoc
  left_distrib := splitCommAlg.left_distrib
  right_distrib := splitCommAlg.right_distrib
  mul_comm := splitCommAlg.mul_comm
  exists_one := splitCommAlg.exists_one
  vonNeumann := by sorry
  smul_mul := splitCommAlg.smul_mul
  mul_smul := splitCommAlg.mul_smul

/-- The `2 × 2` Hadamard matrix `[[1, 1], [1, -1]]`. -/
def hadamard2 : Matrix (Fin 2) (Fin 2) ℂ := !![1, 1; 1, -1]

/-- **Example 14**: the split-complex product is `⋆_M` with `M = [[1, 1], [1, -1]]`. -/
theorem example14 (x y : Fin 2 → ℝ) : toC (splitMul x y) = starMC hadamard2 (toC x) (toC y) := by
  sorry

/-- The DFT matrix `F_n`, `(F_n)_{jk} = e^{-2πi jk/n}`. -/
def dftMatrix (n : ℕ) : Matrix (Fin n) (Fin n) ℂ :=
  fun j k => Complex.exp (-2 * Real.pi * I * (j : ℂ) * (k : ℂ) / (n : ℂ))

/-- **Example 14**: `[[1, 1], [1, -1]]` coincides with the unscaled DFT matrix for `n = 2`;
hence the split-complex product is the t-product for `n = 2`. -/
theorem example14_dft : dftMatrix 2 = hadamard2 := by
  sorry

/-! ### Example 15 (dual numbers) -/

/-- **Example 15**: the dual number product defines a commutative ring over `ℝ²`. -/
def dualCommAlg : CommAlgOn 2 where
  mul := dualMul
  mul_assoc := by sorry
  left_distrib := by sorry
  right_distrib := by sorry
  mul_comm := by sorry
  exists_one := by sorry
  smul_mul := by sorry
  mul_smul := by sorry

/-- **Example 15**: for any dual number `x + yε`, `ε · (x + yε) · ε = 0`, so `ε` does not have
a weak inverse. -/
theorem example15_eps (x : Fin 2 → ℝ) : dualMul (dualMul ![0, 1] x) ![0, 1] = 0 := by
  sorry

/-- **Example 15**: the dual numbers are *not* a tubal ring. -/
theorem example15_not_tubal : ¬ ∃ T : TubalRing 2, T.mul = dualMul := by
  sorry

/-- **Example 15**: "Indeed, no invertible `M` exists that makes dual numbers isomorphic to
`ℝ²`", i.e. the dual product is not `⋆_M` for any invertible `M`. -/
theorem example15_no_M :
    ¬ ∃ M : Matrix (Fin 2) (Fin 2) ℂ, IsUnit M ∧
      ∀ x y : Fin 2 → ℝ, toC (dualMul x y) = starMC M (toC x) (toC y) := by
  sorry

/-- **Example 15** (in the sense of ring isomorphism): the ring of dual numbers is not
isomorphic (as a ring) to any `𝕂_M`. -/
theorem example15_not_iso (M : Matrix (Fin 2) (Fin 2) ℂ) [Fact (Admissible M)] :
    IsEmpty (DualNumber ℝ ≃+* KM M) := by
  sorry

/-! ### Example 16 (t-product via circulant matrices) -/

/-- The circulant matrix whose first column is `x`: `circ(x)_{ij} = x_{(i - j) mod n}`. -/
def circ (x : Fin n → ℝ) : Matrix (Fin n) (Fin n) ℝ := fun i j => x (i - j)

/-- The t-product `x ⋆_t y := F_n⁻¹ (F_n x • F_n y)` (real part; it is real). -/
def tProd (x y : Fin n → ℝ) : Fin n → ℝ := fun i => (starMC (dftMatrix n) (toC x) (toC y) i).re

theorem dftMatrix_admissible (n : ℕ) : Admissible (dftMatrix n) := by
  sorry

/-- **Example 16**: the sum of circulant matrices is circulant, the product of circulant
matrices is also circulant, any two circulant matrices commute, and the identity matrix is a
circulant matrix. -/
theorem example16_circ_algebra :
    (∀ x y : Fin n → ℝ, circ x + circ y = circ (x + y)) ∧
    (∀ x y : Fin n → ℝ, ∃ z, circ x * circ y = circ z) ∧
    (∀ x y : Fin n → ℝ, circ x * circ y = circ y * circ x) ∧
    (∃ z : Fin n → ℝ, circ z = 1) := by
  sorry

/-- **Example 16**: `x ⋆_t y` is real and `circ(x ⋆_t y) = circ(x) · circ(y)`; i.e. the ring
obtained by identifying `x` with `circ(x)` is exactly the t-product (`⋆_M` with `M = F_n`). -/
theorem example16 (x y : Fin n → ℝ) :
    starMC (dftMatrix n) (toC x) (toC y) = toC (tProd x y) ∧
    circ (tProd x y) = circ x * circ y := by
  sorry

end Tubal
