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

/-! ### Eq. (3) and Example 17 (polynomial products modulo `Q`) -/

/-- The polynomial `P_a := a₁ + a₂ X + ⋯ + aₙ X^{n-1}` associated with a vector `a`. -/
def polyOf {R : Type*} [CommRing R] (a : Fin n → R) : R[X] := ∑ k, C (a k) * X ^ (k : ℕ)

/-- **Example 17.** Let `Q` be a polynomial of degree `n` all of whose roots `r₀, …, r_{n-1}`
are distinct, and let `M` be the Vandermonde matrix at the roots of `Q`. Then
`P_c = P_a · P_b mod Q ⟺ M c = M a • M b`. -/
theorem example17 (Q : ℝ[X]) (hQ : Q.natDegree = n) (r : Fin n → ℂ) (hr : Function.Injective r)
    (hroot : ∀ j, (Q.map (algebraMap ℝ ℂ)).IsRoot (r j)) (a b c : Fin n → ℝ) :
    Q ∣ polyOf c - polyOf a * polyOf b ↔
      vandermonde r *ᵥ toC c = (vandermonde r *ᵥ toC a) * (vandermonde r *ᵥ toC b) := by
  sorry

/-- The product of Section 3.2 / Example 17: `a · b` is the tube associated with the remainder
`P_a · P_b mod Q` (whose degree is `< n` when `Q` has degree `n`). -/
def polyModMul (Q : ℝ[X]) (a b : Fin n → ℝ) : Fin n → ℝ :=
  fun k => ((polyOf a * polyOf b) % Q).coeff (k : ℕ)

/-- Section 3.2 / **Example 17**: "we can choose some other polynomial `Q`, as long as its degree
is `n` (for a ring over `ℝⁿ`) and all its roots are distinct … polynomial product modulo `Q` is
essentially `⋆_M` with this `M`": the Vandermonde matrix at the roots is admissible, the mod-`Q`
product is `⋆_M`, and it makes `ℝⁿ` a tubal ring. -/
theorem example17_tubal (Q : ℝ[X]) (hQ : Q.natDegree = n) (r : Fin n → ℂ)
    (hr : Function.Injective r) (hroot : ∀ j, (Q.map (algebraMap ℝ ℂ)).IsRoot (r j)) :
    Admissible (vandermonde r) ∧
    (∀ a b : Fin n → ℝ, toC (polyModMul Q a b) = starMC (vandermonde r) (toC a) (toC b)) ∧
    ∃ T : TubalRing n, T.mul = polyModMul Q := by
  sorry

/-- **Eq. (3)**: `P_c = P_a · P_b mod (Xⁿ - 1) ⟺ F_n c = F_n a • F_n b`
(the paper writes `X^p - 1`, a typo for `Xⁿ - 1`). -/
theorem eq3 (a b c : Fin n → ℝ) :
    (X ^ n - 1 : ℝ[X]) ∣ polyOf c - polyOf a * polyOf b ↔
      dftMatrix n *ᵥ toC c = (dftMatrix n *ᵥ toC a) * (dftMatrix n *ᵥ toC b) := by
  sorry

/-- The skew-Fourier matrix `F_n diag(1, e^{πi/n}, e^{2πi/n}, …, e^{(n-1)πi/n})`. -/
def skewFourier (n : ℕ) : Matrix (Fin n) (Fin n) ℂ :=
  dftMatrix n * diagonal (fun k : Fin n => Complex.exp (Real.pi * I * (k : ℂ) / (n : ℂ)))

/-- **Example 17**: for `Q = Xⁿ + 1`, `M` (the Vandermonde matrix at the roots of `Q`) is the
skew-Fourier matrix. -/
theorem example17_skewFourier :
    ∃ r : Fin n → ℂ, Function.Injective r ∧ (∀ j, ((X ^ n + 1 : ℝ[X]).map (algebraMap ℝ ℂ)).IsRoot (r j)) ∧
      skewFourier n = vandermonde r := by
  sorry

/-- **Example 17**: when `n = 2`, `M` is the same matrix as in Example 4 … -/
theorem example17_two : skewFourier 2 = M4 := by
  sorry

/-- **Example 17**: … so the ring we obtain is isomorphic to `ℂ` and is a field. -/
theorem example17_field :
    haveI : Fact (Admissible (skewFourier 2)) := ⟨example17_two ▸ M4_admissible⟩
    IsField (KM (skewFourier 2)) ∧ Nonempty (KM (skewFourier 2) ≃+* ℂ) := by
  sorry

/-- **Example 17**: `ℂ` is isomorphic as a field to `ℝ[x]/(x² + 1)` ([7, Section 9.4,
Exercise 7]). -/
theorem example17_complex_quotient : Nonempty (ℂ ≃+* AdjoinRoot (X ^ 2 + 1 : ℝ[X])) := by
  sorry

/-! ### Example 18 (group rings) -/

/-- The convolution product of the group ring `ℝ[G]`: `(f · g)(x) = ∑_{u · v = x} f(u) g(v)`. -/
def groupConv {G : Type*} [CommGroup G] [Fintype G] [DecidableEq G] (f g : G → ℝ) : G → ℝ :=
  fun x => ∑ u, ∑ v, if u * v = x then f u * g v else 0

/-- **Example 18.** Let `G` be a finite abelian group of size `n`. The group ring `ℝ[G]`
(functions `G → ℝ` with point-wise addition and convolution as product) is a commutative von
Neumann regular ring; identifying each group element with an index in `{1, …, n}` makes it a
tubal ring. -/
theorem example18 {G : Type*} [CommGroup G] [Fintype G] [DecidableEq G] (e : G ≃ Fin n) :
    ∃ T : TubalRing n, ∀ a b : Fin n → ℝ,
      T.mul a b = fun i => groupConv (a ∘ e) (b ∘ e) (e.symm i) := by
  sorry

/-- **Example 18**: the t-product is obtained by using the cyclic group `G = ℤ_n`. -/
theorem example18_tProduct [NeZero n] (a b : Fin n → ℝ) :
    toC (fun i => groupConv (G := Multiplicative (Fin n)) (a ∘ Multiplicative.toAdd)
        (b ∘ Multiplicative.toAdd) (Multiplicative.ofAdd i)) =
      starMC (dftMatrix n) (toC a) (toC b) := by
  sorry

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
  sorry

/-- The (Sylvester) Walsh–Hadamard matrix `WHT_{ij} = (-1)^{∑_b i_b j_b}` (`i_b` the bits). -/
def walshHadamard (k : ℕ) : Matrix (Fin (2 ^ k)) (Fin (2 ^ k)) ℂ :=
  fun i j => ∏ b : Fin k, if (i : ℕ).testBit b && (j : ℕ).testBit b then -1 else 1

/-- **Example 18**: the XOR-convolution `(a · b)_i = ∑_j a_j b_{i⊕j}` (convolution over the
group `ℤ₂^k`) diagonalizes under the Walsh–Hadamard transform: it is a tubal ring with
`M = WHT`. -/
theorem example18_xor (k : ℕ) :
    IsUnit (walshHadamard k) ∧
    (∀ a b : Fin (2 ^ k) → ℝ, toC (xorConv k a b) = starMC (walshHadamard k) (toC a) (toC b)) ∧
    ∃ T : TubalRing (2 ^ k), T.mul = xorConv k := by
  sorry

end Tubal
