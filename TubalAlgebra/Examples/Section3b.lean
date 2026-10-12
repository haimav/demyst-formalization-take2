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
