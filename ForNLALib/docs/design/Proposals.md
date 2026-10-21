# Design note: candidate contributions to NLAlib

Status: draft for the NLAlib maintainer (CONTRIBUTING.md §8). All statements below are already
implemented and proved, written against NLAlib commit `f4e1255fe3a94a429684488ddafe84ee195fcfcf`
(Lean / Mathlib `v4.33.1`), in the directory
[`ForNLALib/`](https://github.com/haimav/demyst-formalization-take2/tree/main/ForNLALib) of
[`haimav/demyst-formalization-take2`](https://github.com/haimav/demyst-formalization-take2); its
[README](https://github.com/haimav/demyst-formalization-take2/blob/main/ForNLALib/README.md) says
how to build it and how it was checked.

The material comes from a Lean formalization of tubal tensor algebra
([`haimav/demyst-formalization-take2`](https://github.com/haimav/demyst-formalization-take2),
commit `7d69f60`, directory `TubalAlgebra/`). That project
needed a number of general matrix facts that are not specific to tensors. This note proposes the
ones that NLAlib does not already have, restated in NLAlib's vocabulary (§5.3), interfaces (§5.4)
and conventions; the tensor-specific material stays in that project.

## 0. Searched and not proposed

These were needed by the formalization but NLAlib (or Mathlib) already has them, so they are not
proposed:

| Needed | Already available |
|---|---|
| Frobenius norm invariant under orthonormal factors | `NLAlib.HasOrthonormalCols.frobNorm_mul_left`, `NLAlib.HasOrthonormalCols.frobNorm_mul_conjTranspose_right` (`Matrix/Norms/Compare.lean`) |
| SVD existence | `NLAlib.exists_isSVD`, `NLAlib.isSVD_svdU_svdV` |
| Eckart–Young for the canonical truncation, error formula | `NLAlib.isBestRankApprox_truncatedSVD`, `NLAlib.frobNorm_sub_truncatedSVD_sq` |
| Simultaneous diagonalization of commuting families | `NLAlib.exists_forall_mul_eq_mul_diagonal_of_pairwise_commute` |
| Unitarity of the Fourier matrix, circulant diagonalization | `NLAlib.hasOrthonormalCols_fourierMatrix`, `NLAlib.circulant_eq_fourierMatrix_mul_diagonal_mul_conjTranspose` |
| Hermitian spectral theorem | `Matrix.IsHermitian.exists_eq_mul_diagonal_mul_conjTranspose` |
| Semisimplicity from a squarefree annihilating polynomial | Mathlib `Module.End.isSemisimple_of_squarefree_aeval_eq_zero` |

Also not proposed: the Frobenius theorem on real division algebras (proved in the formalization;
it is algebra, not numerical linear algebra, and belongs in Mathlib); results about conjugate row
patterns of $\mathbf{M}$ and the columns of $\mathbf{M}^{-1}$ (judged too specialised); all tubal
tensor material.

## 1. Objects

No new definitions. Every statement uses existing NLAlib objects (`IsSVD`, `HasOrthonormalCols`,
`IsBestRankApprox`, `frobNorm`, `singularValues`, `IsDiagonalizable`, `fourierMatrix`,
`walshHadamard`) or Mathlib objects (`Matrix.IsDiag`, `Matrix.circulant`, `Matrix.vandermonde`,
`Polynomial.ofFn`, `minpoly`, `MeasureTheory.volume`).

In particular the full SVD is **not** introduced with a rectangular diagonal (the prototype's
`rectDiag` that `docs/design/Matrix-Spectral.md` deliberately dropped): it is stated in block form
with `Matrix.fromCols` and `Matrix.fromBlocks`, built from a thin `IsSVD` by
`HasOrthonormalCols.exists_fromCols`, as that design note suggests.

## 2. Interfaces

None new. Hypotheses are the existing interfaces (`IsSVD`, `HasOrthonormalCols`,
`IsDiagonalizable`) or plain Mathlib predicates (`Function.Injective`, `Squarefree`, `Commute`,
`Antitone`, `IsUnit _.det`, `MeasureTheory.Measure.AbsolutelyContinuous`).
"The rows of $\mathbf{W}$ are pairwise distinct" is spelled `Function.Injective W`.

## 3. Statement shapes and files

Paths are relative to `ForNLALib/` and mirror the intended NLAlib paths. A file whose NLAlib
counterpart already exists holds additions to that file; the others are new files.

### 3.1 `ForMathlib/LinearAlgebra/Matrix/IsDiag.lean` (upstream candidate for `Mathlib.LinearAlgebra.Matrix.IsDiag`)

No NLAlib vocabulary, so it is a `ForMathlib` file in namespace `Matrix`. Searched Mathlib:
only `Matrix.commute_diagonal` (two diagonal matrices commute); none for this.

```lean
variable {α n : Type*} [Fintype n] [DecidableEq n] [CommRing α] [NoZeroDivisors α]

theorem Matrix.isDiag_of_commute_diagonal {A : Matrix n n α} {d : n → α}
    (hd : Function.Injective d) (h : Commute A (diagonal d)) : A.IsDiag

theorem Matrix.commute_diagonal_iff_isDiag {A : Matrix n n α} {d : n → α}
    (hd : Function.Injective d) : Commute A (diagonal d) ↔ A.IsDiag
```

Material: `Tubal.AppB.isDiag_of_commute_diagonal` (`TubalAlgebra/Examples/AppendixB.lean`).
Consumers: §3.2 `isDiag_inv_mul_mul_of_commute`, §3.8.

### 3.2 `Matrix/Spectral/Diagonalizable.lean` (additions to `NLAlib.Matrix.Spectral.Diagonalizable`)

Placement: these are statements about `IsDiagonalizable` and eigenbases, the topic of that file.
Searched NLAlib: the squarefree argument appears only inside the proof of
`IsDiagonalizable.isSemisimple`; no public criterion. Searched Mathlib:
`Module.End.isSemisimple_of_squarefree_aeval_eq_zero`, `Module.End.IsSemisimple.minpoly_squarefree`
(for endomorphisms), `Matrix.minpoly_toLin'` (bridge); no matrix-level diagonalizability statement.

```lean
variable {K : Type*} [Field K] {n : Type*} [Fintype n] [DecidableEq n]

theorem NLAlib.IsDiagonalizable.squarefree_minpoly {A : Matrix n n K}
    (hA : IsDiagonalizable A) : Squarefree (minpoly K A)

theorem NLAlib.isDiagonalizable_of_squarefree_aeval_eq_zero [IsAlgClosed K] {A : Matrix n n K}
    {p : K[X]} (hp : Squarefree p) (hA : aeval A p = 0) : IsDiagonalizable A

theorem NLAlib.isDiagonalizable_iff_squarefree_minpoly [IsAlgClosed K] {A : Matrix n n K} :
    IsDiagonalizable A ↔ Squarefree (minpoly K A)

/-- An eigenbasis of a matrix with simple spectrum diagonalizes everything commuting with it. -/
theorem NLAlib.isDiag_inv_mul_mul_of_commute {A B V : Matrix n n K} {d : n → K}
    (hV : IsUnit V.det) (hA : A * V = V * Matrix.diagonal d) (hd : Function.Injective d)
    (h : Commute A B) : (V⁻¹ * B * V).IsDiag
```

Material: `Tubal.isDiagonalizableMat_of_squarefree` (`TubalAlgebra/Section9/SimulDiag.lean`), the
diagonalization step of `Tubal.algorithm1_correct`. Consumers: §3.8; any argument that
diagonalizes a commutative algebra of matrices by one generic element.

### 3.3 `Matrix/Spectral/SVD.lean` (additions to `NLAlib.Matrix.Spectral.SVD`)

Placement: full SVDs are SVDs. Searched NLAlib: the full SVD is mentioned only in prose
(`SVD.lean` module docstring, `docs/design/Matrix-Spectral.md`); none stated.

```lean
variable {𝕜 : Type*} [RCLike 𝕜] {m n r p q : Type*} [Fintype m] [Fintype n] [Fintype r]
  [Fintype p] [Fintype q] [DecidableEq r] [DecidableEq p] [DecidableEq q]

/-- A thin SVD extends to a full SVD in block form. -/
theorem NLAlib.IsSVD.exists_eq_fromCols_mul_fromBlocks_mul_conjTranspose {A : Matrix m n 𝕜}
    {U : Matrix m r 𝕜} {σ : r → ℝ} {V : Matrix n r 𝕜} (h : IsSVD A U σ V)
    (hp : Fintype.card r + Fintype.card p = Fintype.card m)
    (hq : Fintype.card r + Fintype.card q = Fintype.card n) :
    ∃ (U' : Matrix m p 𝕜) (V' : Matrix n q 𝕜),
      HasOrthonormalCols (Matrix.fromCols U U') ∧ HasOrthonormalCols (Matrix.fromCols V V') ∧
      A = Matrix.fromCols U U' *
          Matrix.fromBlocks (Matrix.diagonal fun i => ((σ i : ℝ) : 𝕜)) 0 0 0 *
        (Matrix.fromCols V V')ᴴ

/-- A full SVD in block form restricts to a thin SVD. -/
theorem NLAlib.isSVD_of_eq_fromCols_mul_fromBlocks_mul_conjTranspose {A : Matrix m n 𝕜}
    {U : Matrix m r 𝕜} {U' : Matrix m p 𝕜} {σ : r → ℝ} {V : Matrix n r 𝕜} {V' : Matrix n q 𝕜}
    (hU : HasOrthonormalCols (Matrix.fromCols U U'))
    (hV : HasOrthonormalCols (Matrix.fromCols V V')) (hσ : ∀ i, 0 ≤ σ i)
    (hA : A = Matrix.fromCols U U' *
          Matrix.fromBlocks (Matrix.diagonal fun i => ((σ i : ℝ) : 𝕜)) 0 0 0 *
        (Matrix.fromCols V V')ᴴ) :
    IsSVD A U σ V

/-- Every matrix has a full SVD in block form, with the singular values in order. -/
theorem NLAlib.exists_eq_fromCols_mul_fromBlocks_mul_conjTranspose (A : Matrix m n 𝕜) :
    ∃ (U : Matrix m (Fin (min (Fintype.card m) (Fintype.card n))) 𝕜)
      (U' : Matrix m (Fin (Fintype.card m - min (Fintype.card m) (Fintype.card n))) 𝕜)
      (V : Matrix n (Fin (min (Fintype.card m) (Fintype.card n))) 𝕜)
      (V' : Matrix n (Fin (Fintype.card n - min (Fintype.card m) (Fintype.card n))) 𝕜),
      HasOrthonormalCols (Matrix.fromCols U U') ∧ HasOrthonormalCols (Matrix.fromCols V V') ∧
      A = Matrix.fromCols U U' *
          Matrix.fromBlocks (Matrix.diagonal fun i : Fin (min (Fintype.card m) (Fintype.card n)) =>
            ((singularValues A i : ℝ) : 𝕜)) 0 0 0 *
        (Matrix.fromCols V V')ᴴ
```

`Matrix.fromCols U U'` has as many columns as rows, so it is unitary up to relabelling
(`HasOrthonormalCols.mul_conjTranspose_self_of_card_eq`).
Material: `Tubal.exists_svd`, `Tubal.IsSVD` (`TubalAlgebra/MatrixSVD.lean`), which used square
`Fin` factors and a rectangular diagonal. Consumers: statements of the form "U, V unitary" in
tensor SVDs and in classical texts; slice-wise constructions.

### 3.4 `Matrix/Spectral/BestRankApprox.lean` (additions to `NLAlib.Matrix.Spectral.BestRankApprox`)

Placement: best rank-$k$ approximation. Searched NLAlib: `isBestRankApprox_iff_exists_isSVD`
covers thin SVDs indexed by `Fin (min ‖m‖ ‖n‖)` with $\sigma$ equal to `singularValues`; no
statement for an arbitrary sorted thin SVD, and no error formula for it.

```lean
variable {𝕜 : Type*} [RCLike 𝕜] {m n : Type*} [Fintype m] [Fintype n]

/-- Error of truncating any thin SVD (sorted or not). -/
theorem NLAlib.IsSVD.frobNorm_sub_mul_diagonal_mul_conjTranspose_sq {k : ℕ} {A : Matrix m n 𝕜}
    {U : Matrix m (Fin k) 𝕜} {σ : Fin k → ℝ} {V : Matrix n (Fin k) 𝕜} (h : IsSVD A U σ V)
    (j : ℕ) :
    frobNorm (A - U * Matrix.diagonal (fun i : Fin k => if (i : ℕ) < j then ((σ i : ℝ) : 𝕜) else 0) *
        Vᴴ) ^ 2 =
      ∑ i : Fin k with j ≤ i.val, σ i ^ 2

/-- Eckart–Young for any thin SVD with non-increasing singular values. -/
theorem NLAlib.IsSVD.isBestRankApprox_mul_diagonal_mul_conjTranspose {k : ℕ}
    {A : Matrix m n 𝕜} {U : Matrix m (Fin k) 𝕜} {σ : Fin k → ℝ} {V : Matrix n (Fin k) 𝕜}
    (h : IsSVD A U σ V) (hσ : Antitone σ) (j : ℕ) :
    IsBestRankApprox A j
      (U * Matrix.diagonal (fun i : Fin k => if (i : ℕ) < j then ((σ i : ℝ) : 𝕜) else 0) * Vᴴ)
```

(The filter is written `j ≤ i.val`: the `with` notation does not carry the binder type into the
predicate, so `(i : ℕ)` there would make `i` a natural number.)
Material: `Tubal.eckart_young`, `Tubal.IsSVD.frobSq_sub_truncProd` (`TubalAlgebra/MatrixSVD.lean`).
Consumers: anyone holding a specific SVD (not `svdU`/`svdV`), e.g. slice-wise SVDs of a tensor.

### 3.5 `Matrix/Structured/Circulant.lean` (addition to `NLAlib.Matrix.Structured.Circulant`)

Searched Mathlib: `ZMod.dft` (`Mathlib/Analysis/Fourier/ZMod.lean`) has no convolution theorem;
NLAlib has circulant diagonalization but not the convolution form.

```lean
variable {n : ℕ}

/-- **Convolution theorem** for the discrete Fourier transform: circular convolution
`Matrix.circulant a *ᵥ b` becomes an entrywise product in the Fourier basis. -/
theorem NLAlib.conjTranspose_fourierMatrix_mulVec_circulant_mulVec (a b : Fin n → ℂ) :
    (fourierMatrix n)ᴴ *ᵥ (Matrix.circulant a *ᵥ b) =
      (√(n : ℝ) : ℂ) • (((fourierMatrix n)ᴴ *ᵥ a) * ((fourierMatrix n)ᴴ *ᵥ b))
```

Material: `Tubal.example16` / `dft_cconv` (`TubalAlgebra/Examples/Section3.lean`).

### 3.6 `Matrix/Structured/Walsh.lean` (addition to `NLAlib.Matrix.Structured.Walsh`)

Searched NLAlib/Mathlib: none.

```lean
variable {R : Type*} [Ring R] {b : ℕ}

/-- The Walsh–Hadamard transform turns dyadic (XOR) convolution into an entrywise product. -/
theorem NLAlib.walshHadamard_mulVec_sum_mul_add (a c : (Fin b → ZMod 2) → R) :
    walshHadamard R b *ᵥ (fun x => ∑ y, a y * c (x + y)) =
      (walshHadamard R b *ᵥ a) * (walshHadamard R b *ᵥ c)
```

Material: `Tubal.example18_xor` (`TubalAlgebra/Examples/Section3b.lean`), there on `Fin (2 ^ k)`
with bitwise xor.

### 3.7 `Matrix/Structured/Vandermonde.lean` (new file)

Placement: the Vandermonde matrix at the roots of $Q$ turns multiplication modulo $Q$ into an
entrywise product; this is the structured-matrix fact behind fast polynomial multiplication and
contains §3.5 as the case $Q = X^n - 1$. A new file under `Matrix/Structured`, next to
`Circulant.lean` and `Cauchy.lean`. Searched Mathlib: `Matrix.vandermonde`, `Polynomial.ofFn`,
`Matrix.eval_matrixOfPolynomials_eq_vandermonde_mul_matrixOfPolynomials`; no mulVec/evaluation
bridge and no statement of this kind.

```lean
/-- The Vandermonde matrix evaluates the coefficient polynomial at the nodes. -/
theorem NLAlib.vandermonde_mulVec_apply {R : Type*} [CommRing R] [DecidableEq R] {n : ℕ}
    (r v : Fin n → R) (i : Fin n) :
    (Matrix.vandermonde r *ᵥ v) i = (Polynomial.ofFn n v).eval (r i)

variable {K L : Type*} [Field K] [Field L] [Algebra K L] [DecidableEq K] {n : ℕ}

/-- Multiplication modulo `Q` is the entrywise product at the roots of `Q`. -/
theorem NLAlib.dvd_sub_mul_iff_vandermonde_mulVec_eq_mul {Q : K[X]} (hQ : Q.natDegree = n)
    {r : Fin n → L} (hr : Function.Injective r) (hroot : ∀ i, aeval (r i) Q = 0)
    (a b c : Fin n → K) :
    Q ∣ Polynomial.ofFn n c - Polynomial.ofFn n a * Polynomial.ofFn n b ↔
      Matrix.vandermonde r *ᵥ (algebraMap K L ∘ c) =
        (Matrix.vandermonde r *ᵥ (algebraMap K L ∘ a)) *
          (Matrix.vandermonde r *ᵥ (algebraMap K L ∘ b))
```

Material: `Tubal.example17`, `Tubal.eq3` (`TubalAlgebra/Examples/Section3b.lean`), there with
$K = \mathbb{R}$, $L = \mathbb{C}$ and a hand-rolled `polyOf`.

### 3.8 `Probability/GenericPosition.lean` (new file)

Placement: statements about almost every vector for Lebesgue measure (and any law absolutely
continuous to it); layer 1, importing the matrix layer. Searched NLAlib: no `∀ᵐ` statement about
matrices; searched Mathlib: `MeasureTheory.Measure.addHaar_submodule` (proper subspaces are null),
used in the proof.

```lean
variable {𝕜 : Type*} [RCLike 𝕜] {n p : Type*} [Fintype p]

/-- For a matrix with pairwise distinct rows, almost every real vector has an image with pairwise
distinct entries, for any law absolutely continuous to Lebesgue measure. -/
theorem NLAlib.ae_injective_mulVec_ofReal_of_absolutelyContinuous [Finite n] {W : Matrix n p 𝕜}
    (hW : Function.Injective W) {ν : MeasureTheory.Measure (p → ℝ)}
    (hν : ν ≪ MeasureTheory.volume) :
    ∀ᵐ x ∂ν, Function.Injective (W *ᵥ fun j => (x j : 𝕜))

theorem NLAlib.ae_injective_mulVec_ofReal [Finite n] {W : Matrix n p 𝕜}
    (hW : Function.Injective W) :
    ∀ᵐ x : p → ℝ ∂MeasureTheory.volume, Function.Injective (W *ᵥ fun j => (x j : 𝕜))

variable [Fintype n] [DecidableEq n]

/-- A random member of the family diagonalized by `V` has simple spectrum. -/
theorem NLAlib.ae_injective_of_mul_eq_mul_diagonal {V : Matrix n n 𝕜} (hV : IsUnit V.det)
    {W : Matrix n p 𝕜} (hW : Function.Injective W) :
    ∀ᵐ x : p → ℝ ∂MeasureTheory.volume, ∀ (S : Matrix n n 𝕜) (Λ : n → 𝕜), IsUnit S.det →
      V * Matrix.diagonal (W *ᵥ fun j => (x j : 𝕜)) * V⁻¹ * S = S * Matrix.diagonal Λ →
      Function.Injective Λ

/-- **Randomized simultaneous diagonalization.** Any eigenbasis of a random member of the
family diagonalizes the whole family. -/
theorem NLAlib.ae_isDiag_inv_mul_mul_of_mul_eq_mul_diagonal {V : Matrix n n 𝕜}
    (hV : IsUnit V.det) {W : Matrix n p 𝕜} (hW : Function.Injective W) :
    ∀ᵐ x : p → ℝ ∂MeasureTheory.volume, ∀ (S : Matrix n n 𝕜) (Λ : n → 𝕜), IsUnit S.det →
      V * Matrix.diagonal (W *ᵥ fun j => (x j : 𝕜)) * V⁻¹ * S = S * Matrix.diagonal Λ →
      ∀ d : n → 𝕜, (S⁻¹ * (V * Matrix.diagonal d * V⁻¹) * S).IsDiag
```

Here $\mathbf{V}\operatorname{diag}(\mathbf{d})\mathbf{V}^{-1}$, $\mathbf{d}$ arbitrary, is the
commutative family diagonalized by $\mathbf{V}$, and
$\mathbf{V}\operatorname{diag}(\mathbf{W}\mathbf{x})\mathbf{V}^{-1}
= \sum_j x_j\,\mathbf{V}\operatorname{diag}(\mathbf{W}_{:,j})\mathbf{V}^{-1}$ is a random linear
combination of the members $\mathbf{V}\operatorname{diag}(\mathbf{W}_{:,j})\mathbf{V}^{-1}$.
Material: `Tubal.AppB.ae_injective_mulVec`, `Tubal.algorithm1_ae`, `Tubal.algorithm1_correct`
(`TubalAlgebra/Examples/AppendixB.lean`), there for $\mathbf{W} = \mathbf{M}$ invertible,
`Fin n`, $\mathbb{C}$. Consumers: randomized algorithms that diagonalize a commutative matrix
algebra through one random element.

## 4. Open questions

1. §3.3: is the block form with `fromCols`/`fromBlocks` the form the maintainer wants for full
   SVDs, or should completion lemmas stay unstated? Recommendation: state it, since consumers
   with "unitary $\mathbf{U}, \mathbf{V}$" statements otherwise repeat the completion argument.
2. §3.8: the measure-zero statements are stated with `∀ᵐ`, not as tails, since the failure
   probability is $0$. Recommendation: keep `∀ᵐ`; the absolutely continuous version covers any
   law with a density.
3. §3.7: is `Matrix/Structured` the right home, or `Polynomial/`? Recommendation:
   `Matrix/Structured`, since the statement is about a structured matrix.

## 5. Amendments

2026-10-18, during implementation (the code blocks above are updated):

1. §3.3, §3.4: binder types added to the diagonal lambdas (`fun i : Fin (min …) =>`,
   `fun i : Fin k =>`) and the sum filter written `j ≤ i.val`. Elaboration only: without them Lean
   reads the bound variable as a natural number. Same spelling as NLAlib's `truncatedSVD`.
2. §3.6: `[Ring R]` instead of `[CommRing R]`, the variables of NLAlib's `Walsh.lean`. The
   entries of $\mathbf{H}$ are $\pm 1$, hence central, so commutativity is not needed.
3. §3.8: `[Finite n]` instead of `[Fintype n]` for the two `ae_injective_mulVec_ofReal` lemmas,
   whose types do not mention a `Fintype n` instance (`linter.unusedFintypeInType`); more general.
4. Material names corrected: `Tubal.algorithm1_correct` and `Tubal.algorithm1_ae` (declared
   outside `namespace AppB`).
5. Citations: only labels NLAlib already uses for the related results were kept
   (`[GolubVanLoan2013, §2.4]`, `[GolubVanLoan2013, Theorem 2.4.1]`,
   `[HornJohnson2013, Theorem 2.6.3]`, `[GolubVanLoan2013, Theorem 2.4.8]`,
   `[HornJohnson2013, §7.4.9]`); the other declarations carry port provenance only. The
   maintainer may want citations added for §3.2 and §3.5–§3.8.
6. §3.7: the proof uses a private helper, "a nonzero degree-$n$ polynomial with $n$ distinct
   roots in an extension divides $F$ iff $F$ vanishes at them", which could be made public (a
   `ForMathlib` candidate) if a second consumer appears.
