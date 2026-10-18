# ForNLALib: candidate contributions to NLAlib

This directory collects the parts of the formalization in `../TubalAlgebra/` that are general
numerical linear algebra rather than tubal tensor algebra, rewritten as proposed contributions to
[NLAlib](https://github.com/NLA-lib/NLAlib) (<https://nla-lib.org/>). They follow NLAlib's
conventions (`CONTRIBUTING.md` of NLAlib) and are written against its API.

It is a **separate Lake package** with its own toolchain:

| | formalization (`../`) | `ForNLALib/` |
|---|---|---|
| Lean / Mathlib | v4.34.1 | v4.33.1 (NLAlib's pin) |
| depends on | Mathlib | NLAlib commit `f4e1255` (and, through it, Mathlib) |

The formalization does not depend on this directory, and nothing in `../TubalAlgebra/` was
changed. The formalization stays self-contained; this folder is only for what might be pushed
upstream.

## Contents

Paths mirror NLAlib's tree. A file whose NLAlib counterpart exists holds proposed **additions** to
that file; "new" marks a proposed new file. The design note `docs/design/Proposals.md` gives the
exact statements, placement, searches of Mathlib/NLAlib, consumers and open questions, as NLAlib's
process (§8) requires.

| File (under `ForNLALib/`) | Declarations | Proposed home in NLAlib | Ported from (`../TubalAlgebra`) |
|---|---|---|---|
| `ForMathlib/LinearAlgebra/Matrix/IsDiag.lean` | `Matrix.isDiag_of_commute_diagonal`, `Matrix.commute_diagonal_iff_isDiag` | `ForMathlib` (upstream candidate for `Mathlib.LinearAlgebra.Matrix.IsDiag`), new | `Tubal.AppB.isDiag_of_commute_diagonal` |
| `Matrix/Spectral/Diagonalizable.lean` | `IsDiagonalizable.squarefree_minpoly`, `isDiagonalizable_of_squarefree_aeval_eq_zero`, `isDiagonalizable_iff_squarefree_minpoly`, `isDiag_inv_mul_mul_of_commute` | `NLAlib/Matrix/Spectral/Diagonalizable.lean` | `Tubal.isDiagonalizableMat_of_squarefree`, step of `Tubal.algorithm1_correct` |
| `Matrix/Spectral/SVD.lean` | `IsSVD.exists_eq_fromCols_mul_fromBlocks_mul_conjTranspose`, `isSVD_of_eq_fromCols_mul_fromBlocks_mul_conjTranspose`, `exists_eq_fromCols_mul_fromBlocks_mul_conjTranspose` (full SVD in block form) | `NLAlib/Matrix/Spectral/SVD.lean` | `Tubal.exists_svd`, `Tubal.IsSVD` |
| `Matrix/Spectral/BestRankApprox.lean` | `IsSVD.frobNorm_sub_mul_diagonal_mul_conjTranspose_sq`, `IsSVD.isBestRankApprox_mul_diagonal_mul_conjTranspose` (Eckart–Young for any sorted thin SVD) | `NLAlib/Matrix/Spectral/BestRankApprox.lean` | `Tubal.eckart_young`, `Tubal.IsSVD.frobSq_sub_truncProd` |
| `Matrix/Structured/Circulant.lean` | `conjTranspose_fourierMatrix_mulVec_circulant_mulVec` (convolution theorem) | `NLAlib/Matrix/Structured/Circulant.lean` | `Tubal.example16` |
| `Matrix/Structured/Walsh.lean` | `walshHadamard_mulVec_sum_mul_add` (XOR convolution) | `NLAlib/Matrix/Structured/Walsh.lean` | `Tubal.example18_xor` |
| `Matrix/Structured/Vandermonde.lean` | `vandermonde_mulVec_apply`, `dvd_sub_mul_iff_vandermonde_mulVec_eq_mul` (multiplication mod $Q$ = entrywise product at the roots) | `NLAlib/Matrix/Structured/Vandermonde.lean`, new | `Tubal.example17`, `Tubal.eq3` |
| `Probability/GenericPosition.lean` | `ae_injective_mulVec_ofReal_of_absolutelyContinuous`, `ae_injective_mulVec_ofReal`, `ae_injective_of_mul_eq_mul_diagonal`, `ae_isDiag_inv_mul_mul_of_mul_eq_mul_diagonal` (randomized simultaneous diagonalization) | `NLAlib/Probability/GenericPosition.lean`, new | `Tubal.AppB.ae_injective_mulVec`, `Tubal.algorithm1_ae` |

19 public declarations, 853 lines. Everything is in `namespace NLAlib`, except the `ForMathlib`
file (namespace `Matrix`). Each statement is stated in NLAlib's form, not the formalization's:
- arbitrary `Fintype` index types instead of `Fin n`;
- `RCLike 𝕜` instead of `ℂ` where the mathematics allows;
- NLAlib's interfaces (`IsSVD`, `HasOrthonormalCols`, `IsBestRankApprox`, `IsDiagonalizable`);
- Mathlib objects (`Polynomial.ofFn`, `Matrix.vandermonde`, `Matrix.circulant`) instead of local
  definitions.

The proofs are new, mostly short derivations from the NLAlib and Mathlib API, as NLAlib asks (§7).
The corresponding material in the formalization takes roughly 1,100 lines, most of it
`MatrixSVD.lean`.

## Not included

- **Already in NLAlib:**
  - Frobenius-norm invariance under orthonormal factors (`HasOrthonormalCols.frobNorm_mul_left`, `…_mul_conjTranspose_right`);
  - SVD existence;
  - Eckart–Young for the canonical truncation and its error formula (`isBestRankApprox_truncatedSVD`, `frobNorm_sub_truncatedSVD_sq`);
  - simultaneous diagonalization of commuting families;
  - unitarity of the Fourier matrix and circulant diagonalization;
  - the Hermitian spectral theorem.
- **Belongs elsewhere:** the Frobenius theorem on real division algebras (Mathlib, not NLAlib).
- **Decided against:** Lemma 63 of the paper (conjugate row patterns of $\mathbf{M}$ and columns of
  $\mathbf{M}^{-1}$), and all tubal tensor material, which stays in `../TubalAlgebra/`.

## Building

```bash
cd ForNLALib
lake exe cache get                       # Mathlib v4.33.1 oleans (never build Mathlib)
LEAN_NUM_THREADS=2 lake build ForNLALib  # builds the needed NLAlib modules, then these files
```

The first build compiles the NLAlib modules these files import, which takes a while.
Check a single file with `lake lean ForNLALib/<path>.lean -- -M 6000`, which applies the
lakefile's options and NLAlib's linters, unlike `lake env lean`.

## Verification

- `lake build ForNLALib` succeeds with no errors and no warnings. The lakefile has NLAlib's options:
  `autoImplicit = false`, `linter.missingDocs`, Mathlib's standard linter set, the header linter.
- No `sorry`, `admit`, `axiom` or `native_decide`. `#print axioms` on all 19 public declarations
  reports only `propext`, `Classical.choice`, `Quot.sound`.
- Each group of files was reviewed independently against the design note and NLAlib's
  CONTRIBUTING. The review covered statements, names (§4), statement shape (§5), docstrings and
  citations (§6), and duplicates in Mathlib and NLAlib. All passed. The few deviations from the
  first draft of the note are recorded as amendments in `docs/design/Proposals.md` §5.
- **Not run:** NLAlib's CI scripts (`scripts/Audit.lean`, `Lint.lean`, `check_refs.py`,
  `check_latex.mjs`, `Duplicates.lean`). They work on NLAlib's own tree and should be run when the
  files are moved there.

## Upstreaming

NLAlib's process (§8–§9):
1. The design note goes to the maintainer first.
2. One topic per pull request. A natural split:
   1. `IsDiag` + `Diagonalizable`;
   2. `SVD` + `BestRankApprox`;
   3. `Circulant` + `Walsh`;
   4. `Vandermonde`;
   5. `GenericPosition`.
3. To move a file, paste its declarations into the NLAlib file named in the table, and change
   `ForNLALib.…` imports to `NLAlib.…`.
4. Drop the sentence "proposed additions" from the module docstrings, and merge the "Main results"
   lists.
5. The docstring of `dvd_sub_mul_iff_vandermonde_mulVec_eq_mul` refers to the convolution theorem
   of the `Circulant` proposal; drop that reference if that proposal is not accepted.
6. Citations are kept only where NLAlib already uses the same label for the related result. The
   others have provenance lines only and may need citations added.
