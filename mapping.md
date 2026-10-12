# Mapping: paper results → Lean declarations

Paper: H. Avron, U. Mor, *Demystifying Tubal Tensor Algebra* (arXiv:2506.03311v2).
Lean project: `TubalAlgebra` (Lean 4 v4.34.1, Mathlib v4.34.1). All declarations live in the
namespace `Tubal` (the Appendix A examples in `Tubal.AppendixA`, the tubal-ring lemmas of
Section 9 in `Tubal.TubalRing`). Build with `lake build`.

**Status:** every numbered result is formalized and fully proved — there is no `sorry`, no
`admit`, no `native_decide`, and **no axiom beyond Lean's standard `propext`,
`Classical.choice`, `Quot.sound`** (not even for the classical results the paper cites: the
Frobenius theorem, simultaneous diagonalization, matrix SVD and the Eckart–Young theorem are all
proved). `python3 scripts/axiom_audit.py` runs `#print axioms` on all 484 public declarations
and checks this.

Every numbered result of the paper is listed below, in order, with the Lean declaration(s) that
formalize it. **Deviations** from the literal text (typos in the paper, implicit assumptions)
are marked with ⚠ and explained; the section *Deviations* at the end collects them.

The last column of each table, *Human Verified?*, is left blank for manual review.

## Conventions used throughout

| Paper | Lean | Human Verified? |
|---|---|---|
| vectors `ℝⁿ`, `ℂⁿ`; entries `1..n` | `Fin n → ℝ`, `Fin n → ℂ`; indices `0..n-1` |  |
| embedding `ℝⁿ ⊂ ℂⁿ` | `toC` |  |
| Hadamard product `x • y` | pointwise product `x * y` of functions |  |
| Eq. (5) `a ⋆_M b = M⁻¹(Ma • Mb)` | `starMC M a b` (`Defs.lean`) |  |
| "every row of `M` is real or the conjugate of exactly one other row" | `ConjRowCondition M` (`RowReal`, `RowConjOf`) |  |
| standing hypothesis "`M` invertible + row condition" | `Admissible M`, used as `[Fact (Admissible M)]` |  |
| the ring `𝕂_M` (tubes `ℝⁿ` with `+`, `⋆_M`) | the type `KM M` with `KM.instCommRing`, `KM.instAlgebra`, `KM.instStarRing` |  |
| transform `â = M a` | `KM.hat` |  |
| `a ≤_M b` (`M(b-a)` real and `≥ 0`) | `≤` on `KM M` (`KM.le_def`) |  |
| `𝕂_M^m` (oriented matrices) | `Fin m → KM M` |  |
| tensors `𝕂_M^{m×p}` ≅ `ℝ^{m×p×n}` | `Matrix (Fin m) (Fin p) (KM M)` (`toTensor`/`ofTensor`) |  |
| `𝒜 ⋆_M ℬ`, `𝒜 ⋆_M X` | Mathlib `Matrix` product `A * B`, `A *ᵥ X` over `KM M` |  |
| `𝒜ᴴ` | `Aᴴ` (`Matrix.conjTranspose` w.r.t. the `⋆_M`-conjugate) |  |
| `𝒜̂ = 𝒜 ×₃ M`, frontal slice `𝒜̂_j` | `tHat A j` (`= mode3 …`, `tHat_eq_mode3`) |  |
| a tubal ring `(ℝⁿ, +, ·)` | `T : TubalRing n` with product `T.mul` |  |

`KM M` carries the multiplication/unit/conjugate defined as the real parts of Eq. (5), `M⁻¹e`
and Eq. (6); `KM.toC_vec_mul`, `KM.toC_vec_one`, `KM.toC_vec_star`, `KM.toC_vec_weakInv` show
that, under admissibility, these complex vectors *are* real, i.e. the operations are exactly
those of the paper.

## Section 3: Algebra of tubes

| Paper | Lean (file) | Human Verified? |
|---|---|---|
| **Theorem 1** (Frobenius) | `theorem1_frobenius` (`Frobenius.lean`) — fully proved (no axiom); commutative case `finrank_field_over_real` |  |
| Eq. (3) (`P_c = P_a P_b mod (Xⁿ-1) ⟺ F_n c = F_n a • F_n b`) ⚠ | `eq3` (`Examples/Section3b.lean`) |  |
| Eq. (5) | `starMC` (`Defs.lean`) |  |
| **Lemma 2** | `lemma2` (`Realness.lean`; identical to Lemma 65) |  |
| **Theorem 3** | `theorem3` (existence of a `CommRing` structure on `Fin n → ℝ` whose `+` is vector addition and whose product is `⋆_M`), `theorem3_KM`, instance `KM.instCommRing` (`KMRing.lean`) |  |
| **Example 4** | `example4`, `M4`, `M4_admissible`, `example4_isField`, `complexTubal`, `example4_no_real_M` (`Examples/Section3.lean`); "the last theorem does not hold if we restrict `M` to be real": `theorem11_not_real` (`Section9/Main.lean`) |  |
| **Proposition 5** ⚠ | `prop5` (`NotField.lean`); `dim_ℝ 𝕂_M = n`: `KM.finrank_eq` |  |
| partial order `≤_M` ("easy to verify") | `KM.le_def`, `le_isPartialOrder` (`KMRing.lean`) |  |
| Eq. (6) (`a* = M⁻¹ conj(Ma)`) | `Star (KM M)`, `KM.toC_vec_star`, `KM.hat_star` |  |
| **Proposition 6** | `prop6`, instance `KM.instStarRing` (`KMRing.lean`) |  |
| `x⁺`, Eq. (7) (`a⁻ = M⁻¹(Ma)⁺`) | `pinvVec`, `KM.weakInv`, `KM.toC_vec_weakInv` |  |
| **Lemma 7** | `lemma7` (`Realness.lean`) |  |
| **Lemma 8** | `lemma8` (`KMRing.lean`); "the first property makes the ring von Neumann regular": `KM.isVonNeumannRegularRing`; "if `a` is invertible, `a⁻` is its inverse": `KM.weakInv_eq_inverse` |  |
| **Definition 9** | `IsVonNeumannRegularRing` (`Defs.lean`); the remark after it (uniqueness of `x` with `a = axa`, `x = xax` in a commutative VN-regular ring): `vonNeumann_unique` (`TubalRing.lean`) |  |
| **Definition 10** | `TubalRing` (`TubalRing.lean`) |  |
| **Theorem 11** (Main Result) | `theorem11` (`Section9/Main.lean`); also `theorem11_admissible` (the `M` satisfies the row condition), converse `exists_tubalRing_of_starM`, `KM.toTubalRing` (`TubalRing.lean`) |  |
| **Definition 12** | `realness`, `IsRealLike` (`Defs.lean`) |  |
| **Proposition 13** | `prop13` (`Canonical.lean`) |  |
| remarks after Prop. 13 | `realness_le_and_parity` (`r ≡ n mod 2`), `star_eq_self_of_realLike` (`a* = a` for real-like rings) (`Canonical.lean`); "there are, up to isomorphism, `⌊n/2⌋+1` tubal rings": `tubalRing_count` (`Count.lean`, including non-isomorphism of different realness, which the paper does not prove) |  |
| **Example 14** | `example14_classification` (every commutative ring over `ℝ²` is ≅ ℂ, split-complex or dual numbers), `splitCommAlg`, `example14_weakInv`, `splitTubal`, `example14` (`⋆_M` with `M = [[1,1],[1,-1]]`), `example14_dft` (= DFT for `n = 2`) |  |
| **Example 15** | `dualCommAlg`, `example15_eps`, `example15_not_tubal`, `example15_no_M`, `example15_not_iso` (ring-isomorphism reading) |  |
| **Example 16** | `circ`, `tProd`, `dftMatrix`, `dftMatrix_admissible`, `example16_circ_algebra`, `example16` |  |
| **Example 17** | `polyOf`, `example17` (`P_c ≡ P_a P_b mod Q ⟺ Mc = Ma • Mb`, `M` = Vandermonde at the roots), `polyModMul`, `example17_tubal` (the mod-`Q` product is a tubal ring, Section 3.2), `skewFourier`, `example17_skewFourier`, `example17_two`, `example17_field`, `example17_complex_quotient` (`Examples/Section3b.lean`) |  |
| **Example 18** ⚠ | `groupConv`, `example18`, `example18_tProduct`, `xorConv`, `walshHadamard`, `example18_xor`; typo evidence: `xorConvLiteral`, `example18_literal_not_comm` (`Examples/Section3b.lean`) |  |

## Section 4: Module of oriented matrices

| Paper | Lean (`Module.lean`) | Human Verified? |
|---|---|---|
| squeeze / twist (`𝕂_M^m ≅ ℝ^{m×n}`) | `squeeze`, `twist`, `orientedEquiv` |  |
| **Theorem 19** ⚠ | `theorem19` (free; basis `E_i` = `stdOriented`; every basis has `m` elements and `finrank = m` when `n ≠ 0`) |  |
| Eq. (8) | `dotM` |  |
| **Theorem 20** | `theorem20`; key step `star_mul_self_nonneg` |  |

## Section 5: Tensors as matrices over `𝕂_M`

| Paper | Lean (`Tensor.lean`) | Human Verified? |
|---|---|---|
| `(𝒜 ⋆_M ℬ)_{ij} = ∑ₖ 𝒜_{ik} ⋆_M ℬ_{kj}` | `tensor_mul_apply` |  |
| **Definition 21** | `IsStarMLinear`, `IsStarMLinearMat` |  |
| **Remark 22** | `remark22_smul_eq`, `remark22_linear`, `remark22_linear_mat`, `remark22_converse_false` (⚠ see deviations), `remark22_converse_false'` |  |
| unnumbered claims after Remark 22 | `isStarMLinearMat_of_tensor`, `exists_tensor_of_isStarMLinearMat`, `tensor_comp`, `isStarMLinear_comp`, `isStarMLinearMat_comp` |  |
| Section 5.1 (`*`-algebra; `(𝒜⋆ℬ)ᴴ = ℬᴴ⋆𝒜ᴴ`) | `tensor_starAlgebra`, `conjTranspose_tensor_mul`, `conjTranspose_tensor_apply` |  |
| **Definition 23** ⚠ | `IsStarMAdjoint`, `isStarMAdjoint_unique`, `exists_isStarMAdjoint` |  |
| **Proposition 24** | `prop24` |  |

## Section 6: Practical tubal algebra

| Paper | Lean (`Transform.lean`) | Human Verified? |
|---|---|---|
| facewise product, `𝒜̂ = 𝒜 ×₃ M` | `facewise`, `facewiseReal`, `mode3`, `tHat`, `tHat_eq_mode3` |  |
| **Fact 25** | `fact25`, `tHat_mul`, `tHat_injective` |  |
| **Example 26** | `identityTensor`, `example26` |  |
| **Example 27** | `example27` |  |
| inverse transform (used later) | `tInv`, `tHat_tInv`, `tInv_tHat`, `SlicesConjPattern` |  |

## Section 7: Tubal SVD and Eckart–Young

| Paper | Lean | Human Verified? |
|---|---|---|
| matrix SVD / Eckart–Young (classical background) | `IsSVD`, `exists_svd`, `eckart_young`, `IsSVD.frobSq_sub_truncProd`, … (`MatrixSVD.lean`) |  |
| **Definition 28** | `IsStarMUnitary`; "unitary iff facewise unitary": `isStarMUnitary_iff_facewise` (`TSVD.lean`) |  |
| **Definition 29** | `frontal`, `IsFDiagonal` (`TSVD.lean`) |  |
| **Theorem 30** | `theorem30`, `IsTSVD`, `sigma` (`TSVD.lean`) |  |
| **Definition 31** | `tsvdRank`, `starMRank` (`TSVD.lean`) |  |
| **Lemma 32** | `lemma32`, `lemma32_any` (independence of the chosen ⋆_M-SVD) |  |
| **Lemma 33** | `lemma33`, `tnorm`, `tubeNorm` (`EckartYoung.lean`) |  |
| **Corollary 34** | `cor34` |  |
| **Theorem 35** ⚠ | `theorem35`, `truncT` |  |
| **Definition 36** | `multirank`, `RespectsConjPattern`, `multirank_respectsConjPattern` |  |
| **Theorem 37** ⚠ | `theorem37`, `truncSlices`; typo evidence `example68_literal_false` |  |

## Section 9: Proof of Theorem 11

| Paper | Lean | Human Verified? |
|---|---|---|
| preamble (`a⁻` as the unique `x` with `a = axa`, `x = xax`; "the two definitions coincide") | `TubalRing.winv`, `winv_spec`, `winv_unique` (`TubalRing.lean`); `TubalRing.winv_eq_eq7`, `TubalRing.exists_winv_eq_eq7` (`Section9/Main.lean`) |  |
| **Lemma 38** ⚠ | `lemma38` (`Section9/SimulDiag.lean`), with `IsDiagonalizableMat`, `IsJointlyDiagonalizableMat` |  |
| **Definition 39** | `TubalRing.repMat`, `repMat_mulVec`, `repMat_unique`, `TubalRing.Rep` (`Section9/RepMatrix.lean`) |  |
| **Example 40** | `example40` |  |
| **Lemma 41** | `TubalRing.lemma41` |  |
| **Lemma 42** | `TubalRing.lemma42` |  |
| **Lemma 43** | `TubalRing.lemma43` |  |
| **Corollary 44** | `TubalRing.cor44` |  |
| **Definition 45** | `TubalRing.IsIdempotent` |  |
| **Lemma 46** | `TubalRing.lemma46` |  |
| `a · b` for `b ∈ ℂⁿ`; `a · b = R_a b` | `TubalRing.mulC`, `mulC_eq_repMat_mulVec` (`Section9/Diagonalizable.lean`) |  |
| **Definition 47** | `TubalRing.IsEigenvector` |  |
| **Definition 48** | `TubalRing.IsDiagonalizable` |  |
| **Lemma 49** | `TubalRing.lemma49` |  |
| **Definition 50** | `IsDiagonalizableSet`, `IsDiagonalizableRing`, `IsJointlyDiagonalizable`, `IsJointlyDiagonalizableRing` |  |
| **Lemma 51** | `TubalRing.lemma51` |  |
| **Lemma 52** | `TubalRing.lemma52` |  |
| **Lemma 53** | `TubalRing.lemma53` |  |
| **Proposition 54** | `TubalRing.prop54` |  |
| **Definition 55** | `TubalRing.IsTubalSubring` (`Section9/Ideals.lean`) |  |
| **Definition 56** | `TubalRing.principalSet`, `TubalRing.principal` |  |
| **Lemma 57** | `TubalRing.lemma57` |  |
| **Lemma 58** | `TubalRing.lemma58` |  |
| **Lemma 59** | `TubalRing.lemma59`; text after it ("proper subsets, lower dimension"): `finrank_principal_lt` |  |
| division ring / tubal sub-field (Sec. 9.4) | `TubalRing.IsDivisionSubring`, `TubalRing.IsTubalSubfield` |  |
| **Lemma 60** | `TubalRing.lemma60` |  |
| **Corollary 61** | `TubalRing.cor61` |  |
| **Proposition 62** | `TubalRing.prop62` (`Section9/SubField.lean`) |  |
| Section 9.6 (bringing it together) | `TubalRing.isDiagonalizableRing`, `theorem11` (`Section9/Main.lean`) |  |

## Section 10: Additional proofs

| Paper | Lean | Human Verified? |
|---|---|---|
| **Lemma 63** | `lemma63` (`Realness.lean`) |  |
| **Lemma 64** | `lemma64` |  |
| **Lemma 65** | `lemma65` |  |
| Proof of Lemma 7 | `lemma7` |  |
| `M_{n,m}`, `M_{n,m}⁻¹`, `𝕂_{n,m}` | `canonicalM`, `canonicalMInv`, `canonicalM_inv`, `canonicalM_admissible`, `realness_canonicalM` (`Canonical.lean`) |  |
| **Proposition 66** | `prop66`; with conjugation: `prop66_star` |  |

## Appendices

| Paper | Lean | Human Verified? |
|---|---|---|
| **Example 67** | `AppendixA.example67`, `AppendixA.example67_step3` (`Examples/AppendixA.lean`) |  |
| **Example 68** | `AppendixA.example68`, `AppendixA.hadamard2_eq_smul_unitary`, `AppendixA.example68_literal_false` |  |
| Appendix B, weak inverses / nilpotents | `not_vonNeumann_has_nilpotent` (`Examples/AppendixB.lean`) |  |
| **Example 69** | `example69` |  |
| **Algorithm 1** ⚠ | `algorithm1`, `algorithm1_correct`, `algorithm1_exists_good_x`, `algorithm1_ae` |  |
| **Proposition 70** | `prop70` (`Hilbert.lean`) |  |
| **Proposition 71** ⚠ | `prop71`; "easy to build counter examples": `eq9_fails_in_general` |  |

## Deviations from the literal text (all justified)

1. **Lemma 38**: the paper writes "such that, for all `A ∈ ℂ^{n×n}`, `SAS⁻¹` is diagonal" — a typo
   for "for all `A ∈ S`" (the literal statement is false). Formalized with `A ∈ S`.
2. **Theorem 19**: "free of rank `m`" — the rank part ("every basis has `m` elements") uses the
   invariant basis number of `𝕂_M`, which fails for the zero ring (`n = 0`). The rank conjuncts
   therefore carry `n ≠ 0`; freeness and the explicit basis `E_1,…,E_m` hold for all `n`.
3. **Proposition 5**: "not a field unless `n = 1` or `n = 2`, since there are elements without
   inverse": formalized as `¬ IsField (KM M)` for `n ∉ {1,2}`, plus existence of a non-zero
   non-invertible element whenever `n ≠ 0` (for `n = 0` the ring is zero, and has no non-zero
   elements; it is still not a field).
4. **Definition 23**: the paper writes `X ∈ 𝕂_M^m`, `Y ∈ 𝕂_M^p`, which is ill-typed for
   `T : 𝕂_M^p → 𝕂_M^m`; formalized with `X ∈ 𝕂_M^p`, `Y ∈ 𝕂_M^m`.
5. **Remark 22** "the converse is not true": formalized as the negation of the universal
   converse (`remark22_converse_false`), and more sharply for every admissible `M` with `n ≥ 2`
   (`remark22_converse_false'`); for `n = 1` the converse actually holds.
6. **Theorem 35**: the paper's `U_{:,1:r,:} ⋆ S_{1:r,1:r,:} ⋆ V^H_{:,1:r,:}` has `r` for `k`
   (typo) and `V^H_{:,1:k,:}` is read as `(V_{:,1:k,:})ᴴ` (the only well-typed reading). The
   statement also records that `[𝒜]_k` has `⋆_M`-rank `≤ k` (part of "optimal rank-`k`
   approximation").
7. **Theorem 37**: the error formula's factor `|c|⁻¹` is a typo for `|c|⁻²` (Example 68 itself
   uses `|c|⁻²`); `example68_literal_false` proves that the literal formula fails on the
   paper's own Example 68. "multirank-`k`" is a typo for "multirank-`r`". The statement also
   records that `[𝒜]_r` has the prescribed transformed slices and multirank `≤ r`.
8. **Proposition 71** is stated in Appendix C as an extension of Eq. (9) and proved from it, so
   it carries Proposition 70's hypothesis `M = D W` (`D` real invertible diagonal, `W`
   unitary); without it the statement is false (`eq9_fails_in_general`).
9. **Example 18**: the printed XOR product `(a·b)_i = ∑_j a_i b_{i⊕j}` is a typo for
   `∑_j a_j b_{i⊕j}`; `example18_literal_not_comm` shows the printed formula is not even
   commutative.
10. **Eq. (3)**: `Xᵖ - 1` is a typo for `Xⁿ - 1`.
11. **Algorithm 1**: "`M ∈ ℝ^{n×n}`" is a typo; `M` is complex in general (cf. Example 4). The
    random choice of `x` is formalized as an almost-everywhere statement (`algorithm1_ae`).
12. **Appendix B**: "a commutative ring … which is not tubal will be reduced, i.e. has an
    element `n` with `n² = 0`" — "reduced" should read "non-reduced".
13. **Definition 55**: commutativity, associativity, distributivity and ℝ-algebra compatibility
    of `(V, +, ·)` are inherited from the ambient tubal ring, so `IsTubalSubring` only requires
    closure, a unit, von Neumann regularity inside `V`, and the ideal property.
14. **Division ring (Sec. 9.4) / Lemma 60**: as recalled in Section 9.4, "a ring is called a
    division ring if every non-zero element has a multiplicative inverse" (no non-triviality
    requirement); with this reading Lemma 60 is true also for `V = {0}`.
15. **Definition 31**: the `⋆_M`-rank is defined from a chosen `⋆_M`-SVD; `lemma32_any` shows
    it does not depend on the choice.
16. **Theorem 3** is stated as: there is a `CommRing` structure on `ℝⁿ` whose addition is the
    usual one and whose multiplication is `⋆_M` (the ring axioms hold), and additionally via
    the type `KM M`.
17. **Example 15** "no invertible `M` exists that makes dual numbers isomorphic to `ℝ²`":
    formalized both as "the dual product is not `⋆_M` for any invertible `M`"
    (`example15_no_M`) and as "the dual numbers are not ring-isomorphic to any `𝕂_M`"
    (`example15_not_iso`).

## Proof strategy notes

* Proofs need not follow the paper; notable differences: Proposition 62 is proved via
  reducedness (every minimal polynomial in a tubal ring is squarefree, so every `R_a` is
  diagonalizable) instead of the Frobenius dimension argument; Theorem 11 is then assembled
  exactly as in Section 9.6 (Cor. 61 + Prop. 62 + Lemma 53 + Prop. 54). Proposition 13/66 use
  conjugacy of the "conjugation involutions" of the rows.
* Classical background proved from scratch on top of Mathlib (no axioms assumed): the
  Frobenius theorem (`Frobenius.lean`, elementary proof via `i, j, k` with `i² = j² = -1`,
  `ji = -ij`), simultaneous diagonalization (`Section9/SimulDiag.lean`), existence of the SVD
  over `ℝ`/`ℂ` and the Eckart–Young theorem (`MatrixSVD.lean`, via a projector/trace-weight
  argument).
* Theorem 30 for a general admissible `M` requires choosing the slice SVDs consistently with
  the conjugation pattern of `M` (real SVDs for real rows, conjugate SVDs for conjugate rows) so
  that `𝒰, 𝒮, 𝒱` are real; the paper's proof glosses over this, the formal proof does it.

## Verification

* `lake build` — builds the whole library without errors or `sorry` warnings.
* `python3 scripts/axiom_audit.py` — `#print axioms` for all 484 public theorems, lemmas,
  definitions and instances; all depend only on `propext`, `Classical.choice`, `Quot.sound`.
* Statement faithfulness was independently reviewed against the paper (one reviewer per
  section plus a completeness critic, each finding adversarially re-verified); the
  confirmed gaps (all low severity: missing side-claims) were added.
