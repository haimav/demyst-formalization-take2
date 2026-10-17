# Mapping: paper results → Lean declarations

Paper: H. Avron, U. Mor, *Demystifying Tubal Tensor Algebra* (arXiv:2506.03311v2).
Lean project: `TubalAlgebra` (Lean 4 v4.34.1, Mathlib v4.34.1). All declarations live in the
namespace `Tubal` (the Appendix A examples in `Tubal.AppendixA`, the tubal-ring lemmas of
Section 9 in `Tubal.TubalRing` ([TubalAlgebra/TubalRing.lean:34](TubalAlgebra/TubalRing.lean#L34))). Build with `lake build`.

**Status:** every numbered result is formalized and fully proved — there is no `sorry`, no
`admit`, no `native_decide`, and **no axiom beyond Lean's standard `propext`,
`Classical.choice`, `Quot.sound`** (not even for the classical results the paper cites: the
Frobenius theorem, simultaneous diagonalization, matrix SVD and the Eckart–Young theorem are all
proved). `python3 scripts/axiom_audit.py` runs `#print axioms` on all 488 public declarations
and checks this.

Every numbered result of the paper is listed below, in order, with the Lean declaration(s) that
formalize it. **Deviations** from the literal text (typos in the paper, implicit assumptions)
are marked with ⚠ and explained; the section *Deviations* at the end collects them.

Each Lean name is followed by its location as a clickable `path:line` link (relative to the
repository root); after editing the sources, regenerate these links with
`python3 scripts/update_mapping_locations.py`. The last column of each table, *Human Verified?*,
is left blank for manual review.

## Conventions used throughout

| Paper | Lean declaration (file:line) | Human Verified? |
|---|---|---|
| vectors `ℝⁿ`, `ℂⁿ`; entries `1..n` | `Fin n → ℝ`, `Fin n → ℂ`; indices `0..n-1` | YES |
| embedding `ℝⁿ ⊂ ℂⁿ` | `toC` ([TubalAlgebra/Defs.lean:34](TubalAlgebra/Defs.lean#L34)) | YES |
| "`v ∈ ℝⁿ`" for a complex vector `v` (e.g. "`a ⋆_M b ∈ ℝⁿ`" in Lemmas 2, 7) | `v ∈ realVectors n`, where `realVectors n := Set.range toC` ([TubalAlgebra/Defs.lean:48](TubalAlgebra/Defs.lean#L48)); equivalently `∀ i, (v i).im = 0` (`mem_realVectors_iff_im` ([TubalAlgebra/Defs.lean:55](TubalAlgebra/Defs.lean#L55))) or `∀ i, conj (v i) = v i` (`mem_realVectors_iff_conj` ([TubalAlgebra/Defs.lean:65](TubalAlgebra/Defs.lean#L65))) | YES |
| Hadamard product `x • y` | pointwise product `x * y` of functions | YES |
| Eq. (5) `a ⋆_M b = M⁻¹(Ma • Mb)` | `starMC M a b` ([TubalAlgebra/Defs.lean:72](TubalAlgebra/Defs.lean#L72)) | YES |
| "every row of `M` is real or the conjugate of exactly one other row" | `ConjRowCondition M` ([TubalAlgebra/Defs.lean:85](TubalAlgebra/Defs.lean#L85)) (`RowReal` ([TubalAlgebra/Defs.lean:76](TubalAlgebra/Defs.lean#L76)), `RowConjOf` ([TubalAlgebra/Defs.lean:80](TubalAlgebra/Defs.lean#L80))) | YES |
| standing hypothesis "`M` invertible + row condition" | `Admissible M` ([TubalAlgebra/Defs.lean:90](TubalAlgebra/Defs.lean#L90)), used as `[Fact (Admissible M)]` | YES |
| the ring `𝕂_M` (tubes `ℝⁿ` with `+`, `⋆_M`) | the type `KM M` ([TubalAlgebra/Defs.lean:108](TubalAlgebra/Defs.lean#L108)) with `KM.instCommRing` ([TubalAlgebra/KMRing.lean:160](TubalAlgebra/KMRing.lean#L160)), `KM.instAlgebra` ([TubalAlgebra/KMRing.lean:173](TubalAlgebra/KMRing.lean#L173)), `KM.instStarRing` ([TubalAlgebra/KMRing.lean:188](TubalAlgebra/KMRing.lean#L188)) | YES |
| transform `â = M a` | `KM.hat` ([TubalAlgebra/Defs.lean:168](TubalAlgebra/Defs.lean#L168)) | YES |
| `a ≤_M b` (`M(b-a)` real and `≥ 0`) | `≤` on `KM M` ([TubalAlgebra/Defs.lean:108](TubalAlgebra/Defs.lean#L108)) (`KM.le_def` ([TubalAlgebra/Defs.lean:200](TubalAlgebra/Defs.lean#L200))) | YES |
| `𝕂_M^m` (oriented matrices) | `Fin m → KM M` | YES |
| tensors `𝕂_M^{m×p}` ≅ `ℝ^{m×p×n}` | `Matrix (Fin m) (Fin p) (KM M)` (`toTensor` ([TubalAlgebra/Tensor.lean:25](TubalAlgebra/Tensor.lean#L25))/`ofTensor` ([TubalAlgebra/Tensor.lean:29](TubalAlgebra/Tensor.lean#L29))) | YES |
| `𝒜 ⋆_M ℬ`, `𝒜 ⋆_M X` | Mathlib `Matrix` product `A * B`, `A *ᵥ X` over `KM M` ([TubalAlgebra/Defs.lean:108](TubalAlgebra/Defs.lean#L108)) | YES |
| `𝒜ᴴ` | `Aᴴ` (`Matrix.conjTranspose` w.r.t. the `⋆_M`-conjugate) | YES |
| `𝒜̂ = 𝒜 ×₃ M`, frontal slice `𝒜̂_j` | `tHat A j` ([TubalAlgebra/Transform.lean:27](TubalAlgebra/Transform.lean#L27)) (`= mode3 …`, `tHat_eq_mode3` ([TubalAlgebra/Transform.lean:31](TubalAlgebra/Transform.lean#L31))) | YES |
| a tubal ring `(ℝⁿ, +, ·)` | `T : TubalRing n` with product `T.mul` | YES |

`KM M` ([TubalAlgebra/Defs.lean:108](TubalAlgebra/Defs.lean#L108)) carries the multiplication/unit/conjugate defined as the real parts of Eq. (5), `M⁻¹e`
and Eq. (6); `KM.toC_vec_mul` ([TubalAlgebra/KMRing.lean:106](TubalAlgebra/KMRing.lean#L106)), `KM.toC_vec_one` ([TubalAlgebra/KMRing.lean:109](TubalAlgebra/KMRing.lean#L109)), `KM.toC_vec_star` ([TubalAlgebra/KMRing.lean:114](TubalAlgebra/KMRing.lean#L114)), `KM.toC_vec_weakInv` ([TubalAlgebra/KMRing.lean:119](TubalAlgebra/KMRing.lean#L119)) show
that, under admissibility, these complex vectors *are* real, i.e. the operations are exactly
those of the paper.

## Section 3: Algebra of tubes

| Paper | Lean declaration (file:line) | Human Verified? |
|---|---|---|
| **Theorem 1** (Frobenius) | `theorem1_frobenius` ([TubalAlgebra/Frobenius.lean:186](TubalAlgebra/Frobenius.lean#L186)) — fully proved (no axiom); commutative case `finrank_field_over_real` ([TubalAlgebra/Frobenius.lean:226](TubalAlgebra/Frobenius.lean#L226)) | YES |
| Eq. (3) (`P_c = P_a P_b mod (Xⁿ-1) ⟺ F_n c = F_n a • F_n b`) ⚠ | `eq3` ([TubalAlgebra/Examples/Section3b.lean:165](TubalAlgebra/Examples/Section3b.lean#L165)) | YES |
| Eq. (5) | `starMC` ([TubalAlgebra/Defs.lean:72](TubalAlgebra/Defs.lean#L72)) | YES |
| **Lemma 2** | `lemma2` ([TubalAlgebra/Realness.lean:409](TubalAlgebra/Realness.lean#L409)) (identical to Lemma 65) |  YES |
| **Theorem 3** | `theorem3` ([TubalAlgebra/KMRing.lean:203](TubalAlgebra/KMRing.lean#L203)) (existence of a `CommRing` structure on `Fin n → ℝ` whose `+` is vector addition and whose product is `⋆_M`), `theorem3_KM` ([TubalAlgebra/KMRing.lean:213](TubalAlgebra/KMRing.lean#L213)), instance `KM.instCommRing` ([TubalAlgebra/KMRing.lean:160](TubalAlgebra/KMRing.lean#L160)) | YES |
| **Example 4** | `example4` ([TubalAlgebra/Examples/Section3.lean:59](TubalAlgebra/Examples/Section3.lean#L59)), `M4` ([TubalAlgebra/Examples/Section3.lean:48](TubalAlgebra/Examples/Section3.lean#L48)), `M4_admissible` ([TubalAlgebra/Examples/Section3.lean:65](TubalAlgebra/Examples/Section3.lean#L65)), `example4_isField` ([TubalAlgebra/Examples/Section3.lean:87](TubalAlgebra/Examples/Section3.lean#L87)), `complexTubal` ([TubalAlgebra/Examples/Section3.lean:173](TubalAlgebra/Examples/Section3.lean#L173)), `example4_no_real_M` ([TubalAlgebra/Examples/Section3.lean:146](TubalAlgebra/Examples/Section3.lean#L146)); "the last theorem does not hold if we restrict `M` to be real": `theorem11_not_real` ([TubalAlgebra/Section9/Main.lean:90](TubalAlgebra/Section9/Main.lean#L90)) | YES |
| **Proposition 5** ⚠ | `prop5` ([TubalAlgebra/NotField.lean:21](TubalAlgebra/NotField.lean#L21)); `dim_ℝ 𝕂_M = n`: `KM.finrank_eq` ([TubalAlgebra/KMRing.lean:337](TubalAlgebra/KMRing.lean#L337)) | YES |
| partial order `≤_M` ("easy to verify") | `KM.le_def` ([TubalAlgebra/Defs.lean:200](TubalAlgebra/Defs.lean#L200)), `le_isPartialOrder` ([TubalAlgebra/KMRing.lean:235](TubalAlgebra/KMRing.lean#L235)) | YES |
| Eq. (6) (`a* = M⁻¹ conj(Ma)`) | `Star (KM M)`, `KM.toC_vec_star` ([TubalAlgebra/KMRing.lean:114](TubalAlgebra/KMRing.lean#L114)), `KM.hat_star` ([TubalAlgebra/KMRing.lean:130](TubalAlgebra/KMRing.lean#L130)) | YES |
| **Proposition 6** | `prop6` ([TubalAlgebra/KMRing.lean:223](TubalAlgebra/KMRing.lean#L223)), instance `KM.instStarRing` ([TubalAlgebra/KMRing.lean:188](TubalAlgebra/KMRing.lean#L188)) | YES  |
| `x⁺`, Eq. (7) (`a⁻ = M⁻¹(Ma)⁺`) | `pinvVec` ([TubalAlgebra/Defs.lean:100](TubalAlgebra/Defs.lean#L100)), `KM.weakInv` ([TubalAlgebra/Defs.lean:193](TubalAlgebra/Defs.lean#L193)), `KM.toC_vec_weakInv` ([TubalAlgebra/KMRing.lean:119](TubalAlgebra/KMRing.lean#L119)) | YES |
| **Lemma 7** | `lemma7` ([TubalAlgebra/Realness.lean:416](TubalAlgebra/Realness.lean#L416)) | YES |
| **Lemma 8** | `lemma8` ([TubalAlgebra/KMRing.lean:264](TubalAlgebra/KMRing.lean#L264)); "the first property makes the ring von Neumann regular": `KM.isVonNeumannRegularRing` ([TubalAlgebra/KMRing.lean:320](TubalAlgebra/KMRing.lean#L320)); "if `a` is invertible, `a⁻` is its inverse": `KM.weakInv_eq_inverse` ([TubalAlgebra/KMRing.lean:326](TubalAlgebra/KMRing.lean#L326)) |  |
| **Definition 9** | `IsVonNeumannRegularRing` ([TubalAlgebra/Defs.lean:104](TubalAlgebra/Defs.lean#L104)); the remark after it (uniqueness of `x` with `a = axa`, `x = xax` in a commutative VN-regular ring): `vonNeumann_unique` ([TubalAlgebra/TubalRing.lean:56](TubalAlgebra/TubalRing.lean#L56)) | YES |
| **Definition 10** | `TubalRing` ([TubalAlgebra/TubalRing.lean:34](TubalAlgebra/TubalRing.lean#L34)) | YES |
| **Theorem 11** (Main Result) | `theorem11` ([TubalAlgebra/Section9/Main.lean:44](TubalAlgebra/Section9/Main.lean#L44)); also `theorem11_admissible` ([TubalAlgebra/Section9/Main.lean:51](TubalAlgebra/Section9/Main.lean#L51)) (the `M` satisfies the row condition), converse `exists_tubalRing_of_starM` ([TubalAlgebra/TubalRing.lean:294](TubalAlgebra/TubalRing.lean#L294)), `KM.toTubalRing` ([TubalAlgebra/TubalRing.lean:259](TubalAlgebra/TubalRing.lean#L259)) | YES |
| **Definition 12** | `realness` ([TubalAlgebra/Defs.lean:94](TubalAlgebra/Defs.lean#L94)), `IsRealLike` ([TubalAlgebra/Defs.lean:97](TubalAlgebra/Defs.lean#L97)) | YES |
| **Proposition 13** | `prop13` ([TubalAlgebra/Canonical.lean:368](TubalAlgebra/Canonical.lean#L368)) |  YES |
| remarks after Prop. 13 | `realness_le_and_parity` ([TubalAlgebra/Canonical.lean:339](TubalAlgebra/Canonical.lean#L339)) (`r ≡ n mod 2`), `star_eq_self_of_realLike` ([TubalAlgebra/Canonical.lean:374](TubalAlgebra/Canonical.lean#L374)) (`a* = a` for real-like rings); "there are, up to isomorphism, `⌊n/2⌋+1` tubal rings": `tubalRing_count` ([TubalAlgebra/Count.lean:138](TubalAlgebra/Count.lean#L138)) (including non-isomorphism of different realness, which the paper does not prove) | YES |
| **Example 14** | `example14_classification` ([TubalAlgebra/Examples/Section3.lean:243](TubalAlgebra/Examples/Section3.lean#L243)) (every commutative ring over `ℝ²` is ≅ ℂ, split-complex or dual numbers), `splitCommAlg` ([TubalAlgebra/Examples/Section3.lean:329](TubalAlgebra/Examples/Section3.lean#L329)), `example14_weakInv` ([TubalAlgebra/Examples/Section3.lean:350](TubalAlgebra/Examples/Section3.lean#L350)), `splitTubal` ([TubalAlgebra/Examples/Section3.lean:367](TubalAlgebra/Examples/Section3.lean#L367)), `example14` ([TubalAlgebra/Examples/Section3.lean:409](TubalAlgebra/Examples/Section3.lean#L409)) (`⋆_M` with `M = [[1,1],[1,-1]]`), `example14_dft` ([TubalAlgebra/Examples/Section3.lean:420](TubalAlgebra/Examples/Section3.lean#L420)) (= DFT for `n = 2`) | YES |
| **Example 15** | `dualCommAlg` ([TubalAlgebra/Examples/Section3.lean:430](TubalAlgebra/Examples/Section3.lean#L430)), `example15_eps` ([TubalAlgebra/Examples/Section3.lean:449](TubalAlgebra/Examples/Section3.lean#L449)), `example15_not_tubal` ([TubalAlgebra/Examples/Section3.lean:453](TubalAlgebra/Examples/Section3.lean#L453)), `example15_no_M` ([TubalAlgebra/Examples/Section3.lean:462](TubalAlgebra/Examples/Section3.lean#L462)), `example15_not_iso` ([TubalAlgebra/Examples/Section3.lean:485](TubalAlgebra/Examples/Section3.lean#L485)) (ring-isomorphism reading) | YES |
| **Example 16** | `circ` ([TubalAlgebra/Examples/Section3.lean:506](TubalAlgebra/Examples/Section3.lean#L506)), `tProd` ([TubalAlgebra/Examples/Section3.lean:509](TubalAlgebra/Examples/Section3.lean#L509)), `dftMatrix` ([TubalAlgebra/Examples/Section3.lean:415](TubalAlgebra/Examples/Section3.lean#L415)), `dftMatrix_admissible` ([TubalAlgebra/Examples/Section3.lean:583](TubalAlgebra/Examples/Section3.lean#L583)), `example16_circ_algebra` ([TubalAlgebra/Examples/Section3.lean:669](TubalAlgebra/Examples/Section3.lean#L669)), `example16` ([TubalAlgebra/Examples/Section3.lean:680](TubalAlgebra/Examples/Section3.lean#L680)) | YES |
| **Example 17** | `polyOf` ([TubalAlgebra/Examples/Section3b.lean:18](TubalAlgebra/Examples/Section3b.lean#L18)), `example17` ([TubalAlgebra/Examples/Section3b.lean:68](TubalAlgebra/Examples/Section3b.lean#L68)) (`P_c ≡ P_a P_b mod Q ⟺ Mc = Ma • Mb`, `M` = Vandermonde at the roots), `polyModMul` ([TubalAlgebra/Examples/Section3b.lean:87](TubalAlgebra/Examples/Section3b.lean#L87)), `example17_tubal` ([TubalAlgebra/Examples/Section3b.lean:108](TubalAlgebra/Examples/Section3b.lean#L108)) (the mod-`Q` product is a tubal ring, Section 3.2), `skewFourier` ([TubalAlgebra/Examples/Section3b.lean:178](TubalAlgebra/Examples/Section3b.lean#L178)), `example17_skewFourier` ([TubalAlgebra/Examples/Section3b.lean:183](TubalAlgebra/Examples/Section3b.lean#L183)), `example17_two` ([TubalAlgebra/Examples/Section3b.lean:207](TubalAlgebra/Examples/Section3b.lean#L207)), `example17_field` ([TubalAlgebra/Examples/Section3b.lean:220](TubalAlgebra/Examples/Section3b.lean#L220)), `example17_complex_quotient` ([TubalAlgebra/Examples/Section3b.lean:256](TubalAlgebra/Examples/Section3b.lean#L256)) | YES |
| **Example 18** ⚠ | `groupConv` ([TubalAlgebra/Examples/Section3b.lean:275](TubalAlgebra/Examples/Section3b.lean#L275)), `example18` ([TubalAlgebra/Examples/Section3b.lean:302](TubalAlgebra/Examples/Section3b.lean#L302)), `example18_tProduct` ([TubalAlgebra/Examples/Section3b.lean:331](TubalAlgebra/Examples/Section3b.lean#L331)), `xorConv` ([TubalAlgebra/Examples/Section3b.lean:349](TubalAlgebra/Examples/Section3b.lean#L349)), `walshHadamard` ([TubalAlgebra/Examples/Section3b.lean:365](TubalAlgebra/Examples/Section3b.lean#L365)), `example18_xor` ([TubalAlgebra/Examples/Section3b.lean:446](TubalAlgebra/Examples/Section3b.lean#L446)); typo evidence: `xorConvLiteral` ([TubalAlgebra/Examples/Section3b.lean:353](TubalAlgebra/Examples/Section3b.lean#L353)), `example18_literal_not_comm` ([TubalAlgebra/Examples/Section3b.lean:356](TubalAlgebra/Examples/Section3b.lean#L356)) | YES |

## Section 4: Module of oriented matrices

| Paper | Lean declaration (file:line) | Human Verified? |
|---|---|---|
| squeeze / twist (`𝕂_M^m ≅ ℝ^{m×n}`) | `squeeze` ([TubalAlgebra/Module.lean:20](TubalAlgebra/Module.lean#L20)), `twist` ([TubalAlgebra/Module.lean:23](TubalAlgebra/Module.lean#L23)), `orientedEquiv` ([TubalAlgebra/Module.lean:31](TubalAlgebra/Module.lean#L31)) | YES |
| **Theorem 19** ⚠ | `theorem19` ([TubalAlgebra/Module.lean:46](TubalAlgebra/Module.lean#L46)) (free; basis `E_i` = `stdOriented` ([TubalAlgebra/Module.lean:41](TubalAlgebra/Module.lean#L41)); every basis has `m` elements and `finrank = m` when `n ≠ 0`) | YES |
| Eq. (8) | `dotM` ([TubalAlgebra/Module.lean:67](TubalAlgebra/Module.lean#L67)) | YES |
| **Theorem 20** | `theorem20` ([TubalAlgebra/Module.lean:91](TubalAlgebra/Module.lean#L91)); key step `star_mul_self_nonneg` ([TubalAlgebra/Module.lean:71](TubalAlgebra/Module.lean#L71)) | YES |

## Section 5: Tensors as matrices over `𝕂_M`

| Paper | Lean declaration (file:line) | Human Verified? |
|---|---|---|
| `(𝒜 ⋆_M ℬ)_{ij} = ∑ₖ 𝒜_{ik} ⋆_M ℬ_{kj}` | `tensor_mul_apply` ([TubalAlgebra/Tensor.lean:34](TubalAlgebra/Tensor.lean#L34)) | YES |
| **Definition 21** | `IsStarMLinear` ([TubalAlgebra/Tensor.lean:40](TubalAlgebra/Tensor.lean#L40)), `IsStarMLinearMat` ([TubalAlgebra/Tensor.lean:46](TubalAlgebra/Tensor.lean#L46)) | YES |
| **Remark 22** | `remark22_smul_eq` ([TubalAlgebra/Tensor.lean:107](TubalAlgebra/Tensor.lean#L107)), `remark22_linear` ([TubalAlgebra/Tensor.lean:112](TubalAlgebra/Tensor.lean#L112)), `remark22_linear_mat` ([TubalAlgebra/Tensor.lean:121](TubalAlgebra/Tensor.lean#L121)), `remark22_converse_false` ([TubalAlgebra/Tensor.lean:181](TubalAlgebra/Tensor.lean#L181)) (⚠ see deviations), `remark22_converse_false'` ([TubalAlgebra/Tensor.lean:138](TubalAlgebra/Tensor.lean#L138)) | YES |
| unnumbered claims after Remark 22 | `isStarMLinearMat_of_tensor` ([TubalAlgebra/Tensor.lean:196](TubalAlgebra/Tensor.lean#L196)), `exists_tensor_of_isStarMLinearMat` ([TubalAlgebra/Tensor.lean:204](TubalAlgebra/Tensor.lean#L204)), `tensor_comp` ([TubalAlgebra/Tensor.lean:215](TubalAlgebra/Tensor.lean#L215)), `isStarMLinear_comp` ([TubalAlgebra/Tensor.lean:224](TubalAlgebra/Tensor.lean#L224)), `isStarMLinearMat_comp` ([TubalAlgebra/Tensor.lean:233](TubalAlgebra/Tensor.lean#L233)) | YES |
| Section 5.1 (`*`-algebra; `(𝒜⋆ℬ)ᴴ = ℬᴴ⋆𝒜ᴴ`) | `tensor_starAlgebra` ([TubalAlgebra/Tensor.lean:253](TubalAlgebra/Tensor.lean#L253)), `conjTranspose_tensor_mul` ([TubalAlgebra/Tensor.lean:270](TubalAlgebra/Tensor.lean#L270)), `conjTranspose_tensor_apply` ([TubalAlgebra/Tensor.lean:276](TubalAlgebra/Tensor.lean#L276)) | YES |
| **Definition 23** ⚠ | `IsStarMAdjoint` ([TubalAlgebra/Tensor.lean:284](TubalAlgebra/Tensor.lean#L284)), `isStarMAdjoint_unique` ([TubalAlgebra/Tensor.lean:289](TubalAlgebra/Tensor.lean#L289)), `exists_isStarMAdjoint` ([TubalAlgebra/Tensor.lean:313](TubalAlgebra/Tensor.lean#L313)) | YES |
| **Proposition 24** | `prop24` ([TubalAlgebra/Tensor.lean:300](TubalAlgebra/Tensor.lean#L300)) | YES |

## Section 6: Practical tubal algebra

| Paper | Lean declaration (file:line) | Human Verified? |
|---|---|---|
| facewise product, `𝒜̂ = 𝒜 ×₃ M` | `facewise` ([TubalAlgebra/Transform.lean:38](TubalAlgebra/Transform.lean#L38)), `facewiseReal` ([TubalAlgebra/Transform.lean:43](TubalAlgebra/Transform.lean#L43)), `mode3` ([TubalAlgebra/Transform.lean:22](TubalAlgebra/Transform.lean#L22)), `tHat` ([TubalAlgebra/Transform.lean:27](TubalAlgebra/Transform.lean#L27)), `tHat_eq_mode3` ([TubalAlgebra/Transform.lean:31](TubalAlgebra/Transform.lean#L31)) | YES |
| **Fact 25** | `fact25` ([TubalAlgebra/Transform.lean:57](TubalAlgebra/Transform.lean#L57)), `tHat_mul` ([TubalAlgebra/Transform.lean:80](TubalAlgebra/Transform.lean#L80)), `tHat_injective` ([TubalAlgebra/Transform.lean:48](TubalAlgebra/Transform.lean#L48)) | YES |
| **Example 26** | `identityTensor` ([TubalAlgebra/Transform.lean:85](TubalAlgebra/Transform.lean#L85)), `example26` ([TubalAlgebra/Transform.lean:91](TubalAlgebra/Transform.lean#L91)) | YES |
| **Example 27** | `example27` ([TubalAlgebra/Transform.lean:109](TubalAlgebra/Transform.lean#L109)) | YES |
| inverse transform (used later) | `tInv` ([TubalAlgebra/Transform.lean:119](TubalAlgebra/Transform.lean#L119)), `tHat_tInv` ([TubalAlgebra/Transform.lean:132](TubalAlgebra/Transform.lean#L132)), `tInv_tHat` ([TubalAlgebra/Transform.lean:140](TubalAlgebra/Transform.lean#L140)), `SlicesConjPattern` ([TubalAlgebra/Transform.lean:123](TubalAlgebra/Transform.lean#L123)) | YES |

## Section 7: Tubal SVD and Eckart–Young

| Paper | Lean declaration (file:line) | Human Verified? |
|---|---|---|
| matrix SVD / Eckart–Young (classical background) | `IsSVD` ([TubalAlgebra/MatrixSVD.lean:34](TubalAlgebra/MatrixSVD.lean#L34)), `exists_svd` ([TubalAlgebra/MatrixSVD.lean:90](TubalAlgebra/MatrixSVD.lean#L90)), `eckart_young` ([TubalAlgebra/MatrixSVD.lean:687](TubalAlgebra/MatrixSVD.lean#L687)), `IsSVD.frobSq_sub_truncProd` ([TubalAlgebra/MatrixSVD.lean:478](TubalAlgebra/MatrixSVD.lean#L478)), … | YES |
| **Definition 28** | `IsStarMUnitary` ([TubalAlgebra/TSVD.lean:18](TubalAlgebra/TSVD.lean#L18)); "unitary iff facewise unitary": `isStarMUnitary_iff_facewise` ([TubalAlgebra/TSVD.lean:35](TubalAlgebra/TSVD.lean#L35)) | YES |
| **Definition 29** | `frontal` ([TubalAlgebra/TSVD.lean:44](TubalAlgebra/TSVD.lean#L44)), `IsFDiagonal` ([TubalAlgebra/TSVD.lean:50](TubalAlgebra/TSVD.lean#L50)) | YES |
| **Theorem 30** | `theorem30` ([TubalAlgebra/TSVD.lean:172](TubalAlgebra/TSVD.lean#L172)), `IsTSVD` ([TubalAlgebra/TSVD.lean:60](TubalAlgebra/TSVD.lean#L60)), `sigma` ([TubalAlgebra/TSVD.lean:55](TubalAlgebra/TSVD.lean#L55)) | YES |
| **Definition 31** | `tsvdRank` ([TubalAlgebra/TSVD.lean:232](TubalAlgebra/TSVD.lean#L232)), `starMRank` ([TubalAlgebra/TSVD.lean:238](TubalAlgebra/TSVD.lean#L238)) | YES |
| **Lemma 32** | `lemma32` ([TubalAlgebra/TSVD.lean:324](TubalAlgebra/TSVD.lean#L324)), `lemma32_any` ([TubalAlgebra/TSVD.lean:330](TubalAlgebra/TSVD.lean#L330)) (independence of the chosen ⋆_M-SVD) | YES |
| **Lemma 33** | `lemma33` ([TubalAlgebra/EckartYoung.lean:195](TubalAlgebra/EckartYoung.lean#L195)), `tnorm` ([TubalAlgebra/EckartYoung.lean:17](TubalAlgebra/EckartYoung.lean#L17)), `tubeNorm` ([TubalAlgebra/EckartYoung.lean:21](TubalAlgebra/EckartYoung.lean#L21)) | YES |
| **Corollary 34** | `cor34` ([TubalAlgebra/EckartYoung.lean:213](TubalAlgebra/EckartYoung.lean#L213)) | YES |
| **Theorem 35** ⚠ | `theorem35` ([TubalAlgebra/EckartYoung.lean:308](TubalAlgebra/EckartYoung.lean#L308)), `truncT` ([TubalAlgebra/EckartYoung.lean:245](TubalAlgebra/EckartYoung.lean#L245)) | YES |
| **Definition 36** | `multirank` ([TubalAlgebra/EckartYoung.lean:354](TubalAlgebra/EckartYoung.lean#L354)), `RespectsConjPattern` ([TubalAlgebra/EckartYoung.lean:360](TubalAlgebra/EckartYoung.lean#L360)), `multirank_respectsConjPattern` ([TubalAlgebra/EckartYoung.lean:377](TubalAlgebra/EckartYoung.lean#L377)) | YES |
| **Theorem 37** ⚠ | `theorem37` ([TubalAlgebra/EckartYoung.lean:457](TubalAlgebra/EckartYoung.lean#L457)), `truncSlices` ([TubalAlgebra/EckartYoung.lean:392](TubalAlgebra/EckartYoung.lean#L392)); typo evidence `example68_literal_false` ([TubalAlgebra/Examples/AppendixA.lean:354](TubalAlgebra/Examples/AppendixA.lean#L354)) | YES |

## Section 9: Proof of Theorem 11

| Paper | Lean declaration (file:line) | Human Verified? |
|---|---|---|
| preamble (`a⁻` as the unique `x` with `a = axa`, `x = xax`; "the two definitions coincide") | `TubalRing.winv` ([TubalAlgebra/TubalRing.lean:234](TubalAlgebra/TubalRing.lean#L234)), `winv_spec` ([TubalAlgebra/TubalRing.lean:240](TubalAlgebra/TubalRing.lean#L240)), `winv_unique` ([TubalAlgebra/TubalRing.lean:246](TubalAlgebra/TubalRing.lean#L246)); `TubalRing.winv_eq_eq7` ([TubalAlgebra/Section9/Main.lean:61](TubalAlgebra/Section9/Main.lean#L61)), `TubalRing.exists_winv_eq_eq7` ([TubalAlgebra/Section9/Main.lean:82](TubalAlgebra/Section9/Main.lean#L82)) |  YES |
| **Lemma 38** ⚠ | `lemma38` ([TubalAlgebra/Section9/SimulDiag.lean:148](TubalAlgebra/Section9/SimulDiag.lean#L148)), with `IsDiagonalizableMat` ([TubalAlgebra/Section9/SimulDiag.lean:17](TubalAlgebra/Section9/SimulDiag.lean#L17)), `IsJointlyDiagonalizableMat` ([TubalAlgebra/Section9/SimulDiag.lean:22](TubalAlgebra/Section9/SimulDiag.lean#L22)) | YES |
| **Definition 39** | `TubalRing.repMat` ([TubalAlgebra/Section9/RepMatrix.lean:29](TubalAlgebra/Section9/RepMatrix.lean#L29)), `repMat_mulVec` ([TubalAlgebra/Section9/RepMatrix.lean:32](TubalAlgebra/Section9/RepMatrix.lean#L32)), `repMat_unique` ([TubalAlgebra/Section9/RepMatrix.lean:41](TubalAlgebra/Section9/RepMatrix.lean#L41)), `TubalRing.Rep` ([TubalAlgebra/Section9/RepMatrix.lean:49](TubalAlgebra/Section9/RepMatrix.lean#L49)) | YES |
| **Example 40** | `example40` ([TubalAlgebra/Section9/RepMatrix.lean:136](TubalAlgebra/Section9/RepMatrix.lean#L136)) | YES |
| **Lemma 41** | `TubalRing.lemma41` ([TubalAlgebra/Section9/RepMatrix.lean:52](TubalAlgebra/Section9/RepMatrix.lean#L52)) | YES |
| **Lemma 42** | `TubalRing.lemma42` ([TubalAlgebra/Section9/RepMatrix.lean:61](TubalAlgebra/Section9/RepMatrix.lean#L61)) | YES |
| **Lemma 43** | `TubalRing.lemma43` ([TubalAlgebra/Section9/RepMatrix.lean:72](TubalAlgebra/Section9/RepMatrix.lean#L72)) | YES |
| **Corollary 44** | `TubalRing.cor44` ([TubalAlgebra/Section9/RepMatrix.lean:92](TubalAlgebra/Section9/RepMatrix.lean#L92)) | YES |
| **Definition 45** | `TubalRing.IsIdempotent` ([TubalAlgebra/Section9/RepMatrix.lean:123](TubalAlgebra/Section9/RepMatrix.lean#L123)) | YES |
| **Lemma 46** | `TubalRing.lemma46` ([TubalAlgebra/Section9/RepMatrix.lean:126](TubalAlgebra/Section9/RepMatrix.lean#L126)) | YES |
| `a · b` for `b ∈ ℂⁿ`; `a · b = R_a b` | `TubalRing.mulC` ([TubalAlgebra/Section9/Diagonalizable.lean:34](TubalAlgebra/Section9/Diagonalizable.lean#L34)), `mulC_eq_repMat_mulVec` ([TubalAlgebra/Section9/Diagonalizable.lean:38](TubalAlgebra/Section9/Diagonalizable.lean#L38)) | YES |
| **Definition 47** | `TubalRing.IsEigenvector` ([TubalAlgebra/Section9/Diagonalizable.lean:53](TubalAlgebra/Section9/Diagonalizable.lean#L53)) | YES |
| **Definition 48** | `TubalRing.IsDiagonalizable` ([TubalAlgebra/Section9/Diagonalizable.lean:58](TubalAlgebra/Section9/Diagonalizable.lean#L58)) | YES |
| **Lemma 49** | `TubalRing.lemma49` ([TubalAlgebra/Section9/Diagonalizable.lean:63](TubalAlgebra/Section9/Diagonalizable.lean#L63)) | YES |
| **Definition 50** | `IsDiagonalizableSet` ([TubalAlgebra/Section9/Diagonalizable.lean:75](TubalAlgebra/Section9/Diagonalizable.lean#L75)), `IsDiagonalizableRing` ([TubalAlgebra/Section9/Diagonalizable.lean:78](TubalAlgebra/Section9/Diagonalizable.lean#L78)), `IsJointlyDiagonalizable` ([TubalAlgebra/Section9/Diagonalizable.lean:82](TubalAlgebra/Section9/Diagonalizable.lean#L82)), `IsJointlyDiagonalizableRing` ([TubalAlgebra/Section9/Diagonalizable.lean:86](TubalAlgebra/Section9/Diagonalizable.lean#L86)) | YES |
| **Lemma 51** | `TubalRing.lemma51` ([TubalAlgebra/Section9/Diagonalizable.lean:94](TubalAlgebra/Section9/Diagonalizable.lean#L94)) | YES |
| **Lemma 52** | `TubalRing.lemma52` ([TubalAlgebra/Section9/Diagonalizable.lean:101](TubalAlgebra/Section9/Diagonalizable.lean#L101)) | YES |
| **Lemma 53** | `TubalRing.lemma53` ([TubalAlgebra/Section9/Diagonalizable.lean:114](TubalAlgebra/Section9/Diagonalizable.lean#L114)) | YES |
| **Proposition 54** | `TubalRing.prop54` ([TubalAlgebra/Section9/Diagonalizable.lean:160](TubalAlgebra/Section9/Diagonalizable.lean#L160)) | YES |
| **Definition 55** | `TubalRing.IsTubalSubring` ([TubalAlgebra/Section9/Ideals.lean:31](TubalAlgebra/Section9/Ideals.lean#L31)) |  |
| **Definition 56** | `TubalRing.principalSet` ([TubalAlgebra/Section9/Ideals.lean:43](TubalAlgebra/Section9/Ideals.lean#L43)), `TubalRing.principal` ([TubalAlgebra/Section9/Ideals.lean:85](TubalAlgebra/Section9/Ideals.lean#L85)) |  |
| **Lemma 57** | `TubalRing.lemma57` ([TubalAlgebra/Section9/Ideals.lean:47](TubalAlgebra/Section9/Ideals.lean#L47)) |  |
| **Lemma 58** | `TubalRing.lemma58` ([TubalAlgebra/Section9/Ideals.lean:117](TubalAlgebra/Section9/Ideals.lean#L117)) |  |
| **Lemma 59** | `TubalRing.lemma59` ([TubalAlgebra/Section9/Ideals.lean:135](TubalAlgebra/Section9/Ideals.lean#L135)); text after it ("proper subsets, lower dimension"): `finrank_principal_lt` ([TubalAlgebra/Section9/Ideals.lean:172](TubalAlgebra/Section9/Ideals.lean#L172)) |  |
| division ring / tubal sub-field (Sec. 9.4) | `TubalRing.IsDivisionSubring` ([TubalAlgebra/Section9/Ideals.lean:215](TubalAlgebra/Section9/Ideals.lean#L215)), `TubalRing.IsTubalSubfield` ([TubalAlgebra/Section9/Ideals.lean:219](TubalAlgebra/Section9/Ideals.lean#L219)) |  |
| **Lemma 60** | `TubalRing.lemma60` ([TubalAlgebra/Section9/Ideals.lean:225](TubalAlgebra/Section9/Ideals.lean#L225)) |  |
| **Corollary 61** | `TubalRing.cor61` ([TubalAlgebra/Section9/Ideals.lean:273](TubalAlgebra/Section9/Ideals.lean#L273)) |  |
| **Proposition 62** | `TubalRing.prop62` ([TubalAlgebra/Section9/SubField.lean:84](TubalAlgebra/Section9/SubField.lean#L84)) |  |
| Section 9.6 (bringing it together) | `TubalRing.isDiagonalizableRing` ([TubalAlgebra/Section9/Main.lean:21](TubalAlgebra/Section9/Main.lean#L21)), `theorem11` ([TubalAlgebra/Section9/Main.lean:44](TubalAlgebra/Section9/Main.lean#L44)) |  |

## Section 10: Additional proofs

| Paper | Lean declaration (file:line) | Human Verified? |
|---|---|---|
| **Lemma 63** | `lemma63` ([TubalAlgebra/Realness.lean:246](TubalAlgebra/Realness.lean#L246)) |  |
| **Lemma 64** | `lemma64` ([TubalAlgebra/Realness.lean:312](TubalAlgebra/Realness.lean#L312)) |  |
| **Lemma 65** | `lemma65` ([TubalAlgebra/Realness.lean:336](TubalAlgebra/Realness.lean#L336)) |  |
| Proof of Lemma 7 | `lemma7` ([TubalAlgebra/Realness.lean:416](TubalAlgebra/Realness.lean#L416)) |  |
| `M_{n,m}`, `M_{n,m}⁻¹`, `𝕂_{n,m}` | `canonicalM` ([TubalAlgebra/Canonical.lean:21](TubalAlgebra/Canonical.lean#L21)), `canonicalMInv` ([TubalAlgebra/Canonical.lean:30](TubalAlgebra/Canonical.lean#L30)), `canonicalM_inv` ([TubalAlgebra/Canonical.lean:308](TubalAlgebra/Canonical.lean#L308)), `canonicalM_admissible` ([TubalAlgebra/Canonical.lean:314](TubalAlgebra/Canonical.lean#L314)), `realness_canonicalM` ([TubalAlgebra/Canonical.lean:326](TubalAlgebra/Canonical.lean#L326)) |  |
| **Proposition 66** | `prop66` ([TubalAlgebra/Canonical.lean:351](TubalAlgebra/Canonical.lean#L351)); with conjugation: `prop66_star` ([TubalAlgebra/Canonical.lean:360](TubalAlgebra/Canonical.lean#L360)) |  |

## Appendices

| Paper | Lean declaration (file:line) | Human Verified? |
|---|---|---|
| **Example 67** | `AppendixA.example67` ([TubalAlgebra/Examples/AppendixA.lean:179](TubalAlgebra/Examples/AppendixA.lean#L179)), `AppendixA.example67_step3` ([TubalAlgebra/Examples/AppendixA.lean:255](TubalAlgebra/Examples/AppendixA.lean#L255)) |  |
| **Example 68** | `AppendixA.example68` ([TubalAlgebra/Examples/AppendixA.lean:310](TubalAlgebra/Examples/AppendixA.lean#L310)), `AppendixA.hadamard2_eq_smul_unitary` ([TubalAlgebra/Examples/AppendixA.lean:292](TubalAlgebra/Examples/AppendixA.lean#L292)), `AppendixA.example68_literal_false` ([TubalAlgebra/Examples/AppendixA.lean:354](TubalAlgebra/Examples/AppendixA.lean#L354)) |  |
| Appendix B, weak inverses / nilpotents | `not_vonNeumann_has_nilpotent` ([TubalAlgebra/Examples/AppendixB.lean:486](TubalAlgebra/Examples/AppendixB.lean#L486)) |  |
| **Example 69** | `example69` ([TubalAlgebra/Examples/AppendixB.lean:19](TubalAlgebra/Examples/AppendixB.lean#L19)) |  |
| **Algorithm 1** ⚠ | `algorithm1` ([TubalAlgebra/Examples/AppendixB.lean:75](TubalAlgebra/Examples/AppendixB.lean#L75)), `algorithm1_correct` ([TubalAlgebra/Examples/AppendixB.lean:291](TubalAlgebra/Examples/AppendixB.lean#L291)), `algorithm1_exists_good_x` ([TubalAlgebra/Examples/AppendixB.lean:315](TubalAlgebra/Examples/AppendixB.lean#L315)), `algorithm1_ae` ([TubalAlgebra/Examples/AppendixB.lean:329](TubalAlgebra/Examples/AppendixB.lean#L329)) |  |
| **Proposition 70** | `prop70` ([TubalAlgebra/Hilbert.lean:74](TubalAlgebra/Hilbert.lean#L74)) |  |
| **Proposition 71** ⚠ | `prop71` ([TubalAlgebra/Hilbert.lean:91](TubalAlgebra/Hilbert.lean#L91)); "easy to build counter examples": `eq9_fails_in_general` ([TubalAlgebra/Hilbert.lean:114](TubalAlgebra/Hilbert.lean#L114)) |  |

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
   converse (`remark22_converse_false` ([TubalAlgebra/Tensor.lean:181](TubalAlgebra/Tensor.lean#L181))), and more sharply for every admissible `M` with `n ≥ 2`
   (`remark22_converse_false'` ([TubalAlgebra/Tensor.lean:138](TubalAlgebra/Tensor.lean#L138))); for `n = 1` the converse actually holds.
6. **Theorem 35**: the paper's `U_{:,1:r,:} ⋆ S_{1:r,1:r,:} ⋆ V^H_{:,1:r,:}` has `r` for `k`
   (typo) and `V^H_{:,1:k,:}` is read as `(V_{:,1:k,:})ᴴ` (the only well-typed reading). The
   statement also records that `[𝒜]_k` has `⋆_M`-rank `≤ k` (part of "optimal rank-`k`
   approximation").
7. **Theorem 37**: the error formula's factor `|c|⁻¹` is a typo for `|c|⁻²` (Example 68 itself
   uses `|c|⁻²`); `example68_literal_false` ([TubalAlgebra/Examples/AppendixA.lean:354](TubalAlgebra/Examples/AppendixA.lean#L354)) proves that the literal formula fails on the
   paper's own Example 68. "multirank-`k`" is a typo for "multirank-`r`". The statement also
   records that `[𝒜]_r` has the prescribed transformed slices and multirank `≤ r`.
8. **Proposition 71** is stated in Appendix C as an extension of Eq. (9) and proved from it, so
   it carries Proposition 70's hypothesis `M = D W` (`D` real invertible diagonal, `W`
   unitary); without it the statement is false (`eq9_fails_in_general` ([TubalAlgebra/Hilbert.lean:114](TubalAlgebra/Hilbert.lean#L114))).
9. **Example 18**: the printed XOR product `(a·b)_i = ∑_j a_i b_{i⊕j}` is a typo for
   `∑_j a_j b_{i⊕j}`; `example18_literal_not_comm` ([TubalAlgebra/Examples/Section3b.lean:356](TubalAlgebra/Examples/Section3b.lean#L356)) shows the printed formula is not even
   commutative.
10. **Eq. (3)**: `Xᵖ - 1` is a typo for `Xⁿ - 1`.
11. **Algorithm 1**: "`M ∈ ℝ^{n×n}`" is a typo; `M` is complex in general (cf. Example 4). The
    random choice of `x` is formalized as an almost-everywhere statement (`algorithm1_ae` ([TubalAlgebra/Examples/AppendixB.lean:329](TubalAlgebra/Examples/AppendixB.lean#L329))).
12. **Appendix B**: "a commutative ring … which is not tubal will be reduced, i.e. has an
    element `n` with `n² = 0`" — "reduced" should read "non-reduced".
13. **Definition 55**: commutativity, associativity, distributivity and ℝ-algebra compatibility
    of `(V, +, ·)` are inherited from the ambient tubal ring, so `IsTubalSubring` ([TubalAlgebra/Section9/Ideals.lean:31](TubalAlgebra/Section9/Ideals.lean#L31)) only requires
    closure, a unit, von Neumann regularity inside `V`, and the ideal property.
14. **Division ring (Sec. 9.4) / Lemma 60**: as recalled in Section 9.4, "a ring is called a
    division ring if every non-zero element has a multiplicative inverse" (no non-triviality
    requirement); with this reading Lemma 60 is true also for `V = {0}`.
15. **Definition 31**: the `⋆_M`-rank is defined from a chosen `⋆_M`-SVD; `lemma32_any` ([TubalAlgebra/TSVD.lean:330](TubalAlgebra/TSVD.lean#L330)) shows
    it does not depend on the choice.
16. **Theorem 3** is stated as: there is a `CommRing` structure on `ℝⁿ` whose addition is the
    usual one and whose multiplication is `⋆_M` (the ring axioms hold), and additionally via
    the type `KM M` ([TubalAlgebra/Defs.lean:108](TubalAlgebra/Defs.lean#L108)).
17. **Example 15** "no invertible `M` exists that makes dual numbers isomorphic to `ℝ²`":
    formalized both as "the dual product is not `⋆_M` for any invertible `M`"
    (`example15_no_M` ([TubalAlgebra/Examples/Section3.lean:462](TubalAlgebra/Examples/Section3.lean#L462))) and as "the dual numbers are not ring-isomorphic to any `𝕂_M`"
    (`example15_not_iso` ([TubalAlgebra/Examples/Section3.lean:485](TubalAlgebra/Examples/Section3.lean#L485))).

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
* `python3 scripts/axiom_audit.py` — `#print axioms` for all 488 public theorems, lemmas,
  definitions and instances; all depend only on `propext`, `Classical.choice`, `Quot.sound`.
* Statement faithfulness was independently reviewed against the paper (one reviewer per
  section plus a completeness critic, each finding adversarially re-verified); the
  confirmed gaps (all low severity: missing side-claims) were added.
