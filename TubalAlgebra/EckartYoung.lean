import TubalAlgebra.TSVD

/-!
# Low-rank tensor approximations via truncated tubal SVD (Section 7.1: Lemma 33,
Corollary 34, Theorem 35, Definition 36, Theorem 37)
-/

open Matrix Complex

noncomputable section

namespace Tubal

variable {n : ℕ} {M : Matrix (Fin n) (Fin n) ℂ}

/-- The Frobenius norm `‖𝒜‖_F` of a real tensor `𝒜 ∈ ℝ^{m×p×n}`. -/
def tnorm {m p : ℕ} (A : Matrix (Fin m) (Fin p) (KM M)) : ℝ :=
  Real.sqrt (∑ i, ∑ k, ∑ j, ((A i k).vec j) ^ 2)

/-- The Frobenius (Euclidean) norm `‖a‖_F` of a tube `a ∈ ℝⁿ`. -/
def tubeNorm (a : KM M) : ℝ := Real.sqrt (∑ j, (a.vec j) ^ 2)

/-- **Lemma 33** (Theorem 3.1 in [16]). Suppose `M = c W` for some unitary matrix `W` and
non-zero scalar `c`. Let `𝒰 ∈ 𝕂_M^{m×m}` be a `⋆_M`-unitary tensor. Then for any tensors `ℬ`
and `𝒞` of compatible sizes, we have `‖𝒰 ⋆_M ℬ‖_F = ‖ℬ‖_F` and `‖𝒞 ⋆_M 𝒰‖_F = ‖𝒞‖_F`. -/
theorem lemma33 [Fact (Admissible M)] (W : Matrix (Fin n) (Fin n) ℂ)
    (hW : W ∈ unitaryGroup (Fin n) ℂ) (c : ℂ) (hc : c ≠ 0) (hMW : M = c • W) {m : ℕ}
    (U : Matrix (Fin m) (Fin m) (KM M)) (hU : IsStarMUnitary U) :
    (∀ {l : ℕ} (B : Matrix (Fin m) (Fin l) (KM M)), tnorm (U * B) = tnorm B) ∧
    (∀ {l : ℕ} (C : Matrix (Fin l) (Fin m) (KM M)), tnorm (C * U) = tnorm C) := by
  sorry

/-- **Corollary 34** (Corollary 3.3 in [16]). Consider the `⋆_M`-SVD of a tensor
`𝒜 ∈ 𝕂_M^{m×p}` given by `𝒜 = 𝒰 ⋆_M 𝒮 ⋆_M 𝒱ᴴ`. If `M = c W` for some unitary matrix `W` and
non-zero scalar `c` then `‖𝒜‖_F² = ‖𝒮‖_F² = ∑_{i=1}^{⋆_M-rank(𝒜)} ‖σᵢ‖_F²`. Moreover,
`‖σ₁‖_F ≥ ‖σ₂‖_F ≥ ⋯`. -/
theorem cor34 [Fact (Admissible M)] (W : Matrix (Fin n) (Fin n) ℂ)
    (hW : W ∈ unitaryGroup (Fin n) ℂ) (c : ℂ) (hc : c ≠ 0) (hMW : M = c • W) {m p : ℕ}
    (A : Matrix (Fin m) (Fin p) (KM M)) (U : Matrix (Fin m) (Fin m) (KM M))
    (S : Matrix (Fin m) (Fin p) (KM M)) (V : Matrix (Fin p) (Fin p) (KM M))
    (h : IsTSVD A U S V) :
    tnorm A ^ 2 = tnorm S ^ 2 ∧
    tnorm S ^ 2 = ∑ i : Fin (min m p), (if (i : ℕ) < starMRank A then tubeNorm (sigma S i) ^ 2
      else 0) ∧
    (∀ i j : Fin (min m p), i ≤ j → tubeNorm (sigma S j) ≤ tubeNorm (sigma S i)) := by
  sorry

/-- The truncation `[𝒜]_k := 𝒰_{:,1:k,:} ⋆_M 𝒮_{1:k,1:k,:} ⋆_M (𝒱_{:,1:k,:})ᴴ`
(for `k ≤ m`, `k ≤ p`). -/
def truncT [Fact (Admissible M)] {m p : ℕ} (U : Matrix (Fin m) (Fin m) (KM M))
    (S : Matrix (Fin m) (Fin p) (KM M)) (V : Matrix (Fin p) (Fin p) (KM M)) (k : ℕ)
    (hkm : k ≤ m) (hkp : k ≤ p) : Matrix (Fin m) (Fin p) (KM M) :=
  U.submatrix id (Fin.castLE hkm) * S.submatrix (Fin.castLE hkm) (Fin.castLE hkp) *
    (V.submatrix id (Fin.castLE hkp))ᴴ

/-- **Theorem 35** (Theorem 3.7 in [16]). Assume that `M = c W` for some unitary matrix `W`
and non-zero scalar `c`. Let `𝒜 ∈ 𝕂_M^{m×p}` be a tensor and let `𝒜 = 𝒰 ⋆_M 𝒮 ⋆_M 𝒱ᴴ` be
its `⋆_M`-SVD. For any `k ≤ ⋆_M-rank(𝒜)`, the tensor
`[𝒜]_k := 𝒰_{:,1:k,:} ⋆_M 𝒮_{1:k,1:k,:} ⋆_M 𝒱ᴴ_{:,1:k,:}` is the optimal `⋆_M`-rank-`k`
approximation of `𝒜` in the Frobenius norm: for any tensor `ℬ` of the same size as `𝒜` with
`⋆_M-rank(ℬ) ≤ k`, `‖𝒜 - [𝒜]_k‖_F² ≤ ‖𝒜 - ℬ‖_F²`. Moreover,
`‖𝒜 - [𝒜]_k‖_F² = ∑_{i=k+1}^{⋆_M-rank(𝒜)} ‖σᵢ‖_F²`.

(The paper's subscripts `1:r` are a typo for `1:k`, and `𝒱ᴴ_{:,1:k,:}` denotes
`(𝒱_{:,1:k,:})ᴴ`, the only reading for which the product is defined.) -/
theorem theorem35 [Fact (Admissible M)] (W : Matrix (Fin n) (Fin n) ℂ)
    (hW : W ∈ unitaryGroup (Fin n) ℂ) (c : ℂ) (hc : c ≠ 0) (hMW : M = c • W) {m p : ℕ}
    (A : Matrix (Fin m) (Fin p) (KM M)) (U : Matrix (Fin m) (Fin m) (KM M))
    (S : Matrix (Fin m) (Fin p) (KM M)) (V : Matrix (Fin p) (Fin p) (KM M))
    (h : IsTSVD A U S V) (k : ℕ) (hk : k ≤ starMRank A) :
    let Ak := truncT U S V k (hk.trans ((starMRank_le_min A).trans (min_le_left m p)))
      (hk.trans ((starMRank_le_min A).trans (min_le_right m p)))
    (∀ B : Matrix (Fin m) (Fin p) (KM M), starMRank B ≤ k →
      tnorm (A - Ak) ^ 2 ≤ tnorm (A - B) ^ 2) ∧
    tnorm (A - Ak) ^ 2 = ∑ i : Fin (min m p),
      (if k ≤ (i : ℕ) ∧ (i : ℕ) < starMRank A then tubeNorm (sigma S i) ^ 2 else 0) := by
  sorry

/-- **Definition 36** (first part). The `⋆_M`-multirank of a tensor `𝒜` is the `n`-tuple of
non-negative integers whose `j`-th entry is the rank of `𝒜̂_j`. -/
def multirank [Fact (Admissible M)] {m p : ℕ} (A : Matrix (Fin m) (Fin p) (KM M)) :
    Fin n → ℕ :=
  fun j => (tHat A j).rank

/-- **Definition 36** (second part). A tuple `r` respects the conjugation pattern of `M` if
`rᵢ = rⱼ` for every conjugate pair of rows `i, j` in `M`. -/
def RespectsConjPattern (M : Matrix (Fin n) (Fin n) ℂ) (r : Fin n → ℕ) : Prop :=
  ∀ i j, i ≠ j → RowConjOf M i j → r i = r j

/-- **Definition 36** (remark). `⋆_M-multirank(𝒜)` respects the conjugation pattern of `M`. -/
theorem multirank_respectsConjPattern [Fact (Admissible M)] {m p : ℕ}
    (A : Matrix (Fin m) (Fin p) (KM M)) : RespectsConjPattern M (multirank A) := by
  sorry

theorem multirank_le_min [Fact (Admissible M)] {m p : ℕ} (A : Matrix (Fin m) (Fin p) (KM M))
    (j : Fin n) : multirank A j ≤ min m p := by
  sorry

/-- The slice-wise truncation `[𝒜̂_j]_{r_j} = Û_{:,1:r_j,j} Ŝ_{1:r_j,1:r_j,j} V̂ᴴ_{:,1:r_j,j}`
of Theorem 37, for a `⋆_M`-SVD `(𝒰, 𝒮, 𝒱)` and a tuple `r ≤ ⋆_M-multirank(𝒜)`. -/
def truncSlices [Fact (Admissible M)] {m p : ℕ} (A : Matrix (Fin m) (Fin p) (KM M))
    (U : Matrix (Fin m) (Fin m) (KM M)) (S : Matrix (Fin m) (Fin p) (KM M))
    (V : Matrix (Fin p) (Fin p) (KM M)) (r : Fin n → ℕ) (hr : r ≤ multirank A) :
    Fin n → Matrix (Fin m) (Fin p) ℂ :=
  fun j => truncSub (tHat U j) (tHat S j) (tHat V j) (r j)
    ((hr j).trans ((multirank_le_min A j).trans (min_le_left m p)))
    ((hr j).trans ((multirank_le_min A j).trans (min_le_right m p)))

/-- **Theorem 37** (Theorem 3.8 in [16]). Assume that `M = c W` for some unitary matrix `W`
and non-zero scalar `c`. Let `𝒜 ∈ 𝕂_M^{m×p}` be a tensor and let `𝒜 = 𝒰 ⋆_M 𝒮 ⋆_M 𝒱ᴴ` be its
`⋆_M`-SVD. For any `n`-size tuple of non-negative integers `r ≤ ⋆_M-multirank(𝒜)` which
respects the conjugation pattern of `M`, we define the tensor `[𝒜]_r` as the tensor in which
the frontal slice `j` in the transformed space is the `r_j` truncated SVD of the `j`th frontal
face of the transformed `𝒜`:
`([𝒜]_r)^_{::j} := [𝒜̂_j]_{r_j} = Û_{:,1:r_j,j} Ŝ_{1:r_j,1:r_j,j} V̂ᴴ_{:,1:r_j,j}`.
`[𝒜]_r` is the optimal `⋆_M`-multirank-`r` approximation of `𝒜` in the Frobenius norm. That
is, for any tensor `ℬ` of the same size as `𝒜` and `⋆_M`-multirank at most `r`, we have
`‖𝒜 - [𝒜]_r‖_F² ≤ ‖𝒜 - ℬ‖_F²`. Moreover,
`‖𝒜 - [𝒜]_r‖_F² = |c|⁻² · ∑_{j=1}^n ∑_{i=r_j+1}^{rank(𝒜̂_j)} σ̂²_{ij}`.

Here `[𝒜]_r := tInv (truncSlices …)`; the first conjunct states that this real tensor indeed
has the prescribed transformed frontal slices.

(The paper's factor `|c|⁻¹` is a typo for `|c|⁻²`, as confirmed by its Example 68;
see `example68_literal_false` in `TubalAlgebra.Examples.AppendixA`. Also "multirank-k" is a
typo for "multirank-r".) -/
theorem theorem37 [Fact (Admissible M)] (W : Matrix (Fin n) (Fin n) ℂ)
    (hW : W ∈ unitaryGroup (Fin n) ℂ) (c : ℂ) (hc : c ≠ 0) (hMW : M = c • W) {m p : ℕ}
    (A : Matrix (Fin m) (Fin p) (KM M)) (U : Matrix (Fin m) (Fin m) (KM M))
    (S : Matrix (Fin m) (Fin p) (KM M)) (V : Matrix (Fin p) (Fin p) (KM M))
    (h : IsTSVD A U S V) (r : Fin n → ℕ) (hr : r ≤ multirank A)
    (hpat : RespectsConjPattern M r) :
    let Ar : Matrix (Fin m) (Fin p) (KM M) := tInv (truncSlices A U S V r hr)
    tHat Ar = truncSlices A U S V r hr ∧
    (∀ B : Matrix (Fin m) (Fin p) (KM M), multirank B ≤ r →
      tnorm (A - Ar) ^ 2 ≤ tnorm (A - B) ^ 2) ∧
    tnorm (A - Ar) ^ 2 = (‖c‖ ^ 2)⁻¹ * ∑ j, ∑ i : Fin (min m p),
      (if r j ≤ (i : ℕ) ∧ (i : ℕ) < (tHat A j).rank then
        (RCLike.re (diagEntry (tHat S j) i)) ^ 2 else 0) := by
  sorry

end Tubal
