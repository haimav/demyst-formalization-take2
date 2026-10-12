import TubalAlgebra.Section9.Main
import TubalAlgebra.Examples.Section3

/-!
# Appendix B: additional discussion of Theorem 11 (Example 69, Algorithm 1, nilpotents)
-/

open Matrix Complex

noncomputable section

namespace Tubal

variable {n : ℕ}

/-- **Example 69** (Dual numbers are not a tubal ring — revisited). The representative matrix
associated with `x = [x₁, x₂]ᵀ` is `R_x = [[x₁, 0], [x₂, x₁]]`, which is not diagonalizable
for `x₂ ≠ 0`. This also proves that the dual numbers are not a tubal ring. -/
theorem example69 :
    (∀ x : Fin 2 → ℝ, repMatOf dualMul x = !![x 0, 0; x 1, x 0]) ∧
    (∀ x : Fin 2 → ℝ, x 1 ≠ 0 → ¬ IsDiagonalizableMat ((repMatOf dualMul x).map (↑))) ∧
    ¬ ∃ T : TubalRing 2, T.mul = dualMul := by
  have h1 : ∀ x : Fin 2 → ℝ, repMatOf dualMul x = !![x 0, 0; x 1, x 0] := by
    intro x
    ext i j
    fin_cases i <;> fin_cases j <;> simp [repMatOf, dualMul]
  refine ⟨h1, ?_, example15_not_tubal⟩
  rintro x hx ⟨S, hS, hD⟩
  have hdet : IsUnit S.det := (Matrix.isUnit_iff_isUnit_det S).1 hS
  set A : Matrix (Fin 2) (Fin 2) ℂ := (repMatOf dualMul x).map (↑) with hA
  set N : Matrix (Fin 2) (Fin 2) ℂ := A - (x 0 : ℂ) • 1 with hNdef
  have hN : N = !![0, 0; (x 1 : ℂ), 0] := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [N, A, h1]
  have hNN : N * N = 0 := by
    rw [hN]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]
  set E := S * N * S⁻¹ with hEdef
  have hE : E = S * A * S⁻¹ - (x 0 : ℂ) • 1 := by
    rw [hEdef, hNdef, Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_smul, Matrix.smul_mul,
      Matrix.mul_one, Matrix.mul_nonsing_inv _ hdet]
  have hEd : E.IsDiag := by
    rw [hE]
    exact hD.sub (isDiag_one.smul _)
  have hEE : E * E = 0 := by
    rw [hEdef]
    simp only [Matrix.mul_assoc, Matrix.nonsing_inv_mul_cancel_left _ _ hdet]
    rw [← Matrix.mul_assoc N, hNN, Matrix.zero_mul, Matrix.mul_zero]
  have hE0 : E = 0 := by
    have hdg := hEd.diagonal_diag
    ext i j
    by_cases hij : i = j
    · subst hij
      have := congrFun (congrFun hEE i) i
      rw [← hdg, diagonal_mul_diagonal, diagonal_apply_eq, Matrix.zero_apply] at this
      simpa [diag] using this
    · exact hEd hij
  have hN0 : N = 0 := by
    have : N = S⁻¹ * E * S := by
      rw [hEdef, Matrix.mul_assoc, Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hdet,
        Matrix.mul_one, Matrix.nonsing_inv_mul_cancel_left _ _ hdet]
    rw [this, hE0, Matrix.mul_zero, Matrix.zero_mul]
  have := congrFun (congrFun hN0 1) 0
  rw [hN] at this
  simp at this
  exact hx this

/-- **Algorithm 1** (Find matrix `M` for tubal ring product), given the eigendecomposition
`R_x = S Λ_x S⁻¹` of line 7: `y ← S e`, and the `i`-th column of `M` is `S⁻¹ R_{e_i} y`.

(The paper's "Ensure: Matrix `M ∈ ℝ^{n×n}`" and line 9 "Initialize `M ∈ ℝ^{n×n}`" are a typo:
the eigenvector matrix `S` of line 7 is complex in general, hence so is `M`; indeed no real `M`
exists for the complex numbers, see `theorem11_not_real`. So `M ∈ ℂ^{n×n}` here.) -/
def algorithm1 (T : TubalRing n) (S : Matrix (Fin n) (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ :=
  Matrix.of fun j i =>
    (S⁻¹ *ᵥ ((T.repMat (Pi.single i 1)).map (↑) *ᵥ (S *ᵥ fun _ => (1 : ℂ)))) j

namespace AppB

lemma map_ofReal_mul (A B : Matrix (Fin n) (Fin n) ℝ) :
    (A * B).map ((↑) : ℝ → ℂ) = A.map (↑) * B.map (↑) :=
  Matrix.map_mul (f := Complex.ofRealHom)

lemma map_ofReal_add (A B : Matrix (Fin n) (Fin n) ℝ) :
    (A + B).map ((↑) : ℝ → ℂ) = A.map (↑) + B.map (↑) :=
  Matrix.map_add _ (fun _ _ => Complex.ofReal_add _ _) A B

lemma map_ofReal_smul (r : ℝ) (A : Matrix (Fin n) (Fin n) ℝ) :
    (r • A).map ((↑) : ℝ → ℂ) = (r : ℂ) • A.map (↑) := by
  ext i j; simp

/-- Matrices agreeing on all real vectors are equal. -/
lemma ext_toC {A B : Matrix (Fin n) (Fin n) ℂ}
    (h : ∀ x : Fin n → ℝ, A *ᵥ toC x = B *ᵥ toC x) : A = B := by
  ext i k
  have := congrFun (h (Pi.single k 1)) i
  rw [toC_single, Matrix.mulVec_single_one, Matrix.mulVec_single_one] at this
  exact this

lemma repMat_mulVec_toC (T : TubalRing n) (a x : Fin n → ℝ) :
    (T.repMat a).map (↑) *ᵥ toC x = toC (T.mul a x) := by
  rw [← TubalRing.mulC_eq_repMat_mulVec]
  have h1 : (fun j => (toC x j).re) = x := funext fun j => by simp
  have h2 : (fun j => (toC x j).im) = 0 := funext fun j => by simp
  funext i
  apply Complex.ext
  · show T.mul a (fun j => (toC x j).re) i = (toC (T.mul a x) i).re
    rw [h1, toC_apply, Complex.ofReal_re]
  · show T.mul a (fun j => (toC x j).im) i = (toC (T.mul a x) i).im
    rw [h2, T.mul_zero, toC_apply, Complex.ofReal_im, Pi.zero_apply]

/-- Core of Algorithm 1: if `S` simultaneously diagonalizes all representation matrices
(`S⁻¹ R_a S` diagonal for all `a`), then the output `M` of Algorithm 1 is invertible and
`a · b = M⁻¹ (M a • M b)`. -/
theorem algorithm1_of_diag (T : TubalRing n) (S : Matrix (Fin n) (Fin n) ℂ) (hS : IsUnit S)
    (hD : ∀ a : Fin n → ℝ, (S⁻¹ * (T.repMat a).map ((↑) : ℝ → ℂ) * S).IsDiag) :
    IsUnit (algorithm1 T S) ∧
      ∀ a b : Fin n → ℝ, toC (T.mul a b) = starMC (algorithm1 T S) (toC a) (toC b) := by
  have hSdet : IsUnit S.det := (Matrix.isUnit_iff_isUnit_det S).1 hS
  set Rc : (Fin n → ℝ) → Matrix (Fin n) (Fin n) ℂ := fun a => (T.repMat a).map (↑) with hRc
  have hRadd : ∀ a b, Rc (a + b) = Rc a + Rc b := fun a b => by
    simp only [hRc]; rw [(T.lemma43 0 a b).2.1, map_ofReal_add]
  have hRsmul : ∀ (r : ℝ) a, Rc (r • a) = (r : ℂ) • Rc a := fun r a => by
    simp only [hRc]; rw [(T.lemma43 r a a).2.2.1, map_ofReal_smul]
  let f : Fin n → (Fin n → ℝ) →ₗ[ℝ] ℂ := fun j =>
    { toFun := fun a => (S⁻¹ * Rc a * S) j j
      map_add' := fun a b => by
        show (S⁻¹ * Rc (a + b) * S) j j = (S⁻¹ * Rc a * S) j j + (S⁻¹ * Rc b * S) j j
        rw [hRadd, Matrix.mul_add, Matrix.add_mul, Matrix.add_apply]
      map_smul' := fun r a => by
        show (S⁻¹ * Rc (r • a) * S) j j = (RingHom.id ℝ r) • (S⁻¹ * Rc a * S) j j
        rw [hRsmul, Matrix.mul_smul, Matrix.smul_mul, Matrix.smul_apply, RingHom.id_apply,
          Complex.real_smul, smul_eq_mul] }
  set M := algorithm1 T S with hMdef
  have hMentry : ∀ j k, M j k = f j (Pi.single k 1) := by
    intro j k
    change (S⁻¹ *ᵥ (Rc (Pi.single k 1) *ᵥ (S *ᵥ fun _ => (1 : ℂ)))) j = (S⁻¹ * Rc _ * S) j j
    rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec,
      (hD (Pi.single k 1)).diagonal_diag.symm, Matrix.mulVec_diagonal, diagonal_apply_eq,
      _root_.mul_one]
  have hM : ∀ a, M *ᵥ toC a = fun j => (S⁻¹ * Rc a * S) j j := by
    intro a
    funext j
    change _ = f j a
    rw [(f j).pi_apply_eq_sum_univ a]
    simp only [Matrix.mulVec, dotProduct, toC_apply, hMentry, Complex.real_smul]
    refine Finset.sum_congr rfl fun k _ => ?_
    have e : (Pi.single k (1 : ℝ) : Fin n → ℝ) = fun l => if k = l then 1 else 0 := by
      funext l; simp [Pi.single_apply, eq_comm]
    rw [e, _root_.mul_comm]
  have hDdiag : ∀ a, S⁻¹ * Rc a * S = diagonal (M *ᵥ toC a) := by
    intro a
    rw [hM a]
    exact (hD a).diagonal_diag.symm
  have hRcP : ∀ a, Rc a = S * diagonal (M *ᵥ toC a) * S⁻¹ := by
    intro a
    rw [← hDdiag a]
    simp only [Matrix.mul_assoc, Matrix.mul_nonsing_inv S hSdet, Matrix.mul_one,
      Matrix.mul_nonsing_inv_cancel_left S _ hSdet]
  have hRe : Rc T.one = 1 := by
    simp only [hRc]
    rw [(T.lemma43 0 0 0).2.2.2.1 T.one fun a => ⟨T.one_mul a, T.mul_one a⟩]
    exact Matrix.map_one _ Complex.ofReal_zero Complex.ofReal_one
  have hMe : M *ᵥ toC T.one = 1 := by
    apply Matrix.diagonal_injective
    rw [← hDdiag, hRe, Matrix.mul_one, Matrix.nonsing_inv_mul S hSdet]
    exact Matrix.diagonal_one.symm
  set β := S⁻¹ *ᵥ toC T.one with hβ
  have hPb : ∀ b, S⁻¹ *ᵥ toC b = (M *ᵥ toC b) * β := by
    intro b
    conv_lhs => rw [← T.mul_one b, ← repMat_mulVec_toC]
    change S⁻¹ *ᵥ (Rc b *ᵥ toC T.one) = _
    rw [hRcP b, Matrix.mulVec_mulVec, ← Matrix.mul_assoc, ← Matrix.mul_assoc,
      Matrix.nonsing_inv_mul S hSdet, Matrix.one_mul, ← Matrix.mulVec_mulVec, ← hβ]
    funext j
    rw [Matrix.mulVec_diagonal, Pi.mul_apply]
  have hab : ∀ a b, toC (T.mul a b) =
      (S * diagonal β) *ᵥ ((M *ᵥ toC a) * (M *ᵥ toC b)) := by
    intro a b
    rw [← repMat_mulVec_toC]
    change Rc a *ᵥ toC b = _
    rw [hRcP a, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, hPb]
    congr 1
    funext j
    simp only [Matrix.mulVec_diagonal, Pi.mul_apply]
    ring
  have hN : S * diagonal β * M = 1 := by
    apply ext_toC
    intro x
    have h := hab x T.one
    rw [T.mul_one, hMe, _root_.mul_one] at h
    rw [← Matrix.mulVec_mulVec, Matrix.one_mulVec, ← h]
  have hMdet : IsUnit M.det := Matrix.isUnit_det_of_left_inverse hN
  refine ⟨(Matrix.isUnit_iff_isUnit_det M).2 hMdet, fun a b => ?_⟩
  rw [starMC, Matrix.inv_eq_left_inv hN, hab]

/-- A matrix commuting with a diagonal matrix with distinct diagonal entries is diagonal. -/
lemma isDiag_of_commute_diagonal {C : Matrix (Fin n) (Fin n) ℂ} {Λ : Fin n → ℂ}
    (hΛ : Function.Injective Λ) (h : C * diagonal Λ = diagonal Λ * C) : C.IsDiag := by
  intro i j hij
  have := congrFun (congrFun h i) j
  rw [mul_diagonal, diagonal_mul] at this
  have hne : Λ j - Λ i ≠ 0 := sub_ne_zero.mpr (fun e => hij (hΛ e).symm)
  have h2 : C i j * (Λ j - Λ i) = 0 := by rw [mul_sub, this]; ring
  exact (mul_eq_zero.mp h2).resolve_right hne


/-- For an invertible `M`, the transform `M x` of almost every real vector `x` has pairwise
distinct entries. -/
lemma ae_injective_mulVec {M : Matrix (Fin n) (Fin n) ℂ} (hM : IsUnit M) :
    ∀ᵐ x : Fin n → ℝ ∂MeasureTheory.volume, Function.Injective (M *ᵥ toC x) := by
  have key : ∀ i j : Fin n, ∀ᵐ x : Fin n → ℝ ∂MeasureTheory.volume,
      (M *ᵥ toC x) i = (M *ᵥ toC x) j → i = j := by
    intro i j
    by_cases hij : i = j
    · exact Filter.Eventually.of_forall fun _ _ => hij
    · let L : (Fin n → ℝ) →ₗ[ℝ] ℂ :=
        { toFun := fun x => (M *ᵥ toC x) i - (M *ᵥ toC x) j
          map_add' := fun x y => by
            simp only [toC_add, Matrix.mulVec_add, Pi.add_apply]; ring
          map_smul' := fun r x => by
            simp only [toC_smul, Matrix.mulVec_smul, Pi.smul_apply, smul_eq_mul,
              RingHom.id_apply, Complex.real_smul]
            ring }
      have hL : LinearMap.ker L ≠ ⊤ := by
        obtain ⟨k, hk⟩ : ∃ k, M i k ≠ M j k := by
          by_contra h
          push Not at h
          exact hij (rows_eq_of_isUnit hM h)
        intro htop
        have hmem : (Pi.single k 1 : Fin n → ℝ) ∈ LinearMap.ker L := htop ▸ Submodule.mem_top
        rw [LinearMap.mem_ker] at hmem
        apply hk
        change (M *ᵥ toC (Pi.single k 1)) i - (M *ᵥ toC (Pi.single k 1)) j = 0 at hmem
        rw [toC_single, Matrix.mulVec_single_one] at hmem
        exact sub_eq_zero.mp hmem
      have h0 := MeasureTheory.Measure.addHaar_submodule MeasureTheory.volume _ hL
      rw [MeasureTheory.ae_iff]
      refine MeasureTheory.measure_mono_null ?_ h0
      intro x hx
      obtain ⟨hx1, -⟩ := not_imp.mp hx
      change (M *ᵥ toC x) i - (M *ᵥ toC x) j = 0
      rw [hx1, sub_self]
  have := MeasureTheory.ae_all_iff.2 fun i => MeasureTheory.ae_all_iff.2 (key i)
  filter_upwards [this] with x hx i j hxij using hx i j hxij

lemma charpoly_conj {S A : Matrix (Fin n) (Fin n) ℂ} (hS : IsUnit S) :
    (S * A * S⁻¹).charpoly = A.charpoly := by
  have hSdet : IsUnit S.det := (Matrix.isUnit_iff_isUnit_det S).1 hS
  rw [Matrix.charpoly_mul_comm, Matrix.nonsing_inv_mul_cancel_left _ _ hSdet]

lemma roots_charpoly_diagonal (d : Fin n → ℂ) :
    (diagonal d).charpoly.roots = Multiset.map d Finset.univ.val := by
  rw [charpoly_diagonal, Finset.prod_eq_multiset_prod]
  have : Multiset.map (fun i => Polynomial.X - Polynomial.C (d i)) Finset.univ.val =
      Multiset.map (fun a => Polynomial.X - Polynomial.C a) (Multiset.map d Finset.univ.val) := by
    rw [Multiset.map_map]; rfl
  rw [this, Polynomial.roots_multiset_prod_X_sub_C]

/-- If two diagonal matrices are similar and the first has distinct diagonal entries, so does
the second. -/
lemma injective_of_similar_diagonal {S : Matrix (Fin n) (Fin n) ℂ} {d Λ : Fin n → ℂ}
    (hS : IsUnit S) (hd : Function.Injective d) (h : diagonal d = S * diagonal Λ * S⁻¹) :
    Function.Injective Λ := by
  have hroots := congrArg (fun A => A.charpoly.roots) h
  simp only [charpoly_conj hS, roots_charpoly_diagonal] at hroots
  have hnd : (Multiset.map d Finset.univ.val).Nodup :=
    (Multiset.nodup_map_iff_of_injective hd).2 Finset.univ.nodup
  rw [hroots] at hnd
  intro i j hij
  exact Multiset.inj_on_of_nodup_map hnd i (Finset.mem_univ i) j (Finset.mem_univ j) hij


/-- If `a · b = M⁻¹ (M a • M b)` with `M` invertible, then `R_a = M⁻¹ diag(M a) M`. -/
lemma repMat_eq_conj (T : TubalRing n) {M : Matrix (Fin n) (Fin n) ℂ}
    (hT : ∀ a b : Fin n → ℝ, toC (T.mul a b) = starMC M (toC a) (toC b)) (a : Fin n → ℝ) :
    (T.repMat a).map (↑) = M⁻¹ * diagonal (M *ᵥ toC a) * M := by
  apply ext_toC
  intro x
  rw [repMat_mulVec_toC, hT, starMC, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec]
  congr 1
  funext j
  rw [Matrix.mulVec_diagonal, Pi.mul_apply]

end AppB

/-- **Algorithm 1** correctness: "If we are dealing with a tubal ring, Algorithm 1 will find
`M`" — whenever the (random) vector `x` of line 1 has a representation matrix with distinct
eigenvalues, the output `M` is invertible and `op(x, y) = M⁻¹ ((M x) • (M y))`. -/
theorem algorithm1_correct (T : TubalRing n) (x : Fin n → ℝ) (S : Matrix (Fin n) (Fin n) ℂ)
    (hS : IsUnit S) (Λ : Fin n → ℂ) (hΛ : Function.Injective Λ)
    (hx : (T.repMat x).map (↑) = S * diagonal Λ * S⁻¹) :
    IsUnit (algorithm1 T S) ∧
      ∀ a b : Fin n → ℝ, toC (T.mul a b) = starMC (algorithm1 T S) (toC a) (toC b) := by
  have hSdet : IsUnit S.det := (Matrix.isUnit_iff_isUnit_det S).1 hS
  apply AppB.algorithm1_of_diag T S hS
  intro a
  have hxS : S⁻¹ * (T.repMat x).map (↑) * S = diagonal Λ := by
    rw [hx]
    simp only [Matrix.mul_assoc, Matrix.nonsing_inv_mul S hSdet, Matrix.mul_one,
      Matrix.nonsing_inv_mul_cancel_left S _ hSdet]
  have hcomm : (T.repMat a).map ((↑) : ℝ → ℂ) * (T.repMat x).map (↑) =
      (T.repMat x).map (↑) * (T.repMat a).map (↑) := by
    rw [← AppB.map_ofReal_mul, ← AppB.map_ofReal_mul, ← (T.lemma43 0 a x).2.2.2.2,
      ← (T.lemma43 0 x a).2.2.2.2, T.mul_comm]
  apply AppB.isDiag_of_commute_diagonal hΛ
  rw [← hxS]
  simp only [Matrix.mul_assoc, Matrix.mul_nonsing_inv_cancel_left S _ hSdet]
  rw [← Matrix.mul_assoc ((T.repMat a).map _), hcomm, Matrix.mul_assoc]


/-- In a tubal ring, there is a vector `x` as required by `algorithm1_correct` (an `x` whose
representation matrix has `n` distinct eigenvalues), so Algorithm 1 can succeed. -/
theorem algorithm1_exists_good_x (T : TubalRing n) :
    ∃ (x : Fin n → ℝ) (S : Matrix (Fin n) (Fin n) ℂ) (Λ : Fin n → ℂ), IsUnit S ∧
      Function.Injective Λ ∧ (T.repMat x).map (↑) = S * diagonal Λ * S⁻¹ := by
  obtain ⟨M, hM, hT⟩ := theorem11 T
  have hMdet : IsUnit M.det := (Matrix.isUnit_iff_isUnit_det M).1 hM
  obtain ⟨x, hx⟩ := (AppB.ae_injective_mulVec hM).exists
  refine ⟨x, M⁻¹, M *ᵥ toC x, Matrix.isUnit_nonsing_inv_iff.2 hM, hx, ?_⟩
  rw [Matrix.nonsing_inv_nonsing_inv M hMdet]
  exact AppB.repMat_eq_conj T hT x

/-- **Algorithm 1**: "If we are dealing with a tubal ring, Algorithm 1 will find `M`", with
`x` drawn at random in line 1: for almost every `x ∈ ℝⁿ` (Lebesgue measure), the
eigendecomposition of line 7 exists, and whatever eigendecomposition `R_x = S Λ_x S⁻¹` line 7
returns, the output `M` is invertible and `op(a, b) = M⁻¹ ((M a) • (M b))`. -/
theorem algorithm1_ae (T : TubalRing n) :
    ∀ᵐ x : Fin n → ℝ ∂MeasureTheory.volume,
      (∃ (S : Matrix (Fin n) (Fin n) ℂ) (Λ : Fin n → ℂ), IsUnit S ∧
        (T.repMat x).map (↑) = S * diagonal Λ * S⁻¹) ∧
      ∀ (S : Matrix (Fin n) (Fin n) ℂ) (Λ : Fin n → ℂ), IsUnit S →
        (T.repMat x).map (↑) = S * diagonal Λ * S⁻¹ →
        IsUnit (algorithm1 T S) ∧
          ∀ a b : Fin n → ℝ, toC (T.mul a b) = starMC (algorithm1 T S) (toC a) (toC b) := by
  obtain ⟨M, hM, hT⟩ := theorem11 T
  have hMdet : IsUnit M.det := (Matrix.isUnit_iff_isUnit_det M).1 hM
  filter_upwards [AppB.ae_injective_mulVec hM] with x hx
  have hR := AppB.repMat_eq_conj T hT x
  refine ⟨⟨M⁻¹, M *ᵥ toC x, Matrix.isUnit_nonsing_inv_iff.2 hM, ?_⟩, fun S Λ hS hSx => ?_⟩
  · rw [Matrix.nonsing_inv_nonsing_inv M hMdet]
    exact hR
  refine algorithm1_correct T x S hS Λ ?_ hSx
  apply AppB.injective_of_similar_diagonal (S := M * S) (hM.mul hS) hx
  have e : M * (M⁻¹ * diagonal (M *ᵥ toC x) * M) * M⁻¹ = diagonal (M *ᵥ toC x) := by
    simp only [Matrix.mul_assoc, Matrix.mul_nonsing_inv M hMdet, Matrix.mul_one,
      Matrix.mul_nonsing_inv_cancel_left M _ hMdet]
  rw [← e, ← hR, hSx, Matrix.mul_inv_rev]
  simp only [Matrix.mul_assoc]

namespace AppB

/-- Elements of a `CommAlgOn n`, as a type carrying Mathlib's ring structures. -/
@[ext]
structure CElem (R : CommAlgOn n) where
  /-- The underlying real vector. -/
  vec : Fin n → ℝ

namespace CElem

variable {R : CommAlgOn n}

lemma vec_injective : Function.Injective (CElem.vec : CElem R → Fin n → ℝ) :=
  fun _ _ h => CElem.ext h

lemma mul_zero' (a : Fin n → ℝ) : R.mul a 0 = 0 := by
  have h := R.left_distrib a 0 0
  rw [add_zero] at h
  exact add_eq_left.mp h.symm

lemma zero_mul' (a : Fin n → ℝ) : R.mul 0 a = 0 := by
  have h := R.right_distrib 0 0 a
  rw [add_zero] at h
  exact add_eq_left.mp h.symm

instance : Zero (CElem R) := ⟨⟨0⟩⟩
instance : Add (CElem R) := ⟨fun a b => ⟨a.vec + b.vec⟩⟩
instance : Neg (CElem R) := ⟨fun a => ⟨-a.vec⟩⟩
instance : Sub (CElem R) := ⟨fun a b => ⟨a.vec - b.vec⟩⟩
instance : SMul ℕ (CElem R) := ⟨fun k a => ⟨k • a.vec⟩⟩
instance : SMul ℤ (CElem R) := ⟨fun k a => ⟨k • a.vec⟩⟩
instance : SMul ℝ (CElem R) := ⟨fun r a => ⟨r • a.vec⟩⟩
instance : Mul (CElem R) := ⟨fun a b => ⟨R.mul a.vec b.vec⟩⟩
instance : One (CElem R) := ⟨⟨Classical.choose R.exists_one⟩⟩

@[simp] lemma vec_zero : (0 : CElem R).vec = 0 := rfl
@[simp] lemma vec_mul (a b : CElem R) : (a * b).vec = R.mul a.vec b.vec := rfl

instance : AddCommGroup (CElem R) :=
  vec_injective.addCommGroup _ rfl (fun _ _ => rfl) (fun _ => rfl) (fun _ _ => rfl)
    (fun _ _ => rfl) (fun _ _ => rfl)

/-- The additive map `a ↦ a.vec`. -/
def vecAddHom : CElem R →+ (Fin n → ℝ) where
  toFun := CElem.vec
  map_zero' := rfl
  map_add' _ _ := rfl

instance : Module ℝ (CElem R) := vec_injective.module ℝ vecAddHom (fun _ _ => rfl)

instance instCommRing : CommRing (CElem R) :=
  { (inferInstance : AddCommGroup (CElem R)) with
    mul := (· * ·)
    one := 1
    mul_assoc := fun a b c => CElem.ext (R.mul_assoc a.vec b.vec c.vec)
    one_mul := fun a => CElem.ext ((Classical.choose_spec R.exists_one a.vec).1)
    mul_one := fun a => CElem.ext ((Classical.choose_spec R.exists_one a.vec).2)
    left_distrib := fun a b c => CElem.ext (R.left_distrib a.vec b.vec c.vec)
    right_distrib := fun a b c => CElem.ext (R.right_distrib a.vec b.vec c.vec)
    zero_mul := fun a => CElem.ext (zero_mul' a.vec)
    mul_zero := fun a => CElem.ext (mul_zero' a.vec)
    mul_comm := fun a b => CElem.ext (R.mul_comm a.vec b.vec)
    natCast := fun k => k • (1 : CElem R)
    natCast_zero := zero_nsmul _
    natCast_succ := fun k => succ_nsmul _ k
    intCast := fun k => k • (1 : CElem R)
    intCast_ofNat := fun k => natCast_zsmul _ k
    intCast_negSucc := fun k => negSucc_zsmul _ k
    npow := fun k a => npowRec k a
    npow_zero := fun _ => rfl
    npow_succ := fun _ _ => rfl }

instance instAlgebra : Algebra ℝ (CElem R) :=
  Algebra.ofModule (fun r a b => CElem.ext (R.smul_mul r a.vec b.vec))
    (fun r a b => CElem.ext (R.mul_smul r a.vec b.vec))

/-- `CElem R ≃ₗ[ℝ] ℝⁿ`. -/
def linearEquivVec : CElem R ≃ₗ[ℝ] (Fin n → ℝ) where
  toFun := CElem.vec
  invFun := CElem.mk
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  left_inv _ := rfl
  right_inv _ := rfl

instance : FiniteDimensional ℝ (CElem R) :=
  LinearEquiv.finiteDimensional linearEquivVec.symm

instance : IsArtinianRing (CElem R) := IsArtinianRing.of_finite ℝ (CElem R)

end CElem

/-- In a commutative ring where `x * x = 0` forces `x = 0`, every nilpotent is zero. -/
lemma eq_zero_of_pow_eq_zero {A : Type*} [CommRing A] (hsq : ∀ x : A, x * x = 0 → x = 0) :
    ∀ k (x : A), x ^ k = 0 → x = 0 := by
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    intro x hk
    rcases Nat.lt_or_ge k 2 with hk2 | hk2
    · interval_cases k
      · simp only [pow_zero] at hk
        rw [← _root_.one_mul x, hk, MulZeroClass.zero_mul]
      · simpa using hk
    · have : x ^ (k - 1) = 0 := by
        apply hsq
        rw [← pow_add]
        have : k - 1 + (k - 1) = k + (k - 2) := by omega
        rw [this, pow_add, hk, MulZeroClass.zero_mul]
      exact ih (k - 1) (by omega) x this

/-- A commutative Artinian ring without non-zero square-zero elements is von Neumann regular. -/
lemma vonNeumann_of_artinian {A : Type*} [CommRing A] [IsArtinianRing A]
    (hsq : ∀ x : A, x * x = 0 → x = 0) (a : A) : ∃ x, a = a * x * a := by
  obtain ⟨k, y, hy⟩ := IsArtinian.exists_pow_succ_smul_dvd a (1 : A)
  simp only [smul_eq_mul, _root_.mul_one] at hy
  -- `a ^ (k+1) * y = a ^ k`, hence `(a - a * y * a) ^ (k + 1) = 0`
  have h0 : a ^ (k + 1) * (1 - a * y) = 0 := by
    have : a ^ (k + 1) * (1 - a * y) = a ^ (k + 1) - a * (a ^ (k + 1) * y) := by ring
    rw [this, hy]; ring
  have h1 : (a - a * y * a) ^ (k + 1) = 0 := by
    have : (a - a * y * a) ^ (k + 1) = a ^ (k + 1) * (1 - a * y) * (1 - a * y) ^ k := by
      rw [show a - a * y * a = a * (1 - a * y) by ring, mul_pow, pow_succ (1 - a * y)]; ring
    rw [this, h0, MulZeroClass.zero_mul]
  have := eq_zero_of_pow_eq_zero hsq (k + 1) _ h1
  exact ⟨y, (sub_eq_zero.mp this)⟩

end AppB

/-- Appendix B ("Importance of existence of weak inverses", also announced in Section 3.5):
a commutative ring over `ℝⁿ` which is not von Neumann regular must have nilpotent elements,
i.e. elements `ν ≠ 0` with `ν² = 0`. (The paper's sentence "a commutative ring over `ℝⁿ`
which is not tubal will be reduced, i.e., has an element `n` such that `n² = 0`" has a typo:
"reduced" should read "non-reduced", as the "i.e." clause shows.) -/
theorem not_vonNeumann_has_nilpotent (R : CommAlgOn n)
    (h : ¬ ∀ a, ∃ x, a = R.mul (R.mul a x) a) : ∃ ν : Fin n → ℝ, ν ≠ 0 ∧ R.mul ν ν = 0 := by
  by_contra hν
  push Not at hν
  apply h
  intro a
  have hsq : ∀ x : AppB.CElem R, x * x = 0 → x = 0 := by
    intro x hx
    by_contra hx0
    exact hν x.vec (fun e => hx0 (AppB.CElem.ext e)) (congrArg AppB.CElem.vec hx)
  obtain ⟨x, hx⟩ := AppB.vonNeumann_of_artinian hsq (⟨a⟩ : AppB.CElem R)
  exact ⟨x.vec, congrArg AppB.CElem.vec hx⟩


end Tubal
