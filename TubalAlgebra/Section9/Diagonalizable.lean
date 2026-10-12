import TubalAlgebra.Section9.RepMatrix
import TubalAlgebra.Section9.SimulDiag

/-!
# Diagonalizability of tubal rings (Section 9.2: Definitions 47, 48, 50, Lemmas 49, 51, 52, 53,
Proposition 54)
-/

open Matrix Complex

noncomputable section

namespace Tubal

variable {n : ℕ}

namespace TubalRing

variable (T : TubalRing n)

private lemma dg_map_ofReal_mul (A B : Matrix (Fin n) (Fin n) ℝ) :
    (A * B).map ((↑) : ℝ → ℂ) = A.map (↑) * B.map (↑) :=
  Matrix.map_mul (f := Complex.ofRealHom)

private lemma dg_map_ofReal_add (A B : Matrix (Fin n) (Fin n) ℝ) :
    (A + B).map ((↑) : ℝ → ℂ) = A.map (↑) + B.map (↑) :=
  Matrix.map_add _ (fun _ _ => Complex.ofReal_add _ _) A B

private lemma dg_map_ofReal_smul (r : ℝ) (A : Matrix (Fin n) (Fin n) ℝ) :
    (r • A).map ((↑) : ℝ → ℂ) = (r : ℂ) • A.map (↑) := by
  ext i j; simp

/-- For `a ∈ ℝⁿ` and `b ∈ ℂⁿ`: `a · b := a · Re b + i (a · Im b)`. -/
def mulC (a : Fin n → ℝ) (b : Fin n → ℂ) : Fin n → ℂ :=
  fun i => ⟨T.mul a (fun j => (b j).re) i, T.mul a (fun j => (b j).im) i⟩

/-- "We still have `a · b = R_a b`." -/
theorem mulC_eq_repMat_mulVec (a : Fin n → ℝ) (b : Fin n → ℂ) :
    T.mulC a b = (T.repMat a).map (↑) *ᵥ b := by
  funext i
  have h1 := congrFun (T.repMat_mulVec a (fun j => (b j).re)) i
  have h2 := congrFun (T.repMat_mulVec a (fun j => (b j).im)) i
  apply Complex.ext
  · simp only [mulC]
    rw [← h1]
    simp [Matrix.mulVec, dotProduct, Complex.re_sum]
  · simp only [mulC]
    rw [← h2]
    simp [Matrix.mulVec, dotProduct, Complex.im_sum]

/-- **Definition 47.** A non-zero `x ∈ ℂⁿ` is an eigenvector of `a` if there exists a
corresponding eigenvalue `λ ∈ ℂ` such that `a · x = λ x`. -/
def IsEigenvector (a : Fin n → ℝ) (x : Fin n → ℂ) : Prop :=
  x ≠ 0 ∧ ∃ μ : ℂ, T.mulC a x = μ • x

/-- **Definition 48.** `a` is diagonalizable if there exists a set of `n` linearly independent
eigenvectors of `a`. -/
def IsDiagonalizable (a : Fin n → ℝ) : Prop :=
  ∃ v : Fin n → Fin n → ℂ, LinearIndependent ℂ v ∧ ∀ i, T.IsEigenvector a (v i)

/-- **Lemma 49.** `a` is diagonalizable if and only if `R_a` is diagonalizable over `ℂ`. The
set of eigenvectors of `a` is exactly the set of eigenvectors of `R_a`. -/
theorem lemma49 (a : Fin n → ℝ) :
    (T.IsDiagonalizable a ↔ IsDiagonalizableMat ((T.repMat a).map (↑))) ∧
    (∀ x, T.IsEigenvector a x ↔ IsEigenvectorMat ((T.repMat a).map (↑)) x) := by
  have hev : ∀ x, T.IsEigenvector a x ↔ IsEigenvectorMat ((T.repMat a).map (↑)) x := by
    intro x
    simp only [IsEigenvector, IsEigenvectorMat, mulC_eq_repMat_mulVec]
  refine ⟨?_, hev⟩
  rw [isDiagonalizableMat_iff_eigenvectors]
  simp only [IsDiagonalizable, hev]

/-- **Definition 50** (first part). `S ⊆ ℝⁿ` is diagonalizable if every `a ∈ S` is
diagonalizable. -/
def IsDiagonalizableSet (S : Set (Fin n → ℝ)) : Prop := ∀ a ∈ S, T.IsDiagonalizable a

/-- **Definition 50**: the tubal ring is diagonalizable if `ℝⁿ` is diagonalizable. -/
def IsDiagonalizableRing : Prop := T.IsDiagonalizableSet Set.univ

/-- **Definition 50** (second part). `S ⊆ ℝⁿ` is jointly diagonalizable if there exists a set
of `n` linearly independent vectors which are eigenvectors for all `a ∈ S`. -/
def IsJointlyDiagonalizable (S : Set (Fin n → ℝ)) : Prop :=
  ∃ v : Fin n → Fin n → ℂ, LinearIndependent ℂ v ∧ ∀ a ∈ S, ∀ i, T.IsEigenvector a (v i)

/-- **Definition 50**: the tubal ring is jointly diagonalizable if `ℝⁿ` is. -/
def IsJointlyDiagonalizableRing : Prop := T.IsJointlyDiagonalizable Set.univ

/-- `Rep(S)` viewed as a set of complex matrices. -/
def RepC (S : Set (Fin n → ℝ)) : Set (Matrix (Fin n) (Fin n) ℂ) :=
  (fun a => (T.repMat a).map (↑)) '' S

/-- **Lemma 51.** `S ⊆ ℝⁿ` is jointly diagonalizable if and only if the set of matrices
`Rep(S)` is jointly diagonalizable. -/
theorem lemma51 (S : Set (Fin n → ℝ)) :
    T.IsJointlyDiagonalizable S ↔ IsJointlyDiagonalizableMat (T.RepC S) := by
  rw [isJointlyDiagonalizableMat_iff_eigenvectors]
  simp only [IsJointlyDiagonalizable, RepC, Set.forall_mem_image, (T.lemma49 _).2]

/-- **Lemma 52.** In a tubal ring, if a set of elements `S` is diagonalizable then it is
jointly diagonalizable. -/
theorem lemma52 (S : Set (Fin n → ℝ)) (hS : T.IsDiagonalizableSet S) :
    T.IsJointlyDiagonalizable S := by
  rw [lemma51]
  have hdiag : ∀ A ∈ T.RepC S, IsDiagonalizableMat A := by
    rintro _ ⟨a, ha, rfl⟩
    exact (T.lemma49 a).1.1 (hS a ha)
  refine (lemma38 _ hdiag).1 ?_
  rintro _ ⟨a, -, rfl⟩ _ ⟨b, -, rfl⟩
  simp only
  rw [← dg_map_ofReal_mul, ← dg_map_ofReal_mul, ← (T.lemma43 0 a b).2.2.2.2,
    ← (T.lemma43 0 b a).2.2.2.2, T.mul_comm]

/-- **Lemma 53.** If `S ⊆ ℝⁿ` is diagonalizable, then `span(S)` is diagonalizable. -/
theorem lemma53 (S : Set (Fin n → ℝ)) (hS : T.IsDiagonalizableSet S) :
    T.IsDiagonalizableSet (Submodule.span ℝ S) := by
  obtain ⟨P, hP, hD⟩ := (T.lemma51 S).1 (T.lemma52 S hS)
  have key : ∀ b ∈ Submodule.span ℝ S,
      (P * (T.repMat b).map ((↑) : ℝ → ℂ) * P⁻¹).IsDiag := by
    intro b hb
    induction hb using Submodule.span_induction with
    | mem x hx => exact hD _ ⟨x, hx, rfl⟩
    | zero =>
      rw [T.lemma41.1, Matrix.map_zero _ Complex.ofReal_zero, Matrix.mul_zero, Matrix.zero_mul]
      exact isDiag_zero
    | add x y _ _ hx hy =>
      rw [(T.lemma43 0 x y).2.1, dg_map_ofReal_add, Matrix.mul_add, Matrix.add_mul]
      exact hx.add hy
    | smul r x _ hx =>
      rw [(T.lemma43 r x x).2.2.1, dg_map_ofReal_smul, Matrix.mul_smul, Matrix.smul_mul]
      exact hx.smul _
  intro b hb
  exact (T.lemma49 b).1.2 ⟨P, hP, key b hb⟩

/-- Matrices agreeing on all real vectors are equal. -/
private lemma dg_ext_toC {A B : Matrix (Fin n) (Fin n) ℂ}
    (h : ∀ x : Fin n → ℝ, A *ᵥ toC x = B *ᵥ toC x) : A = B := by
  ext i k
  have e : toC (Pi.single k (1 : ℝ)) = Pi.single k (1 : ℂ) := by
    funext l; by_cases hl : l = k
    · subst hl; simp [toC]
    · simp [toC, hl]
  have := congrFun (h (Pi.single k 1)) i
  rw [e, Matrix.mulVec_single_one, Matrix.mulVec_single_one] at this
  exact this

private lemma dg_repMat_mulVec_toC (a x : Fin n → ℝ) :
    (T.repMat a).map (↑) *ᵥ toC x = toC (T.mul a x) := by
  rw [← mulC_eq_repMat_mulVec]
  have h1 : (fun j => (toC x j).re) = x := funext fun j => by simp
  have h2 : (fun j => (toC x j).im) = 0 := funext fun j => by simp
  funext i
  apply Complex.ext
  · show T.mul a (fun j => (toC x j).re) i = (toC (T.mul a x) i).re
    rw [h1, toC_apply, Complex.ofReal_re]
  · show T.mul a (fun j => (toC x j).im) i = (toC (T.mul a x) i).im
    rw [h2, T.mul_zero, toC_apply, Complex.ofReal_im, Pi.zero_apply]

/-- **Proposition 54.** A tubal ring is diagonalizable if and only if there exists an
invertible `M ∈ ℂ^{n×n}` such that for all `a, b ∈ ℝⁿ`, `a · b = M⁻¹ (M a • M b)`. -/
theorem prop54 :
    T.IsDiagonalizableRing ↔
      ∃ M : Matrix (Fin n) (Fin n) ℂ, IsUnit M ∧
        ∀ a b : Fin n → ℝ, toC (T.mul a b) = starMC M (toC a) (toC b) := by
  constructor
  · intro hT
    obtain ⟨P, hP, hD⟩ := (T.lemma51 Set.univ).1 (T.lemma52 Set.univ hT)
    have hPdet : IsUnit P.det := (Matrix.isUnit_iff_isUnit_det P).1 hP
    set Rc : (Fin n → ℝ) → Matrix (Fin n) (Fin n) ℂ := fun a => (T.repMat a).map (↑) with hRc
    have hDa : ∀ a, (P * Rc a * P⁻¹).IsDiag := fun a => hD _ ⟨a, Set.mem_univ a, rfl⟩
    have hRadd : ∀ a b, Rc (a + b) = Rc a + Rc b := fun a b => by
      simp only [hRc]; rw [(T.lemma43 0 a b).2.1, dg_map_ofReal_add]
    have hRsmul : ∀ (r : ℝ) a, Rc (r • a) = (r : ℂ) • Rc a := fun r a => by
      simp only [hRc]; rw [(T.lemma43 r a a).2.2.1, dg_map_ofReal_smul]
    let f : Fin n → (Fin n → ℝ) →ₗ[ℝ] ℂ := fun j =>
      { toFun := fun a => (P * Rc a * P⁻¹) j j
        map_add' := fun a b => by
          show (P * Rc (a + b) * P⁻¹) j j = (P * Rc a * P⁻¹) j j + (P * Rc b * P⁻¹) j j
          rw [hRadd, Matrix.mul_add, Matrix.add_mul, Matrix.add_apply]
        map_smul' := fun r a => by
          show (P * Rc (r • a) * P⁻¹) j j = (RingHom.id ℝ r) • (P * Rc a * P⁻¹) j j
          rw [hRsmul, Matrix.mul_smul, Matrix.smul_mul, Matrix.smul_apply, RingHom.id_apply,
            Complex.real_smul, smul_eq_mul] }
    let M : Matrix (Fin n) (Fin n) ℂ := Matrix.of fun j k => f j (fun l => if k = l then 1 else 0)
    have hM : ∀ a, M *ᵥ toC a = fun j => (P * Rc a * P⁻¹) j j := by
      intro a
      funext j
      change _ = f j a
      rw [(f j).pi_apply_eq_sum_univ a]
      simp only [Matrix.mulVec, dotProduct, toC_apply, M, Matrix.of_apply, Complex.real_smul]
      exact Finset.sum_congr rfl fun k _ => _root_.mul_comm _ _
    have hDdiag : ∀ a, P * Rc a * P⁻¹ = diagonal (M *ᵥ toC a) := by
      intro a
      rw [hM a]
      exact (hDa a).diagonal_diag.symm
    have hRcP : ∀ a, Rc a = P⁻¹ * diagonal (M *ᵥ toC a) * P := by
      intro a
      rw [← hDdiag a]
      simp only [Matrix.mul_assoc, Matrix.nonsing_inv_mul P hPdet, Matrix.mul_one,
        Matrix.nonsing_inv_mul_cancel_left P _ hPdet]
    have hRe : Rc T.one = 1 := by
      simp only [hRc]
      rw [(T.lemma43 0 0 0).2.2.2.1 T.one fun a => ⟨T.one_mul a, T.mul_one a⟩]
      exact Matrix.map_one _ Complex.ofReal_zero Complex.ofReal_one
    have hMe : M *ᵥ toC T.one = 1 := by
      apply Matrix.diagonal_injective
      rw [← hDdiag, hRe, Matrix.mul_one, Matrix.mul_nonsing_inv P hPdet]
      exact Matrix.diagonal_one.symm
    set β := P *ᵥ toC T.one with hβ
    have hPb : ∀ b, P *ᵥ toC b = (M *ᵥ toC b) * β := by
      intro b
      conv_lhs => rw [← T.mul_one b, ← dg_repMat_mulVec_toC]
      change P *ᵥ (Rc b *ᵥ toC T.one) = _
      rw [hRcP b, Matrix.mulVec_mulVec, ← Matrix.mul_assoc, ← Matrix.mul_assoc,
        Matrix.mul_nonsing_inv P hPdet, Matrix.one_mul, ← Matrix.mulVec_mulVec, ← hβ]
      funext j
      rw [Matrix.mulVec_diagonal, Pi.mul_apply]
    have hab : ∀ a b, toC (T.mul a b) =
        (P⁻¹ * diagonal β) *ᵥ ((M *ᵥ toC a) * (M *ᵥ toC b)) := by
      intro a b
      rw [← dg_repMat_mulVec_toC]
      change Rc a *ᵥ toC b = _
      rw [hRcP a, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, hPb]
      congr 1
      funext j
      simp only [Matrix.mulVec_diagonal, Pi.mul_apply]
      ring
    have hN : P⁻¹ * diagonal β * M = 1 := by
      apply dg_ext_toC
      intro x
      have h := hab x T.one
      rw [T.mul_one, hMe, _root_.mul_one] at h
      rw [← Matrix.mulVec_mulVec, Matrix.one_mulVec, ← h]
    have hMdet : IsUnit M.det := Matrix.isUnit_det_of_left_inverse hN
    refine ⟨M, (Matrix.isUnit_iff_isUnit_det M).2 hMdet, fun a b => ?_⟩
    rw [starMC, Matrix.inv_eq_left_inv hN, hab]
  · rintro ⟨M, hM, hmul⟩ a _
    have hMdet : IsUnit M.det := (Matrix.isUnit_iff_isUnit_det M).1 hM
    have hR : (T.repMat a).map (↑) = M⁻¹ * diagonal (M *ᵥ toC a) * M := by
      apply dg_ext_toC
      intro x
      rw [dg_repMat_mulVec_toC, hmul, starMC, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec]
      congr 1
      funext j
      rw [Matrix.mulVec_diagonal, Pi.mul_apply]
    refine (T.lemma49 a).1.2 ⟨M, hM, ?_⟩
    rw [hR]
    simp only [Matrix.mul_assoc, Matrix.mul_nonsing_inv M hMdet, Matrix.mul_one,
      Matrix.mul_nonsing_inv_cancel_left M _ hMdet]
    exact isDiag_diagonal _

end TubalRing

end Tubal
