import Mathlib

/-!
# Simultaneous diagonalization (Lemma 38 = Fact 5.17.8 in Bernstein, *Matrix Mathematics*)
-/

open Matrix

noncomputable section

namespace Tubal

variable {n : ℕ}

/-- A matrix `A ∈ ℂ^{n×n}` is diagonalizable (over `ℂ`): there is a nonsingular `S` such that
`S A S⁻¹` is diagonal. -/
def IsDiagonalizableMat (A : Matrix (Fin n) (Fin n) ℂ) : Prop :=
  ∃ S : Matrix (Fin n) (Fin n) ℂ, IsUnit S ∧ (S * A * S⁻¹).IsDiag

/-- A set of matrices is jointly diagonalizable: there is a nonsingular `S` such that `S A S⁻¹`
is diagonal for all `A` in the set. -/
def IsJointlyDiagonalizableMat (𝒮 : Set (Matrix (Fin n) (Fin n) ℂ)) : Prop :=
  ∃ S : Matrix (Fin n) (Fin n) ℂ, IsUnit S ∧ ∀ A ∈ 𝒮, (S * A * S⁻¹).IsDiag

/-- `x` is an eigenvector of the matrix `A` (with some eigenvalue `λ ∈ ℂ`). -/
def IsEigenvectorMat (A : Matrix (Fin n) (Fin n) ℂ) (x : Fin n → ℂ) : Prop :=
  x ≠ 0 ∧ ∃ μ : ℂ, A *ᵥ x = μ • x

namespace SimulDiag

/-- Core of the eigenvector characterizations: a family of matrices is simultaneously
diagonalized by some nonsingular `S` iff there are `n` linearly independent common
eigenvectors (the columns of `S⁻¹`). -/
lemma joint_iff (𝒮 : Set (Matrix (Fin n) (Fin n) ℂ)) :
    (∃ S : Matrix (Fin n) (Fin n) ℂ, IsUnit S ∧ ∀ A ∈ 𝒮, (S * A * S⁻¹).IsDiag) ↔
      ∃ v : Fin n → Fin n → ℂ, LinearIndependent ℂ v ∧
        ∀ A ∈ 𝒮, ∀ i, IsEigenvectorMat A (v i) := by
  constructor
  · rintro ⟨S, hS, hD⟩
    have hdet : IsUnit S.det := (Matrix.isUnit_iff_isUnit_det S).1 hS
    have hli : LinearIndependent ℂ (S⁻¹).col :=
      Matrix.linearIndependent_cols_of_isUnit (Matrix.isUnit_nonsing_inv_iff.2 hS)
    refine ⟨(S⁻¹).col, hli, fun A hA i => ⟨hli.ne_zero i, (S * A * S⁻¹) i i, ?_⟩⟩
    have h1 : A * S⁻¹ = S⁻¹ * (S * A * S⁻¹) := by
      rw [Matrix.mul_assoc S, Matrix.nonsing_inv_mul_cancel_left S _ hdet]
    have h2 : S⁻¹ * (S * A * S⁻¹) = S⁻¹ * diagonal (S * A * S⁻¹).diag := by
      rw [(hD A hA).diagonal_diag]
    ext j
    have h3 := congrFun (congrFun (h1.trans h2) j) i
    rw [Matrix.mul_diagonal, Matrix.mul_apply, Matrix.diag_apply] at h3
    simp only [Matrix.mulVec, dotProduct, Matrix.col_apply, Pi.smul_apply, smul_eq_mul]
    rw [h3, mul_comm]
  · rintro ⟨v, hv, hev⟩
    set P : Matrix (Fin n) (Fin n) ℂ := Matrix.of fun j i => v i j with hPdef
    have hPcol : P.col = v := by ext i j; rfl
    have hP : IsUnit P := Matrix.linearIndependent_cols_iff_isUnit.1 (hPcol ▸ hv)
    have hdet : IsUnit P.det := (Matrix.isUnit_iff_isUnit_det P).1 hP
    refine ⟨P⁻¹, Matrix.isUnit_nonsing_inv_iff.2 hP, fun A hA => ?_⟩
    choose μ hμ using fun i => (hev A hA i).2
    have hAP : A * P = P * diagonal μ := by
      ext j i
      have := congrFun (hμ i) j
      simp only [Matrix.mulVec, dotProduct, Pi.smul_apply, smul_eq_mul] at this
      rw [Matrix.mul_diagonal, Matrix.mul_apply]; simp only [hPdef, Matrix.of_apply]
      rw [this, mul_comm]
    rw [Matrix.nonsing_inv_nonsing_inv _ hdet, Matrix.mul_assoc, hAP,
      Matrix.nonsing_inv_mul_cancel_left P _ hdet]
    exact isDiag_diagonal μ

/-- A pairwise commuting family (indexed by an arbitrary type) of endomorphisms of `ℂ^n` whose
generalized eigenspaces are eigenspaces has `n` linearly independent common eigenvectors. -/
lemma exists_common_eigenvectors {ι : Type*} (f : ι → Module.End ℂ (Fin n → ℂ))
    (hcomm : ∀ i j, Commute (f i) (f j))
    (hss : ∀ i μ, (f i).maxGenEigenspace μ = (f i).eigenspace μ) :
    ∃ v : Fin n → Fin n → ℂ, LinearIndependent ℂ v ∧
      ∀ i k, v k ≠ 0 ∧ ∃ μ : ℂ, f i (v k) = μ • v k := by
  have htop :=
    Module.End.iSup_iInf_maxGenEigenspace_eq_top_of_iSup_maxGenEigenspace_eq_top_of_commute
      f (fun i j _ => hcomm i j) (fun i => Module.End.iSup_maxGenEigenspace_eq_top (f i))
  simp_rw [hss] at htop
  set s : Set (Fin n → ℂ) := {x | x ≠ 0 ∧ ∀ i, ∃ μ : ℂ, f i x = μ • x} with hs
  have hspan : Submodule.span ℂ s = ⊤ := by
    rw [eq_top_iff, ← htop, iSup_le_iff]
    intro χ x hx
    by_cases h0 : x = 0
    · rw [h0]; exact Submodule.zero_mem _
    · apply Submodule.subset_span
      refine ⟨h0, fun i => ⟨χ i, ?_⟩⟩
      exact Module.End.mem_eigenspace_iff.1 ((Submodule.mem_iInf _).1 hx i)
  obtain ⟨b, hbs, hbspan, hbli⟩ := exists_linearIndependent ℂ s
  let B : Module.Basis b ℂ (Fin n → ℂ) :=
    Module.Basis.mk hbli (by rw [Subtype.range_coe, hbspan, hspan])
  let e := B.indexEquiv (Pi.basisFun ℂ (Fin n))
  refine ⟨fun k => ((e.symm k : b) : Fin n → ℂ), hbli.comp _ e.symm.injective, fun i k => ?_⟩
  exact ⟨(hbs (e.symm k).2).1, (hbs (e.symm k).2).2 i⟩

/-- For a diagonalizable matrix, the maximal generalized eigenspaces are the eigenspaces. -/
lemma maxGenEigenspace_eq_eigenspace_of_isDiagonalizableMat (A : Matrix (Fin n) (Fin n) ℂ)
    (hA : IsDiagonalizableMat A) (μ : ℂ) :
    Module.End.maxGenEigenspace (toLin' A) μ = Module.End.eigenspace (toLin' A) μ := by
  refine le_antisymm (fun x hx => ?_) Module.End.eigenspace_le_maxGenEigenspace
  obtain ⟨S, hS, hD⟩ := hA
  have hdet : IsUnit S.det := (Matrix.isUnit_iff_isUnit_det S).1 hS
  obtain ⟨d, hd⟩ : ∃ d, S * A * S⁻¹ = diagonal d := ⟨_, hD.diagonal_diag.symm⟩
  have hDS : diagonal d * S = S * A := by
    rw [← hd, Matrix.nonsing_inv_mul_cancel_right _ _ hdet]
  have hcomp : (toLin' (diagonal d)).comp (toLin' S) = (toLin' S).comp (toLin' A) := by
    rw [← Matrix.toLin'_mul, ← Matrix.toLin'_mul, hDS]
  have h1 := Module.End.mapsTo_genEigenspace_of_comp (toLin' S) hcomp μ ⊤ hx
  change toLin' S x ∈ Module.End.maxGenEigenspace (toLin' (diagonal d)) μ at h1
  rw [Matrix.maxGenEigenspace_toLin'_diagonal_eq_eigenspace, Module.End.mem_eigenspace_iff] at h1
  have h2 := LinearMap.congr_fun hcomp x
  rw [LinearMap.comp_apply, LinearMap.comp_apply, h1, ← LinearMap.map_smul] at h2
  rw [Module.End.mem_eigenspace_iff]
  have hinj : Function.Injective (toLin' S) := by
    intro x y hxy; simp only [Matrix.toLin'_apply] at hxy
    exact Matrix.mulVec_injective_of_isUnit hS hxy
  exact (hinj h2).symm

end SimulDiag

/-- A matrix is diagonalizable iff it has `n` linearly independent eigenvectors. -/
theorem isDiagonalizableMat_iff_eigenvectors (A : Matrix (Fin n) (Fin n) ℂ) :
    IsDiagonalizableMat A ↔
      ∃ v : Fin n → Fin n → ℂ, LinearIndependent ℂ v ∧ ∀ i, IsEigenvectorMat A (v i) := by
  constructor
  · rintro ⟨S, hS, hD⟩
    obtain ⟨v, hv, hev⟩ := (SimulDiag.joint_iff {A}).1
      ⟨S, hS, fun B hB => by rw [Set.mem_singleton_iff.1 hB]; exact hD⟩
    exact ⟨v, hv, hev A rfl⟩
  · rintro ⟨v, hv, hev⟩
    obtain ⟨S, hS, hD⟩ := (SimulDiag.joint_iff {A}).2
      ⟨v, hv, fun B hB => by rw [Set.mem_singleton_iff.1 hB]; exact hev⟩
    exact ⟨S, hS, hD A rfl⟩

/-- A set of matrices is jointly diagonalizable iff there are `n` linearly independent vectors
which are eigenvectors of all the matrices in the set. -/
theorem isJointlyDiagonalizableMat_iff_eigenvectors (𝒮 : Set (Matrix (Fin n) (Fin n) ℂ)) :
    IsJointlyDiagonalizableMat 𝒮 ↔
      ∃ v : Fin n → Fin n → ℂ, LinearIndependent ℂ v ∧ ∀ A ∈ 𝒮, ∀ i, IsEigenvectorMat A (v i) := by
  exact SimulDiag.joint_iff 𝒮

/-- **Lemma 38** (Fact 5.17.8 in [2]). Let `S ⊆ ℂ^{n×n}`, and assume every matrix `A ∈ S` is
diagonalizable over `ℂ`. Then `AB = BA` for all `A, B ∈ S` if and only if there exists a
nonsingular `S ∈ ℂ^{n×n}` such that, for all `A ∈ S`, `S A S⁻¹` is diagonal.

(The paper writes "for all `A ∈ ℂ^{n×n}`", an evident typo for "for all `A ∈ S`".) -/
theorem lemma38 (𝒮 : Set (Matrix (Fin n) (Fin n) ℂ)) (hdiag : ∀ A ∈ 𝒮, IsDiagonalizableMat A) :
    (∀ A ∈ 𝒮, ∀ B ∈ 𝒮, A * B = B * A) ↔
      ∃ S : Matrix (Fin n) (Fin n) ℂ, IsUnit S ∧ ∀ A ∈ 𝒮, (S * A * S⁻¹).IsDiag := by
  constructor
  · intro hcomm
    change IsJointlyDiagonalizableMat 𝒮
    rw [isJointlyDiagonalizableMat_iff_eigenvectors]
    obtain ⟨v, hv, hev⟩ := SimulDiag.exists_common_eigenvectors
      (fun A : 𝒮 => toLin' (A : Matrix (Fin n) (Fin n) ℂ))
      (fun A B => by
        change toLin' A.1 * toLin' B.1 = toLin' B.1 * toLin' A.1
        rw [Module.End.mul_eq_comp, Module.End.mul_eq_comp, ← Matrix.toLin'_mul,
          ← Matrix.toLin'_mul, hcomm A.1 A.2 B.1 B.2])
      (fun A μ =>
        SimulDiag.maxGenEigenspace_eq_eigenspace_of_isDiagonalizableMat A.1 (hdiag A.1 A.2) μ)
    refine ⟨v, hv, fun A hA i => ⟨(hev ⟨A, hA⟩ i).1, ?_⟩⟩
    obtain ⟨μ, hμ⟩ := (hev ⟨A, hA⟩ i).2
    exact ⟨μ, by simpa only [Matrix.toLin'_apply] using hμ⟩
  · rintro ⟨S, hS, hD⟩ A hA B hB
    have hdet : IsUnit S.det := (Matrix.isUnit_iff_isUnit_det S).1 hS
    obtain ⟨a, ha⟩ : ∃ a, S * A * S⁻¹ = diagonal a := ⟨_, (hD A hA).diagonal_diag.symm⟩
    obtain ⟨b, hb⟩ : ∃ b, S * B * S⁻¹ = diagonal b := ⟨_, (hD B hB).diagonal_diag.symm⟩
    have hA' : A = S⁻¹ * diagonal a * S := by
      rw [← ha]
      simp only [Matrix.mul_assoc, Matrix.nonsing_inv_mul S hdet, Matrix.mul_one,
        Matrix.nonsing_inv_mul_cancel_left S _ hdet]
    have hB' : B = S⁻¹ * diagonal b * S := by
      rw [← hb]
      simp only [Matrix.mul_assoc, Matrix.nonsing_inv_mul S hdet, Matrix.mul_one,
        Matrix.nonsing_inv_mul_cancel_left S _ hdet]
    have hc : diagonal a * diagonal b = diagonal b * diagonal a := by
      rw [diagonal_mul_diagonal, diagonal_mul_diagonal]
      congr 1
      ext i
      exact mul_comm _ _
    rw [hA', hB']
    simp only [Matrix.mul_assoc, Matrix.mul_nonsing_inv_cancel_left S _ hdet]
    rw [← Matrix.mul_assoc (diagonal a), hc, Matrix.mul_assoc]

/-- A matrix annihilated by a polynomial with distinct roots (here: a squarefree polynomial)
is diagonalizable over `ℂ`. -/
theorem isDiagonalizableMat_of_squarefree (A : Matrix (Fin n) (Fin n) ℂ)
    (P : Polynomial ℂ) (hP : Squarefree P) (hPA : Polynomial.aeval A P = 0) :
    IsDiagonalizableMat A := by
  have hss : Module.End.IsSemisimple (toLin' A) := by
    apply Module.End.isSemisimple_of_squarefree_aeval_eq_zero hP
    change Polynomial.aeval (Matrix.toLinAlgEquiv' A) P = 0
    rw [Polynomial.aeval_algHom_apply, hPA, map_zero]
  obtain ⟨v, hv, hev⟩ := SimulDiag.exists_common_eigenvectors (ι := Unit)
    (fun _ => toLin' A) (fun _ _ => Commute.refl _)
    (fun _ μ => hss.isFinitelySemisimple.maxGenEigenspace_eq_eigenspace μ)
  refine (isDiagonalizableMat_iff_eigenvectors A).2 ⟨v, hv, fun i => ⟨(hev () i).1, ?_⟩⟩
  obtain ⟨μ, hμ⟩ := (hev () i).2
  exact ⟨μ, by simpa only [Matrix.toLin'_apply] using hμ⟩

end Tubal
