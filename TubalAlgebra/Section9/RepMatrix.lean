import TubalAlgebra.TubalRing

/-!
# Sub-algebra of matrices (Section 9.1: Definitions 39, 45, Example 40, Lemmas 41–43,
Corollary 44, Lemma 46)

Throughout Section 9, `(ℝⁿ, +, ·)` is a tubal ring `T`.
-/

open Matrix Complex

noncomputable section

namespace Tubal

variable {n : ℕ}

/-- The matrix of the map `x ↦ mul a x` (with respect to the standard basis). -/
def repMatOf (mul : (Fin n → ℝ) → (Fin n → ℝ) → (Fin n → ℝ)) (a : Fin n → ℝ) :
    Matrix (Fin n) (Fin n) ℝ :=
  fun i j => mul a (Pi.single j 1) i

namespace TubalRing

variable (T : TubalRing n)

/-- **Definition 39.** Given `a ∈ ℝⁿ`, the unique matrix `R_a ∈ ℝ^{n×n}` for which
`R_a x = a · x` for all `x` is called the representation matrix of `a`. -/
def repMat (a : Fin n → ℝ) : Matrix (Fin n) (Fin n) ℝ := repMatOf T.mul a

/-- **Definition 39**: `R_a x = a · x` for all `x` … -/
theorem repMat_mulVec (a x : Fin n → ℝ) : T.repMat a *ᵥ x = T.mul a x := by
  have h : T.repMat a = LinearMap.toMatrix' (T.mulLeft a) := by
    ext i j
    rw [LinearMap.toMatrix'_apply]
    rfl
  rw [h, LinearMap.toMatrix'_mulVec]
  rfl

/-- **Definition 39**: … and `R_a` is the unique such matrix. -/
theorem repMat_unique (a : Fin n → ℝ) (R : Matrix (Fin n) (Fin n) ℝ)
    (hR : ∀ x, R *ᵥ x = T.mul a x) : R = T.repMat a := by
  ext i j
  have := congrFun (hR (Pi.single j 1)) i
  rw [Matrix.mulVec_single_one] at this
  exact this

/-- **Definition 39**: `Rep(S) := {R_a : a ∈ S}`. -/
def Rep (S : Set (Fin n → ℝ)) : Set (Matrix (Fin n) (Fin n) ℝ) := T.repMat '' S

/-- **Lemma 41.** `R_{0_n} = 0_{n×n}`. There is no non-zero `x` for which `R_x = 0_{n×n}`. -/
theorem lemma41 : T.repMat 0 = 0 ∧ ∀ x, T.repMat x = 0 → x = 0 := by
  refine ⟨?_, fun x hx => ?_⟩
  · ext i j
    simp [repMat, repMatOf, T.zero_mul]
  · have := T.repMat_mulVec x T.one
    rw [hx, Matrix.zero_mulVec, T.mul_one] at this
    exact this.symm

/-- **Lemma 42.** The map `a ↦ R_a` is injective. -/
theorem lemma42 : Function.Injective T.repMat := by
  intro a b h
  have ha := T.repMat_mulVec a T.one
  have hb := T.repMat_mulVec b T.one
  rw [T.mul_one] at ha hb
  rw [← ha, ← hb, h]

/-- **Lemma 43.** For any `α ∈ ℝ` and `x, y ∈ ℝⁿ`:
1. `R_{-x} = -R_x`; 2. `R_{x+y} = R_x + R_y`; 3. `R_{αx} = α R_x`;
4. if `e` denotes the multiplicative identity element in the ring, `R_e = I_n`;
5. `R_{x·y} = R_x R_y`. -/
theorem lemma43 (α : ℝ) (x y : Fin n → ℝ) :
    T.repMat (-x) = -T.repMat x ∧
    T.repMat (x + y) = T.repMat x + T.repMat y ∧
    T.repMat (α • x) = α • T.repMat x ∧
    (∀ e, (∀ a, T.mul e a = a ∧ T.mul a e = a) → T.repMat e = 1) ∧
    T.repMat (T.mul x y) = T.repMat x * T.repMat y := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · ext i j; simp [repMat, repMatOf, T.neg_mul]
  · ext i j; simp [repMat, repMatOf, T.right_distrib]
  · ext i j; simp [repMat, repMatOf, T.smul_mul]
  · intro e he
    ext i j
    simp [repMat, repMatOf, (he _).1, Matrix.one_apply, Pi.single_apply]
  · symm
    apply T.repMat_unique
    intro z
    rw [← Matrix.mulVec_mulVec, T.repMat_mulVec, T.repMat_mulVec, T.mul_assoc]

/-- **Corollary 44.** `Rep(ℝⁿ)` is a linear subspace of `ℝ^{n×n}`, and also an algebra (so is a
sub-algebra of `ℝ^{n×n}`). -/
theorem cor44 :
    (∃ V : Submodule ℝ (Matrix (Fin n) (Fin n) ℝ), (V : Set _) = T.Rep Set.univ) ∧
    (∃ A : Subalgebra ℝ (Matrix (Fin n) (Fin n) ℝ), (A : Set _) = T.Rep Set.univ) := by
  have hrange : T.Rep Set.univ = Set.range T.repMat := Set.image_univ
  have hmul : ∀ x y, T.repMat x * T.repMat y = T.repMat (T.mul x y) := fun x y =>
    (T.lemma43 0 x y).2.2.2.2.symm
  have hadd : ∀ x y, T.repMat x + T.repMat y = T.repMat (x + y) := fun x y =>
    (T.lemma43 0 x y).2.1.symm
  have hsmul : ∀ (r : ℝ) x, r • T.repMat x = T.repMat (r • x) := fun r x =>
    (T.lemma43 r x x).2.2.1.symm
  have hone : T.repMat T.one = 1 :=
    (T.lemma43 0 0 0).2.2.2.1 T.one fun a => ⟨T.one_mul a, T.mul_one a⟩
  have hzero : T.repMat 0 = 0 := T.lemma41.1
  let V : Submodule ℝ (Matrix (Fin n) (Fin n) ℝ) :=
    { carrier := Set.range T.repMat
      add_mem' := by rintro _ _ ⟨x, rfl⟩ ⟨y, rfl⟩; exact ⟨x + y, (hadd x y).symm⟩
      zero_mem' := ⟨0, hzero⟩
      smul_mem' := by rintro r _ ⟨x, rfl⟩; exact ⟨r • x, (hsmul r x).symm⟩ }
  let A : Subalgebra ℝ (Matrix (Fin n) (Fin n) ℝ) :=
    { carrier := Set.range T.repMat
      mul_mem' := by rintro _ _ ⟨x, rfl⟩ ⟨y, rfl⟩; exact ⟨T.mul x y, (hmul x y).symm⟩
      one_mem' := ⟨T.one, hone⟩
      add_mem' := by rintro _ _ ⟨x, rfl⟩ ⟨y, rfl⟩; exact ⟨x + y, (hadd x y).symm⟩
      zero_mem' := ⟨0, hzero⟩
      algebraMap_mem' := by
        intro r
        refine ⟨r • T.one, ?_⟩
        rw [← hsmul, hone, Algebra.algebraMap_eq_smul_one] }
  exact ⟨⟨V, hrange.symm⟩, ⟨A, hrange.symm⟩⟩

/-- **Definition 45.** An element `a ∈ ℝⁿ` is called idempotent if `a · a = a`. -/
def IsIdempotent (a : Fin n → ℝ) : Prop := T.mul a a = a

/-- **Lemma 46.** `a ∈ ℝⁿ` is idempotent if and only if the matrix `R_a` is idempotent. -/
theorem lemma46 (a : Fin n → ℝ) : T.IsIdempotent a ↔ IsIdempotentElem (T.repMat a) := by
  unfold IsIdempotent IsIdempotentElem
  rw [← (T.lemma43 0 a a).2.2.2.2]
  exact T.lemma42.eq_iff.symm

end TubalRing

/-- **Example 40** (Representation matrix for `⋆_M`). Consider the `·` defined by Eq. (5) for
some `M ∈ ℂ^{n×n}` (admissible, so that `(ℝⁿ, +, ⋆_M)` is a tubal ring). Then
`R_a = M⁻¹ diag(M a) M`. -/
theorem example40 (M : Matrix (Fin n) (Fin n) ℂ) [Fact (Admissible M)] (a : Fin n → ℝ) :
    ((KM.toTubalRing M).repMat a).map (↑) = M⁻¹ * diagonal (M *ᵥ toC a) * M := by
  ext i j
  have h := congrFun (KM.toTubalRing_mul M a (Pi.single j 1)) i
  simp only [Matrix.map_apply, TubalRing.repMat, repMatOf]
  rw [toC_apply] at h
  rw [h, starMC]
  have e : toC (Pi.single j (1 : ℝ)) = Pi.single j (1 : ℂ) := by
    funext k; by_cases hk : k = j
    · subst hk; simp [toC]
    · simp [toC, hk]
  rw [e]
  have h2 : (M⁻¹ * diagonal (M *ᵥ toC a) * M) i j =
      ((M⁻¹ * diagonal (M *ᵥ toC a) * M) *ᵥ Pi.single j 1) i := by
    rw [Matrix.mulVec_single_one]; rfl
  rw [h2, ← mulVec_mulVec, ← mulVec_mulVec]
  congr 2
  funext l
  simp [mulVec_diagonal]

end Tubal
