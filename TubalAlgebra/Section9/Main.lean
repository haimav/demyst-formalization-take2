import TubalAlgebra.Section9.SubField
import TubalAlgebra.Examples.Section3

/-!
# Theorem 11 (Main Result) — Section 9.6 "Bringing it all together"

Corollary 61 decomposes `ℝⁿ` into a direct sum of tubal sub-fields, Proposition 62 shows each
is diagonalizable, Lemma 53 shows the span of their union (i.e. `ℝⁿ`) is diagonalizable, and
Proposition 54 concludes.
-/

open Matrix Complex

noncomputable section

namespace Tubal

variable {n : ℕ}

/-- The tubal ring `(ℝⁿ, +, ·)` is diagonalizable (Section 9.6). -/
theorem TubalRing.isDiagonalizableRing (T : TubalRing n) : T.IsDiagonalizableRing := by
  -- Corollary 61: `ℝⁿ = (p₁) ⊕ ⋯ ⊕ (p_N)` with tubal sub-fields `(pⱼ)`
  obtain ⟨N, p, -, hfield, -, hsup⟩ := T.cor61 ⊤ T.top_isTubalSubring
  -- Proposition 62: each `(pⱼ)` is diagonalizable, hence so is their union
  set S : Set (Fin n → ℝ) := ⋃ j, (T.principal (p j) : Set (Fin n → ℝ)) with hSdef
  have hS : T.IsDiagonalizableSet S := by
    intro a ha
    rw [Set.mem_iUnion] at ha
    obtain ⟨j, hj⟩ := ha
    exact T.prop62 _ (hfield j) a hj
  -- the union spans `ℝⁿ`
  have hspan : Submodule.span ℝ S = ⊤ := by
    rw [hSdef, Submodule.span_iUnion]
    simp only [Submodule.span_eq]
    exact hsup
  -- Lemma 53
  have h53 := T.lemma53 S hS
  rw [hspan] at h53
  intro a _
  exact h53 a (Submodule.mem_top)

/-- **Theorem 11** (Main Result). Suppose that `(ℝⁿ, +, ·)` is a tubal ring. Then, there exists
an invertible matrix `M ∈ ℂ^{n×n}` such that for all `a, b ∈ ℝⁿ`, we have `a · b = a ⋆_M b`. -/
theorem theorem11 (T : TubalRing n) :
    ∃ M : Matrix (Fin n) (Fin n) ℂ, IsUnit M ∧
      ∀ a b : Fin n → ℝ, toC (T.mul a b) = starMC M (toC a) (toC b) := by
  exact (T.prop54).mp T.isDiagonalizableRing

/-- Combined with Lemma 2: the matrix `M` of Theorem 11 is admissible, i.e. the tubal ring is
(the ring structure of) `𝕂_M`. -/
theorem theorem11_admissible (T : TubalRing n) :
    ∃ M : Matrix (Fin n) (Fin n) ℂ, Admissible M ∧
      ∀ a b : Fin n → ℝ, toC (T.mul a b) = starMC M (toC a) (toC b) := by
  obtain ⟨M, hM, h⟩ := theorem11 T
  exact ⟨M, ⟨hM, (lemma65 M hM).mp fun a b => ⟨T.mul a b, h a b⟩⟩, h⟩

/-- Section 9 preamble: "we denote … by `a⁻` the unique element for which `a = a·a⁻·a` and
`a⁻ = a⁻·a·a⁻`, eschewing the previous definition in Eq. (7) … Once we prove Theorem 11 the
two definitions coincide": if `a · b = M⁻¹ (M a • M b)` for an invertible `M` (as provided by
Theorem 11), then `a⁻ = M⁻¹ (M a)⁺`. -/
theorem TubalRing.winv_eq_eq7 (T : TubalRing n) (M : Matrix (Fin n) (Fin n) ℂ) (hM : IsUnit M)
    (hT : ∀ a b : Fin n → ℝ, toC (T.mul a b) = starMC M (toC a) (toC b)) (a : Fin n → ℝ) :
    toC (T.winv a) = M⁻¹ *ᵥ pinvVec (M *ᵥ toC a) := by
  have hadm : Admissible M := ⟨hM, (lemma65 M hM).mp fun a b => ⟨T.mul a b, hT a b⟩⟩
  have : Fact (Admissible M) := ⟨hadm⟩
  have hmul : ∀ x y : Fin n → ℝ, T.mul x y = (KM.mk x * KM.mk y : KM M).vec := by
    intro x y
    apply toC_injective
    rw [hT, KM.toC_vec_mul]
  set w := (KM.weakInv (KM.mk a : KM M)).vec with hw
  have h8 := (lemma8 M (KM.mk a)).1
  have h1 : a = T.mul (T.mul a w) a := by
    rw [hmul, hmul]
    exact (congrArg KM.vec h8.1).symm
  have h2 : w = T.mul (T.mul w a) w := by
    rw [hmul, hmul]
    exact (congrArg KM.vec h8.2.1).symm
  rw [← T.winv_unique a w h1 h2, hw, KM.toC_vec_weakInv]

/-- The two definitions of the weak inverse coincide for every tubal ring: with `M` from
Theorem 11 (an invertible `M` with `a · b = a ⋆_M b`), `a⁻ = M⁻¹ (M a)⁺`. -/
theorem TubalRing.exists_winv_eq_eq7 (T : TubalRing n) :
    ∃ M : Matrix (Fin n) (Fin n) ℂ, IsUnit M ∧
      (∀ a b : Fin n → ℝ, toC (T.mul a b) = starMC M (toC a) (toC b)) ∧
      ∀ a : Fin n → ℝ, toC (T.winv a) = M⁻¹ *ᵥ pinvVec (M *ᵥ toC a) := by
  obtain ⟨M, hM, h⟩ := theorem11 T
  exact ⟨M, hM, h, fun a => T.winv_eq_eq7 M hM h a⟩

/-- "As Example 4 shows, the last theorem does not hold if we restrict `M` to be real": for
the tubal ring of complex numbers on `ℝ²`, no real `M` works. -/
theorem theorem11_not_real :
    ∃ T : TubalRing 2, ¬ ∃ M : Matrix (Fin 2) (Fin 2) ℝ, IsUnit M ∧
      ∀ a b : Fin 2 → ℝ, toC (T.mul a b) = starMC (M.map (↑)) (toC a) (toC b) := by
  exact ⟨complexTubal, example4_no_real_M⟩

end Tubal
