import TubalAlgebra.Section9.SubField

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
  sorry

/-- **Theorem 11** (Main Result). Suppose that `(ℝⁿ, +, ·)` is a tubal ring. Then, there exists
an invertible matrix `M ∈ ℂ^{n×n}` such that for all `a, b ∈ ℝⁿ`, we have `a · b = a ⋆_M b`. -/
theorem theorem11 (T : TubalRing n) :
    ∃ M : Matrix (Fin n) (Fin n) ℂ, IsUnit M ∧
      ∀ a b : Fin n → ℝ, toC (T.mul a b) = starMC M (toC a) (toC b) := by
  sorry

/-- Combined with Lemma 2: the matrix `M` of Theorem 11 is admissible, i.e. the tubal ring is
(the ring structure of) `𝕂_M`. -/
theorem theorem11_admissible (T : TubalRing n) :
    ∃ M : Matrix (Fin n) (Fin n) ℂ, Admissible M ∧
      ∀ a b : Fin n → ℝ, toC (T.mul a b) = starMC M (toC a) (toC b) := by
  sorry

/-- Section 9 preamble: "we denote … by `a⁻` the unique element for which `a = a·a⁻·a` and
`a⁻ = a⁻·a·a⁻`, eschewing the previous definition in Eq. (7) … Once we prove Theorem 11 the
two definitions coincide": if `a · b = M⁻¹ (M a • M b)` for an invertible `M` (as provided by
Theorem 11), then `a⁻ = M⁻¹ (M a)⁺`. -/
theorem TubalRing.winv_eq_eq7 (T : TubalRing n) (M : Matrix (Fin n) (Fin n) ℂ) (hM : IsUnit M)
    (hT : ∀ a b : Fin n → ℝ, toC (T.mul a b) = starMC M (toC a) (toC b)) (a : Fin n → ℝ) :
    toC (T.winv a) = M⁻¹ *ᵥ pinvVec (M *ᵥ toC a) := by
  sorry

/-- The two definitions of the weak inverse coincide for every tubal ring: with `M` from
Theorem 11. -/
theorem TubalRing.exists_winv_eq_eq7 (T : TubalRing n) :
    ∃ M : Matrix (Fin n) (Fin n) ℂ, IsUnit M ∧
      ∀ a : Fin n → ℝ, toC (T.winv a) = M⁻¹ *ᵥ pinvVec (M *ᵥ toC a) := by
  sorry

/-- "As Example 4 shows, the last theorem does not hold if we restrict `M` to be real": for
the tubal ring of complex numbers on `ℝ²`, no real `M` works. -/
theorem theorem11_not_real :
    ∃ T : TubalRing 2, ¬ ∃ M : Matrix (Fin 2) (Fin 2) ℝ, IsUnit M ∧
      ∀ a b : Fin 2 → ℝ, toC (T.mul a b) = starMC (M.map (↑)) (toC a) (toC b) := by
  sorry

end Tubal
