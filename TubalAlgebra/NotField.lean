import TubalAlgebra.KMRing
import TubalAlgebra.Frobenius

/-!
# Proposition 5: `𝕂_M` is (in general) not a field
-/

open Matrix Complex

noncomputable section

namespace Tubal

variable {n : ℕ}

/-- **Proposition 5.** The ring `𝕂_M` is not a field, unless `n = 1` or `n = 2`, since there are
elements that do not have a multiplicative inverse (so it is not a division ring).

Formally: if `n ∉ {1, 2}` then `𝕂_M` is not a field, and (when `n ≠ 0`, i.e. there are
non-zero tubes at all) there is a non-zero element with no multiplicative inverse. -/
theorem prop5 (M : Matrix (Fin n) (Fin n) ℂ) [Fact (Admissible M)] (hn : n ≠ 1 ∧ n ≠ 2) :
    ¬ IsField (KM M) ∧ (n ≠ 0 → ∃ a : KM M, a ≠ 0 ∧ ∀ b : KM M, a * b ≠ 1) := by
  have hnf : ¬ IsField (KM M) := by
    intro h
    rcases Nat.eq_zero_or_pos n with hn0 | hnpos
    · obtain ⟨x, y, hxy⟩ := h.exists_pair_ne
      subst hn0
      exact hxy (KM.ext (funext fun i => i.elim0))
    · let _ := h.toField
      have : FiniteDimensional ℝ (KM M) :=
        LinearEquiv.finiteDimensional (KM.linearEquivVec (M := M)).symm
      have := finrank_field_over_real (KM M)
      rw [KM.finrank_eq] at this
      omega
  refine ⟨hnf, fun hn0 => ?_⟩
  by_contra hcon
  push Not at hcon
  apply hnf
  refine ⟨⟨1, 0, fun h => ?_⟩, fun {a b} => mul_comm a b, fun {a} ha => ?_⟩
  · have := congrFun (congrArg KM.hat h) ⟨0, Nat.pos_of_ne_zero hn0⟩
    simp at this
  · exact hcon a ha

end Tubal
