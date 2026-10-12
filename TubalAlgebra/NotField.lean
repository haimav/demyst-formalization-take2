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
  sorry

end Tubal
