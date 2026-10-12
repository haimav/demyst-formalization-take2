import TubalAlgebra.Section9.Ideals
import TubalAlgebra.Section9.Diagonalizable
import TubalAlgebra.Frobenius

/-!
# Diagonalizability of tubal sub-fields (Section 9.5: Proposition 62)
-/

open Matrix Complex

noncomputable section

namespace Tubal

variable {n : ℕ}

namespace TubalRing

variable (T : TubalRing n)

/-- **Proposition 62.** A tubal sub-field is diagonalizable. -/
theorem prop62 (V : Submodule ℝ (Fin n → ℝ)) (hV : T.IsTubalSubfield V) :
    T.IsDiagonalizableSet V := by
  sorry

end TubalRing

end Tubal
