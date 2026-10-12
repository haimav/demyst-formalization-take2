import TubalAlgebra.Section9.RepMatrix

/-!
# Sub-rings, ideals and idempotent elements (Sections 9.3, 9.4: Definitions 55, 56,
Lemmas 57–60, Corollary 61)
-/

open Matrix Complex

noncomputable section

namespace Tubal

variable {n : ℕ}

namespace TubalRing

variable (T : TubalRing n)

/-- `e` is a unit element of the sub-ring `V` (`e ∈ V` and `e · v = v · e = v` for `v ∈ V`). -/
def IsUnitOf (V : Submodule ℝ (Fin n → ℝ)) (e : Fin n → ℝ) : Prop :=
  e ∈ V ∧ ∀ v ∈ V, T.mul e v = v ∧ T.mul v e = v

/-- **Definition 55.** Let `V ⊆ ℝⁿ` be a linear subspace. `(V, +, ·)` is a tubal sub-ring if
it is a commutative, unital, von Neumann regular ring, which is also an associative algebra
over `ℝ`, and `V` is an ideal in `(ℝⁿ, +, ·)` (if `x ∈ V` and `a ∈ ℝⁿ` then `a · x ∈ V`).

(Commutativity, associativity, distributivity and compatibility with scalars are inherited
from the tubal ring `(ℝⁿ, +, ·)`, so only closure, the unit, von Neumann regularity inside
`V`, and the ideal property need to be required.) -/
structure IsTubalSubring (V : Submodule ℝ (Fin n → ℝ)) : Prop where
  /-- `(V, +, ·)` is a ring: `V` is closed under `·`. -/
  mul_mem : ∀ a ∈ V, ∀ b ∈ V, T.mul a b ∈ V
  /-- `(V, +, ·)` is unital. -/
  unital : ∃ e, T.IsUnitOf V e
  /-- `(V, +, ·)` is von Neumann regular. -/
  vonNeumann : ∀ a ∈ V, ∃ x ∈ V, a = T.mul (T.mul a x) a
  /-- `V` is an ideal in `(ℝⁿ, +, ·)`. -/
  isIdeal : ∀ x ∈ V, ∀ a : Fin n → ℝ, T.mul a x ∈ V

/-- **Definition 56.** For `a ∈ ℝⁿ`, the principal ideal associated with `a` is
`(a) := {x · a : x ∈ ℝⁿ}`. -/
def principalSet (a : Fin n → ℝ) : Set (Fin n → ℝ) := {y | ∃ x, y = T.mul x a}

/-- **Lemma 57.** `((a), +, ·)` is a tubal sub-ring (in particular `(a)` is a linear
subspace). -/
theorem lemma57 (a : Fin n → ℝ) :
    ∃ V : Submodule ℝ (Fin n → ℝ), (V : Set (Fin n → ℝ)) = T.principalSet a ∧
      T.IsTubalSubring V := by
  sorry

/-- The principal ideal `(a)` as a linear subspace (Lemma 57). -/
def principal (a : Fin n → ℝ) : Submodule ℝ (Fin n → ℝ) := (T.lemma57 a).choose

theorem coe_principal (a : Fin n → ℝ) :
    (T.principal a : Set (Fin n → ℝ)) = T.principalSet a := (T.lemma57 a).choose_spec.1

theorem principal_isTubalSubring (a : Fin n → ℝ) : T.IsTubalSubring (T.principal a) :=
  (T.lemma57 a).choose_spec.2

/-- **Lemma 58.** If `(V, +, ·)` is a tubal sub-ring, then there is a unique idempotent
`e_V ∈ ℝⁿ` such that `V = (e_V)`. -/
theorem lemma58 (V : Submodule ℝ (Fin n → ℝ)) (hV : T.IsTubalSubring V) :
    ∃! e : Fin n → ℝ, T.IsIdempotent e ∧ V = T.principal e := by
  sorry

/-- **Lemma 59.** Suppose `(V, +, ·)` is a tubal sub-ring, and denote by `e_V` its unique unit
element. Then for every idempotent `p ∈ V` we have `V = (p) ⊕ (e_V - p)`. -/
theorem lemma59 (V : Submodule ℝ (Fin n → ℝ)) (hV : T.IsTubalSubring V) (eV : Fin n → ℝ)
    (heV : T.IsUnitOf V eV) (p : Fin n → ℝ) (hp : p ∈ V) (hpi : T.IsIdempotent p) :
    T.principal p ⊓ T.principal (eV - p) = ⊥ ∧ T.principal p ⊔ T.principal (eV - p) = V := by
  sorry

/-- `(V, +, ·)` is a division ring: every non-zero element of `V` has a multiplicative inverse
in `V` (with respect to the unit `e_V` of `V`). This is the definition recalled in Section 9.4:
"a ring is called a division ring if every non-zero element has a multiplicative inverse". -/
def IsDivisionSubring (V : Submodule ℝ (Fin n → ℝ)) : Prop :=
  ∃ e, T.IsUnitOf V e ∧ ∀ a ∈ V, a ≠ 0 → ∃ b ∈ V, T.mul a b = e

/-- A tubal sub-field: a tubal sub-ring that is also a division ring (Section 9.4). -/
def IsTubalSubfield (V : Submodule ℝ (Fin n → ℝ)) : Prop :=
  T.IsTubalSubring V ∧ T.IsDivisionSubring V

/-- **Lemma 60.** Suppose a tubal sub-ring `V` is not a division ring. Then there exists a
non-trivial idempotent element in `V` (i.e. an idempotent `p ∈ V` with `p ≠ 0_n` and
`p ≠ e_V`). -/
theorem lemma60 (V : Submodule ℝ (Fin n → ℝ)) (hV : T.IsTubalSubring V)
    (hnd : ¬ T.IsDivisionSubring V) :
    ∃ p ∈ V, T.IsIdempotent p ∧ p ≠ 0 ∧ ∀ eV, T.IsUnitOf V eV → p ≠ eV := by
  sorry

/-- **Corollary 61.** Let `V` be a tubal sub-ring. There exist idempotent elements
`p₁, …, p_N ∈ ℝⁿ`, for a finite `N`, such that `V = (p₁) ⊕ (p₂) ⊕ ⋯ ⊕ (p_N)` and `(pⱼ)` are
tubal sub-fields for all `j = 1, …, N`. -/
theorem cor61 (V : Submodule ℝ (Fin n → ℝ)) (hV : T.IsTubalSubring V) :
    ∃ (N : ℕ) (p : Fin N → Fin n → ℝ),
      (∀ j, T.IsIdempotent (p j)) ∧
      (∀ j, T.IsTubalSubfield (T.principal (p j))) ∧
      iSupIndep (fun j => T.principal (p j)) ∧
      (⨆ j, T.principal (p j)) = V := by
  sorry

/-- `ℝⁿ` itself is a tubal sub-ring. -/
theorem top_isTubalSubring : T.IsTubalSubring ⊤ := by
  sorry

end TubalRing

end Tubal
