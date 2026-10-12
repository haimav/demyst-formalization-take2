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
  -- the subspace
  let V : Submodule ℝ (Fin n → ℝ) :=
    { carrier := T.principalSet a
      add_mem' := by
        rintro _ _ ⟨x, rfl⟩ ⟨y, rfl⟩
        exact ⟨x + y, (T.right_distrib x y a).symm⟩
      zero_mem' := ⟨0, (T.zero_mul a).symm⟩
      smul_mem' := by
        rintro r _ ⟨x, rfl⟩
        exact ⟨r • x, (T.smul_mul r x a).symm⟩ }
  refine ⟨V, rfl, ?_⟩
  have hmem : ∀ y, y ∈ V ↔ ∃ x, y = T.mul x a := fun y => Iff.rfl
  -- e_a := a · a⁻
  set e := T.mul a (T.winv a) with he
  have hspec := T.winv_spec a
  have hea : T.mul e a = a := hspec.1.symm
  refine ⟨?_, ⟨e, ⟨?_, fun v hv => ?_⟩⟩, fun v hv => ?_, fun x hx b => ?_⟩
  · rintro _ ⟨x, rfl⟩ _ ⟨y, rfl⟩
    refine ⟨T.mul (T.mul x a) y, ?_⟩
    ac_rfl
  · exact ⟨T.winv a, T.mul_comm _ _⟩
  · obtain ⟨x, rfl⟩ := (hmem v).mp hv
    have h1 : T.mul e (T.mul x a) = T.mul x a := by
      rw [← T.mul_assoc, T.mul_comm e x, T.mul_assoc, hea]
    exact ⟨h1, by rw [T.mul_comm]; exact h1⟩
  · obtain ⟨x, rfl⟩ := (hmem v).mp hv
    refine ⟨T.winv (T.mul x a), ?_, (T.winv_spec _).1⟩
    -- v⁻ = v⁻ · v · v⁻ = (v⁻ · v⁻ · x) · a
    refine ⟨T.mul (T.mul (T.winv (T.mul x a)) (T.winv (T.mul x a))) x, ?_⟩
    conv_lhs => rw [(T.winv_spec (T.mul x a)).2]
    ac_rfl
  · obtain ⟨y, rfl⟩ := (hmem x).mp hx
    exact ⟨T.mul b y, (T.mul_assoc b y a).symm⟩

/-- The principal ideal `(a)` as a linear subspace (Lemma 57). -/
def principal (a : Fin n → ℝ) : Submodule ℝ (Fin n → ℝ) := (T.lemma57 a).choose

theorem coe_principal (a : Fin n → ℝ) :
    (T.principal a : Set (Fin n → ℝ)) = T.principalSet a := (T.lemma57 a).choose_spec.1

theorem principal_isTubalSubring (a : Fin n → ℝ) : T.IsTubalSubring (T.principal a) :=
  (T.lemma57 a).choose_spec.2

theorem mem_principal (a y : Fin n → ℝ) : y ∈ T.principal a ↔ ∃ x, y = T.mul x a := by
  rw [← SetLike.mem_coe, T.coe_principal]
  rfl

/-- Units of a sub-ring are unique. -/
theorem isUnitOf_unique {V : Submodule ℝ (Fin n → ℝ)} {e e' : Fin n → ℝ} (he : T.IsUnitOf V e)
    (he' : T.IsUnitOf V e') : e = e' := by
  have h1 := (he.2 e' he'.1).1
  have h2 := (he'.2 e he.1).2
  rw [← h1, h2]

/-- If `e` is a unit of a sub-ring `V` which is an ideal, then `V = (e)`. -/
theorem eq_principal_of_isUnitOf {V : Submodule ℝ (Fin n → ℝ)} (hV : T.IsTubalSubring V)
    {e : Fin n → ℝ} (he : T.IsUnitOf V e) : V = T.principal e := by
  ext y
  rw [T.mem_principal]
  constructor
  · intro hy
    exact ⟨y, ((he.2 y hy).2).symm⟩
  · rintro ⟨x, rfl⟩
    exact hV.isIdeal e he.1 x

/-- **Lemma 58.** If `(V, +, ·)` is a tubal sub-ring, then there is a unique idempotent
`e_V ∈ ℝⁿ` such that `V = (e_V)`. -/
theorem lemma58 (V : Submodule ℝ (Fin n → ℝ)) (hV : T.IsTubalSubring V) :
    ∃! e : Fin n → ℝ, T.IsIdempotent e ∧ V = T.principal e := by
  obtain ⟨e, he⟩ := hV.unital
  refine ⟨e, ⟨(he.2 e he.1).1, T.eq_principal_of_isUnitOf hV he⟩, ?_⟩
  rintro p ⟨hp, hVp⟩
  have hpV : p ∈ V := by
    rw [hVp, T.mem_principal]; exact ⟨p, hp.symm⟩
  have hpu : T.IsUnitOf V p := by
    refine ⟨hpV, fun v hv => ?_⟩
    rw [hVp, T.mem_principal] at hv
    obtain ⟨x, rfl⟩ := hv
    have h1 : T.mul p (T.mul x p) = T.mul x p := by
      rw [← T.mul_assoc, T.mul_comm p x, T.mul_assoc, hp]
    exact ⟨h1, by rw [T.mul_comm]; exact h1⟩
  exact T.isUnitOf_unique hpu he

/-- **Lemma 59.** Suppose `(V, +, ·)` is a tubal sub-ring, and denote by `e_V` its unique unit
element. Then for every idempotent `p ∈ V` we have `V = (p) ⊕ (e_V - p)`. -/
theorem lemma59 (V : Submodule ℝ (Fin n → ℝ)) (hV : T.IsTubalSubring V) (eV : Fin n → ℝ)
    (heV : T.IsUnitOf V eV) (p : Fin n → ℝ) (hp : p ∈ V) (hpi : T.IsIdempotent p) :
    T.principal p ⊓ T.principal (eV - p) = ⊥ ∧ T.principal p ⊔ T.principal (eV - p) = V := by
  have hpe : T.mul p eV = p := (heV.2 p hp).2
  have hep : eV - p ∈ V := V.sub_mem heV.1 hp
  constructor
  · rw [eq_bot_iff]
    intro x hx
    rw [Submodule.mem_inf, T.mem_principal, T.mem_principal] at hx
    obtain ⟨⟨y, hy⟩, ⟨z, hz⟩⟩ := hx
    rw [Submodule.mem_bot]
    have h1 : T.mul p x = x := by
      rw [hy, T.mul_comm, T.mul_assoc, hpi]
    have h2 : T.mul p x = 0 := by
      rw [hz, T.mul_comm, T.mul_assoc, T.sub_mul, (heV.2 p hp).1, hpi, sub_self, T.mul_zero]
    rw [← h1, h2]
  · apply le_antisymm
    · apply sup_le
      · intro x hx
        rw [T.mem_principal] at hx
        obtain ⟨y, rfl⟩ := hx
        exact hV.isIdeal p hp y
      · intro x hx
        rw [T.mem_principal] at hx
        obtain ⟨y, rfl⟩ := hx
        exact hV.isIdeal _ hep y
    · intro x hx
      have hx' : x = T.mul x p + T.mul x (eV - p) := by
        rw [← T.left_distrib, add_sub_cancel, (heV.2 x hx).2]
      rw [hx']
      apply Submodule.add_mem_sup
      · rw [T.mem_principal]; exact ⟨x, rfl⟩
      · rw [T.mem_principal]; exact ⟨x, rfl⟩

/-- Text after Lemma 59 / Section 9.4: "if we can find a non-trivial idempotent `p ∈ V`, then
both principal ideals `(p)` and `(e_V - p)` are proper subsets of `V`, and so have lower
dimension." -/
theorem finrank_principal_lt (V : Submodule ℝ (Fin n → ℝ)) (hV : T.IsTubalSubring V)
    (eV : Fin n → ℝ) (heV : T.IsUnitOf V eV) (p : Fin n → ℝ) (hp : p ∈ V)
    (hpi : T.IsIdempotent p) (hp0 : p ≠ 0) (hpe : p ≠ eV) :
    T.principal p < V ∧ T.principal (eV - p) < V ∧
    Module.finrank ℝ (T.principal p) < Module.finrank ℝ V ∧
    Module.finrank ℝ (T.principal (eV - p)) < Module.finrank ℝ V := by
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
  obtain ⟨e, he⟩ := hV.unital
  have hnd' : ∃ a ∈ V, a ≠ 0 ∧ ∀ b ∈ V, T.mul a b ≠ e := by
    by_contra hcon
    push Not at hcon
    exact hnd ⟨e, he, hcon⟩
  obtain ⟨a, haV, ha0, hab⟩ := hnd'
  obtain ⟨x, hxV, hx⟩ := hV.vonNeumann a haV
  refine ⟨T.mul a x, hV.mul_mem a haV x hxV, ?_, ?_, ?_⟩
  · unfold IsIdempotent
    calc T.mul (T.mul a x) (T.mul a x) = T.mul (T.mul (T.mul a x) a) x := by
          simp only [T.mul_assoc]
      _ = T.mul a x := by rw [← hx]
  · intro h0
    apply ha0
    rw [hx, h0, T.zero_mul]
  · intro eV heV
    rw [← T.isUnitOf_unique he heV]
    exact hab x hxV

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
