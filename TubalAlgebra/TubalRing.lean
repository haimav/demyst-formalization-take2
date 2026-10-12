import TubalAlgebra.KMRing

/-!
# Tubal rings (Definition 10)

A *tubal ring* is a ring `(ℝⁿ, +, ·)`, where `+` is the usual vector addition and `·` is an
arbitrary binary operation for which the ring axioms hold, which is commutative, unital,
von Neumann regular, and is also an associative algebra over `ℝ` with respect to the usual
scalar-vector product.

Since `+` is the usual vector addition, `(ℝⁿ, +)` is automatically an abelian group; the
remaining ring axioms are associativity of `·` and the two distributive laws.

We also provide:
* basic algebraic lemmas for a tubal ring;
* `TubalRing.Elem T`, a type carrying the corresponding Mathlib `CommRing`/`Algebra ℝ`
  structures;
* the weak inverse `T.winv a` (the unique `x` with `a = a·x·a` and `x = x·a·x`, Section 9);
* `KM.toTubalRing`: for admissible `M`, `𝕂_M` is a tubal ring.
-/

open Matrix Complex

noncomputable section

namespace Tubal

variable {n : ℕ}

/-- **Definition 10** (tubal ring). A ring `(ℝⁿ, +, ·)`, where `+` is the usual vector
addition and `·` is an arbitrary binary operation for which the ring axioms hold, is called a
*tubal ring* if it is commutative, unital, von Neumann regular, and is also an associative
algebra over `ℝ` with respect to the usual scalar-vector product. -/
structure TubalRing (n : ℕ) where
  /-- The product `·`. -/
  mul : (Fin n → ℝ) → (Fin n → ℝ) → (Fin n → ℝ)
  /-- Ring axiom: `(ℝⁿ, ·)` is a semigroup. -/
  mul_assoc : ∀ a b c, mul (mul a b) c = mul a (mul b c)
  /-- Ring axiom: left distributivity. -/
  left_distrib : ∀ a b c, mul a (b + c) = mul a b + mul a c
  /-- Ring axiom: right distributivity. -/
  right_distrib : ∀ a b c, mul (a + b) c = mul a c + mul b c
  /-- Commutative. -/
  mul_comm : ∀ a b, mul a b = mul b a
  /-- Unital. -/
  exists_one : ∃ e, ∀ a, mul e a = a ∧ mul a e = a
  /-- Von Neumann regular (Definition 9). -/
  vonNeumann : ∀ a, ∃ x, a = mul (mul a x) a
  /-- Associative algebra over `ℝ`: `(r a) · a' = r (a · a')`. -/
  smul_mul : ∀ (r : ℝ) a b, mul (r • a) b = r • mul a b
  /-- Associative algebra over `ℝ`: `a · (r a') = r (a · a')`. -/
  mul_smul : ∀ (r : ℝ) a b, mul a (r • b) = r • mul a b

/-- The remark after Definition 9: in a commutative von Neumann regular ring, for every `a`
there exists a *unique* `x` with `a = a·x·a` and `x = x·a·x`. -/
theorem vonNeumann_unique (R : Type*) [CommRing R] (h : IsVonNeumannRegularRing R) (a : R) :
    ∃! x : R, a = a * x * a ∧ x = x * a * x := by
  obtain ⟨x, hx⟩ := h a
  have hxa1 : a = a * (x * a * x) * a := by linear_combination (1 + a * x) * hx
  have hxa2 : x * a * x = (x * a * x) * a * (x * a * x) := by
    linear_combination (x ^ 2 + a * x ^ 3) * hx
  refine ⟨x * a * x, ⟨hxa1, hxa2⟩, ?_⟩
  rintro y ⟨h1, h2⟩
  -- `a y` and `a (x a x)` are equal idempotents
  have e : a * y = a * (x * a * x) := by
    linear_combination (x + y) * hx - x * h1
  calc y = y * (a * y) := by linear_combination h2
    _ = y * (a * (x * a * x)) := by rw [e]
    _ = (a * y) * (x * a * x) := by ring
    _ = (a * (x * a * x)) * (x * a * x) := by rw [e]
    _ = x * a * x := by linear_combination -hxa2

namespace TubalRing

variable (T : TubalRing n)

/-- The unit element `e` of a tubal ring. -/
def one : Fin n → ℝ := Classical.choose T.exists_one

theorem one_mul (a : Fin n → ℝ) : T.mul T.one a = a := (Classical.choose_spec T.exists_one a).1

theorem mul_one (a : Fin n → ℝ) : T.mul a T.one = a := (Classical.choose_spec T.exists_one a).2

theorem one_unique (e : Fin n → ℝ) (he : ∀ a, T.mul e a = a) : e = T.one := by
  calc e = T.mul e T.one := (T.mul_one e).symm
    _ = T.one := he T.one

theorem mul_zero (a : Fin n → ℝ) : T.mul a 0 = 0 := by
  have h := T.left_distrib a 0 0
  rw [add_zero] at h
  exact add_eq_left.mp h.symm

theorem zero_mul (a : Fin n → ℝ) : T.mul 0 a = 0 := by
  have h := T.right_distrib 0 0 a
  rw [add_zero] at h
  exact add_eq_left.mp h.symm

theorem mul_neg (a b : Fin n → ℝ) : T.mul a (-b) = -T.mul a b := by
  have h := T.left_distrib a (-b) b
  rw [neg_add_cancel, T.mul_zero] at h
  exact eq_neg_of_add_eq_zero_left h.symm

theorem neg_mul (a b : Fin n → ℝ) : T.mul (-a) b = -T.mul a b := by
  have h := T.right_distrib (-a) a b
  rw [neg_add_cancel, T.zero_mul] at h
  exact eq_neg_of_add_eq_zero_left h.symm

theorem mul_sub (a b c : Fin n → ℝ) : T.mul a (b - c) = T.mul a b - T.mul a c := by
  rw [sub_eq_add_neg, T.left_distrib, T.mul_neg, ← sub_eq_add_neg]

theorem sub_mul (a b c : Fin n → ℝ) : T.mul (a - b) c = T.mul a c - T.mul b c := by
  rw [sub_eq_add_neg, T.right_distrib, T.neg_mul, ← sub_eq_add_neg]

/-- For each `a`, the map `x ↦ a · x` as an `ℝ`-linear map. -/
def mulLeft (a : Fin n → ℝ) : (Fin n → ℝ) →ₗ[ℝ] (Fin n → ℝ) where
  toFun := T.mul a
  map_add' := T.left_distrib a
  map_smul' r x := T.mul_smul r a x

/-- The product as an `ℝ`-bilinear map. -/
def mulBilin : (Fin n → ℝ) →ₗ[ℝ] (Fin n → ℝ) →ₗ[ℝ] (Fin n → ℝ) :=
  LinearMap.mk₂ ℝ T.mul T.right_distrib T.smul_mul T.left_distrib T.mul_smul

theorem mul_sum {ι : Type*} (s : Finset ι) (a : Fin n → ℝ) (f : ι → Fin n → ℝ) :
    T.mul a (∑ i ∈ s, f i) = ∑ i ∈ s, T.mul a (f i) := by
  exact map_sum (T.mulLeft a) f s

theorem sum_mul {ι : Type*} (s : Finset ι) (f : ι → Fin n → ℝ) (a : Fin n → ℝ) :
    T.mul (∑ i ∈ s, f i) a = ∑ i ∈ s, T.mul (f i) a := by
  rw [T.mul_comm, T.mul_sum]
  exact Finset.sum_congr rfl fun i _ => T.mul_comm _ _

/-! ### Mathlib structures on a tubal ring -/

/-- The elements of the tubal ring `T`, as a type carrying Mathlib's `CommRing` and
`Algebra ℝ` structures. -/
@[ext]
structure Elem (T : TubalRing n) where
  /-- The underlying real vector. -/
  vec : Fin n → ℝ

namespace Elem

variable {T}

lemma vec_injective : Function.Injective (Elem.vec : T.Elem → Fin n → ℝ) :=
  fun _ _ h => Elem.ext h

instance : Zero T.Elem := ⟨⟨0⟩⟩
instance : Add T.Elem := ⟨fun a b => ⟨a.vec + b.vec⟩⟩
instance : Neg T.Elem := ⟨fun a => ⟨-a.vec⟩⟩
instance : Sub T.Elem := ⟨fun a b => ⟨a.vec - b.vec⟩⟩
instance : SMul ℕ T.Elem := ⟨fun k a => ⟨k • a.vec⟩⟩
instance : SMul ℤ T.Elem := ⟨fun k a => ⟨k • a.vec⟩⟩
instance : SMul ℝ T.Elem := ⟨fun r a => ⟨r • a.vec⟩⟩
instance : Mul T.Elem := ⟨fun a b => ⟨T.mul a.vec b.vec⟩⟩
instance : One T.Elem := ⟨⟨T.one⟩⟩

@[simp] lemma vec_zero : (0 : T.Elem).vec = 0 := rfl
@[simp] lemma vec_add (a b : T.Elem) : (a + b).vec = a.vec + b.vec := rfl
@[simp] lemma vec_neg (a : T.Elem) : (-a).vec = -a.vec := rfl
@[simp] lemma vec_sub (a b : T.Elem) : (a - b).vec = a.vec - b.vec := rfl
@[simp] lemma vec_nsmul (k : ℕ) (a : T.Elem) : (k • a).vec = k • a.vec := rfl
@[simp] lemma vec_zsmul (k : ℤ) (a : T.Elem) : (k • a).vec = k • a.vec := rfl
@[simp] lemma vec_smul (r : ℝ) (a : T.Elem) : (r • a).vec = r • a.vec := rfl
@[simp] lemma vec_mul (a b : T.Elem) : (a * b).vec = T.mul a.vec b.vec := rfl
@[simp] lemma vec_one : (1 : T.Elem).vec = T.one := rfl
@[simp] lemma vec_mk (v : Fin n → ℝ) : (Elem.mk v : T.Elem).vec = v := rfl

instance : AddCommGroup T.Elem :=
  vec_injective.addCommGroup _ rfl (fun _ _ => rfl) (fun _ => rfl) (fun _ _ => rfl)
    (fun _ _ => rfl) (fun _ _ => rfl)

/-- The additive map `a ↦ a.vec`. -/
def vecAddHom : T.Elem →+ (Fin n → ℝ) where
  toFun := Elem.vec
  map_zero' := rfl
  map_add' _ _ := rfl

instance : Module ℝ T.Elem := vec_injective.module ℝ vecAddHom (fun _ _ => rfl)

instance instCommRing : CommRing T.Elem :=
  { (inferInstance : AddCommGroup T.Elem) with
    mul := (· * ·)
    one := 1
    mul_assoc := fun a b c => Elem.ext (T.mul_assoc a.vec b.vec c.vec)
    one_mul := fun a => Elem.ext (T.one_mul a.vec)
    mul_one := fun a => Elem.ext (T.mul_one a.vec)
    left_distrib := fun a b c => Elem.ext (T.left_distrib a.vec b.vec c.vec)
    right_distrib := fun a b c => Elem.ext (T.right_distrib a.vec b.vec c.vec)
    zero_mul := fun a => Elem.ext (T.zero_mul a.vec)
    mul_zero := fun a => Elem.ext (T.mul_zero a.vec)
    mul_comm := fun a b => Elem.ext (T.mul_comm a.vec b.vec)
    natCast := fun k => k • (1 : T.Elem)
    natCast_zero := zero_nsmul _
    natCast_succ := fun k => succ_nsmul _ k
    intCast := fun k => k • (1 : T.Elem)
    intCast_ofNat := fun k => natCast_zsmul _ k
    intCast_negSucc := fun k => negSucc_zsmul _ k
    npow := fun k a => npowRec k a
    npow_zero := fun _ => rfl
    npow_succ := fun _ _ => rfl }

instance instAlgebra : Algebra ℝ T.Elem :=
  Algebra.ofModule (fun r a b => Elem.ext (T.smul_mul r a.vec b.vec))
    (fun r a b => Elem.ext (T.mul_smul r a.vec b.vec))

/-- `T.Elem ≃ₗ[ℝ] ℝⁿ`. -/
def linearEquivVec : T.Elem ≃ₗ[ℝ] (Fin n → ℝ) where
  toFun := Elem.vec
  invFun := Elem.mk
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  left_inv _ := rfl
  right_inv _ := rfl

theorem isVonNeumannRegularRing : IsVonNeumannRegularRing T.Elem := by
  intro a
  obtain ⟨x, hx⟩ := T.vonNeumann a.vec
  exact ⟨⟨x⟩, Elem.ext hx⟩

end Elem

/-! ### The weak inverse `a⁻` (Section 9) -/

/-- The weak inverse `a⁻`: the unique element with `a = a·a⁻·a` and `a⁻ = a⁻·a·a⁻`. -/
def winv (a : Fin n → ℝ) : Fin n → ℝ :=
  Classical.choose (show ∃ x, a = T.mul (T.mul a x) a ∧ x = T.mul (T.mul x a) x by
    obtain ⟨⟨x⟩, ⟨h1, h2⟩, -⟩ :=
      vonNeumann_unique T.Elem Elem.isVonNeumannRegularRing (⟨a⟩ : T.Elem)
    exact ⟨x, congrArg Elem.vec h1, congrArg Elem.vec h2⟩)

theorem winv_spec (a : Fin n → ℝ) :
    a = T.mul (T.mul a (T.winv a)) a ∧ T.winv a = T.mul (T.mul (T.winv a) a) (T.winv a) := by
  unfold winv
  generalize_proofs h
  exact Classical.choose_spec h

theorem winv_unique (a y : Fin n → ℝ) (h1 : a = T.mul (T.mul a y) a)
    (h2 : y = T.mul (T.mul y a) y) : y = T.winv a := by
  obtain ⟨z, -, hz⟩ := vonNeumann_unique T.Elem Elem.isVonNeumannRegularRing (⟨a⟩ : T.Elem)
  have hy := hz ⟨y⟩ ⟨Elem.ext h1, Elem.ext h2⟩
  have hw := hz ⟨T.winv a⟩ ⟨Elem.ext (T.winv_spec a).1, Elem.ext (T.winv_spec a).2⟩
  exact congrArg Elem.vec (hy.trans hw.symm)


end TubalRing

/-! ### `𝕂_M` is a tubal ring -/

/-- For admissible `M`, `(ℝⁿ, +, ⋆_M)` is a tubal ring. -/
def KM.toTubalRing (M : Matrix (Fin n) (Fin n) ℂ) [Fact (Admissible M)] : TubalRing n where
  mul a b := (KM.mk a * KM.mk b : KM M).vec
  mul_assoc a b c := by
    change ((KM.mk a * KM.mk b) * KM.mk c : KM M).vec = (KM.mk a * (KM.mk b * KM.mk c) : KM M).vec
    rw [mul_assoc]
  left_distrib a b c := by
    change (KM.mk a * (KM.mk b + KM.mk c) : KM M).vec = _
    rw [mul_add]; rfl
  right_distrib a b c := by
    change ((KM.mk a + KM.mk b) * KM.mk c : KM M).vec = _
    rw [add_mul]; rfl
  mul_comm a b := by
    rw [mul_comm]
  exists_one := ⟨(1 : KM M).vec, fun a => ⟨by
    change ((1 : KM M) * KM.mk a).vec = a
    rw [one_mul], by
    change (KM.mk a * (1 : KM M)).vec = a
    rw [mul_one]⟩⟩
  vonNeumann a := by
    obtain ⟨x, hx⟩ := KM.isVonNeumannRegularRing M (KM.mk a)
    exact ⟨x.vec, congrArg KM.vec hx⟩
  smul_mul r a b := by
    change ((r • KM.mk a) * KM.mk b : KM M).vec = (r • (KM.mk a * KM.mk b) : KM M).vec
    rw [KM.smul_mul_assoc']
  mul_smul r a b := by
    change (KM.mk a * (r • KM.mk b) : KM M).vec = (r • (KM.mk a * KM.mk b) : KM M).vec
    rw [KM.mul_smul_comm']

theorem KM.toTubalRing_mul (M : Matrix (Fin n) (Fin n) ℂ) [Fact (Admissible M)]
    (a b : Fin n → ℝ) :
    toC ((KM.toTubalRing M).mul a b) = starMC M (toC a) (toC b) :=
  KM.toC_vec_mul (KM.mk a) (KM.mk b)

/-- Conversely to Theorem 11: if `M` is invertible and `a ⋆_M b` is real for all real `a, b`,
then `(ℝⁿ, +, ⋆_M)` is a tubal ring. -/
theorem exists_tubalRing_of_starM (M : Matrix (Fin n) (Fin n) ℂ) (hM : IsUnit M)
    (hreal : ∀ a b : Fin n → ℝ, starMC M (toC a) (toC b) ∈ Set.range toC) :
    ∃ T : TubalRing n, ∀ a b, toC (T.mul a b) = starMC M (toC a) (toC b) := by
  have : Fact (Admissible M) := ⟨⟨hM, (lemma65 M hM).mp hreal⟩⟩
  exact ⟨KM.toTubalRing M, KM.toTubalRing_mul M⟩

end Tubal
