import Mathlib

/-!
# Demystifying Tubal Tensor Algebra — core definitions

This file contains the basic objects of the paper "Demystifying Tubal Tensor Algebra"
(H. Avron, U. Mor):

* `toC` — the embedding `ℝⁿ ↪ ℂⁿ`;
* `starMC M a b = M⁻¹ (M a • M b)` — Eq. (5), the `⋆_M` product on complex vectors
  (`•`, the Hadamard product, is the pointwise product `*` of functions `Fin n → ℂ`);
* `RowReal`, `RowConjOf`, `ConjRowCondition` — the condition "every row of `M` is either real,
  or obtained by entry-wise complex conjugation of exactly one other row of `M`";
* `Admissible M` — `M` is invertible and satisfies the above condition (the standing
  hypothesis on `M` under which `𝕂_M` is defined, Theorem 3);
* `KM M` — the set `ℝⁿ` of tubes, on which `⋆_M` will define the ring `𝕂_M`.
  The operations `+`, `0`, `-`, scalar multiplication are the usual vector space operations.
  The product is `a * b := ⋆_M` (more precisely the real part of `M⁻¹(Ma • Mb)`, which is
  real under admissibility, see `TubalAlgebra.KMRing`), the unit is `e_M = M⁻¹ e`
  and the conjugate is Eq. (6) `a* = M⁻¹ conj(M a)`;
* `pinvVec` (the entrywise pseudo-inverse `x⁺`) and `KM.weakInv` — Eq. (7);
* `realness` — Definition 12.
-/

open Matrix Complex

noncomputable section

namespace Tubal

variable {n : ℕ}

/-- The canonical embedding `ℝⁿ ↪ ℂⁿ`. -/
def toC (a : Fin n → ℝ) : Fin n → ℂ := fun i => (a i : ℂ)

@[simp] lemma toC_apply (a : Fin n → ℝ) (i : Fin n) : toC a i = (a i : ℂ) := rfl

lemma toC_injective : Function.Injective (toC : (Fin n → ℝ) → Fin n → ℂ) := by
  intro a b h
  funext i
  have := congrFun h i
  simpa using this

/-- **Eq. (5)**: `a ⋆_M b := M⁻¹ (M a • M b)`, where `•` is the Hadamard (entry-wise) product,
which for functions `Fin n → ℂ` is the pointwise product `*`. -/
def starMC (M : Matrix (Fin n) (Fin n) ℂ) (a b : Fin n → ℂ) : Fin n → ℂ :=
  M⁻¹ *ᵥ ((M *ᵥ a) * (M *ᵥ b))

/-- Row `i` of `M` is real. -/
def RowReal (M : Matrix (Fin n) (Fin n) ℂ) (i : Fin n) : Prop :=
  ∀ k, starRingEnd ℂ (M i k) = M i k

/-- Row `i` of `M` is obtained by entry-wise complex conjugation of row `j` of `M`. -/
def RowConjOf (M : Matrix (Fin n) (Fin n) ℂ) (i j : Fin n) : Prop :=
  ∀ k, M i k = starRingEnd ℂ (M j k)

/-- "Every row of `M` is either real, or obtained by entry-wise complex conjugation of exactly
one other row of `M`." -/
def ConjRowCondition (M : Matrix (Fin n) (Fin n) ℂ) : Prop :=
  ∀ i, RowReal M i ∨ ∃! j, j ≠ i ∧ RowConjOf M i j

/-- The standing hypothesis on `M`: `M` is an invertible matrix in which every row is either
real, or is conjugate to exactly one other row of `M` (hypothesis of Theorem 3). -/
def Admissible (M : Matrix (Fin n) (Fin n) ℂ) : Prop :=
  IsUnit M ∧ ConjRowCondition M

/-- **Definition 12** (Realness): the number of real rows in `M`. -/
def realness (M : Matrix (Fin n) (Fin n) ℂ) : ℕ := Nat.card {i : Fin n // RowReal M i}

/-- **Definition 12**: `M` (or `𝕂_M`) is *fully real* / *real-like* if its realness is `n`. -/
def IsRealLike (M : Matrix (Fin n) (Fin n) ℂ) : Prop := realness M = n

/-- The entry-wise pseudo-inverse `x⁺` of a vector: invert non-zero entries, keep zeros. -/
def pinvVec (y : Fin n → ℂ) : Fin n → ℂ := fun i => if y i = 0 then 0 else (y i)⁻¹

/-- **Definition 9**: a ring `R` is *von Neumann regular* if for every `a ∈ R` there exists
`x ∈ R` such that `a = a · x · a`. -/
def IsVonNeumannRegularRing (R : Type*) [Mul R] : Prop := ∀ a : R, ∃ x : R, a = a * x * a

/-- The tubes `ℝⁿ`, to be endowed with the ring structure `𝕂_M`. -/
@[ext]
structure KM (M : Matrix (Fin n) (Fin n) ℂ) where
  /-- The underlying real vector of a tube. -/
  vec : Fin n → ℝ

namespace KM

variable {M : Matrix (Fin n) (Fin n) ℂ}

lemma vec_injective : Function.Injective (KM.vec : KM M → Fin n → ℝ) := fun _ _ h => KM.ext h

/-- `KM M` is (as a set) `ℝⁿ`. -/
def equivVec : KM M ≃ (Fin n → ℝ) where
  toFun := KM.vec
  invFun := KM.mk
  left_inv _ := rfl
  right_inv _ := rfl

/-! ### Vector space structure: the usual one on `ℝⁿ` -/

instance : Zero (KM M) := ⟨⟨0⟩⟩
instance : Add (KM M) := ⟨fun a b => ⟨a.vec + b.vec⟩⟩
instance : Neg (KM M) := ⟨fun a => ⟨-a.vec⟩⟩
instance : Sub (KM M) := ⟨fun a b => ⟨a.vec - b.vec⟩⟩
instance : SMul ℕ (KM M) := ⟨fun k a => ⟨k • a.vec⟩⟩
instance : SMul ℤ (KM M) := ⟨fun k a => ⟨k • a.vec⟩⟩
instance : SMul ℝ (KM M) := ⟨fun r a => ⟨r • a.vec⟩⟩

@[simp] lemma vec_zero : (0 : KM M).vec = 0 := rfl
@[simp] lemma vec_add (a b : KM M) : (a + b).vec = a.vec + b.vec := rfl
@[simp] lemma vec_neg (a : KM M) : (-a).vec = -a.vec := rfl
@[simp] lemma vec_sub (a b : KM M) : (a - b).vec = a.vec - b.vec := rfl
@[simp] lemma vec_nsmul (k : ℕ) (a : KM M) : (k • a).vec = k • a.vec := rfl
@[simp] lemma vec_zsmul (k : ℤ) (a : KM M) : (k • a).vec = k • a.vec := rfl
@[simp] lemma vec_smul (r : ℝ) (a : KM M) : (r • a).vec = r • a.vec := rfl
@[simp] lemma vec_mk (v : Fin n → ℝ) : (KM.mk v : KM M).vec = v := rfl

instance : AddCommGroup (KM M) :=
  vec_injective.addCommGroup _ rfl (fun _ _ => rfl) (fun _ => rfl) (fun _ _ => rfl)
    (fun _ _ => rfl) (fun _ _ => rfl)

/-- The additive map `a ↦ a.vec`. -/
def vecAddHom : KM M →+ (Fin n → ℝ) where
  toFun := KM.vec
  map_zero' := rfl
  map_add' _ _ := rfl

instance : Module ℝ (KM M) := vec_injective.module ℝ vecAddHom (fun _ _ => rfl)

/-- `KM M ≃ₗ[ℝ] ℝⁿ`. -/
def linearEquivVec : KM M ≃ₗ[ℝ] (Fin n → ℝ) where
  toFun := KM.vec
  invFun := KM.mk
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  left_inv _ := rfl
  right_inv _ := rfl

/-! ### The tubal operations -/

/-- The transform `â := M a ∈ ℂⁿ` of a tube `a`. -/
def hat (a : KM M) : Fin n → ℂ := M *ᵥ toC a.vec

/-- The `⋆_M` product (Eq. (5)). It is defined as the real part of `M⁻¹ (M a • M b)`; under
`Admissible M` this complex vector is real (Lemma 2), see `KMRing.toC_vec_mul`. -/
instance : Mul (KM M) := ⟨fun a b => ⟨fun i => (starMC M (toC a.vec) (toC b.vec) i).re⟩⟩

/-- The unit `e_M := M⁻¹ e`, `e` the all-ones vector (proof of Theorem 3). -/
instance : One (KM M) := ⟨⟨fun i => ((M⁻¹ *ᵥ (1 : Fin n → ℂ)) i).re⟩⟩

/-- Eq. (6): the `⋆_M`-conjugate `a* := M⁻¹ conj(M a)`. -/
instance : Star (KM M) := ⟨fun a => ⟨fun i => ((M⁻¹ *ᵥ star (M *ᵥ toC a.vec)) i).re⟩⟩

instance : NatCast (KM M) := ⟨fun k => k • (1 : KM M)⟩
instance : IntCast (KM M) := ⟨fun k => k • (1 : KM M)⟩
instance : Pow (KM M) ℕ := ⟨fun a k => npowRec k a⟩

lemma vec_mul (a b : KM M) :
    (a * b).vec = fun i => (starMC M (toC a.vec) (toC b.vec) i).re := rfl

lemma vec_one : (1 : KM M).vec = fun i => ((M⁻¹ *ᵥ (1 : Fin n → ℂ)) i).re := rfl

lemma vec_star (a : KM M) :
    (star a).vec = fun i => ((M⁻¹ *ᵥ star (M *ᵥ toC a.vec)) i).re := rfl

/-- Eq. (7): the weak inverse `a⁻ := M⁻¹ (M a)⁺` (real part; it is real by Lemma 7). -/
def weakInv (a : KM M) : KM M := ⟨fun i => ((M⁻¹ *ᵥ pinvVec (M *ᵥ toC a.vec)) i).re⟩

/-- The partial order on `𝕂_M`: `a ≤_M b` iff `M (b - a)` is real and element-wise
non-negative. -/
instance : LE (KM M) :=
  ⟨fun a b => ∀ j, ((b - a).hat j).im = 0 ∧ 0 ≤ ((b - a).hat j).re⟩

lemma le_def (a b : KM M) :
    a ≤ b ↔ ∀ j, ((b - a).hat j).im = 0 ∧ 0 ≤ ((b - a).hat j).re := Iff.rfl

end KM

end Tubal
