import TubalAlgebra.KMRing

/-!
# Module of oriented matrices (Section 4: Theorem 19, Eq. (8), Theorem 20)

`𝕂_M^m := 𝕂_M ⊕ ⋯ ⊕ 𝕂_M` (`m` copies) is modelled by `Fin m → KM M`: addition is element
addition and multiplication by a tube is element-wise multiplication. It is isomorphic to
`ℝ^{m×n}` via "squeeze"/"twist".
-/

open Matrix Complex

noncomputable section

namespace Tubal

variable {n : ℕ} {M : Matrix (Fin n) (Fin n) ℂ}

/-- "squeeze": `𝕂_M^m → ℝ^{m×n}`, the tube entries are laid flat back into matrix rows. -/
def squeeze {m : ℕ} (U : Fin m → KM M) : Matrix (Fin m) (Fin n) ℝ := fun i j => (U i).vec j

/-- "twist": `ℝ^{m×n} → 𝕂_M^m`, each row is lifted into the third dimension to become a tube. -/
def twist {m : ℕ} (X : Matrix (Fin m) (Fin n) ℝ) : Fin m → KM M := fun i => ⟨X i⟩

theorem twist_squeeze {m : ℕ} (U : Fin m → KM M) : twist (squeeze U) = U := rfl

theorem squeeze_twist {m : ℕ} (X : Matrix (Fin m) (Fin n) ℝ) :
    squeeze (twist X : Fin m → KM M) = X := rfl

/-- `𝕂_M^m ≅ ℝ^{m×n}` (as real vector spaces). -/
def orientedEquiv (m : ℕ) : (Fin m → KM M) ≃ₗ[ℝ] Matrix (Fin m) (Fin n) ℝ where
  toFun := squeeze
  invFun := twist
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  left_inv _ := rfl
  right_inv _ := rfl

/-- The natural basis `E_1, …, E_m` of `𝕂_M^m`: `E_i` is all zeros except for the `i`-th tube,
which is the unit element of `𝕂_M`. -/
def stdOriented [Fact (Admissible M)] (m : ℕ) (i : Fin m) : Fin m → KM M := Pi.single i 1

/-- **Theorem 19** (Theorem 4.1 in [14]). `𝕂_M^m` is a free module over `𝕂_M` of rank `m`:
it has the basis `E_1, …, E_m`, and (since `𝕂_M` has invariant basis number, which needs
`𝕂_M ≠ 0`, i.e. `n ≠ 0`) every basis has `m` elements. -/
theorem theorem19 (M : Matrix (Fin n) (Fin n) ℂ) [Fact (Admissible M)] (m : ℕ) :
    Module.Free (KM M) (Fin m → KM M) ∧
    (∃ b : Module.Basis (Fin m) (KM M) (Fin m → KM M), ∀ i, b i = stdOriented m i) ∧
    (n ≠ 0 → ∀ (ι : Type) (b : Module.Basis ι (KM M) (Fin m → KM M)), Cardinal.mk ι = m) ∧
    (n ≠ 0 → Module.finrank (KM M) (Fin m → KM M) = m) := by
  sorry

/-- **Eq. (8)**: the `⋆_M`-dot product `U ·_M V := ∑ᵢ uᵢ* ⋆_M vᵢ ∈ 𝕂_M`. -/
def dotM {m : ℕ} (U V : Fin m → KM M) : KM M := ∑ i, star (U i) * V i

/-- **Theorem 20.** For all `U, V, W ∈ 𝕂_M^m` and `r, s ∈ 𝕂_M`, the `·_M` product satisfies:
* `⋆_M`-conjugate symmetry: `U ·_M V = (V ·_M U)*`;
* `⋆_M`-linearity in the second argument:
  `U ·_M (r ⋆_M V + s ⋆_M W) = r ⋆_M (U ·_M V) + s ⋆_M (U ·_M W)`;
* `⋆_M`-positive definiteness: `U ·_M U ≥_M 0` and `U ·_M U = 0` if and only if `U = 0`. -/
theorem theorem20 (M : Matrix (Fin n) (Fin n) ℂ) [Fact (Admissible M)] {m : ℕ}
    (U V W : Fin m → KM M) (r s : KM M) :
    dotM U V = star (dotM V U) ∧
    dotM U (r • V + s • W) = r * dotM U V + s * dotM U W ∧
    (0 ≤ dotM U U ∧ (dotM U U = 0 ↔ U = 0)) := by
  sorry

/-- The key step in the proof of Theorem 20: for all `u ∈ 𝕂_M`, `u* ⋆_M u ≥_M 0`, and
`u* ⋆_M u = 0` iff `u = 0`. -/
theorem star_mul_self_nonneg (M : Matrix (Fin n) (Fin n) ℂ) [Fact (Admissible M)]
    (u : KM M) : 0 ≤ star u * u ∧ (star u * u = 0 ↔ u = 0) := by
  sorry

end Tubal
