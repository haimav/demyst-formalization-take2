import TubalAlgebra.KMRing

/-!
# Realness and canonical tubal rings (Definition 12, Proposition 13, Section 10.1, Prop. 66)

Given `n` and `m ≤ n` of the same parity, `M_{n,m}` is the block-diagonal matrix with `m`
leading `1`'s followed by `(n - m)/2` blocks `[[1/√2, -i/√2], [1/√2, i/√2]]`, and
`𝕂_{n,m} := 𝕂_{M_{n,m}}` are the canonical tubal rings.
-/

open Matrix Complex

noncomputable section

namespace Tubal

variable {n : ℕ}

/-- The canonical matrix `M_{n,m}` of Section 10.1: `m` leading `1`'s on the diagonal, followed
by the `2 × 2` blocks `[[1/√2, -i/√2], [1/√2, i/√2]]` on the diagonal. -/
def canonicalM (n m : ℕ) : Matrix (Fin n) (Fin n) ℂ := fun i j =>
  if (i : ℕ) < m ∨ (j : ℕ) < m then (if i = j then 1 else 0)
  else if ((i : ℕ) - m) / 2 = ((j : ℕ) - m) / 2 then
    (if ((j : ℕ) - m) % 2 = 0 then ((1 / Real.sqrt 2 : ℝ) : ℂ)
     else if ((i : ℕ) - m) % 2 = 0 then -I / (Real.sqrt 2 : ℂ) else I / (Real.sqrt 2 : ℂ))
  else 0

/-- The inverse of `M_{n,m}` as displayed in the proof of Proposition 66: `m` leading `1`'s
followed by the blocks `[[1/√2, 1/√2], [i/√2, -i/√2]]`. -/
def canonicalMInv (n m : ℕ) : Matrix (Fin n) (Fin n) ℂ := fun i j =>
  if (i : ℕ) < m ∨ (j : ℕ) < m then (if i = j then 1 else 0)
  else if ((i : ℕ) - m) / 2 = ((j : ℕ) - m) / 2 then
    (if ((i : ℕ) - m) % 2 = 0 then ((1 / Real.sqrt 2 : ℝ) : ℂ)
     else if ((j : ℕ) - m) % 2 = 0 then I / (Real.sqrt 2 : ℂ) else -I / (Real.sqrt 2 : ℂ))
  else 0

/-- `M_{n,m}⁻¹` is the displayed matrix (for `m ≤ n` of the same parity as `n`). -/
theorem canonicalM_inv (n m : ℕ) (hmn : m ≤ n) (hpar : m % 2 = n % 2) :
    (canonicalM n m)⁻¹ = canonicalMInv n m := by
  sorry

/-- For `m ≤ n` of the same parity, `M_{n,m}` is admissible, so `𝕂_{n,m}` is a tubal ring. -/
theorem canonicalM_admissible (n m : ℕ) (hmn : m ≤ n) (hpar : m % 2 = n % 2) :
    Admissible (canonicalM n m) := by
  sorry

/-- The realness of `M_{n,m}` is `m`. -/
theorem realness_canonicalM (n m : ℕ) (hmn : m ≤ n) (hpar : m % 2 = n % 2) :
    realness (canonicalM n m) = m := by
  sorry

/-- The realness `r` of an admissible `M` satisfies `r ≤ n` and `r ≡ n (mod 2)`. -/
theorem realness_le_and_parity (M : Matrix (Fin n) (Fin n) ℂ) (hM : Admissible M) :
    realness M ≤ n ∧ realness M % 2 = n % 2 := by
  sorry

/-- **Proposition 66.** Consider the tubal ring defined by `M ∈ ℂ^{n×n}`. Let `m` be the
realness of `M`. Then `𝕂_M` is isomorphic as a ring to `𝕂_{n,m}`. -/
theorem prop66 (M : Matrix (Fin n) (Fin n) ℂ) (hM : Admissible M) :
    Nonempty (KM M ≃+* KM (canonicalM n (realness M))) := by
  sorry

/-- The isomorphism of Proposition 66 also respects the `⋆_M`-conjugation (as shown in its
proof). -/
theorem prop66_star (M : Matrix (Fin n) (Fin n) ℂ) (hM : Admissible M) :
    ∃ e : KM M ≃+* KM (canonicalM n (realness M)), ∀ x, e (star x) = star (e x) := by
  sorry

/-- **Proposition 13.** Let `M` and `M'` be of equal size. The rings `𝕂_M` and `𝕂_{M'}` are
isomorphic as rings if their realness is the same. -/
theorem prop13 (M M' : Matrix (Fin n) (Fin n) ℂ) (hM : Admissible M) (hM' : Admissible M')
    (h : realness M = realness M') : Nonempty (KM M ≃+* KM M') := by
  sorry

/-- "For real-like tubal rings we have `a* = a` for all `a`." -/
theorem star_eq_self_of_realLike (M : Matrix (Fin n) (Fin n) ℂ) [Fact (Admissible M)]
    (h : IsRealLike M) (a : KM M) : star a = a := by
  sorry

end Tubal
