import TubalAlgebra.Canonical
import TubalAlgebra.Section9.Main

/-!
# The number of tubal rings up to isomorphism (Section 3.5, after Proposition 13)

"Since complex rows in `M` come in conjugate pairs, the realness `r` must satisfy
`r ≡ n (mod 2)` … Thus there are, up to isomorphism, `⌊n/2⌋ + 1` tubal rings."

The paper only shows that there are at most that many (Proposition 13); we also show that
canonical tubal rings of different realness are not isomorphic (they have different numbers of
idempotents), so the count is exact.
-/

open Matrix Complex

noncomputable section

namespace Tubal

/-- Section 3.5: there are, up to isomorphism, exactly `⌊n/2⌋ + 1` tubal rings on `ℝⁿ`:
the admissible realness values `m ≤ n`, `m ≡ n (mod 2)`, are `⌊n/2⌋ + 1` many; every tubal
ring is ring-isomorphic to the canonical ring `𝕂_{n,m}` for such an `m`; and canonical rings
with different `m` are not isomorphic. -/
theorem tubalRing_count (n : ℕ) :
    ((Finset.range (n + 1)).filter (fun m => m % 2 = n % 2)).card = n / 2 + 1 ∧
    (∀ T : TubalRing n, ∃ m, m ≤ n ∧ m % 2 = n % 2 ∧
      Nonempty (T.Elem ≃+* KM (canonicalM n m))) ∧
    (∀ m m', m ≤ n → m % 2 = n % 2 → m' ≤ n → m' % 2 = n % 2 →
      Nonempty (KM (canonicalM n m) ≃+* KM (canonicalM n m')) → m = m') := by
  sorry

end Tubal
