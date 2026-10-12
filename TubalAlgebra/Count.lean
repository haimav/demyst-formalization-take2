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

/-! ### Auxiliary lemmas -/

private lemma count_rowConjOf {n m : ℕ} {i p : Fin n} (hi : m ≤ (i : ℕ)) (hp : m ≤ (p : ℕ))
    (hip : ((i : ℕ) - m) / 2 = ((p : ℕ) - m) / 2) (hne : (i : ℕ) ≠ p) :
    RowConjOf (canonicalM n m) i p := by
  intro k
  rw [Canonical.canonicalM_apply, Canonical.canonicalM_apply]
  have e0 : ¬ (i : ℕ) < m := by omega
  have e1 : ¬ (p : ℕ) < m := by omega
  simp only [e0, e1, false_or, hip]
  split_ifs <;> first | omega | simp

/-- The canonical ring `𝕂_{n,m}` has exactly `2^{(n+m)/2}` idempotents. -/
private lemma count_idempotents (n m : ℕ) (hmn : m ≤ n) (hpar : m % 2 = n % 2) :
    Nat.card {e : KM (canonicalM n m) // e * e = e} = 2 ^ ((n + m) / 2) := by
  have hA := canonicalM_admissible n m hmn hpar
  have : Fact (Admissible (canonicalM n m)) := ⟨hA⟩
  set K := (n + m) / 2 with hK
  let q : Fin n → Fin K := fun j =>
    ⟨if (j : ℕ) < m then j else m + ((j : ℕ) - m) / 2, by split_ifs <;> omega⟩
  let g : Fin K → Fin n := fun t =>
    ⟨if (t : ℕ) < m then t else m + 2 * ((t : ℕ) - m), by split_ifs <;> omega⟩
  have hqg : ∀ t, q (g t) = t := by
    intro t
    ext
    simp only [q, g]
    split_ifs <;> omega
  -- rows conjugate to each other lie in the same orbit
  have hqA : ∀ j k, RowConjOf (canonicalM n m) j k → q j = q k := by
    intro j k hjk
    by_cases hj : (j : ℕ) < m
    · have := eq_of_rowReal_of_rowConjOf hA.1 (Canonical.canonicalM_rowReal_of_lt hj) hjk
      rw [this]
    · let p : Fin n := ⟨if ((j : ℕ) - m) % 2 = 0 then (j : ℕ) + 1 else (j : ℕ) - 1, by
        split_ifs <;> omega⟩
      have hp : RowConjOf (canonicalM n m) j p :=
        count_rowConjOf (by omega) (by simp only [p]; split_ifs <;> omega)
          (by simp only [p]; split_ifs <;> omega) (by simp only [p]; split_ifs <;> omega)
      rw [rowConjOf_unique' hA.1 hjk hp]
      ext
      simp only [q, p]
      split_ifs <;> omega
  -- every row is (conjugate to) the representative of its orbit
  have hqB : ∀ j, j = g (q j) ∨ RowConjOf (canonicalM n m) j (g (q j)) := by
    intro j
    by_cases hj : j = g (q j)
    · exact Or.inl hj
    · right
      have hj' : (j : ℕ) ≠ (g (q j) : ℕ) := fun h => hj (Fin.ext h)
      simp only [q, g] at hj' ⊢
      apply count_rowConjOf <;> (try simp only) <;> split_ifs at hj' ⊢ <;> omega
  let y : (Fin K → Bool) → Fin n → ℂ := fun h j => if h (q j) then 1 else 0
  have hy : ∀ h, ConjPattern (canonicalM n m) (y h) := by
    intro h
    refine ⟨fun j _ => ?_, fun j k hjk => ?_⟩
    · simp only [y]; split_ifs <;> simp
    · simp only [y, hqA j k hjk]; split_ifs <;> simp
  choose ψ hψ using fun h => KM.exists_hat_eq (hy h)
  have hidem : ∀ h, ψ h * ψ h = ψ h := by
    intro h
    apply KM.hat_injective
    rw [KM.hat_mul, hψ]
    funext j
    simp only [y, Pi.mul_apply]
    split_ifs <;> simp
  let F : (Fin K → Bool) → {e : KM (canonicalM n m) // e * e = e} := fun h => ⟨ψ h, hidem h⟩
  have hF : Function.Bijective F := by
    refine ⟨fun h h' hhh => ?_, fun ⟨e, he⟩ => ?_⟩
    · have h1 : y h = y h' := by
        rw [← hψ, ← hψ]
        exact congrArg (fun x => KM.hat x.1) hhh
      funext t
      have h2 := congrFun h1 (g t)
      simp only [y, hqg] at h2
      cases hb : h t <;> cases hb' : h' t <;> rw [hb, hb'] at h2 <;> first | rfl | simp at h2
    · have h01 : ∀ j, e.hat j = 0 ∨ e.hat j = 1 := by
        intro j
        have := congrFun (congrArg KM.hat he) j
        rw [KM.hat_mul, Pi.mul_apply] at this
        exact IsIdempotentElem.iff_eq_zero_or_one.mp this
      have hkey : ∀ j, e.hat j = e.hat (g (q j)) := by
        intro j
        rcases hqB j with h | h
        · exact congrArg e.hat h
        · rw [e.hat_conjPattern.2 _ _ h]
          rcases h01 (g (q j)) with h' | h' <;> simp [h']
      refine ⟨fun t => decide (e.hat (g t) = 1), Subtype.ext ?_⟩
      apply KM.hat_injective
      rw [hψ]
      funext j
      simp only [y]
      rw [hkey j]
      rcases h01 (g (q j)) with h' | h' <;> simp [h']
  rw [← Nat.card_congr (Equiv.ofBijective F hF), Nat.card_fun]
  simp

private lemma count_card_filter (n : ℕ) :
    ((Finset.range (n + 1)).filter (fun m => m % 2 = n % 2)).card = n / 2 + 1 := by
  have h : (Finset.range (n + 1)).filter (fun m => m % 2 = n % 2) =
      (Finset.range (n / 2 + 1)).image (fun k => n - 2 * k) := by
    ext m
    simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_image]
    constructor
    · rintro ⟨h1, h2⟩
      exact ⟨(n - m) / 2, by omega, by omega⟩
    · rintro ⟨k, hk, rfl⟩
      omega
  rw [h, Finset.card_image_of_injOn, Finset.card_range]
  intro a ha b hb hab
  simp only [Finset.coe_range, Set.mem_Iio] at ha hb
  simp only at hab
  omega

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
  refine ⟨count_card_filter n, fun T => ?_, fun m m' hm hmp hm' hmp' ⟨e⟩ => ?_⟩
  · obtain ⟨M, hM, hT⟩ := theorem11_admissible T
    have : Fact (Admissible M) := ⟨hM⟩
    have h := realness_le_and_parity M hM
    refine ⟨realness M, h.1, h.2, ⟨?_⟩⟩
    let φ : T.Elem ≃+* KM M :=
      { toFun := fun a => ⟨a.vec⟩
        invFun := fun b => ⟨b.vec⟩
        left_inv := fun _ => rfl
        right_inv := fun _ => rfl
        map_mul' := fun a b => KM.ext (toC_injective (by
          rw [KM.toC_vec_mul]
          exact hT a.vec b.vec))
        map_add' := fun _ _ => rfl }
    exact φ.trans (prop66 M hM).some
  · have hc : Nat.card {x : KM (canonicalM n m) // x * x = x} =
        Nat.card {y : KM (canonicalM n m') // y * y = y} :=
      Nat.card_congr (e.toEquiv.subtypeEquiv fun x => by
        change x * x = x ↔ e x * e x = e x
        rw [← map_mul, e.injective.eq_iff])
    rw [count_idempotents n m hm hmp, count_idempotents n m' hm' hmp'] at hc
    have := Nat.pow_right_injective (le_refl 2) hc
    omega

end Tubal
