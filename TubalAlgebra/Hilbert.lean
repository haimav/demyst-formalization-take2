import TubalAlgebra.Tensor

/-!
# Hilbert algebra structure (Section 7.2 / Appendix C: Propositions 70, 71)

The Frobenius inner product of tubes is `⟨a, b⟩_F := aᵀ b`; for oriented matrices (and more
generally tensors) it is the sum of the entry-wise products.
-/

open Matrix Complex

noncomputable section

namespace Tubal

variable {n : ℕ} {M : Matrix (Fin n) (Fin n) ℂ}

/-- The Frobenius inner product of tubes `⟨a, b⟩_F := aᵀ b`. -/
def frobInner (a b : KM M) : ℝ := ∑ i, a.vec i * b.vec i

/-- The Frobenius inner product of oriented matrices `𝐀, 𝐁 ∈ ℝ^{p×1×n} ≅ 𝕂_M^p`:
`⟨𝐀, 𝐁⟩_F = ∑ᵢ ⟨𝐀_{i1:}, 𝐁_{i1:}⟩_F`. -/
def frobInnerVec {p : ℕ} (X Y : Fin p → KM M) : ℝ := ∑ i, frobInner (X i) (Y i)

/-! ### Auxiliary lemmas -/

lemma unitary_dot (W : Matrix (Fin n) (Fin n) ℂ) (hW : W ∈ unitaryGroup (Fin n) ℂ)
    (x y : Fin n → ℂ) : star (W *ᵥ x) ⬝ᵥ (W *ᵥ y) = star x ⬝ᵥ y := by
  rw [Matrix.star_mulVec, dotProduct_mulVec, vecMul_vecMul]
  have : star W * W = 1 := (Matrix.mem_unitaryGroup_iff').mp hW
  rw [show Wᴴ = star W from rfl, this, vecMul_one]

lemma frobInner_eq (a b : KM M) :
    ((frobInner a b : ℝ) : ℂ) = star (toC a.vec) ⬝ᵥ toC b.vec := by
  simp [frobInner, dotProduct, toC]

/-- Under `M = D W`: `⟨u, v⟩ = ∑ⱼ conj(ûⱼ) v̂ⱼ / dⱼ²`. -/
lemma frobInner_hat (d : Fin n → ℝ) (hd : ∀ i, d i ≠ 0)
    (W : Matrix (Fin n) (Fin n) ℂ) (hW : W ∈ unitaryGroup (Fin n) ℂ)
    (hMW : M = diagonal (fun i => (d i : ℂ)) * W) (a b : KM M) :
    ((frobInner a b : ℝ) : ℂ) = ∑ j, starRingEnd ℂ (a.hat j) * b.hat j / ((d j : ℂ) ^ 2) := by
  rw [frobInner_eq, ← unitary_dot W hW]
  simp only [dotProduct, Pi.star_apply, KM.hat, hMW, ← mulVec_mulVec, mulVec_diagonal]
  refine Finset.sum_congr rfl fun j _ => ?_
  have hdj : (d j : ℂ) ≠ 0 := by exact_mod_cast hd j
  rw [map_mul, Complex.conj_ofReal]
  field_simp
  rw [mul_comm]
  rfl


lemma frobInner_add_left (a b c : KM M) : frobInner (a + b) c = frobInner a c + frobInner b c := by
  simp [frobInner, add_mul, Finset.sum_add_distrib]

lemma frobInner_add_right (a b c : KM M) : frobInner a (b + c) = frobInner a b + frobInner a c := by
  simp [frobInner, mul_add, Finset.sum_add_distrib]

lemma frobInner_sum_left {ι : Type*} (s : Finset ι) (f : ι → KM M) (c : KM M) :
    frobInner (∑ i ∈ s, f i) c = ∑ i ∈ s, frobInner (f i) c := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [frobInner]
  | insert a s ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, frobInner_add_left, ih]

lemma frobInner_sum_right {ι : Type*} (s : Finset ι) (f : ι → KM M) (c : KM M) :
    frobInner c (∑ i ∈ s, f i) = ∑ i ∈ s, frobInner c (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [frobInner]
  | insert a s ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, frobInner_add_right, ih]

/-- **Proposition 70.** Suppose that `M = D W` for some invertible real diagonal matrix `D` and
unitary `W`. Then for every `a, x, y` we have `⟨a ⋆_M x, y⟩_F = ⟨x, a* ⋆_M y⟩_F` (Eq. (9)). -/
theorem prop70 [Fact (Admissible M)] (d : Fin n → ℝ) (hd : ∀ i, d i ≠ 0)
    (W : Matrix (Fin n) (Fin n) ℂ) (hW : W ∈ unitaryGroup (Fin n) ℂ)
    (hMW : M = diagonal (fun i => (d i : ℂ)) * W) (a x y : KM M) :
    frobInner (a * x) y = frobInner x (star a * y) := by
  apply Complex.ofReal_injective
  rw [frobInner_hat d hd W hW hMW, frobInner_hat d hd W hW hMW]
  refine Finset.sum_congr rfl fun j _ => ?_
  simp only [KM.hat_mul, KM.hat_star, Pi.mul_apply, Pi.star_apply, map_mul]
  rw [show star (a.hat j) = starRingEnd ℂ (a.hat j) from rfl]
  ring

/-- **Proposition 71.** Suppose that `𝒜 ∈ 𝕂_M^{m×p}`. For every `X ∈ 𝕂_M^p` and `Y ∈ 𝕂_M^m`
we have `⟨𝒜 ⋆_M X, Y⟩_F = ⟨X, 𝒜ᴴ ⋆_M Y⟩_F`.

(This is stated in Appendix C as an extension of Eq. (9) and is proved from it, so it carries
the hypothesis of Proposition 70: `M = D W` with `D` invertible real diagonal and `W` unitary.
Without it, the statement fails: see `eq9_fails_in_general`.) -/
theorem prop71 [Fact (Admissible M)] (d : Fin n → ℝ) (hd : ∀ i, d i ≠ 0)
    (W : Matrix (Fin n) (Fin n) ℂ) (hW : W ∈ unitaryGroup (Fin n) ℂ)
    (hMW : M = diagonal (fun i => (d i : ℂ)) * W) {m p : ℕ}
    (A : Matrix (Fin m) (Fin p) (KM M)) (X : Fin p → KM M) (Y : Fin m → KM M) :
    frobInnerVec (A *ᵥ X) Y = frobInnerVec X (Aᴴ *ᵥ Y) := by
  simp only [frobInnerVec, mulVec, dotProduct, frobInner_sum_left, frobInner_sum_right]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun i _ => ?_
  rw [prop70 d hd W hW hMW, conjTranspose_apply]

/-- The matrix `[[1, 0], [1, 1]]` (real, invertible, hence admissible), used to show that
Eq. (9) does not hold for general `M` ("it is easy to build counter examples"). -/
def counterM : Matrix (Fin 2) (Fin 2) ℂ := !![1, 0; 1, 1]

theorem counterM_admissible : Admissible counterM := by
  refine ⟨?_, fun i => Or.inl fun k => ?_⟩
  · rw [Matrix.isUnit_iff_isUnit_det]
    simp [counterM, Matrix.det_fin_two]
  · fin_cases i <;> fin_cases k <;> simp [counterM]

/-- "We would expect that this adjoint will be given by the conjugate to `a` … however it is
easy to build counter examples for which this does not hold": Eq. (9) fails for
`M = [[1, 0], [1, 1]]`. -/
theorem eq9_fails_in_general :
    haveI : Fact (Admissible counterM) := ⟨counterM_admissible⟩
    ∃ a x y : KM counterM, frobInner (a * x) y ≠ frobInner x (star a * y) := by
  have hinv : counterM⁻¹ = !![1, 0; -1, 1] := by
    apply Matrix.inv_eq_left_inv
    ext i j
    fin_cases i <;> fin_cases j <;> simp [counterM, Matrix.mul_apply, Fin.sum_univ_two]
  have hinv' : (!![1, 0; 1, 1] : Matrix (Fin 2) (Fin 2) ℂ)⁻¹ = !![1, 0; -1, 1] := hinv
  have : Fact (Admissible counterM) := ⟨counterM_admissible⟩
  set a : KM counterM := ⟨![0, 1]⟩
  set x : KM counterM := ⟨![1, 0]⟩
  have hsa : star a = a := by
    apply KM.ext
    apply toC_injective
    rw [KM.toC_vec_star]
    funext i
    fin_cases i <;> simp [a, hinv', counterM, mulVec, dotProduct, Fin.sum_univ_two, toC]
  have h1 : ∀ i, toC (a * x).vec i = toC ![0, 1] i := by
    intro i
    rw [KM.toC_vec_mul]
    fin_cases i <;> simp [a, x, starMC, hinv', counterM, mulVec, dotProduct, Fin.sum_univ_two, toC]
  have h2 : ∀ i, toC (a * a).vec i = toC ![0, 1] i := by
    intro i
    rw [KM.toC_vec_mul]
    fin_cases i <;> simp [a, starMC, hinv', counterM, mulVec, dotProduct, Fin.sum_univ_two, toC]
  have e1 : (a * x).vec = ![0, 1] := toC_injective (funext h1)
  have e2 : (a * a).vec = ![0, 1] := toC_injective (funext h2)
  refine ⟨a, x, a, ?_⟩
  rw [hsa]
  simp only [frobInner, e1, e2, Fin.sum_univ_two]
  simp [a, x]

end Tubal
