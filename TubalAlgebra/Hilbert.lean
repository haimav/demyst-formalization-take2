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

/-- **Proposition 70.** Suppose that `M = D W` for some invertible real diagonal matrix `D` and
unitary `W`. Then for every `a, x, y` we have `⟨a ⋆_M x, y⟩_F = ⟨x, a* ⋆_M y⟩_F` (Eq. (9)). -/
theorem prop70 [Fact (Admissible M)] (d : Fin n → ℝ) (hd : ∀ i, d i ≠ 0)
    (W : Matrix (Fin n) (Fin n) ℂ) (hW : W ∈ unitaryGroup (Fin n) ℂ)
    (hMW : M = diagonal (fun i => (d i : ℂ)) * W) (a x y : KM M) :
    frobInner (a * x) y = frobInner x (star a * y) := by
  sorry

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
  sorry

/-- The matrix `[[1, 0], [1, 1]]` (real, invertible, hence admissible), used to show that
Eq. (9) does not hold for general `M` ("it is easy to build counter examples"). -/
def counterM : Matrix (Fin 2) (Fin 2) ℂ := !![1, 0; 1, 1]

theorem counterM_admissible : Admissible counterM := by
  sorry

/-- "We would expect that this adjoint will be given by the conjugate to `a` … however it is
easy to build counter examples for which this does not hold": Eq. (9) fails for
`M = [[1, 0], [1, 1]]`. -/
theorem eq9_fails_in_general :
    haveI : Fact (Admissible counterM) := ⟨counterM_admissible⟩
    ∃ a x y : KM counterM, frobInner (a * x) y ≠ frobInner x (star a * y) := by
  sorry

end Tubal
