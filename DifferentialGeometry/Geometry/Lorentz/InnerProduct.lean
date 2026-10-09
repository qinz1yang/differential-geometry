import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.LinearAlgebra.Prod
import Mathlib.Tactic.Linarith

namespace DifferentialGeometry

variable (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E]

noncomputable def lorentzForm : LinearMap.BilinForm ℝ (ℝ × E) :=
  (innerₗ E).compl₁₂ (LinearMap.snd ℝ ℝ E) (LinearMap.snd ℝ ℝ E) -
    (LinearMap.fst ℝ ℝ E).smulRight (LinearMap.fst ℝ ℝ E)

@[simp] theorem lorentzForm_apply (x y : ℝ × E) :
    lorentzForm E x y = inner ℝ x.2 y.2 - x.1 * y.1 :=
  rfl

theorem lorentzForm_isSymm : (lorentzForm E).IsSymm := by
  constructor
  intro x y
  change inner ℝ x.2 y.2 - x.1 * y.1 = inner ℝ y.2 x.2 - y.1 * x.1
  rw [real_inner_comm y.2 x.2, mul_comm y.1]

variable {E}

theorem lorentzForm_sq_le_of_orthogonal {p x y : ℝ × E}
    (hp : lorentzForm E p p ≤ 0) (hp0 : p ≠ 0)
    (hx : lorentzForm E p x = 0) (hy : lorentzForm E p y = 0) :
    (lorentzForm E x y) ^ 2 ≤ lorentzForm E x x * lorentzForm E y y := by
  have hp' : ‖p.2‖ ^ 2 ≤ p.1 ^ 2 := by
    simpa only [lorentzForm_apply, real_inner_self_eq_norm_sq, ← sq, sub_nonpos] using hp
  have ht : p.1 ≠ 0 := by
    intro ht
    have hn : ‖p.2‖ = 0 := by
      rw [ht] at hp'
      nlinarith [norm_nonneg p.2]
    exact hp0 (Prod.ext ht (norm_eq_zero.mp hn))
  let K := LinearMap.ker (lorentzForm E p)
  let B : LinearMap.BilinForm ℝ K := (lorentzForm E).domRestrict₁₂ K K
  have hB (z : K) : 0 ≤ B z z := by
    have hz : inner ℝ p.2 z.val.2 = p.1 * z.val.1 := by
      exact sub_eq_zero.mp z.property
    have hi := real_inner_mul_inner_self_le p.2 z.val.2
    rw [real_inner_self_eq_norm_sq, real_inner_self_eq_norm_sq] at hi
    have hc : p.1 ^ 2 * z.val.1 ^ 2 ≤ p.1 ^ 2 * ‖z.val.2‖ ^ 2 := calc
      p.1 ^ 2 * z.val.1 ^ 2 = (inner ℝ p.2 z.val.2) ^ 2 := by rw [hz]; ring
      _ ≤ ‖p.2‖ ^ 2 * ‖z.val.2‖ ^ 2 := by simpa only [sq] using hi
      _ ≤ p.1 ^ 2 * ‖z.val.2‖ ^ 2 :=
        mul_le_mul_of_nonneg_right hp' (sq_nonneg _)
    have hz' := (mul_le_mul_iff_right₀ (sq_pos_of_ne_zero ht)).mp hc
    change 0 ≤ inner ℝ z.val.2 z.val.2 - z.val.1 * z.val.1
    rw [real_inner_self_eq_norm_sq, ← sq]
    exact sub_nonneg.mpr hz'
  exact B.apply_sq_le_of_symm hB ((lorentzForm_isSymm E).domRestrict K) ⟨x, hx⟩ ⟨y, hy⟩

theorem neg_lorentzForm_self_mul_norm_snd_sq_le_of_orthogonal {p z : ℝ × E}
    (hz : lorentzForm E p z = 0) :
    -(lorentzForm E p p) * ‖z.2‖ ^ 2 ≤ p.1 ^ 2 * lorentzForm E z z := by
  have hz' : inner ℝ p.2 z.2 = p.1 * z.1 := sub_eq_zero.mp hz
  have hi := real_inner_mul_inner_self_le p.2 z.2
  rw [real_inner_self_eq_norm_sq, real_inner_self_eq_norm_sq, hz'] at hi
  rw [lorentzForm_apply, lorentzForm_apply, real_inner_self_eq_norm_sq,
    real_inner_self_eq_norm_sq]
  nlinarith

theorem norm_snd_sq_le_mul_lorentzForm_self_of_orthogonal {p z : ℝ × E}
    (hp : lorentzForm E p p ≤ -1) (hz : lorentzForm E p z = 0) :
    ‖z.2‖ ^ 2 ≤ p.1 ^ 2 * lorentzForm E z z := by
  have hcoef : 1 ≤ -(lorentzForm E p p) := by linarith
  have hmul := mul_le_mul_of_nonneg_right hcoef (sq_nonneg ‖z.2‖)
  simp only [one_mul] at hmul
  exact hmul.trans (neg_lorentzForm_self_mul_norm_snd_sq_le_of_orthogonal hz)

end DifferentialGeometry
