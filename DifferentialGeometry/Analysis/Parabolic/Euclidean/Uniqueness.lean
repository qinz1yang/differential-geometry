import DifferentialGeometry.Analysis.Parabolic.MaximumPrinciple.PeriodicReaction
import DifferentialGeometry.Analysis.Parabolic.Euclidean.VectorNorm

open Set Filter
open scoped Topology InnerProductSpace ContDiff

namespace DifferentialGeometry.Analysis.Parabolic

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

theorem norm_sq_parabolic_le_of_residual_bound
    {u : ℝ → ℝ → E} {x t a δ L : ℝ}
    (hδ : 0 < δ) (ha : δ ≤ a)
    (hx : ∀ᶠ y in 𝓝 x, DifferentiableAt ℝ (fun y => u y t) y)
    (hxx : DifferentiableAt ℝ (deriv (fun y => u y t)) x)
    (ht : DifferentiableAt ℝ (fun s => u x s) t)
    (hres : ‖deriv (fun s => u x s) t - a • deriv (deriv (fun y => u y t)) x‖ ≤
      L * (‖u x t‖ + ‖deriv (fun y => u y t) x‖)) :
    deriv (fun s => ‖u x s‖ ^ 2) t - a * deriv (deriv (fun y => ‖u y t‖ ^ 2)) x ≤
      (2 * L + L ^ 2 / δ) * ‖u x t‖ ^ 2 := by
  rw [norm_sq_parabolic_eq hx hxx ht]
  have hi := real_inner_le_norm (u x t)
    (deriv (fun s => u x s) t - a • deriv (deriv (fun y => u y t)) x)
  have hri := mul_le_mul_of_nonneg_left hres (norm_nonneg (u x t))
  have hyoung : 2 * L * ‖u x t‖ * ‖deriv (fun y => u y t) x‖ ≤
      L ^ 2 / δ * ‖u x t‖ ^ 2 + δ * ‖deriv (fun y => u y t) x‖ ^ 2 := by
    have hs := sq_nonneg (L * ‖u x t‖ - δ * ‖deriv (fun y => u y t) x‖)
    apply (mul_le_mul_iff_right₀ hδ).mp
    field_simp
    nlinarith
  have ha' := mul_le_mul_of_nonneg_right ha (sq_nonneg ‖deriv (fun y => u y t) x‖)
  nlinarith [sq_nonneg ‖deriv (fun y => u y t) x‖]


theorem periodic_eq_zero_of_parabolic_residual_bound
    {u : ℝ → ℝ → E} {a : ℝ → ℝ → ℝ} {δ L s v : ℝ}
    (hsv : s < v) (hδ : 0 < δ)
    (hper : ∀ x t, u (x + 1) t = u x t)
    (hcont : ContinuousOn (Function.uncurry u) (Icc 0 1 ×ˢ Icc s v))
    (hinit : ∀ x, u x s = 0)
    (hx : ∀ x t, t ∈ Ioo s v → ContDiffAt ℝ 2 (fun y => u y t) x)
    (ht : ∀ x t, t ∈ Ioo s v → DifferentiableAt ℝ (fun τ => u x τ) t)
    (ha : ∀ x t, t ∈ Ioo s v → δ ≤ a x t)
    (hres : ∀ x t, t ∈ Ioo s v →
      ‖deriv (fun τ => u x τ) t - a x t • deriv (deriv (fun y => u y t)) x‖ ≤
        L * (‖u x t‖ + ‖deriv (fun y => u y t) x‖)) :
    ∀ x t, t ∈ Icc s v → u x t = 0 := by
  have hz := periodic_eq_zero_of_nonnegative_of_maximum_deriv_le_mul
    (w := fun x t => ‖u x t‖ ^ 2) (C := 2 * L + L ^ 2 / δ) hsv
    (fun x t => by rw [hper]) (hcont.norm.pow 2)
    (fun x => by rw [hinit]; simp) (fun _ _ _ => sq_nonneg _)
    (fun x t ht' => (ht x t ht').hasDerivAt.norm_sq.differentiableAt) ?_
  · intro x t ht'
    have hn : ‖u x t‖ = 0 := (sq_eq_zero_iff.mp (hz x t ht'))
    exact norm_eq_zero.mp hn
  · intro x t ht' hmax
    have hxe : ∀ᶠ y in 𝓝 x, DifferentiableAt ℝ (fun y => u y t) y := by
      filter_upwards with y
      exact (hx y t ht').differentiableAt (by norm_num)
    have hxx : DifferentiableAt ℝ (deriv (fun y => u y t)) x :=
      ((hx x t ht').derivWithin (m := 1) (by norm_num)).differentiableAt (by norm_num)
    have hsq : HasDerivAt (fun y => ‖u y t‖ ^ 2)
        (2 * ⟪u x t, deriv (fun y => u y t) x⟫_ℝ) x :=
      hxe.self_of_nhds.hasDerivAt.norm_sq
    have hsq2 := hasDerivAt_deriv_norm_sq hxe hxx
    have hneg : HasDerivAt (deriv (fun y => -(‖u y t‖ ^ 2)))
        (-(2 * ‖deriv (fun y => u y t) x‖ ^ 2 +
          2 * ⟪u x t, deriv (deriv (fun y => u y t)) x⟫_ℝ)) x := by
      have heq : deriv (fun y => -(‖u y t‖ ^ 2)) =
          (fun y => -(deriv (fun y => ‖u y t‖ ^ 2) y)) := by
        funext y
        exact deriv.neg (f := fun y => ‖u y t‖ ^ 2)
      rw [heq]
      exact hsq2.neg
    have hnonpos := IsLocalMin.second_deriv_nonneg hmax.neg hsq.neg hneg
    have hsecond : deriv (deriv (fun y => ‖u y t‖ ^ 2)) x ≤ 0 := by
      rw [deriv_deriv_norm_sq hxe hxx]
      linarith
    have hineq := norm_sq_parabolic_le_of_residual_bound hδ (ha x t ht') hxe hxx
      (ht x t ht') (hres x t ht')
    have hmul := mul_nonpos_of_nonneg_of_nonpos (hδ.le.trans (ha x t ht')) hsecond
    linarith

end DifferentialGeometry.Analysis.Parabolic
