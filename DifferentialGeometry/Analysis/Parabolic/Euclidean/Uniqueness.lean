import Mathlib.Analysis.Normed.Module.Dual
import DifferentialGeometry.Analysis.Parabolic.MaximumPrinciple.PeriodicMaximum
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

private theorem periodic_eq_zero_of_homogeneous_parabolic_equation_inner
    {u : ℝ → ℝ → E} {a : ℝ → ℝ → ℝ} {s v : ℝ}
    (hper : ∀ x t, t ∈ Icc s v → u (x + 1) t = u x t)
    (hcont : ContinuousOn (Function.uncurry u) (Icc 0 1 ×ˢ Icc s v))
    (hinit : ∀ x, u x s = 0)
    (hx : ∀ x t, t ∈ Ioo s v → ContDiffAt ℝ 2 (fun y => u y t) x)
    (ht : ∀ x t, t ∈ Ioo s v → HasDerivAt (u x)
      (a x t • deriv (deriv (fun y => u y t)) x) t)
    (ha : ∀ x t, t ∈ Ioo s v → 0 ≤ a x t) :
    ∀ x t, t ∈ Icc s v → u x t = 0 := by
  classical
  by_cases hsv : s < v
  · let w : ℝ → ℝ → E := fun x t => if t ∈ Icc s v then u x t else 0
    have hw (t : ℝ) (ht' : t ∈ Icc s v) : (fun x => w x t) = fun x => u x t := by
      funext x
      exact if_pos ht'
    have hwt (x t : ℝ) (ht' : t ∈ Ioo s v) :
        (fun r => w x r) =ᶠ[𝓝 t] u x := by
      filter_upwards [Icc_mem_nhds ht'.1 ht'.2] with r hr
      exact if_pos hr
    have hwper (x t : ℝ) : w (x + 1) t = w x t := by
      by_cases ht' : t ∈ Icc s v
      · simp only [w, if_pos ht', hper x t ht']
      · simp only [w, if_neg ht']
    have hwcont : ContinuousOn (Function.uncurry w) (Icc 0 1 ×ˢ Icc s v) := by
      apply hcont.congr
      intro p hp
      exact if_pos hp.2
    have hwtime (x t : ℝ) (ht' : t ∈ Ioo s v) :
        HasDerivAt (w x) (a x t • deriv (deriv (fun y => u y t)) x) t :=
      (ht x t ht').congr_of_eventuallyEq (hwt x t ht')
    have hz := periodic_le_of_nonpositive_maximum_derivative
      (w := fun x t => ‖w x t‖ ^ 2) (M := 0) hsv
      (fun x t => by rw [hwper]) (hwcont.norm.pow 2)
      (fun x => by rw [congrFun (hw s ⟨le_rfl, hsv.le⟩) x, hinit]; simp)
      (fun x t ht' => (hwtime x t ht').norm_sq.differentiableAt) ?_
    · intro x t ht'
      have hn : ‖w x t‖ ^ 2 = 0 := le_antisymm (hz x t ht') (sq_nonneg _)
      have hzero : w x t = 0 := norm_eq_zero.mp (sq_eq_zero_iff.mp hn)
      exact (congrFun (hw t ht') x).symm.trans hzero
    · intro x t ht' hmax
      have hxe : ∀ᶠ y in 𝓝 x, DifferentiableAt ℝ (fun y => w y t) y := by
        filter_upwards with y
        rw [hw t ⟨ht'.1.le, ht'.2.le⟩]
        exact (hx y t ht').differentiableAt (by norm_num)
      have hxx : DifferentiableAt ℝ (deriv (fun y => w y t)) x := by
        rw [hw t ⟨ht'.1.le, ht'.2.le⟩]
        exact ((hx x t ht').derivWithin (m := 1) (by norm_num)).differentiableAt (by norm_num)
      have hsq : HasDerivAt (fun y => ‖w y t‖ ^ 2)
          (2 * ⟪w x t, deriv (fun y => w y t) x⟫_ℝ) x :=
        hxe.self_of_nhds.hasDerivAt.norm_sq
      have hsq2 := hasDerivAt_deriv_norm_sq hxe hxx
      have hneg : HasDerivAt (deriv (fun y => -(‖w y t‖ ^ 2)))
          (-(2 * ‖deriv (fun y => w y t) x‖ ^ 2 +
            2 * ⟪w x t, deriv (deriv (fun y => w y t)) x⟫_ℝ)) x := by
        have heq : deriv (fun y => -(‖w y t‖ ^ 2)) =
            (fun y => -(deriv (fun y => ‖w y t‖ ^ 2) y)) := by
          funext y
          exact deriv.neg (f := fun y => ‖w y t‖ ^ 2)
        rw [heq]
        exact hsq2.neg
      have hnonpos := IsLocalMin.second_deriv_nonneg hmax.neg hsq.neg hneg
      have hsecond : deriv (deriv (fun y => ‖w y t‖ ^ 2)) x ≤ 0 := by
        rw [deriv_deriv_norm_sq hxe hxx]
        linarith
      have hres : deriv (w x) t - a x t • deriv (deriv (fun y => w y t)) x = 0 := by
        rw [(hwtime x t ht').deriv, hw t ⟨ht'.1.le, ht'.2.le⟩, sub_self]
      have heq := norm_sq_parabolic_eq hxe hxx (hwtime x t ht').differentiableAt (a := a x t)
      simp only [hres, inner_zero_right, mul_zero, zero_sub] at heq
      have hmul := mul_nonpos_of_nonneg_of_nonpos (ha x t ht') hsecond
      have hgrad : 0 ≤ 2 * a x t * ‖deriv (fun y => w y t) x‖ ^ 2 :=
        mul_nonneg (mul_nonneg (by norm_num) (ha x t ht')) (sq_nonneg _)
      linarith
  · intro x t ht'
    have hts : t = s := le_antisymm (ht'.2.trans (not_lt.mp hsv)) ht'.1
    simpa only [hts] using hinit x

section Normed

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]

theorem periodic_eq_zero_of_homogeneous_parabolic_equation
    {u : ℝ → ℝ → V} {a : ℝ → ℝ → ℝ} {s v : ℝ}
    (hper : ∀ x t, t ∈ Icc s v → u (x + 1) t = u x t)
    (hcont : ContinuousOn (Function.uncurry u) (Icc 0 1 ×ˢ Icc s v))
    (hinit : ∀ x, u x s = 0)
    (hx : ∀ x t, t ∈ Ioo s v → ContDiffAt ℝ 2 (fun y => u y t) x)
    (ht : ∀ x t, t ∈ Ioo s v → HasDerivAt (u x)
      (a x t • deriv (deriv (fun y => u y t)) x) t)
    (ha : ∀ x t, t ∈ Ioo s v → 0 ≤ a x t) :
    ∀ x t, t ∈ Icc s v → u x t = 0 := by
  intro x t ht'
  apply SeparatingDual.eq_zero_of_forall_dual_eq_zero (R := ℝ)
  intro L
  have hderiv (y r : ℝ) (hr : r ∈ Ioo s v) :
      deriv (fun z => L (u z r)) y = L (deriv (fun z => u z r) y) :=
    (L.hasFDerivAt.comp_hasDerivAt y ((hx y r hr).differentiableAt (by norm_num)).hasDerivAt).deriv
  have hsecond (y r : ℝ) (hr : r ∈ Ioo s v) :
      deriv (deriv (fun z => L (u z r))) y = L (deriv (deriv (fun z => u z r)) y) := by
    rw [show deriv (fun z => L (u z r)) = fun z => L (deriv (fun z => u z r) z) from
      funext fun z => hderiv z r hr]
    exact (L.hasFDerivAt.comp_hasDerivAt y
      (((hx y r hr).derivWithin (m := 1) (by norm_num)).differentiableAt (by norm_num)).hasDerivAt).deriv
  exact periodic_eq_zero_of_homogeneous_parabolic_equation_inner
    (u := fun y r => L (u y r)) (a := a)
    (fun y r hr => congrArg L (hper y r hr))
    (L.continuous.comp_continuousOn hcont)
    (fun y => by rw [hinit, map_zero])
    (fun y r hr => L.contDiff.contDiffAt.comp y (hx y r hr))
    (fun y r hr => by
      rw [hsecond y r hr]
      convert L.hasFDerivAt.comp_hasDerivAt r (ht y r hr) using 1
      · rfl
      · exact (L.map_smul _ _).symm) ha x t ht'

theorem affine_periodic_eq_affine_of_homogeneous_parabolic_equation
    {u : ℝ → ℝ → V} {a : ℝ → ℝ → ℝ} {s v : ℝ} (p q : V)
    (hper : ∀ x t, t ∈ Icc s v → u (x + 1) t = u x t + p)
    (hcont : ContinuousOn (Function.uncurry u) (Icc 0 1 ×ˢ Icc s v))
    (hinit : ∀ x, u x s = x • p + q)
    (hx : ∀ x t, t ∈ Ioo s v → ContDiffAt ℝ 2 (fun y => u y t) x)
    (ht : ∀ x t, t ∈ Ioo s v → HasDerivAt (u x)
      (a x t • deriv (deriv (fun y => u y t)) x) t)
    (ha : ∀ x t, t ∈ Ioo s v → 0 ≤ a x t) :
    ∀ x t, t ∈ Icc s v → u x t = x • p + q := by
  let w : ℝ → ℝ → V := fun x t => u x t - (x • p + q)
  have hderiv (x t : ℝ) (ht' : t ∈ Ioo s v) :
      deriv (fun y => w y t) x = deriv (fun y => u y t) x - p := by
    convert (((hx x t ht').differentiableAt (by norm_num)).hasDerivAt.sub
      (((hasDerivAt_id x).smul_const p).add_const q)).deriv using 1
    · rfl
    · rw [one_smul]
  have hsecond (x t : ℝ) (ht' : t ∈ Ioo s v) :
      deriv (deriv (fun y => w y t)) x = deriv (deriv (fun y => u y t)) x := by
    rw [show deriv (fun y => w y t) = fun y => deriv (fun z => u z t) y - p from
      funext fun y => hderiv y t ht', deriv_sub_const]
  have hzero := periodic_eq_zero_of_homogeneous_parabolic_equation
    (u := w) (a := a) (s := s) (v := v)
    (fun x t ht' => by
      dsimp [w]
      rw [hper x t ht', add_smul, one_smul]
      abel)
    (hcont.sub ((continuous_fst.smul continuous_const).add continuous_const).continuousOn)
    (fun x => by dsimp [w]; rw [hinit, sub_self])
    (fun x t ht' => (hx x t ht').sub
      ((contDiffAt_id.smul contDiffAt_const).add contDiffAt_const))
    (fun x t ht' => by
      rw [hsecond x t ht']
      exact (ht x t ht').sub_const (x • p + q)) ha
  intro x t ht'
  exact sub_eq_zero.mp (hzero x t ht')

theorem affine_periodic_eq_id_of_homogeneous_parabolic_equation
    {u a : ℝ → ℝ → ℝ} {s v : ℝ}
    (hper : ∀ x t, t ∈ Icc s v → u (x + 1) t = u x t + 1)
    (hcont : ContinuousOn (Function.uncurry u) (Icc 0 1 ×ˢ Icc s v))
    (hinit : ∀ x, u x s = x)
    (hx : ∀ x t, t ∈ Ioo s v → ContDiffAt ℝ 2 (fun y => u y t) x)
    (ht : ∀ x t, t ∈ Ioo s v → HasDerivAt (u x)
      (a x t * deriv (deriv (fun y => u y t)) x) t)
    (ha : ∀ x t, t ∈ Ioo s v → 0 ≤ a x t) :
    ∀ x t, t ∈ Icc s v → u x t = x := by
  simpa only [smul_eq_mul, mul_one, add_zero] using
    affine_periodic_eq_affine_of_homogeneous_parabolic_equation
      (u := u) (a := a) 1 0 hper hcont
      (fun x => by simpa only [smul_eq_mul, mul_one, add_zero] using hinit x) hx ht ha

end Normed


end DifferentialGeometry.Analysis.Parabolic
