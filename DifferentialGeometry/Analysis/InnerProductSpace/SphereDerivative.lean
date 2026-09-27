import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.Calculus.Deriv.Comp

open Set Filter Metric
open scoped Topology RealInnerProductSpace

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

theorem fderiv_apply_eq_of_eventuallyEq_sphere {f g : E → F} {c x v : E} {r : ℝ}
    (hr : 0 < r) (hx : x ∈ sphere c r) (hf : DifferentiableAt ℝ f x)
    (hg : DifferentiableAt ℝ g x) (hfg : f =ᶠ[𝓝[sphere c r] x] g)
    (hv : ⟪x - c, v⟫ = 0) : fderiv ℝ f x v = fderiv ℝ g x v := by
  have hnorm : ‖x - c‖ = r := by simpa only [mem_sphere, dist_eq_norm] using hx
  let α : ℝ → E := fun t => x - c + t • v
  have hα : HasDerivAt α v 0 := by
    convert! (hasDerivAt_const (0 : ℝ) (x - c)).add
      ((hasDerivAt_id (0 : ℝ)).smul_const v) using 1
    simp
  have hα0 : α 0 = x - c := by simp [α]
  have hsquare : HasDerivAt (fun t => ‖α t‖ ^ 2) 0 0 := by
    simpa only [hα0, hv, mul_zero] using hα.norm_sq
  have hnorm' : HasDerivAt (fun t => ‖α t‖) 0 0 := by
    have hd := hsquare.sqrt (by rw [hα0, hnorm]; positivity)
    simpa only [Real.sqrt_sq (norm_nonneg _), zero_div] using hd
  have hscale : HasDerivAt (fun t => r / ‖α t‖) 0 0 := by
    have hd := (hasDerivAt_const (0 : ℝ) r).div hnorm' (by rw [hα0, hnorm]; exact hr.ne')
    convert! hd using 1
    simp
  let γ : ℝ → E := fun t => c + (r / ‖α t‖) • α t
  have hγ : HasDerivAt γ v 0 := by
    have hd := (hasDerivAt_const (0 : ℝ) c).add (hscale.smul hα)
    convert! hd using 1
    simp [hα0, hnorm, hr.ne']
  have hγ0 : γ 0 = x := by
    simp only [γ, hα0, hnorm, div_self hr.ne', one_smul]
    abel
  have hnonzero : ∀ᶠ t in 𝓝 (0 : ℝ), α t ≠ 0 :=
    hα.continuousAt.eventually_ne (by rw [hα0]; exact norm_ne_zero_iff.mp (hnorm.trans_ne hr.ne'))
  have hγsphere : ∀ᶠ t in 𝓝 (0 : ℝ), γ t ∈ sphere c r := by
    filter_upwards [hnonzero] with t ht
    rw [mem_sphere, dist_eq_norm]
    change ‖c + (r / ‖α t‖) • α t - c‖ = r
    rw [add_sub_cancel_left, norm_smul, Real.norm_eq_abs,
      abs_of_nonneg (div_nonneg hr.le (norm_nonneg _))]
    exact div_mul_cancel₀ r (norm_ne_zero_iff.mpr ht)
  have hγt : Tendsto γ (𝓝 (0 : ℝ)) (𝓝[sphere c r] x) :=
    tendsto_nhdsWithin_iff.mpr ⟨by simpa only [hγ0] using hγ.continuousAt.tendsto, hγsphere⟩
  have heq : f ∘ γ =ᶠ[𝓝 (0 : ℝ)] g ∘ γ := hfg.comp_tendsto hγt
  have hfx : HasFDerivAt f (fderiv ℝ f x) (γ 0) := by simpa only [hγ0] using hf.hasFDerivAt
  have hgx : HasFDerivAt g (fderiv ℝ g x) (γ 0) := by simpa only [hγ0] using hg.hasFDerivAt
  have hfd := hfx.comp_hasDerivAt (0 : ℝ) hγ
  have hgd := hgx.comp_hasDerivAt (0 : ℝ) hγ
  exact hfd.unique (hgd.congr_of_eventuallyEq heq)

theorem fderiv_apply_eq_of_eqOn_sphere {f g : E → F} {c x v : E} {r : ℝ}
    (hr : 0 < r) (hx : x ∈ sphere c r) (hf : DifferentiableAt ℝ f x)
    (hg : DifferentiableAt ℝ g x) (hfg : EqOn f g (sphere c r))
    (hv : ⟪x - c, v⟫ = 0) : fderiv ℝ f x v = fderiv ℝ g x v := by
  apply fderiv_apply_eq_of_eventuallyEq_sphere hr hx hf hg ?_ hv
  filter_upwards [self_mem_nhdsWithin] with y hy
  exact hfg hy
