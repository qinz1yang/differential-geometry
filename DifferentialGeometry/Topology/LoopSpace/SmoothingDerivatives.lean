import DifferentialGeometry.Topology.LoopSpace.Regular
import Mathlib.Analysis.Calculus.ParametricIntegral









noncomputable section

open Set Filter Function ContinuousMap MeasureTheory ContinuousLinearMap
open scoped Topology ContDiff Convolution

namespace DifferentialGeometry.Topology

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]

omit [CompleteSpace F] in
theorem deriv_smoothPeriodic (φ : ContDiffBump (0 : ℝ)) (γ : freeLoop F)
    (hγ : ContDiff ℝ 1 (fun t : ℝ => γ (t : loopCircle))) :
    deriv (DifferentialGeometry.Analysis.smoothPeriodic φ (fun t : ℝ => γ (t : loopCircle))) =
      DifferentialGeometry.Analysis.smoothPeriodic φ (deriv (fun t : ℝ => γ (t : loopCircle))) := by
  let f : ℝ → F := fun t => γ (t : loopCircle)
  have hf : Continuous f := hγ.continuous
  have hdf : Continuous (deriv f) := by
    simpa only [iteratedDeriv_one] using (contDiff_nat_iff_iteratedDeriv.mp hγ).1 1 le_rfl
  have hper : Periodic (deriv f) 1 := by
    simpa only [iteratedDeriv_one] using periodic_iteratedDeriv (f := f) (n := 1) (by
      intro t
      simp only [f, QuotientAddGroup.mk_add, AddCircle.coe_period, add_zero])
  let dγ : freeLoop F := periodicLoop (deriv f) hper hdf
  have hbound (x : ℝ) : ‖deriv f x‖ ≤ ‖dγ‖ := dγ.norm_coe_le_norm (x : loopCircle)
  funext x
  have hi : Integrable (fun t => φ.normed volume t • f (x - t)) :=
    φ.hasCompactSupport_normed.convolutionExists_left_of_continuous_right (lsmul ℝ ℝ)
      φ.integrable_normed.locallyIntegrable hf x
  have hm : ∀ᶠ y : ℝ in 𝓝 x,
      AEStronglyMeasurable (fun t => φ.normed volume t • f (y - t)) := by
    exact Eventually.of_forall fun y =>
      (φ.continuous_normed.smul (hf.comp (continuous_const.sub continuous_id))).aestronglyMeasurable
  have hdm : AEStronglyMeasurable (fun t => φ.normed volume t • deriv f (x - t)) :=
    (φ.continuous_normed.smul (hdf.comp (continuous_const.sub continuous_id))).aestronglyMeasurable
  have hb : ∀ᵐ t : ℝ, ∀ y ∈ (Set.univ : Set ℝ),
      ‖φ.normed volume t • deriv f (y - t)‖ ≤ φ.normed volume t * ‖dγ‖ := by
    filter_upwards [] with t y _
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (φ.nonneg_normed t)]
    exact mul_le_mul_of_nonneg_left (hbound (y - t)) (φ.nonneg_normed t)
  have hd : ∀ᵐ t : ℝ, ∀ y ∈ (Set.univ : Set ℝ),
      HasDerivAt (fun y => φ.normed volume t • f (y - t))
        (φ.normed volume t • deriv f (y - t)) y := by
    filter_upwards [] with t y _
    apply HasDerivAt.const_smul
    simpa only [one_smul, f, Function.comp_def, id_eq] using ((hγ.differentiable one_ne_zero (y - t)).hasDerivAt.scomp y
      ((hasDerivAt_id y).sub_const t))
  have h := (hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (Filter.univ_mem : (Set.univ : Set ℝ) ∈ 𝓝 x) hm hi hdm hb
    (φ.integrable_normed.mul_const ‖dγ‖) hd).2.deriv
  change deriv (fun y => ∫ t, φ.normed volume t • f (y - t)) x =
    ∫ t, φ.normed volume t • deriv f (x - t)
  exact h

end DifferentialGeometry.Topology
