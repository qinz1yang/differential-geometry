import Mathlib.Analysis.Calculus.LineDeriv.Basic
import Mathlib.Topology.Algebra.Order.Field
import Mathlib.Topology.Separation.Hausdorff

open scoped Topology

theorem HasLineDerivAt.tendsto_homothety_atTop
    {E F : Type*} [AddCommGroup E] [Module ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    {h : E → F} {d : F} {z v : E} (hv : HasLineDerivAt ℝ h d z v) (t : ℝ) :
    Filter.Tendsto
      (fun s : ℝ => h z + s • (h (z + s⁻¹ • (t • v)) - h z))
      Filter.atTop (𝓝 (h z + t • d)) := by
  simpa only [Function.comp_def, inv_inv] using
    (tendsto_const_nhds (x := h z)).add
      ((hv.smul t).tendsto_slope_zero_right.comp tendsto_inv_atTop_nhdsGT_zero)

theorem Continuous.homothety_limit_eq_add_smul
    {E F : Type*} [AddCommGroup E] [Module ℝ E] [TopologicalSpace E]
    [ContinuousAdd E] [ContinuousConstSMul ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    {h H : E → F} {z : E} (hH : Continuous H) (s : ℕ → ℝ)
    (hs : Filter.Tendsto s Filter.atTop Filter.atTop)
    (hdense : Dense {v : E | LineDifferentiableAt ℝ h z v})
    (hlim : ∀ w : E, Filter.Tendsto
      (fun n => h z + s n • (h (z + (s n)⁻¹ • (w - z)) - h z))
      Filter.atTop (𝓝 (H w))) :
    ∀ (v : E) (t : ℝ), H (z + t • v) = h z + t • (H (z + v) - h z) := by
  have hdirectional (v : E) (hv : LineDifferentiableAt ℝ h z v) (t : ℝ) :
      H (z + t • v) = h z + t • lineDeriv ℝ h z v := by
    have hfirst := hlim (z + t • v)
    simp only [add_sub_cancel_left] at hfirst
    exact tendsto_nhds_unique hfirst ((hv.hasLineDerivAt.tendsto_homothety_atTop t).comp hs)
  intro v t
  have heq : (fun w : E => H (z + t • w)) =
      (fun w : E => h z + t • (H (z + w) - h z)) := by
    apply Continuous.ext_on hdense
    · exact hH.comp (continuous_const.add (continuous_id.const_smul t))
    · exact continuous_const.add
        (((hH.comp (continuous_const.add continuous_id)).sub continuous_const).const_smul t)
    · intro w hw
      change H (z + t • w) = h z + t • (H (z + w) - h z)
      have hone : H (z + w) = h z + lineDeriv ℝ h z w := by
        simpa only [one_smul] using hdirectional w hw 1
      rw [hone, add_sub_cancel_left]
      exact hdirectional w hw t
  exact congrFun heq v
