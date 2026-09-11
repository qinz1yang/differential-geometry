import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Topology.Instances.EReal.Lemmas








open Set Filter
open scoped Topology

namespace DifferentialGeometry.Analysis



theorem limsup_right_slope_le_of_upper_contact
    {f F : ℝ → ℝ} {x d : ℝ} (hF : HasDerivAt F d x)
    (hle : ∀ᶠ t in 𝓝[>] x, f t ≤ F t) (heq : f x = F x) :
    limsup (fun t => (slope f x t : EReal)) (𝓝[>] x) ≤ (d : EReal) := by
  have hsl : (fun t => (slope f x t : EReal)) ≤ᶠ[𝓝[>] x]
      (fun t => (slope F x t : EReal)) := by
    filter_upwards [hle, self_mem_nhdsWithin] with t ht hxt
    apply EReal.coe_le_coe_iff.mpr
    rw [slope_def_field, slope_def_field, heq]
    exact div_le_div_of_nonneg_right (sub_le_sub_right ht _) (sub_nonneg.mpr (le_of_lt hxt))
  have ht : Tendsto (slope F x) (𝓝[>] x) (𝓝 d) :=
    (hasDerivWithinAt_iff_tendsto_slope' (show x ∉ Ioi x from lt_irrefl x)).mp
      hF.hasDerivWithinAt
  exact (limsup_le_limsup hsl).trans_eq
    ((continuous_coe_real_ereal.tendsto d).comp ht).limsup_eq

end DifferentialGeometry.Analysis
