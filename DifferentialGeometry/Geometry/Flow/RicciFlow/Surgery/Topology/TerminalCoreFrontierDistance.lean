import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.InverseSqrtScalarDistance
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.TerminalScalarBall
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.TerminalScalarCurvature
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Contract.Terminal
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.CanonicalNeighborhoodInduction

set_option autoImplicit false

noncomputable section

open Set Filter
open DifferentialGeometry.Geometry.Curvature
open scoped Manifold ContDiff Topology NNReal ENNReal

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.OrientedThreeStage.IncomingSlab

universe u

variable {P : OrientedThreeStage.{u}} {a s : ℝ} {G : P.IncomingSlab a s}

theorem TerminalLimitMetric.inv_sqrt_sub_inv_sqrt_scalar_le_of_gradientBoundBefore
    (L : G.TerminalLimitMetric) {Cgrad : ℝ≥0} {q m r : ℝ}
    (hgrad : G.GradientBoundBefore Cgrad q s) (hqm : q < m) {x y : G.terminalRegularOpen}
    (hx : m < metricScalarAt L.metric x) (hy : metricScalarAt L.metric y < m)
    (hxy : riemannianEDistOf L.metric x y < ENNReal.ofReal r) :
    (Real.sqrt m)⁻¹ - (Real.sqrt (metricScalarAt L.metric x))⁻¹ ≤ Cgrad / 2 * r := by
  have hr : 0 ≤ r := by
    by_contra hneg
    rw [ENNReal.ofReal_of_nonpos (not_le.mp hneg).le] at hxy
    exact ENNReal.not_lt_zero hxy
  rcases le_or_gt m 0 with hm0 | hm0
  · rw [Real.sqrt_eq_zero'.mpr hm0, inv_zero, zero_sub]
    exact (neg_nonpos.mpr (inv_nonneg.mpr (Real.sqrt_nonneg _))).trans (by positivity)
  have hxpos : 0 < metricScalarAt L.metric x := hm0.trans hx
  have hlim : Tendsto (fun t => (Real.sqrt m)⁻¹ -
      (Real.sqrt (metricScalarAt (G.flow.base.metric t) x.1))⁻¹) (𝓝[<] s)
      (𝓝 ((Real.sqrt m)⁻¹ - (Real.sqrt (metricScalarAt L.metric x))⁻¹)) :=
    ((L.tendsto_metricScalarAt x).sqrt.inv₀ (Real.sqrt_pos.mpr hxpos).ne').const_sub _
  refine le_of_tendsto hlim ?_
  filter_upwards [Ioo_mem_nhdsLT G.lt, (L.tendsto_metricScalarAt x).eventually (lt_mem_nhds hx),
    (L.tendsto_metricScalarAt y).eventually (gt_mem_nhds hy),
    L.eventually_riemannianEDistOf_lt x y hxy] with t ht hxt hyt hd
  exact Perelman.CanonicalNeighborhood.inv_sqrt_sub_inv_sqrt_scalar_le_of_threshold_gradient_bound
    G.flow Cgrad.coe_nonneg hqm (fun z hz v => hgrad z t ht hz v) hxt.le hyt.le hr
    (show riemannianEDistOf (G.flow.base.metric t) x.1 y.1 ≤ ENNReal.ofReal r from hd.le)

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.OrientedThreeStage.IncomingSlab

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.TerminalCorePresentation

universe u

theorem ofReal_lt_riemannianEDistOf_frontier_of_gradientBoundBefore {D : OneStepIncoming.{u}}
    {ε Λ : ℝ} (P : TerminalCorePresentation D ε Λ)
    (c : ConnectedComponents D.slab.terminalRegularOpen) (hc : c ∈ P.component)
    {Cgrad : ℝ≥0} {q A : ℝ} (hgrad : D.slab.GradientBoundBefore Cgrad q D.endTime)
    (hq : 0 < q) (hA : 0 ≤ A) (x : D.slab.terminalRegularOpen)
    (hx : 2 * max (Λ * (P.coreRadius ^ 2)⁻¹) q * (1 + Cgrad * A) ^ 2 <
      metricScalarAt D.terminal.metric x) :
    ∀ w ∈ frontier (P.core c),
      ENNReal.ofReal (A / Real.sqrt (metricScalarAt D.terminal.metric x)) <
        riemannianEDistOf D.terminal.metric x w := by
  intro w hw
  set μ := max (Λ * (P.coreRadius ^ 2)⁻¹) q with hμdef
  have hμ : 0 < μ := hq.trans_le (le_max_right _ _)
  set R := metricScalarAt D.terminal.metric x with hRdef
  have hqm : q < 2 * μ := by linarith [le_max_right (Λ * (P.coreRadius ^ 2)⁻¹) q]
  have hwμ : metricScalarAt D.terminal.metric w < 2 * μ := by
    linarith [P.frontier_scalar_le c hc hw, le_max_left (Λ * (P.coreRadius ^ 2)⁻¹) q]
  have hCA : 0 ≤ (Cgrad : ℝ) * A := mul_nonneg Cgrad.coe_nonneg hA
  have h1 : 1 ≤ (1 + (Cgrad : ℝ) * A) ^ 2 := by nlinarith
  have hxμ : 2 * μ < R := lt_of_le_of_lt (le_mul_of_one_le_right (by positivity) h1) hx
  have hRpos : 0 < R := by linarith
  have hsR : 0 < Real.sqrt R := Real.sqrt_pos.mpr hRpos
  have hsm : 0 < Real.sqrt (2 * μ) := Real.sqrt_pos.mpr (by positivity)
  by_contra hcon
  have hle := not_lt.mp hcon
  have hbound : (Real.sqrt (2 * μ))⁻¹ - (Real.sqrt R)⁻¹ ≤ Cgrad / 2 * (A / Real.sqrt R) := by
    refine le_of_forall_pos_le_add fun η hη => ?_
    have hη' : 0 < η / ((Cgrad : ℝ) / 2 + 1) := by positivity
    have hlt : riemannianEDistOf D.terminal.metric x w <
        ENNReal.ofReal (A / Real.sqrt R + η / ((Cgrad : ℝ) / 2 + 1)) :=
      hle.trans_lt ((ENNReal.ofReal_lt_ofReal_iff (by positivity)).mpr (by linarith))
    have h := D.terminal.inv_sqrt_sub_inv_sqrt_scalar_le_of_gradientBoundBefore hgrad hqm hxμ
      hwμ hlt
    have hCη : (Cgrad : ℝ) / 2 * (η / ((Cgrad : ℝ) / 2 + 1)) ≤ η := by
      rw [mul_div_assoc', div_le_iff₀ (by positivity)]
      nlinarith [Cgrad.coe_nonneg]
    nlinarith
  have hkey : Real.sqrt R / Real.sqrt (2 * μ) - 1 ≤ (Cgrad : ℝ) * A / 2 := by
    have h2 := mul_le_mul_of_nonneg_left hbound hsR.le
    rw [mul_sub, mul_inv_cancel₀ hsR.ne', ← div_eq_mul_inv] at h2
    calc Real.sqrt R / Real.sqrt (2 * μ) - 1 ≤ Real.sqrt R * ((Cgrad : ℝ) / 2 * (A / Real.sqrt R))
          := h2
      _ = (Cgrad : ℝ) * A / 2 := by field_simp
  have hsq : Real.sqrt (2 * μ) * (1 + (Cgrad : ℝ) * A) < Real.sqrt R := by
    rw [← Real.sqrt_sq (by positivity : (0 : ℝ) ≤ 1 + Cgrad * A), ← Real.sqrt_mul (by positivity)]
    exact Real.sqrt_lt_sqrt (by positivity) hx
  have hdiv : 1 + (Cgrad : ℝ) * A < Real.sqrt R / Real.sqrt (2 * μ) := by
    rw [lt_div_iff₀ hsm]
    linarith
  linarith

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.TerminalCorePresentation
