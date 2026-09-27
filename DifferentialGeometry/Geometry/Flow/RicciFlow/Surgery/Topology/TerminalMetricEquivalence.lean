import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.EventData
import DifferentialGeometry.Geometry.Flow.RicciFlow.Estimates.CurvatureMetricComparison
import DifferentialGeometry.Geometry.Metric.PointwiseInner.Bounds

noncomputable section

open Set Manifold
open DifferentialGeometry.Geometry.Curvature DifferentialGeometry.Tensor0SBundle
open scoped Manifold ContDiff

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.OrientedThreeStage

universe u

variable {P : OrientedThreeStage.{u}} {a s : ℝ}

theorem IncomingSlab.metric_inner_bounds_on_tail
    (G : P.IncomingSlab a s) {c K : ℝ} (hc : c ∈ Ico a s) (hK : 0 ≤ K)
    (U : Set P.Carrier)
    (hcurv : ∀ y ∈ U, ∀ t ∈ Ico c s, G.riemannNorm t y ≤ K) :
    ∀ t ∈ Ico c s, ∀ y ∈ U, ∀ v : TangentSpace ThreeModel y,
      Real.exp (-(18 * K * (s - c))) * (G.flow.base.metric c).inner y v v ≤
          (G.flow.base.metric t).inner y v v ∧
        (G.flow.base.metric t).inner y v v ≤
          Real.exp (18 * K * (s - c)) * (G.flow.base.metric c).inner y v v := by
  intro t ht y hy v
  have hsq : ∀ r ∈ Icc c t,
      normSq0S (G.flow.base.metric r) y 4 (G.flow.base.rm04 r y) ≤ K ^ 2 := by
    intro r hr
    have hb := hcurv y hy r ⟨hr.1, hr.2.trans_lt ht.2⟩
    have hn := normSq0S_nonneg (G.flow.base.metric r) y 4 (G.flow.base.rm04 r y)
    have he := Real.sq_sqrt hn
    change Real.sqrt (normSq0S (G.flow.base.metric r) y 4 (G.flow.base.rm04 r y)) ≤ K at hb
    nlinarith [Real.sqrt_nonneg (normSq0S (G.flow.base.metric r) y 4 (G.flow.base.rm04 r y))]
  have hcmp := metric_inner_exp_bounds_of_curvature_bound G.flow G.equation
    (a := c) (b := t) (C := K ^ 2)
    (fun r hr => ⟨hc.1.trans hr.1, hr.2.trans_lt ht.2⟩)
    (fun r hr => ⟨hc.1.trans_lt hr.1, hr.2.trans ht.2⟩)
    y hsq ⟨ht.1, le_rfl⟩ ⟨le_rfl, ht.1⟩ v
  have heq : 2 * (Module.finrank ℝ ThreeSpace : ℝ) ^ 2 * Real.sqrt (K ^ 2) * |t - c| =
      18 * K * (t - c) := by
    rw [Real.sqrt_sq hK, abs_of_nonneg (sub_nonneg.mpr ht.1)]
    norm_num [ThreeSpace]
  rw [heq] at hcmp
  have htime : 18 * K * (t - c) ≤ 18 * K * (s - c) :=
    mul_le_mul_of_nonneg_left (sub_le_sub_right ht.2.le c) (by positivity)
  have hnn := metric_inner_self_nonneg (G.flow.base.metric c) y v
  constructor
  · exact (mul_le_mul_of_nonneg_right
      (Real.exp_le_exp.mpr (neg_le_neg htime)) hnn).trans hcmp.1
  · exact hcmp.2.trans (mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr htime) hnn)

theorem IncomingSlab.exists_terminalRegular_metric_bounds
    (G : P.IncomingSlab a s) {x : P.Carrier} (hx : x ∈ G.terminalRegularRegion) :
    ∃ (U : Set P.Carrier) (c K : ℝ), IsOpen U ∧ x ∈ U ∧ c ∈ Ico a s ∧ 0 ≤ K ∧
      ∀ t ∈ Ico c s, ∀ y ∈ U, ∀ v : TangentSpace ThreeModel y,
        Real.exp (-(18 * K * (s - c))) * (G.flow.base.metric c).inner y v v ≤
            (G.flow.base.metric t).inner y v v ∧
          (G.flow.base.metric t).inner y v v ≤
            Real.exp (18 * K * (s - c)) * (G.flow.base.metric c).inner y v v := by
  obtain ⟨U, hU, hxU, c, hc, K, hK, hcurv⟩ := hx
  exact ⟨U, c, K, hU, hxU, hc, hK, G.metric_inner_bounds_on_tail hc hK U hcurv⟩

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.OrientedThreeStage
