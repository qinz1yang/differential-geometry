import DifferentialGeometry.Geometry.Metric.DerivativeScaleENorm
import DifferentialGeometry.Geometry.Metric.Convergence.Scaling
import DifferentialGeometry.Geometry.Metric.Convergence.CovariantDerivative.Norm.ReferenceChange


noncomputable section

namespace DifferentialGeometry.CheegerGromovCompactness

open Filter Set
open DifferentialGeometry.Geometry.Metric
open scoped Manifold ContDiff Topology

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M]

private local instance metricScaleComplete : CompleteSpace E :=
  FiniteDimensional.complete ℝ E

private theorem metricCPConvergenceOn_scaleMetric_of_tendsto_one
    {gSeq : ℕ → SmoothRiemannianMetric I M} {gInf : SmoothRiemannianMetric I M}
    {K : Set M} {p : ℕ} (hconv : MetricCPConvergenceOn K p gSeq gInf gInf)
    (hK : IsCompact K)
    {c : ℕ → ℝ} (hc : ∀ k, 0 < c k) (hscale : Tendsto c atTop (𝓝 1)) :
    MetricCPConvergenceOn K p (fun k => scaleMetric (c k) (hc k) (gSeq k))
      gInf gInf := by
  intro ε hε
  have hhalf : 0 < ε / 2 := half_pos hε
  have hweight : Tendsto
      (fun k => c k * (ε / 2) +
        |c k - 1| * Real.sqrt (Module.finrank ℝ E : ℝ)) atTop (𝓝 (ε / 2)) := by
    simpa only [one_mul, sub_self, abs_zero, zero_mul, add_zero] using
      (hscale.mul_const (ε / 2)).add
        ((hscale.sub_const 1).abs.mul_const (Real.sqrt (Module.finrank ℝ E : ℝ)))
  obtain ⟨Nc, hNc⟩ := eventually_atTop.mp
    (hweight.eventually (gt_mem_nhds (show ε / 2 < ε by linarith)))
  obtain ⟨Ng, hNg⟩ := hconv (ε / 2) hhalf
  refine ⟨max Nc Ng, fun k hk => ?_⟩
  have hg : metricDerivENormSupOn K p (gSeq k) gInf gInf < ENNReal.ofReal (ε / 2) := by
    rw [metricDerivENormSupOn_eq_ofReal_of_isCompact hK]
    exact (ENNReal.ofReal_lt_ofReal_iff hhalf).mpr (hNg k ((le_max_right _ _).trans hk))
  have hscaled := metricDerivENormSupOn_scaleMetric_left_lt K p (c k) (hc k)
    (gSeq k) gInf hg
  rw [metricDerivENormSupOn_eq_ofReal_of_isCompact hK] at hscaled
  exact (ENNReal.ofReal_lt_ofReal_iff hε).mp
    (hscaled.trans_le (ENNReal.ofReal_le_ofReal (hNc k ((le_max_left _ _).trans hk)).le))

theorem MetricCPConvergenceOn.scaleMetric_of_tendsto_one
    {gSeq : ℕ → SmoothRiemannianMetric I M}
    {gInf gRef : SmoothRiemannianMetric I M}
    {K : Set M} {p : ℕ} (hconv : MetricCPConvergenceOn K p gSeq gInf gRef)
    (hK : IsCompact K) {c : ℕ → ℝ}
    (hc : ∀ k, 0 < c k) (hscale : Tendsto c atTop (𝓝 1)) :
    MetricCPConvergenceOn K p (fun k => scaleMetric (c k) (hc k) (gSeq k))
      gInf gRef := by
  have hself := hconv.change_reference hK gInf
  exact (metricCPConvergenceOn_scaleMetric_of_tendsto_one hself hK hc hscale).change_reference
    hK gRef

theorem MetricCPConvergenceOn.scaleMetric_of_tendsto
    {gSeq : ℕ → SmoothRiemannianMetric I M}
    {gInf gRef : SmoothRiemannianMetric I M}
    {K : Set M} {p : ℕ} (hconv : MetricCPConvergenceOn K p gSeq gInf gRef)
    (hK : IsCompact K) {cSeq : ℕ → ℝ} {c : ℝ}
    (hcSeq : ∀ k, 0 < cSeq k) (hc : 0 < c) (hscale : Tendsto cSeq atTop (𝓝 c)) :
    MetricCPConvergenceOn K p (fun k => scaleMetric (cSeq k) (hcSeq k) (gSeq k))
      (scaleMetric c hc gInf) (scaleMetric c hc gRef) := by
  have hratio : Tendsto (fun k => cSeq k / c) atTop (𝓝 1) := by
    simpa only [div_self hc.ne'] using hscale.div_const c
  have hnormalized := hconv.scaleMetric_of_tendsto_one hK
    (fun k => div_pos (hcSeq k) hc) hratio
  have hscaled := metricCPConvOn_scale_all c hc hK p
    (fun k => scaleMetric (cSeq k / c) (div_pos (hcSeq k) hc) (gSeq k))
    gInf gRef hnormalized
  have heq (k : ℕ) :
      scaleMetric c hc (scaleMetric (cSeq k / c) (div_pos (hcSeq k) hc) (gSeq k)) =
        scaleMetric (cSeq k) (hcSeq k) (gSeq k) := by
    apply SmoothRiemannianMetric.ext_inner
    intro x v w
    simp only [scaleMetric_inner]
    field_simp
  simpa only [heq] using hscaled

theorem MetricCInfConvergenceOnCompacts.scaleMetric_of_tendsto_one
    {gSeq : ℕ → SmoothRiemannianMetric I M}
    {gInf gRef : SmoothRiemannianMetric I M}
    (hconv : MetricCInfConvergenceOnCompacts gSeq gInf gRef)
    {c : ℕ → ℝ} (hc : ∀ k, 0 < c k) (hscale : Tendsto c atTop (𝓝 1)) :
    MetricCInfConvergenceOnCompacts (fun k => scaleMetric (c k) (hc k) (gSeq k))
      gInf gRef := by
  intro K hK p
  exact (hconv K hK p).scaleMetric_of_tendsto_one hK hc hscale

end DifferentialGeometry.CheegerGromovCompactness
