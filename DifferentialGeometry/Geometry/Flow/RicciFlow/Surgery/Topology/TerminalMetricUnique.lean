import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.EventData
import DifferentialGeometry.Geometry.Metric.TensorInner.Tensor0S.Coordinates.MetricComparison

noncomputable section
open Bundle Manifold Set
open scoped Manifold ContDiff BigOperators

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

universe u

private theorem inner_sub_le_metricDerivNorm
    {M : Type u} [TopologicalSpace M] [ChartedSpace ThreeSpace M]
    [IsManifold ThreeModel ∞ M] [T2Space M] [SigmaCompactSpace M]
    (g h : SmoothRiemannianMetric ThreeModel M) (x : M)
    (v w : TangentSpace ThreeModel x) :
    |g.inner x v w - h.inner x v w| ≤
      CheegerGromovCompactness.metricDerivNorm 0 g h h x *
        (Real.sqrt (h.inner x v v) * Real.sqrt (h.inner x w w)) := by
  have hbound := Tensor0SBundle.abs_apply_le_norm0S (I := ThreeModel) h x 2
    (CheegerGromovCompactness.metricDiffCovDerivAt 0 g h h x) ![v, w]
  have heval : CheegerGromovCompactness.metricDiffCovDerivAt 0 g h h x ![v, w] =
      g.inner x v w - h.inner x v w := by
    change (Tensor0SBundle.metricTensorField g x - Tensor0SBundle.metricTensorField h x)
      ![v, w] = _
    simp only [sub_apply, Tensor0SBundle.metricTensorField_apply,
      Matrix.cons_val_zero, Matrix.cons_val_one]
  rw [heval] at hbound
  simpa only [CheegerGromovCompactness.metricDerivNorm, Fin.prod_univ_two, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.head_cons] using hbound

namespace OrientedThreeStage.IncomingSlab

variable {P : OrientedThreeStage.{u}} {a s : ℝ} (G : P.IncomingSlab a s)

theorem terminalLimitMetric_unique (g h : G.TerminalLimitMetric) : g.metric = h.metric := by
  let : SecondCountableTopology P.Carrier :=
    ChartedSpace.secondCountable_of_sigmaCompact ThreeSpace P.Carrier
  let : LocallyCompactSpace G.terminalRegularOpen :=
    ChartedSpace.locallyCompactSpace ThreeSpace G.terminalRegularOpen
  apply SmoothRiemannianMetric.ext_inner
  intro x v w
  by_contra hne
  let δ := |g.metric.inner x v w - h.metric.inner x v w|
  have hδ : 0 < δ := abs_pos.mpr (sub_ne_zero.mpr hne)
  let Cg := Real.sqrt (g.metric.inner x v v) * Real.sqrt (g.metric.inner x w w)
  let Ch := Real.sqrt (h.metric.inner x v v) * Real.sqrt (h.metric.inner x w w)
  have hCg : 0 ≤ Cg := mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
  have hCh : 0 ≤ Ch := mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
  let εg := δ / (2 * (Cg + 1))
  let εh := δ / (2 * (Ch + 1))
  have heg : 0 < εg := div_pos hδ (by positivity)
  have heh : 0 < εh := div_pos hδ (by positivity)
  obtain ⟨dg, hdg, hbg⟩ := g.converges {x} (isCompact_singleton) 0 εg heg
  obtain ⟨dh, hdh, hbh⟩ := h.converges {x} (isCompact_singleton) 0 εh heh
  obtain ⟨t, hleft, hright⟩ := exists_between (max_lt hdg.2 hdh.2)
  let gt := (G.flow.base.metric t).restrictOpen G.terminalRegularOpen
  have htg := hbg t ⟨(le_max_left dg dh).trans_lt hleft, hright⟩ x (mem_singleton x)
  have hth := hbh t ⟨(le_max_right dg dh).trans_lt hleft, hright⟩ x (mem_singleton x)
  have hg : |gt.inner x v w - g.metric.inner x v w| < δ / 2 := by
    calc
      _ ≤ CheegerGromovCompactness.metricDerivNorm 0 gt g.metric g.metric x * Cg :=
        inner_sub_le_metricDerivNorm gt g.metric x v w
      _ ≤ εg * Cg := mul_le_mul_of_nonneg_right htg.le hCg
      _ < εg * (Cg + 1) := mul_lt_mul_of_pos_left (lt_add_one Cg) heg
      _ = δ / 2 := by dsimp [εg]; field_simp
  have hh : |gt.inner x v w - h.metric.inner x v w| < δ / 2 := by
    calc
      _ ≤ CheegerGromovCompactness.metricDerivNorm 0 gt h.metric h.metric x * Ch :=
        inner_sub_le_metricDerivNorm gt h.metric x v w
      _ ≤ εh * Ch := mul_le_mul_of_nonneg_right hth.le hCh
      _ < εh * (Ch + 1) := mul_lt_mul_of_pos_left (lt_add_one Ch) heh
      _ = δ / 2 := by dsimp [εh]; field_simp
  have htriangle : δ ≤ |gt.inner x v w - g.metric.inner x v w| +
      |gt.inner x v w - h.metric.inner x v w| := by
    dsimp [δ]
    calc
      _ ≤ |g.metric.inner x v w - gt.inner x v w| +
          |gt.inner x v w - h.metric.inner x v w| := abs_sub_le _ _ _
      _ = _ := by rw [abs_sub_comm (g.metric.inner x v w) (gt.inner x v w)]
  linarith

end OrientedThreeStage.IncomingSlab

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
