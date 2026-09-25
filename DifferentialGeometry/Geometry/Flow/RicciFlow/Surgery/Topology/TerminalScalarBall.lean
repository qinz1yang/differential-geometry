import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.TerminalScalarSublevel
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.LocalPropagation
import DifferentialGeometry.Geometry.Metric.Convergence.Metric.DistanceUpper
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.TerminalCanonicalCapture
import DifferentialGeometry.Geometry.Metric.BilinearPerturbation
import DifferentialGeometry.Geometry.Comparison.Distance.Continuity

noncomputable section

open Filter Set Bundle Manifold
open DifferentialGeometry.CheegerGromovCompactness
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood
open DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn (CanonicalWitness)
open scoped Manifold ContDiff Topology ENNReal NNReal

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.OrientedThreeStage.IncomingSlab

universe u

variable {P : OrientedThreeStage.{u}} {a s : ℝ} {G : P.IncomingSlab a s}

theorem TerminalLimitMetric.eventually_riemannianEDistOf_lt
    (L : G.TerminalLimitMetric) (x y : G.terminalRegularOpen) {R : ℝ}
    (hxy : riemannianEDistOf L.metric x y < ENNReal.ofReal R) :
    ∀ᶠ t in 𝓝[<] s, riemannianEDistOf (G.flow.base.metric t)
      (x : P.Carrier) (y : P.Carrier) < ENNReal.ofReal R := by
  have hupper : ∀ K : Set G.terminalRegularOpen, IsCompact K → ∀ B : ℝ, 1 < B →
      ∀ᶠ t in 𝓝[<] s, ∀ z ∈ K, ∀ v : TangentSpace ThreeModel z,
        ((G.flow.base.metric t).restrictOpen G.terminalRegularOpen).inner z v v ≤
          B ^ 2 * L.metric.inner z v v := by
    intro K hK B hB
    obtain ⟨d, hd, hb⟩ := L.converges K hK 0 (B ^ 2 - 1) (by nlinarith)
    filter_upwards [Ioo_mem_nhdsLT hd.2] with t ht
    intro z hz v
    have hbound := (Geometry.Metric.inner_bounds_of_metricDerivNorm_le L.metric
      ((G.flow.base.metric t).restrictOpen G.terminalRegularOpen) z (hb t ht z hz).le v).2
    convert hbound using 1; ring
  have h := Geometry.Riemannian.eventually_riemannianEDistOf_lt_of_compact_metric_upper
    L.metric (fun t => (G.flow.base.metric t).restrictOpen G.terminalRegularOpen)
    hupper x y hxy
  filter_upwards [h] with t ht
  exact (riemannianEDistOf_le_restrictOpen (G.flow.base.metric t)
    G.terminalRegularOpen x y).trans_lt ht


theorem TerminalLimitMetric.scalar_le_on_small_ball_of_gradient_bound_on_time_window
    {P : OrientedThreeStage.{u}} {a s c : ℝ} {G : P.IncomingSlab a s}
    (L : G.TerminalLimitMetric) {q Q : ℝ} (C : ℝ≥0)
    (hQ : 0 < Q) (hqQ : q ≤ Q) (hcs : c < s)
    (hgradient : ∀ x : P.Carrier, ∀ t ∈ Ioo a s, c ≤ t → q < G.flow.scalar t x →
      ∀ v : TangentSpace ThreeModel x,
        |scalarDifferential G.flow t x v| ≤ C * G.flow.scalar t x *
          Real.sqrt (G.flow.scalar t x) * Real.sqrt ((G.flow.base.metric t).inner x v v))
    (x : G.terminalRegularOpen) (hx : metricScalarAt L.metric x ≤ Q)
    (y : G.terminalRegularOpen)
    (hy : y ∈ riemannianClosedBallOf L.metric x
      (localPropagationRadius C / (2 * Real.sqrt (2 * Q)))) :
    metricScalarAt L.metric y ≤ 6 * Q := by
  have htwoQ : 0 < 2 * Q := by positivity
  have hrad : 0 < localPropagationRadius C / Real.sqrt (2 * Q) :=
    div_pos (localPropagationRadius_pos C.coe_nonneg) (Real.sqrt_pos.mpr htwoQ)
  have hdist : riemannianEDistOf L.metric x y <
      ENNReal.ofReal (localPropagationRadius C / Real.sqrt (2 * Q)) := by
    apply hy.trans_lt
    apply (ENNReal.ofReal_lt_ofReal_iff hrad).mpr
    have heq : localPropagationRadius C / (2 * Real.sqrt (2 * Q)) =
        (localPropagationRadius C / Real.sqrt (2 * Q)) / 2 := by ring
    rw [heq]
    exact half_lt_self hrad
  have hbase : ∀ᶠ t in 𝓝[<] s, G.flow.scalar t x.val < 2 * Q :=
    (L.tendsto_metricScalarAt x).eventually_lt_const (by linarith)
  apply le_of_tendsto (L.tendsto_metricScalarAt y)
  filter_upwards [Ioo_mem_nhdsLT G.lt, Ioo_mem_nhdsLT hcs, hbase, L.eventually_riemannianEDistOf_lt x y hdist] with t ht hct hb hd
  have hgrad (w : P.Carrier) (hw : 2 * (2 * Q) ≤ G.flow.scalar t w)
      (v : TangentSpace ThreeModel w) :
      |scalarDifferential G.flow t w v| ≤
        2 * C * (G.flow.scalar t w * Real.sqrt (G.flow.scalar t w)) *
          Real.sqrt ((G.flow.base.metric t).inner w v v) := by
    have hhigh : q < G.flow.scalar t w := by linarith
    have hpos : 0 ≤ G.flow.scalar t w := by linarith
    have hbound := hgradient w t ht hct.1.le hhigh v
    have hterm : 0 ≤ (C : ℝ) * G.flow.scalar t w * Real.sqrt (G.flow.scalar t w) *
        Real.sqrt ((G.flow.base.metric t).inner w v v) := by positivity
    nlinarith
  have hh := scalar_le_on_ball_of_gradient_bound G.flow C.coe_nonneg htwoQ hgrad hb.le hd.le
  change G.flow.scalar t y.val ≤ 6 * Q
  simpa only [show (3 : ℝ) * (2 * Q) = 6 * Q by ring] using hh


theorem TerminalLimitMetric.isCompact_small_ball_of_gradient_bound_on_time_window
    {P : OrientedThreeStage.{u}} {a s c : ℝ} {G : P.IncomingSlab a s}
    (L : G.TerminalLimitMetric) {q Q : ℝ} (C : ℝ≥0)
    (hQ : 0 < Q) (hqQ : q ≤ Q) (hcs : c < s)
    (hgradient : ∀ x : P.Carrier, ∀ t ∈ Ioo a s, c ≤ t → q < G.flow.scalar t x →
      ∀ v : TangentSpace ThreeModel x,
        |scalarDifferential G.flow t x v| ≤ C * G.flow.scalar t x *
          Real.sqrt (G.flow.scalar t x) * Real.sqrt ((G.flow.base.metric t).inner x v v))
    (x : G.terminalRegularOpen) (hx : metricScalarAt L.metric x ≤ Q) :
    IsCompact (riemannianClosedBallOf L.metric x
      (localPropagationRadius C / (2 * Real.sqrt (2 * Q)))) := by
  apply (L.isCompact_scalar_sublevel (6 * Q)).of_isClosed_subset
  · exact isClosed_le (by
      unfold riemannianEDistOf
      exact DifferentialGeometry.Geometry.Riemannian.continuous_riemannianEDist L.metric x)
      continuous_const
  · exact fun y hy => L.scalar_le_on_small_ball_of_gradient_bound_on_time_window C hQ hqQ hcs
      hgradient x hx y hy

theorem TerminalLimitMetric.scalar_le_on_small_ball_of_gradient_bound
    {P : OrientedThreeStage.{u}} {a s : ℝ} {G : P.IncomingSlab a s}
    (L : G.TerminalLimitMetric) {q Q : ℝ} (C : ℝ≥0)
    (hQ : 0 < Q) (hqQ : q ≤ Q)
    (hgradient : ∀ x : P.Carrier, ∀ t ∈ Ioo a s, q < G.flow.scalar t x →
      ∀ v : TangentSpace ThreeModel x,
        |scalarDifferential G.flow t x v| ≤ C * G.flow.scalar t x *
          Real.sqrt (G.flow.scalar t x) * Real.sqrt ((G.flow.base.metric t).inner x v v))
    (x : G.terminalRegularOpen) (hx : metricScalarAt L.metric x ≤ Q)
    (y : G.terminalRegularOpen)
    (hy : y ∈ riemannianClosedBallOf L.metric x
      (localPropagationRadius C / (2 * Real.sqrt (2 * Q)))) :
    metricScalarAt L.metric y ≤ 6 * Q := by
  exact L.scalar_le_on_small_ball_of_gradient_bound_on_time_window C hQ hqQ G.lt
    (fun x t ht _ => hgradient x t ht) x hx y hy

theorem TerminalLimitMetric.isCompact_small_ball_of_scalar_derivative_bounds
    {P : OrientedThreeStage.{u}} {a s : ℝ} {G : P.IncomingSlab a s}
    (L : G.TerminalLimitMetric) {q Q : ℝ} (C D : ℝ≥0)
    (hQ : 0 < Q) (hqQ : q ≤ Q)
    (hgradient : ∀ x : P.Carrier, ∀ t ∈ Ioo a s, q < G.flow.scalar t x →
      ∀ v : TangentSpace ThreeModel x,
        |scalarDifferential G.flow t x v| ≤ C * G.flow.scalar t x *
          Real.sqrt (G.flow.scalar t x) * Real.sqrt ((G.flow.base.metric t).inner x v v))
    (htime : ∀ x : P.Carrier, ∀ t ∈ Ioo a s, q < G.flow.scalar t x →
      |derivWithin (fun v => G.flow.scalar v x) (Iic t) t| ≤ D * G.flow.scalar t x ^ 2)
    (x : G.terminalRegularOpen) (hx : metricScalarAt L.metric x ≤ Q) :
    IsCompact (riemannianClosedBallOf L.metric x
      (localPropagationRadius C / (2 * Real.sqrt (2 * Q)))) := by
  have hderiv : ∀ y : P.Carrier, ∀ t ∈ Ioo a s, Q < G.flow.scalar t y →
      |derivWithin (fun v => G.flow.scalar v y) (Iic t) t| ≤ D * G.flow.scalar t y ^ 2 := by
    intro y t ht hy
    exact htime y t ht (hqQ.trans_lt hy)
  obtain ⟨Phi, hPhi, hpinch⟩ :=
    Perelman.exists_admissiblePinchingFunction_phiAlmostNonnegative_closedOpen
      G.lt G.flow G.equation (by simp [ThreeSpace])
  apply (L.isCompact_scalar_sublevel_of_time_derivative_bound
    hQ hderiv hPhi hpinch (6 * Q)).of_isClosed_subset
  · exact isClosed_le (by
      unfold riemannianEDistOf
      exact DifferentialGeometry.Geometry.Riemannian.continuous_riemannianEDist L.metric x)
      continuous_const
  · exact fun y hy => L.scalar_le_on_small_ball_of_gradient_bound C hQ hqQ hgradient x hx y hy

theorem TerminalLimitMetric.scalar_le_on_small_ball_of_canonical
    {P : OrientedThreeStage.{u}} {a s : ℝ} {G : P.IncomingSlab a s}
    (L : G.TerminalLimitMetric) {eps C1 q Q : ℝ} (C : ℝ≥0)
    (hQ : 0 < Q) (hqQ : q ≤ Q)
    (hcanonical : ∀ x : P.Carrier, ∀ t ∈ Ioo a s, q < G.flow.scalar t x →
      Nonempty (CanonicalWitness G.flow eps C1 C x t))
    (x : G.terminalRegularOpen) (hx : metricScalarAt L.metric x ≤ Q)
    (y : G.terminalRegularOpen)
    (hy : y ∈ riemannianClosedBallOf L.metric x
      (localPropagationRadius C / (2 * Real.sqrt (2 * Q)))) :
    metricScalarAt L.metric y ≤ 6 * Q := by
  exact L.scalar_le_on_small_ball_of_gradient_bound C hQ hqQ
    (fun z t ht hz v => (hcanonical z t ht hz).some.gradient v) x hx y hy


theorem TerminalLimitMetric.isCompact_small_ball_of_canonical
    {P : OrientedThreeStage.{u}} {a s : ℝ} {G : P.IncomingSlab a s}
    (L : G.TerminalLimitMetric) {eps C1 q Q : ℝ} (C : ℝ≥0)
    (hQ : 0 < Q) (hqQ : q ≤ Q)
    (hcanonical : ∀ x : P.Carrier, ∀ t ∈ Ioo a s, q < G.flow.scalar t x →
      Nonempty (CanonicalWitness G.flow eps C1 C x t))
    (x : G.terminalRegularOpen) (hx : metricScalarAt L.metric x ≤ Q) :
    IsCompact (riemannianClosedBallOf L.metric x
      (localPropagationRadius C / (2 * Real.sqrt (2 * Q)))) := by
  exact L.isCompact_small_ball_of_scalar_derivative_bounds C C hQ hqQ
    (fun z t ht hz v => (hcanonical z t ht hz).some.gradient v)
    (fun z t ht hz => (hcanonical z t ht hz).some.time_derivative) x hx

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.OrientedThreeStage.IncomingSlab
