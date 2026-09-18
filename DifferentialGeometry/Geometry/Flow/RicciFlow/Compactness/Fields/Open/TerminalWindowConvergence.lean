import DifferentialGeometry.Geometry.Flow.RicciFlow.Compactness.Fields.Open.TerminalWindowExtensions
import DifferentialGeometry.Geometry.Flow.RicciFlow.Compactness.Metric.Bounds.TerminalWindow
import DifferentialGeometry.Geometry.Flow.RicciFlow.Compactness.Bounds.CovariantDerivative.TerminalTimeLipschitz
import DifferentialGeometry.Geometry.Metric.Convergence.Window.EventualBounds
import DifferentialGeometry.Geometry.Flow.RicciFlow.Compactness.Fields.Open.HalfLineConvergence

noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn

open Set Filter
open DifferentialGeometry.Geometry.Curvature DifferentialGeometry.CheegerGromovCompactness
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
open scoped Manifold ContDiff _root_.Topology

universe u

attribute [local instance] PointedFlowData.topology PointedFlowData.charted
  PointedFlowData.smooth PointedFlowData.t2 PointedFlowData.sigmaCompact
  PointedFlowData.t2TangentBundle PointedRiemannianManifold.topology
  PointedRiemannianManifold.charted PointedRiemannianManifold.smooth
  PointedRiemannianManifold.t2 PointedRiemannianManifold.sigmaCompact
  PointedRiemannianManifold.t2TangentBundle

theorem StaticTerminalLimit.exists_bumpMetricConvergence_on_window
    {X : FlowSequence.{u}} {depthBound : ℝ} (L : StaticTerminalLimit X depthBound)
    {width : ℝ} (hw : 0 < width) (hwd : width < depthBound) :
    let Y := L.windowSequence (hw.le.trans hwd.le)
    let Phi := pointedCGHMapsOfManifold Y L.space L.subseq L.maps
    ∃ (bf : BumpFamily Phi) (hsrc : SourceIsSigmaCompact Phi)
      (htgt : TargetIsSigmaCompact Phi) (rho : ℕ → ℕ), StrictMono rho ∧
      ∃ gInf : ℝ → SmoothRiemannianMetric I3 L.space.M,
        BumpMetricConvergence Phi L.space.metric bf hsrc htgt rho gInf (-width) 0 := by
  classical
  let Y := L.windowSequence (hw.le.trans hwd.le)
  let Phi := pointedCGHMapsOfManifold Y L.space L.subseq L.maps
  obtain ⟨bf, hsrc, htgt, hG, hind⟩ := L.exists_metric_extensions_on_window hw hwd
  let G := gSeqExt Phi L.space.metric bf hsrc htgt
  obtain ⟨rho, hrho, gInf, hconv⟩ :=
    exists_metric_subsequence_tendsto_uniformly_on_time_interval_of_eventual_pointwise_lower
      (neg_nonpos.mpr hw.le) L.space.metric G hind
      (L.eventually_metric_time_lipschitz_of_local_pullbacks hw hwd G hG)
      (by
        intro t ht q K hK
        obtain ⟨C, _hC, hbound⟩ := L.eventually_covariant_bounds_of_local_pullbacks
          hw hwd G hG K hK q
        exact ⟨C, hbound.mono fun i hi x hx => hi q le_rfl t ht x hx⟩)
      (by
        intro t ht x
        obtain ⟨c, hc, hbound⟩ := L.eventually_metric_lower_bound_of_local_pullbacks
          hw hwd G hG {x} isCompact_singleton
        exact ⟨c, hc, hbound.mono fun i hi v => hi t ht x (mem_singleton x) v⟩)
  refine ⟨bf, hsrc, htgt, rho, hrho, gInf, hconv, ?_⟩
  intro K hK p epsilon hepsilon
  obtain ⟨N, hN⟩ := hconv K hK p epsilon hepsilon
  exact ⟨N, fun i hi t ht q hq x hx =>
    (derivNorm_le_sup hK hq (G (rho i) t) (gInf t) L.space.metric hx).trans_lt
      (hN i hi t ht)⟩

end DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn
