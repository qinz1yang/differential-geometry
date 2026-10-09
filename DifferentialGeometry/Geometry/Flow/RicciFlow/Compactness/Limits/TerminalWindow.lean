import DifferentialGeometry.Geometry.Flow.RicciFlow.Compactness.Fields.Open.TerminalWindowConvergence
import DifferentialGeometry.Geometry.Compactness.CheegerGromov.Pointed.Convergence.Inner
import DifferentialGeometry.Geometry.Flow.RicciFlow.Compactness.Limits.ClosedInterval
import DifferentialGeometry.Geometry.Flow.RicciFlow.Compactness.Fields.Open.MetricComparison

section

set_option autoImplicit false
noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn

open Set Filter
open DifferentialGeometry.Geometry.Curvature DifferentialGeometry.CheegerGromovCompactness
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
open scoped _root_.Manifold ContDiff _root_.Topology

universe u

attribute [local instance] PointedFlowData.topology PointedFlowData.charted
  PointedFlowData.smooth PointedFlowData.t2 PointedFlowData.sigmaCompact
  PointedFlowData.t2TangentBundle PointedRiemannianManifold.topology
  PointedRiemannianManifold.charted PointedRiemannianManifold.smooth
  PointedRiemannianManifold.t2 PointedRiemannianManifold.sigmaCompact
  PointedRiemannianManifold.t2TangentBundle

theorem StaticTerminalLimit.terminal_metric_eq_of_bumpMetricConvergence
    {X : FlowSequence.{u}} {depthBound : ℝ} (L : StaticTerminalLimit X depthBound)
    {width : ℝ} (hw : 0 < width) (hwd : width < depthBound)
    (bf : BumpFamily (pointedCGHMapsOfManifold
      (L.windowSequence (hw.le.trans hwd.le)) L.space L.subseq L.maps))
    (hsrc : SourceIsSigmaCompact (pointedCGHMapsOfManifold
      (L.windowSequence (hw.le.trans hwd.le)) L.space L.subseq L.maps))
    (htgt : TargetIsSigmaCompact (pointedCGHMapsOfManifold
      (L.windowSequence (hw.le.trans hwd.le)) L.space L.subseq L.maps))
    {rho : ℕ → ℕ} (hrho : StrictMono rho) {g : ℝ → SmoothRiemannianMetric I3 L.space.M}
    (hconv : BumpMetricConvergence (pointedCGHMapsOfManifold
      (L.windowSequence (hw.le.trans hwd.le)) L.space L.subseq L.maps)
      L.space.metric bf hsrc htgt rho g (-width) 0) :
    g 0 = L.space.metric := by
  let Y := L.windowSequence (hw.le.trans hwd.le)
  let Phi := pointedCGHMapsOfManifold Y L.space L.subseq L.maps
  let co : FlowMetricConvergenceData Phi L.space.metric bf hsrc htgt (-width) 0 := {
    φ := rho
    strictMono := hrho
    gInf := g
    convergence := hconv.convergence
    convergencePt := hconv.convergencePt }
  apply gInf_zero_eq Phi L.space.metric bf hsrc htgt (-width) 0 co
    ⟨by linarith, le_rfl⟩ L.space.metric
  intro x v w epsilon hepsilon
  have hconv0 : ∀ K : Set L.space.M, IsCompact K →
      metricSourceConvergesOn (I := I3) L.maps
        (CanonicalMetricCompactness.canonicalSourceData L.maps) K 0 := by
    intro K hK
    have h := L.converges.converges K hK 0
    rwa [show L.converges.domain = CanonicalMetricCompactness.canonicalSourceData L.maps
      from funext L.canonical_domains] at h
  have hh := pointed_metric_inner_tendsto hconv0 x v w
  obtain ⟨N, hN⟩ := Metric.tendsto_atTop.mp hh epsilon hepsilon
  refine ⟨N, ?_⟩
  intro i hi hx
  rw [KappaSolutions.pointed_srcMetric_inner_eq_pullback]
  exact (Real.dist_eq _ _ ▸ hN i hi)

theorem StaticTerminalLimit.isSolutionOn_of_bumpMetricConvergence
    {X : FlowSequence.{u}} {depthBound : ℝ} (L : StaticTerminalLimit X depthBound)
    {width : ℝ} (hw : 0 < width) (hwd : width < depthBound)
    (bf : BumpFamily (pointedCGHMapsOfManifold
      (L.windowSequence (hw.le.trans hwd.le)) L.space L.subseq L.maps))
    (hsrc : SourceIsSigmaCompact (pointedCGHMapsOfManifold
      (L.windowSequence (hw.le.trans hwd.le)) L.space L.subseq L.maps))
    (htgt : TargetIsSigmaCompact (pointedCGHMapsOfManifold
      (L.windowSequence (hw.le.trans hwd.le)) L.space L.subseq L.maps))
    {rho : ℕ → ℕ} (hrho : StrictMono rho) {g : ℝ → SmoothRiemannianMetric I3 L.space.M}
    (hconv : BumpMetricConvergence (pointedCGHMapsOfManifold
      (L.windowSequence (hw.le.trans hwd.le)) L.space L.subseq L.maps)
      L.space.metric bf hsrc htgt rho g (-width) 0) :
    IsSolutionOn (flowOn (N := L.space.M)
      (RealTimeInterval.closed (-width) 0 (by linarith)) g) := by
  let Y := L.windowSequence (hw.le.trans hwd.le)
  let Phi := pointedCGHMapsOfManifold Y L.space L.subseq L.maps
  let co : FlowMetricConvergenceData Phi L.space.metric bf hsrc htgt (-width) 0 := {
    φ := rho
    strictMono := hrho
    gInf := g
    convergence := hconv.convergence
    convergencePt := hconv.convergencePt }
  apply FlowMetricConvergenceData.isSolutionOn_closed_interval (X := Y) (Φ := Phi)
    (co := co) (by linarith)
    (show Set.Icc (-width) 0 ⊆ Y.D.carrier from by
      intro t ht
      exact ⟨by linarith [ht.1], ht.2⟩)
    (show Set.Ioo (-width) 0 ⊆ Y.D.regular from by
      intro t ht
      exact ⟨by linarith [ht.1], ht.2⟩)
  intro K hK p
  apply Filter.Eventually.of_forall
  intro i
  obtain ⟨C, _hC, hbound⟩ := exists_metric_extension_time_lipschitz_constant_on_closed_interval
    Phi L.space.metric bf hsrc htgt (a := -width) (b := 0) (by linarith)
    (fun t ht => ⟨by linarith [ht.1], ht.2⟩)
    (fun t ht => ⟨by linarith [ht.1], ht.2⟩) i K hK p
  exact ⟨C, hbound⟩

end DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn

end

end

section

set_option autoImplicit false
noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn

open Set Filter
open DifferentialGeometry.Geometry.Curvature DifferentialGeometry.CheegerGromovCompactness
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
open scoped _root_.Manifold ContDiff _root_.Topology

universe u

attribute [local instance] PointedFlowData.topology PointedFlowData.charted
  PointedFlowData.smooth PointedFlowData.t2 PointedFlowData.sigmaCompact
  PointedFlowData.t2TangentBundle PointedRiemannianManifold.topology
  PointedRiemannianManifold.charted PointedRiemannianManifold.smooth
  PointedRiemannianManifold.t2 PointedRiemannianManifold.sigmaCompact
  PointedRiemannianManifold.t2TangentBundle

theorem StaticTerminalLimit.slabComparison_of_bumpMetricConvergence
    {X : FlowSequence.{u}} {depthBound : ℝ} (L : StaticTerminalLimit X depthBound)
    {width : ℝ} (hw : 0 < width) (hwd : width < depthBound)
    (bf : BumpFamily (pointedCGHMapsOfManifold
      (L.windowSequence (hw.le.trans hwd.le)) L.space L.subseq L.maps))
    (hsrc : SourceIsSigmaCompact (pointedCGHMapsOfManifold
      (L.windowSequence (hw.le.trans hwd.le)) L.space L.subseq L.maps))
    (htgt : TargetIsSigmaCompact (pointedCGHMapsOfManifold
      (L.windowSequence (hw.le.trans hwd.le)) L.space L.subseq L.maps))
    {rho : ℕ → ℕ} (hrho : StrictMono rho) {g : ℝ → SmoothRiemannianMetric I3 L.space.M}
    (hconv : BumpMetricConvergence (pointedCGHMapsOfManifold
      (L.windowSequence (hw.le.trans hwd.le)) L.space L.subseq L.maps)
      L.space.metric bf hsrc htgt rho g (-width) 0)
    {delta : ℝ} (hd : 0 < delta) (hdw : delta < width) :
    SlabComparison L delta rho g := by
  let Y := L.windowSequence (hw.le.trans hwd.le)
  let Phi := pointedCGHMapsOfManifold Y L.space L.subseq L.maps
  let S := flowOn (N := L.space.M) (RealTimeInterval.closed (-width) 0 (by linarith)) g
  have hS : IsSolutionOn S := L.isSolutionOn_of_bumpMetricConvergence hw hwd
    bf hsrc htgt hrho hconv
  intro K hK a b hab hsub order epsilon hepsilon
  exact BumpMetricConvergence.eventually_metric_comparison Phi L.space.metric bf hsrc htgt
    hrho S hS hconv
    (a := -width) (c := -delta) (b := 0) (by linarith) (by linarith)
    (show Icc (-width) 0 ⊆ Y.D.carrier from by
      intro t ht
      exact ⟨by linarith [ht.1], ht.2⟩)
    (show Ioo (-width) 0 ⊆ Y.D.regular from by
      intro t ht
      exact ⟨by linarith [ht.1], ht.2⟩)
    Subset.rfl Subset.rfl (fun _ ht => ⟨by linarith [ht.1], ht.2⟩)
    hab hsub K hK order epsilon hepsilon

theorem StaticTerminalLimit.exists_slab_solution
    {X : FlowSequence.{u}} {depthBound : ℝ} (L : StaticTerminalLimit X depthBound)
    {delta : ℝ} (hd : 0 < delta) (hdd : delta < depthBound) :
    ∃ g : ℝ → SmoothRiemannianMetric I3 L.space.M,
      IsSlabLimit L delta hd g ∧ IsSolutionOn (flowOn (N := L.space.M)
        (RealTimeInterval.closed (-delta) 0 (by linarith)) g) := by
  let width := (delta + depthBound) / 2
  have hdw : delta < width := by dsimp only [width]; linarith
  have hw : 0 < width := hd.trans hdw
  have hwd : width < depthBound := by dsimp only [width]; linarith
  obtain ⟨bf, hsrc, htgt, rho, hrho, g, hconv⟩ := L.exists_bumpMetricConvergence_on_window hw hwd
  have hzero := L.terminal_metric_eq_of_bumpMetricConvergence hw hwd bf hsrc htgt hrho hconv
  have hflow := L.isSolutionOn_of_bumpMetricConvergence hw hwd bf hsrc htgt hrho hconv
  have hcomp := L.slabComparison_of_bumpMetricConvergence hw hwd bf hsrc htgt hrho hconv hd hdw
  refine ⟨g, isSlabLimit_of_slabComparison L hd hdd.le hrho hzero hcomp, ?_⟩
  apply isSolutionOn_timeRestrict hflow
  · intro t ht
    exact ⟨by linarith [ht.1], ht.2⟩
  · intro t ht
    exact ⟨by linarith [ht.1], ht.2⟩

theorem StaticTerminalLimit.slab_limit_exists
    {X : FlowSequence.{u}} {depthBound : ℝ} (L : StaticTerminalLimit X depthBound)
    {delta : ℝ} (hd : 0 < delta) (hdd : delta < depthBound) :
    SlabLimitExists L delta := by
  obtain ⟨g, ⟨hg0, rho, hrho, hconv⟩, _hflow⟩ := L.exists_slab_solution hd hdd
  refine ⟨g, hg0, rho, hrho, ?_⟩
  intro K hK a b hab hsub order epsilon hepsilon
  exact (hconv K hK a b hab hsub order epsilon hepsilon).mono fun _ hi => hi.2.2

end DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn

end

end
