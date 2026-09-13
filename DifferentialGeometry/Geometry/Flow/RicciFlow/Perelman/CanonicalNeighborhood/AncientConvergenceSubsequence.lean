import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.FlowConvergenceAssembly
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.TerminalBackwardExtension

set_option autoImplicit false
noncomputable section
open scoped Topology

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn

open DifferentialGeometry.Geometry.Curvature DifferentialGeometry.CheegerGromovCompactness
open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
open scoped Manifold ContDiff ENNReal

universe u

attribute [local instance] PointedFlowData.topology PointedFlowData.charted
  PointedFlowData.smooth PointedFlowData.t2 PointedFlowData.sigmaCompact
  PointedFlowData.t2TangentBundle PointedRiemannianManifold.topology
  PointedRiemannianManifold.charted PointedRiemannianManifold.smooth
  PointedRiemannianManifold.t2 PointedRiemannianManifold.sigmaCompact
  PointedRiemannianManifold.t2TangentBundle

theorem convergesOn_subsequence {X : FlowSequence.{u}}
    {P : PointedRiemannianManifold.{u, 0, 0} I3} {f : ℕ → ℕ}
    {F : PointedRiemannianConvergenceMaps (I := I3) (X.atTime 0) P f}
    {D : RealTimeInterval} {S : SolutionOn (I := I3) (M := P.M) D}
    (hconv : ConvergesOn F S) {k : ℕ → ℕ} (hk : StrictMono k) :
    ConvergesOn (subsequenceMaps F k hk) S := by
  intro K hK a b hab hsub order eps heps
  simpa only [subsequenceMaps, Function.comp_apply] using
    hk.tendsto_atTop.eventually (hconv K hK a b hab hsub order eps heps)

theorem slabComparison_subsequence {X : FlowSequence.{u}} {depthBound : ℝ}
    (L : StaticTerminalLimit X depthBound) {delta : ℝ} {k : ℕ → ℕ}
    {g : ℝ → SmoothRiemannianMetric I3 L.space.M}
    (hcomp : SlabComparison L delta k g) {e : ℕ → ℕ} (he : StrictMono e) :
    SlabComparison L delta (k ∘ e) g := by
  intro K hK a b hab hsub order eps heps
  simpa only [Function.comp_apply] using
    he.tendsto_atTop.eventually (hcomp K hK a b hab hsub order eps heps)

theorem isHalfLineExtension_of_eventually_metricComparisonOn_subsequence
    {eps kappa sigma : ℝ} {Phi : ℝ → ℝ}
    {X : NormalizedSequence.{u} eps kappa sigma Phi} {L : TerminalLimit X}
    {J : RealTimeInterval} (B : BackwardExtension L J)
    {g : ℝ → SmoothRiemannianMetric I3 L.space.M} {diagonal : ℕ → ℕ}
    (hdiag : StrictMono diagonal)
    (hg0 : g 0 = L.space.metric)
    (hagree : ∀ s ∈ J.carrier, g s = B.solution.base.metric s)
    (hcomparison : ∀ K : Set L.space.M, IsCompact K → ∀ a b : ℝ, a ≤ b → b ≤ 0 →
      ∀ order : ℕ, ∀ eps : ℝ, 0 < eps → ∀ᶠ i in Filter.atTop,
        Nonempty (MetricComparisonOn (fun s => g s)
          (fun s => (X.term (L.subseq (B.subseq (diagonal i)))).S.base.metric s)
          (L.maps.partialDiffeomorph (B.subseq (diagonal i)))
          K (Set.Icc a b) order eps))
    {e : ℕ → ℕ} (he : StrictMono e) :
    IsHalfLineExtension B g :=
  isHalfLineExtension_of_eventually_metricComparisonOn B (hdiag.comp he) hg0 hagree
    (fun K hK a b hab hb order eps heps =>
      by
        simpa only [Function.comp_apply] using
          he.tendsto_atTop.eventually (hcomparison K hK a b hab hb order eps heps))

end DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn
