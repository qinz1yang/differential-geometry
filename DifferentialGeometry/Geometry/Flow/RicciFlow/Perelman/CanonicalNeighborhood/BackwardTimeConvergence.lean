import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.BlowupConvergence
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.SlabRicciCoefficientLimit
import DifferentialGeometry.Geometry.Compactness.CheegerGromov.Pointed.Convergence.Inner

set_option autoImplicit false
noncomputable section
open scoped Topology
namespace DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn
open Filter Set
open DifferentialGeometry.Geometry.Curvature DifferentialGeometry.CheegerGromovCompactness
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
open scoped _root_.Manifold ContDiff ENNReal
universe u
attribute [local instance] PointedFlowData.topology PointedFlowData.charted
  PointedFlowData.smooth PointedFlowData.t2 PointedFlowData.sigmaCompact
  PointedFlowData.t2TangentBundle PointedRiemannianManifold.topology
  PointedRiemannianManifold.charted PointedRiemannianManifold.smooth
  PointedRiemannianManifold.t2 PointedRiemannianManifold.sigmaCompact
  PointedRiemannianManifold.t2TangentBundle

def FlowSequence.timeShift (X : FlowSequence.{u}) (s : ℝ) : FlowSequence.{u} where
  interval i := (X.interval i).timeShift s
  term i := {
    M := (X.term i).M
    topology := (X.term i).topology
    charted := (X.term i).charted
    smooth := (X.term i).smooth
    sigmaCompact := (X.term i).sigmaCompact
    t2 := (X.term i).t2
    t2TangentBundle := (X.term i).t2TangentBundle
    basepoint := (X.term i).basepoint
    S := (X.term i).S.timeShift s
    isSolution := isSolutionOn_timeShift (X.term i).isSolution s }

theorem FlowSequence.timeShift_atTime (X : FlowSequence.{u}) (s t : ℝ) :
    (X.timeShift s).atTime t = X.atTime (t + s) := rfl


end DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn

end

set_option autoImplicit false
noncomputable section
open scoped Topology
namespace DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn
open Filter Set
open DifferentialGeometry.Geometry.Curvature DifferentialGeometry.CheegerGromovCompactness
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
open scoped _root_.Manifold ContDiff ENNReal
universe u
attribute [local instance] PointedFlowData.topology PointedFlowData.charted
  PointedFlowData.smooth PointedFlowData.t2 PointedFlowData.sigmaCompact
  PointedFlowData.t2TangentBundle PointedRiemannianManifold.topology
  PointedRiemannianManifold.charted PointedRiemannianManifold.smooth
  PointedRiemannianManifold.t2 PointedRiemannianManifold.sigmaCompact
  PointedRiemannianManifold.t2TangentBundle

theorem ConvergesOn.tendsto_metric_inner
    {X : FlowSequence.{u}} {P : PointedRiemannianManifold.{u, 0, 0} I3} {f : ℕ → ℕ}
    {F : PointedRiemannianConvergenceMaps (X.atTime 0) P f}
    {D : RealTimeInterval} {S : SolutionOn (I := I3) (M := P.M) D}
    (hconv : ConvergesOn F S) {t : ℝ} (ht : t ∈ D.carrier)
    (x : P.M) (v w : TangentSpace I3 x) :
    Tendsto (fun i => ((X.term (f i)).S.base.metric t).inner
      (F.partialDiffeomorph i x) (mfderiv I3 I3 (F.partialDiffeomorph i) x v)
      (mfderiv I3 I3 (F.partialDiffeomorph i) x w))
      atTop (𝓝 ((S.base.metric t).inner x v w)) := by
  obtain ⟨C, hcanonical⟩ := hconv.exists_canonical_metric_convergence ht
  exact pointed_metric_inner_tendsto (Phi := X.sliceMaps F S.base.metric t)
    (fun K hK => by
      have h := C.converges K hK 0
      rwa [show C.domain = _ from funext hcanonical] at h) x v w

theorem ConvergesOn.metric_eq_on_overlap
    {X : FlowSequence.{u}} {P : PointedRiemannianManifold.{u, 0, 0} I3} {f : ℕ → ℕ}
    {F : PointedRiemannianConvergenceMaps (X.atTime 0) P f}
    {D₁ D₂ : RealTimeInterval} {S₁ : SolutionOn (I := I3) (M := P.M) D₁}
    {S₂ : SolutionOn (I := I3) (M := P.M) D₂}
    (h₁ : ConvergesOn F S₁) (h₂ : ConvergesOn F S₂)
    {t : ℝ} (ht₁ : t ∈ D₁.carrier) (ht₂ : t ∈ D₂.carrier) :
    S₁.base.metric t = S₂.base.metric t := by
  apply SmoothRiemannianMetric.ext_inner
  intro x v w
  exact tendsto_nhds_unique (h₁.tendsto_metric_inner ht₁ x v w)
    (h₂.tendsto_metric_inner ht₂ x v w)



end DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn

end
