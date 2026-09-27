import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.BlowupConvergence
import DifferentialGeometry.Geometry.Flow.RicciFlow.Compactness.Limits.FlowOfMetric

set_option autoImplicit false
noncomputable section
open scoped Topology

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn

open DifferentialGeometry.Geometry.Curvature DifferentialGeometry.CheegerGromovCompactness
open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
open scoped _root_.Manifold ContDiff ENNReal

universe u

attribute [local instance] PointedFlowData.topology PointedFlowData.charted
  PointedFlowData.smooth PointedFlowData.t2 PointedFlowData.sigmaCompact
  PointedFlowData.t2TangentBundle PointedRiemannianManifold.topology
  PointedRiemannianManifold.charted PointedRiemannianManifold.smooth
  PointedRiemannianManifold.t2 PointedRiemannianManifold.sigmaCompact
  PointedRiemannianManifold.t2TangentBundle

variable {M : Type u} [TopologicalSpace M] [ChartedSpace ThreeSpace M]
  [IsManifold I3 ∞ M] [T2Space M] [SigmaCompactSpace M]
  {D : RealTimeInterval}


def BackwardExtension.pointed {eps kappa sigma : ℝ} {Phi : ℝ → ℝ}
    {X : NormalizedSequence.{u} eps kappa sigma Phi} {L : TerminalLimit X}
    {J : RealTimeInterval} (B : BackwardExtension L J) : PointedFlowData.{u, 0, 0} I3 J where
  M := L.space.M
  topology := L.space.topology
  charted := L.space.charted
  smooth := L.space.smooth
  sigmaCompact := L.space.sigmaCompact
  t2 := L.space.t2
  t2TangentBundle := L.space.t2TangentBundle
  basepoint := L.space.basepoint
  S := B.solution
  isSolution := B.isSolution

structure AncientExtension {eps kappa sigma : ℝ} {Phi : ℝ → ℝ}
    {X : NormalizedSequence.{u} eps kappa sigma Phi} {L : TerminalLimit X}
    {J : RealTimeInterval} (B : BackwardExtension L J) where
  extension : BackwardExtension L ancientTimeInterval
  agrees : ∀ s ∈ J.carrier, extension.solution.base.metric s = B.solution.base.metric s
  diagonal : ℕ → ℕ
  strictMono : StrictMono diagonal
  maps_agree : extension.subseq = B.subseq ∘ diagonal
  ancient : IsAncientKappaSolution kappa extension.pointed
  normalized : PointedFlowScalarAtBase extension.pointed 1
  global_rm : ∃ C : ℝ, PointedFlowRmNormSqBounded extension.pointed C

def IsHalfLineExtension {eps kappa sigma : ℝ} {Phi : ℝ → ℝ}
    {X : NormalizedSequence.{u} eps kappa sigma Phi} {L : TerminalLimit X}
    {J : RealTimeInterval} (B : BackwardExtension L J)
    (g : ℝ → SmoothRiemannianMetric I3 L.space.M) : Prop :=
  g 0 = L.space.metric ∧
    (∀ s ∈ J.carrier, g s = B.solution.base.metric s) ∧
    ∃ diagonal : ℕ → ℕ, ∃ hdiag : StrictMono diagonal,
      ConvergesOn (subsequenceMaps L.maps (B.subseq ∘ diagonal)
        (B.strictMono.comp hdiag))
        ({ base := { metric := g } } :
          SolutionOn (I := I3) (M := L.space.M) ancientTimeInterval)

def HalfLineExtensionExists {eps kappa sigma : ℝ} {Phi : ℝ → ℝ}
    {X : NormalizedSequence.{u} eps kappa sigma Phi} {L : TerminalLimit X}
    {J : RealTimeInterval} (B : BackwardExtension L J) : Prop :=
  ∃ g : ℝ → SmoothRiemannianMetric I3 L.space.M, IsHalfLineExtension B g

def HalfLineExtensionIsFlow {eps kappa sigma : ℝ} {Phi : ℝ → ℝ}
    {X : NormalizedSequence.{u} eps kappa sigma Phi} {L : TerminalLimit X}
    {J : RealTimeInterval} (B : BackwardExtension L J) : Prop :=
  ∀ g : ℝ → SmoothRiemannianMetric I3 L.space.M, IsHalfLineExtension B g →
    IsSolutionOn ({ base := { metric := g } } :
      SolutionOn (I := I3) (M := L.space.M) ancientTimeInterval)

def HalfLineExtensionSliceGeometry {eps kappa sigma : ℝ} {Phi : ℝ → ℝ}
    {X : NormalizedSequence.{u} eps kappa sigma Phi} {L : TerminalLimit X}
    {J : RealTimeInterval} (B : BackwardExtension L J) : Prop :=
  ∀ g : ℝ → SmoothRiemannianMetric I3 L.space.M, IsHalfLineExtension B g →
    (∀ t ∈ ancientTimeInterval.carrier,
      MetricComplete ({ L.space with metric := g t } : PointedRiemannianManifold.{u, 0, 0} I3)) ∧
    ∀ t ∈ ancientTimeInterval.carrier, SecLower (g t) 0 Set.univ

def HalfLineExtensionCurvatureBound {eps kappa sigma : ℝ} {Phi : ℝ → ℝ}
    {X : NormalizedSequence.{u} eps kappa sigma Phi} {L : TerminalLimit X}
    {J : RealTimeInterval} (B : BackwardExtension L J) : Prop :=
  ∀ g : ℝ → SmoothRiemannianMetric I3 L.space.M, IsHalfLineExtension B g →
    ∃ C : ℝ, ∀ t ∈ ancientTimeInterval.carrier, ∀ x : L.space.M,
      FlowMetricBall.rmNormSq ({ base := { metric := g } } :
        SolutionOn (I := I3) (M := L.space.M) ancientTimeInterval) t x ≤ C

def HalfLineExtensionAncient {eps kappa sigma : ℝ} {Phi : ℝ → ℝ}
    {X : NormalizedSequence.{u} eps kappa sigma Phi} {L : TerminalLimit X}
    {J : RealTimeInterval} (B : BackwardExtension L J) : Prop :=
  ∀ g : ℝ → SmoothRiemannianMetric I3 L.space.M, IsHalfLineExtension B g →
    ∃ hsol : IsSolutionOn ({ base := { metric := g } } :
        SolutionOn (I := I3) (M := L.space.M) ancientTimeInterval),
      IsAncientKappaSolution kappa (flowOfMetric ancientTimeInterval L.space g hsol)

theorem halfLineExtensionIsFlow_of_ancient {eps kappa sigma : ℝ} {Phi : ℝ → ℝ}
    {X : NormalizedSequence.{u} eps kappa sigma Phi} {L : TerminalLimit X}
    {J : RealTimeInterval} {B : BackwardExtension L J} (h : HalfLineExtensionAncient B) :
    HalfLineExtensionIsFlow B :=
  fun g hg => (h g hg).1

theorem pointedFlowScalarAtBase_flowOfMetric {eps kappa sigma : ℝ} {Phi : ℝ → ℝ}
    {X : NormalizedSequence.{u} eps kappa sigma Phi} {L : TerminalLimit X}
    {g : ℝ → SmoothRiemannianMetric I3 L.space.M} (hg : g 0 = L.space.metric)
    (hsol : IsSolutionOn ({ base := { metric := g } } :
      SolutionOn (I := I3) (M := L.space.M) ancientTimeInterval)) :
    PointedFlowScalarAtBase (flowOfMetric ancientTimeInterval L.space g hsol) 1 := by
  change (flowOfMetric ancientTimeInterval L.space g hsol).S.scalar 0
    (flowOfMetric ancientTimeInterval L.space g hsol).basepoint = 1
  change metricScalarAt ((flowOfMetric ancientTimeInterval L.space g hsol).S.base.metric 0)
    (flowOfMetric ancientTimeInterval L.space g hsol).basepoint = 1
  rw [show (flowOfMetric ancientTimeInterval L.space g hsol).S.base.metric 0 = g 0 from rfl,
    show (flowOfMetric ancientTimeInterval L.space g hsol).basepoint = L.space.basepoint from rfl,
    hg]
  exact L.scalar_one


def HalfLineAnalyticInputs {eps kappa sigma : ℝ} {Phi : ℝ → ℝ}
    {X : NormalizedSequence.{u} eps kappa sigma Phi} {L : TerminalLimit X}
    {J : RealTimeInterval} (B : BackwardExtension L J) : Prop :=
  HalfLineExtensionExists B ∧ HalfLineExtensionSliceGeometry B ∧
    HalfLineExtensionCurvatureBound B ∧ HalfLineExtensionAncient B

theorem ancientExtension_of_halfLine {eps kappa sigma : ℝ} {Phi : ℝ → ℝ}
    {X : NormalizedSequence.{u} eps kappa sigma Phi} {L : TerminalLimit X}
    {J : RealTimeInterval} (B : BackwardExtension L J)
    (h : HalfLineAnalyticInputs B) :
    Nonempty (AncientExtension B) := by
  obtain ⟨⟨g, hg0, hagree, diagonal, hdiag, hconv⟩, hgeom, hrm, hanc⟩ := h
  have hlim : IsHalfLineExtension B g := ⟨hg0, hagree, diagonal, hdiag, hconv⟩
  obtain ⟨hsol, hanc1⟩ := hanc g hlim
  have hanc2 : PointedFlowScalarAtBase
      (flowOfMetric ancientTimeInterval L.space g hsol) 1 :=
    pointedFlowScalarAtBase_flowOfMetric hlim.1 hsol
  obtain ⟨Cr, hCr⟩ := hrm g hlim
  refine ⟨{ extension :=
              { solution := ({ base := { metric := g } } :
                  SolutionOn (I := I3) (M := L.space.M) ancientTimeInterval)
                isSolution := hsol
                terminal := hg0
                subseq := B.subseq ∘ diagonal
                strictMono := B.strictMono.comp hdiag
                convergence := hconv
                complete := fun t ht => (hgeom g hlim).1 t ht
                nonnegative := fun t ht => (hgeom g hlim).2 t ht
                compact_time_bound := fun a b hab hsub =>
                  ⟨Cr, fun t ht x => hCr t (hsub ht) x⟩ }
            agrees := hagree
            diagonal := diagonal
            strictMono := hdiag
            maps_agree := rfl
            ancient := hanc1
            normalized := hanc2
            global_rm := ⟨Cr, fun t ht x => hCr t ht x⟩ }⟩

end DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn
