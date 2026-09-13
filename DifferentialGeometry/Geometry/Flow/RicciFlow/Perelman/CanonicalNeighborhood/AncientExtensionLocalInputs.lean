import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.AncientExtension

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

def HalfLineExtensionSlabCurvatureBound {eps kappa sigma : ℝ} {Phi : ℝ → ℝ}
    {X : NormalizedSequence.{u} eps kappa sigma Phi} {L : TerminalLimit X}
    {J : RealTimeInterval} (B : BackwardExtension L J) : Prop :=
  ∀ g : ℝ → SmoothRiemannianMetric I3 L.space.M, IsHalfLineExtension B g →
    ∀ a b : ℝ, a ≤ b → Set.Icc a b ⊆ ancientTimeInterval.carrier →
      ∃ C : ℝ, ∀ t ∈ Set.Icc a b, ∀ x : L.space.M,
        FlowMetricBall.rmNormSq ({ base := { metric := g } } :
          SolutionOn (I := I3) (M := L.space.M) ancientTimeInterval) t x ≤ C

def HalfLineSlabAnalyticInputs {eps kappa sigma : ℝ} {Phi : ℝ → ℝ}
    {X : NormalizedSequence.{u} eps kappa sigma Phi} {L : TerminalLimit X}
    {J : RealTimeInterval} (B : BackwardExtension L J) : Prop :=
  HalfLineExtensionExists B ∧ HalfLineExtensionSliceGeometry B ∧
    HalfLineExtensionSlabCurvatureBound B ∧ HalfLineExtensionAncient B

theorem halfLineSlabAnalyticInputs_of_halfLineAnalyticInputs
    {eps kappa sigma : ℝ} {Phi : ℝ → ℝ}
    {X : NormalizedSequence.{u} eps kappa sigma Phi} {L : TerminalLimit X}
    {J : RealTimeInterval} {B : BackwardExtension L J} (h : HalfLineAnalyticInputs B) :
    HalfLineSlabAnalyticInputs B := by
  obtain ⟨hex, hgeom, hrm, hanc⟩ := h
  refine ⟨hex, hgeom, ?_, hanc⟩
  intro g hg a b hab hsub
  obtain ⟨C, hC⟩ := hrm g hg
  exact ⟨C, fun t ht x => hC t (hsub ht) x⟩

theorem ancientExtension_nonempty_of_halfLineSlabAnalyticInputs
    {eps kappa sigma : ℝ} {Phi : ℝ → ℝ}
    {X : NormalizedSequence.{u} eps kappa sigma Phi} {L : TerminalLimit X}
    {J : RealTimeInterval} (B : BackwardExtension L J)
    (h : HalfLineSlabAnalyticInputs B) :
    Nonempty (AncientExtension B) := by
  obtain ⟨⟨g, hg0, hagree, diagonal, hdiag, hconv⟩, hgeom, hrm, hanc⟩ := h
  have hlim : IsHalfLineExtension B g := ⟨hg0, hagree, diagonal, hdiag, hconv⟩
  obtain ⟨hsol, hanc1⟩ := hanc g hlim
  have hanc2 : PointedFlowScalarAtBase
      (flowOfMetric ancientTimeInterval L.space g hsol) 1 :=
    pointedFlowScalarAtBase_flowOfMetric hlim.1 hsol
  obtain ⟨Cr, _hCrs, hCr⟩ :=
    DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.ancientKappa_rmNormSqBounded
      (I := I3) (flowOfMetric ancientTimeInterval L.space g hsol) (by simp [ThreeSpace]) hanc1
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
                compact_time_bound := fun a b hab hsub => hrm g hlim a b hab hsub }
            agrees := hagree
            diagonal := diagonal
            strictMono := hdiag
            maps_agree := rfl
            ancient := hanc1
            normalized := hanc2
            global_rm := ⟨(Real.sqrt 3 * Cr) ^ 2, fun t ht x => hCr t ht x⟩ }⟩

end DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn
