import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.History
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.ChildParent
import DifferentialGeometry.Geometry.Flow.RicciFlow.Compactness.Solutions.OpenRestriction

noncomputable section
open Bundle Manifold Set
open scoped Manifold ContDiff Topology
open DifferentialGeometry
open DifferentialGeometry.PDE.RicciFlow
open DifferentialGeometry.Geometry.Curvature
open Surgery.Topology
namespace DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening
universe u
variable {P : OrientedThreeStage.{u}} {a b : ℝ}

theorem incoming_component_native_solution (G : P.IncomingSlab a b)
    (c : ConnectedComponents P.Carrier) :
    ∃ F : SolutionOn (I := ThreeModel) (M := (P.component c).Carrier)
        (RealTimeInterval.closedOpen a b G.lt),
      DifferentialGeometry.PDE.RicciFlow.IsSolutionOn F ∧
      (∀ t ∈ Ico a b, F.base.metric t = P.componentMetric (G.flow.base.metric t) c) ∧
      (∀ t ∈ Ico a b, ∀ x : (P.component c).Carrier,
        F.base.scalar t x = G.flow.base.scalar t x.1) := by
  let : CompactSpace (P.componentOpen c) := P.component_compact c
  let : T2Space (P.componentOpen c) := (P.component c).hausdorff
  let : IsManifold ThreeModel ∞ (P.componentOpen c) := (P.component c).smooth
  let : SigmaCompactSpace (P.componentOpen c) := inferInstance
  let F : SolutionOn (I := ThreeModel) (M := (P.component c).Carrier)
      (RealTimeInterval.closedOpen a b G.lt) :=
    CheegerGromovCompactness.solutionOnRestrictOpen (I := ThreeModel) (M := P.Carrier)
      (D := RealTimeInterval.closedOpen a b G.lt) G.flow (P.componentOpen c)
  have hF : DifferentialGeometry.PDE.RicciFlow.IsSolutionOn F :=
    CheegerGromovCompactness.isSolutionOn_restrictOpen (I := ThreeModel) (M := P.Carrier)
      (D := RealTimeInterval.closedOpen a b G.lt) G.flow G.equation (P.componentOpen c)
  refine ⟨F, hF, ?_, ?_⟩
  · intro t _
    rfl
  · intro t _ x
    dsimp only [F, CheegerGromovCompactness.solutionOnRestrictOpen, SolutionFamily.scalar]
    exact CheegerGromovCompactness.metricScalarAt_restrictOpen
      (I := ThreeModel) (M := P.Carrier) (G.flow.base.metric t) (P.componentOpen c) x

end DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening
