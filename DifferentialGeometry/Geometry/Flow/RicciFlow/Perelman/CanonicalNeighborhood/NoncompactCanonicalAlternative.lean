import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.CanonicalCapCollar
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.SpatialNeckLocalTransport

noncomputable section

open Set
open scoped Manifold ContDiff

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn

open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

variable {M : Type*} [TopologicalSpace M] [ChartedSpace ThreeSpace M]
  [IsManifold I3 ∞ M] [T2Space M] [SigmaCompactSpace M] [PreconnectedSpace M] [NoncompactSpace M]
  {D : RealTimeInterval} {flow : SolutionOn (I := I3) (M := M) D}
  {eps C1 C2 time : ℝ} {x : M}

theorem CanonicalWitness.neck_or_cap_on_noncompact
    (witness : CanonicalWitness flow eps C1 C2 x time) :
    Nonempty (SpatialNeck (flow.base.metric time) eps x) ∨
      ∃ cap : LocalCap flow eps x time witness.domain.carrier,
        ∃ depth : ∀ z ∈ cap.tube, 10000 / Real.sqrt (flow.scalar time x) ≤
          metricDistance (flow.base.metric time) x z,
          witness.alternative = CanonicalAlternative.cap cap depth := by
  cases htag : witness.alternative with
  | neck data => exact Or.inl ⟨data.strong.toSpatialNeck⟩
  | cap data deep => exact Or.inr ⟨data, deep, rfl⟩
  | positive whole data sec =>
    have hu : witness.domain.carrier = univ := whole.trans (PreconnectedSpace.connectedComponent_eq_univ x)
    exact (noncompact_univ (X := M) (hu ▸ witness.domain.compact)).elim
  | round whole data =>
    have hu : witness.domain.carrier = univ := whole.trans (PreconnectedSpace.connectedComponent_eq_univ x)
    exact (noncompact_univ (X := M) (hu ▸ witness.domain.compact)).elim

end DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn
