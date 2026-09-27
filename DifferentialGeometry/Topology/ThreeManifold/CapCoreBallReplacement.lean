import DifferentialGeometry.Topology.ThreeManifold.RelativeBallReplacement
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.CapRegionStructure

noncomputable section

open Set Metric Manifold
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
open scoped Manifold ContDiff Topology

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn

universe u

variable {Z M : Type u} [TopologicalSpace Z] [ChartedSpace ThreeSpace Z] [T3Space Z]
  [TopologicalSpace M] [ChartedSpace ThreeSpace M] [T2Space M]

theorem CapCore.nonempty_ball_replacement
    {Ω : Set Z} (cap : CapCore Ω)
    (b : PartialDiffeomorph I3 I3 ThreeSpace Z ∞)
    (P : PartialDiffeomorph I3 I3 Z M ∞)
    (G : PartialDiffeomorph I3 I3 ThreeSpace M ∞)
    (hb : closedBall (0 : ThreeSpace) 1 ⊆ b.source)
    (hG : closedBall (0 : ThreeSpace) 1 ⊆ G.source)
    (hbΩ : b '' closedBall (0 : ThreeSpace) 1 ⊆ interior Ω)
    (hP : Ω \ b '' Metric.ball (0 : ThreeSpace) 1 ⊆ P.source)
    (hboundary : P '' (b '' sphere (0 : ThreeSpace) 1) = G '' sphere (0 : ThreeSpace) 1)
    (hinter : P '' (Ω \ b '' Metric.ball (0 : ThreeSpace) 1) ∩ G '' closedBall (0 : ThreeSpace) 1 ⊆
      G '' sphere (0 : ThreeSpace) 1) :
    Nonempty (CapCore (P '' (Ω \ b '' Metric.ball (0 : ThreeSpace) 1) ∪
      G '' closedBall (0 : ThreeSpace) 1)) ∧
      ∃ (J : PartialDiffeomorph I3 I3 Z M ∞)
        (D : Diffeomorph I3 I3 ThreeSpace ThreeSpace ∞),
        Ω ⊆ J.source ∧
        J '' Ω = P '' (Ω \ b '' Metric.ball (0 : ThreeSpace) 1) ∪ G '' closedBall (0 : ThreeSpace) 1 ∧
        D '' closedBall (0 : ThreeSpace) 1 = closedBall (0 : ThreeSpace) 1 ∧
        (∀ z ∈ closedBall (0 : ThreeSpace) 1, J (b z) = G (D z)) ∧
        ∃ O : Set Z, IsOpen O ∧ Ω \ b '' Metric.ball (0 : ThreeSpace) 1 ⊆ O ∧
          O ⊆ P.source ∧ EqOn J P O := by
  obtain ⟨J, D, hJ, hJimage, hD, hcap, O, hO, hKO, hOP, hJP⟩ :=
    DifferentialGeometry.Topology.Manifold.exists_partialDiffeomorph_ball_replacement_eqOn_complement
      b P G hb hG cap.isCompact_carrier hbΩ hP hboundary hinter
  refine ⟨?_, J, D, hJ, hJimage, hD, hcap, O, hO, hKO, hOP, hJP⟩
  rw [← hJimage]
  exact cap.image_of_partialDiffeomorph J hJ

end DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn

section

open Set Metric Manifold
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
open scoped Manifold ContDiff

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn

universe u
variable {Z M : Type u} {ι : Type*}
  [TopologicalSpace Z] [ChartedSpace ThreeSpace Z] [T3Space Z]
  [TopologicalSpace M] [ChartedSpace ThreeSpace M] [T2Space M]

theorem CapCore.nonempty_finite_ball_replacement
    {Ω : Set Z} (cap : CapCore Ω) (s : Finset ι)
    (b : ι → PartialDiffeomorph I3 I3 ThreeSpace Z ∞)
    (G : ι → PartialDiffeomorph I3 I3 ThreeSpace M ∞)
    (hb : ∀ i ∈ s, closedBall (0 : ThreeSpace) 1 ⊆ (b i).source)
    (hG : ∀ i ∈ s, closedBall (0 : ThreeSpace) 1 ⊆ (G i).source)
    (hbΩ : ∀ i ∈ s, b i '' closedBall (0 : ThreeSpace) 1 ⊆ interior Ω)
    (hdisb : (s : Set ι).Pairwise (fun i j => Disjoint
      (b i '' closedBall (0 : ThreeSpace) 1) (b j '' closedBall (0 : ThreeSpace) 1)))
    (hdisG : (s : Set ι).Pairwise (fun i j => Disjoint
      (G i '' closedBall (0 : ThreeSpace) 1) (G j '' closedBall (0 : ThreeSpace) 1)))
    (P : PartialDiffeomorph I3 I3 Z M ∞)
    (hP : Ω \ ⋃ i ∈ s, b i '' Metric.ball (0 : ThreeSpace) 1 ⊆ P.source)
    (hboundary : ∀ i ∈ s,
      P '' (b i '' sphere (0 : ThreeSpace) 1) = G i '' sphere (0 : ThreeSpace) 1)
    (hinter : ∀ i ∈ s, P '' (Ω \ ⋃ j ∈ s, b j '' Metric.ball (0 : ThreeSpace) 1) ∩
      G i '' closedBall (0 : ThreeSpace) 1 ⊆ G i '' sphere (0 : ThreeSpace) 1) :
    Nonempty (CapCore (P '' (Ω \ ⋃ i ∈ s, b i '' Metric.ball (0 : ThreeSpace) 1) ∪
      ⋃ i ∈ s, G i '' closedBall (0 : ThreeSpace) 1)) ∧
      ∃ J : PartialDiffeomorph I3 I3 Z M ∞,
        Ω ⊆ J.source ∧
        J '' Ω = P '' (Ω \ ⋃ i ∈ s, b i '' Metric.ball (0 : ThreeSpace) 1) ∪
          ⋃ i ∈ s, G i '' closedBall (0 : ThreeSpace) 1 ∧
        (∀ i ∈ s, ∃ D : ThreeSpace ≃ₘ[ℝ] ThreeSpace,
          D '' closedBall (0 : ThreeSpace) 1 = closedBall (0 : ThreeSpace) 1 ∧
          ∀ z ∈ closedBall (0 : ThreeSpace) 1, J (b i z) = G i (D z)) ∧
        ∃ O : Set Z, IsOpen O ∧ (Ω \ ⋃ i ∈ s, b i '' Metric.ball (0 : ThreeSpace) 1) ⊆ O ∧
          O ⊆ P.source ∧ EqOn J P O := by
  obtain ⟨J,hJ,himage,hballs,O,hO,hKO,hOP,hJP⟩ :=
    DifferentialGeometry.Topology.Manifold.exists_partialDiffeomorph_finite_ball_replacement_eqOn_complement
      s b G hb hG cap.isCompact_carrier hbΩ hdisb hdisG P hP hboundary hinter
  refine ⟨?_,J,hJ,himage,hballs,O,hO,hKO,hOP,hJP⟩
  rw [← himage]
  exact cap.image_of_partialDiffeomorph J hJ

end DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn

end
