import DifferentialGeometry.Topology.ThreeManifold.TwoBallCharts
import DifferentialGeometry.Topology.Manifold.Components
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.ClosedOrientedStage
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.DiscardedCapMaps
import DifferentialGeometry.Topology.ThreeManifold.ConnectedSum.OppositeInvarianceObstruction

noncomputable section

open Set Metric Manifold
open DifferentialGeometry.Topology
open scoped Manifold ContDiff

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.SmoothCutCapTransition

universe u

local notation "E3" => EuclideanSpace ℝ (Fin 3)
local notation "S3" => Metric.sphere (0 : EuclideanSpace ℝ (Fin 4)) 1

variable {P Q D N : OrientedThreeStage.{u}} (E : SmoothCutCapTransition P Q D N)

theorem exists_sphere_diffeomorph_of_discarded_cap_and_complementary_ball
    (c : ConnectedComponents D.Carrier)
    (boundary : E.trace.tubes.Boundary) (hdiscarded : E.trace.capDiscarded boundary)
    (A B : PartialDiffeomorph (𝓡 3) (𝓡 3) E3
      (D.toClosedOrientedManifold.component c).Carrier ∞)
    (hA : closedBall (0 : E3) 1 ⊆ A.source)
    (hB : closedBall (0 : E3) 1 ⊆ B.source)
    (hcap : ∀ (z : E3) (hz : z ∈ closedBall (0 : E3) 1),
      (A z).val = E.trace.discardedCap boundary hdiscarded ⟨z, hz⟩)
    (hcover : B '' ball (0 : E3) 1 = (A '' closedBall (0 : E3) 1)ᶜ) :
    ∃ e : S3 ≃ₘ⟮𝓡 3, 𝓡 3⟯ (D.toClosedOrientedManifold.component c).Carrier,
      (∃ a b : PartialDiffeomorph (𝓡 3) (𝓡 3) E3 S3 ∞,
        a.source = univ ∧ b.source = univ ∧
        a '' closedBall (0 : E3) 1 = (b '' ball (0 : E3) 1)ᶜ ∧
        (∀ (z : E3) (hz : z ∈ closedBall (0 : E3) 1),
          (e (a z)).val = E.trace.discardedCap boundary hdiscarded ⟨z, hz⟩) ∧
        ∃ F : E3 ≃ₘ[ℝ] E3,
          F '' closedBall (0 : E3) 1 = closedBall (0 : E3) 1 ∧
          ∀ z ∈ closedBall (0 : E3) 1, e (b z) = B (F z)) ∧
      Nonempty (ClosedOrientedManifold.OrientedDiffeomorph
        (D.toClosedOrientedManifold.component c).toClosedOrientedManifold
        standardThreeSphereLift.{u}.toClosedOrientedManifold) := by
  obtain ⟨e, a, b, ha, hb, hab, heA, F, hF, heB⟩ :=
    DifferentialGeometry.Topology.Manifold.exists_sphere_diffeomorph_of_complementary_ball_charts
      A B hA hB hcover
  refine ⟨e, ⟨a, b, ha, hb, hab, ?_, F, hF, heB⟩, ?_⟩
  · intro z hz
    rw [heA z hz]
    exact hcap z hz
  · exact nonempty_orientedDiffeomorph_standardThreeSphere_of_diffeomorph
      (D.toClosedOrientedManifold.component c)
      ⟨e.symm.trans standardThreeSphereLiftDiffeomorph⟩

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.SmoothCutCapTransition
