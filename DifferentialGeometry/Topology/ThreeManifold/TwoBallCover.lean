import DifferentialGeometry.Topology.ThreeManifold.TwoBallCharts
import DifferentialGeometry.Topology.ThreeManifold.BallCapTrim

set_option autoImplicit false
noncomputable section
open Set Metric Manifold
open scoped Manifold ContDiff Topology

namespace DifferentialGeometry.Topology.Manifold

private abbrev E3 := EuclideanSpace ℝ (Fin 3)
private abbrev E4 := EuclideanSpace ℝ (Fin 4)
private abbrev S3 := sphere (0 : E4) 1

theorem exists_sphere_diffeomorph_of_ball_chart_cover
    {M : Type*} [TopologicalSpace M] [ChartedSpace E3 M]
    [IsManifold (𝓡 3) ∞ M] [T2Space M]
    (A B : PartialDiffeomorph (𝓡 3) (𝓡 3) E3 M ∞)
    (hA : closedBall (0 : E3) 1 ⊆ A.source)
    (hB : closedBall (0 : E3) 1 ⊆ B.source)
    (hcover : B '' closedBall (0 : E3) 1 ∪ A '' closedBall (0 : E3) 1 = univ) :
    ∃ (e : M ≃ₘ⟮𝓡 3,𝓡 3⟯ S3)
      (a b : PartialDiffeomorph (𝓡 3) (𝓡 3) E3 S3 ∞)
      (G : PartialDiffeomorph (𝓡 3) (𝓡 3) E3 M ∞),
      a.source = univ ∧ b.source = univ ∧ closedBall (0 : E3) 1 ⊆ G.source ∧
      G '' ball (0 : E3) 1 = (B '' closedBall (0 : E3) 1)ᶜ ∧
      G '' closedBall (0 : E3) 1 = (B '' ball (0 : E3) 1)ᶜ ∧
      G '' sphere (0 : E3) 1 = B '' sphere (0 : E3) 1 ∧
      a '' closedBall (0 : E3) 1 = (b '' ball (0 : E3) 1)ᶜ ∧
      (∀ z ∈ closedBall (0 : E3) 1, e (B z) = a z) ∧
      (∃ D : E3 ≃ₘ[ℝ] E3,
        D '' closedBall (0 : E3) 1 = closedBall (0 : E3) 1 ∧
        ∀ z ∈ closedBall (0 : E3) 1, e (G (D z)) = b z) ∧
      ∃ U : Set M, IsOpen U ∧ B '' closedBall (0 : E3) 1 ⊆ U ∧
        U ⊆ (B.symm.trans a).source ∧ EqOn e (B.symm.trans a) U := by
  obtain ⟨G,hG,hGo,hGc,hGs⟩ :=
    DifferentialGeometry.Topology.ThreeManifold.exists_complementary_ball_chart_of_ball_cap_cover
      A B hA hB hcover
  obtain ⟨e,a,b,ha,hb,hab,heB,D,hD,heG,U,hU,hBU,hUs,hEq⟩ :=
    exists_sphere_diffeomorph_of_complementary_ball_charts_eqOn_neighborhood B G hB hG hGo
  refine ⟨e.symm,a,b,G,ha,hb,hG,hGo,hGc,hGs,hab,?_,⟨D,hD,?_⟩,U,hU,hBU,hUs,hEq⟩
  · intro z hz
    exact (congrArg e.symm (heB z hz)).symm.trans (e.symm_apply_apply _)
  · intro z hz
    exact (congrArg e.symm (heG z hz)).symm.trans (e.symm_apply_apply _)

end DifferentialGeometry.Topology.Manifold
