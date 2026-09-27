import DifferentialGeometry.Topology.ThreeManifold.ProjectiveCapTrim
import DifferentialGeometry.Topology.ThreeManifold.TwoBallCharts

set_option autoImplicit false
noncomputable section
open Set Metric Manifold
open scoped Manifold ContDiff Topology

namespace DifferentialGeometry.Topology.ThreeManifold

private abbrev E3 := EuclideanSpace ℝ (Fin 3)
private abbrev E4 := EuclideanSpace ℝ (Fin 4)
private abbrev S3 := sphere (0 : E4) 1

variable {M Z : Type*} [TopologicalSpace M] [ChartedSpace E3 M]
  [IsManifold (𝓡 3) ∞ M] [T2Space M] [PreconnectedSpace M]
  [TopologicalSpace Z] [ChartedSpace E3 Z] [IsManifold (𝓡 3) ∞ Z] [T2Space Z] [CompactSpace Z]

theorem exists_sphere_or_projective_diffeomorph_of_cap_cover
    (p : S3 → Z) (hp : IsLocalDiffeomorph (𝓡 3) (𝓡 3) ∞ p)
    (honto : Function.Surjective p)
    (hfib : ∀ x y : S3, p x = p y ↔ x = y ∨ (x : E4) = -(y : E4))
    (b : PartialDiffeomorph (𝓡 3) (𝓡 3) E3 Z ∞)
    (F : PartialDiffeomorph (𝓡 3) (𝓡 3) Z M ∞)
    (B : PartialDiffeomorph (𝓡 3) (𝓡 3) E3 M ∞)
    (hb : closedBall (0 : E3) 1 ⊆ b.source)
    (hF : (b '' ball (0 : E3) 1)ᶜ ⊆ F.source)
    (hB : closedBall (0 : E3) 1 ⊆ B.source)
    (hcover : B '' closedBall (0 : E3) 1 ∪ F '' (b '' ball (0 : E3) 1)ᶜ = univ) :
    (∃ (e : M ≃ₘ⟮𝓡 3,𝓡 3⟯ S3)
      (a : PartialDiffeomorph (𝓡 3) (𝓡 3) E3 S3 ∞),
      a.source = univ ∧
      (∀ z ∈ closedBall (0 : E3) 1, e (B z) = a z) ∧
      ∃ U : Set M, IsOpen U ∧ B '' closedBall (0 : E3) 1 ⊆ U ∧
        U ⊆ (B.symm.trans a).source ∧ EqOn e (B.symm.trans a) U) ∨
    ∃ (e : M ≃ₘ⟮𝓡 3,𝓡 3⟯ Z)
      (G : PartialDiffeomorph (𝓡 3) (𝓡 3) E3 Z ∞)
      (D : E3 ≃ₘ[ℝ] E3),
      closedBall (0 : E3) 1 ⊆ G.source ∧
      (G '' ball (0 : E3) 1)ᶜ ⊆ F.source ∧
      D '' closedBall (0 : E3) 1 = closedBall (0 : E3) 1 ∧
      (∀ z ∈ closedBall (0 : E3) 1, e (B (D z)) = G z) ∧
      EqOn e.symm F (G '' ball (0 : E3) 1)ᶜ ∧
      e '' (B '' ball (0 : E3) 1) = G '' ball (0 : E3) 1 ∧
      F '' (G '' ball (0 : E3) 1)ᶜ = (B '' ball (0 : E3) 1)ᶜ ∧
      F '' (G '' sphere (0 : E3) 1) = B '' sphere (0 : E3) 1 ∧
      ∃ U : Set Z, IsOpen U ∧ (G '' ball (0 : E3) 1)ᶜ ⊆ U ∧
        U ⊆ F.source ∧ EqOn e.symm F U := by
  obtain h | h := exists_ball_or_projective_complement_of_cap_cover p hp honto hfib b F B hb hF hB hcover
  · obtain ⟨G,hG,hGo,_,_⟩ := h
    obtain ⟨e,a,c,ha,_,_,heB,D,hD,heG,U,hU,hBU,hUs,hEq⟩ :=
      DifferentialGeometry.Topology.Manifold.exists_sphere_diffeomorph_of_complementary_ball_charts_eqOn_neighborhood
        B G hB hG hGo
    refine Or.inl ⟨e.symm,a,ha,?_,U,hU,hBU,hUs,hEq⟩
    intro z hz
    exact (congrArg e.symm (heB z hz)).symm.trans (e.symm_apply_apply _)
  · obtain ⟨G,hG,hGF,hFo,hFc,hFs⟩ := h
    have hBo : B '' ball (0 : E3) 1 = ((B '' ball (0 : E3) 1)ᶜ)ᶜ := (compl_compl _).symm
    obtain ⟨e,heF,heBall,D,hD,heB,U,hU,hGU,hUF,hEq⟩ :=
      DifferentialGeometry.Topology.Manifold.exists_diffeomorph_of_ball_complement_and_ball G F B
        hG hGF hB hFc hBo
    refine Or.inr ⟨e.symm,G,D,hG,hGF,hD,?_,heF,?_,hFc,hFs,U,hU,hGU,hUF,hEq⟩
    · intro z hz
      exact (congrArg e.symm (heB z hz)).symm.trans (e.symm_apply_apply _)
    · rw [← compl_compl (B '' ball (0 : E3) 1),← heBall,image_image]
      simp only [e.symm_apply_apply,image_id']

end DifferentialGeometry.Topology.ThreeManifold
