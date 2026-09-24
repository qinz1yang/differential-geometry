import DifferentialGeometry.Topology.ThreeManifold.ChartSphereBall
import DifferentialGeometry.Topology.Manifold.StereographicChart

noncomputable section

open Set Metric Manifold
open scoped Manifold ContDiff

namespace DifferentialGeometry.Topology.ThreeManifold

private abbrev E3 := EuclideanSpace ℝ (Fin 3)
private abbrev E4 := EuclideanSpace ℝ (Fin 4)
private abbrev S2 := Metric.sphere (0 : E3) 1
private abbrev S3 := Metric.sphere (0 : E4) 1

theorem exists_ball_chart_of_sphere_embedding_avoiding_point
    (e : S2 → S3) (he : IsSmoothEmbedding (𝓡 2) (𝓡 3) ∞ e)
    (p : S3) (hp : p ∉ range e) :
    ∃ B : PartialDiffeomorph (𝓡 3) (𝓡 3) E3 S3 ∞,
      closedBall (0 : E3) 1 ⊆ B.source ∧
      B '' sphere (0 : E3) 1 = range e ∧ p ∉ B '' closedBall (0 : E3) 1 := by
  let A : PartialDiffeomorph (𝓡 3) (𝓡 3) E3 S3 ∞ :=
    { toPartialEquiv := (stereographic' 3 p).symm.toPartialEquiv
      open_source := (stereographic' 3 p).symm.open_source
      open_target := (stereographic' 3 p).symm.open_target
      contMDiffOn_toFun :=
        (DifferentialGeometry.Topology.Manifold.stereographicInverse_isLocalDiffeomorph p)
          |>.contMDiff.contMDiffOn
      contMDiffOn_invFun :=
        (DifferentialGeometry.Topology.Manifold.stereographic_isLocalDiffeomorphOn p).contMDiffOn }
  have hAs : A.source = univ := by change (stereographic' 3 p).target = univ; simp
  have hAt : A.target = {p}ᶜ := by change (stereographic' 3 p).source = {p}ᶜ; simp
  have hes : range e ⊆ A.target := by
    rw [hAt]
    intro x hx hxp
    exact hp (mem_singleton_iff.mp hxp ▸ hx)
  let f : S2 → E3 := A.symm ∘ e
  have hf : IsSmoothEmbedding (𝓡 2) (𝓡 3) ∞ f :=
    DifferentialGeometry.Topology.isSmoothEmbedding_comp_partialDiffeomorph A.symm he hes
  obtain ⟨F, hF⟩ := smooth_schoenflies_three f hf
  let B := F.toPartialDiffeomorph.trans A
  have hB : closedBall (0 : E3) 1 ⊆ B.source := by
    intro x _
    exact ⟨mem_univ _, hAs ▸ mem_univ _⟩
  have hBsphere : B '' sphere (0 : E3) 1 = range e := by
    change (A ∘ F) '' sphere (0 : E3) 1 = range e
    rw [image_comp, hF, range_comp]
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      obtain ⟨z, hz, hzy⟩ := hy
      rw [← hzy]
      exact (A.right_inv (hes hz)).symm ▸ hz
    · rintro ⟨z, rfl⟩
      refine ⟨A.symm (e z), mem_image_of_mem _ (mem_range_self z), ?_⟩
      exact A.right_inv (hes (mem_range_self z))
  refine ⟨B, hB, hBsphere, ?_⟩
  rintro ⟨x, hx, hxp⟩
  have hmem := A.map_source (hAs ▸ mem_univ (F x))
  change B x ∈ A.target at hmem
  rw [hxp, hAt] at hmem
  exact hmem (mem_singleton p)

end DifferentialGeometry.Topology.ThreeManifold
