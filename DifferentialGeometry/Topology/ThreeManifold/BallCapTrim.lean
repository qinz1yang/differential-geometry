import DifferentialGeometry.Topology.ThreeManifold.ChartSphereBall
import DifferentialGeometry.Topology.Manifold.PartialDiffeomorph.Boundary
import DifferentialGeometry.Topology.Embedding.Sphere

noncomputable section

open Set Metric Manifold
open scoped Manifold ContDiff Topology

namespace DifferentialGeometry.Topology.ThreeManifold

private abbrev E3 := EuclideanSpace ℝ (Fin 3)
private abbrev S2 := sphere (0 : E3) 1

variable {M : Type*} [TopologicalSpace M] [ChartedSpace E3 M] [T2Space M] [IsManifold (𝓡 3) ∞ M]

theorem exists_complementary_ball_chart_of_ball_cap_cover
    (A B : PartialDiffeomorph (𝓡 3) (𝓡 3) E3 M ∞)
    (hA : closedBall (0 : E3) 1 ⊆ A.source)
    (hB : closedBall (0 : E3) 1 ⊆ B.source)
    (hcover : B '' closedBall (0 : E3) 1 ∪ A '' closedBall (0 : E3) 1 = univ) :
    ∃ G : PartialDiffeomorph (𝓡 3) (𝓡 3) E3 M ∞,
      closedBall (0 : E3) 1 ⊆ G.source ∧
      G '' ball (0 : E3) 1 = (B '' closedBall (0 : E3) 1)ᶜ ∧
      G '' closedBall (0 : E3) 1 = (B '' ball (0 : E3) 1)ᶜ ∧
      G '' sphere (0 : E3) 1 = B '' sphere (0 : E3) 1 := by
  let C : Set M := (B '' closedBall (0 : E3) 1)ᶜ
  have hBA : IsCompact (B '' closedBall (0 : E3) 1) :=
    (isCompact_closedBall _ _).image_of_continuousOn
      (B.contMDiffOn_toFun.continuousOn.mono hB)
  have hAA : IsCompact (A '' closedBall (0 : E3) 1) :=
    (isCompact_closedBall _ _).image_of_continuousOn
      (A.contMDiffOn_toFun.continuousOn.mono hA)
  have hCsub : C ⊆ A '' closedBall (0 : E3) 1 := by
    intro x hx
    have hh : x ∈ B '' closedBall (0 : E3) 1 ∪ A '' closedBall (0 : E3) 1 := by
      rw [hcover]
      exact mem_univ x
    exact hh.resolve_left hx
  have hclsub : closure C ⊆ A '' closedBall (0 : E3) 1 :=
    closure_minimal hCsub hAA.isClosed
  have hcompact : IsCompact (closure C) := hAA.of_isClosed_subset isClosed_closure hclsub
  have hsource : closure C ⊆ A.target := by
    rintro x hx
    obtain ⟨y, hy, rfl⟩ := hclsub hx
    exact A.map_source (hA hy)
  let e : S2 → M := B ∘ Subtype.val
  have he : IsSmoothEmbedding (𝓡 2) (𝓡 3) ∞ e :=
    DifferentialGeometry.Topology.isSmoothEmbedding_comp_partialDiffeomorph B
      (isSmoothEmbedding_coe_sphere (E := E3) (n := 2))
      (by rw [Subtype.range_val]; exact sphere_subset_closedBall.trans hB)
  have hfront : frontier C = range e := by
    have hh := B.image_frontier_of_isCompact (isCompact_closedBall (0 : E3) 1) hB
    rw [frontier_closedBall _ one_ne_zero] at hh
    change frontier (B '' closedBall (0 : E3) 1)ᶜ = range (B ∘ Subtype.val)
    rw [frontier_compl, ← hh, range_comp, Subtype.range_val]
  have hne : C.Nonempty := by
    by_contra hh
    have hall : B '' closedBall (0 : E3) 1 = univ := by
      apply eq_univ_of_forall
      intro z
      by_contra hz
      exact hh ⟨z, hz⟩
    have hfrontne : (frontier C).Nonempty := by
      rw [hfront]
      exact range_nonempty e
    change (frontier (B '' closedBall (0 : E3) 1)ᶜ).Nonempty at hfrontne
    simp only [hall, compl_univ, frontier_empty, Set.not_nonempty_empty] at hfrontne
  obtain ⟨G, hGs, hGo, hGc, hGf⟩ :=
    exists_ball_chart_of_compact_closure_sphere_frontier A hBA.isClosed.isOpen_compl
      hne hcompact hsource e he hfront
  have hclosure : closure C = (B '' ball (0 : E3) 1)ᶜ := by
    change closure (B '' closedBall (0 : E3) 1)ᶜ = _
    rw [closure_compl]
    congr 1
    have hh := B.toOpenPartialHomeomorph.image_interior_of_subset_source hB
    change B '' interior (closedBall (0 : E3) 1) =
      interior (B '' closedBall (0 : E3) 1) at hh
    rw [interior_closedBall _ one_ne_zero] at hh
    exact hh.symm
  refine ⟨G, hGs, hGo, hGc.trans hclosure, ?_⟩
  simpa only [e, range_comp, Subtype.range_val] using hGf

end DifferentialGeometry.Topology.ThreeManifold
