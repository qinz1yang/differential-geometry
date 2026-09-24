import DifferentialGeometry.Topology.ThreeManifold.AntipodalQuotientBall
import DifferentialGeometry.Topology.Manifold.PartialDiffeomorph.Boundary

noncomputable section

open Set Metric Manifold
open scoped Manifold ContDiff

namespace DifferentialGeometry.Topology.ThreeManifold

private abbrev E3 := EuclideanSpace ℝ (Fin 3)
private abbrev E4 := EuclideanSpace ℝ (Fin 4)
private abbrev S2 := Metric.sphere (0 : E3) 1
private abbrev S3 := Metric.sphere (0 : E4) 1

variable {Z : Type*} [TopologicalSpace Z] [ChartedSpace E3 Z] [T2Space Z]

theorem exists_ball_or_complement_avoiding_closed_ball_of_projective_sphere_embedding
    (p : S3 → Z) (hp : IsLocalDiffeomorph (𝓡 3) (𝓡 3) ∞ p)
    (honto : Function.Surjective p)
    (hfib : ∀ x y : S3, p x = p y ↔ x = y ∨ (x : E4) = -(y : E4))
    (C : PartialDiffeomorph (𝓡 3) (𝓡 3) E3 Z ∞)
    (hC : closedBall (0 : E3) 1 ⊆ C.source)
    (e : S2 → Z) (he : IsSmoothEmbedding (𝓡 2) (𝓡 3) ∞ e)
    (havoid : Disjoint (C '' closedBall (0 : E3) 1) (range e)) :
    ∃ B : PartialDiffeomorph (𝓡 3) (𝓡 3) E3 Z ∞,
      closedBall (0 : E3) 1 ⊆ B.source ∧
      B '' sphere (0 : E3) 1 = range e ∧
      (B '' closedBall (0 : E3) 1 ⊆ (C '' closedBall (0 : E3) 1)ᶜ ∨
        (B '' ball (0 : E3) 1)ᶜ ⊆ (C '' closedBall (0 : E3) 1)ᶜ) := by
  obtain ⟨B, hB, hBs⟩ :=
    exists_ball_chart_of_antipodal_quotient_sphere_embedding p hp honto hfib e he
  let K := B '' closedBall (0 : E3) 1
  let O := C '' closedBall (0 : E3) 1
  have hK : IsCompact K :=
    (isCompact_closedBall _ _).image_of_continuousOn (B.contMDiffOn_toFun.continuousOn.mono hB)
  have hKfront : frontier K = range e := by
    rw [← B.image_frontier_of_isCompact (isCompact_closedBall _ _) hB,
      frontier_closedBall _ one_ne_zero, hBs]
  have hKint : interior K = B '' ball (0 : E3) 1 := by
    have h := B.toOpenPartialHomeomorph.image_interior_of_subset_source hB
    change B '' interior (closedBall (0 : E3) 1) = interior K at h
    rw [interior_closedBall _ one_ne_zero] at h
    exact h.symm
  have hO : IsPreconnected O :=
    (convex_closedBall (0 : E3) 1).isPreconnected.image C (C.contMDiffOn_toFun.continuousOn.mono hC)
  have hcover : O ⊆ interior K ∪ Kᶜ := by
    intro x hx
    have hxnot : x ∈ (frontier K)ᶜ := by
      rw [hKfront]
      exact fun h => disjoint_left.mp havoid hx h
    rwa [compl_frontier_eq_union_interior, hK.isClosed.isOpen_compl.interior_eq] at hxnot
  refine ⟨B, hB, hBs, ?_⟩
  rcases hO.subset_or_subset isOpen_interior hK.isClosed.isOpen_compl
    (disjoint_compl_right.mono_left interior_subset) hcover with hin | hout
  · right
    intro x hx hy
    exact hx (hKint ▸ hin hy)
  · left
    exact fun x hx hy => hout hy hx

end DifferentialGeometry.Topology.ThreeManifold
