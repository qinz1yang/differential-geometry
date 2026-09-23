import DifferentialGeometry.Topology.ThreeManifold.SphereInsideProjectiveCap
import DifferentialGeometry.Topology.Manifold.PartialChartEmbedding
import DifferentialGeometry.Topology.OpenPartialHomeomorph.Images

noncomputable section

open Set Metric Manifold
open scoped Manifold ContDiff Topology

namespace DifferentialGeometry.Topology.ThreeManifold

private abbrev E3 := EuclideanSpace ℝ (Fin 3)
private abbrev E4 := EuclideanSpace ℝ (Fin 4)
private abbrev S2 := Metric.sphere (0 : E3) 1
private abbrev S3 := Metric.sphere (0 : E4) 1

variable {M Z : Type*} [TopologicalSpace M] [ChartedSpace E3 M]
  [T2Space M]
  [TopologicalSpace Z] [ChartedSpace E3 Z] [IsManifold (𝓡 3) ∞ Z] [T2Space Z] [CompactSpace Z]

theorem exists_compact_side_inside_projective_cap_of_sphere_embedding
    (p : S3 → Z) (hp : IsLocalDiffeomorph (𝓡 3) (𝓡 3) ∞ p)
    (honto : Function.Surjective p)
    (hfib : ∀ x y : S3, p x = p y ↔ x = y ∨ (x : E4) = -(y : E4))
    (C : PartialDiffeomorph (𝓡 3) (𝓡 3) E3 Z ∞)
    (F : PartialDiffeomorph (𝓡 3) (𝓡 3) Z M ∞)
    (hC : closedBall (0 : E3) 1 ⊆ C.source)
    (hF : (C '' ball (0 : E3) 1)ᶜ ⊆ F.source)
    (e : S2 → M) (he : IsSmoothEmbedding (𝓡 2) (𝓡 3) ∞ e)
    (hinside : range e ⊆ interior (F '' (C '' ball (0 : E3) 1)ᶜ)) :
    ∃ (K : Set M) (B : PartialDiffeomorph (𝓡 3) (𝓡 3) E3 Z ∞),
      closedBall (0 : E3) 1 ⊆ B.source ∧
      F '' (B '' sphere (0 : E3) 1) = range e ∧
      (K = F '' (B '' closedBall (0 : E3) 1) ∨ K = F '' (B '' ball (0 : E3) 1)ᶜ) ∧
      IsCompact K ∧ closure (interior K) = K ∧ frontier K = range e ∧
      K ⊆ interior (F '' (C '' ball (0 : E3) 1)ᶜ) := by
  let K0 := (C '' ball (0 : E3) 1)ᶜ
  have hK0int : interior K0 = (C '' closedBall (0 : E3) 1)ᶜ := by
    rw [interior_compl, DifferentialGeometry.Topology.Manifold.closure_image_ball_of_partialDiffeomorph C hC]
  have hFint : F '' (C '' closedBall (0 : E3) 1)ᶜ = interior (F '' K0) := by
    have h := F.toOpenPartialHomeomorph.image_interior_of_subset_source hF
    change F '' interior K0 = interior (F '' K0) at h
    rwa [hK0int] at h
  have hes : range e ⊆ F.target := by
    rintro x hx
    obtain ⟨z, hz, rfl⟩ := interior_subset (hinside hx)
    exact F.map_source (hF hz)
  let eZ : S2 → Z := F.symm ∘ e
  have heZ : IsSmoothEmbedding (𝓡 2) (𝓡 3) ∞ eZ :=
    DifferentialGeometry.Topology.isSmoothEmbedding_comp_partialDiffeomorph F.symm he hes
  have heZsub : range eZ ⊆ (C '' closedBall (0 : E3) 1)ᶜ := by
    rintro x ⟨q, rfl⟩
    obtain ⟨z, hz, heq⟩ := hFint.symm ▸ hinside (mem_range_self q)
    have hz0 : z ∈ K0 := fun hzball => hz (image_mono ball_subset_closedBall hzball)
    change F.toPartialEquiv.symm (e q) ∈ _
    rw [← heq, F.toPartialEquiv.left_inv (hF hz0)]
    exact hz
  obtain ⟨B, hB, hBs, havoid⟩ :=
    exists_ball_or_complement_avoiding_closed_ball_of_projective_sphere_embedding
      p hp honto hfib C hC eZ heZ
      (disjoint_left.mpr (fun x hx he => heZsub he hx))
  have hFsphere : F '' (B '' sphere (0 : E3) 1) = range e := by
    rw [hBs, ← range_comp]
    apply congrArg range
    funext q
    exact F.right_inv (hes (mem_range_self q))
  have hBcompact : IsCompact (B '' closedBall (0 : E3) 1) :=
    (isCompact_closedBall _ _).image_of_continuousOn (B.contMDiffOn_toFun.continuousOn.mono hB)
  have hBint : interior (B '' closedBall (0 : E3) 1) = B '' ball (0 : E3) 1 := by
    have h := B.toOpenPartialHomeomorph.image_interior_of_subset_source hB
    change B '' interior (closedBall (0 : E3) 1) = interior (B '' closedBall (0 : E3) 1) at h
    rw [interior_closedBall _ one_ne_zero] at h
    exact h.symm
  have hBfront : frontier (B '' closedBall (0 : E3) 1) = B '' sphere (0 : E3) 1 := by
    rw [← B.image_frontier_of_isCompact (isCompact_closedBall _ _) hB,
      frontier_closedBall _ one_ne_zero]
  have hBreg : closure (interior (B '' closedBall (0 : E3) 1)) =
      B '' closedBall (0 : E3) 1 := by
    rw [hBint, DifferentialGeometry.Topology.Manifold.closure_image_ball_of_partialDiffeomorph B hB]
  have hBoreg : closure (interior (B '' ball (0 : E3) 1)ᶜ) =
      (B '' ball (0 : E3) 1)ᶜ := by
    rw [interior_compl, DifferentialGeometry.Topology.Manifold.closure_image_ball_of_partialDiffeomorph B hB,
      closure_compl, hBint]
  have hBofront : frontier (B '' ball (0 : E3) 1)ᶜ = B '' sphere (0 : E3) 1 := by
    rw [frontier_compl, DifferentialGeometry.Topology.Manifold.frontier_image_ball_of_partialDiffeomorph B hB]
  have finish (A : Set Z) (hA : IsCompact A) (hAr : closure (interior A) = A)
      (hAf : frontier A = B '' sphere (0 : E3) 1)
      (hAin : A ⊆ (C '' closedBall (0 : E3) 1)ᶜ) :
      IsCompact (F '' A) ∧ closure (interior (F '' A)) = F '' A ∧
        frontier (F '' A) = range e ∧ F '' A ⊆ interior (F '' K0) := by
    have hAs : A ⊆ F.source := fun x hx => hF (fun h => hAin hx (image_mono ball_subset_closedBall h))
    have hK : IsCompact (F '' A) := hA.image_of_continuousOn (F.contMDiffOn_toFun.continuousOn.mono hAs)
    refine ⟨hK, ?_, ?_, ?_⟩
    · exact F.toOpenPartialHomeomorph.closure_interior_image_of_subset_source hAs hAr hK.isClosed
    · rw [← F.image_frontier_of_isCompact hA hAs, hAf, hFsphere]
    · rw [← hFint]
      exact image_mono hAin
  rcases havoid with havoid | havoid
  · exact ⟨F '' (B '' closedBall (0 : E3) 1), B, hB, hFsphere, Or.inl rfl,
      finish _ hBcompact hBreg hBfront havoid⟩
  · have hcompact : IsCompact (B '' ball (0 : E3) 1)ᶜ :=
      (B.toOpenPartialHomeomorph.isOpen_image_of_subset_source isOpen_ball
        (ball_subset_closedBall.trans hB)).isClosed_compl.isCompact
    exact ⟨F '' (B '' ball (0 : E3) 1)ᶜ, B, hB, hFsphere, Or.inr rfl,
      finish _ hcompact hBoreg hBofront havoid⟩

end DifferentialGeometry.Topology.ThreeManifold
