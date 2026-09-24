import DifferentialGeometry.Topology.ThreeManifold.SmoothSchoenflies
import DifferentialGeometry.Topology.SphereSeparation.SmoothSchoenfliesBallFilling
import DifferentialGeometry.Topology.SphereSeparation.ReconstructionRegions
import DifferentialGeometry.Topology.Manifold.PartialChartEmbedding
import DifferentialGeometry.Topology.OpenPartialHomeomorph.Images

noncomputable section

open Set Metric Manifold
open scoped Manifold ContDiff Topology

namespace DifferentialGeometry.Topology.ThreeManifold

private abbrev E3 := EuclideanSpace ℝ (Fin 3)
private abbrev S2 := Metric.sphere (0 : E3) 1

variable {M : Type*} [TopologicalSpace M] [ChartedSpace E3 M]

theorem exists_ball_chart_of_compact_closure_sphere_frontier
    (A : PartialDiffeomorph (𝓡 3) (𝓡 3) E3 M ∞)
    {C : Set M} (hC : IsOpen C) (hne : C.Nonempty) (hcompact : IsCompact (closure C))
    (hsource : closure C ⊆ A.target)
    (e : S2 → M) (he : IsSmoothEmbedding (𝓡 2) (𝓡 3) ∞ e)
    (hfront : frontier C = range e) :
    ∃ G : PartialDiffeomorph (𝓡 3) (𝓡 3) E3 M ∞,
      closedBall (0 : E3) 1 ⊆ G.source ∧ G '' ball (0 : E3) 1 = C ∧
      G '' closedBall (0 : E3) 1 = closure C ∧
      G '' sphere (0 : E3) 1 = range e := by
  let V := A.symm '' C
  have hCsource : C ⊆ A.target := subset_closure.trans hsource
  have hVopen : IsOpen V :=
    A.symm.toOpenPartialHomeomorph.isOpen_image_of_subset_source hC hCsource
  have hVne : V.Nonempty := hne.image A.symm
  have hK : IsCompact (A.symm '' closure C) :=
    hcompact.image_of_continuousOn (A.contMDiffOn_invFun.continuousOn.mono hsource)
  have hcl : closure V = A.symm '' closure C := by
    apply Subset.antisymm (closure_minimal (image_mono subset_closure) hK.isClosed)
    exact (A.contMDiffOn_invFun.continuousOn.mono hsource).image_closure
  have hVs : closure V ⊆ A.source := by
    rw [hcl]
    rintro x ⟨y, hy, rfl⟩
    exact A.map_target (hsource hy)
  have hfrontV : frontier V = A.symm '' frontier C := by
    have hh :=
      (A.symm.toOpenPartialHomeomorph.isImage_image_of_subset_source hCsource).frontier.image_eq
    have h1 : frontier C ⊆ A.target := frontier_subset_closure.trans hsource
    have h2 : frontier V ⊆ A.source := frontier_subset_closure.trans hVs
    change A.symm '' (A.target ∩ frontier C) = A.source ∩ frontier V at hh
    rw [inter_eq_right.mpr h1, inter_eq_right.mpr h2] at hh
    exact hh.symm
  let f : S2 → E3 := A.symm ∘ e
  have hesource : range e ⊆ A.target := hfront ▸ frontier_subset_closure.trans hsource
  have hf : IsSmoothEmbedding (𝓡 2) (𝓡 3) ∞ f :=
    DifferentialGeometry.Topology.isSmoothEmbedding_comp_partialDiffeomorph A.symm he hesource
  have hfrange : frontier V = range f := by rw [hfrontV, hfront, ← range_comp]
  let sides := SphereSeparation.jordanBrouwer_openThreeSpace f hf
    (Diffeomorph.refl (𝓡 3) E3 ∞)
  have hside : V = sides.compactSide :=
    sides.toSphereSides.eq_compactSide_of_frontier_subset hVopen hVne (hcl ▸ hK)
      (by
        rw [← hfrange]
        apply disjoint_left.mpr
        intro x hx hfrontier
        exact hfrontier.2 (hVopen.interior_eq.symm ▸ hx)) hfrange.subset
  have hSch : SphereSeparation.smoothSchoenfliesThree :=
    SphereSeparation.smoothSchoenfliesThree_iff_exists_ambient_diffeomorph.mpr
      smooth_schoenflies_three
  obtain ⟨F, hF⟩ :=
    SphereSeparation.smoothSchoenfliesThree_iff_smoothSchoenfliesBallFilling.mp hSch f hf
  have hFball : F '' ball (0 : E3) 1 = V := hF.trans hside.symm
  have hFclosed : F '' closedBall (0 : E3) 1 = closure V := by
    calc
      F '' closedBall (0 : E3) 1 = F '' closure (ball (0 : E3) 1) := by
        rw [closure_ball _ one_ne_zero]
      _ = closure (F '' ball (0 : E3) 1) := F.toHomeomorph.image_closure _
      _ = closure V := by rw [hFball]
  let G := F.toPartialDiffeomorph.trans A
  have hGs : closedBall (0 : E3) 1 ⊆ G.source := by
    intro x hx
    exact ⟨mem_univ _, hVs (hFclosed ▸ mem_image_of_mem F hx)⟩
  have hCV : A '' V = C := by
    ext x
    constructor
    · rintro ⟨y, ⟨z, hz, rfl⟩, rfl⟩
      exact (A.right_inv (hCsource hz)).symm ▸ hz
    · intro hx
      exact ⟨A.symm x, mem_image_of_mem _ hx, A.right_inv (hCsource hx)⟩
  have hGC : G '' ball (0 : E3) 1 = C := by
    change (A ∘ F) '' ball (0 : E3) 1 = C
    rw [image_comp, hFball, hCV]
  have hGclosed : G '' closedBall (0 : E3) 1 = closure C := by
    change (A ∘ F) '' closedBall (0 : E3) 1 = closure C
    rw [image_comp, hFclosed, hcl]
    ext x
    constructor
    · rintro ⟨y, ⟨z, hz, rfl⟩, rfl⟩
      exact (A.right_inv (hsource hz)).symm ▸ hz
    · intro hx
      exact ⟨A.symm x, mem_image_of_mem _ hx, A.right_inv (hsource hx)⟩
  refine ⟨G, hGs, hGC, hGclosed, ?_⟩
  have hFsphere : F '' sphere (0 : E3) 1 = frontier V := by
    calc
      F '' sphere (0 : E3) 1 = F '' frontier (ball (0 : E3) 1) := by
        rw [frontier_ball _ one_ne_zero]
      _ = frontier (F '' ball (0 : E3) 1) := F.toHomeomorph.image_frontier _
      _ = frontier V := by rw [hFball]
  change (A ∘ F) '' sphere (0 : E3) 1 = range e
  rw [image_comp, hFsphere, hfrontV, hfront]
  ext x
  constructor
  · rintro ⟨y, ⟨z, hz, rfl⟩, rfl⟩
    exact (A.right_inv (hesource hz)).symm ▸ hz
  · intro hx
    exact ⟨A.symm x, mem_image_of_mem _ hx, A.right_inv (hesource hx)⟩

end DifferentialGeometry.Topology.ThreeManifold
