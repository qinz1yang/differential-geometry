/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.BoundaryAnnulusEmbedding

open Set Topology Manifold
open scoped Manifold ContDiff

namespace DifferentialGeometry.Topology.PiecewiseLinear

open DifferentialGeometry.Integral.DivergenceTheorem.WithBoundary

theorem isSmoothEmbedding_coe_of_boundary_surface_openPartialHomeomorph
    {M : Type} [TopologicalSpace M] [ChartedSpace (EuclideanHalfSpace 3) M]
    [IsManifold (𝓡∂ 3) ∞ M] {N : Type*} [TopologicalSpace N]
    [ChartedSpace (EuclideanSpace ℝ (Fin 2)) N] [IsManifold (𝓡 2) ∞ N]
    (F : OpenPartialHomeomorph N (BoundaryManifold (𝓡∂ 3) M)) (hFs : F.source = univ)
    (hF : ContMDiffOn (𝓡 2) (HasSmoothBoundary.boundaryI (I := 𝓡∂ 3)) ∞ F univ)
    (hFi : ContMDiffOn (HasSmoothBoundary.boundaryI (I := 𝓡∂ 3)) (𝓡 2) ∞ F.symm F.target) :
    IsSmoothEmbedding (𝓡 2) (𝓡∂ 3) ∞ (fun x => (F x : M)) := by
  classical
  let _ : Nonempty (HasSmoothBoundary.boundaryH (I := 𝓡∂ 3)) :=
    ⟨(0 : EuclideanSpace ℝ (Fin 2))⟩
  refine ⟨?_, IsEmbedding.subtypeVal.comp (F.isOpenEmbedding hFs).isEmbedding⟩
  apply IsImmersionOfComplement.isImmersion (F := ℝ)
  intro x
  set y := F x with hydef
  let b := chartAt (HasSmoothBoundary.boundaryH (I := 𝓡∂ 3)) y
  have hb : b ∈ IsManifold.maximalAtlas (HasSmoothBoundary.boundaryI (I := 𝓡∂ 3)) ∞
      (BoundaryManifold (𝓡∂ 3) M) := IsManifold.chart_mem_maximalAtlas y
  have hbeq : b = BoundaryManifold.boundaryChart (I := 𝓡∂ 3) y :=
    BoundaryManifold.defaultBoundaryChart_eq_boundaryChart (I := 𝓡∂ 3) y
  let ψ := chartAt (EuclideanHalfSpace 3) (y : M)
  let α : OpenPartialHomeomorph N (EuclideanSpace ℝ (Fin 2)) := F.trans b
  have hαs : α.source = F.source ∩ F ⁻¹' b.source := OpenPartialHomeomorph.trans_source F b
  have hαt : α.target = b.target ∩ b.symm ⁻¹' F.target := OpenPartialHomeomorph.trans_target F b
  have hxα : x ∈ α.source := by
    rw [hαs]
    exact ⟨hFs ▸ mem_univ x, mem_chart_source _ y⟩
  have hbsm : ContMDiffOn (HasSmoothBoundary.boundaryI (I := 𝓡∂ 3))
      (HasSmoothBoundary.boundaryI (I := 𝓡∂ 3)) ∞ b b.source :=
    contMDiffOn_of_mem_maximalAtlas hb
  have hbsi : ContMDiffOn (HasSmoothBoundary.boundaryI (I := 𝓡∂ 3))
      (HasSmoothBoundary.boundaryI (I := 𝓡∂ 3)) ∞ b.symm b.target :=
    contMDiffOn_symm_of_mem_maximalAtlas hb
  have hαmax : α ∈ IsManifold.maximalAtlas (𝓡 2) ∞ N := by
    refine DifferentialGeometry.OpenPartialHomeomorph.mem_maximalAtlas_of_contMDiffOn α ?_ ?_
    · rw [hαs]
      exact hbsm.comp (hF.mono (subset_univ _)) fun z hz => hz.2
    · rw [hαt]
      exact hFi.comp (hbsi.mono inter_subset_left) fun u hu => hu.2
  have hψmax : ψ ∈ IsManifold.maximalAtlas (𝓡∂ 3) ∞ M := IsManifold.chart_mem_maximalAtlas _
  have hsrcM : ∀ p : BoundaryManifold (𝓡∂ 3) M, p ∈ b.source → (p : M) ∈ ψ.source := by
    intro p hp
    rw [hbeq] at hp
    exact hp
  refine IsImmersionAtOfComplement.mk_of_charts (normalFirstEquiv 2) α ψ hxα
    (hsrcM y (mem_chart_source _ y)) hαmax hψmax (fun z hz => ?_) fun u hu => ?_
  · rw [hαs] at hz
    exact hsrcM _ hz.2
  · have hu' : u ∈ α.target := hu.2
    rw [hαt] at hu'
    obtain ⟨hwb, hwF⟩ := hu'
    have hFeq : F (α.symm u) = b.symm u := by
      change F (F.symm (b.symm u)) = _
      rw [F.right_inv hwF]
    have hmemψ : ((b.symm u : BoundaryManifold (𝓡∂ 3) M) : M) ∈ ψ.source :=
      hsrcM _ (b.map_target hwb)
    have hincl := BoundaryManifold.inclH_boundaryChart_apply (I := 𝓡∂ 3) y (b.symm u) hmemψ
    rw [← hbeq, b.right_inv hwb] at hincl
    change (𝓡∂ 3) (ψ ((F (α.symm u)) : M)) = normalFirstEquiv 2 (u, 0)
    rw [hFeq, ← hincl]
    exact inclEuclidean_three_eq_normalFirstEquiv u

theorem isSmoothEmbedding_coe_of_diffeomorph_boundary_opens
    {M : Type} [TopologicalSpace M] [ChartedSpace (EuclideanHalfSpace 3) M]
    [IsManifold (𝓡∂ 3) ∞ M] {N : Type*} [TopologicalSpace N] [Nonempty N]
    [ChartedSpace (EuclideanSpace ℝ (Fin 2)) N] [IsManifold (𝓡 2) ∞ N]
    (W : TopologicalSpace.Opens (BoundaryManifold (𝓡∂ 3) M))
    (D : N ≃ₘ⟮𝓡 2, HasSmoothBoundary.boundaryI (I := 𝓡∂ 3)⟯ W) :
    IsSmoothEmbedding (𝓡 2) (𝓡∂ 3) ∞ (fun x => ((D x : BoundaryManifold (𝓡∂ 3) M) : M)) := by
  classical
  have hne : Nonempty W := ⟨D (Classical.arbitrary N)⟩
  let F : OpenPartialHomeomorph N (BoundaryManifold (𝓡∂ 3) M) :=
    D.toHomeomorph.toOpenPartialHomeomorph.trans (W.openPartialHomeomorphSubtypeCoe hne)
  have hFs : F.source = univ := eq_univ_of_forall fun _ => ⟨trivial, trivial⟩
  have hF : ContMDiffOn (𝓡 2) (HasSmoothBoundary.boundaryI (I := 𝓡∂ 3)) ∞ F univ :=
    (contMDiff_subtype_val.comp D.contMDiff).contMDiffOn
  have hFi : ContMDiffOn (HasSmoothBoundary.boundaryI (I := 𝓡∂ 3)) (𝓡 2) ∞ F.symm F.target := by
    intro y hy
    have hyW : y ∈ W := by
      have h := hy.1
      rwa [TopologicalSpace.Opens.openPartialHomeomorphSubtypeCoe_target] at h
    have hfun : (fun z : W => F.symm z) = D.symm := by
      funext z
      change D.symm ((W.openPartialHomeomorphSubtypeCoe hne).symm z) = D.symm z
      exact congrArg D.symm ((W.openPartialHomeomorphSubtypeCoe hne).left_inv (mem_univ z))
    have h1 : ContMDiffAt (HasSmoothBoundary.boundaryI (I := 𝓡∂ 3)) (𝓡 2) ∞
        (fun z : W => F.symm z) ⟨y, hyW⟩ := by
      rw [hfun]
      exact D.symm.contMDiff.contMDiffAt
    exact (contMDiffAt_subtype_iff.mp h1).contMDiffWithinAt
  exact isSmoothEmbedding_coe_of_boundary_surface_openPartialHomeomorph F hFs hF hFi

end DifferentialGeometry.Topology.PiecewiseLinear
