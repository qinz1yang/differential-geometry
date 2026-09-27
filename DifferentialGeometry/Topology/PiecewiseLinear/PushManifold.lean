/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.SchoenfliesManifold
import DifferentialGeometry.Topology.PiecewiseLinear.PLSchoenflies
import DifferentialGeometry.Topology.PiecewiseLinear.ChartPolyhedron
import DifferentialGeometry.Topology.PiecewiseLinear.ChartConjugate
import DifferentialGeometry.Topology.PiecewiseLinear.PolyhedralBallBoundary

open Set
open scoped Manifold

namespace DifferentialGeometry.Topology.PiecewiseLinear

universe u

variable {X : Type u} [TopologicalSpace X] [T2Space X]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) X] [HasGroupoid X (plGroupoid 3)]

theorem exists_isPL_homeomorph_push_disk_in_chart
    {C D N : Set X} (hC : IsPolyhedralBall (n := 3) 3 C)
    (hD : IsPolyhedralBall (n := 3) 2 D) (hDC : D ⊆ frontier C)
    (e : OpenPartialHomeomorph X (EuclideanSpace ℝ (Fin 3)))
    (he : e ∈ atlas (EuclideanSpace ℝ (Fin 3)) X) (hCe : C ⊆ e.source)
    (T : PolyhedronIn 3 X N)
    (hCN : C \ polyhedralBoundary 2 D hD.isPolyhedralManifoldWithBoundary ⊆ interior N) :
    ∃ h : X ≃ₜ X, IsPL 3 3 h ∧ IsPL 3 3 h.symm ∧
      h '' D = closure (frontier C \ D) ∧ EqOn h id Nᶜ := by
  have hcomp := hC.isPolyhedralManifoldWithBoundary.isCompact
  have hDe : D ⊆ e.source := hDC.trans (hcomp.isClosed.frontier_subset.trans hCe)
  have hC' := hC.isPLBall_chart_image e he hCe
  have hD' := hD.isPLBall_chart_image e he hDe
  have hpush := hasPushProperty_of_isSimplyEmbedded_frontier hC'
    hC'.isPLSphere_frontier.isSimplyEmbedded
  have hDC' : e '' D ⊆ frontier (e '' C) := by
    rw [← hC.image_frontier_chart e he hCe]
    exact image_mono hDC
  obtain ⟨q, hq, hqJ⟩ := hD.exists_isPLHomeomorphOn_chart_image_boundary e he hDe
  obtain ⟨P, hP, hCP, hPt, hPN⟩ :=
    T.piece.exists_isPolyhedron_chart_neighborhood e he hcomp hCe hCN
  rw [← hqJ] at hCP
  obtain ⟨k, hk, hkD, hkfix⟩ := (hpush.2 _ hD' hDC').2.2.2 q hq P hP hCP
  let H := e.conjugateHomeomorph k hP.isCompact hPt hkfix
  have hH : IsPL 3 3 H := isPL_conjugateHomeomorph e
    ((plGroupoid 3).subset_maximalAtlas he) k hk.isPiecewiseAffineOn hP.isCompact hPt hkfix
  refine ⟨H, hH, isPL_symm_of_homeomorph hH, ?_, ?_⟩
  · have hcl : closure (frontier C \ D) ⊆ C :=
      closure_minimal (sdiff_subset.trans hcomp.isClosed.frontier_subset) hcomp.isClosed
    have hclosedImage := image_closure_of_isCompact
      (hcomp.of_isClosed_subset isClosed_closure hcl) (e.continuousOn.mono (hcl.trans hCe))
    have hdiff : e '' (frontier C \ D) = frontier (e '' C) \ e '' D := by
      rw [(e.injOn.mono (hcomp.isClosed.frontier_subset.trans hCe)).image_sdiff_subset hDC,
        hC.image_frontier_chart e he hCe]
    calc
      H '' D = e.symm '' (k '' (e '' D)) := by
        rw [image_image, image_image]
        apply EqOn.image_eq
        intro x hx
        exact e.conjugateMap_of_mem k (hDe hx)
      _ = e.symm '' closure (frontier (e '' C) \ e '' D) := congrArg (Set.image e.symm) hkD
      _ = closure (frontier C \ D) := by
        rw [← hdiff, ← hclosedImage]
        exact e.symm_image_image_of_subset_source (hcl.trans hCe)
  · intro x hx
    exact e.conjugateMap_eqOn_compl hkfix (fun hxP => hx (hPN hxP))

theorem exists_isPL_homeomorph_push_between_disks_in_chart
    {C D₁ D₂ N : Set X} (hC : IsPolyhedralBall (n := 3) 3 C)
    (hD₁ : IsPolyhedralBall (n := 3) 2 D₁) (hD₂ : IsPolyhedralBall (n := 3) 2 D₂)
    (hcover : D₁ ∪ D₂ = frontier C)
    (hinter₁ : D₁ ∩ D₂ = polyhedralBoundary 2 D₁ hD₁.isPolyhedralManifoldWithBoundary)
    (hinter₂ : D₁ ∩ D₂ = polyhedralBoundary 2 D₂ hD₂.isPolyhedralManifoldWithBoundary)
    (e : OpenPartialHomeomorph X (EuclideanSpace ℝ (Fin 3)))
    (he : e ∈ atlas (EuclideanSpace ℝ (Fin 3)) X) (hCe : C ⊆ e.source)
    (T : PolyhedronIn 3 X N) (hCN : C \ (D₁ ∩ D₂) ⊆ interior N) :
    ∃ h : X ≃ₜ X, IsPL 3 3 h ∧ IsPL 3 3 h.symm ∧ h '' D₁ = D₂ ∧ EqOn h id Nᶜ := by
  have hD₁C : D₁ ⊆ frontier C := subset_union_left.trans hcover.le
  rw [hinter₁] at hCN
  obtain ⟨h, hh, hhi, himage, hfix⟩ :=
    exists_isPL_homeomorph_push_disk_in_chart hC hD₁ hD₁C e he hCe T hCN
  refine ⟨h, hh, hhi, himage.trans ?_, hfix⟩
  have hdiff : frontier C \ D₁ = D₂ \ (D₁ ∩ D₂) := by
    rw [← hcover]
    ext x
    simp only [mem_sdiff, mem_union, mem_inter_iff]
    tauto
  rw [hdiff, hinter₂]
  exact hD₂.closure_sdiff_polyhedralBoundary

theorem exists_isPL_homeomorph_push_between_disks_in_openStar
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    (K : Geometry.SimplicialComplex ℝ E) [Finite K.faces] (hK : IsCombinatorialManifold 3 K)
    {p : E} (hp : {p} ∈ K.faces) :
    letI := combinatorialChartedSpace K hK
    ∀ {C D₁ D₂ N : Set K.space}, IsPolyhedralBall (n := 3) 3 C →
      ∀ (hD₁ : IsPolyhedralBall (n := 3) 2 D₁) (hD₂ : IsPolyhedralBall (n := 3) 2 D₂),
      D₁ ∪ D₂ = frontier C →
      D₁ ∩ D₂ = polyhedralBoundary 2 D₁ hD₁.isPolyhedralManifoldWithBoundary →
      D₁ ∩ D₂ = polyhedralBoundary 2 D₂ hD₂.isPolyhedralManifoldWithBoundary →
      C ⊆ Subtype.val ⁻¹' openStar K p → PolyhedronIn 3 K.space N →
      C \ (D₁ ∩ D₂) ⊆ interior N →
      ∃ h : K.space ≃ₜ K.space,
        IsPL 3 3 h ∧ IsPL 3 3 h.symm ∧ h '' D₁ = D₂ ∧ EqOn h id Nᶜ := by
  let _ := combinatorialChartedSpace K hK
  let _ := combinatorialChartedSpace_hasGroupoid K hK
  intro C D₁ D₂ N hC hD₁ hD₂ hcover hinter₁ hinter₂ hCe T hCN
  let e := vertexChart K hp (hK.isPLSphere_link hp)
  have he : e ∈ atlas (EuclideanSpace ℝ (Fin 3)) K.space := ⟨⟨p, hp⟩, rfl⟩
  exact exists_isPL_homeomorph_push_between_disks_in_chart hC hD₁ hD₂
    hcover hinter₁ hinter₂ e he hCe T hCN

end DifferentialGeometry.Topology.PiecewiseLinear
