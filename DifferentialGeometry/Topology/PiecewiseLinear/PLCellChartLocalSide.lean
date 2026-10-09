/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.BicollarLocalSide
import DifferentialGeometry.Topology.PiecewiseLinear.BicollarEmbedding
import DifferentialGeometry.Topology.PiecewiseLinear.ChartImagePLCell
import DifferentialGeometry.Topology.PiecewiseLinear.PLCellOnClosure

open Set Topology

namespace DifferentialGeometry.Topology.PiecewiseLinear

local notation "E3" => EuclideanSpace ℝ (Fin 3)

variable {M : Type*} [TopologicalSpace M] [T2Space M] [ChartedSpace E3 M]
  {c : OpenPartialHomeomorph M E3}

theorem IsPLCellOn.isBicollared_frontier_in_chart {V VB : Set M} (hV : IsPLCellOn 3 V VB)
    (hc : c ∈ (plGroupoid 3).maximalAtlas M) (hVc : V ⊆ c.source) :
    IsBicollared (frontier V) := by
  obtain ⟨hVi, hVfr⟩ := hV.isPLBall_image_chart hc hVc
  have hS : IsPLSphere 2 (frontier (c '' V)) := hVi.isPLSphere_frontier
  have hpoly : IsPolyhedralManifold (n := 3) 2 (frontier (c '' V)) := by
    have h := isPolyhedralSphere_chart_symm_image (chartAt E3 (0 : E3))
      (chart_mem_atlas _ _) hS (by rw [chartAt_self_eq]; exact subset_univ _)
    simpa only [chartAt_self_eq, OpenPartialHomeomorph.refl_symm,
      OpenPartialHomeomorph.refl_apply, image_id] using h.isPolyhedralManifold
  have hSt : frontier (c '' V) ⊆ c.target := by
    intro z hz
    obtain ⟨x, hx, rfl⟩ := hVi.isPolyhedron.isClosed.frontier_subset hz
    exact c.map_source (hVc hx)
  have hnhds : c.target ∈ 𝓝ˢ (frontier (c '' V)) :=
    subset_interior_iff_mem_nhdsSet.mp (c.open_target.interior_eq.symm ▸ hSt)
  have hi : IsOpenEmbedding (fun x : c.target => c.symm x) := by
    apply IsOpenEmbedding.of_continuous_injective_isOpenMap c.continuousOn_symm.domRestrict
      (fun x y hxy => Subtype.ext (c.symm.injOn x.2 y.2 hxy))
    intro U hU
    change IsOpen ((c.symm ∘ Subtype.val) '' U)
    rw [image_comp]
    apply c.isOpen_image_symm_of_subset_target (c.open_target.isOpenMap_subtype_val U hU)
    rintro _ ⟨x, _, rfl⟩
    exact x.2
  have hbi := hpoly.isBicollared_image (hpoly.isTwoSided hS.isConnected) hnhds hi
  have heq : c.symm '' frontier (c '' V) = frontier V := by
    rw [← hVfr, hV.boundary_eq_frontier]
    exact c.symm_image_image_of_subset_source (hV.isCompact.isClosed.frontier_subset.trans hVc)
  rwa [heq] at hbi

theorem IsPLCellOn.exists_mem_nhds_of_inter_frontier_subset_in_chart {V VB R RB O : Set M}
    (hV : IsPLCellOn 3 V VB) (hR : IsPLCellOn 3 R RB)
    (hc : c ∈ (plGroupoid 3).maximalAtlas M) (hVc : V ⊆ c.source)
    (hO : IsOpen O) (hRO : O ∩ frontier R ⊆ V)
    (hint : Disjoint (interior R) (interior V)) {y : M} (hyO : y ∈ O)
    (hyR : y ∈ R) (hyV : y ∈ frontier V) :
    ∃ U ∈ 𝓝 y, U ∩ frontier V ⊆ R ∧ U \ V ⊆ interior R := by
  have hbi := hV.isBicollared_frontier_in_chart hc hVc
  let _ : LocallyConnectedSpace M := ChartedSpace.locallyConnectedSpace E3 M
  let _ : LocallyConnectedSpace (frontier V) := hbi.locallyConnectedSpace
  have hVreg : V ⊆ closure (interior V) := by
    rw [← hV.sdiff_boundary_eq_interior, hV.closure_sdiff_boundary]
  have hyRc : y ∈ closure (interior R) := by
    rw [← hR.sdiff_boundary_eq_interior, hR.closure_sdiff_boundary]
    exact hyR
  exact hbi.exists_mem_nhds_of_inter_frontier_subset hV.isCompact.isClosed hR.isCompact.isClosed
    hVreg hO hRO hint hyO hyRc hyV

end DifferentialGeometry.Topology.PiecewiseLinear
