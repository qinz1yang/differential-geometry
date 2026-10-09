/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.Homology.CompactChainSupport
import DifferentialGeometry.Topology.PiecewiseLinear.FirstHomologyCarrying
import DifferentialGeometry.Topology.PiecewiseLinear.GeneralPosition
import DifferentialGeometry.Topology.PiecewiseLinear.MayerVietorisSubcomplexDifference
import DifferentialGeometry.Topology.PiecewiseLinear.SubcomplexComplement
import DifferentialGeometry.Topology.PiecewiseLinear.ExistsGeneralPositionSolidTorusRelative

open Set Topology CategoryTheory

namespace DifferentialGeometry.Topology.PiecewiseLinear

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

private theorem exists_cycle_inter_of_boundary_difference
    {K L M : Geometry.SimplicialComplex ℝ E} [Finite K.faces]
    (hL : L.faces ⊆ K.faces) (hM : M.faces ⊆ K.faces)
    (hcover : K.faces ⊆ L.faces ∪ M.faces)
    (z w : (integralSingularChains E).X 1) (b : (integralSingularChains E).X 2)
    (hz : z ∈ integralSingularChainsIn 1 L.space)
    (hzc : (integralSingularChains E).d 1 0 z = 0)
    (hw : w ∈ integralSingularChainsIn 1 M.space)
    (hwc : (integralSingularChains E).d 1 0 w = 0)
    (hb : b ∈ integralSingularChainsIn 2 K.space)
    (hbd : (integralSingularChains E).d 2 1 b = z - w) :
    ∃ v ∈ integralSingularChainsIn 1 (intersectionComplex L M).space,
      (integralSingularChains E).d 1 0 v = 0 ∧
        ∃ d ∈ integralSingularChainsIn 2 L.space,
          (integralSingularChains E).d 2 1 d = z - v := by
  rw [integralSingularChainsIn_eq_range] at hz hw hb
  obtain ⟨zL, hzL⟩ := hz
  obtain ⟨wM, hwM⟩ := hw
  obtain ⟨bK, hbK⟩ := hb
  let cz : integralSingularCycles 0 L.space :=
    ⟨zL, integralSingularChains_d_eq_zero_of_inclusion (by rw [hzL]; exact hzc)⟩
  let cw : integralSingularCycles 0 M.space :=
    ⟨wM, integralSingularChains_d_eq_zero_of_inclusion (by rw [hwM]; exact hwc)⟩
  let iz := subcomplexInclusion hL
  let iw := subcomplexInclusion hM
  let czK : integralSingularCycles 0 K.space :=
    ⟨_, integralSingularChainMap_mem_integralSingularCycles iz cz⟩
  let cwK : integralSingularCycles 0 K.space :=
    ⟨_, integralSingularChainMap_mem_integralSingularCycles iw cw⟩
  have heq : integralSingularHomologyMap 1 iz (integralOneCycleClass cz) =
      integralSingularHomologyMap 1 iw (integralOneCycleClass cw) := by
    rw [integralOneCycleClass_map iz cz czK rfl, integralOneCycleClass_map iw cw cwK rfl,
      integralOneCycleClass_eq_iff]
    refine ⟨bK, integralSingularChainInclusion_injective 1 K.space ?_⟩
    rw [integralSingularChainMap_boundary, hbK, hbd, map_sub]
    change z - w =
      (integralSingularChainMap (singularSubspaceInclusion K.space)).f 1
        ((integralSingularChainMap
          ⟨inclusion (space_mono_of_faces_subset hL),
            continuous_inclusion (space_mono_of_faces_subset hL)⟩).f 1 zL) -
      (integralSingularChainMap (singularSubspaceInclusion K.space)).f 1
        ((integralSingularChainMap
          ⟨inclusion (space_mono_of_faces_subset hM),
            continuous_inclusion (space_mono_of_faces_subset hM)⟩).f 1 wM)
    rw [integralSingularChainMap_inclusion_apply, integralSingularChainMap_inclusion_apply,
      hzL, hwM]
  obtain ⟨a, ha, _⟩ := exists_mem_inter_of_maps_eq integralSingularCoefficients
    hL hM hcover 1 (integralOneCycleClass cz) (integralOneCycleClass cw) heq
  obtain ⟨cv, rfl⟩ := integralOneCycleClass_surjective a
  let iv := subcomplexInclusion (K := L) (L := intersectionComplex L M) (fun _ hs => hs.1)
  have hJL : (intersectionComplex L M).space ⊆ L.space :=
    space_mono_of_faces_subset (K := L) (L := intersectionComplex L M) (fun _ hs => hs.1)
  let cvL : integralSingularCycles 0 L.space :=
    ⟨_, integralSingularChainMap_mem_integralSingularCycles iv cv⟩
  have hvz : integralOneCycleClass cvL = integralOneCycleClass cz :=
    (integralOneCycleClass_map iv cv cvL rfl).symm.trans ha
  obtain ⟨dL, hdL⟩ := (integralOneCycleClass_eq_iff cz cvL).mp hvz.symm
  refine ⟨(integralSingularChainMap
    (singularSubspaceInclusion (intersectionComplex L M).space)).f 1 cv.val, ?_,
    integralSingularChains_d_inclusion_eq_zero cv.property,
    (integralSingularChainMap (singularSubspaceInclusion L.space)).f 2 dL, ?_, ?_⟩
  · rw [integralSingularChainsIn_eq_range]
    exact ⟨cv.val, rfl⟩
  · rw [integralSingularChainsIn_eq_range]
    exact ⟨dL, rfl⟩
  · rw [← integralSingularChainMap_boundary, hdL, map_sub]
    change (integralSingularChainMap (singularSubspaceInclusion L.space)).f 1 zL -
      (integralSingularChainMap (singularSubspaceInclusion L.space)).f 1
        ((integralSingularChainMap
          ⟨inclusion hJL, continuous_inclusion hJL⟩).f 1 cv.val) = _
    rw [integralSingularChainMap_inclusion_apply, hzL]

theorem exists_cycle_frontier_of_boundary_difference {S A : Set E}
    (hS : IsPolyhedron S) (hA : IsOpen A)
    (z w : (integralSingularChains E).X 1) (b : (integralSingularChains E).X 2)
    (hz : z ∈ integralSingularChainsIn 1 (A ∩ S))
    (hzc : (integralSingularChains E).d 1 0 z = 0)
    (hw : w ∈ integralSingularChainsIn 1 (A \ S))
    (hwc : (integralSingularChains E).d 1 0 w = 0)
    (hb : b ∈ integralSingularChainsIn 2 A)
    (hbd : (integralSingularChains E).d 2 1 b = z - w) :
    ∃ v ∈ integralSingularChainsIn 1 (frontier S ∩ A),
      (integralSingularChains E).d 1 0 v = 0 ∧
        ∃ d ∈ integralSingularChainsIn 2 S, (integralSingularChains E).d 2 1 d = z - v := by
  classical
  obtain ⟨Cz, hCz, hCzA, hzC⟩ := exists_isCompact_support_of_mem_integralSingularChainsIn 1 hz
  obtain ⟨Cw, hCw, hCwA, hwC⟩ := exists_isCompact_support_of_mem_integralSingularChainsIn 1 hw
  obtain ⟨Cb, hCb, hCbA, hbC⟩ := exists_isCompact_support_of_mem_integralSingularChainsIn 2 hb
  obtain ⟨P, hP, hCP, hPA⟩ := exists_isPolyhedron_neighborhood ((hCz.union hCw).union hCb) hA
    (union_subset (union_subset (hCzA.trans inter_subset_left)
      (hCwA.trans sdiff_subset)) hCbA)
  have hzP : Cz ⊆ P := (subset_union_left.trans subset_union_left).trans
    (hCP.trans interior_subset)
  have hwP : Cw ⊆ P := (subset_union_right.trans subset_union_left).trans
    (hCP.trans interior_subset)
  have hbP : Cb ⊆ P := subset_union_right.trans (hCP.trans interior_subset)
  obtain ⟨K, hKfin, hKP⟩ := hP.exists_simplicialComplex
  let _ : Finite K.faces := hKfin.to_subtype
  obtain ⟨R, hR, hRfin, hRL⟩ := exists_isSubdivision_restrict_space K (hP.inter hS)
    (inter_subset_left.trans hKP.ge)
  let _ : Finite R.faces := hRfin.to_subtype
  have hRP : R.space = P := hR.space_eq.trans hKP
  let L := restrict R (P ∩ S)
  let M := subcomplexGeneratedBy R L.facesᶜ
  have hL : L.faces ⊆ R.faces := restrict_faces_subset R _
  have hM : M.faces ⊆ R.faces := subcomplexGeneratedBy_faces_subset R _
  have hLS : L.space ⊆ S := hRL.le.trans inter_subset_right
  have hMC : M.space = closure (P \ S) := by
    rw [← closure_space_sdiff_space_eq_subcomplexGeneratedBy R R L subset_rfl hL,
      hRP, hRL]
    congr 1
    exact Set.ext fun x => by simp only [mem_sdiff, mem_inter_iff]; tauto
  have hcover : R.faces ⊆ L.faces ∪ M.faces := by
    intro s hs
    by_cases hsL : s ∈ L.faces
    · exact Or.inl hsL
    · exact Or.inr ⟨s, ⟨hs, hsL⟩, Subset.rfl, R.nonempty_of_mem_faces hs⟩
  have hzL : z ∈ integralSingularChainsIn 1 L.space := by
    apply integralSingularChainsIn_mono 1 _ hzC
    intro x hx
    rw [hRL]
    exact ⟨hzP hx, (hCzA hx).2⟩
  have hwM : w ∈ integralSingularChainsIn 1 M.space := by
    apply integralSingularChainsIn_mono 1 _ hwC
    intro x hx
    rw [hMC]
    exact subset_closure ⟨hwP hx, (hCwA hx).2⟩
  have hbR : b ∈ integralSingularChainsIn 2 R.space := by
    rw [hRP]
    exact integralSingularChainsIn_mono 2 hbP hbC
  obtain ⟨v, hv, hvc, d, hd, hbd⟩ := exists_cycle_inter_of_boundary_difference
    hL hM hcover z w b hzL hzc hwM hwc hbR hbd
  refine ⟨v, integralSingularChainsIn_mono 1 ?_ hv, hvc,
    d, integralSingularChainsIn_mono 2 hLS hd, hbd⟩
  intro x hx
  have hxL := space_mono_of_faces_subset (K := L) (L := intersectionComplex L M)
    (fun _ hs => hs.1) hx
  have hxM := space_mono_of_faces_subset (K := M) (L := intersectionComplex L M)
    (fun _ hs => hs.2) hx
  have hxP : x ∈ P := (hRL.le hxL).1
  refine ⟨?_, hPA hxP⟩
  rw [frontier_eq_closure_inter_closure]
  refine ⟨subset_closure (hLS hxL), ?_⟩
  rw [hMC] at hxM
  exact closure_mono (fun _ hy => hy.2) hxM

namespace SpineCarrier

local notation "E3" => EuclideanSpace ℝ (Fin 3)

theorem exists_frontier_cycle_of_homologous_cycles {S A : Set E3}
    (hS : IsCombinatorialSolidTorus S) (hA : IsOpen A)
    (z w : (integralSingularChains E3).X 1) (b : (integralSingularChains E3).X 2)
    (hz : z ∈ integralSingularChainsIn 1 (A ∩ interior S))
    (hzc : (integralSingularChains E3).d 1 0 z = 0)
    (hw : w ∈ integralSingularChainsIn 1 (A \ S))
    (hwc : (integralSingularChains E3).d 1 0 w = 0)
    (hb : b ∈ integralSingularChainsIn 2 A)
    (hbd : (integralSingularChains E3).d 2 1 b = z - w) :
    ∃ v ∈ integralSingularChainsIn 1 (frontier S ∩ A),
      (integralSingularChains E3).d 1 0 v = 0 ∧
        ∃ d ∈ integralSingularChainsIn 2 S, (integralSingularChains E3).d 2 1 d = z - v := by
  exact exists_cycle_frontier_of_boundary_difference hS.isPolyhedron hA z w b
    (integralSingularChainsIn_mono 1 (inter_subset_inter_right A interior_subset) hz)
    hzc hw hwc hb hbd

end SpineCarrier

end DifferentialGeometry.Topology.PiecewiseLinear
