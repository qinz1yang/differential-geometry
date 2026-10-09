/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.Homology.CompactChainSupport
import DifferentialGeometry.Topology.PiecewiseLinear.CompactSubsurfaceNeighborhood
import DifferentialGeometry.Topology.PiecewiseLinear.NonseparatingPolygonHomologySummand
import DifferentialGeometry.Topology.PiecewiseLinear.TorusSubsurfaceHomologyRange
import DifferentialGeometry.Topology.PiecewiseLinear.SolidTorusSeparatingSubsurface

open Set Topology
open scoped BigOperators ContinuousMap

namespace DifferentialGeometry.Topology.PiecewiseLinear.SpineCarrier

local notation "E3" => EuclideanSpace ℝ (Fin 3)

private noncomputable def firstHomologyInclusion {A B : Set E3} (h : A ⊆ B) :
    integralSingularHomology 1 A →ₗ[ℤ] integralSingularHomology 1 B :=
  integralSingularHomologyMap 1 ⟨inclusion h, continuous_inclusion h⟩

private theorem firstHomologyInclusion_comp {A B C : Set E3} (hAB : A ⊆ B) (hBC : B ⊆ C)
    (a : integralSingularHomology 1 A) :
    firstHomologyInclusion hBC (firstHomologyInclusion hAB a) =
      firstHomologyInclusion (hAB.trans hBC) a := by
  rw [firstHomologyInclusion, firstHomologyInclusion, ← LinearMap.comp_apply,
    ← integralSingularHomologyMap_comp]
  rfl

private theorem exists_compact_firstHomology_preimage {A : Set E3}
    (a : integralSingularHomology 1 A) :
    ∃ C : Set E3, IsCompact C ∧ ∃ hCA : C ⊆ A,
      ∃ b : integralSingularHomology 1 C, firstHomologyInclusion hCA b = a := by
  obtain ⟨c, rfl⟩ := integralOneCycleClass_surjective a
  let z := (integralSingularChainMap (singularSubspaceInclusion A)).f 1 c.val
  have hz : z ∈ integralSingularChainsIn 1 A := by
    rw [integralSingularChainsIn_eq_range]
    exact ⟨c.val, rfl⟩
  obtain ⟨C, hC, hCA, hzC⟩ := exists_isCompact_support_of_mem_integralSingularChainsIn 1 hz
  rw [integralSingularChainsIn_eq_range] at hzC
  obtain ⟨d, hd⟩ := hzC
  have hdc : (integralSingularChains C).d 1 0 d = 0 :=
    integralSingularChains_d_eq_zero_of_inclusion (by
      rw [hd]
      exact integralSingularChains_d_inclusion_eq_zero c.property)
  let dC : integralSingularCycles 0 C := ⟨d, hdc⟩
  refine ⟨C, hC, hCA, integralOneCycleClass dC, ?_⟩
  apply integralOneCycleClass_map
  apply integralSingularChainInclusion_injective 1 A
  rw [integralSingularChainMap_inclusion_apply]
  exact hd

private theorem exists_oriented_cycle_multiple {G : Set E3} (hG : IsPLSphere 1 G)
    (a : integralSingularHomology 1 G) :
    ∃ c : integralSingularCycles 0 G,
      AddSubgroup.zmultiples (integralOneCycleClass c) = ⊤ ∧
        ∃ m : ℤ, a = m • integralOneCycleClass c := by
  obtain ⟨e⟩ := hG.nonempty_integralSingularHomologyOne_equiv_int
  obtain ⟨c, hc⟩ := integralOneCycleClass_surjective (e.symm 1)
  have hmul (b : integralSingularHomology 1 G) : b = e b • integralOneCycleClass c := by
    apply e.injective
    simp [hc]
  refine ⟨c, ?_, e a, hmul a⟩
  apply top_unique
  intro b _
  exact AddSubgroup.mem_zmultiples_iff.mpr ⟨e b, (hmul b).symm⟩

private theorem not_mem_closure_sdiff_of_mem_nhdsWithin {T W : Set E3} {x : E3}
    (hx : W ∈ 𝓝[T] x) : x ∉ closure (T \ W) := by
  obtain ⟨V, hV, hxV, hVT⟩ := mem_nhdsWithin.mp hx
  intro hcl
  obtain ⟨y, hyV, hyT, hyW⟩ := mem_closure_iff.mp hcl V hV hxV
  exact hyW (hVT ⟨hyV, hyT⟩)

private theorem firstHomologyInclusion_range_eq_of_eq {A B S : Set E3}
    (hAB : A = B) (hAS : A ⊆ S) (hBS : B ⊆ S) :
    LinearMap.range (firstHomologyInclusion hAS) =
      LinearMap.range (firstHomologyInclusion hBS) := by
  subst B
  rfl

private theorem exists_polygon_of_annular_compact_support {S U C K : Set E3}
    (hS : IsCombinatorialSolidTorus S) (hU : IsOpen U) (hTS : frontier S ∩ U ⊆ S)
    (hC : IsCompact C) (hCTU : C ⊆ frontier S ∩ U)
    (a : integralSingularHomology 1 S)
    (haC : a ∈ LinearMap.range (firstHomologyInclusion (hCTU.trans hTS))) (haz : a ≠ 0)
    (hK : IsPLSphere 1 K) (hKT : K ⊆ frontier S)
    (hKsep : IsPreconnected (frontier S \ K)) (hCK : Disjoint C K) :
    ∃ (G : Set E3) (_ : IsPLSphere 1 G) (hGU : G ⊆ frontier S ∩ U),
      a ∈ LinearMap.range (firstHomologyInclusion (hGU.trans hTS)) := by
  have hT : IsPLTorus (frontier S) := hS.isPLTorus_frontier
  obtain ⟨L, hLfin, hL, -, hLT⟩ := hT.exists_combinatorial_triangulation
  let _ : Finite L.faces := hLfin.to_subtype
  have hCL : C ⊆ L.space := hLT.symm ▸ (hCTU.trans inter_subset_left)
  have hCUK : C ⊆ U \ K := fun x hx =>
    ⟨(hCTU hx).2, disjoint_left.mp hCK hx⟩
  obtain ⟨W, hWfin, n, G, -, hWU, hCW, hG, hGdis, hfr⟩ :=
    hL.exists_compact_subsurface_neighborhood hC hCL (hU.sdiff hK.isPolyhedron.isClosed) hCUK
  let _ : Finite W.faces := hWfin.to_subtype
  have hCWsub : C ⊆ W.space := fun x hx => mem_of_mem_nhdsWithin (hCL hx) (hCW x hx)
  rw [hLT] at hWU hfr
  have hWT : W.space ⊆ frontier S := hWU.trans inter_subset_left
  have hWTU : W.space ⊆ frontier S ∩ U := fun x hx => ⟨(hWU hx).1, (hWU hx).2.1⟩
  have hGW : ∀ i, G i ⊆ W.space := fun i x hx =>
    ((hfr.symm ▸ (mem_iUnion.mpr ⟨i, hx⟩)) : x ∈ W.space ∩ closure
      (frontier S \ W.space)).1
  have hGT : ∀ i, G i ⊆ frontier S := fun i => (hGW i).trans hWT
  have hGKU : ∀ i, G i ⊆ frontier S ∩ U := fun i => (hGW i).trans hWTU
  have hWK : Disjoint W.space K := disjoint_left.mpr fun x hx hxK => (hWU hx).2.2 hxK
  have hGK : ∀ i, Disjoint (G i) K := fun i => hWK.mono_left (hGW i)
  have himage : id '' frontier S ⊆ S := by
    simpa only [image_id] using hS.isPolyhedron.isClosed.frontier_subset
  have hWr : LinearMap.range (integralSingularHomologyMap 1
      (⟨inclusion ((image_mono hWT).trans himage), continuous_inclusion _⟩ :
        C(id '' W.space, S))) =
      LinearMap.range (firstHomologyInclusion (hWTU.trans hTS)) :=
    firstHomologyInclusion_range_eq_of_eq (image_id W.space) _ _
  have hGr (i : Fin n) : LinearMap.range (integralSingularHomologyMap 1
      (⟨inclusion ((image_mono (hGT i)).trans himage), continuous_inclusion _⟩ :
        C(id '' G i, S))) =
      LinearMap.range (firstHomologyInclusion ((hGKU i).trans hTS)) :=
    firstHomologyInclusion_range_eq_of_eq (image_id (G i)) _ _
  have haW : a ∈ LinearMap.range (firstHomologyInclusion (hWTU.trans hTS)) := by
    obtain ⟨b, rfl⟩ := haC
    refine ⟨firstHomologyInclusion hCWsub b, ?_⟩
    exact firstHomologyInclusion_comp hCWsub (hWTU.trans hTS) b
  rcases hT.range_integralSingularHomologyMap_le_or_eq_bot_of_disjoint hK hKT hKsep
    hG hGT hGdis hGK hWT (isPolyhedron_space W).isClosed hWK hfr.subset
    (φ := id) continuousOn_id (fun _ _ _ _ h => h) himage with ⟨i, hi⟩ | hbot
  · rw [hWr, hGr i] at hi
    exact ⟨G i, hG i, hGKU i, hi haW⟩
  · rw [hWr] at hbot
    rw [hbot] at haW
    exact (haz haW).elim

theorem exists_disjoint_oriented_polygons_of_nonzero_cycle {S U : Set E3}
    (hS : IsCombinatorialSolidTorus S) (hU : IsOpen U)
    (hTS : frontier S ∩ U ⊆ S) (c : integralSingularCycles 0 (frontier S ∩ U : Set E3))
    (hcnz : firstHomologyInclusion hTS (integralOneCycleClass c) ≠ 0) :
    ∃ (n : ℕ) (G : Fin (n + 1) → Set E3) (_hG : ∀ i, IsPLSphere 1 (G i))
      (hGU : ∀ i, G i ⊆ frontier S ∩ U)
      (cG : ∀ i, integralSingularCycles 0 (G i)) (m : Fin (n + 1) → ℤ),
      Pairwise (fun i j => Disjoint (G i) (G j)) ∧
        (∀ i, AddSubgroup.zmultiples (integralOneCycleClass (cG i)) = ⊤) ∧
          firstHomologyInclusion hTS (integralOneCycleClass c) =
            ∑ i, m i • firstHomologyInclusion ((hGU i).trans hTS)
              (integralOneCycleClass (cG i)) := by
  classical
  let a := firstHomologyInclusion hTS (integralOneCycleClass c)
  obtain ⟨C, hC, hCTU, b, hb⟩ := exists_compact_firstHomology_preimage (integralOneCycleClass c)
  have hab : firstHomologyInclusion (hCTU.trans hTS) b = a := by
    rw [← firstHomologyInclusion_comp hCTU hTS, hb]
  have haC : a ∈ LinearMap.range (firstHomologyInclusion (hCTU.trans hTS)) := ⟨b, hab⟩
  have haz : a ≠ 0 := hcnz
  have hT : IsPLTorus (frontier S) := hS.isPLTorus_frontier
  obtain ⟨L, hLfin, hL, -, hLT⟩ := hT.exists_combinatorial_triangulation
  let _ : Finite L.faces := hLfin.to_subtype
  have hCL : C ⊆ L.space := hLT.symm ▸ (hCTU.trans inter_subset_left)
  obtain ⟨W, hWfin, k, B, -, hWU, hCW, hB, hBdis, hfr⟩ :=
    hL.exists_compact_subsurface_neighborhood hC hCL hU (hCTU.trans inter_subset_right)
  let _ : Finite W.faces := hWfin.to_subtype
  rw [hLT] at hWU hCW hfr
  have hCWsub : C ⊆ W.space := fun x hx => mem_of_mem_nhdsWithin (hCTU hx).1 (hCW x hx)
  have hBW : ∀ i, B i ⊆ W.space := fun i x hx =>
    ((hfr.symm ▸ (mem_iUnion.mpr ⟨i, hx⟩)) : x ∈ W.space ∩ closure
      (frontier S \ W.space)).1
  have hWT : W.space ⊆ frontier S := hWU.trans inter_subset_left
  have hBT : ∀ i, B i ⊆ frontier S := fun i => (hBW i).trans hWT
  have hpolygon : ∃ (G : Set E3) (_ : IsPLSphere 1 G) (hGU : G ⊆ frontier S ∩ U),
      a ∈ LinearMap.range (firstHomologyInclusion (hGU.trans hTS)) := by
    by_cases hex : ∃ i, IsPreconnected (frontier S \ B i)
    · obtain ⟨i, hi⟩ := hex
      have hCB : Disjoint C (B i) := by
        apply disjoint_left.mpr
        intro x hxC hxB
        have hxfr : x ∈ W.space ∩ closure (frontier S \ W.space) :=
          hfr.symm ▸ mem_iUnion.mpr ⟨i, hxB⟩
        exact not_mem_closure_sdiff_of_mem_nhdsWithin (hCW x hxC) hxfr.2
      exact exists_polygon_of_annular_compact_support hS hU hTS hC hCTU a haC haz
        (hB i) (hBT i) hi hCB
    · have hsep : ∀ i, ¬ IsPreconnected (frontier S \ B i) := fun i hi => hex ⟨i, hi⟩
      rcases hS.exists_polygon_carrier_or_range_eq_bot_of_separating_boundary
        hWT (isPolyhedron_space W).isClosed hB hBW hBdis hfr.subset hsep with
        ⟨G, hG, hGW, hGS⟩ | hzero
      · have hGU : G ⊆ frontier S ∩ U := hGW.trans hWU
        exact ⟨G, hG, hGU, hGS.2 (hGU.trans hTS) a⟩
      · have haW : a ∈ LinearMap.range (firstHomologyInclusion (hWU.trans hTS)) := by
          refine ⟨firstHomologyInclusion hCWsub b, ?_⟩
          exact (firstHomologyInclusion_comp hCWsub (hWU.trans hTS) b).trans hab
        change LinearMap.range (firstHomologyInclusion (hWU.trans hTS)) = ⊥ at hzero
        rw [hzero] at haW
        exact (haz haW).elim
  obtain ⟨G, hG, hGU, d, hd⟩ := hpolygon
  obtain ⟨cG, hgen, m, hm⟩ := exists_oriented_cycle_multiple hG d
  refine ⟨0, fun _ => G, fun _ => hG, fun _ => hGU, fun _ => cG, fun _ => m, ?_,
    fun _ => hgen, ?_⟩
  · intro i j hij
    exact (hij (Fin.ext (by omega))).elim
  · change a = ∑ _i : Fin 1,
      m • firstHomologyInclusion (hGU.trans hTS) (integralOneCycleClass cG)
    rw [Fin.sum_univ_one, ← hd, hm]
    exact map_zsmul (firstHomologyInclusion (hGU.trans hTS)).toAddMonoidHom m _

end DifferentialGeometry.Topology.PiecewiseLinear.SpineCarrier
