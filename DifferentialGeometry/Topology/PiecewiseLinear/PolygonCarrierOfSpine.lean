/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.FrontierCycleCut
import DifferentialGeometry.Topology.PiecewiseLinear.MaximalPolygonHomologyImage
import DifferentialGeometry.Topology.PiecewiseLinear.PolygonCycleResolution
import DifferentialGeometry.Topology.PiecewiseLinear.SolidTorusHurewiczOne
import DifferentialGeometry.Topology.PiecewiseLinear.SolidTorusInteriorHomology

open Set Topology
open scoped BigOperators ContinuousMap

namespace DifferentialGeometry.Topology.PiecewiseLinear

local notation "E3" => EuclideanSpace ℝ (Fin 3)

private noncomputable def spineCarrierHomologyInclusion {A B : Set E3} (h : A ⊆ B) :
    integralSingularHomology 1 A →ₗ[ℤ] integralSingularHomology 1 B :=
  integralSingularHomologyMap 1 ⟨inclusion h, continuous_inclusion h⟩

private theorem nonempty_integralFirstHomology_equiv_int {S : Set E3}
    (hS : IsTopologicalSolidTorus S) : Nonempty (integralSingularHomology 1 S ≃+ ℤ) := by
  obtain ⟨φ⟩ := hS
  let D := Metric.closedBall (0 : EuclideanSpace ℝ (Fin 2)) 1
  let C := Metric.sphere (0 : EuclideanSpace ℝ (Fin 2)) 1
  let p : D := ⟨0, by simp [D]⟩
  let e : S ≃ₕ C := φ.toHomotopyEquiv.trans
    ((Homeomorph.prodComm D C).toHomotopyEquiv.trans
      (DifferentialGeometry.HomotopyEquiv.productConvex C (convex_closedBall _ _) p))
  exact ⟨((integralSingularHomologyHomotopyEquiv 1 e).trans
    (integralSphereTopHomologyEquiv 0 (EuclideanSpace ℝ (Fin 2)) (by simp))).toAddEquiv⟩

private theorem carriesFirstHomologyOnto_subset_of_injective {P A S : Set E3}
    (hPS : CarriesFirstHomologyOnto P S) (hPA : P ⊆ A) (hAS : A ⊆ S)
    (hi : Function.Injective (spineCarrierHomologyInclusion hAS)) :
    CarriesFirstHomologyOnto P A := by
  refine ⟨hPA, fun hsub a => ?_⟩
  obtain ⟨p, hp⟩ := hPS.2 (hPA.trans hAS) (spineCarrierHomologyInclusion hAS a)
  refine ⟨p, hi ?_⟩
  change spineCarrierHomologyInclusion hAS (spineCarrierHomologyInclusion hsub p) = _
  rw [spineCarrierHomologyInclusion, spineCarrierHomologyInclusion, ← LinearMap.comp_apply,
    ← integralSingularHomologyMap_comp]
  exact hp

private theorem carriesFirstHomologyOnto_frontier_inter_of_cutting {S A P Q : Set E3}
    (hS : IsCombinatorialSolidTorus S) (hA : IsOpen A)
    (hP : CarriesFirstHomologyOnto P A) (hPS : Disjoint P S)
    (hQ : CarriesFirstHomologyOnto Q S) (hQA : Q ⊆ A ∩ interior S) :
    CarriesFirstHomologyOnto (frontier S ∩ A) S := by
  refine carriesFirstHomologyOnto_of_forall_cycle
    (inter_subset_left.trans hS.isPolyhedron.isClosed.frontier_subset) fun z hz hzc => ?_
  obtain ⟨q, hq, hqc, d, hd, hdq⟩ := hQ.exists_cycle hz hzc
  have hqA := integralSingularChainsIn_mono 1 (hQA.trans inter_subset_left) hq
  obtain ⟨p, hp, hpc, b, hb, hbp⟩ := hP.exists_cycle hqA hqc
  have hPA : P ⊆ A \ S := fun x hx =>
    ⟨hP.1 hx, fun hxS => Set.disjoint_left.mp hPS hx hxS⟩
  obtain ⟨v, hv, hvc, e, he, hev⟩ :=
    SpineCarrier.exists_frontier_cycle_of_homologous_cycles hS hA q p b
    (integralSingularChainsIn_mono 1 hQA hq) hqc
    (integralSingularChainsIn_mono 1 hPA hp) hpc hb hbp
  refine ⟨v, hv, hvc, d + e, Submodule.add_mem _ hd he, ?_⟩
  rw [map_add, hdq, hev]
  abel

private theorem carriesFundamentalGroupOnto_of_firstHomology {S G : Set E3}
    (hS : IsTopologicalSolidTorus S) (hG : IsPathConnected G)
    (hH : CarriesFirstHomologyOnto G S) : CarriesFundamentalGroupOnto G S := by
  refine ⟨hH.1, fun hGS x γ => ?_⟩
  let i : C(G, S) := ⟨inclusion hGS, continuous_inclusion hGS⟩
  let _ : PathConnectedSpace G := isPathConnected_iff_pathConnectedSpace.mp hG
  obtain ⟨a, ha⟩ := hH.2 hGS (hurewiczOne (i x) γ).toAdd
  obtain ⟨β, hβ⟩ := hurewiczOne_surjective x (Multiplicative.ofAdd a)
  refine ⟨β, hS.hurewiczOne_injective (i x) ?_⟩
  apply Multiplicative.toAdd.injective
  rw [hurewiczOne_map, hβ]
  exact ha

private theorem exists_polygon_carrier_of_firstHomology {S U : Set E3}
    (hS : IsCombinatorialSolidTorus S) (hU : IsOpen U)
    (hcarry : CarriesFirstHomologyOnto (frontier S ∩ U) S) :
    ∃ K : Set E3, IsPLSphere 1 K ∧ K ⊆ frontier S ∩ U ∧
      CarriesFundamentalGroupOnto K S := by
  classical
  obtain ⟨e⟩ := nonempty_integralFirstHomology_equiv_int hS.1
  obtain ⟨a, ha⟩ := hcarry.2 hcarry.1 (e.symm 1)
  obtain ⟨c, rfl⟩ := integralOneCycleClass_surjective a
  have hc : spineCarrierHomologyInclusion hcarry.1 (integralOneCycleClass c) = e.symm 1 := ha
  have hcnz : spineCarrierHomologyInclusion hcarry.1 (integralOneCycleClass c) ≠ 0 := by
    rw [hc]
    intro hz
    have hh := congrArg e hz
    simp at hh
  obtain ⟨n, G, hG, hGU, cG, m, hdisj, _horient, hsum⟩ :=
    SpineCarrier.exists_disjoint_oriented_polygons_of_nonzero_cycle hS hU hcarry.1 c hcnz
  change spineCarrierHomologyInclusion hcarry.1 (integralOneCycleClass c) =
    ∑ j, m j • spineCarrierHomologyInclusion ((hGU j).trans hcarry.1)
      (integralOneCycleClass (cG j)) at hsum
  obtain ⟨i, hi⟩ := exists_maximal_firstHomology_image_of_disjoint_polygons hS G hG
    (fun j => (hGU j).trans inter_subset_left) (fun j => (hGU j).trans hcarry.1) hdisj
  have hone : e.symm 1 ∈
      LinearMap.range (spineCarrierHomologyInclusion ((hGU i).trans hcarry.1)) := by
    rw [← hc, hsum]
    apply Submodule.sum_mem
    intro j _hj
    exact (LinearMap.range
      (spineCarrierHomologyInclusion ((hGU i).trans hcarry.1))).toAddSubgroup.zsmul_mem
      (hi j ⟨integralOneCycleClass (cG j), rfl⟩) (m j)
  have hH : CarriesFirstHomologyOnto (G i) S := by
    refine ⟨(hGU i).trans hcarry.1, fun hGS x => ?_⟩
    have hmul : (e x) • e.symm 1 = x := by
      apply e.injective
      simp
    have hx := (LinearMap.range
      (spineCarrierHomologyInclusion ((hGU i).trans hcarry.1))).toAddSubgroup.zsmul_mem hone (e x)
    rw [hmul] at hx
    exact hx
  exact ⟨G i, hG i, hGU i,
    carriesFundamentalGroupOnto_of_firstHomology hS.1 (hG i).isPathConnected_one hH⟩

private theorem isSpine_nonempty {T Z : Set E3} (h : IsSpine T Z) (hT : T.Nonempty) :
    Z.Nonempty := by
  obtain ⟨φ, p, hp, hZ⟩ := h
  obtain ⟨t, ht⟩ := hT
  let q := (φ.symm ⟨t, ht⟩).2
  let p' : Metric.closedBall (0 : EuclideanSpace ℝ (Fin 2)) 1 := ⟨p, interior_subset hp⟩
  refine ⟨φ (p', q), ?_⟩
  rw [hZ]
  exact ⟨φ (p', q), ⟨(p', q), rfl, rfl⟩, rfl⟩

theorem exists_polygon_carrier_of_spine {S₁ S₂ T₁ T₂ Z₀ Z₁ : Set (EuclideanSpace ℝ (Fin 3))}
    (hS₁ : IsCombinatorialSolidTorus S₁) (hS₂ : IsCombinatorialSolidTorus S₂)
    (hT₁ : IsTopologicalSolidTorus T₁) (hT₂ : IsTopologicalSolidTorus T₂)
    (hS₁T₁ : S₁ ⊆ interior T₁) (hS₂T₂ : S₂ ⊆ interior T₂)
    (hZ₁T₁ : IsSpine T₁ Z₁) (hZ₁T₂ : IsSpine T₂ Z₁) (hZ₁S₁ : Z₁ ⊆ interior S₁)
    (hZ₁S₂ : Z₁ ⊆ interior S₂) (hZ₀ : Z₀.Nonempty) (hZ₀S₁ : Z₀ ⊆ interior S₁)
    (hZ₀S₂ : Disjoint Z₀ S₂) (hZ₀gen : CarriesFundamentalGroupOnto Z₀ S₁) :
    ∃ K : Set (EuclideanSpace ℝ (Fin 3)), IsPLSphere 1 K ∧ K ⊆ frontier S₂ ∩ interior S₁ ∧
      CarriesFundamentalGroupOnto K S₂ := by
  have hZ₁gen₁ : CarriesFundamentalGroupOnto Z₁ S₁ :=
    ⟨hZ₁S₁.trans interior_subset, fun hsub x =>
      (fundamentalGroup_map_inclusion_bijective_of_isSpine_of_isTopologicalSolidTorus
        hS₁.1 hT₁ hS₁T₁ hZ₁T₁ hsub x).2⟩
  let _ := hZ₁gen₁
  have hZ₁gen₂ : CarriesFundamentalGroupOnto Z₁ S₂ :=
    ⟨hZ₁S₂.trans interior_subset, fun hsub x =>
      (fundamentalGroup_map_inclusion_bijective_of_isSpine_of_isTopologicalSolidTorus
        hS₂.1 hT₂ hS₂T₂ hZ₁T₂ hsub x).2⟩
  have hZ₁ne : Z₁.Nonempty := isSpine_nonempty hZ₁T₂
    (hS₂.1.isPathConnected.nonempty.mono (hS₂T₂.trans interior_subset))
  have hZ₀H := hZ₀gen.carriesFirstHomologyOnto hZ₀ hS₁.1.isPathConnected
  have hZ₀int := carriesFirstHomologyOnto_subset_of_injective hZ₀H hZ₀S₁ interior_subset
    (hS₁.1.integralSingularHomologyMap_interior_injective)
  have htrace := carriesFirstHomologyOnto_frontier_inter_of_cutting hS₂ isOpen_interior
    hZ₀int hZ₀S₂ (hZ₁gen₂.carriesFirstHomologyOnto hZ₁ne hS₂.1.isPathConnected)
    (fun _ hx => ⟨hZ₁S₁ hx, hZ₁S₂ hx⟩)
  exact exists_polygon_carrier_of_firstHomology hS₂ isOpen_interior htrace

end DifferentialGeometry.Topology.PiecewiseLinear
