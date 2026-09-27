/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.Connected.CollaredCover
import DifferentialGeometry.Topology.FundamentalGroup.OpenCoverKernel
import DifferentialGeometry.Topology.FundamentalGroup.Retraction
import DifferentialGeometry.Topology.VanKampen.BoundaryCollarInjection
import DifferentialGeometry.Topology.VanKampen.BoundaryCollarOrientation

open Set
open scoped ContinuousMap

namespace DifferentialGeometry.Topology.ThreeManifold.TwoSidedCollar

open VanKampen

variable {S X : Type*} [TopologicalSpace S] [TopologicalSpace X]
  {e : S → X} (c : TwoSidedCollar e)

noncomputable def zeroSection : C(S, c.range) :=
  ⟨fun s => c.homeomorphRange (s, 0),
    c.homeomorphRange.continuous.comp (continuous_id.prodMk continuous_const)⟩

theorem zeroSection_coe (s : S) : (c.zeroSection s).val = e s := c.zero_eq s

noncomputable def rangeHomotopyEquiv : c.range ≃ₕ S :=
  c.homeomorphRange.symm.toHomotopyEquiv.trans
    (((ContinuousMap.HomotopyEquiv.refl S).prodCongr
      (ContractibleSpace.hequiv_unit ℝ).some).trans
        (Homeomorph.prodUnique S Unit).toHomotopyEquiv)

theorem rangeHomotopyEquiv_zeroSection (s : S) : c.rangeHomotopyEquiv (c.zeroSection s) = s :=
  congrArg Prod.fst (c.homeomorphRange.symm_apply_apply (s, 0))

theorem bijective_fundamentalGroup_map_zeroSection (s : S) :
    Function.Bijective (FundamentalGroup.map c.zeroSection s) :=
  bijective_fundamentalGroup_map_of_homotopyEquiv_leftInverse c.rangeHomotopyEquiv
    c.zeroSection c.rangeHomotopyEquiv_zeroSection s

def domainBoundaryInclusion {P : Set X} (hP : Set.range e ⊆ P) : C(S, P) :=
  ⟨fun s => ⟨e s, hP ⟨s, rfl⟩⟩, c.continuous_e.subtype_mk _⟩

theorem exists_nontrivial_fundamentalGroup_kernel_of_closed_cover
    [PathConnectedSpace S] {P Q : Set X} [PathConnectedSpace P] [PathConnectedSpace Q]
    (hcover : P ∪ Q = univ) (hmeet : P ∩ Q = Set.range e)
    (hPcl : closure (P \ Q) = P) (hQcl : closure (Q \ P) = Q)
    (s : S) (g : FundamentalGroup S s) (hg : g ≠ 1)
    (hnull : FundamentalGroup.map (⟨e, c.continuous_e⟩ : C(S, X)) s g = 1) :
    ∃ a : FundamentalGroup S s, a ≠ 1 ∧
      (FundamentalGroup.map
          (c.domainBoundaryInclusion (hmeet.symm.subset.trans inter_subset_left)) s a = 1 ∨
        FundamentalGroup.map
          (c.domainBoundaryInclusion (hmeet.symm.subset.trans inter_subset_right)) s a = 1) := by
  have hP : IsClosed P := hPcl ▸ isClosed_closure
  have hQ : IsClosed Q := hQcl ▸ isClosed_closure
  have hQP : Q ∪ P = univ := (union_comm Q P).trans hcover
  have hPf : frontier P = Set.range e :=
    (frontier_eq_inter_of_closure_sdiff_eq hcover hPcl hQcl).trans hmeet
  have hQf : frontier Q = Set.range e :=
    (frontier_eq_inter_of_closure_sdiff_eq hQP hQcl hPcl).trans
      ((inter_comm Q P).trans hmeet)
  obtain ⟨d, _, hdP, hdrQ, hUV, hUVinter⟩ :=
    c.exists_open_cover_of_closed_cover hcover hmeet hPcl hQcl
  let U := d.domainNeighborhood P
  let V := d.reverse.domainNeighborhood Q
  have hU : IsOpen U := d.isOpen_domainNeighborhood P
  have hV : IsOpen V := d.reverse.isOpen_domainNeighborhood Q
  let _ : PathConnectedSpace U := d.pathConnectedSpace_domainNeighborhood hP hPf.subset hdP
  let _ : PathConnectedSpace V := d.reverse.pathConnectedSpace_domainNeighborhood hQ hQf.subset hdrQ
  let j : d.range ≃ₜ ↑(U ∩ V) := (Homeomorph.setCongr hUVinter).symm
  let _ : PathConnectedSpace d.range :=
    d.homeomorphRange.surjective.pathConnectedSpace d.homeomorphRange.continuous
  let _ : PathConnectedSpace (↑(U ∩ V)) := j.surjective.pathConnectedSpace j.continuous
  let z : C(S, ↑(U ∩ V)) := (⟨j, j.continuous⟩ : C(d.range, ↑(U ∩ V))).comp d.zeroSection
  have hz (x : S) : (z x).val = e x := d.zeroSection_coe x
  let ep : ↑(U ∩ V) ≃ₕ S := j.symm.toHomotopyEquiv.trans d.rangeHomotopyEquiv
  have hzinv : Function.LeftInverse ep z := by
    intro x
    change d.rangeHomotopyEquiv (j.symm (j (d.zeroSection x))) = x
    rw [j.symm_apply_apply, d.rangeHomotopyEquiv_zeroSection]
  have hzbij := bijective_fundamentalGroup_map_of_homotopyEquiv_leftInverse ep z hzinv s
  have hzg : FundamentalGroup.map z s g ≠ 1 := by
    intro h
    exact hg (hzbij.1 (h.trans (map_one _).symm))
  have hcomp : (subsetToAmbient U).comp ((interToLeft U V).comp z) =
      (⟨e, c.continuous_e⟩ : C(S, X)) := by
    ext x
    exact hz x
  have hzgnull : (fundamentalGroupLeftToAmbient U (z s).val (z s).property.1).hom
      ((fundamentalGroupInterToLeft U V (z s).val (z s).property).hom
        (FundamentalGroup.map z s g)) = 1 := by
    have h := hnull
    rw [← hcomp] at h
    change Path.Homotopic.Quotient.map g _ = .refl _ at h
    rw [Path.Homotopic.Quotient.map_comp, Path.Homotopic.Quotient.map_comp] at h
    change FundamentalGroup.mapOfEq (subsetToAmbient U) rfl
      (FundamentalGroup.mapOfEq (interToLeft U V) rfl (FundamentalGroup.map z s g)) = 1
    rw [eq_of_heq (fundamentalGroup_mapOfEq_heq_map _ _ _ rfl _),
      eq_of_heq (fundamentalGroup_mapOfEq_heq_map _ _ _ rfl _)]
    exact h
  have hPcomp : (d.domainRetraction hdP).comp ((interToLeft U V).comp z) =
      c.domainBoundaryInclusion (hmeet.symm.subset.trans inter_subset_left) := by
    apply ContinuousMap.ext
    intro x
    have hfix := d.domainRetraction_leftInverse hP hPf.subset hdP
      (c.domainBoundaryInclusion (hmeet.symm.subset.trans inter_subset_left) x)
    exact (congrArg (d.domainRetraction hdP) (Subtype.ext (hz x))).trans hfix
  have hQcomp : (d.reverse.domainRetraction hdrQ).comp ((interToRight U V).comp z) =
      c.domainBoundaryInclusion (hmeet.symm.subset.trans inter_subset_right) := by
    apply ContinuousMap.ext
    intro x
    have hfix := d.reverse.domainRetraction_leftInverse hQ hQf.subset hdrQ
      (c.domainBoundaryInclusion (hmeet.symm.subset.trans inter_subset_right) x)
    exact (congrArg (d.reverse.domainRetraction hdrQ) (Subtype.ext (hz x))).trans hfix
  have transfer {Y Z : Set X}
      (i : C(↑(U ∩ V), Y)) (r : C(Y, Z)) (f : C(S, Z))
      (hf : r.comp (i.comp z) = f)
      (q : FundamentalGroup (↑(U ∩ V)) (z s)) (hq : q ≠ 1)
      (hqn : FundamentalGroup.map i (z s) q = 1) :
      ∃ a : FundamentalGroup S s, a ≠ 1 ∧ FundamentalGroup.map f s a = 1 := by
    obtain ⟨a, ha⟩ := hzbij.2 q
    refine ⟨a, fun h => hq (ha.symm.trans (h ▸ map_one _)), ?_⟩
    rw [← hf]
    change Path.Homotopic.Quotient.map a _ = .refl _
    rw [Path.Homotopic.Quotient.map_comp, Path.Homotopic.Quotient.map_comp]
    change FundamentalGroup.map r _ (FundamentalGroup.map i (z s)
      (FundamentalGroup.map z s a)) = 1
    rw [ha, hqn, map_one]
  rcases exists_nontrivial_fundamentalGroup_kernel_of_open_cover U V hU hV hUV
      (z s).val (z s).property (FundamentalGroup.map z s g) hzg hzgnull with
    ⟨q, hq, hqn⟩ | ⟨q, hq, hqn⟩
  · obtain ⟨a, ha, han⟩ := transfer (interToLeft U V) (d.domainRetraction hdP) _ hPcomp q hq
      ((eq_of_heq (fundamentalGroup_mapOfEq_heq_map _ _ _ rfl q)).symm.trans hqn)
    exact ⟨a, ha, Or.inl han⟩
  · obtain ⟨a, ha, han⟩ := transfer (interToRight U V)
      (d.reverse.domainRetraction hdrQ) _ hQcomp q hq
      ((eq_of_heq (fundamentalGroup_mapOfEq_heq_map _ _ _ rfl q)).symm.trans hqn)
    exact ⟨a, ha, Or.inr han⟩

end DifferentialGeometry.Topology.ThreeManifold.TwoSidedCollar
