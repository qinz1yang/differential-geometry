/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.FundamentalGroup.BicollarKernel
import DifferentialGeometry.Topology.FundamentalGroup.Retraction
import DifferentialGeometry.Topology.VanKampen.TwoSidedCollarRetraction

open Set
open scoped ContinuousMap

namespace DifferentialGeometry.Topology.ThreeManifold.TwoSidedCollar

open VanKampen

section

variable {S X : Type*} [TopologicalSpace S] [TopologicalSpace X]
  [CompactSpace S] [ConnectedSpace S] [T2Space X]
  [LocallyPathConnectedSpace X] [SimplyConnectedSpace X]
  {e : S → X} (c : TwoSidedCollar e)

noncomputable def collarMiddleInclusion : C(S, ↑(c.negativeCover ∩ c.positiveCover)) :=
  ⟨fun s => c.collarMiddleHomeomorph (s, ⟨0, by norm_num⟩),
    c.collarMiddleHomeomorph.continuous.comp (continuous_id.prodMk continuous_const)⟩

theorem collarMiddleInclusion_coe (s : S) : (c.collarMiddleInclusion s).val = e s := by
  change c.toFun (s, 0) = e s
  exact c.zero_eq s

noncomputable def collarMiddleProjection : C(↑(c.negativeCover ∩ c.positiveCover), S) :=
  ⟨fun x => (c.collarMiddleHomeomorph.symm x).1,
    continuous_fst.comp c.collarMiddleHomeomorph.symm.continuous⟩

theorem collarMiddleProjection_comp_inclusion :
    c.collarMiddleProjection.comp c.collarMiddleInclusion = ContinuousMap.id S := by
  ext s
  exact congrArg Prod.fst (c.collarMiddleHomeomorph.symm_apply_apply (s, ⟨0, by norm_num⟩))

theorem fundamentalGroup_map_collarMiddleInclusion_bijective (s : S) :
    Function.Bijective (FundamentalGroup.map c.collarMiddleInclusion s) := by
  let _ : ContractibleSpace (Ioo (-1 : ℝ) 1) :=
    (convex_Ioo (-1 : ℝ) 1).contractibleSpace ⟨0, by norm_num⟩
  let ep : S × Ioo (-1 : ℝ) 1 ≃ₕ S :=
    ((ContinuousMap.HomotopyEquiv.refl S).prodCongr
      (ContractibleSpace.hequiv_unit (Ioo (-1 : ℝ) 1)).some).trans
        (Homeomorph.prodUnique S Unit).toHomotopyEquiv
  let eh : ↑(c.negativeCover ∩ c.positiveCover) ≃ₕ S :=
    c.collarMiddleHomeomorph.symm.toHomotopyEquiv.trans ep
  exact bijective_fundamentalGroup_map_of_homotopyEquiv_leftInverse eh
    c.collarMiddleInclusion
    (fun x => DFunLike.congr_fun c.collarMiddleProjection_comp_inclusion x) s

def negativeBoundaryInclusion : C(S, closure c.negativeSide) :=
  ⟨fun s => ⟨e s, c.range_e_subset_closure_negativeSide ⟨s, rfl⟩⟩,
    c.continuous_e.subtype_mk _⟩

def positiveBoundaryInclusion : C(S, closure c.positiveSide) :=
  ⟨fun s => ⟨e s, c.range_e_subset_closure_positiveSide ⟨s, rfl⟩⟩,
    c.continuous_e.subtype_mk _⟩

theorem negativeRetraction_comp_collarMiddleInclusion :
    c.negativeRetraction.comp
        ((interToLeft c.negativeCover c.positiveCover).comp c.collarMiddleInclusion) =
      c.negativeBoundaryInclusion := by
  ext s
  change c.negativeRetractionValue _ = e s
  exact (c.negativeRetractionValue_eq_of_mem_zeroSlice _
    ⟨s, (c.collarMiddleInclusion_coe s).symm⟩).trans (c.collarMiddleInclusion_coe s)

theorem positiveRetraction_comp_collarMiddleInclusion :
    c.positiveRetraction.comp
        ((interToRight c.negativeCover c.positiveCover).comp c.collarMiddleInclusion) =
      c.positiveBoundaryInclusion := by
  ext s
  change c.positiveRetractionValue _ = e s
  exact (c.positiveRetractionValue_eq_of_mem_zeroSlice _
    ⟨s, (c.collarMiddleInclusion_coe s).symm⟩).trans (c.collarMiddleInclusion_coe s)

end

theorem exists_nontrivial_fundamentalGroup_kernel_boundary_of_simplyConnectedSpace
    {S X : Type*} [TopologicalSpace S] [TopologicalSpace X]
    [CompactSpace S] [PathConnectedSpace S] [T2Space X]
    [LocallyPathConnectedSpace X] [SimplyConnectedSpace X]
    {e : S → X} (c : TwoSidedCollar e) (hS : ¬ SimplyConnectedSpace S) (s : S) :
    ∃ g : FundamentalGroup S s, g ≠ 1 ∧
      (FundamentalGroup.map c.negativeBoundaryInclusion s g = 1 ∨
        FundamentalGroup.map c.positiveBoundaryInclusion s g = 1) := by
  let z := c.collarMiddleInclusion
  obtain ⟨a, ha, hside⟩ := c.exists_nontrivial_fundamentalGroup_kernel_of_simplyConnectedSpace
    hS (z s).val (z s).property
  obtain ⟨g, hg⟩ := (c.fundamentalGroup_map_collarMiddleInclusion_bijective s).2 a
  have hgne : g ≠ 1 := by
    intro h
    exact ha (hg.symm.trans (h ▸ map_one _))
  refine ⟨g, hgne, ?_⟩
  rcases hside with hn | hp
  · left
    have hn' : FundamentalGroup.map (interToLeft c.negativeCover c.positiveCover) (z s) a = 1 :=
      (eq_of_heq (fundamentalGroup_mapOfEq_heq_map _ _ _ rfl a)).symm.trans hn
    rw [← c.negativeRetraction_comp_collarMiddleInclusion]
    change Path.Homotopic.Quotient.map g _ = .refl _
    rw [Path.Homotopic.Quotient.map_comp, Path.Homotopic.Quotient.map_comp]
    change FundamentalGroup.map c.negativeRetraction _
      (FundamentalGroup.map (interToLeft c.negativeCover c.positiveCover) (z s)
        (FundamentalGroup.map z s g)) = 1
    rw [hg, hn', map_one]
  · right
    have hp' : FundamentalGroup.map (interToRight c.negativeCover c.positiveCover) (z s) a = 1 :=
      (eq_of_heq (fundamentalGroup_mapOfEq_heq_map _ _ _ rfl a)).symm.trans hp
    rw [← c.positiveRetraction_comp_collarMiddleInclusion]
    change Path.Homotopic.Quotient.map g _ = .refl _
    rw [Path.Homotopic.Quotient.map_comp, Path.Homotopic.Quotient.map_comp]
    change FundamentalGroup.map c.positiveRetraction _
      (FundamentalGroup.map (interToRight c.negativeCover c.positiveCover) (z s)
        (FundamentalGroup.map z s g)) = 1
    rw [hg, hp', map_one]

end DifferentialGeometry.Topology.ThreeManifold.TwoSidedCollar
