/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.FundamentalGroup.OpenCoverKernel
import DifferentialGeometry.Topology.FundamentalGroup.SimplyConnected
import DifferentialGeometry.Topology.VanKampen.TwoSidedCollarCover

open Set
open scoped ContinuousMap

namespace DifferentialGeometry.Topology.ThreeManifold.TwoSidedCollar

open VanKampen

theorem exists_nontrivial_fundamentalGroup_kernel_of_simplyConnectedSpace
    {S X : Type*} [TopologicalSpace S] [TopologicalSpace X]
    [CompactSpace S] [PathConnectedSpace S] [T2Space X]
    [LocallyPathConnectedSpace X] [SimplyConnectedSpace X]
    {e : S → X} (c : TwoSidedCollar e) (hS : ¬ SimplyConnectedSpace S)
    (x : X) (hx : x ∈ c.negativeCover ∩ c.positiveCover) :
    ∃ g : FundamentalGroup (↑(c.negativeCover ∩ c.positiveCover))
        (overlapBasepoint c.negativeCover c.positiveCover x hx),
      g ≠ 1 ∧ ((fundamentalGroupInterToLeft c.negativeCover c.positiveCover x hx).hom g = 1 ∨
        (fundamentalGroupInterToRight c.negativeCover c.positiveCover x hx).hom g = 1) := by
  let _ : ContractibleSpace (Ioo (-1 : ℝ) 1) :=
    (convex_Ioo (-1 : ℝ) 1).contractibleSpace ⟨0, by norm_num⟩
  let ep : S × Ioo (-1 : ℝ) 1 ≃ₕ S :=
    ((ContinuousMap.HomotopyEquiv.refl S).prodCongr
      (ContractibleSpace.hequiv_unit (Ioo (-1 : ℝ) 1)).some).trans
        (Homeomorph.prodUnique S Unit).toHomotopyEquiv
  let eh : ↑(c.negativeCover ∩ c.positiveCover) ≃ₕ S :=
    c.collarMiddleHomeomorph.symm.toHomotopyEquiv.trans ep
  let _ : PathConnectedSpace c.negativeCover :=
    isPathConnected_iff_pathConnectedSpace.mp c.isPathConnected_negativeCover
  let _ : PathConnectedSpace c.positiveCover :=
    isPathConnected_iff_pathConnectedSpace.mp c.isPathConnected_positiveCover
  let _ : PathConnectedSpace (↑(c.negativeCover ∩ c.positiveCover)) :=
    c.collarMiddleHomeomorph.surjective.pathConnectedSpace c.collarMiddleHomeomorph.continuous
  have hn : ¬ SimplyConnectedSpace (↑(c.negativeCover ∩ c.positiveCover)) := by
    intro h
    let _ := h
    exact hS eh.symm.simplyConnectedSpace
  obtain ⟨g, hg⟩ := exists_fundamentalGroup_ne_one_of_not_simplyConnectedSpace hn
    (overlapBasepoint c.negativeCover c.positiveCover x hx)
  have hnull : (fundamentalGroupLeftToAmbient c.negativeCover x hx.1).hom
      ((fundamentalGroupInterToLeft c.negativeCover c.positiveCover x hx).hom g) = 1 :=
    Subsingleton.elim _ _
  rcases exists_nontrivial_fundamentalGroup_kernel_of_open_cover
    c.negativeCover c.positiveCover c.isOpen_negativeCover c.isOpen_positiveCover
    c.negativeCover_union_positiveCover x hx g hg hnull with ⟨a, ha, hleft⟩ | ⟨a, ha, hright⟩
  · exact ⟨a, ha, Or.inl hleft⟩
  · exact ⟨a, ha, Or.inr hright⟩

end DifferentialGeometry.Topology.ThreeManifold.TwoSidedCollar
