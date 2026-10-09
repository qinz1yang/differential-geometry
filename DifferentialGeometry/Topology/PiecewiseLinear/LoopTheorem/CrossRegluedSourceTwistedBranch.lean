/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.LoopTheorem.CrossRegluedSourceTwistedCrossing
import DifferentialGeometry.Topology.PiecewiseLinear.LoopTheorem.BranchDeletion
import DifferentialGeometry.Topology.PiecewiseLinear.LoopTheorem.BranchDescent

open Set Topology

namespace DifferentialGeometry.Topology.PiecewiseLinear

theorem twistedStripCell_doublePointSet_isCompact :
    IsCompact (doublePointSet (⇑twistedStripCell) twistedStripCell.domain) := by
  rw [twistedStripCell_doublePointSet]
  exact isCompact_Icc.image
    (continuous_twistedStripMap.comp (continuous_const.prodMk continuous_id))

theorem twistedStripCell_doublePointSet_isConnected :
    IsConnected (doublePointSet (⇑twistedStripCell) twistedStripCell.domain) := by
  rw [twistedStripCell_doublePointSet]
  exact (isConnected_Icc (by norm_num : (0 : ℝ) ≤ 1)).image _
    (continuous_twistedStripMap.comp (continuous_const.prodMk continuous_id)).continuousOn

theorem twistedStripCell_exists_branch_equiv
    (T : NormalSingularSetTriangulation twistedStripCell (frontier twistedStripSide)) :
    ∃ e : Unit ≃ T.Branch,
      T.branchCarrier (e ()) = doublePointSet (⇑twistedStripCell) twistedStripCell.domain ∧
        T.IsBoundaryBranch (e ()) := by
  classical
  let _ : Finite T.Branch := T.finite_branch
  let f : Unit → Set halfTurnQuotient := fun _ =>
    doublePointSet (⇑twistedStripCell) twistedStripCell.domain
  have hdis : Pairwise fun i j => Disjoint (f i) (f j) :=
    fun _ _ h => (h (Subsingleton.elim _ _)).elim
  have huni : ⋃ i, f i = ⋃ c, T.branchCarrier c := by
    rw [T.iUnion_branchCarrier]
    simp only [f, iUnion_const]
  obtain ⟨e, he⟩ := exists_equiv_of_isClosed_isConnected_partition
    (fun _ => twistedStripCell_doublePointSet_isConnected) T.branchCarrier_isConnected
    (fun _ => twistedStripCell_doublePointSet_isCompact.isClosed) T.isClosed_branchCarrier
    hdis T.pairwise_disjoint_branchCarrier huni
  refine ⟨e, (he ()).symm, ?_⟩
  by_contra hc
  have hbd : twistedStripMap (0, 0) ∈ frontier twistedStripSide :=
    (twistedStripMap_core_mem_frontier_iff (by norm_num)).mpr (Or.inl rfl)
  have hmem : twistedStripMap (0, 0) ∈ T.branchCarrier (e ()) := by
    rw [← he ()]
    rw [twistedStripCell_doublePointSet]
    exact mem_image_of_mem _ (by norm_num)
  exact disjoint_left.mp (T.branchCarrier_disjoint_boundary_of_not_isBoundaryBranch hc) hmem hbd

theorem twistedStripCell_complexity_eq_one
    (T : NormalSingularSetTriangulation twistedStripCell (frontier twistedStripSide)) :
    T.complexity = 1 := by
  obtain ⟨e, -⟩ := twistedStripCell_exists_branch_equiv T
  rw [T.complexity_eq_natCard_branch, ← Nat.card_congr e]
  simp

theorem twistedStripCell_exists_branchTube {B : Set halfTurnQuotient}
    (hD : NormalSingularCellData twistedStripCell (frontier twistedStripSide) B) :
    ∃ (c : hD.singularSet.Branch)
      (T : CrossSeamTubeData hD c (halfTurnSlabChart 0).source),
      hD.singularSet.complexity = 1 ∧ hD.singularSet.IsBoundaryBranch c ∧
      hD.singularSet.branchCarrier c =
        doublePointSet (⇑twistedStripCell) twistedStripCell.domain ∧
      T.chart = twistedTubeChart ∧ Nonempty (PLSeamTubeChart halfTurnQuotient T.chart) ∧
      T.chart '' spliceCylinder ⊆ twistedStripSide ∧
      T.chart '' spliceCylinder ∩ frontier twistedStripSide = T.chart '' spliceEndDisks ∧
      T.chart '' crossingFigure ⊂ ⇑twistedStripCell '' twistedStripCell.domain := by
  obtain ⟨e, he, hb⟩ := twistedStripCell_exists_branch_equiv hD.singularSet
  let T : CrossSeamTubeData hD (e ()) (halfTurnSlabChart 0).source := {
    chart := twistedTubeChart
    isTube := by rw [he]; exact crossSeamTubeCore_twistedStripCell }
  exact ⟨e (), T, twistedStripCell_complexity_eq_one hD.singularSet, hb, he, rfl,
    nonempty_plSeamTubeChart_twistedTubeChart, twistedTubeChart_side,
    twistedTubeChart_boundary, twistedTubeChart_crossingFigure_ssubset_image⟩

end DifferentialGeometry.Topology.PiecewiseLinear
