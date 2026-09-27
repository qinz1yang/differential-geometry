/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.BranchBoundaryCollar

open Set

namespace DifferentialGeometry.Topology.PiecewiseLinear

theorem doublePointSet_inter_eq_empty_of_eq_sdiff {X Y : Type*} {f g : X → Y} {Pd : Set X}
    {S T : Set Y} (hdouble : doublePointSet g Pd = doublePointSet f Pd \ S)
    (hclean : doublePointSet f Pd ∩ T ⊆ S) : doublePointSet g Pd ∩ T = ∅ := by
  rw [eq_empty_iff_forall_notMem]
  rintro y ⟨hy, hyT⟩
  rw [hdouble] at hy
  exact hy.2 (hclean ⟨hy.1, hyT⟩)

theorem disjoint_doublePointSet_of_eq_sdiff {X Y : Type*} {f g : X → Y} {Pd : Set X}
    {S T C : Set Y} (hdouble : doublePointSet g Pd = doublePointSet f Pd \ S)
    (hclean : doublePointSet f Pd ∩ T ⊆ S) (hCT : C ⊆ T) :
    Disjoint (doublePointSet g Pd) C := by
  rw [Set.disjoint_right]
  intro y hyC hy
  have hmem : y ∈ doublePointSet g Pd ∩ T := ⟨hy, hCT hyC⟩
  rw [doublePointSet_inter_eq_empty_of_eq_sdiff hdouble hclean] at hmem
  exact hmem

universe u

variable {M : Type u} [TopologicalSpace M] [T2Space M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [HasGroupoid M (plGroupoid 3)]
  {D : SingularTwoCell M} {BdM B : Set M}

open Classical in
omit [T2Space M] [HasGroupoid M (plGroupoid 3)] in
theorem NormalSingularCellData.disjoint_doublePointSet_separated_of_subset_nbhd
    (hD : NormalSingularCellData D BdM B) (cb : hD.singularSet.Branch)
    {W C : Set M} {P : Set (EuclideanSpace ℝ (Fin 2))} {h : M → M}
    (hclean : doublePointSet D D.domain ∩ W ⊆ hD.singularSet.branchCarrier cb)
    (hgdouble : doublePointSet (P.piecewise (h ∘ D) D) D.domain =
      doublePointSet D D.domain \ hD.singularSet.branchCarrier cb)
    (hCW : C ⊆ W) :
    Disjoint (doublePointSet (P.piecewise (h ∘ D) D) D.domain) C :=
  disjoint_doublePointSet_of_eq_sdiff hgdouble hclean hCW

end DifferentialGeometry.Topology.PiecewiseLinear
