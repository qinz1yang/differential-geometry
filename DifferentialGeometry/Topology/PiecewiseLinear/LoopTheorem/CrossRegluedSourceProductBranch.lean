/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.LoopTheorem.CrossRegluedSourceProductNormal
import DifferentialGeometry.Topology.PiecewiseLinear.LoopTheorem.BranchDeletion
import DifferentialGeometry.Topology.PiecewiseLinear.LoopTheorem.BranchDescent

open Set Topology

namespace DifferentialGeometry.Topology.PiecewiseLinear

noncomputable def crossingProductBranchCarrier (i : Bool) : Set (EuclideanSpace ℝ (Fin 3)) :=
  spliceEmbedding '' ({((0 : ℝ), if i then 3 else 0)} ×ˢ Icc (0 : ℝ) 1)

theorem isCompact_crossingProductBranchCarrier (i : Bool) :
    IsCompact (crossingProductBranchCarrier i) :=
  (isCompact_singleton.prod isCompact_Icc).image spliceEmbedding.continuous

theorem isConnected_crossingProductBranchCarrier (i : Bool) :
    IsConnected (crossingProductBranchCarrier i) := by
  have hconn : IsConnected ({((0 : ℝ), if i then (3 : ℝ) else 0)} ×ˢ Icc (0 : ℝ) 1) :=
    ⟨⟨((0, if i then 3 else 0), 0), rfl, by norm_num⟩,
      ((convex_singleton _).prod (convex_Icc (0 : ℝ) 1)).isPreconnected⟩
  exact hconn.image spliceEmbedding spliceEmbedding.continuous.continuousOn

theorem pairwise_disjoint_crossingProductBranchCarrier :
    Pairwise fun i j => Disjoint (crossingProductBranchCarrier i)
      (crossingProductBranchCarrier j) := by
  intro i j hij
  apply Set.disjoint_left.mpr
  rintro z ⟨p, hp, hpz⟩ ⟨q, hq, hqz⟩
  have hpq := spliceEmbedding.injective (hpz.trans hqz.symm)
  have hh : ((0 : ℝ), if i then (3 : ℝ) else 0) = ((0 : ℝ), if j then 3 else 0) :=
    hp.1.symm.trans ((congrArg Prod.fst hpq).trans hq.1)
  cases i <;> cases j <;> simp_all

theorem iUnion_crossingProductBranchCarrier :
    ⋃ i, crossingProductBranchCarrier i =
      doublePointSet (⇑crossingProductCell) crossingProductCell.domain := by
  have hUnion : (⋃ i, crossingProductBranchCarrier i) =
      crossingProductBranchCarrier false ∪ crossingProductBranchCarrier true := by
    ext z
    constructor
    · intro hz
      obtain ⟨i, hi⟩ := mem_iUnion.mp hz
      cases i
      · exact Or.inl hi
      · exact Or.inr hi
    · rintro (h | h)
      · exact mem_iUnion.mpr ⟨false, h⟩
      · exact mem_iUnion.mpr ⟨true, h⟩
  rw [hUnion, crossingProductCell_doublePointSet, union_prod, image_union]
  simp only [crossingProductBranchCarrier, Bool.false_eq_true, ↓reduceIte]

theorem crossingProductBranchCarrier_mem_boundary (i : Bool) :
    spliceEmbedding ((0, if i then 3 else 0), 0) ∈
      crossingProductBranchCarrier i ∩ frontier crossingProductSide := by
  refine ⟨⟨((0, if i then 3 else 0), 0), ⟨rfl, by norm_num⟩, rfl⟩, ?_⟩
  have hfront : frontier crossingProductSide =
      spliceEmbedding '' frontier crossingProductBox :=
    (spliceEmbedding.toHomeomorph.image_frontier _).symm
  rw [hfront]
  refine ⟨_, ?_, rfl⟩
  rw [isHPolytope_crossingProductBox.isPolyhedron.isClosed.frontier_eq, crossingProductBox,
    interior_prod_eq, interior_prod_eq, interior_Icc, interior_Icc, interior_Icc]
  cases i <;> norm_num

theorem crossingProductCell_exists_branch_equiv
    (T : NormalSingularSetTriangulation crossingProductCell (frontier crossingProductSide)) :
    ∃ e : Bool ≃ T.Branch, ∀ i,
      T.branchCarrier (e i) = crossingProductBranchCarrier i ∧ T.IsBoundaryBranch (e i) := by
  classical
  let _ : Finite T.Branch := T.finite_branch
  obtain ⟨e, he⟩ := exists_equiv_of_isClosed_isConnected_partition
    isConnected_crossingProductBranchCarrier T.branchCarrier_isConnected
    (fun i => (isCompact_crossingProductBranchCarrier i).isClosed) T.isClosed_branchCarrier
    pairwise_disjoint_crossingProductBranchCarrier T.pairwise_disjoint_branchCarrier
    (iUnion_crossingProductBranchCarrier.trans T.iUnion_branchCarrier.symm)
  refine ⟨e, fun i => ⟨(he i).symm, ?_⟩⟩
  by_contra hc
  have hdis := T.branchCarrier_disjoint_boundary_of_not_isBoundaryBranch hc
  have hz := crossingProductBranchCarrier_mem_boundary i
  exact Set.disjoint_left.mp hdis (he i ▸ hz.1) hz.2

theorem crossingProductCell_complexity_eq_two
    (T : NormalSingularSetTriangulation crossingProductCell (frontier crossingProductSide)) :
    T.complexity = 2 := by
  obtain ⟨e, -⟩ := crossingProductCell_exists_branch_equiv T
  rw [T.complexity_eq_natCard_branch, ← Nat.card_congr e]
  simp

theorem isPLBall_crossingProductSide : IsPLBall 3 crossingProductSide := by
  have hbox : IsPLBall 3 crossingProductBox :=
    isPLBall_three_prod
      (isPLBall_two_prod (isPLBall_Icc (by norm_num)) (isPLBall_Icc (by norm_num)))
      (isPLBall_Icc (by norm_num))
  apply hbox.of_isPLHomeomorphOn (f := ⇑spliceEmbedding)
  have hpa : IsPiecewiseAffineOn (⇑spliceEmbedding) univ :=
    isPiecewiseAffineOn_of_affine spliceEmbedding.toLinearMap.toAffineMap isOpen_univ
  exact isPLHomeomorphOn_of_isPiecewiseAffineOn_of_bijOn
    isHPolytope_crossingProductBox.isPolyhedron
    (hpa.mono_of_isPolyhedron isHPolytope_crossingProductBox.isPolyhedron (subset_univ _))
    spliceEmbedding.injective.injOn.bijOn_image

theorem crossingProductCell_exists_boundaryTube {B : Set (EuclideanSpace ℝ (Fin 3))}
    (hD : NormalSingularCellData crossingProductCell (frontier crossingProductSide) B) :
    ∃ (c d : hD.singularSet.Branch)
      (T : CrossSeamTubeData hD c (spliceEmbedding '' tubeWitnessTube)),
      c ≠ d ∧ hD.singularSet.IsBoundaryBranch c ∧ hD.singularSet.IsBoundaryBranch d ∧
        hD.singularSet.branchCarrier c = spliceEmbedding '' spliceCore ∧
        hD.singularSet.branchCarrier d = crossingProductBranchCarrier true ∧
        T.chart = ⇑spliceEmbedding ∧
        Nonempty (PLSeamTubeChart (EuclideanSpace ℝ (Fin 3)) T.chart) ∧
        T.chart '' spliceCylinder ⊆ crossingProductSide ∧
        T.chart '' spliceCylinder ∩ frontier crossingProductSide = T.chart '' spliceEndDisks := by
  obtain ⟨e, he⟩ := crossingProductCell_exists_branch_equiv hD.singularSet
  have hcore : hD.singularSet.branchCarrier (e false) = spliceEmbedding '' spliceCore := by
    simpa only [crossingProductBranchCarrier, Bool.false_eq_true, ↓reduceIte, spliceCore] using
      (he false).1
  let T : CrossSeamTubeData hD (e false) (spliceEmbedding '' tubeWitnessTube) := {
    chart := spliceEmbedding
    isTube := by
      rw [hcore]
      exact crossSeamTubeCore_crossingProductCell }
  refine ⟨e false, e true, T, fun h => Bool.noConfusion (e.injective h),
    (he false).2, (he true).2, hcore, (he true).1, rfl, ?_,
    crossingProductTube_side, crossingProductTube_boundary⟩
  exact nonempty_plSeamTubeChart_spliceEmbedding

end DifferentialGeometry.Topology.PiecewiseLinear
