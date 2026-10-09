/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.LoopTheorem.BoundaryBranchCrosscut
import DifferentialGeometry.Topology.PiecewiseLinear.InnermostLevel
import DifferentialGeometry.Topology.PlanarJordan.CompactRegion

open Set Topology

namespace DifferentialGeometry.Topology.PiecewiseLinear

universe u

theorem injOn_of_doublePointPreimage_inter_subset {X Y : Type*} {f : X → Y}
    {P Q J : Set X} (hQP : Q ⊆ P) (hinter : doublePointPreimage f P ∩ Q ⊆ J)
    (hJ : InjOn f J) : InjOn f Q := by
  intro x hx y hy hxy
  by_contra hne
  have hxP : x ∈ P := hQP hx
  have hyP : y ∈ P := hQP hy
  have hxDouble : x ∈ doublePointPreimage f P :=
    ⟨hxP, x, hxP, y, hyP, hne, rfl, hxy.symm⟩
  have hyDouble : y ∈ doublePointPreimage f P :=
    ⟨hyP, y, hyP, x, hxP, Ne.symm hne, rfl, hxy⟩
  exact hne (hJ (hinter ⟨hxDouble, hx⟩) (hinter ⟨hyDouble, hy⟩) hxy)

theorem image_inter_doublePointSet_eq_empty_of_disjoint_doublePointPreimage
    {X Y : Type*} {f : X → Y} {P S : Set X} (hSP : S ⊆ P)
    (hdisjoint : Disjoint (doublePointPreimage f P) S) :
    f '' S ∩ doublePointSet f P = ∅ := by
  apply eq_empty_iff_forall_notMem.mpr
  rintro y ⟨⟨x, hxS, rfl⟩, hy⟩
  exact Set.disjoint_left.mp hdisjoint ⟨hSP hxS, hy⟩ hxS

theorem disjoint_doublePointPreimage_interior_of_inter_subset_frontier
    {X : Type*} [TopologicalSpace X] {Y : Type*} {f : X → Y} {P Q : Set X}
    (hinter : doublePointPreimage f P ∩ Q ⊆ frontier Q) :
    Disjoint (doublePointPreimage f P) (interior Q) := by
  apply Set.disjoint_left.mpr
  intro x hxDouble hxint
  have hxQ : x ∈ Q := interior_subset hxint
  exact (mem_interior_iff_notMem_frontier hxQ).mp hxint (hinter ⟨hxDouble, hxQ⟩)

theorem image_interior_inter_doublePointSet_eq_empty_of_inter_subset_frontier
    {X : Type*} [TopologicalSpace X] {Y : Type*} {f : X → Y} {P Q : Set X}
    (hQP : Q ⊆ P) (hinter : doublePointPreimage f P ∩ Q ⊆ frontier Q) :
    f '' interior Q ∩ doublePointSet f P = ∅ :=
  image_inter_doublePointSet_eq_empty_of_disjoint_doublePointPreimage
    (interior_subset.trans hQP)
    (disjoint_doublePointPreimage_interior_of_inter_subset_frontier hinter)

theorem image_inter_doublePointSet_eq_image_frontier_of_inter_eq_frontier
    {X : Type*} [TopologicalSpace X] {Y : Type*} {f : X → Y} {P Q : Set X}
    (hQP : Q ⊆ P) (hinter : doublePointPreimage f P ∩ Q = frontier Q) :
    f '' Q ∩ doublePointSet f P = f '' frontier Q := by
  apply Subset.antisymm
  · rintro y ⟨⟨x, hxQ, rfl⟩, hy⟩
    exact ⟨x, hinter.subset ⟨⟨hQP hxQ, hy⟩, hxQ⟩, rfl⟩
  · rintro y ⟨x, hx, rfl⟩
    obtain ⟨hxDouble, hxQ⟩ := hinter.symm.subset hx
    exact ⟨⟨x, hxQ, rfl⟩, hxDouble.2⟩

theorem isPLBall_subset_interior_of_frontier_subset_interior
    {Q P : Set (EuclideanSpace ℝ (Fin 2))} (hQ : IsPLBall 2 Q) (hP : IsPLBall 2 P)
    (hfrontier : frontier Q ⊆ interior P) : Q ⊆ interior P := by
  have hQclosure : closure (Schoenflies.inside (frontier Q)) = Q :=
    PlanarJordan.closure_inside_frontier_eq_of_isCompact hQ.isPolyhedron.isCompact
      (isJordanCurve_of_isPLSphere_one hQ.isPLSphere_frontier) hQ.interior_nonempty
  have hPclosure : closure (Schoenflies.inside (frontier P)) = P :=
    PlanarJordan.closure_inside_frontier_eq_of_isCompact hP.isPolyhedron.isCompact
      (isJordanCurve_of_isPLSphere_one hP.isPLSphere_frontier) hP.interior_nonempty
  have hfrontier' : frontier Q ⊆ closure (Schoenflies.inside (frontier P)) := by
    rw [← hP.interior_eq_inside_frontier]
    exact hfrontier.trans subset_closure
  have hinside : Schoenflies.inside (frontier Q) ⊆ Schoenflies.inside (frontier P) :=
    PlanarJordan.inside_subset_of_subset_closure_inside
      (Schoenflies.jordan_curve_theorem
        (isJordanCurve_of_isPLSphere_one hP.isPLSphere_frontier))
      (Schoenflies.jordan_curve_theorem
        (isJordanCurve_of_isPLSphere_one hQ.isPLSphere_frontier)) hfrontier'
  have hsub : Q ⊆ P := by
    rw [← hQclosure, ← hPclosure]
    exact closure_mono hinside
  intro x hxQ
  by_cases hxfrontier : x ∈ frontier Q
  · exact hfrontier hxfrontier
  · exact interior_mono hsub ((mem_interior_iff_notMem_frontier hxQ).mpr hxfrontier)

theorem exists_innermost_isPLBall_subset_interior
    {P : Set (EuclideanSpace ℝ (Fin 2))} (hP : IsPLBall 2 P)
    {C : Set (Set (EuclideanSpace ℝ (Fin 2)))} (hC : C.Finite) (hne : C.Nonempty)
    (hsphere : ∀ J ∈ C, IsPLSphere 1 J) (hCsub : ∀ J ∈ C, J ⊆ interior P)
    (p : EuclideanSpace ℝ (Fin 2))
    (hinter : ∀ J ∈ C, ∀ T ∈ C, J ≠ T → J ∩ T ⊆ {p}) :
    ∃ J ∈ C, ∃ Q : Set (EuclideanSpace ℝ (Fin 2)),
      IsPLBall 2 Q ∧ Q ⊆ interior P ∧ frontier Q = J ∧ (⋃₀ C) ∩ Q = J ∧
        (⋃₀ C) ∩ interior Q = ∅ := by
  obtain ⟨J, hJC, Q, hQ, hfrontier, hQinter⟩ :=
    exists_innermost_isPLBall hC hne hsphere p hinter
  refine ⟨J, hJC, Q, hQ, ?_, hfrontier, hQinter, ?_⟩
  · apply isPLBall_subset_interior_of_frontier_subset_interior hQ hP
    rw [hfrontier]
    exact hCsub J hJC
  · apply eq_empty_iff_forall_notMem.mpr
    rintro x ⟨hxC, hxint⟩
    have hxQ : x ∈ Q := interior_subset hxint
    have hxJ : x ∈ frontier Q := hfrontier.symm.subset (hQinter.subset ⟨hxC, hxQ⟩)
    exact (mem_interior_iff_notMem_frontier hxQ).mp hxint hxJ

theorem exists_innermost_isPLBall_subset_interior_of_pairwiseDisjoint
    {P : Set (EuclideanSpace ℝ (Fin 2))} (hP : IsPLBall 2 P)
    {C : Set (Set (EuclideanSpace ℝ (Fin 2)))} (hC : C.Finite) (hne : C.Nonempty)
    (hsphere : ∀ J ∈ C, IsPLSphere 1 J) (hCsub : ∀ J ∈ C, J ⊆ interior P)
    (hdisjoint : C.PairwiseDisjoint id) :
    ∃ J ∈ C, ∃ Q : Set (EuclideanSpace ℝ (Fin 2)),
      IsPLBall 2 Q ∧ Q ⊆ interior P ∧ frontier Q = J ∧ (⋃₀ C) ∩ Q = J ∧
        (⋃₀ C) ∩ interior Q = ∅ := by
  apply exists_innermost_isPLBall_subset_interior hP hC hne hsphere hCsub 0
  intro J hJ T hT hJT
  exact (hdisjoint hJ hT hJT).le_bot.trans (empty_subset _)

namespace SingularTwoCell

variable {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]

theorem restrict_isNonsingular_of_doublePointPreimage_inter_subset
    (D : SingularTwoCell M) {Q J : Set (EuclideanSpace ℝ (Fin 2))}
    (hQ : IsPLBall 2 Q) (hQsub : Q ⊆ D.domain)
    (hinter : doublePointPreimage D D.domain ∩ Q ⊆ J) (hJ : InjOn D J) :
    (D.restrict hQ hQsub).IsNonsingular :=
  (D.restrict_isNonsingular_iff hQ hQsub).mpr
    (injOn_of_doublePointPreimage_inter_subset hQsub hinter hJ)

theorem image_interior_inter_doublePointSet_eq_empty
    (D : SingularTwoCell M) {Q : Set (EuclideanSpace ℝ (Fin 2))} (hQsub : Q ⊆ D.domain)
    (hinter : doublePointPreimage D D.domain ∩ Q ⊆ frontier Q) :
    D '' interior Q ∩ doublePointSet D D.domain = ∅ :=
  image_interior_inter_doublePointSet_eq_empty_of_inter_subset_frontier hQsub hinter

theorem image_inter_doublePointSet_eq_image_frontier
    (D : SingularTwoCell M) {Q : Set (EuclideanSpace ℝ (Fin 2))} (hQsub : Q ⊆ D.domain)
    (hinter : doublePointPreimage D D.domain ∩ Q = frontier Q) :
    D '' Q ∩ doublePointSet D D.domain = D '' frontier Q :=
  image_inter_doublePointSet_eq_image_frontier_of_inter_eq_frontier hQsub hinter

end SingularTwoCell

namespace NormalSingularCellData

variable {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
  {D : SingularTwoCell M} {BdM B : Set M}

theorem exists_innermost_cleanDisk_of_exists_not_boundaryBranch
    [T2Space M] (hD : NormalSingularCellData D BdM B)
    (hclosed : ∃ c : hD.singularSet.Branch,
      ¬hD.singularSet.IsBoundaryBranch c) :
    ∃ c : hD.singularSet.Branch,
    ∃ J Q : Set (EuclideanSpace ℝ (Fin 2)),
      ¬hD.singularSet.IsBoundaryBranch c ∧ IsPLSphere 1 J ∧
        IsPLBall 2 Q ∧ Q ⊆ interior D.domain ∧ frontier Q = J ∧
          doublePointPreimage D D.domain ∩ Q = J ∧
            D '' interior Q ∩ doublePointSet D D.domain = ∅ ∧
              D '' Q ∩ doublePointSet D D.domain = D '' J ∧
                (hD.branchPreimage c = J ∨
                  ∃ T : Set (EuclideanSpace ℝ (Fin 2)),
                    IsPLSphere 1 T ∧ Disjoint J T ∧
                      hD.branchPreimage c = J ∪ T ∧ InjOn D Q) := by
  obtain ⟨c, J, Q, hc, hJ, hQ, hQsub, hfrontier, hfull, hsplit⟩ :=
    hD.exists_innermost_isPLBall_doublePointPreimage_decomposition_with_coordinate
      hclosed
  have hQdomain : Q ⊆ D.domain := hQsub.trans interior_subset
  have hinterFrontier : doublePointPreimage D D.domain ∩ Q = frontier Q := by
    rw [hfull, hfrontier]
  refine ⟨c, J, Q, hc, hJ, hQ, hQsub, hfrontier, hfull,
    D.image_interior_inter_doublePointSet_eq_empty hQdomain hinterFrontier.subset,
    (D.image_inter_doublePointSet_eq_image_frontier hQdomain hinterFrontier).trans
      (congrArg (fun S => D '' S) hfrontier), ?_⟩
  rcases hsplit with hsingle | ⟨T, hT, hdisjoint, hcover, hJcoordinate, -⟩
  · exact Or.inl hsingle
  · have hJsub : J ⊆ hD.branchPreimage c := by
      rw [hcover]
      exact subset_union_left
    exact Or.inr ⟨T, hT, hdisjoint, hcover,
      hD.injOn_of_doublePointPreimage_inter_eq_of_branchCoordinate hJsub hQdomain
        hfull hJcoordinate⟩

end NormalSingularCellData

end DifferentialGeometry.Topology.PiecewiseLinear
