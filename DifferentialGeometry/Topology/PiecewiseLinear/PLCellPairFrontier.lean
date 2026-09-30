/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.PLCellPullback
import DifferentialGeometry.Topology.PiecewiseLinear.PLCellOnBoundary
import DifferentialGeometry.Topology.PiecewiseLinear.BallUnionMeetingDisk
import DifferentialGeometry.Topology.PiecewiseLinear.BallUnionFrontier

open Set

namespace DifferentialGeometry.Topology.PiecewiseLinear

local notation "E3" => EuclideanSpace ℝ (Fin 3)

theorem IsPLCellOn.boundary_subset_frontier_union_of_model
    {M : Type*} [TopologicalSpace M] [T2Space M] [ChartedSpace E3 M]
    {A B Ab Bb Db Ubd : Set M} (hA : IsPLCellOn 3 A Ab) (hB : IsPLCellOn 3 B Bb)
    (hD : IsPLCellOn 2 (A ∩ B) Db) (hU : IsPLCellOn 3 (A ∪ B) Ubd) :
    Db ⊆ frontier (A ∪ B) := by
  classical
  obtain ⟨P, p, u, hp, hu, hUP, -⟩ := hU
  let g := Function.invFunOn u P
  have hAU : A ⊆ u '' P := by rw [← hUP]; exact subset_union_left
  have hBU : B ⊆ u '' P := by rw [← hUP]; exact subset_union_right
  obtain ⟨a, ha, -⟩ := hA.exists_isPLHomeomorphOn_invFunOn hu hAU
  obtain ⟨b, hb, -⟩ := hB.exists_isPLHomeomorphOn_invFunOn hu hBU
  obtain ⟨q, hq, hqb⟩ := hD.exists_isPLHomeomorphOn_invFunOn hu
    (inter_subset_left.trans hAU)
  have hg : InjOn g (u '' P) := Function.invFunOn_injOn_image u P
  have hinter : g '' (A ∩ B) = g '' A ∩ g '' B := hg.image_inter hAU hBU
  have hq' : IsPLHomeomorphOn q (Convexity.StdSimplex.coordinateSet ℝ (Fin 3)) (g '' A ∩ g '' B) := hinter ▸ hq
  have hAa : IsPLBall 3 (g '' A) := ⟨a, ha⟩
  have hBb : IsPLBall 3 (g '' B) := ⟨b, hb⟩
  have hDa : g '' A ∩ g '' B ⊆ frontier (g '' A) :=
    hBb.inter_subset_frontier_of_isPLBall (show IsPLBall 2 _ from ⟨q, hq'⟩) (by decide)
  let C : Bool → Set E3 := fun i => cond i (g '' A) (g '' B)
  have hC : ∀ i, IsPLBall 3 (C i) := by
    intro i
    cases i
    · exact hBb
    · exact hAa
  have h3 : ∀ i j k : Bool, i ≠ j → k ≠ i → k ≠ j →
      Disjoint (C i ∩ C j) (C k) := by
    intro i j k hij hki hkj
    exfalso
    cases i <;> cases j <;> cases k <;> simp_all
  have hbound := image_stdSimplexBoundary_subset_frontier_iUnion hC h3
    (show (true : Bool) ≠ false by decide) hq' hDa
  have hcover : (⋃ i, C i) = P := by
    rw [← union_eq_iUnion, ← image_union, hUP]
    rw [image_image]
    exact (image_congr fun x hx => hu.injOn.leftInvOn_invFunOn hx).trans (image_id P)
  rw [hcover, ← hqb] at hbound
  have hPcompact : IsCompact P := (IsPLBall.isPolyhedron ⟨p, hp⟩).isCompact
  intro y hy
  have hyU : y ∈ u '' P := ((hD.boundary_subset.trans inter_subset_left).trans hAU) hy
  have hgy : g y ∈ frontier P := hbound ⟨y, hy, rfl⟩
  have hfr : u '' frontier P = frontier (A ∪ B) := by
    rw [hu.image_frontier_of_isCompact hPcompact, ← hUP]
  rw [← hfr]
  exact ⟨g y, hgy, hu.injOn.bijOn_image.invOn_invFunOn.2 hyU⟩

theorem IsPLCellOn.sdiff_subset_interior_union_of_model
    {M : Type*} [TopologicalSpace M] [ChartedSpace E3 M]
    {A B Ab Bb Db Ubd : Set M} (hA : IsPLCellOn 3 A Ab) (hB : IsPLCellOn 3 B Bb)
    (hD : IsPLCellOn 2 (A ∩ B) Db) (hU : IsPLCellOn 3 (A ∪ B) Ubd) :
    (A ∩ B) \ Db ⊆ interior (A ∪ B) := by
  classical
  obtain ⟨P, p, u, hp, hu, hUP, -⟩ := hU
  let g := Function.invFunOn u P
  have hAU : A ⊆ u '' P := by rw [← hUP]; exact subset_union_left
  have hBU : B ⊆ u '' P := by rw [← hUP]; exact subset_union_right
  obtain ⟨a, ha, -⟩ := hA.exists_isPLHomeomorphOn_invFunOn hu hAU
  obtain ⟨b, hb, -⟩ := hB.exists_isPLHomeomorphOn_invFunOn hu hBU
  obtain ⟨q, hq, hqb⟩ := hD.exists_isPLHomeomorphOn_invFunOn hu
    (inter_subset_left.trans hAU)
  have hg : InjOn g (u '' P) := Function.invFunOn_injOn_image u P
  have hinter : g '' (A ∩ B) = g '' A ∩ g '' B := hg.image_inter hAU hBU
  have hq' : IsPLHomeomorphOn q (Convexity.StdSimplex.coordinateSet ℝ (Fin 3)) (g '' A ∩ g '' B) := hinter ▸ hq
  have hAa : IsPLBall 3 (g '' A) := ⟨a, ha⟩
  have hBb : IsPLBall 3 (g '' B) := ⟨b, hb⟩
  have hDa : g '' A ∩ g '' B ⊆ frontier (g '' A) :=
    hBb.inter_subset_frontier_of_isPLBall (show IsPLBall 2 _ from ⟨q, hq'⟩) (by decide)
  have hDb : g '' A ∩ g '' B ⊆ frontier (g '' B) := by
    have hq'' : IsPLBall 2 (g '' B ∩ g '' A) := by rw [inter_comm]; exact ⟨q, hq'⟩
    rw [inter_comm]
    exact hAa.inter_subset_frontier_of_isPLBall hq'' (by decide)
  have hcover : g '' A ∪ g '' B = P := by
    rw [← image_union, hUP]
    exact hu.injOn.invFunOn_image (Subset.refl P)
  have hkey := sdiff_subset_interior_union_of_inter_eq hAa hBb hq' rfl hDa hDb
  rw [hcover, ← hqb] at hkey
  rintro y ⟨hy, hyb⟩
  have hyP : y ∈ u '' P := hAU hy.1
  have hgy : g y ∈ interior P := by
    apply hkey
    refine ⟨hinter.subset ⟨y, hy, rfl⟩, ?_⟩
    rintro ⟨z, hz, hzy⟩
    exact hyb (hg ((hD.boundary_subset.trans inter_subset_left).trans hAU hz) hyP hzy ▸ hz)
  rw [hUP, ← hu.image_interior]
  exact ⟨g y, hgy, hu.injOn.bijOn_image.invOn_invFunOn.2 hyP⟩

end DifferentialGeometry.Topology.PiecewiseLinear
