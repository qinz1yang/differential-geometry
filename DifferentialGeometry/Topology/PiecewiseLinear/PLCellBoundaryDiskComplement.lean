/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.PLCellOnBoundary
import DifferentialGeometry.Topology.PiecewiseLinear.PLCellPullback
import DifferentialGeometry.Topology.PiecewiseLinear.PLModelCellRestriction
import DifferentialGeometry.Topology.PiecewiseLinear.SphericalDiskComplement

open Set

namespace DifferentialGeometry.Topology.PiecewiseLinear

local notation "E3" => EuclideanSpace ℝ (Fin 3)

theorem IsPLCellOn.isPLCellOn_closure_boundary_sdiff
    {M : Type*} [TopologicalSpace M] [T2Space M] [ChartedSpace E3 M]
    {B Bb D Db : Set M} (hB : IsPLCellOn 3 B Bb) (hD : IsPLCellOn 2 D Db)
    (hDB : D ⊆ Bb) :
    IsPLCellOn 2 (closure (Bb \ D)) Db ∧ D ∩ closure (Bb \ D) = Db := by
  classical
  have hDbD := hD.boundary_subset
  have hBbB := hB.boundary_subset
  obtain ⟨P, p, u, hp, hu, hBP, hBbP⟩ := hB
  have hP : IsPLBall 3 P := ⟨p, hp⟩
  have hfrontP : frontier P ⊆ P := hP.isPolyhedron.isClosed.frontier_subset
  have hfront : u '' frontier P = Bb := by
    rw [← hp.image_stdSimplexBoundary]
    exact hBbP.symm
  let g := Function.invFunOn u P
  have hleft : LeftInvOn g u P := hu.injOn.leftInvOn_invFunOn
  have hDQ : D ⊆ u '' P := by
    rw [← hBP]
    exact hDB.trans hBbB
  have hDbQ : Db ⊆ u '' P := hDbD.trans hDQ
  have himage (Z : Set M) (hZ : Z ⊆ u '' P) : u '' (g '' Z) = Z := by
    apply Subset.antisymm
    · rintro _ ⟨z, ⟨y, hy, rfl⟩, rfl⟩
      rwa [hu.injOn.bijOn_image.invOn_invFunOn.2 (hZ hy)]
    · intro y hy
      exact ⟨g y, ⟨y, hy, rfl⟩, hu.injOn.bijOn_image.invOn_invFunOn.2 (hZ hy)⟩
  obtain ⟨q, hq, hqb⟩ := hD.exists_isPLHomeomorphOn_invFunOn hu hDQ
  have hDF : g '' D ⊆ frontier P := by
    rintro _ ⟨y, hy, rfl⟩
    obtain ⟨z, hz, hzy⟩ := hfront.symm ▸ hDB hy
    rw [← hzy, hleft (hfrontP hz)]
    exact hz
  let Q := closure (frontier P \ g '' D)
  have hS := hP.isPLSphere_frontier
  have hQ : IsPLBall 2 Q := hS.isPLBall_closure_sdiff ⟨q, hq⟩ hDF
  have hQF : Q ⊆ frontier P := closure_minimal sdiff_subset isClosed_frontier
  have hQP : Q ⊆ P := hQF.trans hfrontP
  obtain ⟨r, hr⟩ := hQ
  have hQr : IsPLBall 2 Q := ⟨r, hr⟩
  have hbound : r '' stdSimplexBoundary 2 = g '' Db := by
    rw [hS.image_stdSimplexBoundary_complement ⟨q, hq⟩ hDF hr, inter_comm,
      hS.inter_closure_sdiff_eq_image_stdSimplexBoundary hq hDF, ← hqb]
  have hdiff : u '' (frontier P \ g '' D) = Bb \ D := by
    rw [(hu.injOn.mono hfrontP).image_sdiff_subset hDF, hfront, himage D hDQ]
  have hcont : ContinuousOn u Q := hu.continuousOn.mono hQP
  have himageQ : u '' Q = closure (Bb \ D) := by
    rw [← hdiff]
    exact image_closure_of_isCompact hQr.isPolyhedron.isCompact hcont
  have huQpl := hu.isPLOn.mono_of_isPolyhedron hQr.isPolyhedron hQP
  have huQ : IsPLHomeomorphInto 3 u Q :=
    huQpl.isPLHomeomorphInto_of_isCompact hQr.isPolyhedron.isCompact (hu.injOn.mono hQP)
  refine ⟨⟨Q, r, u, hr, huQ, himageQ.symm, ?_⟩, ?_⟩
  · rw [hbound, himage Db hDbQ]
  · calc
      D ∩ closure (Bb \ D) = u '' ((g '' D) ∩ Q) := by
        rw [hu.injOn.image_inter (hDF.trans hfrontP) hQP, himage D hDQ, himageQ]
      _ = u '' (q '' stdSimplexBoundary 2) := by
        rw [hS.inter_closure_sdiff_eq_image_stdSimplexBoundary hq hDF]
      _ = Db := by rw [← hqb, himage Db hDbQ]

end DifferentialGeometry.Topology.PiecewiseLinear
