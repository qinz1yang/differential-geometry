/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.UpperLinkBoundary
import DifferentialGeometry.Topology.PiecewiseLinear.CircleFourPoints
import DifferentialGeometry.Topology.PiecewiseLinear.LoopTheorem.BoundaryBranchCrosscut

open Set

namespace DifferentialGeometry.Topology.PiecewiseLinear

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

open Classical in
theorem exists_parametrization_derivedNeighborhoodCellBase_inter
    (K L : Geometry.SimplicialComplex ℝ E) [Finite L.faces]
    (hL : IsCombinatorialManifoldWithBoundary 2 L) (hLK : L.faces ⊆ K.faces)
    {s : Finset E} (hs : s ∈ (boundaryComplex 2 L).faces) {p q : E}
    (hboundary : (derivedNeighborhoodCellBase K s).space ∩ (boundaryComplex 2 L).space =
      {p, q}) :
    ∃ γ : ℝ → E,
      IsPLHomeomorphOn γ (Icc 0 1) ((derivedNeighborhoodCellBase K s).space ∩ L.space) ∧
      γ 0 = p ∧ γ 1 = q := by
  let _ : Finite (boundaryComplex 2 L).faces := (boundaryComplex_faces_finite 2 L).to_subtype
  let A := derivedNeighborhoodCellBase L s
  let _ : Finite A.faces := (upperLink_faces_finite _ _).to_subtype
  have hA : IsPLBall 1 A.space := hL.isPLBall_derivedNeighborhoodCellBase hs
  have hAb : (boundaryComplex 1 A).space = {p, q} := by
    change (boundaryComplex 1 (derivedNeighborhoodCellBase L s)).space = _
    rw [boundaryComplex_derivedNeighborhoodCellBase L hL hs]
    rw [← derivedNeighborhoodCellBase_inter_subcomplex K (boundaryComplex 2 L)
      ((boundaryComplex_faces_subset 2 L).trans hLK) hs]
    exact hboundary
  obtain ⟨γ, hγ, hγb⟩ :=
    IsPLHomeomorphOn.exists_parametrization_Icc_boundaryComplex hA A
      (isPolyhedron_space A).isPLHomeomorphOn_id
  have h0 : (0 : ℝ) ∈ Icc (0 : ℝ) 1 := ⟨le_rfl, zero_le_one⟩
  have h1 : (1 : ℝ) ∈ Icc (0 : ℝ) 1 := ⟨zero_le_one, le_rfl⟩
  have hγ0 : γ 0 = p ∨ γ 0 = q := by
    have h := (hγb 0 h0).mpr (Or.inl rfl)
    change γ 0 ∈ (boundaryComplex 1 A).space at h
    simpa only [hAb, mem_insert_iff, mem_singleton_iff] using h
  have hγ1 : γ 1 = p ∨ γ 1 = q := by
    have h := (hγb 1 h1).mpr (Or.inr rfl)
    change γ 1 ∈ (boundaryComplex 1 A).space at h
    simpa only [hAb, mem_insert_iff, mem_singleton_iff] using h
  have hne : γ 0 ≠ γ 1 := fun h => zero_ne_one (hγ.bijOn.injOn h0 h1 h)
  have hγ' : IsPLHomeomorphOn γ (Icc 0 1)
      ((derivedNeighborhoodCellBase K s).space ∩ L.space) := by
    rw [derivedNeighborhoodCellBase_inter_subcomplex K L hLK
      (boundaryComplex_faces_subset 2 L hs)]
    exact hγ
  rcases hγ0 with hp | hq
  · exact ⟨γ, hγ', hp, hγ1.resolve_left fun h => hne (hp.trans h.symm)⟩
  · refine ⟨fun t => γ (1 - t), isPLHomeomorphOn_comp_one_sub hγ', ?_, ?_⟩
    · simpa only [sub_zero] using hγ1.resolve_right fun h => hne (hq.trans h.symm)
    · simpa only [sub_self] using hq

end DifferentialGeometry.Topology.PiecewiseLinear
