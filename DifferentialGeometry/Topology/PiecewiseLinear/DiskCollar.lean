/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.BoundaryDiskPush
import DifferentialGeometry.Topology.PiecewiseLinear.PrismBoundary
import DifferentialGeometry.Topology.PiecewiseLinear.SphericalDiskExtension

open Set

namespace DifferentialGeometry.Topology.PiecewiseLinear

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

open Classical in
theorem IsCombinatorialManifoldWithBoundary.exists_collar_of_boundary_disk
    {K : Geometry.SimplicialComplex ℝ E} [Finite K.faces]
    (hK : IsCombinatorialManifoldWithBoundary 3 K) {D : Set E}
    (hD : IsPLBall 2 D) (hDK : D ⊆ (boundaryComplex 3 K).space) :
    ∃ (C : Set E) (ρ : E × ℝ → E),
      IsPLHomeomorphOn ρ (D ×ˢ Icc 0 1) C ∧ C ⊆ K.space ∧
      C ∩ (boundaryComplex 3 K).space = D ∧ (∀ x ∈ D, ρ (x, 0) = x) ∧
      MapsTo ρ (D ×ˢ Ioc 0 1) (K.space \ (boundaryComplex 3 K).space) := by
  classical
  let _ : DecidableEq (E × ℝ) := Classical.decEq _
  obtain ⟨L, hLfin, hL, hLK, hmeet, hDL⟩ := hK.exists_isPLBall_inter_boundaryComplex_eq hD hDK
  let _ : Finite L.faces := hLfin.to_subtype
  have hP : IsPLBall 3 (D ×ˢ Icc (0 : ℝ) 1) :=
    isPLBall_three_prod hD (isPLBall_Icc (by norm_num))
  obtain ⟨A, hAfin, hAP⟩ := hP.isPolyhedron.exists_simplicialComplex
  let _ : Finite A.faces := hAfin.to_subtype
  have hA : IsPLBall 3 A.space := hAP.symm ▸ hP
  have hbase : IsPLBall 2 (D ×ˢ {(0 : ℝ)}) :=
    hD.of_isPLHomeomorphOn (hD.isPolyhedron.isPLHomeomorphOn_prod_const 0)
  have hbaseA : D ×ˢ {(0 : ℝ)} ⊆ (boundaryComplex 3 A).space :=
    prod_left_endpoint_subset_boundaryComplex hD (by norm_num) A hAP
  obtain ⟨ρ, hρ, hfix⟩ := exists_isPLHomeomorphOn_eqOn_disk_of_boundaryComplex A L hA hL
    hbase hbaseA (hD.isPolyhedron.isPLHomeomorphOn_fst_prod_const 0) hDL
  rw [hAP] at hρ
  refine ⟨L.space, ρ, hρ, hLK, hmeet, fun x hx => hfix ⟨hx, rfl⟩, ?_⟩
  rintro z ⟨hzD, hzt, hzt1⟩
  have hzDom : z ∈ D ×ˢ Icc (0 : ℝ) 1 := ⟨hzD, hzt.le, hzt1⟩
  have hzL := hρ.bijOn.mapsTo hzDom
  refine ⟨hLK hzL, ?_⟩
  intro hzB
  have hzD' : ρ z ∈ D := hmeet ▸ ⟨hzL, hzB⟩
  have hyDom : (ρ z, (0 : ℝ)) ∈ D ×ˢ Icc (0 : ℝ) 1 := ⟨hzD', le_rfl, zero_le_one⟩
  have heq := hρ.bijOn.injOn hzDom hyDom (hfix (show (ρ z, (0 : ℝ)) ∈ D ×ˢ {0}
    from ⟨hzD', rfl⟩)).symm
  exact (ne_of_gt hzt) (congrArg Prod.snd heq)

end DifferentialGeometry.Topology.PiecewiseLinear
