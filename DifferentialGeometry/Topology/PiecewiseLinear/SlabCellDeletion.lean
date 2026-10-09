/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.SubcomplexSlab
import DifferentialGeometry.Topology.PiecewiseLinear.HeightCellDeletion
import DifferentialGeometry.Topology.PiecewiseLinear.DiskCellDeletion
import DifferentialGeometry.Topology.PiecewiseLinear.RegionCellPush
import DifferentialGeometry.Topology.PiecewiseLinear.SlabFiberInterior

open Set

namespace DifferentialGeometry.Topology.PiecewiseLinear

open Classical in
theorem exists_isPLHomeomorphOn_slab_of_free_disk_cell_deletion (I : SchoenfliesInput)
    (K A : Geometry.SimplicialComplex ℝ (EuclideanSpace ℝ (Fin 3))) [Finite A.faces]
    (hAK : A.faces ⊆ K.faces) (hreg : closure (interior A.space) = A.space)
    (ℓ : EuclideanSpace ℝ (Fin 3) →L[ℝ] ℝ) (hℓ : ℓ ≠ 0) (hinj : InjOn ℓ K.vertices)
    {p : EuclideanSpace ℝ (Fin 3)} {a b : ℝ} (hab : a < b) (hpheight : ℓ p ∈ Icc a b)
    (hgap : ∀ v ∈ K.vertices, v ≠ p → ℓ v < a ∨ b < ℓ v)
    {P Q : Geometry.SimplicialComplex ℝ (EuclideanSpace ℝ (Fin 3)) × Finset (Set (EuclideanSpace ℝ
        (Fin 3)))}
    (hstep : IsFreeDiskCellDeletion (closedStar K p ∩ {x | ℓ x = ℓ p}) P Q)
    (hPspace : P.1.space = A.space ∩ {x | ℓ x = ℓ p})
    (hcells : P.2 ⊆ heightSectionCells 2 A ℓ.toLinearMap (ℓ p))
    (hS : IsPLSphere 2 (frontier (A.space ∩ ℓ ⁻¹' Icc a b)))
    {W : Set (EuclideanSpace ℝ (Fin 3))} (hW : IsOpen W) (hWconv : Convex ℝ W)
    (hSW : frontier (A.space ∩ ℓ ⁻¹' Icc a b) ⊆ W) :
    ∃ B : Geometry.SimplicialComplex ℝ (EuclideanSpace ℝ (Fin 3)), ∃ hBfin : B.faces.Finite,
      B.faces ⊆ A.faces ∧ closure (interior B.space) = B.space ∧
      (∀ s ∈ A.faces, p ∈ s → s ∈ B.faces) ∧
      Q.1.space = B.space ∩ {x | ℓ x = ℓ p} ∧ IsPLDiskDecomposition Q.1 Q.2 ∧
      Q.2 ⊆ @heightSectionCells _ _ _ 2 B hBfin.to_subtype ℓ.toLinearMap (ℓ p) ∧
      ∃ H : EuclideanSpace ℝ (Fin 3) ≃ₜ EuclideanSpace ℝ (Fin 3),
        IsPLHomeomorphOn H univ univ ∧ EqOn H id Wᶜ ∧
        H '' frontier (A.space ∩ ℓ ⁻¹' Icc a b) = frontier (B.space ∩ ℓ ⁻¹' Icc a b) := by
  classical
  let _ : DecidableEq (EuclideanSpace ℝ (Fin 3)) := Classical.decEq _
  obtain ⟨hdec, C, hC, hnot, hfree, hQcomplex, hQcells⟩ := hstep
  let _ : Finite P.1.faces := hdec.finite_faces.to_subtype
  obtain ⟨T, hT, hTcard, -, -, hCeq⟩ := mem_heightSectionCells_iff.mp (hcells hC)
  have hpnot : p ∉ T := by
    intro hpT
    apply hnot
    rw [hCeq]
    rintro x ⟨hxT, hxp⟩
    exact ⟨mem_iUnion₂.mpr ⟨T, ⟨hAK hT, subset_convexHull ℝ _ hpT⟩, hxT⟩, hxp⟩
  have hvertices : ∀ v ∈ T, ℓ v < a ∨ b < ℓ v := fun v hv =>
    hgap v (K.down_closed (hAK hT) (Finset.singleton_subset_iff.mpr hv) (Finset.singleton_nonempty
        v))
      (fun h => hpnot (h ▸ hv))
  have havoidT : ∀ v ∈ T, ℓ v ≠ a ∧ ℓ v ≠ b := by
    intro v hv
    rcases hvertices v hv with hlow | hhigh
    · exact ⟨hlow.ne, (hlow.trans hab).ne⟩
    · exact ⟨(hab.trans hhigh).ne', hhigh.ne'⟩
  let B := subcomplexGeneratedBy A {s | ¬s ⊆ T}
  have hBfin : B.faces.Finite := subcomplexGeneratedBy_faces_finite A _
  let _ : Finite B.faces := hBfin.to_subtype
  have hBA : B.faces ⊆ A.faces := subcomplexGeneratedBy_faces_subset A _
  have hBspace : B.space = closure (A.space \ convexHull ℝ (T : Set (EuclideanSpace ℝ (Fin 3)))) :=
    (closure_space_sdiff_convexHull_eq_subcomplexGeneratedBy A A Subset.rfl hT).symm
  have hBreg : closure (interior B.space) = B.space := by
    rw [hBspace]
    exact Topology.closure_interior_closure_sdiff hreg (T.finite_toSet.isCompact_convexHull
        ℝ).isClosed
  have hkeep : ∀ s ∈ A.faces, p ∈ s → s ∈ B.faces := by
    intro s hs hps
    exact ⟨s, ⟨hs, fun hst => hpnot (hst hps)⟩, Finset.Subset.rfl, A.nonempty_of_mem_faces hs⟩
  have hnew := hdec.erase_of_isFreeDiskCell hC hfree
  have hQdec : IsPLDiskDecomposition Q.1 Q.2 := by rwa [hQcomplex, hQcells]
  have hQspace : Q.1.space = closure (P.1.space \ C) := by
    rw [hQcomplex]
    exact hnew.space_eq.trans (hdec.closure_sdiff_cell_eq_biUnion_erase hC).symm
  have hfiber : Q.1.space = B.space ∩ {x | ℓ x = ℓ p} := by
    rw [hQspace, hPspace, hCeq]
    exact (fiber_subcomplexGeneratedBy_eq_closure_sdiff A (by simp) hreg hT hTcard ℓ.toLinearMap
      (hinj.mono (fun _ hv => hAK hv)) (fun v hv => by
        rcases hvertices v hv with hlow | hhigh
        · exact (hlow.trans_le hpheight.1).ne
        · exact (hpheight.2.trans_lt hhigh).ne')).symm
  have hQheight : Q.2 ⊆ heightSectionCells 2 B ℓ.toLinearMap (ℓ p) := by
    intro D hD
    rw [hQcells] at hD
    have hDmem := Finset.mem_erase.mp hD
    apply heightSectionCells_erase_subset_subcomplexGeneratedBy A hTcard ℓ.toLinearMap (ℓ p)
    rw [← hCeq]
    exact Finset.mem_erase.mpr ⟨hDmem.1, hcells hDmem.2⟩
  let Z := convexHull ℝ (T : Set (EuclideanSpace ℝ (Fin 3))) ∩ ℓ ⁻¹' Icc a b
  have hZpoly : IsHPolytope Z :=
    (isHPolytope_convexHull_of_affineIndependent T (A.indep hT)).inter_preimage isHPolytope_Icc
        ℓ.toLinearMap.toAffineMap
  have hZne : Z.Nonempty := by
    obtain ⟨x, hx⟩ := (hdec.cell_isPLBall C hC).nonempty
    rw [hCeq] at hx
    exact ⟨x, hx.1, by change a ≤ ℓ x ∧ ℓ x ≤ b; have hxp : ℓ x = ℓ p := hx.2; rw [hxp]; exact
        hpheight⟩
  have hZ : IsPLBall 3 Z := by
    have h := hZpoly.isPLBall (interior_convexHull_inter_slab_nonempty T (A.indep hT)
      (by simpa using hTcard) ℓ.toLinearMap.toAffineMap hab
      havoidT hZne)
    simpa using h
  have hpatch := isPLBall_frontier_slab_inter_cell_of_isFreeDiskCell K A hAK (by simp) hT ℓ hℓ hinj
      hab
    hpheight hvertices hdec hPspace (hCeq ▸ hC) (hCeq ▸ hfree)
  have hslabpoly : IsPolyhedron (A.space ∩ ℓ ⁻¹' Icc a b) :=
    (isPolyhedron_space A).inter_preimage isHPolytope_Icc.isPolyhedron ℓ.toLinearMap.toAffineMap
  have hD : IsPLBall 2 (A.space ∩ {x | ℓ.toLinearMap x = ℓ.toLinearMap p}) := hPspace ▸
      hdec.isPLBall
  have hslabreg := closure_interior_space_inter_slab_of_isPLBall_fiber A hreg ℓ.toLinearMap
    (hinj.mono (fun _ hv => hAK hv)) hab hpheight (fun v hv => hgap v (hAK hv)) hD
  obtain ⟨H, hH, hfix, -, himage⟩ := exists_isPLHomeomorphOn_frontier_closure_sdiff_of_convex I
    hslabpoly hslabreg hS hZ hZpoly.convex (inter_subset_inter_left _ (A.convexHull_subset_space
        hT))
    hpatch hW hWconv hSW
  have hBD : IsPLBall 2 (B.space ∩ {x | ℓ.toLinearMap x = ℓ.toLinearMap p}) := hfiber ▸
      hQdec.isPLBall
  have hBslabreg := closure_interior_space_inter_slab_of_isPLBall_fiber B hBreg ℓ.toLinearMap
    (hinj.mono (fun _ hv => hAK (hBA hv))) hab hpheight
    (fun v hv => hgap v (hAK (hBA hv))) hBD
  have hTball : IsPLBall 3 (convexHull ℝ (T : Set (EuclideanSpace ℝ (Fin 3)))) :=
    isPLBall_convexHull_of_affineIndependent T (A.indep hT) hTcard
  have hslabeq : closure ((A.space ∩ ℓ ⁻¹' Icc a b) \ Z) = B.space ∩ ℓ ⁻¹' Icc a b := by
    rw [hBspace] at hBslabreg ⊢
    exact Topology.closure_inter_sdiff_eq_inter_closure_sdiff (isPolyhedron_space A).isClosed
      (isClosed_Icc.preimage ℓ.continuous) hTball.closure_interior hBslabreg
  rw [hslabeq] at himage
  exact ⟨B, hBfin, hBA, hBreg, hkeep, hfiber, hQdec, hQheight, H, hH, hfix, himage⟩

end DifferentialGeometry.Topology.PiecewiseLinear
