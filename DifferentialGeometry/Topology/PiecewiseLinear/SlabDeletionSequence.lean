import DifferentialGeometry.Topology.PiecewiseLinear.SlabCellDeletion
import DifferentialGeometry.Topology.PiecewiseLinear.ClosedStarSlab
import DifferentialGeometry.Topology.PiecewiseLinear.HeightStarDeletion
import DifferentialGeometry.Topology.PiecewiseLinear.HeightSlabSurgery

open Set

namespace DifferentialGeometry.Topology.PiecewiseLinear

open Classical in
theorem exists_isPLHomeomorphOn_slab_of_free_disk_cell_deletion_sequence (I : SchoenfliesInput)
    (K A : Geometry.SimplicialComplex ℝ (EuclideanSpace ℝ (Fin 3))) [Finite K.faces] [Finite A.faces]
    (hAK : A.faces ⊆ K.faces) (hreg : closure (interior A.space) = A.space)
    (ℓ : EuclideanSpace ℝ (Fin 3) →L[ℝ] ℝ) (hℓ : ℓ ≠ 0) (hinj : InjOn ℓ K.vertices)
    {p : EuclideanSpace ℝ (Fin 3)} {a b : ℝ} (hab : a < b) (hpheight : ℓ p ∈ Icc a b)
    (hgap : ∀ v ∈ K.vertices, v ≠ p → ℓ v < a ∨ b < ℓ v)
    {P Q : Geometry.SimplicialComplex ℝ (EuclideanSpace ℝ (Fin 3)) × Finset (Set (EuclideanSpace ℝ (Fin 3)))}
    (hsequence : Relation.ReflTransGen (IsFreeDiskCellDeletion (closedStar K p ∩ {x | ℓ x = ℓ p})) P Q)
    (hdec : IsPLDiskDecomposition P.1 P.2) (hPspace : P.1.space = A.space ∩ {x | ℓ x = ℓ p})
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
  induction hsequence using Relation.ReflTransGen.head_induction_on generalizing A with
  | refl =>
      refine ⟨A, Set.toFinite A.faces, Subset.rfl, hreg, fun _ hs _ => hs, hPspace, hdec, hcells,
        Homeomorph.refl _, ?_, fun _ _ => rfl, ?_⟩
      · exact ⟨bijOn_id univ, isPiecewiseAffineOn_id isOpen_univ,
          (isPiecewiseAffineOn_id isOpen_univ).congr fun _ hx => (bijOn_id univ).invOn_invFunOn.1 hx⟩
      · exact image_id _
  | @head P R hstep hseq ih =>
      obtain ⟨B, hBfin, hBA, hBreg, hkeep, hRspace, hRdec, hRcells, H, hH, hHfix, hHimage⟩ :=
        exists_isPLHomeomorphOn_slab_of_free_disk_cell_deletion I K A hAK hreg ℓ hℓ hinj
          hab hpheight hgap hstep hPspace hcells hS hW hWconv hSW
      let _ : Finite B.faces := hBfin.to_subtype
      have hBpoly : IsPLSphere 2 (frontier (B.space ∩ ℓ ⁻¹' Icc a b)) := by
        rw [← hHimage]
        exact hS.of_isPLHomeomorphOn (hH.restrict hS.isPolyhedron (subset_univ _))
      have hBW : frontier (B.space ∩ ℓ ⁻¹' Icc a b) ⊆ W := by
        rw [← hHimage]
        rintro _ ⟨x, hx, rfl⟩
        by_contra hnot
        have heq : H x = x := H.injective (hHfix hnot)
        exact hnot (heq.symm ▸ hSW hx)
      obtain ⟨C, hCfin, hCB, hCreg, hkeepC, hQspace, hQdec, hQcells, G, hG, hGfix, hGimage⟩ :=
        ih B (hBA.trans hAK) hBreg hRdec hRspace hRcells hBpoly hBW
      refine ⟨C, hCfin, hCB.trans hBA, hCreg, fun s hs hp => hkeepC s (hkeep s hs hp) hp,
        hQspace, hQdec, hQcells, H.trans G, hH.trans hG, ?_, ?_⟩
      · intro x hx
        change G (H x) = x
        rw [hHfix hx]
        exact hGfix hx
      · change (G ∘ H) '' _ = _
        rw [image_comp, hHimage, hGimage]

theorem exists_isPLHomeomorphOn_frontier_slab_closedStar (I : SchoenfliesInput)
    (K : Geometry.SimplicialComplex ℝ (EuclideanSpace ℝ (Fin 3))) [Finite K.faces]
    (hK : IsCombinatorialManifoldWithBoundary 3 K) (hS : IsPLSphere 2 (frontier K.space))
    (hreg : closure (interior K.space) = K.space) (hconn : IsPreconnected (interior K.space))
    (ℓ : EuclideanSpace ℝ (Fin 3) →L[ℝ] ℝ) (hℓ : ℓ ≠ 0) (hinj : InjOn ℓ K.vertices)
    (hzero : heightIndex (frontier K.space) ℓ = 0)
    {p : EuclideanSpace ℝ (Fin 3)} (hp : {p} ∈ K.faces) {a b : ℝ} (hab : a < b) (hpheight : ℓ p ∈ Icc a b)
    (hgap : ∀ v ∈ K.vertices, v ≠ p → ℓ v < a ∨ b < ℓ v)
    (hbelow : ∃ x ∈ frontier K.space, ℓ x < a) (habove : ∃ y ∈ frontier K.space, b < ℓ y)
    {W : Set (EuclideanSpace ℝ (Fin 3))} (hW : IsOpen W) (hWconv : Convex ℝ W)
    (hSW : frontier (K.space ∩ ℓ ⁻¹' Icc a b) ⊆ W) :
    ∃ H : EuclideanSpace ℝ (Fin 3) ≃ₜ EuclideanSpace ℝ (Fin 3),
      IsPLHomeomorphOn H univ univ ∧ EqOn H id Wᶜ ∧
      H '' frontier (K.space ∩ ℓ ⁻¹' Icc a b) = frontier (closedStar K p ∩ ℓ ⁻¹' Icc a b) := by
  classical
  obtain ⟨_, _, _, _, g, hg, -⟩ := exists_isPLDiskDecomposition_fiber_of_heightIndex_eq_zero K hK hS
    (by simp) hreg hconn ℓ hℓ hinj hzero (ℓ p)
    (hbelow.imp fun _ hx => ⟨hx.1, hx.2.trans_le hpheight.1⟩)
    (habove.imp fun _ hx => ⟨hx.1, hpheight.2.trans_lt hx.2⟩)
  obtain ⟨L, R, hL, hLspace, -, hRspace, hsequence⟩ :=
    exists_free_disk_cell_deletion_sequence_to_closedStar K (by simp) hreg ℓ.toLinearMap hinj hp ⟨g, hg⟩
  have hslab := isPLSphere_frontier_slab_of_heightIndex_eq_zero K hK hS (by simp) hreg hconn
    ℓ hℓ hinj hzero hab hbelow habove
  obtain ⟨B, hBfin, hBK, -, hkeep, hfiber, -, -, H, hH, hfix, himage⟩ :=
    exists_isPLHomeomorphOn_slab_of_free_disk_cell_deletion_sequence I K K Subset.rfl hreg ℓ hℓ hinj
      hab hpheight hgap hsequence hL hLspace Subset.rfl hslab hW hWconv hSW
  have hstar : closedStar K p ⊆ B.space := by
    intro x hx
    obtain ⟨T, ⟨hT, hpT⟩, hxT⟩ := mem_iUnion₂.mp hx
    exact B.convexHull_subset_space (hkeep T hT (mem_of_mem_convexHull_of_singleton_mem K hp hT hpT)) hxT
  have hfiber' : B.space ∩ {x | ℓ.toLinearMap x = ℓ.toLinearMap p} ⊆ closedStar K p := by
    intro x hx
    exact (hRspace.subset (hfiber.symm.subset hx)).1
  have heq := inter_slab_eq_closedStar_inter_of_fiber_subset K B hBK hp hstar ℓ.toLinearMap
    hpheight hgap hfiber'
  change B.space ∩ ℓ ⁻¹' Icc a b = closedStar K p ∩ ℓ ⁻¹' Icc a b at heq
  rw [heq] at himage
  exact ⟨H, hH, hfix, himage⟩
end DifferentialGeometry.Topology.PiecewiseLinear
