import DifferentialGeometry.Topology.PiecewiseLinear.FreeCellSlab
import DifferentialGeometry.Topology.PiecewiseLinear.HeightStarDecomposition
import DifferentialGeometry.Topology.PiecewiseLinear.PolytopeSection
import DifferentialGeometry.Topology.SlabBoundary

open Set

namespace DifferentialGeometry.Topology.PiecewiseLinear

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

theorem exists_convex_slab_cell_of_ne_closedStar
    (K : Geometry.SimplicialComplex ℝ E) [Finite K.faces]
    (hK : IsCombinatorialManifoldWithBoundary 3 K) (hdim : Module.finrank ℝ E = 3)
    (hreg : closure (interior K.space) = K.space)
    (ℓ : E →L[ℝ] ℝ) (hℓ : ℓ ≠ 0) (hinj : InjOn ℓ K.vertices)
    {p : E} (hp : {p} ∈ K.faces) {a b : ℝ} (hab : a < b) (hpheight : ℓ p ∈ Icc a b)
    (hgap : ∀ v ∈ K.vertices, v ≠ p → ℓ v < a ∨ b < ℓ v)
    {g : (Fin 3 → ℝ) → E}
    (hg : IsPLHomeomorphOn g (stdSimplex ℝ (Fin 3)) (K.space ∩ {x | ℓ x = ℓ p}))
    (hgBd : g '' stdSimplexBoundary 2 = frontier K.space ∩ {x | ℓ x = ℓ p})
    (hne : closedStar K p ∩ {x | ℓ x = ℓ p} ≠ K.space ∩ {x | ℓ x = ℓ p}) :
    ∃ T ∈ K.faces, T.card = 4 ∧ p ∉ T ∧
      let C := convexHull ℝ (T : Set E) ∩ ℓ ⁻¹' Icc a b
      Convex ℝ C ∧ IsPLBall 3 C ∧
        IsPLBall 2 (frontier (K.space ∩ ℓ ⁻¹' Icc a b) ∩ C) ∧
        frontier (K.space ∩ ℓ ⁻¹' Icc a b) ∩ C ⊆ frontier C := by
  classical
  obtain ⟨L, D, hLfin, hLspace, hdec, hD, hnot, hfree⟩ :=
    exists_free_heightSectionCell_outside_closedStar K hdim hreg ℓ.toLinearMap hinj hp ⟨g, hg⟩ hne
  let _ : Finite L.faces := hLfin.to_subtype
  obtain ⟨T, hT, hcard, hbelow, habove, hD_eq⟩ := mem_heightSectionCells_iff.mp hD
  have hpnot : p ∉ T := by
    intro hpT
    apply hnot
    rw [hD_eq]
    intro x hx
    exact mem_iUnion₂.mpr ⟨T, ⟨hT, subset_convexHull ℝ _ hpT⟩, hx.1⟩
  have hvertices : ∀ v ∈ T, ℓ v < a ∨ b < ℓ v := by
    intro v hv
    exact hgap v (K.down_closed hT (Finset.singleton_subset_iff.mpr hv) (Finset.singleton_nonempty v))
      (fun hvp => hpnot (hvp ▸ hv))
  have hlow : ∃ v ∈ T, ℓ v ≤ a := by
    obtain ⟨v, hv, hvp⟩ := hbelow
    rcases hvertices v hv with hva | hbv
    · exact ⟨v, hv, hva.le⟩
    · exact (hbv.not_ge (hvp.le.trans hpheight.2)).elim
  have hhigh : ∃ v ∈ T, b ≤ ℓ v := by
    obtain ⟨v, hv, hpv⟩ := habove
    rcases hvertices v hv with hva | hbv
    · exact (hva.not_ge (hpheight.1.trans hpv.le)).elim
    · exact ⟨v, hv, hbv.le⟩
  let C := convexHull ℝ (T : Set E) ∩ ℓ ⁻¹' Icc a b
  have hCpoly : IsHPolytope C :=
    (isHPolytope_convexHull_of_affineIndependent T (K.indep hT)).inter_preimage
      isHPolytope_Icc ℓ.toLinearMap.toAffineMap
  have hC : IsPLBall 3 C := by
    have h := isPLBall_convexHull_inter_slab T (K.indep hT) (by simpa [hdim, C] using hcard)
      ℓ.toLinearMap.toAffineMap hab hlow hhigh
    convert h using 1
    · exact hdim.symm
    · ext x
      rfl
  have hKfront : frontier K.space = (boundaryComplex 3 K).space :=
    frontier_space_eq_boundaryComplex_space_of_finrank hdim K hK
  have hgL : IsPLHomeomorphOn g (stdSimplex ℝ (Fin 3)) L.space := hLspace.symm ▸ hg
  have hLboundary : (boundaryComplex 2 L).space =
      (boundaryComplex 3 K).space ∩ {x | ℓ x = ℓ p} := by
    rw [boundaryComplex_space_of_isPLHomeomorphOn_stdSimplex L hgL,
      simplexBoundary_stdVertices_space, hgBd, hKfront]
  have hpatch := isPLBall_slab_patch_of_isFreeDiskCell K (boundaryComplex 3 K)
    (boundaryComplex_faces_subset 3 K) hT ℓ.toLinearMap hab hpheight hvertices hdec hLboundary
    (hD_eq ▸ hD) (hD_eq ▸ hfree)
  have hslabBoundary := Topology.frontier_inter_preimage_Icc_of_ne_zero
    (isPolyhedron_space K).isClosed ℓ hℓ hab.le
  have hpatch' : IsPLBall 2 (frontier (K.space ∩ ℓ ⁻¹' Icc a b) ∩ C) := by
    rw [hslabBoundary, hKfront, inter_comm]
    exact hpatch
  refine ⟨T, hT, hcard, hpnot, hCpoly.convex, hC, hpatch', ?_⟩
  rintro x ⟨hx, hxC⟩
  refine ⟨subset_closure hxC, ?_⟩
  intro hint
  exact hx.2 (interior_mono (inter_subset_inter_left _ (K.convexHull_subset_space hT)) hint)

end DifferentialGeometry.Topology.PiecewiseLinear
