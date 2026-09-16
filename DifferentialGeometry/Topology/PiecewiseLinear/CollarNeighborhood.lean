import DifferentialGeometry.Topology.PiecewiseLinear.SurfaceCollar
import DifferentialGeometry.Topology.PiecewiseLinear.ClosedStarNeighborhood

open Set Topology

namespace DifferentialGeometry.Topology.PiecewiseLinear

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

open Classical in
theorem IsPLHomeomorphOn.mem_nhdsSetWithin_boundaryComplex
    (K : Geometry.SimplicialComplex ℝ E) [Finite K.faces]
    (hK : IsCombinatorialManifoldWithBoundary 3 K) {a b : ℝ} (hab : a < b)
    {ρ : E × ℝ → E} {W : Set E}
    (hρ : IsPLHomeomorphOn ρ ((boundaryComplex 3 K).space ×ˢ Icc a b) W)
    (hWK : W ⊆ K.space) (hbottom : ∀ x ∈ (boundaryComplex 3 K).space, ρ (x, a) = x) :
    W ∈ 𝓝ˢ[K.space] (boundaryComplex 3 K).space := by
  let B := boundaryComplex 3 K
  let _ : Finite B.faces := (boundaryComplex_faces_finite 3 K).to_subtype
  have hB : IsCombinatorialManifold 2 B := isCombinatorialManifold_boundaryComplex K hK
  have hnot : ∀ x ∈ B.space, x ∉ closure (K.space \ W) := by
    intro x hxB
    obtain ⟨D, hD, hDB', hDnhds⟩ :=
      hB.exists_isPLBall_subset_of_mem_nhds hxB (U := univ) Filter.univ_mem
    have hDB : D ⊆ B.space := hDB'.trans inter_subset_left
    have hxcl : x ∉ closure (B.space \ D) := by
      intro hxcl
      obtain ⟨y, hy, hyD⟩ := ((mem_closure_iff_frequently.mp hxcl).and_eventually
        (mem_nhdsWithin_iff_eventually.mp hDnhds)).exists
      exact hy.2 (hyD hy.1)
    obtain ⟨J, hJfin, hJspace⟩ := hD.isPolyhedron.exists_simplicialComplex
    let _ : Finite J.faces := hJfin.to_subtype
    let _ : Finite (boundaryComplex 2 J).faces := (boundaryComplex_faces_finite 2 J).to_subtype
    have hJ : IsPLBall 2 J.space := hJspace.symm ▸ hD
    have hboundaryJ : (boundaryComplex 2 J).space = D ∩ closure (B.space \ D) := by
      obtain ⟨r, hr⟩ := hD
      rw [boundaryComplex_space_of_isPLHomeomorphOn_stdSimplex J (hJspace.symm ▸ hr),
        simplexBoundary_stdVertices_space, ← hB.inter_closure_sdiff_eq_image_stdSimplexBoundary B hr hDB]
    have hxnotJ : x ∉ (boundaryComplex 2 J).space := fun hx =>
      hxcl ((hboundaryJ.subset hx).2)
    have hprod : IsPLBall 3 (D ×ˢ Icc a b) := isPLBall_three_prod hD (isPLBall_Icc hab)
    have hρD := hρ.restrict hprod.isPolyhedron (prod_mono hDB Subset.rfl)
    let C := ρ '' (D ×ˢ Icc a b)
    have hC : IsPLBall 3 C := hprod.of_isPLHomeomorphOn hρD
    have hCW : C ⊆ W := (image_mono (prod_mono hDB Subset.rfl)).trans hρ.image_eq.subset
    have hCK : C ⊆ K.space := hCW.trans hWK
    have hCB : C ∩ B.space = D := by
      apply Subset.antisymm
      · rintro y ⟨⟨z, hz, rfl⟩, hzB⟩
        have heq : z = (ρ z, a) := hρ.bijOn.injOn ⟨hDB hz.1, hz.2⟩
          ⟨hzB, le_rfl, hab.le⟩ (hbottom (ρ z) hzB).symm
        exact (congrArg (fun y => y ∈ D) (show z.1 = ρ z from congrArg Prod.fst heq)).mp hz.1
      · intro y hy
        exact ⟨⟨(y, a), ⟨hy, le_rfl, hab.le⟩, hbottom y (hDB hy)⟩, hDB hy⟩
    obtain ⟨L, hLfin, hLspace⟩ := hC.isPolyhedron.exists_simplicialComplex
    let _ : Finite L.faces := hLfin.to_subtype
    have hL : IsPLBall 3 L.space := hLspace.symm ▸ hC
    obtain ⟨T, hTfin, hTspace⟩ := (isPLBall_three_prod hJ (isPLBall_Icc hab)).isPolyhedron.exists_simplicialComplex
    let _ : Finite T.faces := hTfin.to_subtype
    let _ : DecidableEq (E × ℝ) := Classical.decEq _
    have hT : IsPLBall 3 T.space := hTspace.symm ▸ isPLBall_three_prod hJ (isPLBall_Icc hab)
    have hmap : IsPLHomeomorphOn ρ T.space L.space := by
      rw [hTspace, hJspace, hLspace]
      exact hρD
    have hboundaryL : (boundaryComplex 3 L).space =
        ρ '' (D ×ˢ {a, b} ∪ (boundaryComplex 2 J).space ×ˢ Icc a b) := by
      rw [boundaryComplex_space_of_isPLHomeomorphOn T L hT.isCombinatorialManifoldWithBoundary hmap,
        boundaryComplex_space_prism J hJ hab T hTspace, hJspace]
    let F := ρ '' (D ×ˢ {b} ∪ (boundaryComplex 2 J).space ×ˢ Icc a b)
    have hFdom : D ×ˢ {b} ∪ (boundaryComplex 2 J).space ×ˢ Icc a b ⊆ B.space ×ˢ Icc a b := by
      rintro z (hz | hz)
      · exact ⟨hDB hz.1, by rw [show z.2 = b from hz.2]; exact ⟨hab.le, le_rfl⟩⟩
      · exact ⟨hDB (hJspace.subset (boundaryComplex_space_subset 2 J hz.1)), hz.2⟩
    have hFclosed : IsClosed F :=
      (((hD.isPolyhedron.isCompact.prod isCompact_singleton).union
        ((isPolyhedron_space (boundaryComplex 2 J)).isCompact.prod isCompact_Icc)).image_of_continuousOn
        (hρ.isPiecewiseAffineOn.continuousOn.mono hFdom)).isClosed
    have hxF : x ∉ F := by
      rintro ⟨z, hz, hzx⟩
      have heq : z = (x, a) := hρ.bijOn.injOn (hFdom hz)
        ⟨hxB, le_rfl, hab.le⟩ (hzx.trans (hbottom x hxB).symm)
      rw [heq] at hz
      rcases hz with hz | hz
      · exact hab.ne hz.2
      · exact hxnotJ hz.1
    have hdiffF : (boundaryComplex 3 L).space \ B.space ⊆ F := by
      rintro y ⟨hyL, hyB⟩
      obtain ⟨z, hz, rfl⟩ := hboundaryL.subset hyL
      rcases hz with hz | hz
      · rcases hz.2 with hza | hzb
        · have heq : z = (z.1, a) := Prod.ext rfl hza
          exact (hyB (by rw [heq, hbottom z.1 (hDB hz.1)]; exact hDB hz.1)).elim
        · exact ⟨z, Or.inl ⟨hz.1, hzb⟩, rfl⟩
      · exact ⟨z, Or.inr hz, rfl⟩
    have hCdisk : IsPLBall 2 (C ∩ (boundaryComplex 3 K).space) := hCB.symm ▸ hD
    obtain ⟨Q, hQfin, hQ, hQspace⟩ :=
      hK.exists_isCombinatorialManifoldWithBoundary_closure_sdiff hC hCK hCdisk
    let _ : Finite Q.faces := hQfin.to_subtype
    have hQK : Q.space ⊆ K.space := by
      rw [hQspace]
      exact closure_minimal sdiff_subset (isPolyhedron_space K).isClosed
    have hxnotC : x ∉ closure (K.space \ C) := by
      rw [← hQspace]
      intro hxQ
      have hxQb := inter_boundaryComplex_space_subset_of_subset K Q hK hQ hQK ⟨hxQ, hxB⟩
      rw [boundaryComplex_space_of_closure_sdiff K L Q hK hL.isCombinatorialManifoldWithBoundary
        (hLspace.symm ▸ hCK) hQ (hLspace.symm ▸ hQspace)] at hxQb
      rcases hxQb with hxold | hxnew
      · apply hxcl
        apply closure_mono (t := B.space \ D) _ hxold
        rw [hLspace]
        rintro y ⟨hyB, hyC⟩
        exact ⟨hyB, fun hyD => hyC (hCB.symm.subset hyD).1⟩
      · exact hxF (closure_minimal hdiffF hFclosed hxnew)
    exact fun hx => hxnotC (closure_mono (sdiff_subset_sdiff_right hCW) hx)
  refine mem_nhdsSetWithin.mpr ⟨(closure (K.space \ W))ᶜ, isClosed_closure.isOpen_compl, hnot, ?_⟩
  rintro x ⟨hx, hxK⟩
  by_contra hxW
  exact hx (subset_closure ⟨hxK, hxW⟩)

open Classical in
theorem IsCombinatorialManifoldWithBoundary.exists_collar
    (K : Geometry.SimplicialComplex ℝ E) [Finite K.faces]
    (hK : IsCombinatorialManifoldWithBoundary 3 K) :
    ∃ (W : Set E) (ρ : E × ℝ → E), IsPolyhedron W ∧ W ⊆ K.space ∧
      W ∈ 𝓝ˢ[K.space] (boundaryComplex 3 K).space ∧
      IsPLHomeomorphOn ρ ((boundaryComplex 3 K).space ×ˢ Icc (0 : ℝ) 1) W ∧
      (∀ x ∈ (boundaryComplex 3 K).space, ρ (x, 0) = x) ∧
      W ∩ (boundaryComplex 3 K).space = (boundaryComplex 3 K).space ∧
      MapsTo ρ ((boundaryComplex 3 K).space ×ˢ Ioc (0 : ℝ) 1)
        (K.space \ (boundaryComplex 3 K).space) := by
  let B := boundaryComplex 3 K
  let _ : Finite B.faces := (boundaryComplex_faces_finite 3 K).to_subtype
  have hB : IsCombinatorialManifoldWithBoundary 2 B :=
    (isCombinatorialManifold_boundaryComplex K hK).isCombinatorialManifoldWithBoundary
  obtain ⟨W, ρ, -, hW, hWK, hρ, hbottom, hWB, hpositive, -⟩ :=
    hK.exists_isPLHomeomorphOn_surface_prod_Icc K B hB Subset.rfl (a := 0) (b := 1) (by norm_num)
  exact ⟨W, ρ, hW, hWK, hρ.mem_nhdsSetWithin_boundaryComplex K hK (by norm_num) hWK hbottom,
    hρ, hbottom, hWB, hpositive⟩

end DifferentialGeometry.Topology.PiecewiseLinear
