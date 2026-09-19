/-
Copyright (c) 2026 Yuan Liao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuan Liao
-/
import DifferentialGeometry.Topology.PiecewiseLinear.SurfaceSplitCapping

/-! Finite realizations of surface splitting along annular collars. -/

open Set

namespace DifferentialGeometry.Topology.PiecewiseLinear

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

private theorem exists_simplicialComplex_space_union_five
    (K L M N P : Geometry.SimplicialComplex ℝ E)
    [Finite K.faces] [Finite L.faces] [Finite M.faces] [Finite N.faces] [Finite P.faces] :
    ∃ R : Geometry.SimplicialComplex ℝ E, R.faces.Finite ∧
      R.space = K.space ∪ L.space ∪ M.space ∪ N.space ∪ P.space ∧
      IsSubdivision (restrict R K.space) K ∧
      IsSubdivision (restrict R L.space) L ∧
      IsSubdivision (restrict R M.space) M ∧
      IsSubdivision (restrict R N.space) N ∧
      IsSubdivision (restrict R P.space) P := by
  let C : Fin 5 → Geometry.SimplicialComplex ℝ E := ![K, L, M, N, P]
  let _ : ∀ i, Finite (C i).faces := by
    intro i
    fin_cases i <;> dsimp [C] <;> infer_instance
  obtain ⟨R, hfin, hspace, hsub⟩ := exists_simplicialComplex_space_iUnion C
  refine ⟨R, hfin, ?_, hsub 0, hsub 1, hsub 2, hsub 3, hsub 4⟩
  rw [hspace]
  ext x
  constructor
  · intro hx
    obtain ⟨i, hxi⟩ := mem_iUnion.mp hx
    fin_cases i
    · exact Or.inl (Or.inl (Or.inl (Or.inl hxi)))
    · exact Or.inl (Or.inl (Or.inl (Or.inr hxi)))
    · exact Or.inl (Or.inl (Or.inr hxi))
    · exact Or.inl (Or.inr hxi)
    · exact Or.inr hxi
  · rintro ((((hx | hx) | hx) | hx) | hx)
    · exact mem_iUnion.mpr ⟨0, hx⟩
    · exact mem_iUnion.mpr ⟨1, hx⟩
    · exact mem_iUnion.mpr ⟨2, hx⟩
    · exact mem_iUnion.mpr ⟨3, hx⟩
    · exact mem_iUnion.mpr ⟨4, hx⟩

open Classical in
theorem exists_surface_split_along_polygon_of_annulus_complement
    (K R : Geometry.SimplicialComplex ℝ E) [Finite K.faces] [Finite R.faces]
    (hR : IsCombinatorialManifoldWithBoundary 2 R)
    {J W : Set E} (hJ : IsPLSphere 1 J) {ρ : E × ℝ → E}
    (hρ : IsPLHomeomorphOn ρ (J ×ˢ Icc (-1 : ℝ) 1) W)
    (hcover : W ∪ R.space = K.space)
    (htrace : W ∩ R.space = ρ '' (J ×ˢ {(-1 : ℝ), 1})) :
    ∃ source split : Geometry.SimplicialComplex ℝ E,
      source.faces.Finite ∧ split.faces.Finite ∧ IsSubdivision source K ∧
      IsSubdivision split R ∧ IsCombinatorialManifoldWithBoundary 2 split ∧
      Nonempty (SurfaceSplitAlongPolygon source split) := by
  let C₀ := ρ '' (J ×ˢ {(-1 : ℝ)})
  let C₁ := ρ '' (J ×ˢ {(1 : ℝ)})
  have hminus : J ×ˢ {(-1 : ℝ)} ⊆ J ×ˢ Icc (-1 : ℝ) 1 := by
    rintro ⟨x, t⟩ ⟨hx, ht⟩
    have ht : t = -1 := by simpa only [mem_singleton_iff] using ht
    subst t
    exact ⟨hx, by norm_num⟩
  have hplus : J ×ˢ {(1 : ℝ)} ⊆ J ×ˢ Icc (-1 : ℝ) 1 := by
    rintro ⟨x, t⟩ ⟨hx, ht⟩
    have ht : t = 1 := by simpa only [mem_singleton_iff] using ht
    subst t
    exact ⟨hx, by norm_num⟩
  let e₀ : E → E := ρ ∘ fun x => (x, (-1 : ℝ))
  let e₁ : E → E := ρ ∘ fun x => (x, (1 : ℝ))
  have he₀ : IsPLHomeomorphOn e₀ J C₀ :=
    hJ.isPolyhedron.isPLHomeomorphOn_prod_const (-1) |>.trans
      (hρ.restrict (hJ.isPolyhedron.prod
        (isHPolytope_singleton (-1 : ℝ)).isPolyhedron) hminus)
  have he₁ : IsPLHomeomorphOn e₁ J C₁ :=
    hJ.isPolyhedron.isPLHomeomorphOn_prod_const 1 |>.trans
      (hρ.restrict (hJ.isPolyhedron.prod
        (isHPolytope_singleton (1 : ℝ)).isPolyhedron) hplus)
  have hC₀ : IsPLSphere 1 C₀ := hJ.of_isPLHomeomorphOn he₀
  have hC₁ : IsPLSphere 1 C₁ := hJ.of_isPLHomeomorphOn he₁
  let q : ℝ := (1 - (-1)) / (1 - 0)
  let τ : ℝ →ᵃ[ℝ] ℝ := AffineMap.const ℝ ℝ (-1) +
    q • (AffineMap.id ℝ ℝ - AffineMap.const ℝ ℝ 0)
  have hq : q = 2 := by norm_num [q]
  have hτapply (t : ℝ) : τ t = -1 + q * (t - 0) := rfl
  have hτ : IsPLHomeomorphOn τ (Icc (0 : ℝ) 1) (Icc (-1 : ℝ) 1) := by
    apply isPLHomeomorphOn_of_isPiecewiseAffineOn_of_bijOn isHPolytope_Icc.isPolyhedron
      (isPiecewiseAffineOn_of_affine_of_isHPolytope τ isHPolytope_Icc)
    refine ⟨?_, ?_, ?_⟩
    · intro t ht
      rw [hτapply, hq]
      constructor <;> linarith [ht.1, ht.2]
    · intro s hs t ht hst
      rw [hτapply, hτapply, hq] at hst
      linarith
    · intro t ht
      refine ⟨(t + 1) / 2, ?_, ?_⟩
      · constructor <;> linarith [ht.1, ht.2]
      · rw [hτapply, hq]
        ring
  have hcollarMap : IsPLHomeomorphOn
      (ρ ∘ Prod.map (Function.invFunOn e₀ J) τ)
      (C₀ ×ˢ Icc (0 : ℝ) 1) W := (he₀.symm.prodMap hτ).trans hρ
  have htrace' : W ∩ R.space = C₀ ∪ C₁ := by
    change W ∩ R.space =
      ρ '' (J ×ˢ {(-1 : ℝ)}) ∪ ρ '' (J ×ˢ {(1 : ℝ)})
    rw [htrace, ← image_union, ← prod_union, singleton_union]
  have hCdis : Disjoint C₀ C₁ := by
    apply disjoint_left.mpr
    rintro y ⟨z, hz, rfl⟩ ⟨w, hw, hwy⟩
    have hzw := hρ.bijOn.injOn (hminus hz) (hplus hw) hwy.symm
    have ht := hz.2.symm.trans ((congrArg Prod.snd hzw).trans hw.2)
    norm_num at ht
  have hC₀WR : C₀ ⊆ W ∩ R.space := fun _ hx => htrace'.symm.subset (Or.inl hx)
  have hC₁WR : C₁ ⊆ W ∩ R.space := fun _ hx => htrace'.symm.subset (Or.inr hx)
  have hWK : W ⊆ K.space := subset_union_left.trans hcover.subset
  have hRK : R.space ⊆ K.space := subset_union_right.trans hcover.subset
  have hW : IsPolyhedron W := hρ.image_eq ▸
    (hJ.isPolyhedron.prod isHPolytope_Icc.isPolyhedron).image_of_isPiecewiseAffineOn
      hρ.isPiecewiseAffineOn hρ.bijOn.injOn
  obtain ⟨A, hAfin, hAspace⟩ := hW.exists_simplicialComplex
  obtain ⟨L₀, hL₀fin, hL₀space⟩ := hC₀.isPolyhedron.exists_simplicialComplex
  obtain ⟨L₁, hL₁fin, hL₁space⟩ := hC₁.isPolyhedron.exists_simplicialComplex
  let _ : Finite A.faces := hAfin.to_subtype
  let _ : Finite L₀.faces := hL₀fin.to_subtype
  let _ : Finite L₁.faces := hL₁fin.to_subtype
  obtain ⟨T, hTfin, hTspace, hTK, hTR, hTA, hTL₀, hTL₁⟩ :=
    exists_simplicialComplex_space_union_five K R A L₀ L₁
  let _ : Finite T.faces := hTfin.to_subtype
  let source := restrict T K.space
  let core := restrict T R.space
  let collar := restrict T W
  let boundary₀ := restrict T C₀
  let boundary₁ := restrict T C₁
  let split := core
  have hsourcefin : source.faces.Finite := restrict_faces_finite T K.space
  have hcorefin : core.faces.Finite := restrict_faces_finite T R.space
  have hcollarfin : collar.faces.Finite := restrict_faces_finite T W
  have hboundary₀fin : boundary₀.faces.Finite := restrict_faces_finite T C₀
  have hboundary₁fin : boundary₁.faces.Finite := restrict_faces_finite T C₁
  let _ : Finite source.faces := hsourcefin.to_subtype
  let _ : Finite core.faces := hcorefin.to_subtype
  let _ : Finite collar.faces := hcollarfin.to_subtype
  let _ : Finite boundary₀.faces := hboundary₀fin.to_subtype
  let _ : Finite boundary₁.faces := hboundary₁fin.to_subtype
  let _ : Finite split.faces := hcorefin.to_subtype
  have hTA' : IsSubdivision collar A := by
    simpa only [collar, hAspace] using hTA
  have hTL₀' : IsSubdivision boundary₀ L₀ := by
    simpa only [boundary₀, hL₀space] using hTL₀
  have hTL₁' : IsSubdivision boundary₁ L₁ := by
    simpa only [boundary₁, hL₁space] using hTL₁
  have hcorespace : core.space = R.space := hTR.space_eq
  have hcollarspace : collar.space = W := hTA'.space_eq.trans hAspace
  have hboundary₀space : boundary₀.space = C₀ := hTL₀'.space_eq.trans hL₀space
  have hboundary₁space : boundary₁.space = C₁ := hTL₁'.space_eq.trans hL₁space
  have hC₀W : C₀ ⊆ W := fun _ hx => (hC₀WR hx).1
  have hC₀R : C₀ ⊆ R.space := fun _ hx => (hC₀WR hx).2
  have hC₁W : C₁ ⊆ W := fun _ hx => (hC₁WR hx).1
  have hC₁R : C₁ ⊆ R.space := fun _ hx => (hC₁WR hx).2
  have hsourceFaces : source.faces = core.faces ∪ collar.faces := by
    ext s
    constructor
    · intro hs
      have hxs := centroid_mem_openSimplex_of_mem_faces T s hs.1
      have hxK : s.centroid ℝ id ∈ K.space :=
        hs.2 (openSimplex_subset_convexHull s hxs)
      rcases hcover.symm.subset hxK with hxW | hxR
      · exact Or.inr (mem_faces_of_mem_openSimplex_of_mem_space
          (restrict_faces_subset T W) hs.1 hxs (hcollarspace.symm.subset hxW))
      · exact Or.inl (mem_faces_of_mem_openSimplex_of_mem_space
          (restrict_faces_subset T R.space) hs.1 hxs (hcorespace.symm.subset hxR))
    · rintro (hs | hs)
      · exact ⟨hs.1, hs.2.trans hRK⟩
      · exact ⟨hs.1, hs.2.trans hWK⟩
  have hinterFaces : (intersectionComplex core collar).faces =
      boundary₀.faces ∪ boundary₁.faces := by
    ext s
    constructor
    · rintro ⟨hsR, hsW⟩
      have hxs := centroid_mem_openSimplex_of_mem_faces T s hsR.1
      have hxR : s.centroid ℝ id ∈ R.space :=
        hcorespace.subset (core.convexHull_subset_space hsR
          (openSimplex_subset_convexHull s hxs))
      have hxW : s.centroid ℝ id ∈ W :=
        hcollarspace.subset (collar.convexHull_subset_space hsW
          (openSimplex_subset_convexHull s hxs))
      rcases htrace'.subset ⟨hxW, hxR⟩ with hx₀ | hx₁
      · exact Or.inl (mem_faces_of_mem_openSimplex_of_mem_space
          (restrict_faces_subset T C₀) hsR.1 hxs (hboundary₀space.symm.subset hx₀))
      · exact Or.inr (mem_faces_of_mem_openSimplex_of_mem_space
          (restrict_faces_subset T C₁) hsR.1 hxs (hboundary₁space.symm.subset hx₁))
    · rintro (hs | hs)
      · exact ⟨⟨hs.1, hs.2.trans hC₀R⟩, ⟨hs.1, hs.2.trans hC₀W⟩⟩
      · exact ⟨⟨hs.1, hs.2.trans hC₁R⟩, ⟨hs.1, hs.2.trans hC₁W⟩⟩
  have hboundaryFacesDisjoint : Disjoint boundary₀.faces boundary₁.faces := by
    apply disjoint_left.mpr
    intro s hs₀ hs₁
    have hxs := centroid_mem_openSimplex_of_mem_faces T s hs₀.1
    exact Set.disjoint_left.mp hCdis
      (hboundary₀space.subset (boundary₀.convexHull_subset_space hs₀
        (openSimplex_subset_convexHull s hxs)))
      (hboundary₁space.subset (boundary₁.convexHull_subset_space hs₁
        (openSimplex_subset_convexHull s hxs)))
  have hdata : SurfaceSplitAlongPolygon source split := by
    refine
      { core := core
        collar := collar
        boundary₀ := boundary₀
        boundary₁ := boundary₁
        core_faces_finite := hcorefin
        collar_faces_finite := hcollarfin
        boundary₀_faces_finite := hboundary₀fin
        boundary₁_faces_finite := hboundary₁fin
        source_faces := hsourceFaces
        core_inter_collar_faces := hinterFaces
        boundary_faces_disjoint := hboundaryFacesDisjoint
        boundary₀_isPLSphere := hboundary₀space.symm ▸ hC₀
        boundary₁_isPLSphere := hboundary₁space.symm ▸ hC₁
        collarHomeomorph := ⟨_, hboundary₀space.symm ▸ hcollarspace.symm ▸ hcollarMap⟩
        splitHomeomorph := ⟨id, (isPolyhedron_space core).isPLHomeomorphOn_id⟩ }
  have hsplit : IsSubdivision split R := hTR
  exact ⟨source, split, hsourcefin, hcorefin, hTK, hsplit,
    hR.of_isSubdivision hsplit, ⟨hdata⟩⟩

end DifferentialGeometry.Topology.PiecewiseLinear
