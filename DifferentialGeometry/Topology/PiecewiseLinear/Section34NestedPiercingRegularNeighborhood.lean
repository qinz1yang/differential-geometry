/-
Copyright (c) 2026 Bennett Chow. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bennett Chow
-/
import DifferentialGeometry.Topology.PiecewiseLinear.DiskBallNeighborhoodImage
import DifferentialGeometry.Topology.PiecewiseLinear.DerivedNeighborhoodRestriction
import DifferentialGeometry.Topology.PiecewiseLinear.PieceRestrict

open Set Topology

namespace DifferentialGeometry.Topology.PiecewiseLinear

def LocallyFinitePLPieceIn.finiteRestriction
    {E X : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] {n : ℕ} [TopologicalSpace X]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) X] {U : Set X}
    (T : LocallyFinitePLPieceIn E n X U)
    (L : Geometry.SimplicialComplex ℝ E) [Finite L.faces]
    (hsub : L.space ⊆ T.complex.space) : PLPieceIn E n X (T.map '' L.space) := by
  have hbij : BijOn T.map L.space (T.map '' L.space) :=
    (T.bijOn.injOn.mono hsub).bijOn_image
  refine ⟨L, Set.toFinite _, T.map, hbij, T.continuousOn.mono hsub, fun e he => ?_, fun e he => ?_⟩
  · have h := (T.isPiecewiseAffineOn_chart e he).inter_of_isPolyhedron
      (PiecewiseLinear.isPolyhedron_space L)
    have heq : (T.complex.space ∩ T.map ⁻¹' e.source) ∩ L.space =
        L.space ∩ T.map ⁻¹' e.source := by
      ext x
      exact ⟨fun hx => ⟨hx.2, hx.1.2⟩, fun hx => ⟨⟨hsub hx.1, hx.2⟩, hx.1⟩⟩
    rwa [heq] at h
  · have h := (T.isPiecewiseAffineOn_chart_symm e he).inter_preimage_of_isPolyhedron
      (PiecewiseLinear.isPolyhedron_space L)
    have heq : (e.target ∩ e.symm ⁻¹' U) ∩
        (Function.invFunOn T.map T.complex.space ∘ e.symm) ⁻¹' L.space =
        e.target ∩ e.symm ⁻¹' (T.map '' L.space) := by
      ext y
      constructor
      · rintro ⟨⟨hy, hyY⟩, hyL⟩
        exact ⟨hy, Function.invFunOn T.map T.complex.space (e.symm y), hyL,
          T.bijOn.invOn_invFunOn.2 hyY⟩
      · rintro ⟨hy, z, hz, hzy⟩
        refine ⟨⟨hy, ?_⟩, ?_⟩
        · change e.symm y ∈ U
          rw [← hzy]
          exact T.bijOn.mapsTo (hsub hz)
        · change Function.invFunOn T.map T.complex.space (e.symm y) ∈ L.space
          rw [← hzy, T.bijOn.invOn_invFunOn.1 (hsub hz)]
          exact hz
    rw [heq] at h
    refine h.congr fun y hy => ?_
    have hmem := hbij.surjOn.mapsTo_invFunOn hy.2
    have hY := (image_mono hsub).trans T.bijOn.mapsTo.image_subset hy.2
    exact T.bijOn.injOn (hsub hmem) (T.bijOn.surjOn.mapsTo_invFunOn hY)
      ((hbij.invOn_invFunOn.2 hy.2).trans (T.bijOn.invOn_invFunOn.2 hY).symm)

theorem LocallyFinitePLPieceIn.exists_derivedNeighborhood_stage
    {E X : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [TopologicalSpace X]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) X] {U : Set X}
    (T : LocallyFinitePLPieceIn E 3 X U)
    (A : ℕ → Geometry.SimplicialComplex ℝ E)
    (hA : T.complex.faces = ⋃ i, (A i).faces)
    (hfin : ∀ i, (A i).faces.Finite) (hmono : Monotone fun i => (A i).faces)
    (G : Geometry.SimplicialComplex ℝ E) [Finite G.faces]
    (hG : G.faces ⊆ T.complex.faces) :
    ∃ k : ℕ, G.faces ⊆ (A k).faces ∧
      (∀ i, k ≤ i →
        (@derivedNeighborhood E _ _ (Classical.decEq E) (A i) G).space =
          (@derivedNeighborhood E _ _ (Classical.decEq E) T.complex G).space) ∧
      ∀ x ∈ G.space,
        (@derivedNeighborhood E _ _ (Classical.decEq E) (A k) G).space ∈
          𝓝[T.complex.space] x := by
  classical
  let F := {s : Finset E | s ∈ T.complex.faces ∧
    (convexHull ℝ (s : Set E) ∩ G.space).Nonempty}
  have hF : F.Finite := T.finite_faces_inter_of_isCompact
    (isPolyhedron_space G).isCompact (space_mono_of_faces_subset hG)
  have : Finite F := hF.to_subtype
  choose j hj using fun s : F => mem_iUnion.mp (hA ▸ s.2.1)
  obtain ⟨k, hk⟩ := (finite_range j).bddAbove
  have hFA (s : Finset E) (hs : s ∈ F) : s ∈ (A k).faces :=
    hmono (hk (mem_range_self ⟨s, hs⟩)) (hj ⟨s, hs⟩)
  have hsub (i : ℕ) : (A i).faces ⊆ T.complex.faces := by
    rw [hA]
    exact subset_iUnion (fun i => (A i).faces) i
  have hGA : G.faces ⊆ (A k).faces := by
    intro s hs
    have hcent : s.centroid ℝ id ∈ convexHull ℝ (s : Set E) :=
      s.centroid_mem_convexHull (G.nonempty_of_mem_faces hs)
    exact hFA s ⟨hG hs, s.centroid ℝ id, hcent, G.convexHull_subset_space hs hcent⟩
  have hDA : (derivedNeighborhood T.complex G).space ⊆ (A k).space := by
    apply derivedNeighborhood_space_subset_of_forall_face
    intro s hs t ht hst
    exact (A k).convexHull_subset_space (hFA t ⟨ht, s.centroid ℝ id, hst,
      G.convexHull_subset_space hs (s.centroid_mem_convexHull (G.nonempty_of_mem_faces hs))⟩)
  refine ⟨k, hGA, ?_, ?_⟩
  · intro i hki
    have hDAi : (derivedNeighborhood T.complex G).space ⊆ (A i).space :=
      hDA.trans (space_mono_of_faces_subset (hmono hki))
    exact (derivedNeighborhood_space_inter_subcomplex T.complex (A i) G (hsub i)).symm.trans
      (inter_eq_left.mpr hDAi)
  · intro x hx
    let I := {s : T.complex.faces // (s : Finset E) ∉ (A k).faces}
    let C (s : T.complex.faces) :=
      (Subtype.val : T.complex.space → E) ⁻¹' convexHull ℝ ((s : Finset E) : Set E)
    have hclosed : IsClosed (⋃ s : I, C s.1) :=
      (T.locallyFinite.comp_injective Subtype.val_injective).isClosed_iUnion fun s =>
        (s.1.1.finite_toSet.isCompact_convexHull (𝕜 := ℝ)).isClosed.preimage
          continuous_subtype_val
    have hxT : x ∈ T.complex.space := space_mono_of_faces_subset hG hx
    have hxnot : (⟨x, hxT⟩ : T.complex.space) ∉ ⋃ s : I, C s.1 := by
      intro h
      obtain ⟨s, hs⟩ := mem_iUnion.mp h
      exact s.2 (hFA s.1 ⟨s.1.2, x, hs, hx⟩)
    have hAn : (Subtype.val : T.complex.space → E) ⁻¹' (A k).space ∈
        𝓝 (⟨x, hxT⟩ : T.complex.space) := by
      apply Filter.mem_of_superset (hclosed.isOpen_compl.mem_nhds hxnot)
      intro z hz
      obtain ⟨s, hs, hzs⟩ := T.complex.mem_space_iff.mp z.2
      have hsA : s ∈ (A k).faces := by
        by_contra hsA
        exact hz (mem_iUnion.mpr ⟨⟨⟨s, hs⟩, hsA⟩, hzs⟩)
      exact (A k).convexHull_subset_space hsA hzs
    have : Finite (A k).faces := (hfin k).to_subtype
    exact nhdsWithin_le_of_mem (preimage_coe_mem_nhds_subtype.mp hAn)
      (derivedNeighborhood_mem_nhdsWithin hGA hx)

theorem LocallyFinitePLPieceIn.isLocallyFiniteRegularNeighborhoodOf_derivedNeighborhood
    {m : ℕ} {X : Type*} [TopologicalSpace X]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) X] {U : Set X} (hU : IsOpen U)
    (T : LocallyFinitePLPieceIn (EuclideanSpace ℝ (Fin m)) 3 X U)
    (A : ℕ → Geometry.SimplicialComplex ℝ (EuclideanSpace ℝ (Fin m)))
    (hA : T.complex.faces = ⋃ i, (A i).faces)
    (hfin : ∀ i, (A i).faces.Finite) (hmono : Monotone fun i => (A i).faces)
    (hman : ∀ i, IsCombinatorialManifoldWithBoundary 3 (A i))
    (G : Geometry.SimplicialComplex ℝ (EuclideanSpace ℝ (Fin m))) [Finite G.faces]
    (hG : G.faces ⊆ T.complex.faces) (hcard : ∀ s ∈ G.faces, s.card ≤ 2) :
    IsLocallyFiniteRegularNeighborhoodOf (n := 3)
      (T.map '' (@derivedNeighborhood _ _ _ (Classical.decEq _) T.complex G).space)
      (T.map '' G.space) U := by
  classical
  let _ : DecidableEq (EuclideanSpace ℝ (Fin m)) := Classical.decEq _
  obtain ⟨k, hGk, hstable, hnhds⟩ := T.exists_derivedNeighborhood_stage A hA hfin hmono G hG
  have : Finite (A k).faces := (hfin k).to_subtype
  let D := derivedNeighborhood (A k) G
  have hD : D.space = (derivedNeighborhood T.complex G).space := hstable k le_rfl
  let B (i : ℕ) := A (k + i)
  let L (_ : ℕ) := G
  have hBsub (i : ℕ) : (B i).faces ⊆ T.complex.faces := by
    rw [hA]
    exact subset_iUnion (fun j => (A j).faces) (k + i)
  have hcover : T.complex.faces = ⋃ i, (B i).faces := by
    apply Subset.antisymm
    · intro s hs
      obtain ⟨i, hi⟩ := mem_iUnion.mp (hA ▸ hs)
      exact mem_iUnion.mpr ⟨i, hmono (Nat.le_add_left i k) hi⟩
    · exact iUnion_subset hBsub
  have hBG (i : ℕ) : G.faces ⊆ (B i).faces := hGk.trans (hmono (Nat.le_add_right k i))
  have hBstable (i : ℕ) : (derivedNeighborhood (B i) (L i)).space = D.space :=
    (hstable (k + i) (Nat.le_add_right k i)).trans hD.symm
  have hamb : derivedNeighborhoodExhaustionAmbient B L = D.space := by
    simp only [derivedNeighborhoodExhaustionAmbient, hBstable, iUnion_const]
  have hrange : Set.range (fun x : derivedNeighborhoodExhaustionAmbient B L => T.map x) =
      T.map '' D.space := by
    ext y
    constructor
    · rintro ⟨x, rfl⟩
      exact ⟨x, hamb ▸ x.2, rfl⟩
    · rintro ⟨x, hx, rfl⟩
      exact ⟨⟨x, hamb.symm ▸ hx⟩, rfl⟩
  have hcore : (fun x : derivedNeighborhoodExhaustionAmbient B L => T.map x) ''
      derivedNeighborhoodExhaustionCore B L = T.map '' G.space := by
    ext y
    constructor
    · rintro ⟨x, hx, rfl⟩
      change (x : EuclideanSpace ℝ (Fin m)) ∈ ⋃ i, (L i).space at hx
      simpa only [L, iUnion_const] using mem_image_of_mem T.map hx
    · rintro ⟨x, hx, rfl⟩
      have hxD : x ∈ D.space := subcomplex_space_subset_derivedNeighborhood hGk hx
      let z : derivedNeighborhoodExhaustionAmbient B L := ⟨x, hamb.symm ▸ hxD⟩
      refine ⟨z, ?_, rfl⟩
      change (z : EuclideanSpace ℝ (Fin m)) ∈ ⋃ i, (L i).space
      simpa only [L, iUnion_const] using hx
  have hPL : IsPLDerivedNeighborhoodExhaustion (n := 3)
      (T.map '' D.space) (T.map '' G.space) U := by
    refine ⟨m, T, B, L, hcover, fun i => hfin (k + i), hBG, fun _ => hcard,
      fun i => hman (k + i), ?_, ?_, ?_, ?_, ?_, hrange, hcore⟩
    · intro i
      have : Finite (B i).faces := (hfin (k + i)).to_subtype
      exact (hman (k + i)).derivedNeighborhood G
    · intro i j hij
      exact hmono (Nat.add_le_add_left hij k)
    · intro i j hij
      exact Subset.rfl
    · intro i j hij s hsA hsL
      exact hsL
    · intro i x hx
      rw [hBstable, hamb]
      exact self_mem_nhdsWithin
  have hopen : IsOpenEmbedding (fun x : T.complex.space => T.map x) := by
    refine ⟨T.isEmbedding, ?_⟩
    have hrangeT : Set.range (fun x : T.complex.space => T.map x) = U := by
      exact (Set.image_eq_range T.map T.complex.space).symm.trans T.bijOn.image_eq
    rwa [hrangeT]
  have hN : T.map '' D.space ∈ nhdsSet (T.map '' G.space) := by
    apply mem_nhdsSet_iff_forall.mpr
    rintro y ⟨x, hx, rfl⟩
    have hxT := space_mono_of_faces_subset hG hx
    have hDn : (Subtype.val : T.complex.space → _) ⁻¹' D.space ∈
        𝓝 (⟨x, hxT⟩ : T.complex.space) :=
      preimage_coe_mem_nhds_subtype.mpr (hnhds x hx)
    apply Filter.mem_of_superset (hopen.isOpenMap.image_mem_nhds hDn)
    rintro z ⟨w, hw, rfl⟩
    exact ⟨w, hw, rfl⟩
  have : Finite D.faces := (derivedNeighborhood_faces_finite (A k) G).to_subtype
  have hDsub : D.space ⊆ T.complex.space := by
    rw [hD]
    exact derivedNeighborhood_space_subset T.complex G
  have hDman : IsCombinatorialManifoldWithBoundary 3 D := (hman k).derivedNeighborhood G
  have hpoly := isPolyhedralManifoldWithBoundary_of_pieceIn
    (T.finiteRestriction D hDsub) hDman
  rw [← hD]
  exact ⟨hPL, hN, hpoly.isLocallyFinite⟩

theorem IsPLDerivedNeighborhoodExhaustion.exists_ambient_derivedNeighborhoods
    {X : Type*} [TopologicalSpace X] [ChartedSpace (EuclideanSpace ℝ (Fin 3)) X]
    {N K U : Set X} (h : IsPLDerivedNeighborhoodExhaustion (n := 3) N K U)
    (hU : IsOpen U) :
    ∃ (m : ℕ) (T : LocallyFinitePLPieceIn (EuclideanSpace ℝ (Fin m)) 3 X U),
      ∀ G : Geometry.SimplicialComplex ℝ (EuclideanSpace ℝ (Fin m)),
        G.faces.Finite → G.faces ⊆ T.complex.faces →
        (∀ s ∈ G.faces, s.card ≤ 2) →
        IsLocallyFiniteRegularNeighborhoodOf (n := 3)
          (T.map '' (@derivedNeighborhood _ _ _ (Classical.decEq _) T.complex G).space)
          (T.map '' G.space) U := by
  obtain ⟨m, T, A, -, hcover, hfin, -, -, hman, -, hmono, -⟩ := h
  refine ⟨m, T, ?_⟩
  intro G hGfin hG hcard
  have : Finite G.faces := hGfin.to_subtype
  exact T.isLocallyFiniteRegularNeighborhoodOf_derivedNeighborhood hU A hcover hfin hmono
    hman G hG hcard

end DifferentialGeometry.Topology.PiecewiseLinear
