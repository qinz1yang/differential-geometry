/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.LoopTheorem.NormalCell
import DifferentialGeometry.Topology.PiecewiseLinear.LoopTheorem.SingularSetLocalModel

open Set Topology
namespace DifferentialGeometry.Topology.PiecewiseLinear
universe u
section Restrict
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {n : ℕ} {X : Type u} [TopologicalSpace X] [ChartedSpace (EuclideanSpace ℝ (Fin n)) X]
def PLPieceIn.restrictOfSpaceSubset {Y : Set X} (T : PLPieceIn E n X Y)
    (L : Geometry.SimplicialComplex ℝ E) (hfin : L.faces.Finite)
    (hsub : L.space ⊆ T.complex.space) : PLPieceIn E n X (T.map '' L.space) := by
  have : Finite L.faces := hfin.to_subtype
  have hbij : BijOn T.map L.space (T.map '' L.space) :=
    (T.bijOn.injOn.mono hsub).bijOn_image
  refine ⟨L, hfin, T.map, hbij, T.continuousOn.mono hsub, fun e he => ?_, fun e he => ?_⟩
  · have h := (T.isPiecewiseAffineOn_chart e he).inter_of_isPolyhedron
      (PiecewiseLinear.isPolyhedron_space L)
    have heq : (T.complex.space ∩ T.map ⁻¹' e.source) ∩ L.space =
        L.space ∩ T.map ⁻¹' e.source := by
      ext x
      exact ⟨fun hx => ⟨hx.2, hx.1.2⟩, fun hx => ⟨⟨hsub hx.1, hx.2⟩, hx.1⟩⟩
    rwa [heq] at h
  · have h := (T.isPiecewiseAffineOn_chart_symm e he).inter_preimage_of_isPolyhedron
      (PiecewiseLinear.isPolyhedron_space L)
    have heq : (e.target ∩ e.symm ⁻¹' Y) ∩
        (Function.invFunOn T.map T.complex.space ∘ e.symm) ⁻¹' L.space =
        e.target ∩ e.symm ⁻¹' (T.map '' L.space) := by
      ext y
      constructor
      · rintro ⟨⟨hy, hyY⟩, hyL⟩
        exact ⟨hy, Function.invFunOn T.map T.complex.space (e.symm y), hyL,
          T.bijOn.invOn_invFunOn.2 hyY⟩
      · rintro ⟨hy, z, hz, hzy⟩
        refine ⟨⟨hy, ?_⟩, ?_⟩
        · change e.symm y ∈ Y
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
open Classical in
theorem PLPieceIn.exists_transport_isPLHomeomorphOn {F : Type*} [NormedAddCommGroup F]
    [NormedSpace ℝ F] [FiniteDimensional ℝ F] {Y : Set X} (T : PLPieceIn E n X Y)
    (L : E ≃ₗ[ℝ] F) :
    ∃ T' : PLPieceIn F n X Y, IsPLHomeomorphOn (L : E → F) T.complex.space T'.complex.space ∧
      ∀ x ∈ T.complex.space, T'.map (L x) = T.map x := by
  classical
  have : Finite T.complex.faces := T.finite_faces.to_subtype
  obtain ⟨T', hfaces, htrans⟩ := T.exists_transport L
  have hind : ∀ s ∈ T.complex.faces,
      AffineIndependent ℝ ((↑) : {u // u ∈ s.image (L : E → F)} → F) := fun _ hs =>
    affineIndependent_image_of_injOn_convexHull (L : E →ₗ[ℝ] F).toAffineMap (T.complex.indep hs)
      L.injective.injOn
  have hmapeq : EqOn (simplicialMap T.complex (L : E → F)) (L : E → F) T.complex.space :=
    simplicialMap_eq_of_forall_affineOn T.complex (L : E → F) fun _ _ =>
      ⟨(L : E →ₗ[ℝ] F).toAffineMap, fun _ _ => rfl⟩
  have hinjmap : InjOn (simplicialMap T.complex (L : E → F)) T.complex.space :=
    fun x hx y hy hxy => L.injective ((hmapeq hx).symm.trans (hxy.trans (hmapeq hy)))
  have hspaceim : T'.complex.space
      = (simplicialImage T.complex (L : E → F) hind hinjmap).space := by
    ext z
    constructor
    · intro hz
      obtain ⟨s, hs, hzs⟩ := T'.complex.mem_space_iff.mp hz
      refine (simplicialImage T.complex (L : E → F) hind hinjmap).mem_space_iff.mpr
        ⟨s, ?_, hzs⟩
      rw [hfaces] at hs
      exact hs
    · intro hz
      obtain ⟨s, hs, hzs⟩ :=
        (simplicialImage T.complex (L : E → F) hind hinjmap).mem_space_iff.mp hz
      refine T'.complex.mem_space_iff.mpr ⟨s, ?_, hzs⟩
      rw [hfaces]
      exact hs
  refine ⟨T', ?_, htrans⟩
  rw [hspaceim]
  exact (isPLHomeomorphOn_simplicialImage T.complex (L : E → F) hind hinjmap).congr hmapeq.symm
end Restrict
section Subdivision
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
theorem exists_isSubdivision_singleton_mem_of_finset (K : Geometry.SimplicialComplex ℝ E)
    [Finite K.faces] (t : Finset E) (hsub : (t : Set E) ⊆ K.space) :
    ∃ K' : Geometry.SimplicialComplex ℝ E, IsSubdivision K' K ∧ K'.faces.Finite ∧
      ∀ x ∈ t, ({x} : Finset E) ∈ K'.faces := by
  classical
  induction t using Finset.induction_on with
  | empty => exact ⟨K, IsSubdivision.refl K, Set.toFinite _, by simp⟩
  | insert a s ha ih =>
      obtain ⟨K₁, hK₁sub, hK₁fin, hK₁vert⟩ := ih
        (subset_trans (by simp) hsub)
      have _ : Finite K₁.faces := hK₁fin.to_subtype
      have haK₁ : a ∈ K₁.space := by
        rw [hK₁sub.space_eq]
        exact hsub (by simp)
      obtain ⟨K₂, hK₂sub, hK₂fin, haK₂⟩ := exists_isSubdivision_singleton_mem K₁ haK₁
      refine ⟨K₂, hK₂sub.trans hK₁sub, hK₂fin, fun x hx => ?_⟩
      rcases Finset.mem_insert.mp hx with rfl | hxs
      · exact haK₂
      · exact hK₂sub.singleton_mem (hK₁vert x hxs)
end Subdivision
section Recognition
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
open Classical in
theorem SingularTwoCell.exists_triangulation_image_doublePointSet
    (K : Geometry.SimplicialComplex ℝ E) [Finite K.faces] (hK : IsCombinatorialManifold 3 K) :
    letI := combinatorialChartedSpace K hK
    ∀ (D : SingularTwoCell K.space) (BdM : Set K.space),
      (∀ x ∈ D.domain, ∃ V ∈ 𝓝[D.domain] x, Set.InjOn D V) →
      D '' D.domain ∩ BdM = Set.range D.boundary →
      (∀ y ∈ doublePointSet D D.domain,
        ∃ e ∈ atlas (EuclideanSpace ℝ (Fin 3)) K.space, y ∈ e.source ∧
          HasPLNormalDoubleCrossingAt (e ∘ D) (D.domain ∩ D ⁻¹' e.source)
            (e '' (e.source ∩ BdM)) (e y)) →
      ∃ G : Geometry.SimplicialComplex ℝ E, G.faces.Finite ∧
        G.space = Subtype.val '' doublePointSet D D.domain ∧
          IsCombinatorialManifoldWithBoundary 1 G ∧
            (boundaryComplex 1 G).space =
              Subtype.val '' doublePointSet D D.domain ∩ Subtype.val '' BdM := by
  let _ := combinatorialChartedSpace K hK
  intro D BdM hloc himage hcross
  have hpoly : IsPolyhedron (Subtype.val '' doublePointSet D D.domain) :=
    SingularTwoCell.isPolyhedron_image_doublePointSet K hK D hloc
  obtain ⟨G₀, hG₀fin, hG₀space⟩ := hpoly.exists_simplicialComplex
  have _ : Finite G₀.faces := hG₀fin.to_subtype
  have hbdfinite : (Subtype.val '' doublePointSet D D.domain ∩ Subtype.val '' BdM).Finite :=
    SingularTwoCell.finite_image_doublePointSet_inter_boundary K hK D BdM hloc himage hcross
  obtain ⟨G, hsubG, hGfin, hGvert⟩ :=
    exists_isSubdivision_singleton_mem_of_finset G₀ hbdfinite.toFinset (by
      rw [hbdfinite.coe_toFinset, hG₀space]
      exact inter_subset_left)
  have _ : Finite G.faces := hGfin.to_subtype
  have hGspace : G.space = Subtype.val '' doublePointSet D D.domain := by
    rw [hsubG.space_eq, hG₀space]
  have hGcard : ∀ s ∈ G.faces, s.card ≤ 2 :=
    SingularTwoCell.card_le_two_of_space_eq_image_doublePointSet K hK D BdM G himage hcross
      hGspace
  have hmodel :=
    SingularTwoCell.exists_local_arc_model_image_doublePointSet K hK D BdM himage hcross
  have hev : ∀ x ∈ Subtype.val '' doublePointSet D D.domain,
      ∀ (H : Geometry.SimplicialComplex ℝ E) (N : Set E), IsOpen N → x ∈ N →
        (∀ z ∈ N, (z ∈ Subtype.val '' doublePointSet D D.domain ↔ z ∈ H.space)) →
          ∀ᶠ z in 𝓝 x, (z ∈ G.space ↔ z ∈ H.space) := by
    intro x _ H N hNopen hxN hgerm
    filter_upwards [hNopen.mem_nhds hxN] with z hz
    rw [hGspace]
    exact hgerm z hz
  have hGman : IsCombinatorialManifoldWithBoundary 1 G := by
    refine isCombinatorialManifoldWithBoundary_one_of_locally_eq G hGcard fun x hx => ?_
    rw [hGspace] at hx
    obtain ⟨H, N, hHfin, hHball, -, hNopen, hxN, hgerm, -, -⟩ := hmodel x hx
    have _ : Finite H.faces := hHfin.to_subtype
    exact ⟨H, hHfin, IsPLBall.isCombinatorialManifoldWithBoundary (n := 0) hHball,
      (hgerm x hxN).mp hx, hev x hx H N hNopen hxN hgerm⟩
  have hGbd : (boundaryComplex 1 G).space =
      Subtype.val '' doublePointSet D D.domain ∩ Subtype.val '' BdM := by
    ext x
    constructor
    · intro hxb
      have hxS : x ∈ Subtype.val '' doublePointSet D D.domain := by
        rw [← hGspace]
        exact boundaryComplex_space_subset 1 G hxb
      refine ⟨hxS, ?_⟩
      obtain ⟨H, N, hHfin, hHball, hxH, hNopen, hxN, hgerm, -, hbdiff⟩ := hmodel x hxS
      have _ : Finite H.faces := hHfin.to_subtype
      have hxGf : ({x} : Finset E) ∈ G.faces :=
        ((mem_boundaryComplex_one_space_iff G hGcard).mp hxb).1
      exact hbdiff.mp ((mem_boundaryComplex_one_space_iff_of_eventually_eq G H hGcard
        (IsPLBall.isCombinatorialManifoldWithBoundary (n := 0) hHball) hxGf hxH
        (hev x hxS H N hNopen hxN hgerm)).mp hxb)
    · rintro ⟨hxS, hxB⟩
      obtain ⟨H, N, hHfin, hHball, hxH, hNopen, hxN, hgerm, -, hbdiff⟩ := hmodel x hxS
      have _ : Finite H.faces := hHfin.to_subtype
      have hxGf : ({x} : Finset E) ∈ G.faces :=
        hGvert x (hbdfinite.mem_toFinset.mpr ⟨hxS, hxB⟩)
      exact (mem_boundaryComplex_one_space_iff_of_eventually_eq G H hGcard
        (IsPLBall.isCombinatorialManifoldWithBoundary (n := 0) hHball) hxGf hxH
        (hev x hxS H N hNopen hxN hgerm)).mpr (hbdiff.mpr hxB)
  exact ⟨G, hGfin, hGspace, hGman, hGbd⟩
open Classical in
theorem nonempty_normalSingularSetTriangulation_of_piece {M : Type u} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] {D : SingularTwoCell M} {BdM : Set M}
    (T : PLPieceIn E 3 M univ) (G : Geometry.SimplicialComplex ℝ E) (hGfin : G.faces.Finite)
    (hGsub : G.space ⊆ T.complex.space) (hGman : IsCombinatorialManifoldWithBoundary 1 G)
    (hspace : T.map '' G.space = doublePointSet D D.domain)
    (hbd : T.map '' (boundaryComplex 1 G).space = doublePointSet D D.domain ∩ BdM) :
    Nonempty (NormalSingularSetTriangulation D BdM) := by
  have _ : Finite G.faces := hGfin.to_subtype
  obtain ⟨Tres, hTrescomplex, hTresmap⟩ :
      ∃ Tres : PLPieceIn E 3 M (T.map '' G.space), Tres.complex = G ∧ Tres.map = T.map :=
    ⟨T.restrictOfSpaceSubset G hGfin hGsub, rfl, rfl⟩
  obtain ⟨Lin⟩ : Nonempty (E ≃ₗ[ℝ] EuclideanSpace ℝ (Fin (Module.finrank ℝ E))) :=
    ⟨(Module.finBasis ℝ E).equivFun.trans (WithLp.linearEquiv 2 ℝ _).symm⟩
  obtain ⟨T₂, hPLL, htrans⟩ := Tres.exists_transport_isPLHomeomorphOn Lin
  rw [hTrescomplex] at hPLL
  rw [hTrescomplex, hTresmap] at htrans
  have _ : Finite T₂.complex.faces := T₂.finite_faces.to_subtype
  have hspaceLin : T₂.complex.space = (Lin : E → _) '' G.space := hPLL.bijOn.image_eq.symm
  have hdec : (fun (a b : EuclideanSpace ℝ (Fin (Module.finrank ℝ E))) =>
      Classical.propDecidable (a = b)) =
      (inferInstance : DecidableEq (EuclideanSpace ℝ (Fin (Module.finrank ℝ E)))) :=
    Subsingleton.elim _ _
  have hbdLin : (boundaryComplex 1 T₂.complex).space =
      (Lin : E → _) '' (boundaryComplex 1 G).space := by
    have h := boundaryComplex_space_of_isPLHomeomorphOn (n := 0) G T₂.complex hGman hPLL
    rwa [hdec] at h
  have htransimage : ∀ S : Set E, S ⊆ G.space →
      T₂.map '' ((Lin : E → _) '' S) = T.map '' S := by
    intro S hS
    ext w
    constructor
    · rintro ⟨_, ⟨z, hz, rfl⟩, rfl⟩
      exact ⟨z, hz, (htrans z (hS hz)).symm⟩
    · rintro ⟨z, hz, rfl⟩
      exact ⟨Lin z, ⟨z, hz, rfl⟩, htrans z (hS hz)⟩
  have hmapspace : T₂.map '' T₂.complex.space = doublePointSet D D.domain := by
    rw [hspaceLin, htransimage G.space subset_rfl, hspace]
  have hmapbd : T₂.map '' (boundaryComplex 1 T₂.complex).space =
      doublePointSet D D.domain ∩ BdM := by
    rw [hbdLin, htransimage _ (boundaryComplex_space_subset 1 G), hbd]
  have hman : IsCombinatorialManifoldWithBoundary 1 T₂.complex :=
    hGman.of_isPLHomeomorphOn hPLL
  exact ⟨{
    carrier := T.map '' G.space
    piece := ⟨Module.finrank ℝ E, T₂⟩
    complex := T₂.complex
    finite_faces := T₂.finite_faces
    faces_subset := subset_rfl
    isManifoldWithBoundary := hman
    map_space := hmapspace
    map_boundary := hmapbd }⟩
open Classical in
theorem nonempty_normalSingularSetTriangulation_of_triangulation
    (K : Geometry.SimplicialComplex ℝ E) [Finite K.faces] (hK : IsCombinatorialManifold 3 K) :
    letI := combinatorialChartedSpace K hK
    ∀ (D : SingularTwoCell K.space) (BdM : Set K.space) (G : Geometry.SimplicialComplex ℝ E),
      G.faces.Finite →
      G.space = Subtype.val '' doublePointSet D D.domain →
      IsCombinatorialManifoldWithBoundary 1 G →
      (boundaryComplex 1 G).space =
        Subtype.val '' doublePointSet D D.domain ∩ Subtype.val '' BdM →
      Nonempty (NormalSingularSetTriangulation D BdM) := by
  let _ := combinatorialChartedSpace K hK
  intro D BdM G hGfin hGspace hGman hGbd
  obtain ⟨p⟩ : Nonempty K.space := ⟨D (0 : EuclideanSpace ℝ (Fin 2))⟩
  obtain ⟨T, hTcomplex, hTmapval⟩ :
      ∃ T : PLPieceIn E 3 K.space univ, T.complex = K ∧ ∀ q : K.space, T.map (q : E) = q :=
    ⟨combinatorialPLPieceIn K hK p, rfl, fun q => Subtype.ext (by
      simp only [combinatorialPLPieceIn, dite_eq_left q.2])⟩
  have hTimage : ∀ S : Set K.space, T.map '' (Subtype.val '' S) = S := by
    intro S
    ext w
    constructor
    · rintro ⟨_, ⟨q, hq, rfl⟩, rfl⟩
      rw [hTmapval q]
      exact hq
    · intro hw
      exact ⟨(w : E), ⟨w, hw, rfl⟩, hTmapval w⟩
  refine nonempty_normalSingularSetTriangulation_of_piece T G hGfin ?_ hGman ?_ ?_
  · rw [hTcomplex, hGspace]
    rintro _ ⟨q, -, rfl⟩
    exact q.2
  · rw [hGspace, hTimage]
  · rw [hGbd, ← Set.image_inter Subtype.val_injective, hTimage]
open Classical in
theorem SingularTwoCell.nonempty_normalSingularSetTriangulation_of_crossing
    (K : Geometry.SimplicialComplex ℝ E) [Finite K.faces] (hK : IsCombinatorialManifold 3 K) :
    letI := combinatorialChartedSpace K hK
    ∀ (D : SingularTwoCell K.space) (BdM : Set K.space),
      (∀ x ∈ D.domain, ∃ V ∈ 𝓝[D.domain] x, Set.InjOn D V) →
      D '' D.domain ∩ BdM = Set.range D.boundary →
      (∀ y ∈ doublePointSet D D.domain,
        ∃ e ∈ atlas (EuclideanSpace ℝ (Fin 3)) K.space, y ∈ e.source ∧
          HasPLNormalDoubleCrossingAt (e ∘ D) (D.domain ∩ D ⁻¹' e.source)
            (e '' (e.source ∩ BdM)) (e y)) →
      Nonempty (NormalSingularSetTriangulation D BdM) := by
  let _ := combinatorialChartedSpace K hK
  intro D BdM hloc himage hcross
  obtain ⟨G, hGfin, hGspace, hGman, hGbd⟩ :=
    SingularTwoCell.exists_triangulation_image_doublePointSet K hK D BdM hloc himage hcross
  exact nonempty_normalSingularSetTriangulation_of_triangulation K hK D BdM G hGfin hGspace
    hGman hGbd
open Classical in
theorem SingularTwoCell.nonempty_normalSingularCellData_of_fields
    (K : Geometry.SimplicialComplex ℝ E) [Finite K.faces] (hK : IsCombinatorialManifold 3 K) :
    letI := combinatorialChartedSpace K hK
    ∀ (D : SingularTwoCell K.space) (BdM B : Set K.space),
      (∀ x ∈ D.domain, ∃ V ∈ 𝓝[D.domain] x, Set.InjOn D V) →
      (∀ y, (D.domain ∩ D ⁻¹' {y}).encard ≤ 2) →
      Set.range D.boundary ⊆ B →
      D '' D.domain ∩ BdM = Set.range D.boundary →
      (∀ y ∈ doublePointSet D D.domain,
        ∃ e ∈ atlas (EuclideanSpace ℝ (Fin 3)) K.space, y ∈ e.source ∧
          HasPLNormalDoubleCrossingAt (e ∘ D) (D.domain ∩ D ⁻¹' e.source)
            (e '' (e.source ∩ BdM)) (e y)) →
      Nonempty (NormalSingularCellData D BdM B) := by
  let _ := combinatorialChartedSpace K hK
  intro D BdM B hloc hfiber hbsub himage hcross
  obtain ⟨T⟩ := SingularTwoCell.nonempty_normalSingularSetTriangulation_of_crossing K hK D BdM
    hloc himage hcross
  exact ⟨{
    locallyInjective := hloc
    fiber_le_two := hfiber
    boundary_image_subset := hbsub
    image_inter_boundary := himage
    singularSet := T
    crossing := hcross }⟩
end Recognition
end DifferentialGeometry.Topology.PiecewiseLinear
