import DifferentialGeometry.Topology.PiecewiseLinear.Section34CompactRegularNeighborhood
import DifferentialGeometry.Topology.PiecewiseLinear.PieceTransition
import DifferentialGeometry.Topology.PiecewiseLinear.CylindricalClassification
import DifferentialGeometry.Topology.PiecewiseLinear.Section34InnerTubeBicollar

open Set Topology

namespace DifferentialGeometry.Topology.PiecewiseLinear

theorem LocallyFinitePLPieceIn.exists_finite_piece_of_space_subset
    {n : ℕ} {X E : Type*} [TopologicalSpace X]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) X]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] {U : Set X}
    (T : LocallyFinitePLPieceIn E n X U) (L : Geometry.SimplicialComplex ℝ E)
    (hfin : L.faces.Finite) (hsub : L.space ⊆ T.complex.space) :
    ∃ P : PLPieceIn E n X (T.map '' L.space), P.complex = L ∧ P.map = T.map := by
  let _ : Finite L.faces := hfin.to_subtype
  have hbij : BijOn T.map L.space (T.map '' L.space) :=
    (T.bijOn.injOn.mono hsub).bijOn_image
  refine ⟨⟨L, hfin, T.map, hbij, T.continuousOn.mono hsub, ?_, ?_⟩, rfl, rfl⟩
  · intro e he
    have h := (T.isPiecewiseAffineOn_chart e he).inter_of_isPolyhedron
      (isPolyhedron_space L)
    have heq : (T.complex.space ∩ T.map ⁻¹' e.source) ∩ L.space =
        L.space ∩ T.map ⁻¹' e.source := by
      ext x
      exact ⟨fun hx => ⟨hx.2, hx.1.2⟩, fun hx => ⟨⟨hsub hx.1, hx.2⟩, hx.1⟩⟩
    rwa [heq] at h
  · intro e he
    have h := (T.isPiecewiseAffineOn_chart_symm e he).inter_preimage_of_isPolyhedron
      (isPolyhedron_space L)
    have heq : (e.target ∩ e.symm ⁻¹' U) ∩
        (Function.invFunOn T.map T.complex.space ∘ e.symm) ⁻¹' L.space =
        e.target ∩ e.symm ⁻¹' (T.map '' L.space) := by
      ext y
      constructor
      · rintro ⟨⟨hy, hyU⟩, hyL⟩
        exact ⟨hy, Function.invFunOn T.map T.complex.space (e.symm y), hyL,
          T.bijOn.invOn_invFunOn.2 hyU⟩
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
    have hU := (image_mono hsub).trans T.bijOn.mapsTo.image_subset hy.2
    exact T.bijOn.injOn (hsub hmem) (T.bijOn.surjOn.mapsTo_invFunOn hU)
      ((hbij.invOn_invFunOn.2 hy.2).trans (T.bijOn.invOn_invFunOn.2 hU).symm)

open Classical in
theorem IsPLDerivedNeighborhoodExhaustion.exists_cylindrical_piece_of_isPolyhedralSphere
    {X : Type*} [TopologicalSpace X] [ChartedSpace (EuclideanSpace ℝ (Fin 3)) X]
    {N J U : Set X} (h : IsPLDerivedNeighborhoodExhaustion (n := 3) N J U)
    (hN : IsCompact N) (hJ : IsPolyhedralSphere (n := 3) 1 J) :
    ∃ (m : ℕ) (T : PLPieceIn (EuclideanSpace ℝ (Fin m)) 3 X N)
      (f : (Fin 3 → ℝ) × ℝ → EuclideanSpace ℝ (Fin m)),
      IsCombinatorialManifoldWithBoundary 3 T.complex ∧
      IsCylindricalDiagram f (Convexity.StdSimplex.coordinateSet ℝ (Fin 3)) T.complex.space := by
  obtain ⟨m, T, A, L, hAfin, hLfin, hAT, hLA, -, hA, hD, hNimage, hJimage⟩ :=
    h.exists_finite_stage_of_isCompact hN
  let _ : DecidableEq (EuclideanSpace ℝ (Fin m)) := Classical.decEq _
  let _ : Finite A.faces := hAfin.to_subtype
  let _ : Finite L.faces := hLfin.to_subtype
  have hAS : A.space ⊆ T.complex.space := space_mono_of_faces_subset hAT
  obtain ⟨P, hPL, -⟩ := T.exists_finite_piece_of_space_subset L hLfin
    ((space_mono_of_faces_subset hLA).trans hAS)
  have hL : IsPLSphere 1 L.space := by
    have hJ' : IsPolyhedralSphere (n := 3) 1 (T.map '' L.space) := hJimage.symm ▸ hJ
    have h := hJ'.isPLSphere_of_piece (⟨m, P⟩ : PLPiece 3 X (T.map '' L.space))
    change IsPLSphere 1 P.complex.space at h
    rwa [hPL] at h
  obtain ⟨f, hf⟩ := exists_cylindricalDiagram_derivedNeighborhood_circle A L hA hLA
    hL.isCombinatorialManifold hL.isConnected
  obtain ⟨Q, hQD, -⟩ := T.exists_finite_piece_of_space_subset (derivedNeighborhood A L)
    (derivedNeighborhood_faces_finite A L) ((derivedNeighborhood_space_subset A L).trans hAS)
  have hout : ∃ Q : PLPieceIn (EuclideanSpace ℝ (Fin m)) 3 X
      (T.map '' (derivedNeighborhood A L).space),
      IsCombinatorialManifoldWithBoundary 3 Q.complex ∧
      IsCylindricalDiagram f (Convexity.StdSimplex.coordinateSet ℝ (Fin 3)) Q.complex.space := by
    exact ⟨Q, hQD.symm ▸ hD, hQD.symm ▸ hf⟩
  rw [hNimage] at hout
  obtain ⟨Q, hQ, hf⟩ := hout
  exact ⟨m, Q, f, hQ, hf⟩

theorem PLPieceIn.isPLHomeomorphOn_invFunOn_comp
    {X : Type*} [TopologicalSpace X] [ChartedSpace (EuclideanSpace ℝ (Fin 3)) X]
    {m : ℕ} {N : Set X} (T : PLPieceIn (EuclideanSpace ℝ (Fin m)) 3 X N)
    {P : Set (EuclideanSpace ℝ (Fin 3))} {u : EuclideanSpace ℝ (Fin 3) → X}
    (hu : IsPLHomeomorphInto 3 u P) (hNP : N ⊆ u '' P) :
    IsPLHomeomorphOn (Function.invFunOn u P ∘ T.map) T.complex.space
      (Function.invFunOn u P '' N) := by
  have hid : IsPiecewiseAffineOn (id : EuclideanSpace ℝ (Fin m) → _)
      T.complex.space :=
    (isPiecewiseAffineOn_id isOpen_univ).mono_of_isPolyhedron T.isPolyhedron_space
      (subset_univ _)
  have hmap : IsPLOn m 3 (T.map ∘ id) T.complex.space :=
    T.isPLOn_comp hid (mapsTo_id _)
  have hmaps : MapsTo (T.map ∘ id) T.complex.space (u '' P) :=
    fun x hx => hNP (T.bijOn.mapsTo hx)
  have hpa : IsPiecewiseAffineOn (Function.invFunOn u P ∘ T.map ∘ id)
      T.complex.space :=
    isPLOn_iff_isPiecewiseAffineOn.mp
      (IsPLOn.comp_of_mapsTo (hu.isPLOn_inverse hu.injOn.leftInvOn_invFunOn) hmap hmaps)
  have hsec : ∀ z ∈ u '' P, u (Function.invFunOn u P z) = z := fun z hz =>
    hu.injOn.bijOn_image.invOn_invFunOn.2 hz
  have hinj : InjOn (Function.invFunOn u P ∘ T.map) T.complex.space := by
    intro x hx y hy hxy
    refine T.bijOn.injOn hx hy ?_
    have hx' := hsec _ (hmaps hx)
    have hy' := hsec _ (hmaps hy)
    exact hx'.symm.trans ((congrArg u hxy).trans hy')
  have himg : (Function.invFunOn u P ∘ T.map) '' T.complex.space =
      Function.invFunOn u P '' N := by rw [image_comp, T.bijOn.image_eq]
  rw [← himg]
  exact isPLHomeomorphOn_of_isPiecewiseAffineOn_of_bijOn T.isPolyhedron_space hpa
    hinj.bijOn_image

theorem IsCylindricalDiagram.postcomp_equivalence
    {E F G : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    [NormedAddCommGroup G] [NormedSpace ℝ G]
    {f : E × ℝ → F} {P : Set E} {S : Set F} {S' : Set G} {g : F → G}
    (hf : IsCylindricalDiagram f P S) (hg : IsPLHomeomorphOn g S S') :
    IsCylindricalDiagram (g ∘ f) P S' := by
  have hmap : MapsTo f (P ×ˢ Icc (0 : ℝ) 1) S := hf.image_eq ▸ mapsTo_image f _
  have hpa := hg.isPiecewiseAffineOn.comp hf.isPiecewiseAffineOn
  have heq : (P ×ˢ Icc (0 : ℝ) 1) ∩ f ⁻¹' S = P ×ˢ Icc (0 : ℝ) 1 :=
    inter_eq_left.mpr hmap
  rw [heq] at hpa
  refine ⟨hpa, ?_, ?_, ?_⟩
  · rw [image_comp, hf.image_eq, hg.image_eq]
  · rw [image_comp, image_comp, hf.image_top_eq_bottom]
  · intro x hx y hy hxy
    exact hf.eq_or_endpoints x hx y hy (hg.bijOn.injOn (hmap hx) (hmap hy) hxy)

open Classical in
theorem IsPLHomeomorphInto.exists_cylindrical_regular_circle_model
    {X : Type*} [TopologicalSpace X] [ChartedSpace (EuclideanSpace ℝ (Fin 3)) X]
    {N J U : Set X} {P : Set (EuclideanSpace ℝ (Fin 3))}
    {u : EuclideanSpace ℝ (Fin 3) → X} (hu : IsPLHomeomorphInto 3 u P)
    (h : IsPLDerivedNeighborhoodExhaustion (n := 3) N J U)
    (hN : IsCompact N) (hJ : IsPolyhedralSphere (n := 3) 1 J) (hNP : N ⊆ u '' P) :
    ∃ (R : Geometry.SimplicialComplex ℝ (EuclideanSpace ℝ (Fin 3)))
      (f : (Fin 3 → ℝ) × ℝ → EuclideanSpace ℝ (Fin 3)),
      R.faces.Finite ∧ R.space = Function.invFunOn u P '' N ∧ R.space ⊆ P ∧
      u '' R.space = N ∧ IsCombinatorialManifoldWithBoundary 3 R ∧
      IsCylindricalDiagram f (Convexity.StdSimplex.coordinateSet ℝ (Fin 3)) R.space ∧
      ∀ x ∈ Convexity.StdSimplex.coordinateSet ℝ (Fin 3), f (x, 0) = f (x, 1) := by
  obtain ⟨m, T, f₀, hT, hf₀⟩ := h.exists_cylindrical_piece_of_isPolyhedralSphere hN hJ
  let _ : Finite T.complex.faces := T.finite_faces.to_subtype
  have hτ := T.isPLHomeomorphOn_invFunOn_comp hu hNP
  have hpoly : IsPolyhedron (Function.invFunOn u P '' N) := by
    rw [← hτ.image_eq]
    exact T.isPolyhedron_space.image_of_isPiecewiseAffineOn hτ.isPiecewiseAffineOn hτ.bijOn.injOn
  obtain ⟨R, hRfin, hRspace⟩ := hpoly.exists_simplicialComplex
  let _ : Finite R.faces := hRfin.to_subtype
  have hτR : IsPLHomeomorphOn (Function.invFunOn u P ∘ T.map) T.complex.space R.space :=
    hRspace.symm ▸ hτ
  have hR : IsCombinatorialManifoldWithBoundary 3 R := hT.of_isPLHomeomorphOn hτR
  have hdiagram := hf₀.postcomp_equivalence hτR
  obtain ⟨S, -, hScard, hRS⟩ := exists_affineIndependent_openSimplex_superset 3 (by simp)
    (isPolyhedron_space R).isCompact.isBounded
  have hor : IsOrientable 3 R := isOrientable_of_space_subset_convexHull R hR S hScard
    (hRS.trans (openSimplex_subset_convexHull S))
  obtain ⟨f, hf, hends⟩ := hdiagram.exists_endMap_id_of_isOrientable (isPLBall_stdSimplex 2)
    R hR hor
  have hRP : R.space ⊆ P := by
    rw [hRspace]
    rintro x ⟨y, hy, rfl⟩
    exact hu.injOn.bijOn_image.surjOn.mapsTo_invFunOn (hNP hy)
  have himage : u '' R.space = N := by
    rw [hRspace]
    ext y
    constructor
    · rintro ⟨x, ⟨z, hz, rfl⟩, rfl⟩
      simpa only [hu.injOn.bijOn_image.invOn_invFunOn.2 (hNP hz)] using hz
    · intro hy
      exact ⟨Function.invFunOn u P y, mem_image_of_mem _ hy,
        hu.injOn.bijOn_image.invOn_invFunOn.2 (hNP hy)⟩
  exact ⟨R, f, hRfin, hRspace, hRP, himage, hR, hf, hends⟩

universe u

variable {Ea : Type} [NormedAddCommGroup Ea] [NormedSpace ℝ Ea]
  {M₁ M₂ : Type u} [TopologicalSpace M₁] [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M₁]
  [MetricSpace M₂] [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M₂] {U : Set M₁} {h : M₁ → M₂}
  {𝒦 𝒦' : LocallyFinitePLPieceIn Ea 3 M₁ U}
  {src : Section34CutLabelOf 𝒦 𝒦' → Set M₁}
  {Q : Section34VertexIndex 𝒦 𝒦' → Set M₂}
  {Cp CpBd Cc CcBd Kcore : Section34VertexIndex 𝒦 𝒦' → Set M₁}
  {ε : Section34VertexIndex 𝒦 𝒦' → ℝ}
  {ends : Section34EdgeIndex 𝒦 𝒦' →
    Section34VertexIndex 𝒦 𝒦' × Section34VertexIndex 𝒦 𝒦'}
  {Sn Tn Aa Ab₀ Ab₁ Bb Bb₀ Bb₁ Bc Bc₀ Bc₁ : Section34EdgeIndex 𝒦 𝒦' → Set M₁}
  {Sp Tp : Section34EdgeIndex 𝒦 𝒦' → Set M₂} {cnt : Section34EdgeIndex 𝒦 𝒦' → ℕ}
  {Pg : Section34EdgeIndex 𝒦 𝒦' → ℕ → Set M₂}
  {G : Section34VertexIndex 𝒦 𝒦' → M₁ → M₂}

theorem exists_section34_outer_tube_cylindrical_model
    (hprep : Section34VertexPreparation U 𝒦 𝒦' h src Q ends Cp CpBd Cc CcBd Kcore Sn Tn Aa Ab₀ Ab₁
      Bb Bb₀ Bb₁ Bc Bc₀ Bc₁ ε)
    (hpack : Section34PiercingConditions U 𝒦 𝒦' h Q ends Cp CpBd Cc Sn Tn Aa Ab₀ Ab₁ Bb Bb₀
      Bb₁ Sp Tp cnt Pg G) (e : Section34EdgeIndex 𝒦 𝒦') :
    ∃ (P : Set (EuclideanSpace ℝ (Fin 3))) (u : EuclideanSpace ℝ (Fin 3) → M₂)
      (R : Geometry.SimplicialComplex ℝ (EuclideanSpace ℝ (Fin 3)))
      (f : (Fin 3 → ℝ) × ℝ → EuclideanSpace ℝ (Fin 3)),
      IsPLBall 3 P ∧ IsPLHomeomorphInto 3 u P ∧ u '' P = G (ends e).1 '' Cc (ends e).1 ∧
      R.faces.Finite ∧ R.space ⊆ P ∧ u '' R.space = Sp e ∧
      IsCombinatorialManifoldWithBoundary 3 R ∧
      IsCylindricalDiagram f (Convexity.StdSimplex.coordinateSet ℝ (Fin 3)) R.space ∧
      ∀ x ∈ Convexity.StdSimplex.coordinateSet ℝ (Fin 3), f (x, 0) = f (x, 1) := by
  obtain ⟨-, hCc, -, -, -, -, -, -, -, hJ, hreg, htor, hSn, -⟩ := id hprep
  obtain ⟨hG, -, -, htube, -⟩ := id hpack
  obtain ⟨P, r, u, hr, hu, hcell, -⟩ := hCc (ends e).1
  have hNP : Sn e ⊆ u '' P := (hSn e (ends e).1 (Or.inl rfl)).trans hcell.subset
  obtain ⟨v⟩ := (htor e).2.1
  have hN : IsCompact (Sn e) := isCompact_iff_compactSpace.mpr v.symm.compactSpace
  obtain ⟨R, f, hRfin, -, hRP, hRimage, hR, hf, hends⟩ :=
    hu.exists_cylindrical_regular_circle_model (hreg e).1.1 hN (hJ e).1 hNP
  have hGu : IsPLHomeomorphInto 3 (G (ends e).1 ∘ u) P :=
    hu.comp_of_image_eq (hcell ▸ hG (ends e).1)
  refine ⟨P, G (ends e).1 ∘ u, R, f, ⟨r, hr⟩, hGu, ?_, hRfin, hRP, ?_, hR, hf, hends⟩
  · rw [image_comp, ← hcell]
  · rw [image_comp, hRimage, ← (htube e).1]

end DifferentialGeometry.Topology.PiecewiseLinear
