import DifferentialGeometry.Topology.PiecewiseLinear.Bicollar
import DifferentialGeometry.Topology.PiecewiseLinear.ManifoldRelativeTopology
import DifferentialGeometry.Topology.PiecewiseLinear.Section34Frame

open Set Topology

namespace DifferentialGeometry.Topology.PiecewiseLinear

theorem IsPLHomeomorphInto.exists_simplicialComplex_invFunOn_image
    {M : Type*} [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
    {m : ℕ} {P : Set (EuclideanSpace ℝ (Fin 3))} {u : EuclideanSpace ℝ (Fin 3) → M}
    (hu : IsPLHomeomorphInto 3 u P) {N : Set M}
    (hN : IsPolyhedralManifoldWithBoundary (n := 3) m N) (hNP : N ⊆ u '' P) :
    ∃ K : Geometry.SimplicialComplex ℝ (EuclideanSpace ℝ (Fin 3)),
      K.faces.Finite ∧ K.space = Function.invFunOn u P '' N ∧
        IsCombinatorialManifoldWithBoundary m K := by
  obtain ⟨T, hT⟩ := hN
  let _ : Finite T.piece.complex.faces := T.piece.finite_faces.to_subtype
  have hid : IsPiecewiseAffineOn (id : EuclideanSpace ℝ (Fin T.ambientDim) → _)
      T.piece.complex.space :=
    (isPiecewiseAffineOn_id isOpen_univ).mono_of_isPolyhedron T.piece.isPolyhedron_space
      (subset_univ _)
  have hmap : IsPLOn T.ambientDim 3 (T.piece.map ∘ id) T.piece.complex.space :=
    T.piece.isPLOn_comp hid (mapsTo_id _)
  have hmaps : MapsTo (T.piece.map ∘ id) T.piece.complex.space (u '' P) :=
    fun x hx => hNP (T.piece.bijOn.mapsTo hx)
  have hpa : IsPiecewiseAffineOn (Function.invFunOn u P ∘ T.piece.map ∘ id)
      T.piece.complex.space :=
    isPLOn_iff_isPiecewiseAffineOn.mp
      (IsPLOn.comp_of_mapsTo (hu.isPLOn_inverse hu.injOn.leftInvOn_invFunOn) hmap hmaps)
  have hsec : ∀ z ∈ u '' P, u (Function.invFunOn u P z) = z := fun z hz =>
    hu.injOn.bijOn_image.invOn_invFunOn.2 hz
  have hinj : InjOn (Function.invFunOn u P ∘ T.piece.map ∘ id) T.piece.complex.space := by
    intro x hx y hy hxy
    refine T.piece.bijOn.injOn hx hy ?_
    have hx' := hsec _ (hmaps hx)
    have hy' := hsec _ (hmaps hy)
    simp only [Function.comp_apply, id] at hxy hx' hy'
    rw [← hx', ← hy', hxy]
  have himg : (Function.invFunOn u P ∘ T.piece.map ∘ id) '' T.piece.complex.space =
      Function.invFunOn u P '' N := by
    rw [image_comp, image_comp, image_id, T.piece.bijOn.image_eq]
  have hpoly := T.piece.isPolyhedron_space.image_of_isPiecewiseAffineOn hpa hinj
  obtain ⟨K, hKfin, hKspace⟩ := (himg ▸ hpoly).exists_simplicialComplex
  let _ : Finite K.faces := hKfin.to_subtype
  refine ⟨K, hKfin, hKspace,
    hT.of_isPLHomeomorphOn (f := Function.invFunOn u P ∘ T.piece.map ∘ id) ?_⟩
  rw [hKspace, ← himg]
  exact isPLHomeomorphOn_of_isPiecewiseAffineOn_of_bijOn T.piece.isPolyhedron_space hpa
    hinj.bijOn_image

open Classical in
theorem IsPLHomeomorphInto.exists_bicollar_invFunOn_image
    {M : Type*} [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
    {P : Set (EuclideanSpace ℝ (Fin 3))} {u : EuclideanSpace ℝ (Fin 3) → M}
    (hu : IsPLHomeomorphInto 3 u P) (hP : IsPLBall 3 P) {N O : Set M}
    (hN : IsPolyhedralManifoldWithBoundary (n := 3) 3 N)
    (hO : IsOpen O) (hNO : N ⊆ O) (hOP : O ⊆ u '' P) :
    ∃ (W : Set (EuclideanSpace ℝ (Fin 3)))
        (ρ : EuclideanSpace ℝ (Fin 3) × ℝ → EuclideanSpace ℝ (Fin 3)),
      IsPolyhedron W ∧ W ⊆ interior P ∩ u ⁻¹' O ∧
      W ∈ 𝓝ˢ[P] (frontier (Function.invFunOn u P '' N)) ∧
      IsPLHomeomorphOn ρ ((frontier (Function.invFunOn u P '' N)) ×ˢ Icc (-1 : ℝ) 1) W ∧
      ∀ x ∈ frontier (Function.invFunOn u P '' N), ρ (x, 0) = x := by
  let _ : DecidableEq (EuclideanSpace ℝ (Fin 3)) := Classical.decEq _
  obtain ⟨K, hKfin, hKspace⟩ := hP.isPolyhedron.exists_simplicialComplex
  let _ : Finite K.faces := hKfin.to_subtype
  have hK : IsCombinatorialManifoldWithBoundary 3 K :=
    (hKspace.symm ▸ hP).isCombinatorialManifoldWithBoundary
  obtain ⟨A, hAfin, hAspace, hA⟩ := hu.exists_simplicialComplex_invFunOn_image hN
    (hNO.trans hOP)
  let _ : Finite A.faces := hAfin.to_subtype
  have hNint : N ⊆ interior (u '' P) :=
    hNO.trans (interior_maximal hOP hO)
  have hAint : A.space ⊆ interior P := by
    rw [hAspace]
    rintro _ ⟨y, hy, rfl⟩
    obtain ⟨x, hx, hxy⟩ := hu.image_interior.symm.subset (hNint hy)
    rw [← hxy, hu.injOn.leftInvOn_invFunOn (interior_subset hx)]
    exact hx
  have hAK : A.space ⊆ K.space := hAint.trans (interior_subset.trans hKspace.symm.subset)
  have hAdis : Disjoint A.space (boundaryComplex 3 K).space := by
    rw [← frontier_space_eq_boundaryComplex_space hK, hKspace]
    exact disjoint_interior_frontier.mono_left hAint
  let L := boundaryComplex 3 A
  let _ : Finite L.faces := (boundaryComplex_faces_finite 3 A).to_subtype
  have hL : IsCombinatorialManifold 2 L := isCombinatorialManifold_boundaryComplex A hA
  have hLA : L.space ⊆ A.space := boundaryComplex_space_subset 3 A
  have htwo := hK.isTwoSided_boundaryComplex K A hA hAK hAdis
  let V := interior P ∩ u ⁻¹' O
  have hV : IsOpen V :=
    (hu.continuousOn.mono interior_subset).isOpen_inter_preimage isOpen_interior hO
  have hLV : L.space ⊆ V := by
    intro x hx
    refine ⟨hAint (hLA hx), ?_⟩
    obtain ⟨y, hy, hxy⟩ := hAspace.subset (hLA hx)
    rw [← hxy]
    change u (Function.invFunOn u P y) ∈ O
    rw [hu.injOn.bijOn_image.invOn_invFunOn.2 (hOP (hNO hy))]
    exact hNO hy
  have hVnhds : V ∈ 𝓝ˢ[K.space] L.space :=
    Filter.mem_inf_of_left (hV.mem_nhdsSet.mpr hLV)
  obtain ⟨W, ρ, hW, -, hWV, hWnhds, hρ, hcenter⟩ :=
    hK.exists_bicollar hL (hLA.trans hAK) (hAdis.mono_left hLA) htwo hVnhds
  have hLspace : L.space = frontier (Function.invFunOn u P '' N) := by
    rw [← hAspace, frontier_space_eq_boundaryComplex_space hA]
  rw [hKspace, hLspace] at hWnhds
  rw [hLspace] at hρ hcenter
  exact ⟨W, ρ, hW, hWV, hWnhds, hρ, hcenter⟩

universe u

variable {Ea : Type} [NormedAddCommGroup Ea] [NormedSpace ℝ Ea]
  {M₁ M₂ : Type u} [TopologicalSpace M₁] [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M₁]
  [MetricSpace M₂] [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M₂]
  {U : Set M₁} {h : M₁ → M₂} {𝒦 𝒦' : LocallyFinitePLPieceIn Ea 3 M₁ U}
  {src : Section34CutLabelOf 𝒦 𝒦' → Set M₁}
  {Q : Section34VertexIndex 𝒦 𝒦' → Set M₂}
  {Cp CpBd Cc CcBd Kcore : Section34VertexIndex 𝒦 𝒦' → Set M₁}
  {ε : Section34VertexIndex 𝒦 𝒦' → ℝ}
  {ends : Section34EdgeIndex 𝒦 𝒦' →
    Section34VertexIndex 𝒦 𝒦' × Section34VertexIndex 𝒦 𝒦'}
  {Sn Tn Aa Ab₀ Ab₁ Bb Bb₀ Bb₁ Bc Bc₀ Bc₁ : Section34EdgeIndex 𝒦 𝒦' → Set M₁}

theorem exists_section34_inner_tube_bicollar
    (hprep : Section34VertexPreparation U 𝒦 𝒦' h src Q ends Cp CpBd Cc CcBd Kcore Sn Tn Aa Ab₀ Ab₁
      Bb Bb₀ Bb₁ Bc Bc₀ Bc₁ ε) (e : Section34EdgeIndex 𝒦 𝒦') :
    ∃ (P : Set (EuclideanSpace ℝ (Fin 3))) (u : EuclideanSpace ℝ (Fin 3) → M₁)
        (W : Set (EuclideanSpace ℝ (Fin 3)))
        (ρ : EuclideanSpace ℝ (Fin 3) × ℝ → EuclideanSpace ℝ (Fin 3)),
      IsPLBall 3 P ∧ IsPLHomeomorphInto 3 u P ∧ Cc (ends e).1 = u '' P ∧
      IsPolyhedralManifoldWithBoundary (n := 3) 3 (Tn e) ∧ IsPolyhedron W ∧
      W ⊆ interior P ∩ u ⁻¹' interior (Sn e) ∧
      W ∈ 𝓝ˢ[P] (frontier (Function.invFunOn u P '' Tn e)) ∧
      IsPLHomeomorphOn ρ
        ((frontier (Function.invFunOn u P '' Tn e)) ×ˢ Icc (-1 : ℝ) 1) W ∧
      ∀ x ∈ frontier (Function.invFunOn u P '' Tn e), ρ (x, 0) = x := by
  obtain ⟨-, hcell, -, -, -, -, -, -, -, -, hreg, htor, hSnCc, -⟩ := hprep
  have hcompact : IsCompact (Tn e) := by
    obtain ⟨f⟩ := (htor e).2.2.1
    exact isCompact_iff_compactSpace.mpr f.symm.compactSpace
  have hloc := (hreg e).2.isLocallyFinitePolyhedralManifoldWithBoundary
  have hN := hloc.isPolyhedralManifoldWithBoundary hcompact
  obtain ⟨P, r, u, hr, hu, hCc, -⟩ := hcell (ends e).1
  have hP : IsPLBall 3 P := ⟨r, hr⟩
  have hOP : interior (Sn e) ⊆ u '' P :=
    interior_subset.trans ((hSnCc e (ends e).1 (Or.inl rfl)).trans hCc.subset)
  obtain ⟨W, ρ, hW, hWV, hWnhds, hρ, hcenter⟩ :=
    hu.exists_bicollar_invFunOn_image hP hN isOpen_interior (htor e).1 hOP
  exact ⟨P, u, W, ρ, hP, hu, hCc, hN, hW, hWV, hWnhds, hρ, hcenter⟩

end DifferentialGeometry.Topology.PiecewiseLinear
