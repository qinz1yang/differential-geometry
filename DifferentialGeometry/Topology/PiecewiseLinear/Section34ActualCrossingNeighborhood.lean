import DifferentialGeometry.Topology.PiecewiseLinear.Section34ActualCrossingSurfaces
import DifferentialGeometry.Topology.PiecewiseLinear.Section34ActualCrossingInModel
import DifferentialGeometry.Topology.PiecewiseLinear.Section34InteriorCrossingNeighborhood
import DifferentialGeometry.Topology.PiecewiseLinear.Section34InteriorFillingQuadrantRegions

open Set Topology

namespace DifferentialGeometry.Topology.PiecewiseLinear

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

open Classical in
theorem exists_section34_actual_crossing_neighborhood_in_model
    (hprep : Section34VertexPreparation U 𝒦 𝒦' h src Q ends Cp CpBd Cc CcBd Kcore Sn Tn Aa Ab₀ Ab₁
      Bb Bb₀ Bb₁ Bc Bc₀ Bc₁ ε)
    (hpack : Section34PiercingConditions U 𝒦 𝒦' h Q ends Cp CpBd Cc Sn Tn Aa Ab₀ Ab₁ Bb Bb₀
      Bb₁ Sp Tp cnt Pg G) (e : Section34EdgeIndex 𝒦 𝒦') {i : ℕ} (hi : i < cnt e)
    {P : Set (EuclideanSpace ℝ (Fin 3))} {u : EuclideanSpace ℝ (Fin 3) → M₂}
    (hP : IsPLBall 3 P) (hu : IsPLHomeomorphInto 3 u P)
    (hmodel : u '' P = G (ends e).1 '' Cc (ends e).1)
    {O : Set M₂} (hO : IsOpen O) (hJO : Pg e i ⊆ O) :
    ∃ (C : Set (EuclideanSpace ℝ (Fin 3)))
      (f : (ℝ × ℝ) × ℝ → EuclideanSpace ℝ (Fin 3)),
      IsPolyhedron C ∧ C ⊆ interior P ∧ IsCylindricalDiagram f spliceSquare C ∧
      (∀ x ∈ spliceSquare, f (x, 0) = f (x, 1)) ∧
      u '' (f '' section34MarkedAxis) = Pg e i ∧
      u '' (f '' (section34MarkedRibbon 0 ∪ section34MarkedRibbon 2)) =
        u '' C ∩ G (ends e).1 '' CpBd (ends e).1 ∧
      u '' (f '' (section34MarkedRibbon 1 ∪ section34MarkedRibbon 3)) =
        u '' C ∩ G (ends e).2 '' CpBd (ends e).2 ∧
      (∀ j : Fin 4, u '' (f '' section34MarkedRibbon j) = u '' C ∩
        ![G (ends e).1 '' CpBd (ends e).1 ∩ G (ends e).2 '' Cp (ends e).2,
          G (ends e).2 '' CpBd (ends e).2 ∩ G (ends e).1 '' Cp (ends e).1,
          G (ends e).1 '' CpBd (ends e).1 \ interior (G (ends e).2 '' Cp (ends e).2),
          G (ends e).2 '' CpBd (ends e).2 \ interior (G (ends e).1 '' Cp (ends e).1)] j) ∧
      u '' C ⊆ O ∧ Pg e i ⊆ interior (u '' C) := by
  let _ : DecidableEq (EuclideanSpace ℝ (Fin 3)) := Classical.decEq _
  obtain ⟨K₀, K₁, N, hfin₀, hfin₁, hK₀, hK₁, hor₀, hor₁,
      -, -, -, -, hJ, hJK, hBd₀, hBd₁, hN, hJN, hNP, hNX, hNY, htrace⟩ :=
    exists_section34_actual_crossing_surfaces_in_model hprep hpack e hi hu hmodel
  let _ : Finite K₀.faces := hfin₀.to_subtype
  let _ : Finite K₁.faces := hfin₁.to_subtype
  let τ := Function.invFunOn u P
  let J := τ '' Pg e i
  let A := G (ends e).1 '' Cp (ends e).1
  let B := G (ends e).2 '' Cp (ends e).2
  let X := closure (interior (P ∩ u ⁻¹' A))
  let Y := closure (interior (P ∩ u ⁻¹' B))
  obtain ⟨-, -, -, -, hCp, -⟩ := id hprep
  obtain ⟨-, -, -, -, -, -, -, -, -, -, hGp, -⟩ := id hpack
  have hcellA := (hCp (ends e).1).image (hGp (ends e).1)
  have hcellB := (hCp (ends e).2).image (hGp (ends e).2)
  have hregA : closure (interior A) = A := by
    rw [← hcellA.sdiff_boundary_eq_interior]
    exact hcellA.closure_sdiff_boundary
  have hregB : closure (interior B) = B := by
    rw [← hcellB.sdiff_boundary_eq_interior]
    exact hcellB.closure_sdiff_boundary
  have hright : RightInvOn τ u (u '' P) := hu.injOn.bijOn_image.invOn_invFunOn.2
  have hJP : Pg e i ⊆ u '' P := by
    obtain ⟨hnear, hBint, hJboth⟩ :=
      section34_piercing_circle_annulus_neighborhood hprep hpack e hi
    obtain ⟨W, -, hJW, hWB⟩ := mem_nhdsSetWithin.mp hnear
    intro y hy
    exact hmodel.symm ▸ interior_subset (hBint (hWB ⟨hJW hy, (hJboth hy).2⟩))
  have hJimage : u '' J = Pg e i := by
    apply Subset.antisymm
    · rintro _ ⟨x, ⟨y, hy, rfl⟩, rfl⟩
      rw [hright (hJP hy)]
      exact hy
    · intro y hy
      exact ⟨τ y, ⟨y, hy, rfl⟩, hright (hJP hy)⟩
  let V := N ∩ u ⁻¹' O
  have hV : IsOpen V :=
    (hu.continuousOn.mono (hNP.trans interior_subset)).isOpen_inter_preimage hN hO
  have hJV : J ⊆ V := fun x hx => ⟨hJN hx, hJO (hJimage.subset ⟨x, hx, rfl⟩)⟩
  have hVP : V ⊆ interior P := inter_subset_left.trans hNP
  have hAX (x : EuclideanSpace ℝ (Fin 3)) (hx : x ∈ interior P) :
      x ∈ frontier X ↔ u x ∈ G (ends e).1 '' CpBd (ends e).1 := by
    rw [hu.regularized_clipped_region_frontier hregA hx |>.1,
      ← hcellA.boundary_eq_frontier]
  have hBY (x : EuclideanSpace ℝ (Fin 3)) (hx : x ∈ interior P) :
      x ∈ frontier Y ↔ u x ∈ G (ends e).2 '' CpBd (ends e).2 := by
    rw [hu.regularized_clipped_region_frontier hregB hx |>.1,
      ← hcellB.boundary_eq_frontier]
  have hVX : V ∩ K₀.space = V ∩ frontier X := by
    ext x
    constructor
    · exact fun hx => ⟨hx.1, (hAX x (hVP hx.1)).mpr (hNX.subset ⟨hx.1.1, hx.2⟩).2⟩
    · exact fun hx => ⟨hx.1, (hNX.symm.subset
        ⟨hx.1.1, (hAX x (hVP hx.1)).mp hx.2⟩).2⟩
  have hVY : V ∩ K₁.space = V ∩ frontier Y := by
    ext x
    constructor
    · exact fun hx => ⟨hx.1, (hBY x (hVP hx.1)).mpr (hNY.subset ⟨hx.1.1, hx.2⟩).2⟩
    · exact fun hx => ⟨hx.1, (hNY.symm.subset
        ⟨hx.1.1, (hBY x (hVP hx.1)).mp hx.2⟩).2⟩
  have hcross : ∀ x ∈ J, HasPLCrossingAt K₀.space K₁.space x := by
    intro x hx
    have hxN := hJN hx
    have hc := section34_hasPLCrossingAt_boundary_preimages hprep hpack e hu (hNP hxN)
      ⟨(hNX.subset ⟨hxN, (hJK hx).1⟩).2, (hNY.subset ⟨hxN, (hJK hx).2⟩).2⟩
    apply hc.congr
    · filter_upwards [hN.mem_nhds hxN] with y hy
      exact ⟨fun hm => (hNX.symm.subset ⟨hy, hm⟩).2,
        fun hm => (hNX.subset ⟨hy, hm⟩).2⟩
    · filter_upwards [hN.mem_nhds hxN] with y hy
      exact ⟨fun hm => (hNY.symm.subset ⟨hy, hm⟩).2,
        fun hm => (hNY.subset ⟨hy, hm⟩).2⟩
  obtain ⟨K, hKfin, hKP⟩ := hP.isPolyhedron.exists_simplicialComplex
  let _ : Finite K.faces := hKfin.to_subtype
  have hK : IsPLBall 3 K.space := hKP.symm ▸ hP
  obtain ⟨R, f, -, hRfin, -, hf, hends, haxis, hfirst, hsecond, hpages, hCV, hJint⟩ :=
    exists_interior_crossing_circle_neighborhood K K₀ K₁
      hK.isCombinatorialManifoldWithBoundary (by simp)
      hK₀.isCombinatorialManifoldWithBoundary hK₁ hor₀ hor₁ isClosed_closure isClosed_closure
      closure_interior_idem closure_interior_idem hVX hVY hJ
      (hJK.trans inter_subset_left) (hJK.trans inter_subset_right) hBd₀ hBd₁
      (by rw [hKP]; exact hJN.trans hNP) hV hJV
      (fun _ hx => htrace ⟨hx.1, hx.2.1⟩) hcross
  let _ : Finite R.faces := hRfin.to_subtype
  let C := (derivedNeighborhood R (PiecewiseLinear.restrict R J)).space
  let _ : Finite (derivedNeighborhood R (PiecewiseLinear.restrict R J)).faces :=
    (derivedNeighborhood_faces_finite R (PiecewiseLinear.restrict R J)).to_subtype
  have hCP : C ⊆ interior P := hCV.trans hVP
  have himage (S : Set (EuclideanSpace ℝ (Fin 3))) (T : Set M₂)
      (hST : ∀ x ∈ C, x ∈ S ↔ u x ∈ T) : u '' (C ∩ S) = u '' C ∩ T := by
    apply Subset.antisymm
    · rintro _ ⟨x, ⟨hxC, hxS⟩, rfl⟩
      exact ⟨⟨x, hxC, rfl⟩, (hST x hxC).mp hxS⟩
    · rintro _ ⟨⟨x, hxC, rfl⟩, hxT⟩
      exact ⟨x, ⟨hxC, (hST x hxC).mpr hxT⟩, rfl⟩
  have hXA (x : EuclideanSpace ℝ (Fin 3)) (hx : x ∈ C) : x ∈ X ↔ u x ∈ A :=
    (hu.regularized_clipped_region hP.isPolyhedron.isClosed hcellA.isCompact.isClosed hregA).2.2.2
      x (hCP hx)
  have hYB (x : EuclideanSpace ℝ (Fin 3)) (hx : x ∈ C) : x ∈ Y ↔ u x ∈ B :=
    (hu.regularized_clipped_region hP.isPolyhedron.isClosed hcellB.isCompact.isClosed hregB).2.2.2
      x (hCP hx)
  refine ⟨C, f, isPolyhedron_space _, hCP, hf, hends,
    (congrArg (u '' ·) haxis).trans hJimage, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hfirst]
    exact himage _ _ fun x hx => hAX x (hCP hx)
  · rw [hsecond]
    exact himage _ _ fun x hx => hBY x (hCP hx)
  · intro j
    rw [hpages j]
    apply himage
    intro x hx
    fin_cases j
    · exact (hAX x (hCP hx)).and (hYB x hx)
    · exact (hBY x (hCP hx)).and (hXA x hx)
    · exact (hAX x (hCP hx)).and
        (hu.regularized_clipped_region_frontier hregB (hCP hx)).2.not
    · exact (hBY x (hCP hx)).and
        (hu.regularized_clipped_region_frontier hregA (hCP hx)).2.not
  · rintro _ ⟨x, hx, rfl⟩
    exact (hCV hx).2
  · rw [← hJimage, ← hu.image_interior_of_isCompact_subset_interior
      (isPolyhedron_space _).isCompact hCP]
    exact image_mono hJint

open Classical in
theorem exists_section34_actual_crossing_neighborhood
    (hprep : Section34VertexPreparation U 𝒦 𝒦' h src Q ends Cp CpBd Cc CcBd Kcore Sn Tn Aa Ab₀ Ab₁
      Bb Bb₀ Bb₁ Bc Bc₀ Bc₁ ε)
    (hpack : Section34PiercingConditions U 𝒦 𝒦' h Q ends Cp CpBd Cc Sn Tn Aa Ab₀ Ab₁ Bb Bb₀
      Bb₁ Sp Tp cnt Pg G) (e : Section34EdgeIndex 𝒦 𝒦') {i : ℕ} (hi : i < cnt e)
    {O : Set M₂} (hO : IsOpen O) (hJO : Pg e i ⊆ O) :
    ∃ (P C : Set (EuclideanSpace ℝ (Fin 3))) (u : EuclideanSpace ℝ (Fin 3) → M₂)
      (f : (ℝ × ℝ) × ℝ → EuclideanSpace ℝ (Fin 3)),
      IsPLBall 3 P ∧ IsPLHomeomorphInto 3 u P ∧ u '' P = G (ends e).1 '' Cc (ends e).1 ∧
      IsPolyhedron C ∧ C ⊆ interior P ∧ IsCylindricalDiagram f spliceSquare C ∧
      (∀ x ∈ spliceSquare, f (x, 0) = f (x, 1)) ∧
      u '' (f '' section34MarkedAxis) = Pg e i ∧
      u '' (f '' (section34MarkedRibbon 0 ∪ section34MarkedRibbon 2)) =
        u '' C ∩ G (ends e).1 '' CpBd (ends e).1 ∧
      u '' (f '' (section34MarkedRibbon 1 ∪ section34MarkedRibbon 3)) =
        u '' C ∩ G (ends e).2 '' CpBd (ends e).2 ∧
      (∀ j : Fin 4, u '' (f '' section34MarkedRibbon j) = u '' C ∩
        ![G (ends e).1 '' CpBd (ends e).1 ∩ G (ends e).2 '' Cp (ends e).2,
          G (ends e).2 '' CpBd (ends e).2 ∩ G (ends e).1 '' Cp (ends e).1,
          G (ends e).1 '' CpBd (ends e).1 \ interior (G (ends e).2 '' Cp (ends e).2),
          G (ends e).2 '' CpBd (ends e).2 \ interior (G (ends e).1 '' Cp (ends e).1)] j) ∧
      u '' C ⊆ O ∧ Pg e i ⊆ interior (u '' C) := by
  obtain ⟨-, hCc, -⟩ := id hprep
  obtain ⟨hG, -⟩ := id hpack
  obtain ⟨P, r, u, hr, hu, hmodel, -⟩ := (hCc (ends e).1).image (hG (ends e).1)
  obtain ⟨C, f, hC⟩ := exists_section34_actual_crossing_neighborhood_in_model
    hprep hpack e hi ⟨r, hr⟩ hu hmodel.symm hO hJO
  exact ⟨P, C, u, f, ⟨r, hr⟩, hu, hmodel.symm, hC⟩

end DifferentialGeometry.Topology.PiecewiseLinear
