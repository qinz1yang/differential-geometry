import DifferentialGeometry.Topology.PiecewiseLinear.Section34ActualFillingBoundaryCollar
import DifferentialGeometry.Topology.PiecewiseLinear.Section34CollarSheetLocalization

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

theorem exists_section34_actual_filling_collar_traces
    (hprep : Section34VertexPreparation U 𝒦 𝒦' h src Q ends Cp CpBd Cc CcBd Kcore Sn Tn Aa Ab₀ Ab₁
      Bb Bb₀ Bb₁ Bc Bc₀ Bc₁ ε)
    (hpack : Section34PiercingConditions U 𝒦 𝒦' h Q ends Cp CpBd Cc Sn Tn Aa Ab₀ Ab₁ Bb Bb₀
      Bb₁ Sp Tp cnt Pg G) (e : Section34EdgeIndex 𝒦 𝒦')
    {P : Set (EuclideanSpace ℝ (Fin 3))} {u : EuclideanSpace ℝ (Fin 3) → M₂}
    (hP : IsPLBall 3 P) (hu : IsPLHomeomorphInto 3 u P)
    (hmodel : u '' P = G (ends e).1 '' Cc (ends e).1)
    (R : Geometry.SimplicialComplex ℝ (EuclideanSpace ℝ (Fin 3))) [Finite R.faces]
    (hR : IsCombinatorialManifoldWithBoundary 3 R)
    (hsolid : IsTopologicalSolidTorus R.space) (hRP : R.space ⊆ P)
    (hRT : u '' R.space ⊆ Tp e) {D F : Set M₂}
    (hfront : u '' frontier R.space = D ∪ F)
    (hcontactA : G (ends e).1 '' CpBd (ends e).1 ∩ u '' R.space = F)
    (hcontactB : G (ends e).2 '' CpBd (ends e).2 ∩ u '' R.space = D)
    {i j : ℕ} (hJDF : Pg e i ∪ Pg e j ⊆ D ∩ F)
    (hfill : Section34FaceAlignedBandFilling
      (G (ends e).1 '' Cc (ends e).1) (G (ends e).1 '' Cp (ends e).1)
      (G (ends e).1 '' CpBd (ends e).1) (G (ends e).2 '' CpBd (ends e).2) (Tp e) D F
      (Pg e i) (Pg e j))
    {C : Fin 2 → Set (EuclideanSpace ℝ (Fin 3))}
    {f : Fin 2 → (ℝ × ℝ) × ℝ → EuclideanSpace ℝ (Fin 3)}
    (hC : ∀ k, IsPolyhedron (C k)) (hCP : ∀ k, C k ⊆ interior P)
    (hf : ∀ k, IsCylindricalDiagram (f k) spliceSquare (C k))
    (haxis : ∀ k, u '' (f k '' section34MarkedAxis) = ![Pg e i, Pg e j] k)
    (hfirst : ∀ k, u '' (f k '' (section34MarkedRibbon 0 ∪ section34MarkedRibbon 2)) =
      u '' C k ∩ G (ends e).1 '' CpBd (ends e).1)
    (hsecond : ∀ k, u '' (f k '' (section34MarkedRibbon 1 ∪ section34MarkedRibbon 3)) =
      u '' C k ∩ G (ends e).2 '' CpBd (ends e).2)
    (hpages : ∀ k, ∀ l : Fin 4, u '' (f k '' section34MarkedRibbon l) = u '' C k ∩
      ![G (ends e).1 '' CpBd (ends e).1 ∩ G (ends e).2 '' Cp (ends e).2,
        G (ends e).2 '' CpBd (ends e).2 ∩ G (ends e).1 '' Cp (ends e).1,
        G (ends e).1 '' CpBd (ends e).1 \ interior (G (ends e).2 '' Cp (ends e).2),
        G (ends e).2 '' CpBd (ends e).2 \ interior (G (ends e).1 '' Cp (ends e).1)] l)
    (hJC : ∀ k, ![Pg e i, Pg e j] k ⊆ interior (u '' C k))
    (hends : ∀ k, ∀ p ∈ spliceSquare, f k (p, 0) = f k (p, 1)) (a b : Fin 2 → Bool)
    (hquad : ∀ k, f k '' (section34CrossingQuadrant (a k) (b k) ×ˢ Icc (0 : ℝ) 1) =
      C k ∩ R.space) (hdis : Disjoint (C 0) (C 1)) :
    let J := (f 0 '' section34MarkedAxis) ∪ (f 1 '' section34MarkedAxis)
    let B := fun k => f k '' (section34CornerBase (a k) (b k) ×ˢ Icc (0 : ℝ) 1)
    ∃ (c : ℝ) (L : Geometry.SimplicialComplex ℝ (EuclideanSpace ℝ (Fin 3)))
      (W : Set (EuclideanSpace ℝ (Fin 3)))
      (ρ : EuclideanSpace ℝ (Fin 3) × ℝ → EuclideanSpace ℝ (Fin 3)),
      0 < c ∧ c ≤ 1 ∧ L.faces.Finite ∧ IsCombinatorialManifoldWithBoundary 2 L ∧
      L.space ⊆ frontier R.space ∩ (B 0 ∪ B 1) ∧ J ⊆ L.space ∧
      (∀ x ∈ J, L.space ∈ 𝓝[frontier R.space] x) ∧
      J = Function.invFunOn u P '' (Pg e i ∪ Pg e j) ∧
      IsPolyhedron W ∧ W ⊆ interior P ∧ u '' W ⊆ interior (Sp e) ∧
      IsPLHomeomorphOn ρ (frontier R.space ×ˢ Icc (0 : ℝ) c) W ∧
      (∀ x ∈ frontier R.space, ρ (x, 0) = x) ∧ W ∩ R.space = frontier R.space ∧
      MapsTo ρ (frontier R.space ×ˢ Ioc (0 : ℝ) c) (interior P \ R.space) ∧
      (∀ k, ∀ p ∈ section34CornerBase (a k) (b k), ∀ s ∈ Icc (0 : ℝ) 1,
        f k (p, s) ∈ L.space → ∀ t ∈ Icc (0 : ℝ) c,
          ρ (f k (p, s), t) = f k (section34CornerExteriorPush (a k) (b k) (p, t), s) ∧
          (u (ρ (f k (p, s), t)) ∈ G (ends e).1 '' CpBd (ends e).1 ↔
            p.2 = (if b k then t / 2 else -t / 2)) ∧
          (u (ρ (f k (p, s), t)) ∈ G (ends e).2 '' CpBd (ends e).2 ↔
            p.1 = (if a k then t / 2 else -t / 2))) ∧
      ∀ x ∈ frontier R.space, ∀ t ∈ Ioc (0 : ℝ) c,
        (u (ρ (x, t)) ∈ G (ends e).1 '' CpBd (ends e).1 ↔
          ∃ k p s, p ∈ section34CornerBase (a k) (b k) ∧ s ∈ Icc (0 : ℝ) 1 ∧
            x = f k (p, s) ∧ x ∈ L.space ∧ p.2 = (if b k then t / 2 else -t / 2)) ∧
        (u (ρ (x, t)) ∈ G (ends e).2 '' CpBd (ends e).2 ↔
          ∃ k p s, p ∈ section34CornerBase (a k) (b k) ∧ s ∈ Icc (0 : ℝ) 1 ∧
            x = f k (p, s) ∧ x ∈ L.space ∧ p.1 = (if a k then t / 2 else -t / 2)) := by
  obtain ⟨c, L, W, ρ, hc, hc1, hLfin, hL, hLB, hJL, hLnhds, hJid, hW, hWP, huW,
      hρ, hzero, htrace, hpositive, hread⟩ :=
    exists_section34_actual_filling_boundary_exterior_collar hprep hpack e hP hu hmodel R
      hR hsolid hRP hRT hfront hcontactA hcontactB hJDF hC hCP hf haxis hfirst hsecond
      hpages hJC hends a b hquad hdis
  have hRc := (isPolyhedron_space R).isCompact
  have hfrontP : frontier R.space ⊆ P := hRc.isClosed.frontier_subset.trans hRP
  have hJpre : frontier R.space ∩ u ⁻¹' (Pg e i ∪ Pg e j) ⊆
      (f 0 '' section34MarkedAxis) ∪ (f 1 '' section34MarkedAxis) := by
    rw [hJid]
    intro x hx
    exact ⟨u x, hx.2, hu.injOn.leftInvOn_invFunOn (hfrontP hx.1)⟩
  have hLn : L.space ∈ 𝓝ˢ[frontier R.space]
      (frontier R.space ∩ u ⁻¹' (Pg e i ∪ Pg e j)) := by
    rw [nhdsSetWithin, Filter.mem_inf_principal, mem_nhdsSet_iff_forall]
    intro x hx
    exact Filter.mem_inf_principal.mp (hLnhds x (hJpre hx))
  obtain ⟨d, hd, hdc, hlocal⟩ :=
    exists_section34_collar_sheet_localization hprep hpack e hfill hu hRc hRP hfront hLn hc
      hρ.isPiecewiseAffineOn.continuousOn
      (hρ.bijOn.mapsTo.mono_right (hWP.trans interior_subset)) hzero
      (fun z hz => (hpositive hz).2)
  let W' := ρ '' (frontier R.space ×ˢ Icc (0 : ℝ) d)
  have hsmall : frontier R.space ×ˢ Icc (0 : ℝ) d ⊆
      frontier R.space ×ˢ Icc (0 : ℝ) c :=
    prod_mono_right (Icc_subset_Icc le_rfl hdc)
  have hpoly : IsPolyhedron (frontier R.space ×ˢ Icc (0 : ℝ) d) :=
    (isPolyhedron_space R).frontier.prod isHPolytope_Icc.isPolyhedron
  have hρ' : IsPLHomeomorphOn ρ (frontier R.space ×ˢ Icc (0 : ℝ) d) W' :=
    hρ.restrict hpoly hsmall
  have hWW : W' ⊆ W := (image_mono hsmall).trans hρ.image_eq.subset
  have htrace' : W' ∩ R.space = frontier R.space := by
    refine Subset.antisymm ((inter_subset_inter_left _ hWW).trans htrace.subset) ?_
    intro x hx
    exact ⟨⟨(x, 0), ⟨hx, le_rfl, hd.le⟩, hzero x hx⟩, hRc.isClosed.frontier_subset hx⟩
  have hrepr : ∀ x ∈ L.space, ∃ k p s,
      p ∈ section34CornerBase (a k) (b k) ∧ s ∈ Icc (0 : ℝ) 1 ∧ x = f k (p, s) := by
    intro x hx
    rcases (hLB hx).2 with hx | hx
    · obtain ⟨⟨p, s⟩, ⟨hp, hs⟩, hps⟩ := hx
      exact ⟨0, p, s, hp, hs, hps.symm⟩
    · obtain ⟨⟨p, s⟩, ⟨hp, hs⟩, hps⟩ := hx
      exact ⟨1, p, s, hp, hs, hps.symm⟩
  refine ⟨d, L, W', ρ, hd, hdc.trans hc1, hLfin, hL, hLB, hJL, hLnhds, hJid,
    hρ'.isPiecewiseAffineOn.isPolyhedron_image hpoly, hWW.trans hWP,
    (image_mono hWW).trans huW, hρ', hzero, htrace', ?_, ?_, ?_⟩
  · intro z hz
    exact hpositive ⟨hz.1, hz.2.1, hz.2.2.trans hdc⟩
  · intro k p hp s hs hx t ht
    exact hread k p hp s hs hx t ⟨ht.1, ht.2.trans hdc⟩
  · intro x hx t ht
    have ht' : t ∈ Icc (0 : ℝ) c := ⟨ht.1.le, ht.2.trans hdc⟩
    constructor
    · constructor
      · intro hy
        have hxL := hlocal x hx t ht (Or.inl hy)
        obtain ⟨k, p, s, hp, hs, hps⟩ := hrepr x hxL
        refine ⟨k, p, s, hp, hs, hps, hxL, ?_⟩
        rw [hps] at hy hxL
        exact (hread k p hp s hs hxL t ht').2.1.mp hy
      · rintro ⟨k, p, s, hp, hs, hps, hxL, hp₂⟩
        rw [hps] at hxL ⊢
        exact (hread k p hp s hs hxL t ht').2.1.mpr hp₂
    · constructor
      · intro hy
        have hxL := hlocal x hx t ht (Or.inr hy)
        obtain ⟨k, p, s, hp, hs, hps⟩ := hrepr x hxL
        refine ⟨k, p, s, hp, hs, hps, hxL, ?_⟩
        rw [hps] at hy hxL
        exact (hread k p hp s hs hxL t ht').2.2.mp hy
      · rintro ⟨k, p, s, hp, hs, hps, hxL, hp₁⟩
        rw [hps] at hxL ⊢
        exact (hread k p hp s hs hxL t ht').2.2.mpr hp₁

end DifferentialGeometry.Topology.PiecewiseLinear
