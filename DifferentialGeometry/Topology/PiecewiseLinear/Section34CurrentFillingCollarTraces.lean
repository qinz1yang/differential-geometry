import DifferentialGeometry.Topology.PiecewiseLinear.Section34CurrentFillingBoundaryCollar
import DifferentialGeometry.Topology.PiecewiseLinear.Section34CurrentCollarSheetLocalization

open Set Topology

namespace DifferentialGeometry.Topology.PiecewiseLinear

theorem exists_filling_collar_traces_of_cell_contacts
    {M : Type*} [MetricSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
    {A As B Bs D F J₀ J₁ S : Set M}
    (hcellA : IsPLCellOn 3 A As) (hcellB : IsPLCellOn 3 B Bs)
    {P : Set (EuclideanSpace ℝ (Fin 3))} {u : EuclideanSpace ℝ (Fin 3) → M}
    (hP : IsPLBall 3 P) (hu : IsPLHomeomorphInto 3 u P)
    (R : Geometry.SimplicialComplex ℝ (EuclideanSpace ℝ (Fin 3))) [Finite R.faces]
    (hR : IsCombinatorialManifoldWithBoundary 3 R)
    (hsolid : IsTopologicalSolidTorus R.space) (hRint : R.space ⊆ interior P)
    (hRS : u '' R.space ⊆ interior S)
    (hfront : u '' frontier R.space = D ∪ F)
    (hcontactA : As ∩ u '' R.space = F)
    (hcontactB : Bs ∩ u '' R.space = D)
    (hJDF : J₀ ∪ J₁ ⊆ D ∩ F)
    (hF : IsAnnulusOn F J₀ J₁) (hD : IsAnnulusOn D J₀ J₁)
    (hDF : D ∩ F = J₀ ∪ J₁)
    {C : Fin 2 → Set (EuclideanSpace ℝ (Fin 3))}
    {f : Fin 2 → (ℝ × ℝ) × ℝ → EuclideanSpace ℝ (Fin 3)}
    (hC : ∀ k, IsPolyhedron (C k)) (hCP : ∀ k, C k ⊆ interior P)
    (hf : ∀ k, IsCylindricalDiagram (f k) spliceSquare (C k))
    (haxis : ∀ k, u '' (f k '' section34MarkedAxis) = ![J₀, J₁] k)
    (hfirst : ∀ k, u '' (f k '' (section34MarkedRibbon 0 ∪ section34MarkedRibbon 2)) =
      u '' C k ∩ As)
    (hsecond : ∀ k, u '' (f k '' (section34MarkedRibbon 1 ∪ section34MarkedRibbon 3)) =
      u '' C k ∩ Bs)
    (hpages : ∀ k, ∀ l : Fin 4, u '' (f k '' section34MarkedRibbon l) = u '' C k ∩
      ![As ∩ B,
        Bs ∩ A,
        As \ interior (B),
        Bs \ interior (A)] l)
    (hJC : ∀ k, ![J₀, J₁] k ⊆ interior (u '' C k))
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
      J = Function.invFunOn u P '' (J₀ ∪ J₁) ∧
      IsPolyhedron W ∧ W ⊆ interior P ∧ u '' W ⊆ interior S ∧
      IsPLHomeomorphOn ρ (frontier R.space ×ˢ Icc (0 : ℝ) c) W ∧
      (∀ x ∈ frontier R.space, ρ (x, 0) = x) ∧ W ∩ R.space = frontier R.space ∧
      MapsTo ρ (frontier R.space ×ˢ Ioc (0 : ℝ) c) (interior P \ R.space) ∧
      (∀ k, ∀ p ∈ section34CornerBase (a k) (b k), ∀ s ∈ Icc (0 : ℝ) 1,
        f k (p, s) ∈ L.space → ∀ t ∈ Icc (0 : ℝ) c,
          ρ (f k (p, s), t) = f k (section34CornerExteriorPush (a k) (b k) (p, t), s) ∧
          (u (ρ (f k (p, s), t)) ∈ As ↔
            p.2 = (if b k then t / 2 else -t / 2)) ∧
          (u (ρ (f k (p, s), t)) ∈ Bs ↔
            p.1 = (if a k then t / 2 else -t / 2))) ∧
      ∀ x ∈ frontier R.space, ∀ t ∈ Ioc (0 : ℝ) c,
        (u (ρ (x, t)) ∈ As ↔
          ∃ k p s, p ∈ section34CornerBase (a k) (b k) ∧ s ∈ Icc (0 : ℝ) 1 ∧
            x = f k (p, s) ∧ x ∈ L.space ∧ p.2 = (if b k then t / 2 else -t / 2)) ∧
        (u (ρ (x, t)) ∈ Bs ↔
          ∃ k p s, p ∈ section34CornerBase (a k) (b k) ∧ s ∈ Icc (0 : ℝ) 1 ∧
            x = f k (p, s) ∧ x ∈ L.space ∧ p.1 = (if a k then t / 2 else -t / 2)) := by
  obtain ⟨c, L, W, ρ, hc, hc1, hLfin, hL, hLB, hJL, hLnhds, hJid, hW, hWP, huW,
      hρ, hzero, htrace, hpositive, hread⟩ :=
    exists_filling_boundary_exterior_collar_of_cell_contacts hcellA hcellB hP hu R
      hR hsolid hRint hRS hfront hcontactA hcontactB hJDF hC hCP hf haxis hfirst hsecond
      hpages hJC hends a b hquad hdis
  have hRP : R.space ⊆ P := hRint.trans interior_subset
  have hRc := (isPolyhedron_space R).isCompact
  have hfrontP : frontier R.space ⊆ P := hRc.isClosed.frontier_subset.trans hRP
  have hJpre : frontier R.space ∩ u ⁻¹' (J₀ ∪ J₁) ⊆
      (f 0 '' section34MarkedAxis) ∪ (f 1 '' section34MarkedAxis) := by
    rw [hJid]
    intro x hx
    exact ⟨u x, hx.2, hu.injOn.leftInvOn_invFunOn (hfrontP hx.1)⟩
  have hLn : L.space ∈ 𝓝ˢ[frontier R.space]
      (frontier R.space ∩ u ⁻¹' (J₀ ∪ J₁)) := by
    rw [nhdsSetWithin, Filter.mem_inf_principal, mem_nhdsSet_iff_forall]
    intro x hx
    exact Filter.mem_inf_principal.mp (hLnhds x (hJpre hx))
  obtain ⟨d, hd, hdc, hlocal⟩ :=
    exists_collar_sheet_localization_of_annular_contacts hcellA hcellB hF hD hDF hu hRc hRP
      hfront hcontactA hcontactB hLn hc
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
