import DifferentialGeometry.Topology.PiecewiseLinear.DerivedNeighborhoodSurgery
import DifferentialGeometry.Topology.PiecewiseLinear.Section34AnnularCollarExtensionAdaptation
import DifferentialGeometry.Topology.PiecewiseLinear.Section34AnnularCollarExtensionSupport

open Set Topology

namespace DifferentialGeometry.Topology.PiecewiseLinear

open Classical in
theorem IsCombinatorialManifoldWithBoundary.exists_adapted_polyhedral_collar_base
    {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    (H : Geometry.SimplicialComplex ℝ E) [Finite H.faces]
    (hH : IsCombinatorialManifoldWithBoundary 2 H) {Z P : Set E}
    (hZ : IsPolyhedron Z) (hZH : Z ⊆ H.space) (hP : P ∈ 𝓝ˢ[H.space] Z) :
    ∃ H' L : Geometry.SimplicialComplex ℝ E, IsSubdivision H' H ∧
      H'.faces.Finite ∧ L.faces.Finite ∧ IsCombinatorialManifoldWithBoundary 2 L ∧
      L.space ⊆ H.space ∩ P ∧ (∀ x ∈ Z, L.space ∈ 𝓝[H.space] x) ∧
      ∃ d : Finset {v : E // ({v} : Finset E) ∈ H'.faces},
        L.space = section34AnnularCollarBase H' d := by
  obtain ⟨O, hO, hZO, hOP⟩ := mem_nhdsSetWithin.mp hP
  obtain ⟨δ, hδ, hthick⟩ := hZ.isCompact.exists_cthickening_subset_open hO hZO
  obtain ⟨R, hRH, hRfin, hΓspace, -, hdiam⟩ :=
    exists_isSubdivision_restrict_space_diam_lt H hZ hZH hZ hZH hδ
  let _ : Finite R.faces := hRfin.to_subtype
  let Γ := PiecewiseLinear.restrict R Z
  let _ : Finite Γ.faces := (restrict_faces_finite R Z).to_subtype
  have hΓR : Γ.faces ⊆ R.faces := restrict_faces_subset R Z
  let L := PiecewiseLinear.derivedNeighborhood R Γ
  have hLH : L.space ⊆ H.space := (derivedNeighborhood_space_subset R Γ).trans hRH.space_eq.subset
  have hLO : L.space ⊆ O := by
    have h := derivedNeighborhood_space_subset_cthickening (K := R) (L := Γ) hdiam
    rw [show Γ.space = Z from hΓspace] at h
    exact h.trans hthick
  refine ⟨PiecewiseLinear.barycentricSubdivision R, L,
    (barycentricSubdivision_isSubdivision R).trans hRH,
    Set.toFinite _, derivedNeighborhood_faces_finite R Γ,
    (hH.of_isSubdivision hRH).derivedNeighborhood Γ,
    fun x hx => ⟨hLH hx, hOP ⟨hLO hx, hLH hx⟩⟩, ?_, ?_⟩
  · intro x hx
    rw [← hRH.space_eq]
    exact derivedNeighborhood_mem_nhdsWithin hΓR (hΓspace.symm.subset hx)
  · exact exists_selected_dual_cells_of_derived_neighborhood R Γ hΓR


open Classical in
theorem exists_relative_collar_extension_of_polyhedral_mark
    {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    (K H : Geometry.SimplicialComplex ℝ E) [Finite K.faces] [Finite H.faces]
    (hK : IsCombinatorialManifoldWithBoundary 3 K)
    (hH : IsCombinatorialManifoldWithBoundary 2 H)
    (hHK : H.space ⊆ (boundaryComplex 3 K).space) {Z P W₀ : Set E}
    (hZ : IsPolyhedron Z) (hZH : Z ⊆ H.space) (hP : P ∈ 𝓝ˢ[H.space] Z)
    {a b : ℝ} (hab : a < b) {ρ₀ : E × ℝ → E}
    (hρ₀ : IsPLHomeomorphOn ρ₀ (P ×ˢ Icc a b) W₀) (hW₀K : W₀ ⊆ K.space)
    (hbottom₀ : ∀ x ∈ P, ρ₀ (x, a) = x)
    (htrace₀ : W₀ ∩ (boundaryComplex 3 K).space = P) :
    ∃ (L : Geometry.SimplicialComplex ℝ E) (W : Set E) (ρ : E × ℝ → E)
      (R : Geometry.SimplicialComplex ℝ E),
      L.faces.Finite ∧ IsCombinatorialManifoldWithBoundary 2 L ∧ L.space ⊆ H.space ∩ P ∧
      (∀ x ∈ Z, L.space ∈ 𝓝[H.space] x) ∧
      IsPolyhedron W ∧ W ⊆ K.space ∧ IsPLHomeomorphOn ρ (H.space ×ˢ Icc a b) W ∧
      EqOn ρ ρ₀ (L.space ×ˢ Icc a b) ∧ (∀ x ∈ H.space, ρ (x, a) = x) ∧
      W ∩ (boundaryComplex 3 K).space = H.space ∧
      MapsTo ρ (H.space ×ˢ Ioc a b) (K.space \ (boundaryComplex 3 K).space) ∧
      R.faces.Finite ∧ IsCombinatorialManifoldWithBoundary 3 R ∧
      R.space = closure (K.space \ W) ∧
      W ∩ R.space ⊆ (boundaryComplex 3 R).space ∧
      (boundaryComplex 3 K).space ∩ R.space ⊆ (boundaryComplex 3 R).space := by
  obtain ⟨H', L, hH'H, hH'fin, hLfin, hL, hLP, hLnhds, d₀, hLspace⟩ :=
    hH.exists_adapted_polyhedral_collar_base H hZ hZH hP
  let _ : Finite H'.faces := hH'fin.to_subtype
  let _ : Finite L.faces := hLfin.to_subtype
  let W₁ := ρ₀ '' (L.space ×ˢ Icc a b)
  have hρ₁ : IsPLHomeomorphOn ρ₀ (L.space ×ˢ Icc a b) W₁ :=
    hρ₀.restrict ((isPolyhedron_space L).prod isHPolytope_Icc.isPolyhedron)
      (prod_mono (hLP.trans inter_subset_right) subset_rfl)
  have hW₁W₀ : W₁ ⊆ W₀ := (image_mono
    (prod_mono (hLP.trans inter_subset_right) subset_rfl)).trans hρ₀.image_eq.subset
  have hbottom₁ : ∀ x ∈ L.space, ρ₀ (x, a) = x := fun x hx => hbottom₀ x (hLP hx).2
  have htrace₁ : W₁ ∩ (boundaryComplex 3 K).space = L.space := by
    apply Subset.antisymm
    · rintro x ⟨⟨z, hz, hzx⟩, hxB⟩
      have hxP := htrace₀.subset ⟨hW₁W₀ ⟨z, hz, hzx⟩, hxB⟩
      have heq := hρ₀.bijOn.injOn ⟨(hLP hz.1).2, hz.2⟩ ⟨hxP, le_rfl, hab.le⟩
        (hzx.trans (hbottom₀ x hxP).symm)
      have hzx' : z.1 = x := congrArg Prod.fst heq
      exact hzx' ▸ hz.1
    · intro x hx
      exact ⟨⟨(x, a), ⟨hx, le_rfl, hab.le⟩, hbottom₁ x hx⟩, hHK (hLP hx).1⟩
  have hH'K : H'.space ⊆ (boundaryComplex 3 K).space := hH'H.space_eq ▸ hHK
  obtain ⟨W, ρ, R, hW, -, hWK, hρ, hfix, hbottom, htrace, hpositive,
    hRfin, hR, hRspace, hWR, hBR⟩ :=
    exists_annular_collar_extension_of_surface_initial_cells K H' L hK
      (hH.of_isSubdivision hH'H) hL hH'K d₀ hLspace hab (hW₁W₀.trans hW₀K) hρ₁
      hbottom₁ htrace₁
  rw [hH'H.space_eq] at hρ hbottom htrace hpositive
  exact ⟨L, W, ρ, R, hLfin, hL, hLP, hLnhds, hW, hWK, hρ, hfix, hbottom, htrace,
    hpositive, hRfin, hR, hRspace, hWR, hBR⟩


open Classical in
theorem exists_relative_collar_extension_of_polyhedral_mark_with_support
    {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    (K H : Geometry.SimplicialComplex ℝ E) [Finite K.faces] [Finite H.faces]
    (hK : IsCombinatorialManifoldWithBoundary 3 K)
    (hH : IsCombinatorialManifoldWithBoundary 2 H)
    (hHK : H.space ⊆ (boundaryComplex 3 K).space) {Z P W₀ O : Set E}
    (hZ : IsPolyhedron Z) (hZH : Z ⊆ H.space) (hP : P ∈ 𝓝ˢ[H.space] Z)
    (hO : O ∈ 𝓝ˢ[K.space] H.space) {a b : ℝ} (hab : a < b) {ρ₀ : E × ℝ → E}
    (hρ₀ : IsPLHomeomorphOn ρ₀ (P ×ˢ Icc a b) W₀) (hW₀K : W₀ ⊆ K.space)
    (hbottom₀ : ∀ x ∈ P, ρ₀ (x, a) = x)
    (htrace₀ : W₀ ∩ (boundaryComplex 3 K).space = P) :
    ∃ (c : ℝ) (L : Geometry.SimplicialComplex ℝ E) (W : Set E) (ρ : E × ℝ → E)
      (R : Geometry.SimplicialComplex ℝ E),
      a < c ∧ c ≤ b ∧ L.faces.Finite ∧ IsCombinatorialManifoldWithBoundary 2 L ∧
      L.space ⊆ H.space ∩ P ∧
      (∀ x ∈ Z, L.space ∈ 𝓝[H.space] x) ∧
      IsPolyhedron W ∧ W ⊆ K.space ∩ O ∧ IsPLHomeomorphOn ρ (H.space ×ˢ Icc a c) W ∧
      EqOn ρ ρ₀ (L.space ×ˢ Icc a c) ∧ (∀ x ∈ H.space, ρ (x, a) = x) ∧
      W ∩ (boundaryComplex 3 K).space = H.space ∧
      MapsTo ρ (H.space ×ˢ Ioc a c) (K.space \ (boundaryComplex 3 K).space) ∧
      R.faces.Finite ∧ IsCombinatorialManifoldWithBoundary 3 R ∧
      R.space = closure (K.space \ W) ∧
      W ∩ R.space ⊆ (boundaryComplex 3 R).space ∧
      (boundaryComplex 3 K).space ∩ R.space ⊆ (boundaryComplex 3 R).space := by
  obtain ⟨L, W, ρ, _, hLfin, hL, hLP, hLnhds, _, hWK, hρ, hfix, hbottom, htrace,
    hpositive, -⟩ :=
    exists_relative_collar_extension_of_polyhedral_mark K H hK hH hHK hZ hZH hP hab
      hρ₀ hW₀K hbottom₀ htrace₀
  obtain ⟨c, hac, hcb, hcO⟩ := exists_short_product_image_subset_of_compact
    (isPolyhedron_space H).isCompact hab hρ.isPiecewiseAffineOn.continuousOn
    (hρ.bijOn.mapsTo.mono_right hWK) (fun x hx => by rw [hbottom x hx]; exact hx) hO
  let W' := ρ '' (H.space ×ˢ Icc a c)
  have hsmall : H.space ×ˢ Icc a c ⊆ H.space ×ˢ Icc a b :=
    prod_mono subset_rfl (Icc_subset_Icc le_rfl hcb)
  have hρ' : IsPLHomeomorphOn ρ (H.space ×ˢ Icc a c) W' :=
    hρ.restrict ((isPolyhedron_space H).prod isHPolytope_Icc.isPolyhedron) hsmall
  have hW'W : W' ⊆ W := (image_mono hsmall).trans hρ.image_eq.subset
  have htrace' : W' ∩ (boundaryComplex 3 K).space = H.space := by
    apply Subset.antisymm
    · exact (inter_subset_inter_left _ hW'W).trans htrace.subset
    · intro x hx
      exact ⟨⟨(x, a), ⟨hx, le_rfl, hac.le⟩, hbottom x hx⟩, hHK hx⟩
  obtain ⟨_, R, -, hRfin, -, hR, -, hRspace, -, hWR, hBR⟩ :=
    exists_complement_of_surface_collar K H hK hH hac hρ' (hW'W.trans hWK) htrace'
  refine ⟨c, L, W', ρ, R, hac, hcb, hLfin, hL, hLP, hLnhds, ?_,
    fun x hx => ⟨hWK (hW'W hx), hcO hx⟩, hρ', ?_, hbottom, htrace', ?_,
    hRfin, hR, hRspace, hWR, hBR⟩
  · have hprod := (isPolyhedron_space H).prod (isHPolytope_Icc (a := a) (b := c)).isPolyhedron
    exact hprod.image_of_isPiecewiseAffineOn hρ'.isPiecewiseAffineOn hρ'.bijOn.injOn
  · exact hfix.mono (prod_mono subset_rfl (Icc_subset_Icc le_rfl hcb))
  · intro x hx
    exact hpositive ⟨hx.1, hx.2.1, hx.2.2.trans hcb⟩

end DifferentialGeometry.Topology.PiecewiseLinear
