import DifferentialGeometry.Topology.PiecewiseLinear.Section34AnnularCollarExtension
import DifferentialGeometry.Topology.PiecewiseLinear.Section34AnnularCollarExtensionComplement
import DifferentialGeometry.Topology.PiecewiseLinear.ManifoldInteriorDensity

open Set Topology

namespace DifferentialGeometry.Topology.PiecewiseLinear

open Classical in
theorem exists_annular_collar_extension_of_surface_initial_cells
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    (K H L : Geometry.SimplicialComplex ℝ E)
    [Finite K.faces] [Finite H.faces] [Finite L.faces]
    (hK : IsCombinatorialManifoldWithBoundary 3 K)
    (hH : IsCombinatorialManifoldWithBoundary 2 H)
    (hL : IsCombinatorialManifoldWithBoundary 2 L)
    (hHK : H.space ⊆ (boundaryComplex 3 K).space)
    (d₀ : Finset {v : E // ({v} : Finset E) ∈ H.faces})
    (hLspace : L.space = section34AnnularCollarBase H d₀)
    {a b : ℝ} (hab : a < b) {W₀ : Set E} {ρ₀ : E × ℝ → E}
    (hW₀K : W₀ ⊆ K.space) (hρ₀ : IsPLHomeomorphOn ρ₀ (L.space ×ˢ Icc a b) W₀)
    (hbottom₀ : ∀ x ∈ L.space, ρ₀ (x, a) = x)
    (htrace₀ : W₀ ∩ (boundaryComplex 3 K).space = L.space) :
    ∃ (W : Set E) (ρ : E × ℝ → E) (R : Geometry.SimplicialComplex ℝ E),
      IsPolyhedron W ∧ W₀ ⊆ W ∧ W ⊆ K.space ∧
      IsPLHomeomorphOn ρ (H.space ×ˢ Icc a b) W ∧ EqOn ρ ρ₀ (L.space ×ˢ Icc a b) ∧
      (∀ x ∈ H.space, ρ (x, a) = x) ∧ W ∩ (boundaryComplex 3 K).space = H.space ∧
      MapsTo ρ (H.space ×ˢ Ioc a b) (K.space \ (boundaryComplex 3 K).space) ∧
      R.faces.Finite ∧ IsCombinatorialManifoldWithBoundary 3 R ∧
      R.space = closure (K.space \ W) ∧
      W ∩ R.space ⊆ (boundaryComplex 3 R).space ∧
      (boundaryComplex 3 K).space ∩ R.space ⊆ (boundaryComplex 3 R).space := by
  obtain ⟨A, R₀, hAfin, hR₀fin, hA, hR₀, hAspace, hR₀space, hAbd, hW₀R₀, hBR₀⟩ :=
    exists_complement_of_surface_collar K L hK hL hab hρ₀ hW₀K htrace₀
  let _ : Finite A.faces := hAfin.to_subtype
  let _ : Finite R₀.faces := hR₀fin.to_subtype
  have hAK : A.space ⊆ K.space := hAspace ▸ hW₀K
  have hfrontR := boundaryComplex_space_of_closure_sdiff K A R₀ hK hA hAK hR₀
    (by rw [hAspace]; exact hR₀space)
  rw [hAspace] at hfrontR
  have hLH : L.space ⊆ H.space := by
    rw [hLspace]
    intro x hx
    obtain ⟨v, -, hv⟩ := mem_iUnion₂.mp hx
    rw [← iUnion_dualCell_singleton_space H]
    exact mem_iUnion.mpr ⟨v, hv⟩
  have hattach : ∀ v ∉ d₀, (dualCell H {v.1} v.2).space ∪
      ρ₀ '' (((dualCell H {v.1} v.2).space ∩ L.space) ×ˢ Icc a b) ⊆
        (boundaryComplex 3 R₀).space := by
    intro v hv
    let D := dualCell H {v.1} v.2
    let _ : Finite D.faces := (dualCell_faces_finite H v.2).to_subtype
    have hD : IsPLBall 2 D.space :=
      hH.isPLBall_dualCell H v.2 (k := 0) (Finset.card_singleton v.1) (by norm_num)
    have hDH : D.space ⊆ H.space := by
      intro x hx
      rw [← iUnion_dualCell_singleton_space H]
      exact mem_iUnion.mpr ⟨v, hx⟩
    obtain ⟨e, -, hE, hcover⟩ :=
      hH.exists_boundary_arcs_cover_inter_dualCell_iUnion H d₀ hv
    have hmeet : D.space ∩ L.space ⊆ (boundaryComplex 2 D).space := by
      rw [hLspace, section34AnnularCollarBase, ← hcover]
      exact iUnion₂_subset fun w hw => (hE w hw).2
    have hdense : D.space ⊆ closure (H.space \ L.space) :=
      hD.isCombinatorialManifoldWithBoundary.space_subset_closure_sdiff_boundaryComplex_space.trans
        (closure_mono fun x hx => ⟨hDH hx.1, fun hxL => hx.2 (hmeet ⟨hx.1, hxL⟩)⟩)
    have hbase : D.space ⊆ (boundaryComplex 3 R₀).space := by
      intro x hx
      rw [hfrontR]
      apply Or.inl
      apply closure_mono (fun y hy => ?_) (hdense hx)
      exact ⟨hHK hy.1, fun hyW => hy.2 (htrace₀.subset ⟨hyW, hHK hy.1⟩)⟩
    have hmeetL : D.space ∩ L.space ⊆ (boundaryComplex 2 L).space := fun x hx =>
      inter_closure_sdiff_subset_boundaryComplex H L hH hL hLH ⟨hx.2, hdense hx.1⟩
    have hpositive : ρ₀ '' ((D.space ∩ L.space) ×ˢ Ioc a b) ⊆
        (boundaryComplex 3 A).space \ (boundaryComplex 3 K).space := by
      rintro y ⟨z, hz, rfl⟩
      have hzI : z.2 ∈ Icc a b := Ioc_subset_Icc_self hz.2
      refine ⟨hAbd.symm.subset ⟨z, Or.inr ⟨hmeetL hz.1, hzI⟩, rfl⟩, ?_⟩
      intro hyB
      have hyL := htrace₀.subset ⟨hρ₀.bijOn.mapsTo ⟨hz.1.2, hzI⟩, hyB⟩
      have heq := hρ₀.bijOn.injOn ⟨hz.1.2, hzI⟩ ⟨hyL, le_rfl, hab.le⟩
        (hbottom₀ _ hyL).symm
      exact hz.2.1.ne' (congrArg Prod.snd heq)
    refine union_subset hbase ?_
    rintro y ⟨z, hz, rfl⟩
    have hzcl : z ∈ closure ((D.space ∩ L.space) ×ˢ Ioc a b) := by
      rw [closure_prod_eq, closure_Ioc hab.ne]
      exact ⟨subset_closure hz.1, hz.2⟩
    have hc := ((hρ₀.isPiecewiseAffineOn.continuousOn z ⟨hz.1.2, hz.2⟩).mono
      (prod_mono inter_subset_right Ioc_subset_Icc_self)).mem_closure_image hzcl
    rw [hfrontR]
    exact Or.inr (closure_mono hpositive hc)
  have hρ₀' : IsPLHomeomorphOn ρ₀ (section34AnnularCollarBase H d₀ ×ˢ Icc a b) W₀ := by
    rwa [← hLspace]
  have hbottom₀' : ∀ x ∈ section34AnnularCollarBase H d₀, ρ₀ (x, a) = x := by
    rwa [← hLspace]
  have htrace₀' : W₀ ∩ (boundaryComplex 3 K).space = section34AnnularCollarBase H d₀ :=
    htrace₀.trans hLspace
  have hattach' : ∀ v ∉ d₀, (dualCell H {v.1} v.2).space ∪
      ρ₀ '' (((dualCell H {v.1} v.2).space ∩ section34AnnularCollarBase H d₀) ×ˢ Icc a b) ⊆
        (boundaryComplex 3 R₀).space := by
    rwa [← hLspace]
  obtain ⟨W, ρ, R, hW, hW₀W, hWK, hρ, hfix, hbottom, htrace, hpos,
    hRfin, hR, hRspace, hWR, hBR⟩ :=
    exists_annular_collar_extension_of_initial_cells K H R₀ hH hHK d₀ hab hW₀K hρ₀'
      hbottom₀' htrace₀' hR₀ hR₀space hW₀R₀ hBR₀ hattach'
  exact ⟨W, ρ, R, hW, hW₀W, hWK, hρ, hLspace ▸ hfix, hbottom, htrace, hpos,
    hRfin, hR, hRspace, hWR, hBR⟩

end DifferentialGeometry.Topology.PiecewiseLinear
