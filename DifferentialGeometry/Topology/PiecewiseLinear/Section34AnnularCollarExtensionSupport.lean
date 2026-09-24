import DifferentialGeometry.Topology.PiecewiseLinear.Section34AnnularCollarExtensionRelative

open Set Topology

namespace DifferentialGeometry.Topology.PiecewiseLinear

theorem exists_short_product_image_subset_of_compact
    {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    {S : Set X} (hS : IsCompact S) {T V O : Set Y} {a b : ℝ} (hab : a < b)
    {f : X × ℝ → Y} (hf : ContinuousOn f (S ×ˢ Icc a b))
    (hV : MapsTo f (S ×ˢ Icc a b) V) (ha : ∀ x ∈ S, f (x, a) ∈ T)
    (hO : O ∈ 𝓝ˢ[V] T) :
    ∃ c : ℝ, a < c ∧ c ≤ b ∧ f '' (S ×ˢ Icc a c) ⊆ O := by
  have hpre := hf.preimage_mem_nhdsSetWithin hO
  rw [show (S ×ˢ Icc a b) ∩ f ⁻¹' V = S ×ˢ Icc a b from
    inter_eq_left.mpr hV] at hpre
  have hcenter : S ×ˢ {a} ⊆ (S ×ˢ Icc a b) ∩ f ⁻¹' T := by
    rintro ⟨x, t⟩ ⟨hx, ht⟩
    change t = a at ht
    subst t
    exact ⟨⟨hx, le_rfl, hab.le⟩, ha x hx⟩
  obtain ⟨U, hU, hSU⟩ := generalized_tube_lemma_right hS isCompact_singleton
    ((nhdsSetWithin_mono_left hcenter) hpre)
  rw [nhdsSetWithin_singleton, nhdsWithin_Icc_eq_nhdsGE hab] at hU
  obtain ⟨c, hac, hcU⟩ := mem_nhdsGE_iff_exists_Icc_subset.mp hU
  refine ⟨min c b, lt_min hac hab, min_le_right _ _, ?_⟩
  rintro _ ⟨⟨x, t⟩, ⟨hx, ht⟩, rfl⟩
  exact hSU ⟨hx, hcU ⟨ht.1, ht.2.trans (min_le_left _ _)⟩⟩

open Classical in
theorem exists_relative_annular_collar_extension_with_support
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    (K H : Geometry.SimplicialComplex ℝ E) [Finite K.faces] [Finite H.faces]
    (hK : IsCombinatorialManifoldWithBoundary 3 K)
    (hH : IsCombinatorialManifoldWithBoundary 2 H)
    (hHK : H.space ⊆ (boundaryComplex 3 K).space) {P W₀ O : Set E}
    (hP : P ∈ 𝓝ˢ[H.space] (boundaryComplex 2 H).space)
    (hO : O ∈ 𝓝ˢ[K.space] H.space) {a b : ℝ} (hab : a < b) {ρ₀ : E × ℝ → E}
    (hρ₀ : IsPLHomeomorphOn ρ₀ (P ×ˢ Icc a b) W₀) (hW₀K : W₀ ⊆ K.space)
    (hbottom₀ : ∀ x ∈ P, ρ₀ (x, a) = x)
    (htrace₀ : W₀ ∩ (boundaryComplex 3 K).space = P) :
    ∃ (c : ℝ) (L : Geometry.SimplicialComplex ℝ E) (W : Set E) (ρ : E × ℝ → E)
      (R : Geometry.SimplicialComplex ℝ E),
      a < c ∧ c ≤ b ∧ L.faces.Finite ∧ IsCombinatorialManifoldWithBoundary 2 L ∧
      L.space ⊆ H.space ∩ P ∧
      (∀ x ∈ (boundaryComplex 2 H).space, L.space ∈ 𝓝[H.space] x) ∧
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
    exists_relative_annular_collar_extension K H hK hH hHK hP hab hρ₀ hW₀K hbottom₀ htrace₀
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
