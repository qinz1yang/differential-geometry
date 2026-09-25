import DifferentialGeometry.Topology.PiecewiseLinear.Section34SeamCollarExtension
import DifferentialGeometry.Topology.PiecewiseLinear.Section34AnnularCollarExtensionSupport

open Set Topology

namespace DifferentialGeometry.Topology.PiecewiseLinear

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
