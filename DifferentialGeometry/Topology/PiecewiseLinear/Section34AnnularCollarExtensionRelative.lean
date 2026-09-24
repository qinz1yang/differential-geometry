import DifferentialGeometry.Topology.PiecewiseLinear.Section34AnnularCollarExtensionAdaptation

open Set Topology

namespace DifferentialGeometry.Topology.PiecewiseLinear

open Classical in
theorem exists_relative_annular_collar_extension
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    (K H : Geometry.SimplicialComplex ℝ E) [Finite K.faces] [Finite H.faces]
    (hK : IsCombinatorialManifoldWithBoundary 3 K)
    (hH : IsCombinatorialManifoldWithBoundary 2 H)
    (hHK : H.space ⊆ (boundaryComplex 3 K).space) {P W₀ : Set E}
    (hP : P ∈ 𝓝ˢ[H.space] (boundaryComplex 2 H).space)
    {a b : ℝ} (hab : a < b) {ρ₀ : E × ℝ → E}
    (hρ₀ : IsPLHomeomorphOn ρ₀ (P ×ˢ Icc a b) W₀) (hW₀K : W₀ ⊆ K.space)
    (hbottom₀ : ∀ x ∈ P, ρ₀ (x, a) = x)
    (htrace₀ : W₀ ∩ (boundaryComplex 3 K).space = P) :
    ∃ (L : Geometry.SimplicialComplex ℝ E) (W : Set E) (ρ : E × ℝ → E)
      (R : Geometry.SimplicialComplex ℝ E),
      L.faces.Finite ∧ IsCombinatorialManifoldWithBoundary 2 L ∧ L.space ⊆ H.space ∩ P ∧
      (∀ x ∈ (boundaryComplex 2 H).space, L.space ∈ 𝓝[H.space] x) ∧
      IsPolyhedron W ∧ W ⊆ K.space ∧ IsPLHomeomorphOn ρ (H.space ×ˢ Icc a b) W ∧
      EqOn ρ ρ₀ (L.space ×ˢ Icc a b) ∧ (∀ x ∈ H.space, ρ (x, a) = x) ∧
      W ∩ (boundaryComplex 3 K).space = H.space ∧
      MapsTo ρ (H.space ×ˢ Ioc a b) (K.space \ (boundaryComplex 3 K).space) ∧
      R.faces.Finite ∧ IsCombinatorialManifoldWithBoundary 3 R ∧
      R.space = closure (K.space \ W) ∧
      W ∩ R.space ⊆ (boundaryComplex 3 R).space ∧
      (boundaryComplex 3 K).space ∩ R.space ⊆ (boundaryComplex 3 R).space := by
  obtain ⟨H', L, hH'H, hH'fin, hLfin, hL, hLP, hLnhds, d₀, hLspace⟩ :=
    hH.exists_adapted_boundary_collar_base H hP
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

end DifferentialGeometry.Topology.PiecewiseLinear
