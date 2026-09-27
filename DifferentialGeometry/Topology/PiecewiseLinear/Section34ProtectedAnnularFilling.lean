import DifferentialGeometry.Topology.PiecewiseLinear.Section34AnnulusPairModel
import DifferentialGeometry.Topology.PiecewiseLinear.Section34InnerTubeBicollar
import DifferentialGeometry.Topology.PiecewiseLinear.Section34PiercingGenerators

open Set

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

theorem exists_section34_filling_of_annulus_pair
    (hprep : Section34VertexPreparation U 𝒦 𝒦' h src Q ends Cp CpBd Cc CcBd Kcore Sn Tn Aa Ab₀ Ab₁
      Bb Bb₀ Bb₁ Bc Bc₀ Bc₁ ε)
    (hpack : Section34PiercingConditions U 𝒦 𝒦' h Q ends Cp CpBd Cc Sn Tn Aa Ab₀ Ab₁ Bb Bb₀
      Bb₁ Sp Tp cnt Pg G) (e : Section34EdgeIndex 𝒦 𝒦')
    {D F : Set (EuclideanSpace ℝ (Fin 3))}
    {uD uF : EuclideanSpace ℝ (Fin 3) → M₂}
    (hD : IsPLHomeomorphInto 3 uD D) (hF : IsPLHomeomorphInto 3 uF F)
    {φ ψ : (Fin 3 → ℝ) × ℝ → EuclideanSpace ℝ (Fin 3)}
    (hφ : IsPLHomeomorphOn φ (stdSimplexBoundary 2 ×ˢ Icc (0 : ℝ) 1) D)
    (hψ : IsPLHomeomorphOn ψ (stdSimplexBoundary 2 ×ˢ Icc (0 : ℝ) 1) F)
    (hDT : uD '' D ⊆ Tp e) (hFT : uF '' F ⊆ Tp e)
    (hDF : uD '' D ∩ uF '' F = (uD ∘ φ) '' (stdSimplexBoundary 2 ×ˢ {(0 : ℝ), 1}))
    (hends : (uD ∘ φ) '' (stdSimplexBoundary 2 ×ˢ {(0 : ℝ), 1}) =
      (uF ∘ ψ) '' (stdSimplexBoundary 2 ×ˢ {(0 : ℝ), 1})) :
    ∃ (P : Set (EuclideanSpace ℝ (Fin 3))) (u : EuclideanSpace ℝ (Fin 3) → M₂)
      (R : Geometry.SimplicialComplex ℝ (EuclideanSpace ℝ (Fin 3))),
      IsPLBall 3 P ∧ IsPLHomeomorphInto 3 u P ∧ u '' P = G (ends e).1 '' Cc (ends e).1 ∧
      R.faces.Finite ∧ IsCombinatorialManifoldWithBoundary 3 R ∧
      u '' frontier R.space = uD '' D ∪ uF '' F ∧ closure (interior R.space) = R.space ∧
      IsConnected (interior R.space) ∧ IsConnected R.spaceᶜ ∧ R.space ⊆ P ∧
      u '' R.space ⊆ Tp e := by
  obtain ⟨P, u, _, _, hP, hu, hCc, hN, -⟩ := exists_section34_inner_tube_bicollar hprep e
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, htor, hSnCc, -⟩ := hprep
  obtain ⟨hG, -, -, htube, -⟩ := hpack
  have hNP : Tn e ⊆ u '' P := by
    rw [← hCc]
    exact ((htor e).1.trans interior_subset).trans (hSnCc e _ (Or.inl rfl))
  obtain ⟨K, hKfin, hKspace, hK⟩ := hu.exists_simplicialComplex_invFunOn_image hN hNP
  let _ : Finite K.faces := hKfin.to_subtype
  have hleft := hu.injOn.leftInvOn_invFunOn
  have hright := hu.injOn.bijOn_image.invOn_invFunOn.2
  have hKP : K.space ⊆ P := by
    rw [hKspace]
    rintro _ ⟨x, hx, rfl⟩
    obtain ⟨y, hy, rfl⟩ := hNP hx
    rw [hleft hy]
    exact hy
  have hKtor : IsTopologicalSolidTorus K.space := by
    rw [hKspace]
    apply ((htor e).2.2.1).image_of_continuousOn_injOn
      ((hu.isPLOn_inverse hleft).continuousOn.mono hNP)
    intro x hx y hy hxy
    rw [← hright (hNP hx), ← hright (hNP hy), hxy]
  have hback : u '' K.space = Tn e := by
    rw [hKspace, image_image]
    exact (image_congr fun x hx => hright (hNP hx)).trans (image_id' _)
  let v := G (ends e).1 ∘ u
  have hv : IsPLHomeomorphInto 3 v P := hu.comp_of_image_eq (hCc ▸ hG (ends e).1)
  have hvT : v '' K.space = Tp e := by
    dsimp only [v]
    rw [image_comp, hback, ← (htube e).2]
  have hcircle : IsPLSphere 1 (stdSimplexBoundary 2) := by
    simpa only [simplexBoundary_stdVertices_space] using isPLSphere_simplexBoundary_std 1
  obtain ⟨R, hRfin, hR, hfront, hreg, hint, hext, hRK⟩ :=
    hv.exists_manifold_filling_of_annulus_pair_in_torus hD hF K hK hKP hKtor
      hcircle hcircle hφ hψ (hvT.symm ▸ hDT) (hvT.symm ▸ hFT) hDF hends
  refine ⟨P, v, R, hP, hv, ?_, hRfin, hR, hfront, hreg, hint, hext,
    hRK.trans hKP, hvT ▸ image_mono hRK⟩
  dsimp only [v]
  rw [image_comp, ← hCc]

end DifferentialGeometry.Topology.PiecewiseLinear
