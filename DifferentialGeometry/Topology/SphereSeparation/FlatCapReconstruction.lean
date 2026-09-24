import DifferentialGeometry.Topology.SphereSeparation.FlatCapRegions
import DifferentialGeometry.Topology.SphereSeparation.FlatCapTransport

open Set Metric Manifold
open scoped ContDiff Manifold

namespace DifferentialGeometry.Topology.SphereSeparation

attribute [local instance] Handle.closedCellChartedSpaceSucc Handle.closedCellIsManifold

theorem exists_flat_cap_reconstruction_regions
    {e : SphereTwo → EuclideanThree} (he : IsSmoothEmbedding (𝓡 2) (𝓡 3) ∞ e)
    {b : Fin 2 → ClosedCell 2 → SphereTwo}
    (hb : ∀ i, IsSmoothEmbedding (𝓡∂ 2) (𝓡 2) ∞ (b i))
    {η : AddCircle (1 : ℝ) → SphereTwo}
    (hbboundary : ∀ i, range (b i ∘ cellBoundaryInclusion 2) = range η)
    (hcover : range (b 0) ∪ range (b 1) = univ)
    (hinter : range (b 0) ∩ range (b 1) = range η)
    (Ψ : (EuclideanSpace ℝ (Fin 2) × ℝ) ≃ₘ[ℝ] EuclideanThree)
    {R ε : ℝ} (hR : 1 < R)
    (hS : Ψ ⁻¹' range e ∩ (closedBall (0 : EuclideanSpace ℝ (Fin 2)) R ×ˢ Icc (-ε) ε) =
      sphere (0 : EuclideanSpace ℝ (Fin 2)) 1 ×ˢ Icc (-ε) ε)
    (hboundary : e '' range η = Ψ '' (sphere (0 : EuclideanSpace ℝ (Fin 2)) 1 ×ˢ {0}))
    (χ : Fin 2 → PartialDiffeomorph (𝓡 2) (𝓡 2) (EuclideanSpace ℝ (Fin 2)) SphereTwo ∞)
    (hχ : ∀ i, closedBall (0 : EuclideanSpace ℝ (Fin 2)) 1 ⊆ (χ i).source)
    (hχD : ∀ i, χ i '' closedBall (0 : EuclideanSpace ℝ (Fin 2)) 1 = range (b i))
    {a : Fin 2 → ℝ} (ha : ∀ i, a i ≠ 0) (haε : ∀ i, |a i| < ε)
    {f g : Fin 2 → SphereTwo → EuclideanThree}
    (hf : ∀ i, IsSmoothEmbedding (𝓡 2) (𝓡 3) ∞ (f i))
    (hcap : ∀ i, ∀ x ∈ closedBall (0 : EuclideanSpace ℝ (Fin 2)) 1,
      f i (χ i x) = Ψ (EuclideanGeometry.cylinderCap (a i) x))
    (hffix : ∀ i, EqOn (f i) e (range (b i))ᶜ)
    (hside : ∀ i, ∀ p ∈ ball (0 : EuclideanSpace ℝ (Fin 2)) R ×ˢ Ioo (-ε) ε,
      Ψ p ∈ e '' (range (b i))ᶜ → ‖p.1‖ = 1 ∧ 0 ≤ a i * p.2)
    (hflat : ∀ i, ∀ x ∈ closedBall (0 : EuclideanSpace ℝ (Fin 2)) 1, g i (χ i x) = Ψ (x, 0))
    (hgfix : ∀ i, EqOn (g i) e (range (b i))ᶜ)
    (hrange : ∀ i, range (g i) = Ψ '' (closedBall (0 : EuclideanSpace ℝ (Fin 2)) 1 ×ˢ {0}) ∪
      e '' (range (b i))ᶜ)
    (hgin : range (g 0) ∩ range (g 1) =
      Ψ '' (closedBall (0 : EuclideanSpace ℝ (Fin 2)) 1 ×ˢ {0}))
    (hgun : range (g 0) ∪ range (g 1) = range e ∪
      Ψ '' (closedBall (0 : EuclideanSpace ℝ (Fin 2)) 1 ×ˢ {0})) :
    let d := (jordanBrouwer_openThreeSpace e he
      (Diffeomorph.refl (𝓡 3) EuclideanThree ∞)).toSphereSides
    let d_f := fun i => (jordanBrouwer_openThreeSpace (f i) (hf i)
      (Diffeomorph.refl (𝓡 3) EuclideanThree ∞)).toSphereSides
    ∃ (Φ : Fin 2 → EuclideanThree ≃ₜ EuclideanThree)
      (C : Fin 2 → Set EuclideanThree) (d' : ∀ i, SphereSides (range (g i))),
      (∀ i, Φ i ∘ f i = g i ∧ EqOn (Φ i) id (e '' (range (b i))ᶜ) ∧
        _root_.Topology.IsEmbedding (g i) ∧ IsCompact (C i) ∧
        C i ⊆ Ψ '' (ball (0 : EuclideanSpace ℝ (Fin 2)) R ×ˢ Ioo (-ε) ε) ∧
        EqOn (Φ i) id (C i)ᶜ ∧ EqOn (Φ i).symm id (C i)ᶜ ∧
        (d' i).compactSide = Φ i '' (d_f i).compactSide ∧
        (d' i).endSide = Φ i '' (d_f i).endSide) ∧
      ((Disjoint (d' 0).compactSide (d' 1).compactSide ∧
        closure d.compactSide = closure (d' 0).compactSide ∪ closure (d' 1).compactSide ∧
        closure (d' 0).compactSide ∩ closure (d' 1).compactSide =
          Ψ '' (closedBall (0 : EuclideanSpace ℝ (Fin 2)) 1 ×ˢ {0})) ∨
      ((d' 0).compactSide ⊂ (d' 1).compactSide ∧
        d.compactSide = (d' 1).compactSide \ closure (d' 0).compactSide ∧
        closure d.compactSide =
          closure (interior (closure (d' 1).compactSide) \ closure (d' 0).compactSide) ∧
        closure (d' 1).compactSide = closure d.compactSide ∪ closure (d' 0).compactSide ∧
        closure d.compactSide ∩ closure (d' 0).compactSide = range e ∩ range (g 0)) ∨
      ((d' 1).compactSide ⊂ (d' 0).compactSide ∧
        d.compactSide = (d' 0).compactSide \ closure (d' 1).compactSide ∧
        closure d.compactSide =
          closure (interior (closure (d' 0).compactSide) \ closure (d' 1).compactSide) ∧
        closure (d' 0).compactSide = closure d.compactSide ∪ closure (d' 1).compactSide ∧
        closure d.compactSide ∩ closure (d' 1).compactSide = range e ∩ range (g 1))) := by
  classical
  dsimp only
  have htransport (i : Fin 2) := exists_sphere_sides_flat_cap (hf i) Ψ.toHomeomorph
    (ha i) (haε i) hR (χ i) (hχD i) (hcap i) (hflat i) (hffix i) (hgfix i) (hside i)
  choose Φ hΦ hretained hg C hC hCU hΦfix hΦifix d' hcompact hend using htransport
  refine ⟨Φ, C, d', fun i => ⟨hΦ i, hretained i, hg i, hC i, hCU i, hΦfix i,
    hΦifix i, hcompact i, hend i⟩, ?_⟩
  exact SphereSides.flat_cap_reconstruction_regions he.isEmbedding hb hbboundary hcover
    hinter Ψ (le_of_lt hR) (le_trans (abs_nonneg (a 0)) (le_of_lt (haε 0))) hS hboundary
    χ hχ hχD hg hflat hgfix hrange hgin hgun
    (jordanBrouwer_openThreeSpace e he (Diffeomorph.refl (𝓡 3) EuclideanThree ∞)).toSphereSides d'

end DifferentialGeometry.Topology.SphereSeparation
