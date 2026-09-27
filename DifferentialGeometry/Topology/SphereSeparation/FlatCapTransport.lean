import DifferentialGeometry.Topology.Embedding.FlatCapTransport
import DifferentialGeometry.Topology.SphereSeparation.SourceTheorems
import DifferentialGeometry.Topology.SphereSeparation.Transport

open Set Metric Manifold
open scoped ContDiff Manifold

namespace DifferentialGeometry.Topology.SphereSeparation

theorem exists_sphere_sides_flat_cap
    {e f g : SphereTwo → EuclideanThree} (hf : IsSmoothEmbedding (𝓡 2) (𝓡 3) ∞ f)
    (Ψ : (EuclideanSpace ℝ (Fin 2) × ℝ) ≃ₜ EuclideanThree)
    {a b R : ℝ} (ha : a ≠ 0) (hab : |a| < b) (hR : 1 < R)
    {D : Set SphereTwo} (χ : EuclideanSpace ℝ (Fin 2) → SphereTwo)
    (hχD : χ '' closedBall (0 : EuclideanSpace ℝ (Fin 2)) 1 = D)
    (hcap : ∀ x ∈ closedBall (0 : EuclideanSpace ℝ (Fin 2)) 1,
      f (χ x) = Ψ (EuclideanGeometry.cylinderCap a x))
    (hflat : ∀ x ∈ closedBall (0 : EuclideanSpace ℝ (Fin 2)) 1, g (χ x) = Ψ (x, 0))
    (hfix : EqOn f e Dᶜ) (hgfix : EqOn g e Dᶜ)
    (hside : ∀ p ∈ ball (0 : EuclideanSpace ℝ (Fin 2)) R ×ˢ Ioo (-b) b,
      Ψ p ∈ e '' Dᶜ → ‖p.1‖ = 1 ∧ 0 ≤ a * p.2) :
    let d_f := (jordanBrouwer_openThreeSpace f hf
      (Diffeomorph.refl (𝓡 3) EuclideanThree ∞)).toSphereSides
    ∃ Φ : EuclideanThree ≃ₜ EuclideanThree,
      Φ ∘ f = g ∧ EqOn Φ id (e '' Dᶜ) ∧ _root_.Topology.IsEmbedding g ∧
      ∃ C : Set EuclideanThree, IsCompact C ∧
        C ⊆ Ψ '' (ball (0 : EuclideanSpace ℝ (Fin 2)) R ×ˢ Ioo (-b) b) ∧
        EqOn Φ id Cᶜ ∧ EqOn Φ.symm id Cᶜ ∧
        ∃ d : SphereSides (range g),
          d.compactSide = Φ '' d_f.compactSide ∧ d.endSide = Φ '' d_f.endSide := by
  dsimp only
  obtain ⟨Φ, hΦ, hretained, C, hC, hCU, hfixΦ, hfixΦi⟩ :=
    Homeomorph.exists_cylinderCap_replacement_flattening Ψ ha hab hR χ hχD
      hcap hflat hfix hgfix hside
  have hg : _root_.Topology.IsEmbedding g := hΦ ▸ Φ.isEmbedding.comp hf.isEmbedding
  refine ⟨Φ, hΦ, hretained, hg, C, hC, hCU, hfixΦ, hfixΦi, ?_⟩
  have himage : Φ '' range f = range g := by rw [← range_comp, hΦ]
  rw [← himage]
  exact ⟨((jordanBrouwer_openThreeSpace f hf
    (Diffeomorph.refl (𝓡 3) EuclideanThree ∞)).toSphereSides).image Φ, rfl, rfl⟩

end DifferentialGeometry.Topology.SphereSeparation
