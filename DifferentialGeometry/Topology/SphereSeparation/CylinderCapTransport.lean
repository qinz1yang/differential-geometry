import DifferentialGeometry.Topology.SphereSeparation.CylinderCap
import DifferentialGeometry.Topology.Diffeomorph.CylinderCapTranslation

open Set Metric Manifold
open scoped ContDiff Manifold

namespace DifferentialGeometry.Topology.SphereSeparation

theorem exists_isotopy_displacing_cylinderCap
    {e f : SphereTwo → EuclideanThree} (hf : IsSmoothEmbedding (𝓡 2) (𝓡 3) ∞ f)
    (Ψ : (Schoenflies.Plane × ℝ) ≃ₘ[ℝ] EuclideanThree) {R ε a d σ c : ℝ}
    (hR : 1 < R) (ha : 0 ≤ a) (had : a < d) (hdε : d < ε)
    (hσ : σ = 1 ∨ σ = -1) (hheight : ∀ p, Ψ p 2 = c + p.2)
    (hS : Ψ ⁻¹' range e ∩ (closedBall (0 : Schoenflies.Plane) R ×ˢ Icc (-ε) ε) =
      sphere (0 : Schoenflies.Plane) 1 ×ˢ Icc (-ε) ε)
    {D : Set SphereTwo} (χ : Schoenflies.Plane → SphereTwo)
    (hχD : χ '' closedBall (0 : Schoenflies.Plane) 1 = D)
    (hcap : ∀ x ∈ closedBall (0 : Schoenflies.Plane) 1,
      f (χ x) = Ψ (EuclideanGeometry.cylinderCap (σ * a) x))
    (hfix : EqOn f e Dᶜ)
    (hside : ∀ p ∈ ball (0 : Schoenflies.Plane) R ×ˢ Ioo (-ε) ε,
      Ψ p ∈ e '' Dᶜ → 0 < σ * p.2) :
    ∃ H : ℝ → (EuclideanThree ≃ₘ[ℝ] EuclideanThree),
      ContDiff ℝ ∞ (fun z : ℝ × EuclideanThree => H z.1 z.2) ∧
      ContDiff ℝ ∞ (fun z : ℝ × EuclideanThree => (H z.1).symm z.2) ∧
      H 0 = Diffeomorph.refl (𝓡 3) EuclideanThree ∞ ∧
      (∀ t, H t '' range e = range e) ∧
      (∀ t, IsSmoothEmbedding (𝓡 2) (𝓡 3) ∞ (H t ∘ f)) ∧
      range (H 1 ∘ f) ∩ {z | z 2 = c} = e '' Dᶜ ∩ {z | z 2 = c} ∧
      (∀ x ∈ closedBall (0 : Schoenflies.Plane) 1, 0 < σ * (H 1 (f (χ x)) 2 - c)) ∧
      ∃ U : Set (Schoenflies.Plane × ℝ), IsOpen U ∧
        EuclideanGeometry.cylinderCap (σ * a) '' closedBall (0 : Schoenflies.Plane) 1 ⊆ U ∧
        (∀ t ∈ Icc (0 : ℝ) 1, ∀ p ∈ U, H t (Ψ p) = Ψ (p.1, p.2 + t * (σ * d))) ∧
      ∃ J : Set EuclideanThree, IsCompact J ∧
        J ⊆ Ψ '' (ball (0 : Schoenflies.Plane) R ×ˢ Ioo (-ε) ε) ∧
        ∀ t : ℝ, EqOn (H t) id Jᶜ ∧ EqOn (H t).symm id Jᶜ := by
  have hSopen : Ψ ⁻¹' range e ∩ (ball (0 : Schoenflies.Plane) R ×ˢ Ioo (-ε) ε) =
      sphere (0 : Schoenflies.Plane) 1 ×ˢ Ioo (-ε) ε := by
    ext p
    constructor
    · rintro ⟨hpS, hp⟩
      have hh := hS.subset ⟨hpS, ball_subset_closedBall hp.1, Ioo_subset_Icc_self hp.2⟩
      exact ⟨hh.1, hp.2⟩
    · rintro ⟨hp, ht⟩
      exact ⟨(hS.symm.subset ⟨hp, Ioo_subset_Icc_self ht⟩).1,
        sphere_subset_ball hR hp, ht⟩
  have hrange : range f = e '' Dᶜ ∪
      Ψ '' (EuclideanGeometry.cylinderCap (σ * a) '' closedBall (0 : Schoenflies.Plane) 1) := by
    ext z
    constructor
    · rintro ⟨x, rfl⟩
      by_cases hx : x ∈ D
      · obtain ⟨y, hy, rfl⟩ := hχD.symm.subset hx
        exact Or.inr ⟨EuclideanGeometry.cylinderCap (σ * a) y, ⟨y, hy, rfl⟩, (hcap y hy).symm⟩
      · exact Or.inl ⟨x, hx, (hfix hx).symm⟩
    · rintro (⟨x, hx, rfl⟩ | ⟨p, ⟨x, hx, rfl⟩, rfl⟩)
      · exact ⟨x, hfix hx⟩
      · exact ⟨χ x, hcap x hx⟩
  obtain ⟨H, hH, hHi, hH0, hHS, hpositive, hlevel, U, hU, hcapU, hmove,
    J, hJ, hJU, hsupport⟩ := Diffeomorph.exists_isotopy_cylinderCap_translation_in_chart
      Ψ hR ha had hdε hσ (fun z : EuclideanThree => z 2) hheight hSopen
  refine ⟨H, hH, hHi, hH0, hHS, fun t => hf.diffeomorph_comp (H t), ?_,
    fun x hx => ?_, U, hU, hcapU, hmove, J, hJ, hJU, hsupport⟩
  · rw [range_comp, hrange]
    exact hlevel (e '' Dᶜ) (image_subset_range _ _) hside
  · rw [hcap x hx]
    exact hpositive x hx

end DifferentialGeometry.Topology.SphereSeparation
