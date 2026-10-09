import DifferentialGeometry.Topology.Embedding.FlatPatch
import DifferentialGeometry.Topology.Manifold.PartialDiffeomorph
import DifferentialGeometry.Topology.SphereSeparation.LocalNormalForm

open Set Metric Manifold
open scoped ContDiff Manifold

namespace DifferentialGeometry.Topology.SphereSeparation

theorem embeddedSphereNormalChart_nonempty_of_flat_cap
    {e g : SphereTwo → EuclideanThree} (hg : _root_.Topology.IsEmbedding g)
    (Ψ : (EuclideanSpace ℝ (Fin 2) × ℝ) ≃ₘ[ℝ] EuclideanThree)
    (χ : PartialDiffeomorph (𝓡 2) (𝓡 2) (EuclideanSpace ℝ (Fin 2)) SphereTwo ∞)
    (hχ : closedBall (0 : EuclideanSpace ℝ (Fin 2)) 1 ⊆ χ.source)
    (hflat : ∀ x ∈ closedBall (0 : EuclideanSpace ℝ (Fin 2)) 1, g (χ x) = Ψ (x, 0))
    (hfix : EqOn g e (χ '' closedBall (0 : EuclideanSpace ℝ (Fin 2)) 1)ᶜ)
    (hboundary : Ψ '' (sphere (0 : EuclideanSpace ℝ (Fin 2)) 1 ×ˢ {0}) ⊆ range e)
    {z : SphereTwo} (hz : g z ∉ range e) : Nonempty (EmbeddedSphereNormalChart g z) := by
  have hzD : z ∈ χ '' closedBall (0 : EuclideanSpace ℝ (Fin 2)) 1 := by
    by_contra hn
    exact hz (hfix hn ▸ mem_range_self z)
  obtain ⟨x, hx, rfl⟩ := hzD
  have hxlt : ‖x‖ < 1 := by
    by_contra hn
    have hnorm : ‖x‖ = 1 := le_antisymm (mem_closedBall_zero_iff.mp hx) (le_of_not_gt hn)
    apply hz
    rw [hflat x hx]
    exact hboundary ⟨(x, 0), ⟨mem_sphere_zero_iff_norm.mpr hnorm, rfl⟩, rfl⟩
  let ψ := DifferentialGeometry.Topology.PartialDiffeomorph.restrict χ
    (ball (0 : EuclideanSpace ℝ (Fin 2)) 1) isOpen_ball
  have hxψ : x ∈ ψ.source := ⟨hχ hx, mem_ball_zero_iff.mpr hxlt⟩
  have hformula : ∀ y ∈ ψ.source, g (ψ y) = Ψ (y, 0) := by
    intro y hy
    exact hflat y (ball_subset_closedBall hy.2)
  exact embeddedSphereNormalChart_nonempty_of_isImmersionAtOfComplement hg
    (isImmersionAtOfComplement_of_flat_patch (by simp) ψ Ψ hformula hxψ)

end DifferentialGeometry.Topology.SphereSeparation
