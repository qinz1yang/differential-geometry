import DifferentialGeometry.Geometry.Comparison.SphericalModelAngle

set_option autoImplicit false

namespace DifferentialGeometry.Geometry.Comparison.Toponogov

def fourPointSphericalComparison {X : Type*} [MetricSpace X] (Ω : Set X) : Prop :=
  ∀ p ∈ Ω, ∀ a ∈ Ω, ∀ b ∈ Ω, ∀ c ∈ Ω, a ≠ p → b ≠ p → c ≠ p →
    dist p a + dist p b + dist a b < 2 * Real.pi →
    dist p b + dist p c + dist b c < 2 * Real.pi →
    dist p c + dist p a + dist c a < 2 * Real.pi →
    sphericalComparisonAngle (dist p a) (dist p b) (dist a b) +
      sphericalComparisonAngle (dist p b) (dist p c) (dist b c) +
      sphericalComparisonAngle (dist p c) (dist p a) (dist c a) ≤ 2 * Real.pi

theorem fourPointSphericalComparison.mono {X : Type*} [MetricSpace X]
    {Ω V : Set X} (hΩ : fourPointSphericalComparison Ω) (hV : V ⊆ Ω) :
    fourPointSphericalComparison V := by
  intro p hp a ha b hb c hc hpa hpb hpc hab hbc hca
  exact hΩ p (hV hp) a (hV ha) b (hV hb) c (hV hc) hpa hpb hpc hab hbc hca

end DifferentialGeometry.Geometry.Comparison.Toponogov
