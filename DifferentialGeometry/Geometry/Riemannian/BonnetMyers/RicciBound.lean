import DifferentialGeometry.Integral.Connection.Ricci
import DifferentialGeometry.Integral.Measure.ChartDensity

/-!
# The "Ric ≥ κ · g" predicate

This file introduces the predicate `RicciBoundedBelow g κ`, asserting that
the Ricci tensor of a smooth Riemannian metric `g` is bounded below by
`κ · g` as bilinear forms: for every point `x` and tangent vector `v` at
`x`, one has `κ · ⟨v, v⟩_g ≤ Ric(v, v)`.
-/

noncomputable section

open Bundle Manifold
open scoped Manifold Topology ContDiff
open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Integral.Connection

namespace DifferentialGeometry
namespace Geometry
namespace Riemannian
namespace BonnetMyers

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [I.Boundaryless]
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [T2Space M] [SigmaCompactSpace M]

/-- **Lower Ricci bound predicate.** The metric `g` has Ricci curvature bounded
below by `κ` (interpreted as `Ric ≥ κ · g` as bilinear forms) iff for every
point `x : M` and every tangent vector `v : T_x M`,
`κ · g(v, v) ≤ Ric_g(v, v)`. -/
def RicciBoundedBelow (g : SmoothRiemannianMetric I M) (κ : ℝ) : Prop :=
  ∀ (x : M) (v : TangentSpace I x), κ * (g.inner x v v : ℝ) ≤ ricciTensor (I := I) g x v v

end BonnetMyers
end Riemannian
end Geometry
end DifferentialGeometry

end
