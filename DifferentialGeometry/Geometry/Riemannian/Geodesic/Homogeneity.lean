import DifferentialGeometry.Geometry.Riemannian.Geodesic.MaximalInterval

set_option linter.unusedSectionVars false

/-!
# Homogeneity closure lemmas for the maximal geodesic

Small algebraic closure facts about how `maximalGeodesic g p v t` reacts
to trivial scalar manipulations of the initial velocity `v` and the
time parameter `t`.

## Main lemmas

* `maximalGeodesic_smul_zero_time` — for any scalar `c : ℝ`, the maximal
  geodesic with initial velocity `c • v` evaluated at `t = 0` is the
  base point `p`. This is just `maximalGeodesic_zero` with the velocity
  argument specialised.

* `maximalGeodesic_one_velocity` — replacing the initial velocity `v`
  by `1 • v` does not change the curve: the maximal geodesic depends
  on `v` only up to the canonical action of `ℝ`, and `1 • v = v`.
-/

noncomputable section

open Bundle Manifold Set Filter Function
open scoped Manifold Topology ContDiff

namespace DifferentialGeometry
namespace Geometry
namespace Riemannian
namespace Geodesic

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [InnerProductSpace ℝ E]
  [Module.Finite ℝ E] [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

open DifferentialGeometry.Integral.Measure

section Homogeneity

variable [I.Boundaryless] [CompleteSpace E]

/-- The maximal geodesic with initial velocity `c • v` evaluated at time
`0` is the base point `p`. Specialisation of `maximalGeodesic_zero` to
the scaled velocity. -/
theorem maximalGeodesic_smul_zero_time
    (g : SmoothRiemannianMetric I M) (p : M) (v : TangentSpace I p) (c : ℝ) :
    maximalGeodesic (I := I) g p (c • v) 0 = p :=
  maximalGeodesic_zero (I := I) g p (c • v)

/-- Replacing the initial velocity `v` by `1 • v` leaves the maximal
geodesic unchanged. Direct from `one_smul`. -/
theorem maximalGeodesic_one_velocity
    (g : SmoothRiemannianMetric I M) (p : M) (v : TangentSpace I p) (t : ℝ) :
    maximalGeodesic (I := I) g p ((1 : ℝ) • v) t =
      maximalGeodesic (I := I) g p v t := by
  rw [one_smul]

end Homogeneity

end Geodesic
end Riemannian
end Geometry
end DifferentialGeometry

end
