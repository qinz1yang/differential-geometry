import DifferentialGeometry.Geometry.Riemannian.Curvature.ConstantSectional
import DifferentialGeometry.Geometry.Riemannian.Curvature.Bounds
import DifferentialGeometry.Analysis.Laplacian.MetricBounds

/-!
# Bridges between constant sectional curvature and sectional curvature bounds

This file ships two bridge theorems connecting `HasConstantSectionalCurvature`
to the one-sided sectional-curvature predicates `HasNonnegSectionalCurvature`
and `HasNonposSectionalCurvature`:

* `HasConstantSectionalCurvature.hasNonnegSectionalCurvature`: constant
  sectional curvature `K ≥ 0` implies nonnegative sectional curvature.
* `HasConstantSectionalCurvature.hasNonposSectionalCurvature`: constant
  sectional curvature `K ≤ 0` implies nonpositive sectional curvature.

Both bridges rest on the elementary observation that the Gram determinant
`|V|² |W|² − g(V, W)²` is nonnegative by the Cauchy-Schwarz inequality
applied to the metric inner product.
-/

set_option linter.unusedSectionVars false

noncomputable section

open Bundle Manifold Set
open scoped Manifold Topology ContDiff
open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Integral.Connection

namespace DifferentialGeometry
namespace Geometry
namespace Riemannian
namespace Curvature

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
variable [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M]

/-- The Gram determinant `|V|² |W|² − g(V, W)²` is nonnegative for every
pair of tangent vectors `V, W : T_x M`, by the Cauchy-Schwarz inequality
applied to the metric inner product. -/
private lemma gramDeterminant_nonneg
    (g : SmoothRiemannianMetric I M) (x : M)
    (V W : TangentSpace I x) :
    0 ≤ gramDeterminant (I := I) g x V W := by
  unfold gramDeterminant
  have hCS : (g.inner x V W) ^ 2 ≤ g.inner x V V * g.inner x W W :=
    DifferentialGeometry.Analysis.Laplacian.metric_inner_cauchy_schwarz_sq
      (I := I) (M := M) g x V W
  linarith

/-- A smooth Riemannian metric with constant sectional curvature `K ≥ 0`
has nonnegative sectional curvature. -/
theorem HasConstantSectionalCurvature.hasNonnegSectionalCurvature
    {g : SmoothRiemannianMetric I M} {K : ℝ}
    (h : HasConstantSectionalCurvature (I := I) g K) (hK : 0 ≤ K) :
    HasNonnegSectionalCurvature (I := I) g := by
  intro x V W
  rw [h x V W]
  exact mul_nonneg hK (gramDeterminant_nonneg (I := I) g x V W)

/-- A smooth Riemannian metric with constant sectional curvature `K ≤ 0`
has nonpositive sectional curvature. -/
theorem HasConstantSectionalCurvature.hasNonposSectionalCurvature
    {g : SmoothRiemannianMetric I M} {K : ℝ}
    (h : HasConstantSectionalCurvature (I := I) g K) (hK : K ≤ 0) :
    HasNonposSectionalCurvature (I := I) g := by
  intro x V W
  rw [h x V W]
  exact mul_nonpos_of_nonpos_of_nonneg hK (gramDeterminant_nonneg (I := I) g x V W)

end Curvature
end Riemannian
end Geometry
end DifferentialGeometry

end
