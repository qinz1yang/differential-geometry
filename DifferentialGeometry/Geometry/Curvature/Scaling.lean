import DifferentialGeometry.Geometry.Curvature.Metric
import DifferentialGeometry.Geometry.Connection.LeviCivita.Scaling

set_option autoImplicit false
set_option linter.style.longLine false
set_option linter.unusedSectionVars false

/-!
# Constant metric scaling and curvature

Positive constant scaling leaves the Levi-Civita connection unchanged and
multiplies the lowered Riemann tensor by the same constant.
-/

noncomputable section

namespace DifferentialGeometry.Integral.Connection

open Bundle Tensor0SBundle
open scoped Manifold ContDiff

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
variable [FiniteDimensional Real E] [CompleteSpace E]
variable {H : Type*} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
variable [IsManifold I 1 M] [IsManifold I ((∞ : WithTop ℕ∞) + 1) M]
variable [SigmaCompactSpace M] [T2Space M]

/-- The canonical lowered Riemann tensor scales linearly under positive
constant metric scaling. -/
theorem metricRm_scale
    (c : Real) (hc : 0 < c) (g : SmoothRiemannianMetric I M) (x : M) :
    metricRm04 (I := I) (M := M) (scaleMetric (I := I) c hc g) x =
      c • metricRm04 (I := I) (M := M) g x := by
  ext v
  have hv :
      v = vec4 (I := I) (v 0) (v 1) (v 2) (v 3) := by
    funext i
    fin_cases i <;> simp [vec4]
  rw [hv]
  simp [metricRm04, metricCov, scaleMetric_inner, lcConn_scaleMetric,
    smul_eq_mul]

/-- Standard-slot evaluation of the constant-scaling curvature law. -/
theorem metricRmStd_scale
    (c : Real) (hc : 0 < c) (g : SmoothRiemannianMetric I M) (x : M)
    (X Y Z W : TangentSpace I x) :
    metricRm04StdAt (I := I) (M := M) (scaleMetric (I := I) c hc g)
        x X Y Z W =
      c * metricRm04StdAt (I := I) (M := M) g x X Y Z W := by
  have h := congrArg
    (fun Rm : Tensor04At (I := I) (M := M) x =>
      Rm (vec4 (I := I) X Y Z W))
    (metricRm_scale (I := I) c hc g x)
  simpa [metricRm04_apply, metricRm04StdAt_apply, smul_eq_mul] using h

end DifferentialGeometry.Integral.Connection
