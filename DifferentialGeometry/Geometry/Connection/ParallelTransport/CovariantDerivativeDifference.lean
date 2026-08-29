import DifferentialGeometry.Geometry.Connection.ConnectionDifference
import DifferentialGeometry.Geometry.Connection.ParallelTransport.PullbackNaturality
import DifferentialGeometry.Geometry.Curvature.Metric

set_option autoImplicit false

noncomputable section

open Set Function Filter Bundle Manifold
open scoped Manifold ContDiff Topology
open DifferentialGeometry.Geometry.Connection
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Riemannian.AlongCurve

namespace DifferentialGeometry.Geometry.Riemannian.CovariantDerivativeAlong

universe uE uH uM

variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace Real E]
  [FiniteDimensional Real E] [CompleteSpace E]
  [NeZero (Module.finrank Real E)]
variable {H : Type uH} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H}
variable {M : Type uM} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [T2Space M] [SigmaCompactSpace M]
  [BoundarylessManifold I M]

omit [NeZero (Module.finrank Real E)] [SigmaCompactSpace M] in
theorem covAlong_diff
    (g₁ g₂ : SmoothRiemannianMetric I M) (gamma : Real → M)
    (V : ∀ r, TangentSpace I (gamma r)) (t : Real)
    (hgamma : MDifferentiableAt (modelWithCornersSelf Real Real) I gamma t) :
    covDerivAlong (I := I) g₁ gamma V t -
        covDerivAlong (I := I) g₂ gamma V t =
      (CovariantDerivative.difference
        (metricCov (I := I) g₁) (metricCov (I := I) g₂) (gamma t))
        (V t)
        ((mfderiv (modelWithCornersSelf Real Real) I gamma t :
          Real →L[Real] TangentSpace I (gamma t)) (1 : Real)) := by
  classical
  obtain ⟨Y, hY⟩ := ContMDiffSection.exists_eq_at
    (I := I) (F := E) (V := TangentSpace I) (n := (⊤ : ℕ∞))
    (gamma t) (V t)
  let W : ∀ r, TangentSpace I (gamma r) := fun r ↦ Y (gamma r)
  have hrep : chartRepAt (I := I) gamma V t t =
      chartRepAt (I := I) gamma W t t := by
    simp only [chartRepAt_apply, W, hY]
  have hfield :
      covDerivAlong (I := I) g₁ gamma V t -
          covDerivAlong (I := I) g₂ gamma V t =
        covDerivAlong (I := I) g₁ gamma W t -
          covDerivAlong (I := I) g₂ gamma W t := by
    simp only [covDerivAlong_def, ← map_sub]
    congr 1
    simp only [chartCovDerivAlong_def]
    rw [hrep]
    abel
  rw [hfield, covAlong_sec (I := I) g₁ gamma Y t hgamma,
    covAlong_sec (I := I) g₂ gamma Y t hgamma]
  have hdiff := DifferentialGeometry.PDE.DeTurck.connectionDifference_apply
    (I := I) g₁ g₂ Y.mdifferentiableAt
    ((mfderiv (modelWithCornersSelf Real Real) I gamma t :
      Real →L[Real] TangentSpace I (gamma t)) (1 : Real))
  simpa only [DifferentialGeometry.PDE.DeTurck.connectionDifference, metricCov,
    LeviCivita, hY] using hdiff.symm

end DifferentialGeometry.Geometry.Riemannian.CovariantDerivativeAlong
