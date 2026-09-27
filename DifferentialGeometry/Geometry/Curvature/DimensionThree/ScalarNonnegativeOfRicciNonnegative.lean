import DifferentialGeometry.Geometry.Curvature.DimensionThree.Reconstruction.RicciControlsRiemann
import DifferentialGeometry.Geometry.Curvature.ScalarControlsRm
import DifferentialGeometry.Geometry.Metric.TensorInner.Tensor0S.Coordinates.MetricComparison
import DifferentialGeometry.Geometry.Operator.Laplacian.Rough

set_option autoImplicit false
noncomputable section
open scoped Topology

namespace DifferentialGeometry.Geometry.Curvature

open DifferentialGeometry.Geometry.Operator
open DifferentialGeometry.Tensor0SBundle
open scoped Manifold ContDiff BigOperators

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
variable [CompleteSpace E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
variable {x : M}

theorem metricScalarAt_nonnegative_of_ricci_nonnegative
    (g : SmoothRiemannianMetric I M) (x : M) (hdim : Module.finrank ℝ E = 3)
    (hRic : ∀ v : TangentSpace I x, 0 ≤ metricRicciAt (I := I) (M := M) g x (vec2 v v)) :
    0 ≤ metricScalarAt (I := I) (M := M) g x := by
  classical
  have hdimx : Module.finrank ℝ (TangentSpace I x) = 3 := hdim
  obtain ⟨B, hB⟩ := exists_orthonormalBasisAt (I := I) g x hdimx
  have hinvDelta : MetricInverseInBasis (I := I) g x B delta3 :=
    orthonormal_invBasis3 (I := I) g B hB
  have hinv : MetricInverseInBasis (I := I) g x B (identityInvMetric (Idx := Fin 3)) := by
    intro i j
    simpa [identityInvMetric, diagonalInvMetric, delta3] using hinvDelta i j
  have hscalar : metricScalarAt (I := I) (M := M) g x =
      ∑ i : Fin 3, metricRicciAt (I := I) (M := M) g x (vec2 (B i) (B i)) := by
    calc metricScalarAt (I := I) (M := M) g x =
        DifferentialGeometry.Geometry.Operator.metricTracePair0SAt (I := I) g
          (metricRicciAt (I := I) (M := M) g x) := metricScalarAt_def (I := I) g x
      _ = ∑ i : Fin 3, metricRicciAt (I := I) (M := M) g x (vec2 (B i) (B i)) := by
        rw [DifferentialGeometry.Geometry.Operator.metricTracePair0SAt_eq_sum_basis
          (I := I) g B (identityInvMetric (Idx := Fin 3)) hinv]
        simp [identityInvMetric, diagonalInvMetric]
  rw [hscalar]
  exact Finset.sum_nonneg fun i _ => hRic (B i)

end DifferentialGeometry.Geometry.Curvature
