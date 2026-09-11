import DifferentialGeometry.Geometry.Curvature.Algebraic.CurvatureOperatorCone
import DifferentialGeometry.Geometry.Curvature.Algebraic.TensorMetric
import DifferentialGeometry.Geometry.Curvature.DimensionThree.Reconstruction.RicciControlsRiemann
import DifferentialGeometry.Geometry.Metric.TensorInner.Cotangent.Riemannian
import DifferentialGeometry.Geometry.Metric.TensorInner.Fiber.MetricData
import DifferentialGeometry.Geometry.Curvature.Metric.Defs

set_option autoImplicit false

noncomputable section

open Bundle Manifold DifferentialGeometry
open DifferentialGeometry.Tensor0SBundle
open DifferentialGeometry.Geometry.Connection
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Operator
open scoped BigOperators ContDiff Manifold

namespace DifferentialGeometry.Geometry.Curvature

variable {E H M : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M]

private local instance : CompleteSpace E := FiniteDimensional.complete ℝ E

private theorem scalarControlsRm_lower
    (g : SmoothRiemannianMetric I M) (x : M) :
    Rm04LowersRm13At (I := I) g x (metricRm13At g x) (metricRm04At g x) := by
  simpa only [metricRm13_apply, metricRm04_apply] using
    (rm04LowersRm13At_of_realizes
      (I := I) g (leviCivitaConnectionOfMetric g)
      (metricRm13 g) (metricRm04 g)
      (metricCurvatureSections g).rm13Realizes
      (metricCurvatureSections g).rm04Realizes x)

private theorem scalarControlsRm_firstTrace
    (g : SmoothRiemannianMetric I M) (x : M)
    (B : Module.Basis (Fin 3) ℝ (TangentSpace I x))
    (hB : OrthonormalBasisAt (I := I) g x B) :
    RiemannFromRicci3DTraceDataAt g
      (-metricRicciAt g x) (-metricScalarAt g x) (metricRm04At g x) B := by
  have hcurv : AlgebraicCurvatureSymmetries3
      (standardRmCompAt B (metricRm04 g x)) :=
    algebraicCurvatureSymmetries3_standardRmCompAt_of_leviCivita_realizes
      (g := g) (Rm04 := metricRm04 g)
      (hRm04 := (metricCurvatureSections g).rm04Realizes) B
  have hinv : MetricInverseInBasis g x B delta3 :=
    orthonormal_invBasis3 g B hB
  have hRicFirst : RicciRealizesRm04FirstTraceAt
      (metricRicciAt g x) (metricRm04At g x) delta3 B :=
    ricciFirstTraceAt_of_rm13 g B delta3 hinv
      (metricRicciAt g x) (metricRm13At g x) (metricRm04At g x)
      (metricRicciAt_eq_trace g x) (scalarControlsRm_lower g x)
  have hScalar : ScalarRealizesRicciTraceAt
      (metricScalarAt g x) (metricRicciAt g x) delta3 B := by
    unfold ScalarRealizesRicciTraceAt
    exact metricTracePair0SAt_eq_sum_basis g B delta3 hinv (metricRicciAt g x)
  apply traceDataOfFirst hB
  · simpa only [metricRm04_apply] using hcurv
  · exact hRicFirst
  · exact hScalar

private theorem scalarControlsRm_ricci_nonneg
    (g : SmoothRiemannianMetric I M) (x : M)
    (B : Module.Basis (Fin 3) ℝ (TangentSpace I x))
    (hB : OrthonormalBasisAt (I := I) g x B)
    (hRm : metricAlgebraicCurvatureTensorAt g x ∈
      algebraicCurvatureOperatorNonnegativeCone) :
    RicciNonnegAt (I := I) (metricRicciAt g x) := by
  classical
  have hinv : MetricInverseInBasis g x B delta3 :=
    orthonormal_invBasis3 g B hB
  have hcoord (i : Fin 3) :
      B.coord i = tangentFlatLinear (I := I) g x (B i) := by
    ext v
    simpa [delta3, tangentFlatLinear_apply] using
      (basis_coord_eq_sum_inv_inner (I := I) g B delta3 hinv i v)
  have hsection (u v : TangentSpace I x) :
      0 ≤ metricRm04At g x (vec4 (I := I) u v v u) := by
    have h := (mem_algebraicCurvatureOperatorNonnegativeCone.mp hRm)
      1 (fun _ => 1) (fun _ => u) (fun _ => v)
    simpa only [algebraicCurvatureOperatorQuadraticEval,
      Fin.sum_univ_one, one_mul, tensor04StandardAt,
      metricAlgebraicCurvatureTensorAt_coe] using h
  intro v
  have htrace : metricRicciAt g x (vec2 (I := I) v v) =
      ∑ i : Fin 3, metricRm04At g x (vec4 (I := I) (B i) v v (B i)) := by
    rw [metricRicciAt_eq_trace,
      ricciFromRm13At_apply_basis_trace B (metricRm13At g x) v v]
    apply Finset.sum_congr rfl
    intro i _
    rw [hcoord i]
    exact (scalarControlsRm_lower g x (B i) v v (B i)).symm
  rw [htrace]
  exact Finset.sum_nonneg (fun i _ => hsection (B i) v)

theorem normSq_metricRm04_le_scalar_sq_of_curvatureOperator_nonnegative
    (g : SmoothRiemannianMetric I M) (x : M) (hdim : Module.finrank ℝ E = 3)
    (hRm : metricAlgebraicCurvatureTensorAt g x ∈
      algebraicCurvatureOperatorNonnegativeCone) :
    normSq0S g x 4 (metricRm04 g x) ≤ 100 ^ 2 * (metricScalarAt g x) ^ 2 := by
  have hdimx : Module.finrank ℝ (TangentSpace I x) = 3 := hdim
  obtain ⟨B, hB⟩ := exists_orthonormalBasisAt g x hdimx
  have hinv : MetricInverseInBasis g x B delta3 :=
    orthonormal_invBasis3 g B hB
  have hsymm : RicciSymAt (I := I) (metricRicciAt g x) :=
    ricciSym_of_basis B (metricRicciAt g x)
      (fun i j => metricRicciSymm g B delta3 hinv i j)
  have hnonneg := scalarControlsRm_ricci_nonneg g x B hB hRm
  have hbound := normSqLeOfFirstTrace (g := g)
    (Ric := metricRicciAt g x) (scalar := metricScalarAt g x)
    (Rm04 := metricRm04At g x) hdimx hsymm hnonneg
    (scalarControlsRm_firstTrace g x)
  simpa only [metricRm04_apply] using hbound

end DifferentialGeometry.Geometry.Curvature

end
