import DifferentialGeometry.Geometry.Metric.UniversalCover.Curvature
import DifferentialGeometry.Geometry.Curvature.DimensionThree.ExteriorRank

set_option autoImplicit false

noncomputable section

namespace DifferentialGeometry.Geometry.Riemannian.Topology.UniversalCover

open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Curvature.DimensionThree
open scoped Manifold ContDiff

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [T2Space M] [LocallyPathConnectedSpace M] [SemilocallySimplyConnectedSpace M] [Inhabited M]

theorem metricCurvatureOperatorRankAt_lifted_eq
    (g : SmoothRiemannianMetric I M) (x' : UniversalCover M)
    (hdim : Module.finrank ℝ E = 3) :
    metricCurvatureOperatorRankAt (liftedMetric (I := I) g) x' hdim =
      metricCurvatureOperatorRankAt g (proj x') hdim := by
  obtain ⟨basis, horth⟩ := exists_orthonormalBasisAt g (proj x') hdim
  let e : TangentSpace I (proj x') ≃ₗ[ℝ] TangentSpace I x' :=
    (tangentSpaceModelContinuousLinearEquiv (I := I) (proj x')).toLinearEquiv.trans
      (tangentSpaceModelContinuousLinearEquiv (I := I) x').symm.toLinearEquiv
  let basis' := basis.map e
  have horth' : OrthonormalBasisAt (liftedMetric (I := I) g) x' basis' := by
    intro i j
    change g.inner (proj x') (basis i) (basis j) = _
    exact horth i j
  have hmatrix :
      curvatureOperatorMatrixAt (I := I) x' basis'
          (metricAlgebraicCurvatureTensorAt (I := I) (liftedMetric (I := I) g) x') =
        curvatureOperatorMatrixAt (I := I) (proj x') basis
          (metricAlgebraicCurvatureTensorAt (I := I) g (proj x')) := by
    ext i j
    change metricRm04StandardAt (liftedMetric (I := I) g) x'
        (basis (bivectorIndex3 i).1) (basis (bivectorIndex3 i).2)
        (basis (bivectorIndex3 j).2) (basis (bivectorIndex3 j).1) =
      metricRm04StandardAt g (proj x')
        (basis (bivectorIndex3 i).1) (basis (bivectorIndex3 i).2)
        (basis (bivectorIndex3 j).2) (basis (bivectorIndex3 j).1)
    exact metricRm_lifted g x' _ _ _ _
  exact (metricCurvatureOperatorRankAt_eq_matrix_rank_of_orthonormal
    (I := I) (liftedMetric (I := I) g) x' hdim basis' horth').trans
      ((congrArg Matrix.rank hmatrix).trans
        (metricCurvatureOperatorRankAt_eq_matrix_rank_of_orthonormal
          (I := I) g (proj x') hdim basis horth).symm)

theorem curvatureOperatorImageAt_finrank_liftedMetric
    (g : SmoothRiemannianMetric I M) (x' : UniversalCover M)
    (hdim : Module.finrank ℝ E = 3) :
    Module.finrank ℝ (curvatureOperatorImageAt (liftedMetric (I := I) g) x'
      ⟨metricRm04At (liftedMetric (I := I) g) x',
        metricRm04At_mem_algebraicCurvatureTensorSubmodule (liftedMetric (I := I) g) x'⟩) =
      Module.finrank ℝ (curvatureOperatorImageAt g (proj x')
        ⟨metricRm04At g (proj x'), metricRm04At_mem_algebraicCurvatureTensorSubmodule g (proj x')⟩) := by
  rw [← metricCurvatureOperatorRankAt_eq_curvatureOperatorImageAt_finrank _ x' hdim,
    metricCurvatureOperatorRankAt_lifted_eq g x' hdim]
  exact metricCurvatureOperatorRankAt_eq_curvatureOperatorImageAt_finrank g (proj x') hdim

end DifferentialGeometry.Geometry.Riemannian.Topology.UniversalCover
