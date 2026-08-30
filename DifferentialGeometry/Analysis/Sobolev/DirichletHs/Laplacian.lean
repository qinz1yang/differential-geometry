import DifferentialGeometry.Analysis.Sobolev.DirichletHs.Defs

noncomputable section

open Bundle Manifold MeasureTheory Set Filter
open scoped Manifold Topology ContDiff ENNReal BigOperators
  RealInnerProductSpace InnerProductSpace

namespace DifferentialGeometry
namespace Analysis
namespace Sobolev
namespace Hs

variable {n : ℕ} [NeZero n]
variable {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanHalfSpace n) M]
  [IsManifold (modelWithCornersEuclideanHalfSpace n) ∞ M]
  [T2Space M] [CompactSpace M]

private abbrev I_half (n : ℕ) [NeZero n] :
    ModelWithCorners ℝ (EuclideanSpace ℝ (Fin n)) (EuclideanHalfSpace n) :=
  modelWithCornersEuclideanHalfSpace n

open DifferentialGeometry.Analysis.Laplacian.WithBoundary.Dirichlet

variable {g : SmoothRiemannianMetric (I_half n) M} {σ : ℝ}

private theorem eigenvalue_sq_le
    (i : DirichletLaplacianEigenindex g) :
    (dirichletLaplacianEigenvalue i) ^ 2 ≤
      (1 + dirichletLaplacianEigenvalue i) ^ 2 := by
  have hlam := dirichletLaplacianEigenvalue_nonneg i
  nlinarith

private theorem sobolevWeight_mul_two
    (i : DirichletLaplacianEigenindex g) :
    dirichletSobolevWeight i σ *
        (1 + dirichletLaplacianEigenvalue i) ^ 2 =
      dirichletSobolevWeight i (σ + 2) := by
  have hbase_pos : (0 : ℝ) < 1 + dirichletLaplacianEigenvalue i :=
    lt_of_lt_of_le one_pos
      (one_le_one_add_dirichletLaplacianEigenvalue i)
  rw [dirichletSobolevWeight, dirichletSobolevWeight,
    ← Real.rpow_natCast (1 + dirichletLaplacianEigenvalue i) 2,
    ← Real.rpow_add hbase_pos]
  norm_num

private theorem weight_eigenvalue_mul_sq_le
    (v : dirichletHs g (σ + 2))
    (i : DirichletLaplacianEigenindex g) :
    dirichletSobolevWeight i σ *
        (-dirichletLaplacianEigenvalue i * v.coeff i) ^ 2 ≤
      dirichletSobolevWeight i (σ + 2) * (v.coeff i) ^ 2 := by
  have hw_nonneg : 0 ≤ dirichletSobolevWeight i σ :=
    dirichletSobolevWeight_nonneg i σ
  have hsq : (-dirichletLaplacianEigenvalue i * v.coeff i) ^ 2 ≤
      (1 + dirichletLaplacianEigenvalue i) ^ 2 * (v.coeff i) ^ 2 := by
    have h := eigenvalue_sq_le i
    nlinarith [sq_nonneg (v.coeff i), h]
  calc dirichletSobolevWeight i σ *
          (-dirichletLaplacianEigenvalue i * v.coeff i) ^ 2
      ≤ dirichletSobolevWeight i σ *
          ((1 + dirichletLaplacianEigenvalue i) ^ 2 *
            (v.coeff i) ^ 2) := mul_le_mul_of_nonneg_left hsq hw_nonneg
    _ = dirichletSobolevWeight i (σ + 2) * (v.coeff i) ^ 2 := by
        rw [← mul_assoc, sobolevWeight_mul_two i]

private theorem laplacianWeightedSummable
    (v : dirichletHs g (σ + 2)) :
    Summable (fun i => dirichletSobolevWeight i σ *
      (-dirichletLaplacianEigenvalue i * v.coeff i) ^ 2) := by
  refine Summable.of_nonneg_of_le (fun i => ?_) (fun i => ?_)
    v.weighted_summable
  · exact mul_nonneg (dirichletSobolevWeight_nonneg i σ) (sq_nonneg _)
  · exact weight_eigenvalue_mul_sq_le v i

private def laplacianFun (v : dirichletHs g (σ + 2)) :
    dirichletHs g σ where
  coeff i := -dirichletLaplacianEigenvalue i * v.coeff i
  weighted_summable := laplacianWeightedSummable v

private theorem laplacianFun_add
    (v w : dirichletHs g (σ + 2)) :
    laplacianFun (v + w) = laplacianFun v + laplacianFun w := by
  refine dirichletHs.ext (funext (fun i => ?_))
  simp only [laplacianFun, dirichletHs.add_coeff]
  ring

private theorem laplacianFun_smul (c : ℝ)
    (v : dirichletHs g (σ + 2)) :
    laplacianFun (c • v) = c • laplacianFun v := by
  refine dirichletHs.ext (funext (fun i => ?_))
  simp only [laplacianFun, dirichletHs.smul_coeff]
  ring

private theorem norm_laplacianFun_le
    (v : dirichletHs g (σ + 2)) :
    ‖laplacianFun v‖ ≤ ‖v‖ := by
  have hsq : ‖laplacianFun v‖ ^ 2 ≤ ‖v‖ ^ 2 := by
    rw [dirichletHs.norm_sq_eq_tsum, dirichletHs.norm_sq_eq_tsum]
    refine Summable.tsum_le_tsum (fun i => ?_)
      (laplacianFun v).weighted_summable v.weighted_summable
    exact weight_eigenvalue_mul_sq_le v i
  have h := Real.sqrt_le_sqrt hsq
  rwa [Real.sqrt_sq (norm_nonneg _), Real.sqrt_sq (norm_nonneg _)] at h

def dirichletHsLaplacian (g : SmoothRiemannianMetric (I_half n) M)
    (σ : ℝ) : dirichletHs g (σ + 2) →L[ℝ] dirichletHs g σ :=
  LinearMap.mkContinuous
    { toFun := laplacianFun
      map_add' := laplacianFun_add
      map_smul' := fun c v => laplacianFun_smul c v }
    1
    (fun v => by
      rw [one_mul]
      exact norm_laplacianFun_le v)

@[simp] theorem dirichletHsLaplacian_coeff
    (v : dirichletHs g (σ + 2))
    (i : DirichletLaplacianEigenindex g) :
    (dirichletHsLaplacian g σ v).coeff i =
      -dirichletLaplacianEigenvalue i * v.coeff i := rfl

theorem dirichletHsLaplacian_norm_le
    (v : dirichletHs g (σ + 2)) :
    ‖dirichletHsLaplacian g σ v‖ ≤ ‖v‖ :=
  norm_laplacianFun_le v

theorem dirichletHsLaplacian_opNorm_le_one :
    ‖dirichletHsLaplacian g σ‖ ≤ 1 :=
  ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun v => by
    rw [one_mul]
    exact dirichletHsLaplacian_norm_le v

end Hs
end Sobolev
end Analysis
end DifferentialGeometry
