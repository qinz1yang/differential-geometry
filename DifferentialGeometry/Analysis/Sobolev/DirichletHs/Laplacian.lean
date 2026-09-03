import DifferentialGeometry.Analysis.Sobolev.DirichletHs.ExponentCongr

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

def dirichletHsLaplacianL2
    (g : SmoothRiemannianMetric (I_half n) M) :
    dirichletHs g 2 →L[ℝ] dirichletHs g 0 :=
  (dirichletHsLaplacian g 0).comp
    (dirichletHsCongrL g (by norm_num : (2 : ℝ) = 0 + 2))

@[simp] theorem dirichletHsLaplacianL2_coeff
    (v : dirichletHs g 2)
    (i : DirichletLaplacianEigenindex g) :
    (dirichletHsLaplacianL2 g v).coeff i =
      -dirichletLaplacianEigenvalue i * v.coeff i := by
  rw [dirichletHsLaplacianL2, ContinuousLinearMap.comp_apply,
    dirichletHsLaplacian_coeff, dirichletHsCongrL_coeff]

def dirichletHsOneSubLaplacian
    (g : SmoothRiemannianMetric (I_half n) M) (σ : ℝ) :
    dirichletHs g (σ + 2) →L[ℝ] dirichletHs g σ :=
  dirichletHsInclusion (by linarith) - dirichletHsLaplacian g σ

@[simp] theorem dirichletHsOneSubLaplacian_coeff
    (v : dirichletHs g (σ + 2))
    (i : DirichletLaplacianEigenindex g) :
    (dirichletHsOneSubLaplacian g σ v).coeff i =
      (1 + dirichletLaplacianEigenvalue i) * v.coeff i := by
  change v.coeff i - (-dirichletLaplacianEigenvalue i * v.coeff i) = _
  ring

def dirichletHsOneSubLaplacianL2
    (g : SmoothRiemannianMetric (I_half n) M) :
    dirichletHs g 2 →L[ℝ] dirichletHs g 0 :=
  dirichletHsInclusion (show (0 : ℝ) ≤ 2 by norm_num) -
    dirichletHsLaplacianL2 g

@[simp] theorem dirichletHsOneSubLaplacianL2_coeff
    (v : dirichletHs g 2)
    (i : DirichletLaplacianEigenindex g) :
    (dirichletHsOneSubLaplacianL2 g v).coeff i =
      (1 + dirichletLaplacianEigenvalue i) * v.coeff i := by
  simp only [dirichletHsOneSubLaplacianL2, sub_apply,
    dirichletHs.sub_coeff, dirichletHs.dirichletHsInclusion_coeff,
    dirichletHsLaplacianL2_coeff]
  ring

private theorem weight_neg_one_eigenvalue_mul_sq_le
    (v : dirichletHs g 1) (i : DirichletLaplacianEigenindex g) :
    dirichletSobolevWeight i (-1) *
        (-dirichletLaplacianEigenvalue i * v.coeff i) ^ 2 ≤
      dirichletSobolevWeight i 1 * (v.coeff i) ^ 2 := by
  have hbase : 0 < 1 + dirichletLaplacianEigenvalue i :=
    lt_of_lt_of_le one_pos
      (one_le_one_add_dirichletLaplacianEigenvalue i)
  have hcoeff : (1 + dirichletLaplacianEigenvalue i)⁻¹ *
      dirichletLaplacianEigenvalue i ^ 2 ≤
      1 + dirichletLaplacianEigenvalue i := by
    calc
      (1 + dirichletLaplacianEigenvalue i)⁻¹ *
          dirichletLaplacianEigenvalue i ^ 2 ≤
        (1 + dirichletLaplacianEigenvalue i)⁻¹ *
          (1 + dirichletLaplacianEigenvalue i) ^ 2 :=
        mul_le_mul_of_nonneg_left (eigenvalue_sq_le i) (inv_nonneg.mpr hbase.le)
      _ = 1 + dirichletLaplacianEigenvalue i := by
        field_simp [hbase.ne']
  unfold dirichletSobolevWeight
  rw [Real.rpow_neg_one, Real.rpow_one]
  calc
    (1 + dirichletLaplacianEigenvalue i)⁻¹ *
        (-dirichletLaplacianEigenvalue i * v.coeff i) ^ 2 =
      ((1 + dirichletLaplacianEigenvalue i)⁻¹ *
        dirichletLaplacianEigenvalue i ^ 2) * (v.coeff i) ^ 2 := by ring
    _ ≤ (1 + dirichletLaplacianEigenvalue i) * (v.coeff i) ^ 2 :=
      mul_le_mul_of_nonneg_right hcoeff (sq_nonneg _)

private theorem laplacianNegOneWeightedSummable
    (v : dirichletHs g 1) :
    Summable (fun i => dirichletSobolevWeight i (-1) *
      (-dirichletLaplacianEigenvalue i * v.coeff i) ^ 2) := by
  refine Summable.of_nonneg_of_le (fun i => ?_) (fun i => ?_)
    v.weighted_summable
  · exact mul_nonneg (dirichletSobolevWeight_nonneg i (-1)) (sq_nonneg _)
  · exact weight_neg_one_eigenvalue_mul_sq_le v i

private def laplacianNegOneFun (v : dirichletHs g 1) :
    dirichletHs g (-1) where
  coeff i := -dirichletLaplacianEigenvalue i * v.coeff i
  weighted_summable := laplacianNegOneWeightedSummable v

private theorem laplacianNegOneFun_add
    (v w : dirichletHs g 1) :
    laplacianNegOneFun (v + w) =
      laplacianNegOneFun v + laplacianNegOneFun w := by
  refine dirichletHs.ext (funext (fun i => ?_))
  simp only [laplacianNegOneFun, dirichletHs.add_coeff]
  ring

private theorem laplacianNegOneFun_smul (c : ℝ)
    (v : dirichletHs g 1) :
    laplacianNegOneFun (c • v) = c • laplacianNegOneFun v := by
  refine dirichletHs.ext (funext (fun i => ?_))
  simp only [laplacianNegOneFun, dirichletHs.smul_coeff]
  ring

private theorem norm_laplacianNegOneFun_le
    (v : dirichletHs g 1) :
    ‖laplacianNegOneFun v‖ ≤ ‖v‖ := by
  have hsq : ‖laplacianNegOneFun v‖ ^ 2 ≤ ‖v‖ ^ 2 := by
    rw [dirichletHs.norm_sq_eq_tsum, dirichletHs.norm_sq_eq_tsum]
    refine Summable.tsum_le_tsum (fun i => ?_)
      (laplacianNegOneFun v).weighted_summable v.weighted_summable
    exact weight_neg_one_eigenvalue_mul_sq_le v i
  have h := Real.sqrt_le_sqrt hsq
  rwa [Real.sqrt_sq (norm_nonneg _), Real.sqrt_sq (norm_nonneg _)] at h

def dirichletHsLaplacianNegOne
    (g : SmoothRiemannianMetric (I_half n) M) :
    dirichletHs g 1 →L[ℝ] dirichletHs g (-1) :=
  LinearMap.mkContinuous
    { toFun := laplacianNegOneFun
      map_add' := laplacianNegOneFun_add
      map_smul' := fun c v => laplacianNegOneFun_smul c v }
    1
    (fun v => by
      rw [one_mul]
      exact norm_laplacianNegOneFun_le v)

@[simp] theorem dirichletHsLaplacianNegOne_coeff
    (g : SmoothRiemannianMetric (I_half n) M)
    (u : dirichletHs g 1) (i : DirichletLaplacianEigenindex g) :
    (dirichletHsLaplacianNegOne g u).coeff i =
      -dirichletLaplacianEigenvalue i * u.coeff i := rfl

end Hs
end Sobolev
end Analysis
end DifferentialGeometry
