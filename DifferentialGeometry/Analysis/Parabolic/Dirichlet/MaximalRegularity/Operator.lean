import DifferentialGeometry.Analysis.Parabolic.MaximalRegularity.PerModeL2
import DifferentialGeometry.Analysis.Parabolic.Dirichlet.MaximalRegularity.Synthesis

noncomputable section

open Bundle Manifold MeasureTheory Set Filter
open scoped Manifold Topology ContDiff ENNReal BigOperators
  RealInnerProductSpace InnerProductSpace

namespace DifferentialGeometry
namespace Analysis
namespace Parabolic
namespace Dirichlet
namespace MaximalRegularity

variable {n : ℕ} [NeZero n]
variable {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanHalfSpace n) M]
  [IsManifold (modelWithCornersEuclideanHalfSpace n) ∞ M]
  [T2Space M] [CompactSpace M]

private abbrev I_half (n : ℕ) [NeZero n] :
    ModelWithCorners ℝ (EuclideanSpace ℝ (Fin n)) (EuclideanHalfSpace n) :=
  modelWithCornersEuclideanHalfSpace n

open DifferentialGeometry.Integral.L2
open DifferentialGeometry.Analysis.Laplacian.WithBoundary.Dirichlet
open DifferentialGeometry.Analysis.Parabolic.MaximalRegularity
  (perModeConvL2 perModeConvDerivL2 perModeConvL2_apply
    norm_perModeConvL2Fun_le perModeConvL2_sq_le perModeConvDerivL2_sq_le)
open DifferentialGeometry.Analysis.Parabolic.TimeSobolev
open DifferentialGeometry.Analysis.Sobolev.Hs

variable {g : SmoothRiemannianMetric (I_half n) M}
variable {a : ℝ} {T : ℝ}

def solModeCoeff (hT : 0 ≤ T)
    (f : timeL2 (DirichletHs g a) T)
    (i : DirichletLaplacianEigenIndex g) : timeL2 ℝ T :=
  perModeConvL2 (dirichletLaplacianEigenvalue i)
    (dirichletLaplacianEigenvalue_nonneg i) hT
    (timeModeCoeff f i)

def derivModeCoeff (hT : 0 ≤ T)
    (f : timeL2 (DirichletHs g a) T)
    (i : DirichletLaplacianEigenIndex g) : timeL2 ℝ T :=
  perModeConvDerivL2 (dirichletLaplacianEigenvalue i)
    (dirichletLaplacianEigenvalue_nonneg i) hT
    (timeModeCoeff f i)

private theorem norm_solModeCoeff_le (hT : 0 ≤ T)
    (f : timeL2 (DirichletHs g a) T)
    (i : DirichletLaplacianEigenIndex g) :
    ‖solModeCoeff (a := a) hT f i‖ ≤
      T * ‖timeModeCoeff f i‖ := by
  rw [solModeCoeff, perModeConvL2_apply]
  exact norm_perModeConvL2Fun_le (dirichletLaplacianEigenvalue i)
    (dirichletLaplacianEigenvalue_nonneg i) hT _

private theorem lambda_mul_norm_solModeCoeff_le (hT : 0 ≤ T)
    (f : timeL2 (DirichletHs g a) T)
    (i : DirichletLaplacianEigenIndex g) :
    dirichletLaplacianEigenvalue i *
        ‖solModeCoeff (a := a) hT f i‖ ≤
      ‖timeModeCoeff f i‖ := by
  have hbase := perModeConvL2_sq_le (dirichletLaplacianEigenvalue i)
    (dirichletLaplacianEigenvalue_nonneg i) hT
    (timeModeCoeff f i)
  rw [norm_smul, Real.norm_eq_abs,
    abs_of_nonneg (dirichletLaplacianEigenvalue_nonneg i)] at hbase
  exact hbase

private theorem one_add_lambda_mul_norm_solModeCoeff_le (hT : 0 ≤ T)
    (f : timeL2 (DirichletHs g a) T)
    (i : DirichletLaplacianEigenIndex g) :
    (1 + dirichletLaplacianEigenvalue i) *
        ‖solModeCoeff (a := a) hT f i‖ ≤
      (1 + T) * ‖timeModeCoeff f i‖ := by
  have h1 := norm_solModeCoeff_le (a := a) hT f i
  have h2 := lambda_mul_norm_solModeCoeff_le (a := a) hT f i
  have hexpand : (1 + dirichletLaplacianEigenvalue i) *
        ‖solModeCoeff (a := a) hT f i‖
      = ‖solModeCoeff (a := a) hT f i‖ +
        dirichletLaplacianEigenvalue i *
          ‖solModeCoeff (a := a) hT f i‖ := by ring
  rw [hexpand]
  calc ‖solModeCoeff (a := a) hT f i‖ +
        dirichletLaplacianEigenvalue i *
          ‖solModeCoeff (a := a) hT f i‖
      ≤ T * ‖timeModeCoeff f i‖ +
          ‖timeModeCoeff f i‖ := by gcongr
    _ = (1 + T) * ‖timeModeCoeff f i‖ := by ring

private theorem sqrt_lambda_mul_norm_solModeCoeff_le (hT : 0 ≤ T)
    (f : timeL2 (DirichletHs g a) T)
    (i : DirichletLaplacianEigenIndex g) :
    Real.sqrt (dirichletLaplacianEigenvalue i) *
        ‖solModeCoeff (a := a) hT f i‖ ≤
      Real.sqrt T * ‖timeModeCoeff f i‖ := by
  set lam := dirichletLaplacianEigenvalue i with hlam_def
  have hlam_nn : 0 ≤ lam := dirichletLaplacianEigenvalue_nonneg i
  set φ := ‖solModeCoeff (a := a) hT f i‖ with hφ_def
  set ff := ‖timeModeCoeff f i‖ with hff_def
  have hφ_nn : 0 ≤ φ := norm_nonneg _
  have hff_nn : 0 ≤ ff := norm_nonneg _
  have h1 : φ ≤ T * ff := norm_solModeCoeff_le (a := a) hT f i
  have h2 : lam * φ ≤ ff :=
    lambda_mul_norm_solModeCoeff_le (a := a) hT f i
  have hlhs_nn : 0 ≤ Real.sqrt lam * φ :=
    mul_nonneg (Real.sqrt_nonneg _) hφ_nn
  have hrhs_nn : 0 ≤ Real.sqrt T * ff :=
    mul_nonneg (Real.sqrt_nonneg _) hff_nn
  have hsqL : (Real.sqrt lam * φ) ^ 2 = lam * φ * φ := by
    rw [mul_pow, Real.sq_sqrt hlam_nn]; ring
  have hsqR : (Real.sqrt T * ff) ^ 2 = T * ff * ff := by
    rw [mul_pow, Real.sq_sqrt hT]; ring
  have hsq_le : (Real.sqrt lam * φ) ^ 2 ≤ (Real.sqrt T * ff) ^ 2 := by
    rw [hsqL, hsqR]
    calc lam * φ * φ ≤ ff * φ := mul_le_mul_of_nonneg_right h2 hφ_nn
      _ ≤ ff * (T * ff) := mul_le_mul_of_nonneg_left h1 hff_nn
      _ = T * ff * ff := by ring
  nlinarith [hsq_le, hlhs_nn, hrhs_nn]

private theorem one_add_lambda_sqrt_mul_norm_solModeCoeff_le
    (hT : 0 < T) (hT1 : T ≤ 1)
    (f : timeL2 (DirichletHs g a) T)
    (i : DirichletLaplacianEigenIndex g) :
    (1 + dirichletLaplacianEigenvalue i) ^ (1 / 2 : ℝ) *
        ‖solModeCoeff (a := a) hT.le f i‖ ≤
      2 * Real.sqrt T * ‖timeModeCoeff f i‖ := by
  set lam := dirichletLaplacianEigenvalue i with hlam_def
  have hlam_nn : 0 ≤ lam := dirichletLaplacianEigenvalue_nonneg i
  have hbase_nn : (0 : ℝ) ≤ 1 + lam := by linarith
  set φ := ‖solModeCoeff (a := a) hT.le f i‖ with hφ_def
  set ff := ‖timeModeCoeff f i‖ with hff_def
  have hφ_nn : 0 ≤ φ := norm_nonneg _
  have hff_nn : 0 ≤ ff := norm_nonneg _
  have hsqrt_le : (1 + lam) ^ (1 / 2 : ℝ) ≤ 1 + Real.sqrt lam := by
    have hrw : (1 + lam) ^ (1 / 2 : ℝ) = Real.sqrt (1 + lam) := by
      rw [Real.sqrt_eq_rpow]
    rw [hrw]
    have hsl_nn : 0 ≤ Real.sqrt lam := Real.sqrt_nonneg _
    have hrhs_nn : 0 ≤ 1 + Real.sqrt lam := by linarith
    have hsl_sq : Real.sqrt lam ^ 2 = lam := Real.sq_sqrt hlam_nn
    rw [show (1 + Real.sqrt lam) = Real.sqrt ((1 + Real.sqrt lam) ^ 2) from
      (Real.sqrt_sq hrhs_nn).symm]
    refine Real.sqrt_le_sqrt ?_
    nlinarith [hsl_nn, hsl_sq]
  have hconv : φ ≤ Real.sqrt T * ff := by
    have hTle : T ≤ Real.sqrt T := by
      have hsqrt_ge : Real.sqrt T * Real.sqrt T = T := Real.mul_self_sqrt hT.le
      have hsqrt_le_one : Real.sqrt T ≤ 1 :=
        Real.sqrt_le_one.mpr hT1
      nlinarith [Real.sqrt_nonneg T, hsqrt_ge, hsqrt_le_one]
    calc φ ≤ T * ff := norm_solModeCoeff_le (a := a) hT.le f i
      _ ≤ Real.sqrt T * ff := mul_le_mul_of_nonneg_right hTle hff_nn
  have hhalf : Real.sqrt lam * φ ≤ Real.sqrt T * ff :=
    sqrt_lambda_mul_norm_solModeCoeff_le (a := a) hT.le f i
  calc (1 + lam) ^ (1 / 2 : ℝ) * φ
      ≤ (1 + Real.sqrt lam) * φ := mul_le_mul_of_nonneg_right hsqrt_le hφ_nn
    _ = φ + Real.sqrt lam * φ := by ring
    _ ≤ Real.sqrt T * ff + Real.sqrt T * ff := by gcongr
    _ = 2 * Real.sqrt T * ff := by ring

private theorem norm_derivModeCoeff_le (hT : 0 ≤ T)
    (f : timeL2 (DirichletHs g a) T)
    (i : DirichletLaplacianEigenIndex g) :
    ‖derivModeCoeff (a := a) hT f i‖ ≤
      2 * ‖timeModeCoeff f i‖ :=
  perModeConvDerivL2_sq_le (dirichletLaplacianEigenvalue i)
    (dirichletLaplacianEigenvalue_nonneg i) hT
    (timeModeCoeff f i)

private theorem dirichletSobolevWeight_add_two
    (i : DirichletLaplacianEigenIndex g) (σ : ℝ) :
    dirichletSobolevWeight i (σ + 2) =
      dirichletSobolevWeight i σ *
        (1 + dirichletLaplacianEigenvalue i) ^ 2 := by
  have hbase_pos : (0 : ℝ) < 1 + dirichletLaplacianEigenvalue i :=
    lt_of_lt_of_le one_pos (one_le_one_add_dirichletLaplacianEigenvalue i)
  rw [dirichletSobolevWeight, dirichletSobolevWeight, Real.rpow_add hbase_pos,
    show ((2 : ℝ)) = ((2 : ℕ) : ℝ) from by norm_num, Real.rpow_natCast]

private theorem weighted_solModeCoeff_le (hT : 0 ≤ T)
    (f : timeL2 (DirichletHs g a) T)
    (i : DirichletLaplacianEigenIndex g) :
    dirichletSobolevWeight i (a + 2) *
        ‖solModeCoeff (a := a) hT f i‖ ^ 2 ≤
      (1 + T) ^ 2 * (dirichletSobolevWeight i a *
        ‖timeModeCoeff f i‖ ^ 2) := by
  have hperMode := one_add_lambda_mul_norm_solModeCoeff_le
    (a := a) hT f i
  have hwa_nonneg : 0 ≤ dirichletSobolevWeight i a :=
    dirichletSobolevWeight_nonneg i a
  have hlam_nonneg : 0 ≤ 1 + dirichletLaplacianEigenvalue i := by
    have := dirichletLaplacianEigenvalue_nonneg i; linarith
  have hsol_nonneg : 0 ≤ ‖solModeCoeff (a := a) hT f i‖ :=
    norm_nonneg _
  have hsq : ((1 + dirichletLaplacianEigenvalue i) *
        ‖solModeCoeff (a := a) hT f i‖) ^ 2 ≤
      ((1 + T) * ‖timeModeCoeff f i‖) ^ 2 := by
    have hrhs_nonneg : 0 ≤ (1 + T) * ‖timeModeCoeff f i‖ :=
      mul_nonneg (by linarith) (norm_nonneg _)
    have hlhs_nonneg : 0 ≤ (1 + dirichletLaplacianEigenvalue i) *
        ‖solModeCoeff (a := a) hT f i‖ :=
      mul_nonneg hlam_nonneg hsol_nonneg
    nlinarith [hperMode, hlhs_nonneg, hrhs_nonneg]
  calc dirichletSobolevWeight i (a + 2) *
          ‖solModeCoeff (a := a) hT f i‖ ^ 2
      = dirichletSobolevWeight i a *
          (((1 + dirichletLaplacianEigenvalue i) *
            ‖solModeCoeff (a := a) hT f i‖) ^ 2) := by
        rw [dirichletSobolevWeight_add_two i a]; ring
    _ ≤ dirichletSobolevWeight i a *
          (((1 + T) * ‖timeModeCoeff f i‖) ^ 2) :=
        mul_le_mul_of_nonneg_left hsq hwa_nonneg
    _ = (1 + T) ^ 2 * (dirichletSobolevWeight i a *
          ‖timeModeCoeff f i‖ ^ 2) := by ring

private theorem dirichletSobolevWeight_add_one
    (i : DirichletLaplacianEigenIndex g) (σ : ℝ) :
    dirichletSobolevWeight i (σ + 1) =
      dirichletSobolevWeight i σ *
        (1 + dirichletLaplacianEigenvalue i) := by
  have hbase_pos : (0 : ℝ) < 1 + dirichletLaplacianEigenvalue i :=
    lt_of_lt_of_le one_pos (one_le_one_add_dirichletLaplacianEigenvalue i)
  rw [dirichletSobolevWeight, dirichletSobolevWeight, Real.rpow_add hbase_pos,
    Real.rpow_one]

private theorem weighted_solModeCoeff_Ha1_le (hT : 0 < T) (hT1 : T ≤ 1)
    (f : timeL2 (DirichletHs g a) T)
    (i : DirichletLaplacianEigenIndex g) :
    dirichletSobolevWeight i (a + 1) *
        ‖solModeCoeff (a := a) hT.le f i‖ ^ 2 ≤
      (2 * Real.sqrt T) ^ 2 * (dirichletSobolevWeight i a *
        ‖timeModeCoeff f i‖ ^ 2) := by
  set lam := dirichletLaplacianEigenvalue i with hlam_def
  have hlam_nn : 0 ≤ lam := dirichletLaplacianEigenvalue_nonneg i
  have hbase_nn : (0 : ℝ) ≤ 1 + lam := by linarith
  have hperMode := one_add_lambda_sqrt_mul_norm_solModeCoeff_le
    (a := a) hT hT1 f i
  have hwa_nonneg : 0 ≤ dirichletSobolevWeight i a :=
    dirichletSobolevWeight_nonneg i a
  have hsol_nonneg : 0 ≤ ‖solModeCoeff (a := a) hT.le f i‖ :=
    norm_nonneg _
  have hweight_sq : (1 + lam) = ((1 + lam) ^ (1 / 2 : ℝ)) ^ 2 := by
    rw [← Real.rpow_natCast ((1 + lam) ^ (1 / 2 : ℝ)) 2, ← Real.rpow_mul hbase_nn]
    norm_num
  have hsq : ((1 + lam) ^ (1 / 2 : ℝ) *
        ‖solModeCoeff (a := a) hT.le f i‖) ^ 2 ≤
      (2 * Real.sqrt T * ‖timeModeCoeff f i‖) ^ 2 := by
    have hlhs_nonneg : 0 ≤ (1 + lam) ^ (1 / 2 : ℝ) *
        ‖solModeCoeff (a := a) hT.le f i‖ :=
      mul_nonneg (Real.rpow_nonneg hbase_nn _) hsol_nonneg
    have hrhs_nonneg : 0 ≤ 2 * Real.sqrt T *
        ‖timeModeCoeff f i‖ :=
      mul_nonneg (by positivity) (norm_nonneg _)
    nlinarith [hperMode, hlhs_nonneg, hrhs_nonneg]
  calc dirichletSobolevWeight i (a + 1) *
          ‖solModeCoeff (a := a) hT.le f i‖ ^ 2
      = dirichletSobolevWeight i a *
          (((1 + lam) ^ (1 / 2 : ℝ) *
            ‖solModeCoeff (a := a) hT.le f i‖) ^ 2) := by
        rw [dirichletSobolevWeight_add_one i a, hlam_def]
        rw [mul_pow]
        rw [← hweight_sq]; ring
    _ ≤ dirichletSobolevWeight i a *
          ((2 * Real.sqrt T *
            ‖timeModeCoeff f i‖) ^ 2) :=
        mul_le_mul_of_nonneg_left hsq hwa_nonneg
    _ = (2 * Real.sqrt T) ^ 2 * (dirichletSobolevWeight i a *
          ‖timeModeCoeff f i‖ ^ 2) := by ring

private theorem summable_solModeCoeff_Ha1 (hT : 0 < T) (hT1 : T ≤ 1)
    (f : timeL2 (DirichletHs g a) T) :
    Summable (fun i => dirichletSobolevWeight i (a + 1) *
      ‖solModeCoeff (a := a) hT.le f i‖ ^ 2) := by
  have hdom : Summable (fun i => (2 * Real.sqrt T) ^ 2 *
      (dirichletSobolevWeight i a *
        ‖timeModeCoeff f i‖ ^ 2)) :=
    (summable_weight_mul_norm_timeModeCoeff_sq
      (f := f)).mul_left _
  refine Summable.of_nonneg_of_le (fun i => ?_) (fun i => ?_) hdom
  · exact mul_nonneg (dirichletSobolevWeight_nonneg i (a + 1))
      (sq_nonneg _)
  · exact weighted_solModeCoeff_Ha1_le (a := a) hT hT1 f i

private theorem summable_solModeCoeff (hT : 0 ≤ T)
    (f : timeL2 (DirichletHs g a) T) :
    Summable (fun i => dirichletSobolevWeight i (a + 2) *
      ‖solModeCoeff (a := a) hT f i‖ ^ 2) := by
  have hdom : Summable (fun i => (1 + T) ^ 2 *
      (dirichletSobolevWeight i a *
        ‖timeModeCoeff f i‖ ^ 2)) :=
    (summable_weight_mul_norm_timeModeCoeff_sq
      (f := f)).mul_left _
  refine Summable.of_nonneg_of_le (fun i => ?_) (fun i => ?_) hdom
  · exact mul_nonneg (dirichletSobolevWeight_nonneg i (a + 2))
      (sq_nonneg _)
  · exact weighted_solModeCoeff_le (a := a) hT f i

private theorem weighted_derivModeCoeff_le (hT : 0 ≤ T)
    (f : timeL2 (DirichletHs g a) T)
    (i : DirichletLaplacianEigenIndex g) :
    dirichletSobolevWeight i a *
        ‖derivModeCoeff (a := a) hT f i‖ ^ 2 ≤
      2 ^ 2 * (dirichletSobolevWeight i a *
        ‖timeModeCoeff f i‖ ^ 2) := by
  have hbase := norm_derivModeCoeff_le (a := a) hT f i
  have hwa_nonneg : 0 ≤ dirichletSobolevWeight i a :=
    dirichletSobolevWeight_nonneg i a
  have hsq : ‖derivModeCoeff (a := a) hT f i‖ ^ 2 ≤
      2 ^ 2 * ‖timeModeCoeff f i‖ ^ 2 := by
    nlinarith [hbase, norm_nonneg (derivModeCoeff (a := a) hT f i),
      norm_nonneg (timeModeCoeff f i)]
  calc dirichletSobolevWeight i a *
          ‖derivModeCoeff (a := a) hT f i‖ ^ 2
      ≤ dirichletSobolevWeight i a *
          (2 ^ 2 * ‖timeModeCoeff f i‖ ^ 2) :=
        mul_le_mul_of_nonneg_left hsq hwa_nonneg
    _ = 2 ^ 2 * (dirichletSobolevWeight i a *
          ‖timeModeCoeff f i‖ ^ 2) := by ring

private theorem summable_derivModeCoeff (hT : 0 ≤ T)
    (f : timeL2 (DirichletHs g a) T) :
    Summable (fun i => dirichletSobolevWeight i a *
      ‖derivModeCoeff (a := a) hT f i‖ ^ 2) := by
  have hdom : Summable (fun i => 2 ^ 2 *
      (dirichletSobolevWeight i a *
        ‖timeModeCoeff f i‖ ^ 2)) :=
    (summable_weight_mul_norm_timeModeCoeff_sq
      (f := f)).mul_left _
  refine Summable.of_nonneg_of_le (fun i => ?_) (fun i => ?_) hdom
  · exact mul_nonneg (dirichletSobolevWeight_nonneg i a)
      (sq_nonneg _)
  · exact weighted_derivModeCoeff_le (a := a) hT f i

def maximalRegularityDerivField (a : ℝ) {T : ℝ} (hT : 0 ≤ T)
    (f : timeL2 (DirichletHs g a) T) :
    timeL2 (DirichletHs g a) T :=
  timeL2OfModes
    (fun i => derivModeCoeff (a := a) hT f i)

theorem maximalRegularityDerivField_timeModeCoeff (hT : 0 ≤ T)
    (f : timeL2 (DirichletHs g a) T)
    (i : DirichletLaplacianEigenIndex g) :
    timeModeCoeff
        (maximalRegularityDerivField a hT f) i =
      derivModeCoeff (a := a) hT f i :=
  timeL2OfModes_timeModeCoeff _
    (summable_derivModeCoeff (a := a) hT f) i

def maximalRegularitySolField (a : ℝ) {T : ℝ} (hT : 0 ≤ T)
    (f : timeL2 (DirichletHs g a) T) :
    timeL2 (DirichletHs g (a + 2)) T :=
  timeL2OfModes
    (fun i => solModeCoeff (a := a) hT f i)

theorem maximalRegularitySolField_timeModeCoeff (hT : 0 ≤ T)
    (f : timeL2 (DirichletHs g a) T)
    (i : DirichletLaplacianEigenIndex g) :
    timeModeCoeff
        (maximalRegularitySolField a hT f) i =
      solModeCoeff (a := a) hT f i :=
  timeL2OfModes_timeModeCoeff _
    (summable_solModeCoeff (a := a) hT f) i

def maximalRegularitySolFieldHa1 (a : ℝ) {T : ℝ} (hT : 0 < T)
    (f : timeL2 (DirichletHs g a) T) :
    timeL2 (DirichletHs g (a + 1)) T :=
  timeL2OfModes (σ := a + 1)
    (fun i => solModeCoeff (a := a) hT.le f i)

theorem maximalRegularitySolFieldHa1_timeModeCoeff (hT : 0 < T)
    (hT1 : T ≤ 1)
    (f : timeL2 (DirichletHs g a) T)
    (i : DirichletLaplacianEigenIndex g) :
    timeModeCoeff
        (maximalRegularitySolFieldHa1 a hT f) i =
      solModeCoeff (a := a) hT.le f i :=
  timeL2OfModes_timeModeCoeff (σ := a + 1) _
    (summable_solModeCoeff_Ha1 (a := a) hT hT1
      f) i

theorem maximalRegularitySolFieldHa1_norm_le
    (hT : 0 < T) (hT1 : T ≤ 1)
    (f : timeL2 (DirichletHs g a) T) :
    ‖maximalRegularitySolFieldHa1 a hT f‖ ≤
      2 * Real.sqrt T * ‖f‖ := by
  refine norm_le_of_weighted_perMode_le (b := a + 1)
    (C := 2 * Real.sqrt T)
    (by positivity) _ f (fun i => ?_)
  rw [maximalRegularitySolFieldHa1_timeModeCoeff
    (a := a) hT hT1 f i]
  exact weighted_solModeCoeff_Ha1_le (a := a) hT hT1 f i

theorem maximalRegularitySolFieldHa1_add (hT : 0 < T) (hT1 : T ≤ 1)
    (f f' : timeL2 (DirichletHs g a) T) :
    maximalRegularitySolFieldHa1 a hT (f + f') =
      maximalRegularitySolFieldHa1 a hT f +
        maximalRegularitySolFieldHa1 a hT f' := by
  refine timeModeCoeff_injective
    (fun i => ?_)
  rw [maximalRegularitySolFieldHa1_timeModeCoeff
      (a := a) hT hT1 (f + f') i,
    timeModeCoeff_add ,
    maximalRegularitySolFieldHa1_timeModeCoeff
      (a := a) hT hT1 f i,
    maximalRegularitySolFieldHa1_timeModeCoeff
      (a := a) hT hT1 f' i]
  rw [solModeCoeff, solModeCoeff, solModeCoeff,
    timeModeCoeff_add , map_add]

theorem maximalRegularitySolFieldHa1_sub (hT : 0 < T) (hT1 : T ≤ 1)
    (f f' : timeL2 (DirichletHs g a) T) :
    maximalRegularitySolFieldHa1 a hT (f - f') =
      maximalRegularitySolFieldHa1 a hT f -
        maximalRegularitySolFieldHa1 a hT f' := by
  have hadd := maximalRegularitySolFieldHa1_add
    (a := a) hT hT1 (f - f') f'
  rw [sub_add_cancel] at hadd
  rw [hadd, add_sub_cancel_right]

def maximalRegularityOp (a : ℝ) {T : ℝ} (hT : 0 < T)
    (f : timeL2 (DirichletHs g a) T) :
    timeH1 (DirichletHs g a) T :=
  TimeSobolev.timeH1.mk (0 : DirichletHs g a)
    (maximalRegularityDerivField a hT.le f)

theorem maximalRegularityOp_timeDeriv
    (hT : 0 < T)
    (f : timeL2 (DirichletHs g a) T) :
    TimeSobolev.timeH1.timeDeriv _ T
        (maximalRegularityOp a hT f) =
      maximalRegularityDerivField a hT.le f :=
  rfl

theorem maximalRegularityOp_trace0 (hT : 0 < T)
    (f : timeL2 (DirichletHs g a) T) :
    TimeSobolev.timeH1.trace0 _ T
        (maximalRegularityOp a hT f) = 0 :=
  rfl

theorem maximalRegularityOp_norm_Ha2_le
    (hT : 0 < T)
    (f : timeL2 (DirichletHs g a) T) :
    ‖maximalRegularitySolField a hT.le f‖ ≤
      (1 + T) * ‖f‖ := by
  refine norm_le_of_weighted_perMode_le (b := a + 2)
    (C := 1 + T) (by linarith [hT.le]) _ f (fun i => ?_)
  rw [maximalRegularitySolField_timeModeCoeff
    (a := a) hT.le f i]
  exact weighted_solModeCoeff_le (a := a) hT.le f i

theorem maximalRegularityOp_norm_deriv_le
    (hT : 0 < T)
    (f : timeL2 (DirichletHs g a) T) :
    ‖maximalRegularityDerivField a hT.le f‖ ≤
      2 * ‖f‖ := by
  refine norm_le_of_weighted_perMode_le (b := a)
    (C := 2) (by norm_num) _ f (fun i => ?_)
  rw [maximalRegularityDerivField_timeModeCoeff
    (a := a) hT.le f i]
  exact weighted_derivModeCoeff_le (a := a) hT.le f i

theorem maximalRegularityOp_norm_le
    (hT : 0 < T)
    (f : timeL2 (DirichletHs g a) T) :
    ‖maximalRegularityOp a hT f‖ ≤ 2 * ‖f‖ := by
  have hnormsq := TimeSobolev.timeH1.norm_sq_eq
    (maximalRegularityOp a hT f)
  have hinit : (maximalRegularityOp a hT f).init = 0 :=
    rfl
  have hderiv : (maximalRegularityOp a hT f).deriv =
      maximalRegularityDerivField a hT.le f := rfl
  have hderiv_le := maximalRegularityOp_norm_deriv_le
    (a := a) hT f
  have hsq : ‖maximalRegularityOp a hT f‖ ^ 2 ≤
      (2 * ‖f‖) ^ 2 := by
    rw [hnormsq, hinit, hderiv, norm_zero]
    have h2f_nonneg : 0 ≤ 2 * ‖f‖ := mul_nonneg (by norm_num) (norm_nonneg _)
    nlinarith [hderiv_le, norm_nonneg
      (maximalRegularityDerivField a hT.le f)]
  have h := Real.sqrt_le_sqrt hsq
  rwa [Real.sqrt_sq (norm_nonneg _),
    Real.sqrt_sq (mul_nonneg (by norm_num) (norm_nonneg _))] at h

end MaximalRegularity
end Dirichlet
end Parabolic
end Analysis
end DifferentialGeometry
