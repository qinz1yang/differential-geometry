import DifferentialGeometry.Analysis.Parabolic.Dirichlet.MaximalRegularity.OperatorEquation

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
  (kernelIntegral_time_le_one)
open DifferentialGeometry.Analysis.Parabolic.TimeSobolev
open DifferentialGeometry.Analysis.Sobolev.Hs

variable {g : SmoothRiemannianMetric (I_half n) M}
variable {a T : ℝ}

abbrev MaximalRegularitySolutionSpace (a : ℝ) (T : ℝ) : Type _ :=
  timeH1 (DirichletHs g a) T

def homogeneousModeCoeff
    (u₀ : DirichletHs g (a + 1))
    (i : DirichletLaplacianEigenIndex g) : timeL2 ℝ T :=
  TimeSobolev.ofContinuousOn (X := ℝ) (T := T)
    (f := fun t => Real.exp (-dirichletLaplacianEigenvalue i * t) *
      u₀.coeff i)
    (Continuous.continuousOn (by fun_prop))

def homogeneousDerivModeCoeff
    (u₀ : DirichletHs g (a + 1))
    (i : DirichletLaplacianEigenIndex g) : timeL2 ℝ T :=
  TimeSobolev.ofContinuousOn (X := ℝ) (T := T)
    (f := fun t => -dirichletLaplacianEigenvalue i *
      (Real.exp (-dirichletLaplacianEigenvalue i * t) * u₀.coeff i))
    (Continuous.continuousOn (by fun_prop))

theorem homogeneousDerivModeCoeff_eq_smul
    (u₀ : DirichletHs g (a + 1))
    (i : DirichletLaplacianEigenIndex g) :
    homogeneousDerivModeCoeff (a := a) (T := T) u₀ i =
      (-dirichletLaplacianEigenvalue i) •
        homogeneousModeCoeff (a := a) (T := T) u₀ i := by
  refine Lp.ext ?_
  have hderiv : homogeneousDerivModeCoeff (a := a) (T := T) u₀ i
      =ᵐ[timeMeasure T] fun t => -dirichletLaplacianEigenvalue i *
        (Real.exp (-dirichletLaplacianEigenvalue i * t) * u₀.coeff i) :=
    TimeSobolev.coeFn_ofContinuousOn _
  have hmode : homogeneousModeCoeff (a := a) (T := T) u₀ i
      =ᵐ[timeMeasure T] fun t =>
        Real.exp (-dirichletLaplacianEigenvalue i * t) * u₀.coeff i :=
    TimeSobolev.coeFn_ofContinuousOn _
  have hsmul := Lp.coeFn_smul (-dirichletLaplacianEigenvalue i)
    (homogeneousModeCoeff (a := a) (T := T) u₀ i)
  filter_upwards [hderiv, hmode, hsmul] with t htderiv htmode htsmul
  rw [htderiv, htsmul, Pi.smul_apply, htmode, smul_eq_mul]

private theorem norm_homogeneousModeCoeff_sq_eq
    (u₀ : DirichletHs g (a + 1))
    (i : DirichletLaplacianEigenIndex g) :
    ‖homogeneousModeCoeff (a := a) (T := T) u₀ i‖ ^ 2 =
      ∫ t in Set.Icc (0 : ℝ) T,
        Real.exp (-(2 * dirichletLaplacianEigenvalue i) * t) *
          (u₀.coeff i) ^ 2 := by
  rw [TimeSobolev.norm_sq_eq_integral]
  refine integral_congr_ae ?_
  filter_upwards [TimeSobolev.coeFn_ofContinuousOn
    (Continuous.continuousOn (by fun_prop) :
      ContinuousOn (fun t : ℝ =>
        Real.exp (-dirichletLaplacianEigenvalue i * t) * u₀.coeff i)
        (Set.Icc 0 T))] with t ht
  change ‖(TimeSobolev.ofContinuousOn (X := ℝ) (T := T)
    (f := fun t => Real.exp (-dirichletLaplacianEigenvalue i * t) *
      u₀.coeff i)
    (Continuous.continuousOn (by fun_prop)) : timeL2 ℝ T) t‖ ^ 2 = _
  rw [ht, Real.norm_eq_abs, sq_abs, mul_pow, pow_two, ← Real.exp_add]
  congr 2
  ring

private theorem norm_homogeneousModeCoeff_sq_le (hT : 0 ≤ T)
    (u₀ : DirichletHs g (a + 1))
    (i : DirichletLaplacianEigenIndex g) :
    ‖homogeneousModeCoeff (a := a) (T := T) u₀ i‖ ^ 2 ≤
      T * (u₀.coeff i) ^ 2 := by
  rw [show homogeneousModeCoeff (a := a) (T := T) u₀ i =
      TimeSobolev.ofContinuousOn (X := ℝ) (T := T)
        (f := fun t => Real.exp (-dirichletLaplacianEigenvalue i * t) *
          u₀.coeff i)
        (Continuous.continuousOn (by fun_prop)) from rfl]
  have hbound : ‖TimeSobolev.ofContinuousOn (X := ℝ) (T := T)
        (f := fun t => Real.exp (-dirichletLaplacianEigenvalue i * t) *
          u₀.coeff i)
        (Continuous.continuousOn (by fun_prop))‖ ≤
      Real.sqrt T * |u₀.coeff i| := by
    refine TimeSobolev.norm_ofContinuousOn_le_of_bound _ (fun t ht => ?_)
    have hlam := dirichletLaplacianEigenvalue_nonneg i
    have hexp_le : Real.exp (-dirichletLaplacianEigenvalue i * t) ≤ 1 :=
      Real.exp_le_one_iff.mpr (by nlinarith [ht.1])
    have hexp_pos : 0 < Real.exp (-dirichletLaplacianEigenvalue i * t) :=
      Real.exp_pos _
    rw [Real.norm_eq_abs, abs_mul, abs_of_pos hexp_pos]
    nlinarith [abs_nonneg (u₀.coeff i)]
  have hrhs_nonneg : 0 ≤ Real.sqrt T * |u₀.coeff i| :=
    mul_nonneg (Real.sqrt_nonneg _) (abs_nonneg _)
  have hsq : ‖TimeSobolev.ofContinuousOn (X := ℝ) (T := T)
        (f := fun t => Real.exp (-dirichletLaplacianEigenvalue i * t) *
          u₀.coeff i)
        (Continuous.continuousOn (by fun_prop))‖ ^ 2 ≤
      (Real.sqrt T * |u₀.coeff i|) ^ 2 := by
    nlinarith [norm_nonneg (TimeSobolev.ofContinuousOn (X := ℝ) (T := T)
      (f := fun t => Real.exp (-dirichletLaplacianEigenvalue i * t) *
        u₀.coeff i)
      (Continuous.continuousOn (by fun_prop)))]
  calc
    ‖TimeSobolev.ofContinuousOn (X := ℝ) (T := T)
        (f := fun t => Real.exp (-dirichletLaplacianEigenvalue i * t) *
          u₀.coeff i)
        (Continuous.continuousOn (by fun_prop))‖ ^ 2
        ≤ (Real.sqrt T * |u₀.coeff i|) ^ 2 := hsq
    _ = T * (u₀.coeff i) ^ 2 := by
      rw [mul_pow, Real.sq_sqrt hT, sq_abs]

private theorem eigenvalue_mul_norm_homogeneousModeCoeff_sq_le
    (hT : 0 ≤ T)
    (u₀ : DirichletHs g (a + 1))
    (i : DirichletLaplacianEigenIndex g) :
    dirichletLaplacianEigenvalue i *
        ‖homogeneousModeCoeff (a := a) (T := T) u₀ i‖ ^ 2 ≤
      (1 / 2 : ℝ) * (u₀.coeff i) ^ 2 := by
  rw [norm_homogeneousModeCoeff_sq_eq]
  rw [← MeasureTheory.integral_const_mul]
  have hconvert :
      ∫ t in Set.Icc (0 : ℝ) T,
          dirichletLaplacianEigenvalue i *
            (Real.exp (-(2 * dirichletLaplacianEigenvalue i) * t) *
              (u₀.coeff i) ^ 2) =
        (1 / 2 : ℝ) * (u₀.coeff i) ^ 2 *
          (∫ t in (0 : ℝ)..T,
            (2 * dirichletLaplacianEigenvalue i) *
              Real.exp (-((2 * dirichletLaplacianEigenvalue i) *
                (t - 0)))) := by
    rw [intervalIntegral.integral_of_le hT,
      ← MeasureTheory.integral_Icc_eq_integral_Ioc,
      ← MeasureTheory.integral_const_mul]
    refine integral_congr_ae (Eventually.of_forall fun t => ?_)
    ring_nf
  rw [hconvert]
  have hkernel := kernelIntegral_time_le_one
    (2 * dirichletLaplacianEigenvalue i) 0 T
  have hfactor : 0 ≤ (1 / 2 : ℝ) * (u₀.coeff i) ^ 2 :=
    mul_nonneg (by norm_num) (sq_nonneg _)
  nlinarith

private theorem dirichletSobolevWeight_add_one
    (i : DirichletLaplacianEigenIndex g) (s : ℝ) :
    dirichletSobolevWeight i (s + 1) =
      dirichletSobolevWeight i s *
        (1 + dirichletLaplacianEigenvalue i) := by
  have hbase_pos : (0 : ℝ) < 1 + dirichletLaplacianEigenvalue i :=
    lt_of_lt_of_le one_pos (one_le_one_add_dirichletLaplacianEigenvalue i)
  rw [dirichletSobolevWeight, dirichletSobolevWeight,
    Real.rpow_add hbase_pos, Real.rpow_one]

private theorem weighted_homogeneousModeCoeff_le (hT : 0 ≤ T)
    (u₀ : DirichletHs g (a + 1))
    (i : DirichletLaplacianEigenIndex g) :
    dirichletSobolevWeight i (a + 2) *
        ‖homogeneousModeCoeff (a := a) (T := T) u₀ i‖ ^ 2 ≤
      (T + 1 / 2) *
        (dirichletSobolevWeight i (a + 1) * (u₀.coeff i) ^ 2) := by
  set lam := dirichletLaplacianEigenvalue i with hlam_def
  set q := ‖homogeneousModeCoeff (a := a) (T := T) u₀ i‖ ^ 2 with hq_def
  have hlam : 0 ≤ lam := dirichletLaplacianEigenvalue_nonneg i
  have hq : 0 ≤ q := sq_nonneg _
  have htime : q ≤ T * (u₀.coeff i) ^ 2 :=
    norm_homogeneousModeCoeff_sq_le hT u₀ i
  have heigen : lam * q ≤ (1 / 2 : ℝ) * (u₀.coeff i) ^ 2 :=
    eigenvalue_mul_norm_homogeneousModeCoeff_sq_le hT u₀ i
  have hmode : (1 + lam) * q ≤
      (T + 1 / 2) * (u₀.coeff i) ^ 2 := by
    calc
      (1 + lam) * q = q + lam * q := by ring
      _ ≤ T * (u₀.coeff i) ^ 2 +
          (1 / 2 : ℝ) * (u₀.coeff i) ^ 2 := add_le_add htime heigen
      _ = (T + 1 / 2) * (u₀.coeff i) ^ 2 := by ring
  have hw : 0 ≤ dirichletSobolevWeight i (a + 1) :=
    dirichletSobolevWeight_nonneg i (a + 1)
  calc
    dirichletSobolevWeight i (a + 2) * q =
        dirichletSobolevWeight i (a + 1) * ((1 + lam) * q) := by
      rw [show a + 2 = (a + 1) + 1 by ring,
        dirichletSobolevWeight_add_one, hlam_def]
      ring
    _ ≤ dirichletSobolevWeight i (a + 1) *
        ((T + 1 / 2) * (u₀.coeff i) ^ 2) :=
      mul_le_mul_of_nonneg_left hmode hw
    _ = (T + 1 / 2) *
        (dirichletSobolevWeight i (a + 1) * (u₀.coeff i) ^ 2) := by ring

private theorem weighted_homogeneousDerivModeCoeff_le (hT : 0 ≤ T)
    (u₀ : DirichletHs g (a + 1))
    (i : DirichletLaplacianEigenIndex g) :
    dirichletSobolevWeight i a *
        ‖homogeneousDerivModeCoeff (a := a) (T := T) u₀ i‖ ^ 2 ≤
      (1 / 2 : ℝ) *
        (dirichletSobolevWeight i (a + 1) * (u₀.coeff i) ^ 2) := by
  set lam := dirichletLaplacianEigenvalue i with hlam_def
  set q := ‖homogeneousModeCoeff (a := a) (T := T) u₀ i‖ ^ 2 with hq_def
  have hlam : 0 ≤ lam := dirichletLaplacianEigenvalue_nonneg i
  have heigen : lam * q ≤ (1 / 2 : ℝ) * (u₀.coeff i) ^ 2 :=
    eigenvalue_mul_norm_homogeneousModeCoeff_sq_le hT u₀ i
  have hderiv :
      ‖homogeneousDerivModeCoeff (a := a) (T := T) u₀ i‖ ^ 2 =
        lam ^ 2 * q := by
    rw [homogeneousDerivModeCoeff_eq_smul, norm_smul, mul_pow,
      Real.norm_eq_abs, sq_abs, neg_pow, neg_one_sq, one_mul, hlam_def]
  have hmode : lam ^ 2 * q ≤
      (1 + lam) * ((1 / 2 : ℝ) * (u₀.coeff i) ^ 2) := by
    calc
      lam ^ 2 * q = lam * (lam * q) := by ring
      _ ≤ lam * ((1 / 2 : ℝ) * (u₀.coeff i) ^ 2) :=
        mul_le_mul_of_nonneg_left heigen hlam
      _ ≤ (1 + lam) * ((1 / 2 : ℝ) * (u₀.coeff i) ^ 2) := by
        gcongr
        linarith
  have hw : 0 ≤ dirichletSobolevWeight i a :=
    dirichletSobolevWeight_nonneg i a
  calc
    dirichletSobolevWeight i a *
        ‖homogeneousDerivModeCoeff (a := a) (T := T) u₀ i‖ ^ 2 =
      dirichletSobolevWeight i a * (lam ^ 2 * q) := by rw [hderiv]
    _ ≤ dirichletSobolevWeight i a *
        ((1 + lam) * ((1 / 2 : ℝ) * (u₀.coeff i) ^ 2)) :=
      mul_le_mul_of_nonneg_left hmode hw
    _ = (1 / 2 : ℝ) *
        (dirichletSobolevWeight i (a + 1) * (u₀.coeff i) ^ 2) := by
      rw [dirichletSobolevWeight_add_one, hlam_def]
      ring

private theorem summable_homogeneousModeCoeff (hT : 0 ≤ T)
    (u₀ : DirichletHs g (a + 1)) :
    Summable (fun i => dirichletSobolevWeight i (a + 2) *
      ‖homogeneousModeCoeff (a := a) (T := T) u₀ i‖ ^ 2) := by
  have hdom : Summable (fun i => (T + 1 / 2) *
      (dirichletSobolevWeight i (a + 1) * (u₀.coeff i) ^ 2)) :=
    u₀.weighted_summable.mul_left _
  refine Summable.of_nonneg_of_le (fun i => ?_) (fun i => ?_) hdom
  · exact mul_nonneg (dirichletSobolevWeight_nonneg i (a + 2)) (sq_nonneg _)
  · exact weighted_homogeneousModeCoeff_le hT u₀ i

private theorem summable_homogeneousModeCoeff_Ha1 (hT : 0 ≤ T)
    (u₀ : DirichletHs g (a + 1)) :
    Summable (fun i => dirichletSobolevWeight i (a + 1) *
      ‖homogeneousModeCoeff (a := a) (T := T) u₀ i‖ ^ 2) := by
  have hdom : Summable (fun i => T *
      (dirichletSobolevWeight i (a + 1) * (u₀.coeff i) ^ 2)) :=
    u₀.weighted_summable.mul_left _
  refine Summable.of_nonneg_of_le (fun i => ?_) (fun i => ?_) hdom
  · exact mul_nonneg (dirichletSobolevWeight_nonneg i (a + 1)) (sq_nonneg _)
  · calc
      dirichletSobolevWeight i (a + 1) *
          ‖homogeneousModeCoeff (a := a) (T := T) u₀ i‖ ^ 2 ≤
        dirichletSobolevWeight i (a + 1) *
          (T * (u₀.coeff i) ^ 2) :=
        mul_le_mul_of_nonneg_left
          (norm_homogeneousModeCoeff_sq_le hT u₀ i)
          (dirichletSobolevWeight_nonneg i (a + 1))
      _ = T *
          (dirichletSobolevWeight i (a + 1) * (u₀.coeff i) ^ 2) := by ring

private theorem summable_homogeneousDerivModeCoeff (hT : 0 ≤ T)
    (u₀ : DirichletHs g (a + 1)) :
    Summable (fun i => dirichletSobolevWeight i a *
      ‖homogeneousDerivModeCoeff (a := a) (T := T) u₀ i‖ ^ 2) := by
  have hdom : Summable (fun i => (1 / 2 : ℝ) *
      (dirichletSobolevWeight i (a + 1) * (u₀.coeff i) ^ 2)) :=
    u₀.weighted_summable.mul_left _
  refine Summable.of_nonneg_of_le (fun i => ?_) (fun i => ?_) hdom
  · exact mul_nonneg (dirichletSobolevWeight_nonneg i a) (sq_nonneg _)
  · exact weighted_homogeneousDerivModeCoeff_le hT u₀ i

def maximalRegularityHomogeneousSolField (a : ℝ) (T : ℝ)
    (u₀ : DirichletHs g (a + 1)) :
    timeL2 (DirichletHs g (a + 2)) T :=
  timeL2OfModes (fun i => homogeneousModeCoeff (a := a) (T := T) u₀ i)

theorem maximalRegularityHomogeneousSolField_timeModeCoeff (hT : 0 ≤ T)
    (u₀ : DirichletHs g (a + 1))
    (i : DirichletLaplacianEigenIndex g) :
    timeModeCoeff (maximalRegularityHomogeneousSolField a T u₀) i =
      homogeneousModeCoeff (a := a) (T := T) u₀ i :=
  timeL2OfModes_timeModeCoeff _ (summable_homogeneousModeCoeff hT u₀) i

def maximalRegularityHomogeneousSolFieldHa1 (a : ℝ) (T : ℝ)
    (u₀ : DirichletHs g (a + 1)) :
    timeL2 (DirichletHs g (a + 1)) T :=
  timeL2OfModes (fun i => homogeneousModeCoeff (a := a) (T := T) u₀ i)

theorem maximalRegularityHomogeneousSolFieldHa1_timeModeCoeff (hT : 0 ≤ T)
    (u₀ : DirichletHs g (a + 1))
    (i : DirichletLaplacianEigenIndex g) :
    timeModeCoeff (maximalRegularityHomogeneousSolFieldHa1 a T u₀) i =
      homogeneousModeCoeff (a := a) (T := T) u₀ i :=
  timeL2OfModes_timeModeCoeff _
    (summable_homogeneousModeCoeff_Ha1 hT u₀) i

def maximalRegularityHomogeneousDerivField (a : ℝ) (T : ℝ)
    (u₀ : DirichletHs g (a + 1)) :
    timeL2 (DirichletHs g a) T :=
  timeL2OfModes
    (fun i => homogeneousDerivModeCoeff (a := a) (T := T) u₀ i)

theorem maximalRegularityHomogeneousDerivField_timeModeCoeff (hT : 0 ≤ T)
    (u₀ : DirichletHs g (a + 1))
    (i : DirichletLaplacianEigenIndex g) :
    timeModeCoeff (maximalRegularityHomogeneousDerivField a T u₀) i =
      homogeneousDerivModeCoeff (a := a) (T := T) u₀ i :=
  timeL2OfModes_timeModeCoeff _
    (summable_homogeneousDerivModeCoeff hT u₀) i

def maximalRegularityHomogeneous (a : ℝ) (T : ℝ)
    (u₀ : DirichletHs g (a + 1)) :
    MaximalRegularitySolutionSpace (g := g) a T :=
  TimeSobolev.timeH1.mk
    (dirichletHsInclusion (show a ≤ a + 1 by linarith) u₀)
    (maximalRegularityHomogeneousDerivField a T u₀)

@[simp] theorem maximalRegularityHomogeneous_init
    (u₀ : DirichletHs g (a + 1)) :
    (maximalRegularityHomogeneous a T u₀).init =
      dirichletHsInclusion (show a ≤ a + 1 by linarith) u₀ :=
  rfl

theorem maximalRegularityHomogeneous_trace0
    (u₀ : DirichletHs g (a + 1)) :
    TimeSobolev.timeH1.trace0 _ T
        (maximalRegularityHomogeneous a T u₀) =
      dirichletHsInclusion (show a ≤ a + 1 by linarith) u₀ :=
  rfl

@[simp] theorem maximalRegularityHomogeneous_deriv
    (u₀ : DirichletHs g (a + 1)) :
    (maximalRegularityHomogeneous a T u₀).deriv =
      maximalRegularityHomogeneousDerivField a T u₀ :=
  rfl

theorem maximalRegularityHomogeneousDerivField_eq_laplacian (hT : 0 ≤ T)
    (u₀ : DirichletHs g (a + 1)) :
    maximalRegularityHomogeneousDerivField a T u₀ =
      timeDirichletHsLaplacian g a
        (maximalRegularityHomogeneousSolField a T u₀) := by
  refine timeModeCoeff_injective (fun i => ?_)
  rw [maximalRegularityHomogeneousDerivField_timeModeCoeff hT u₀ i,
    timeModeCoeff_timeDirichletHsLaplacian
      (maximalRegularityHomogeneousSolField a T u₀) i,
    maximalRegularityHomogeneousSolField_timeModeCoeff hT u₀ i]
  exact homogeneousDerivModeCoeff_eq_smul u₀ i

theorem maximalRegularityHomogeneous_timeDeriv_eq (hT : 0 ≤ T)
    (u₀ : DirichletHs g (a + 1)) :
    TimeSobolev.timeH1.timeDeriv _ T
        (maximalRegularityHomogeneous a T u₀) =
      timeDirichletHsLaplacian g a
        (maximalRegularityHomogeneousSolField a T u₀) := by
  rw [TimeSobolev.timeH1.timeDeriv_apply,
    maximalRegularityHomogeneous_deriv]
  exact maximalRegularityHomogeneousDerivField_eq_laplacian hT u₀

theorem maximalRegularityDerivField_add (hT : 0 ≤ T)
    (f f' : timeL2 (DirichletHs g a) T) :
    maximalRegularityDerivField a hT (f + f') =
      maximalRegularityDerivField a hT f +
        maximalRegularityDerivField a hT f' := by
  refine timeModeCoeff_injective (fun i => ?_)
  rw [maximalRegularityDerivField_timeModeCoeff hT (f + f') i,
    timeModeCoeff_add,
    maximalRegularityDerivField_timeModeCoeff hT f i,
    maximalRegularityDerivField_timeModeCoeff hT f' i]
  rw [derivModeCoeff, derivModeCoeff, derivModeCoeff,
    timeModeCoeff_add, map_add]

theorem maximalRegularityOp_add (hT : 0 < T)
    (f f' : timeL2 (DirichletHs g a) T) :
    maximalRegularityOp a hT (f + f') =
      maximalRegularityOp a hT f + maximalRegularityOp a hT f' := by
  refine TimeSobolev.timeH1.ext ?_ ?_
  · rw [TimeSobolev.timeH1.init_add]
    change (0 : DirichletHs g a) = 0 + 0
    rw [add_zero]
  · rw [TimeSobolev.timeH1.deriv_add]
    exact maximalRegularityDerivField_add hT.le f f'

theorem maximalRegularityOp_sub (hT : 0 < T)
    (f f' : timeL2 (DirichletHs g a) T) :
    maximalRegularityOp a hT (f - f') =
      maximalRegularityOp a hT f - maximalRegularityOp a hT f' := by
  have hadd := maximalRegularityOp_add hT (f - f') f'
  rw [sub_add_cancel] at hadd
  rw [hadd, add_sub_cancel_right]

theorem maximalRegularitySolField_add (hT : 0 ≤ T)
    (f f' : timeL2 (DirichletHs g a) T) :
    maximalRegularitySolField a hT (f + f') =
      maximalRegularitySolField a hT f +
        maximalRegularitySolField a hT f' := by
  refine timeModeCoeff_injective (fun i => ?_)
  rw [maximalRegularitySolField_timeModeCoeff hT (f + f') i,
    timeModeCoeff_add,
    maximalRegularitySolField_timeModeCoeff hT f i,
    maximalRegularitySolField_timeModeCoeff hT f' i]
  rw [solModeCoeff, solModeCoeff, solModeCoeff,
    timeModeCoeff_add, map_add]

theorem maximalRegularitySolField_sub (hT : 0 ≤ T)
    (f f' : timeL2 (DirichletHs g a) T) :
    maximalRegularitySolField a hT (f - f') =
      maximalRegularitySolField a hT f -
        maximalRegularitySolField a hT f' := by
  have hadd := maximalRegularitySolField_add hT (f - f') f'
  rw [sub_add_cancel] at hadd
  rw [hadd, add_sub_cancel_right]

def maximalRegularityDuhamelSolField (a : ℝ) {T : ℝ} (hT : 0 < T)
    (u₀ : DirichletHs g (a + 1))
    (f : timeL2 (DirichletHs g a) T) :
    timeL2 (DirichletHs g (a + 2)) T :=
  maximalRegularityHomogeneousSolField a T u₀ +
    maximalRegularitySolField a hT.le f

def maximalRegularityDuhamelSolFieldHa1 (a : ℝ) {T : ℝ} (hT : 0 < T)
    (u₀ : DirichletHs g (a + 1))
    (f : timeL2 (DirichletHs g a) T) :
    timeL2 (DirichletHs g (a + 1)) T :=
  maximalRegularityHomogeneousSolFieldHa1 a T u₀ +
    maximalRegularitySolFieldHa1 a hT f

def maximalRegularityDuhamelMap (a : ℝ) {T : ℝ} (hT : 0 < T)
    (u₀ : DirichletHs g (a + 1))
    (f : timeL2 (DirichletHs g a) T) :
    MaximalRegularitySolutionSpace (g := g) a T :=
  maximalRegularityHomogeneous a T u₀ + maximalRegularityOp a hT f

@[simp] theorem maximalRegularityDuhamelMap_init (hT : 0 < T)
    (u₀ : DirichletHs g (a + 1))
    (f : timeL2 (DirichletHs g a) T) :
    (maximalRegularityDuhamelMap a hT u₀ f).init =
      dirichletHsInclusion (show a ≤ a + 1 by linarith) u₀ := by
  rw [maximalRegularityDuhamelMap, TimeSobolev.timeH1.init_add,
    maximalRegularityHomogeneous_init]
  change dirichletHsInclusion (show a ≤ a + 1 by linarith) u₀ + 0 = _
  rw [add_zero]

theorem maximalRegularityDuhamelMap_trace0 (hT : 0 < T)
    (u₀ : DirichletHs g (a + 1))
    (f : timeL2 (DirichletHs g a) T) :
    TimeSobolev.timeH1.trace0 _ T
        (maximalRegularityDuhamelMap a hT u₀ f) =
      dirichletHsInclusion (show a ≤ a + 1 by linarith) u₀ := by
  rw [TimeSobolev.timeH1.trace0_apply]
  exact maximalRegularityDuhamelMap_init hT u₀ f

@[simp] theorem maximalRegularityDuhamelMap_deriv (hT : 0 < T)
    (u₀ : DirichletHs g (a + 1))
    (f : timeL2 (DirichletHs g a) T) :
    (maximalRegularityDuhamelMap a hT u₀ f).deriv =
      maximalRegularityHomogeneousDerivField a T u₀ +
        maximalRegularityDerivField a hT.le f := by
  rw [maximalRegularityDuhamelMap, TimeSobolev.timeH1.deriv_add]
  rfl

theorem maximalRegularityDuhamelMap_timeDeriv_eq (hT : 0 < T)
    (u₀ : DirichletHs g (a + 1))
    (f : timeL2 (DirichletHs g a) T) :
    TimeSobolev.timeH1.timeDeriv _ T
        (maximalRegularityDuhamelMap a hT u₀ f) =
      timeDirichletHsLaplacian g a
          (maximalRegularityDuhamelSolField a hT u₀ f) + f := by
  rw [TimeSobolev.timeH1.timeDeriv_apply,
    maximalRegularityDuhamelMap_deriv]
  rw [maximalRegularityHomogeneousDerivField_eq_laplacian hT.le u₀]
  have hsolve := maximalRegularityOp_solves (a := a) hT f
  rw [maximalRegularityOp_timeDeriv (a := a) hT f] at hsolve
  rw [hsolve, maximalRegularityDuhamelSolField, map_add]
  abel

theorem maximalRegularityDuhamelMap_norm_sub_le (hT : 0 < T)
    (u₀ : DirichletHs g (a + 1))
    (f f' : timeL2 (DirichletHs g a) T) :
    ‖maximalRegularityDuhamelMap a hT u₀ f -
        maximalRegularityDuhamelMap a hT u₀ f'‖ ≤
      2 * ‖f - f'‖ := by
  have hdiff : maximalRegularityDuhamelMap a hT u₀ f -
        maximalRegularityDuhamelMap a hT u₀ f' =
      maximalRegularityOp a hT (f - f') := by
    rw [maximalRegularityOp_sub hT f f']
    change (maximalRegularityHomogeneous a T u₀ + maximalRegularityOp a hT f) -
        (maximalRegularityHomogeneous a T u₀ + maximalRegularityOp a hT f') =
      maximalRegularityOp a hT f - maximalRegularityOp a hT f'
    abel
  rw [hdiff]
  exact maximalRegularityOp_norm_le (a := a) hT (f - f')

theorem maximalRegularityDuhamelMap_lipschitzWith (hT : 0 < T)
    (u₀ : DirichletHs g (a + 1)) :
    LipschitzWith 2 (fun f : timeL2 (DirichletHs g a) T =>
      maximalRegularityDuhamelMap a hT u₀ f) := by
  refine LipschitzWith.of_dist_le_mul (fun f f' => ?_)
  rw [dist_eq_norm, dist_eq_norm]
  simpa only [NNReal.coe_ofNat] using
    maximalRegularityDuhamelMap_norm_sub_le hT u₀ f f'

theorem maximalRegularityDuhamelSolField_sub (hT : 0 < T)
    (u₀ : DirichletHs g (a + 1))
    (f f' : timeL2 (DirichletHs g a) T) :
    maximalRegularityDuhamelSolField a hT u₀ f -
        maximalRegularityDuhamelSolField a hT u₀ f' =
      maximalRegularitySolField a hT.le (f - f') := by
  rw [maximalRegularitySolField_sub hT.le f f']
  rw [maximalRegularityDuhamelSolField,
    maximalRegularityDuhamelSolField]
  abel

theorem maximalRegularityDuhamelSolField_norm_sub_le (hT : 0 < T)
    (u₀ : DirichletHs g (a + 1))
    (f f' : timeL2 (DirichletHs g a) T) :
    ‖maximalRegularityDuhamelSolField a hT u₀ f -
        maximalRegularityDuhamelSolField a hT u₀ f'‖ ≤
      (1 + T) * ‖f - f'‖ := by
  rw [maximalRegularityDuhamelSolField_sub hT u₀ f f']
  exact maximalRegularityOp_norm_Ha2_le (a := a) hT (f - f')

theorem maximalRegularityDuhamelSolFieldHa1_sub
    (hT : 0 < T) (hT1 : T ≤ 1)
    (u₀ : DirichletHs g (a + 1))
    (f f' : timeL2 (DirichletHs g a) T) :
    maximalRegularityDuhamelSolFieldHa1 a hT u₀ f -
        maximalRegularityDuhamelSolFieldHa1 a hT u₀ f' =
      maximalRegularitySolFieldHa1 a hT (f - f') := by
  rw [maximalRegularitySolFieldHa1_sub hT hT1 f f']
  rw [maximalRegularityDuhamelSolFieldHa1,
    maximalRegularityDuhamelSolFieldHa1]
  abel

theorem maximalRegularityDuhamelSolFieldHa1_norm_sub_le
    (hT : 0 < T) (hT1 : T ≤ 1)
    (u₀ : DirichletHs g (a + 1))
    (f f' : timeL2 (DirichletHs g a) T) :
    ‖maximalRegularityDuhamelSolFieldHa1 a hT u₀ f -
        maximalRegularityDuhamelSolFieldHa1 a hT u₀ f'‖ ≤
      2 * Real.sqrt T * ‖f - f'‖ := by
  rw [maximalRegularityDuhamelSolFieldHa1_sub hT hT1 u₀ f f']
  exact maximalRegularitySolFieldHa1_norm_le hT hT1 (f - f')

end MaximalRegularity
end Dirichlet
end Parabolic
end Analysis
end DifferentialGeometry
