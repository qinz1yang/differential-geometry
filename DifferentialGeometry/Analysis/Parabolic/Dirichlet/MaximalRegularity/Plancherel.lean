import DifferentialGeometry.Analysis.Parabolic.MaximalRegularity.PerMode.Basic
import DifferentialGeometry.Analysis.Parabolic.TimeSobolev.Bochner.L2
import DifferentialGeometry.Analysis.Sobolev.DirichletHs.Defs
import Mathlib.MeasureTheory.Integral.Lebesgue.Add
import Mathlib.MeasureTheory.Integral.DominatedConvergence

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
open DifferentialGeometry.Analysis.Parabolic.TimeSobolev
open DifferentialGeometry.Analysis.Sobolev.Hs

variable {g : SmoothRiemannianMetric (I_half n) M}

private lemma ae_all_coeff_eq {ι : Type*} [Countable ι] {μ : Measure ℝ}
    {gfam f : ι → ℝ → ℝ} (h : ∀ i, gfam i =ᵐ[μ] f i) :
    ∀ᵐ t ∂μ, ∀ i, gfam i t = f i t :=
  (MeasureTheory.ae_all_iff).2 h

private lemma dirichletHsWeightMulCoeffSqLeNormSq {a : ℝ}
    (T : DirichletHs g a)
    (i : DirichletLaplacianEigenIndex g) :
    dirichletSobolevWeight i a * (T.coeff i) ^ 2 ≤ ‖T‖ ^ 2 := by
  rw [DirichletHs.norm_sq_eq_tsum T]
  refine Summable.le_tsum T.weighted_summable i (fun j _ => ?_)
  have hw : 0 ≤ dirichletSobolevWeight j a :=
    dirichletSobolevWeight_nonneg j a
  positivity

private lemma dirichletHsAbsCoeffLe {a : ℝ}
    (T : DirichletHs g a)
    (i : DirichletLaplacianEigenIndex g) :
    |T.coeff i| ≤
      (Real.sqrt (dirichletSobolevWeight i a))⁻¹ * ‖T‖ := by
  have hw_pos : 0 < dirichletSobolevWeight i a :=
    dirichletSobolevWeight_pos i a
  have hsqrt_pos :
      0 < Real.sqrt (dirichletSobolevWeight i a) :=
    Real.sqrt_pos.mpr hw_pos
  have hbound := dirichletHsWeightMulCoeffSqLeNormSq T i
  have hsq : (T.coeff i) ^ 2 ≤
      ((Real.sqrt (dirichletSobolevWeight i a))⁻¹ * ‖T‖) ^ 2 := by
    have hsqrt_sq :
        Real.sqrt (dirichletSobolevWeight i a) ^ 2 =
          dirichletSobolevWeight i a :=
      sq_sqrt_dirichletSobolevWeight i a
    rw [mul_pow, inv_pow, hsqrt_sq, inv_mul_eq_div, le_div_iff₀ hw_pos, mul_comm]
    exact hbound
  have hrhs_nonneg :
      0 ≤ (Real.sqrt (dirichletSobolevWeight i a))⁻¹ * ‖T‖ :=
    mul_nonneg (le_of_lt (inv_pos.mpr hsqrt_pos)) (norm_nonneg T)
  have h := Real.sqrt_le_sqrt hsq
  rwa [Real.sqrt_sq_eq_abs, Real.sqrt_sq hrhs_nonneg] at h

def dirichletHsCoeffL {a : ℝ}
    (i : DirichletLaplacianEigenIndex g) :
    DirichletHs g a →L[ℝ] ℝ :=
  LinearMap.mkContinuous
    { toFun := fun T => T.coeff i
      map_add' := fun S T => by
        simp only [DirichletHs.add_coeff]
      map_smul' := fun c T => by
        simp only [DirichletHs.smul_coeff, smul_eq_mul, RingHom.id_apply] }
    (Real.sqrt (dirichletSobolevWeight i a))⁻¹
    (fun T => by
      change ‖T.coeff i‖ ≤
        (Real.sqrt (dirichletSobolevWeight i a))⁻¹ * ‖T‖
      rw [Real.norm_eq_abs]
      exact dirichletHsAbsCoeffLe T i)

@[simp] lemma dirichletHsCoeffL_apply {a : ℝ}
    (i : DirichletLaplacianEigenIndex g)
    (T : DirichletHs g a) :
    dirichletHsCoeffL i T = T.coeff i := rfl

lemma dirichletHsCoeffL_opNorm_le {a : ℝ}
    (i : DirichletLaplacianEigenIndex g) :
    ‖dirichletHsCoeffL (a := a) i‖ ≤
      (Real.sqrt (dirichletSobolevWeight i a))⁻¹ :=
  LinearMap.mkContinuous_norm_le _
    (le_of_lt (inv_pos.mpr (Real.sqrt_pos.mpr
      (dirichletSobolevWeight_pos i a)))) _

def timeModeCoeff {a : ℝ} {T : ℝ}
    (f : timeL2 (DirichletHs g a) T)
    (i : DirichletLaplacianEigenIndex g) :
    timeL2 ℝ T :=
  (dirichletHsCoeffL i).compLpL 2 (timeMeasure T) f

theorem timeModeCoeff_coeFn {a : ℝ} {T : ℝ}
    (f : timeL2 (DirichletHs g a) T)
    (i : DirichletLaplacianEigenIndex g) :
    timeModeCoeff f i =ᵐ[timeMeasure T]
      fun t => (f t).coeff i := by
  have h := (dirichletHsCoeffL i).coeFn_compLpL
    (p := 2) (μ := timeMeasure T) f
  exact h.trans
    (Eventually.of_forall fun t => dirichletHsCoeffL_apply i (f t))

theorem timeModeCoeff_add {a : ℝ} {T : ℝ}
    (f₁ f₂ : timeL2 (DirichletHs g a) T)
    (i : DirichletLaplacianEigenIndex g) :
    timeModeCoeff (f₁ + f₂) i =
      timeModeCoeff f₁ i +
        timeModeCoeff f₂ i := by
  unfold timeModeCoeff
  rw [map_add]

theorem timeModeCoeff_smul {a : ℝ} {T : ℝ} (c : ℝ)
    (f : timeL2 (DirichletHs g a) T)
    (i : DirichletLaplacianEigenIndex g) :
    timeModeCoeff (c • f) i =
      c • timeModeCoeff f i := by
  unfold timeModeCoeff
  rw [map_smul]

theorem norm_timeModeCoeff_le {a : ℝ} {T : ℝ}
    (f : timeL2 (DirichletHs g a) T)
    (i : DirichletLaplacianEigenIndex g) :
    ‖timeModeCoeff f i‖ ≤
      (Real.sqrt (dirichletSobolevWeight i a))⁻¹ * ‖f‖ := by
  refine le_trans
    (((dirichletHsCoeffL i).compLpL 2
      (timeMeasure T)).le_opNorm f) ?_
  refine mul_le_mul_of_nonneg_right ?_ (norm_nonneg f)
  exact le_trans
    (ContinuousLinearMap.norm_compLpL_le
      (dirichletHsCoeffL i))
    (dirichletHsCoeffL_opNorm_le i)

theorem integrable_timeModeCoeff_sq {a : ℝ} {T : ℝ}
    (f : timeL2 (DirichletHs g a) T)
    (i : DirichletLaplacianEigenIndex g) :
    Integrable (fun t => (timeModeCoeff f i t) ^ 2)
      (timeMeasure T) :=
  (Lp.memLp (timeModeCoeff f i)).integrable_sq

theorem norm_timeModeCoeff_sq_eq_integral {a : ℝ} {T : ℝ}
    (f : timeL2 (DirichletHs g a) T)
    (i : DirichletLaplacianEigenIndex g) :
    ‖timeModeCoeff f i‖ ^ 2 =
      ∫ t in Set.Icc (0 : ℝ) T,
        (timeModeCoeff f i t) ^ 2 := by
  rw [TimeSobolev.norm_sq_eq_integral (timeModeCoeff f i)]
  refine integral_congr_ae (Eventually.of_forall fun t => ?_)
  simp only [Real.norm_eq_abs, sq_abs]

theorem integrable_weight_mul_coeff_sq {a : ℝ} {T : ℝ}
    (f : timeL2 (DirichletHs g a) T)
    (i : DirichletLaplacianEigenIndex g) :
    Integrable (fun t => dirichletSobolevWeight i a *
      ((f t).coeff i) ^ 2) (timeMeasure T) := by
  refine ((integrable_timeModeCoeff_sq f i).const_mul
    (dirichletSobolevWeight i a)).congr ?_
  filter_upwards [timeModeCoeff_coeFn f i] with t ht
  rw [ht]

section PlancherelFubini

variable {a : ℝ} {T : ℝ}
  (f : timeL2 (DirichletHs g a) T)

private def planIntegrand (i : DirichletLaplacianEigenIndex g)
    (t : ℝ) : ℝ≥0∞ :=
  ENNReal.ofReal
    (dirichletSobolevWeight i a * ((f t).coeff i) ^ 2)

private theorem aemeasurable_planIntegrand
    (i : DirichletLaplacianEigenIndex g) :
    AEMeasurable (planIntegrand f i) (timeMeasure T) := by
  let : MeasurableSpace ℝ := borel ℝ
  have : BorelSpace ℝ := ⟨rfl⟩
  have hmeas : AEMeasurable (fun t => (f t).coeff i) (timeMeasure T) := by
    refine AEMeasurable.congr
      (Lp.aestronglyMeasurable
        (timeModeCoeff f i)).aemeasurable ?_
    exact timeModeCoeff_coeFn f i
  exact (((hmeas.pow_const 2).const_mul
    (dirichletSobolevWeight i a))).ennreal_ofReal

private theorem lintegral_planIntegrand
    (i : DirichletLaplacianEigenIndex g) :
    ∫⁻ t, planIntegrand f i t ∂(timeMeasure T) =
      ENNReal.ofReal (dirichletSobolevWeight i a *
        ‖timeModeCoeff f i‖ ^ 2) := by
  have hw_nonneg : 0 ≤ dirichletSobolevWeight i a :=
    dirichletSobolevWeight_nonneg i a
  have hint : Integrable
      (fun t => dirichletSobolevWeight i a *
        ((f t).coeff i) ^ 2) (timeMeasure T) :=
    integrable_weight_mul_coeff_sq f i
  have hnn : 0 ≤ᵐ[timeMeasure T]
      fun t => dirichletSobolevWeight i a *
        ((f t).coeff i) ^ 2 :=
    Eventually.of_forall fun t => mul_nonneg hw_nonneg (sq_nonneg _)
  have hofReal :
      (∫⁻ t, planIntegrand f i t ∂(timeMeasure T))
        = ENNReal.ofReal (∫ t, dirichletSobolevWeight i a *
            ((f t).coeff i) ^ 2 ∂(timeMeasure T)) :=
    (ofReal_integral_eq_lintegral_ofReal hint hnn).symm
  rw [hofReal]
  congr 1
  rw [integral_const_mul]
  congr 1
  rw [norm_timeModeCoeff_sq_eq_integral f i,
    show (∫ t in Set.Icc (0 : ℝ) T,
        (timeModeCoeff f i t) ^ 2)
      = ∫ t, (timeModeCoeff f i t) ^ 2 ∂(timeMeasure T)
      from rfl]
  refine integral_congr_ae ?_
  filter_upwards [timeModeCoeff_coeFn f i] with t ht
  rw [ht]

private theorem ennreal_tsum_weight_mul_norm_sq_ne_top :
    (∑' i, ENNReal.ofReal (dirichletSobolevWeight i a *
      ‖timeModeCoeff f i‖ ^ 2)) ≠ (⊤ : ℝ≥0∞) := by
  have hpoint : ∀ t : ℝ,
      ENNReal.ofReal (‖f t‖ ^ 2) =
        ∑' i, planIntegrand f i t := by
    intro t
    rw [DirichletHs.norm_sq_eq_tsum (f t)]
    have hnn : ∀ i : DirichletLaplacianEigenIndex g,
        0 ≤ dirichletSobolevWeight i a *
          ((f t).coeff i) ^ 2 :=
      fun i => mul_nonneg (dirichletSobolevWeight_nonneg i a)
        (sq_nonneg _)
    rw [ENNReal.ofReal_tsum_of_nonneg hnn (f t).weighted_summable]
    rfl
  have hlintegral_eq :
      ∫⁻ t, ENNReal.ofReal (‖f t‖ ^ 2) ∂(timeMeasure T) =
        ∑' i, ∫⁻ t, planIntegrand f i t
          ∂(timeMeasure T) := by
    rw [show (∫⁻ t, ENNReal.ofReal (‖f t‖ ^ 2) ∂(timeMeasure T))
          = ∫⁻ t, (∑' i, planIntegrand f i t)
              ∂(timeMeasure T)
        from lintegral_congr (fun t => hpoint t)]
    exact lintegral_tsum
      (fun i => aemeasurable_planIntegrand f i)
  have hf_norm_sq_int : Integrable (fun t => ‖f t‖ ^ 2) (timeMeasure T) :=
    (memLp_two_iff_integrable_sq_norm (Lp.aestronglyMeasurable f)).mp
      (Lp.memLp f)
  have hf_nn : 0 ≤ᵐ[timeMeasure T] fun t => ‖f t‖ ^ 2 :=
    Eventually.of_forall fun t => sq_nonneg _
  rw [← tsum_congr (fun i => lintegral_planIntegrand f i),
    ← hlintegral_eq, ← ofReal_integral_eq_lintegral_ofReal hf_norm_sq_int hf_nn]
  exact ENNReal.ofReal_ne_top

private theorem weight_mul_norm_timeModeCoeff_sq_nonneg
    (i : DirichletLaplacianEigenIndex g) :
    0 ≤ dirichletSobolevWeight i a *
      ‖timeModeCoeff f i‖ ^ 2 :=
  mul_nonneg (dirichletSobolevWeight_nonneg i a) (sq_nonneg _)

theorem summable_weight_mul_norm_timeModeCoeff_sq :
    Summable (fun i => dirichletSobolevWeight i a *
      ‖timeModeCoeff f i‖ ^ 2) := by
  refine (ENNReal.summable_toReal
    (ennreal_tsum_weight_mul_norm_sq_ne_top
      (f := f))).congr
    (fun i => ?_)
  exact ENNReal.toReal_ofReal
    (weight_mul_norm_timeModeCoeff_sq_nonneg f i)

theorem norm_sq_eq_tsum_timeModeCoeff :
    ‖f‖ ^ 2 =
      ∑' i, dirichletSobolevWeight i a *
        ‖timeModeCoeff f i‖ ^ 2 := by
  have hpoint : ∀ t : ℝ,
      ENNReal.ofReal (‖f t‖ ^ 2) =
        ∑' i, planIntegrand f i t := by
    intro t
    rw [DirichletHs.norm_sq_eq_tsum (f t)]
    have hnn : ∀ i : DirichletLaplacianEigenIndex g,
        0 ≤ dirichletSobolevWeight i a *
          ((f t).coeff i) ^ 2 :=
      fun i => mul_nonneg (dirichletSobolevWeight_nonneg i a)
        (sq_nonneg _)
    rw [ENNReal.ofReal_tsum_of_nonneg hnn (f t).weighted_summable]
    rfl
  have hlintegral_eq :
      ∫⁻ t, ENNReal.ofReal (‖f t‖ ^ 2) ∂(timeMeasure T) =
        ∑' i, ∫⁻ t, planIntegrand f i t
          ∂(timeMeasure T) := by
    rw [show (∫⁻ t, ENNReal.ofReal (‖f t‖ ^ 2) ∂(timeMeasure T))
          = ∫⁻ t, (∑' i, planIntegrand f i t)
              ∂(timeMeasure T)
        from lintegral_congr (fun t => hpoint t)]
    exact lintegral_tsum
      (fun i => aemeasurable_planIntegrand f i)
  have hf_norm_sq_int : Integrable (fun t => ‖f t‖ ^ 2) (timeMeasure T) :=
    (memLp_two_iff_integrable_sq_norm (Lp.aestronglyMeasurable f)).mp
      (Lp.memLp f)
  have hf_nn : 0 ≤ᵐ[timeMeasure T] fun t => ‖f t‖ ^ 2 :=
    Eventually.of_forall fun t => sq_nonneg _
  calc ‖f‖ ^ 2
      = ∫ t in Set.Icc (0 : ℝ) T, ‖f t‖ ^ 2 :=
        TimeSobolev.norm_sq_eq_integral f
    _ = (∫⁻ t, ENNReal.ofReal (‖f t‖ ^ 2) ∂(timeMeasure T)).toReal := by
        rw [show (∫ t in Set.Icc (0 : ℝ) T, ‖f t‖ ^ 2)
              = ∫ t, ‖f t‖ ^ 2 ∂(timeMeasure T) from rfl]
        exact integral_eq_lintegral_of_nonneg_ae hf_nn
          ((Lp.aestronglyMeasurable f).norm.pow 2)
    _ = (∑' i, ∫⁻ t, planIntegrand f i t
            ∂(timeMeasure T)).toReal := by rw [hlintegral_eq]
    _ = (∑' i, ENNReal.ofReal (dirichletSobolevWeight i a *
            ‖timeModeCoeff f i‖ ^ 2)).toReal := by
        rw [tsum_congr (fun i => lintegral_planIntegrand f i)]
    _ = ∑' i, (ENNReal.ofReal (dirichletSobolevWeight i a *
            ‖timeModeCoeff f i‖ ^ 2)).toReal := by
        rw [ENNReal.tsum_toReal_eq (fun i => ENNReal.ofReal_ne_top)]
    _ = ∑' i, dirichletSobolevWeight i a *
            ‖timeModeCoeff f i‖ ^ 2 := by
        refine tsum_congr (fun i => ?_)
        rw [ENNReal.toReal_ofReal
          (weight_mul_norm_timeModeCoeff_sq_nonneg f i)]

end PlancherelFubini

theorem norm_sq_le_of_weighted_perMode_le {a b : ℝ} {T : ℝ} {C : ℝ}
    (gT : timeL2 (DirichletHs g b) T)
    (fT : timeL2 (DirichletHs g a) T)
    (hbound : ∀ i : DirichletLaplacianEigenIndex g,
      dirichletSobolevWeight i b *
          ‖timeModeCoeff gT i‖ ^ 2 ≤
        C ^ 2 * (dirichletSobolevWeight i a *
          ‖timeModeCoeff fT i‖ ^ 2)) :
    ‖gT‖ ^ 2 ≤ C ^ 2 * ‖fT‖ ^ 2 := by
  have hg := norm_sq_eq_tsum_timeModeCoeff
    (f := gT)
  have hf := norm_sq_eq_tsum_timeModeCoeff
    (f := fT)
  have hg_summ :=
    summable_weight_mul_norm_timeModeCoeff_sq
      (f := gT)
  have hf_summ :=
    summable_weight_mul_norm_timeModeCoeff_sq
      (f := fT)
  rw [hg, hf, ← tsum_mul_left]
  exact Summable.tsum_le_tsum hbound hg_summ (hf_summ.mul_left _)

theorem norm_le_of_weighted_perMode_le {a b : ℝ} {T : ℝ} {C : ℝ}
    (hC : 0 ≤ C)
    (gT : timeL2 (DirichletHs g b) T)
    (fT : timeL2 (DirichletHs g a) T)
    (hbound : ∀ i : DirichletLaplacianEigenIndex g,
      dirichletSobolevWeight i b *
          ‖timeModeCoeff gT i‖ ^ 2 ≤
        C ^ 2 * (dirichletSobolevWeight i a *
          ‖timeModeCoeff fT i‖ ^ 2)) :
    ‖gT‖ ≤ C * ‖fT‖ := by
  have hsq : ‖gT‖ ^ 2 ≤ (C * ‖fT‖) ^ 2 := by
    rw [mul_pow]
    exact norm_sq_le_of_weighted_perMode_le
      gT fT hbound
  have hrhs_nonneg : 0 ≤ C * ‖fT‖ := mul_nonneg hC (norm_nonneg fT)
  have h := Real.sqrt_le_sqrt hsq
  rwa [Real.sqrt_sq (norm_nonneg gT), Real.sqrt_sq hrhs_nonneg] at h

theorem timeModeCoeff_injective {b : ℝ} {T : ℝ}
    {f₁ f₂ : timeL2 (DirichletHs g b) T}
    (h : ∀ i, timeModeCoeff f₁ i =
      timeModeCoeff f₂ i) :
    f₁ = f₂ := by
  refine MeasureTheory.Lp.ext ?_
  have hcoord : ∀ i : DirichletLaplacianEigenIndex g,
      (fun t => (f₁ t).coeff i) =ᵐ[timeMeasure T]
        fun t => (f₂ t).coeff i := by
    intro i
    have h1 := timeModeCoeff_coeFn f₁ i
    have h2 := timeModeCoeff_coeFn f₂ i
    have heq : timeModeCoeff f₁ i =ᵐ[timeMeasure T]
        timeModeCoeff f₂ i := by rw [h i]
    exact (h1.symm.trans heq).trans h2
  filter_upwards [ae_all_iff.mpr hcoord] with t ht
  exact DirichletHs.ext (funext ht)

end MaximalRegularity
end Dirichlet
end Parabolic
end Analysis
end DifferentialGeometry
