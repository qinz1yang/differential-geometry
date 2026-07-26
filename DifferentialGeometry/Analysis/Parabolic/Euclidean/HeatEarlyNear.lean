import DifferentialGeometry.Analysis.Parabolic.Euclidean.HeatKernelGaussian
import DifferentialGeometry.Analysis.Parabolic.Euclidean.RoughCarleson

/-!
# The near part of the early rough heat potential

For `0 < s <= t / 2`, the heat kernel has scale `sqrt (t / 2)`.  Integrating
over the spatial ball `B(x, sqrt t)`, the inverse-volume scale of the kernel
is cancelled exactly by the `R^n` factor in the source Carleson estimate.
The result is a time-independent `Y^0 -> C^0` bound for the actual Bochner
heat potential on that near parabolic cylinder.
-/

noncomputable section

open MeasureTheory Real Set
open scoped ENNReal RealInnerProductSpace

namespace DifferentialGeometry
namespace Analysis
namespace Parabolic
namespace Euclidean

variable {V F : Type*}
  [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  [Nontrivial V]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]

/-- The near spatial part of the early Duhamel cylinder. -/
def earlyCyl (t : ℝ) (x : V) : Set (ℝ × V) :=
  Set.Ioc 0 (t / 2) ×ˢ Metric.ball x (heatScale t)

private theorem earlyCyl_meas (t : ℝ) (x : V) :
    MeasurableSet (earlyCyl t x) :=
  measurableSet_Ioc.prod Metric.measurableSet_ball

/-- The early near cylinder is contained in the Carleson cylinder of radius
`sqrt t`. -/
theorem earlyCyl_sub {t : ℝ} (ht : 0 ≤ t) (x : V) :
    earlyCyl t x ⊆ paraCyl x (heatScale t) := by
  rintro z ⟨hzs, hzy⟩
  refine ⟨⟨hzs.1, ?_⟩, hzy⟩
  have hhalf : t / 2 ≤ t := by linarith
  simpa [heatScale, Real.sq_sqrt ht] using hzs.2.trans hhalf

/-- The actual Bochner heat potential on the near part of the early
parabolic cylinder. -/
def heatEarlyNear (t : ℝ) (f : ℝ × V → F) (x : V) : F :=
  ∫ z in earlyCyl t x,
    heatKernel (t - z.1) (x - z.2) • f z ∂(stVolume : Measure (ℝ × V))

/-- The dimension-dependent constant in the near early-potential bound. -/
def nearHeatC (V : Type*) [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    [FiniteDimensional ℝ V] : ℝ≥0∞ :=
  ENNReal.ofReal
    ((Real.sqrt 2) ^ Module.finrank ℝ V * (baseHeatMass V)⁻¹)

/-- The heat-scale ratio between `t` and `t / 2`; this is the exact
cancellation behind the uniform near-field estimate. -/
theorem halfScale_cancel {t : ℝ} (ht : 0 < t) :
    ((heatScale (t / 2)) ^ Module.finrank ℝ V)⁻¹ *
        (heatScale t) ^ Module.finrank ℝ V =
      (Real.sqrt 2) ^ Module.finrank ℝ V := by
  have hhalf : 0 < t / 2 := half_pos ht
  have hscale :
      heatScale t = Real.sqrt 2 * heatScale (t / 2) := by
    rw [heatScale, heatScale, show t = 2 * (t / 2) by ring]
    exact Real.sqrt_mul (by norm_num) _
  rw [hscale, mul_pow]
  calc
    ((heatScale (t / 2)) ^ Module.finrank ℝ V)⁻¹ *
          ((Real.sqrt 2) ^ Module.finrank ℝ V *
            (heatScale (t / 2)) ^ Module.finrank ℝ V) =
        (Real.sqrt 2) ^ Module.finrank ℝ V *
          (((heatScale (t / 2)) ^ Module.finrank ℝ V)⁻¹ *
            (heatScale (t / 2)) ^ Module.finrank ℝ V) := by ring
    _ = (Real.sqrt 2) ^ Module.finrank ℝ V := by
      rw [inv_mul_cancel₀
        (pow_ne_zero _ (heatScale_pos hhalf).ne'), mul_one]

/-- The actual near early heat potential is bounded in `C⁰` by the source
Carleson constant, uniformly in the observation time. -/
theorem heatEarlyNear_norm {T t : ℝ} {C : ℝ≥0∞}
    (ht : 0 < t) (htT : t ≤ T) (f : ℝ × V → F) (x : V)
    (hsrc : SrcCarl T C f) :
    ‖heatEarlyNear t f x‖ₑ ≤ nearHeatC V * C := by
  let K : ℝ :=
    ((heatScale (t / 2)) ^ Module.finrank ℝ V)⁻¹ *
      (baseHeatMass V)⁻¹
  have hK0 : 0 ≤ K := by
    exact mul_nonneg
      (inv_nonneg.mpr (pow_nonneg (Real.sqrt_nonneg _) _))
      (inv_nonneg.mpr (baseHeatMass_pos (V := V)).le)
  have hpoint : ∀ z ∈ earlyCyl t x,
      ‖heatKernel (t - z.1) (x - z.2) • f z‖ₑ ≤
        ENNReal.ofReal K * ENNReal.ofReal ‖f z‖ := by
    intro z hz
    have hdiff : 0 < t - z.1 := by
      have hhalf : t / 2 < t := by linarith
      exact sub_pos.mpr (hz.1.2.trans_lt hhalf)
    have hk0 : 0 ≤ heatKernel (t - z.1) (x - z.2) :=
      heatKernel_nonneg hdiff _
    have hk : heatKernel (t - z.1) (x - z.2) ≤ K := by
      exact heatKernel_half ht hz.1.1.le hz.1.2 _
    calc
      ‖heatKernel (t - z.1) (x - z.2) • f z‖ₑ =
          ENNReal.ofReal
            (heatKernel (t - z.1) (x - z.2) * ‖f z‖) := by
        rw [← ofReal_norm_eq_enorm, norm_smul, Real.norm_eq_abs,
          abs_of_nonneg hk0]
      _ ≤ ENNReal.ofReal (K * ‖f z‖) :=
        ENNReal.ofReal_le_ofReal
          (mul_le_mul_of_nonneg_right hk (norm_nonneg _))
      _ = ENNReal.ofReal K * ENNReal.ofReal ‖f z‖ :=
        ENNReal.ofReal_mul hK0
  have hm : AEMeasurable (fun z : ℝ × V ↦ ENNReal.ofReal ‖f z‖)
      ((stVolume : Measure (ℝ × V)).restrict (earlyCyl t x)) :=
    (hsrc.ae.norm.aemeasurable.ennreal_ofReal).mono_measure
      Measure.restrict_le_self
  have hlocal :
      ∫⁻ z in earlyCyl t x, ENNReal.ofReal ‖f z‖
          ∂(stVolume : Measure (ℝ × V)) ≤
        srcMass f x (heatScale t) := by
    exact lintegral_mono_set (earlyCyl_sub ht.le x)
  have hscaleT : (heatScale t) ^ 2 ≤ T := by
    simpa [heatScale, Real.sq_sqrt ht.le] using htT
  have hcarl : srcMass f x (heatScale t) ≤
      C * ENNReal.ofReal
        ((heatScale t) ^ Module.finrank ℝ V) :=
    hsrc.bound x (heatScale t) (heatScale_pos ht) hscaleT
  have hmass :
      ‖heatEarlyNear t f x‖ₑ ≤
        ENNReal.ofReal K *
          (C * ENNReal.ofReal
            ((heatScale t) ^ Module.finrank ℝ V)) := by
    unfold heatEarlyNear
    calc
      ‖∫ z in earlyCyl t x,
          heatKernel (t - z.1) (x - z.2) • f z
            ∂(stVolume : Measure (ℝ × V))‖ₑ ≤
          ∫⁻ z in earlyCyl t x,
            ‖heatKernel (t - z.1) (x - z.2) • f z‖ₑ
              ∂(stVolume : Measure (ℝ × V)) :=
        enorm_integral_le_lintegral_enorm _
      _ ≤ ∫⁻ z in earlyCyl t x,
          ENNReal.ofReal K * ENNReal.ofReal ‖f z‖
            ∂(stVolume : Measure (ℝ × V)) := by
        apply lintegral_mono_ae
        filter_upwards [ae_restrict_mem (earlyCyl_meas t x)] with z hz
        exact hpoint z hz
      _ = ENNReal.ofReal K *
          (∫⁻ z in earlyCyl t x, ENNReal.ofReal ‖f z‖
            ∂(stVolume : Measure (ℝ × V))) := by
        rw [lintegral_const_mul'' _ hm]
      _ ≤ ENNReal.ofReal K * srcMass f x (heatScale t) :=
        mul_le_mul_left' hlocal _
      _ ≤ ENNReal.ofReal K *
          (C * ENNReal.ofReal
            ((heatScale t) ^ Module.finrank ℝ V)) :=
        mul_le_mul_left' hcarl _
  refine hmass.trans_eq ?_
  have hreal : K * (heatScale t) ^ Module.finrank ℝ V =
      (Real.sqrt 2) ^ Module.finrank ℝ V *
        (baseHeatMass V)⁻¹ := by
    dsimp [K]
    calc
      (((heatScale (t / 2)) ^ Module.finrank ℝ V)⁻¹ *
          (baseHeatMass V)⁻¹) *
            (heatScale t) ^ Module.finrank ℝ V =
          (((heatScale (t / 2)) ^ Module.finrank ℝ V)⁻¹ *
            (heatScale t) ^ Module.finrank ℝ V) *
              (baseHeatMass V)⁻¹ := by ring
      _ = (Real.sqrt 2) ^ Module.finrank ℝ V *
          (baseHeatMass V)⁻¹ := by
        rw [halfScale_cancel (V := V) ht]
  calc
    ENNReal.ofReal K *
        (C * ENNReal.ofReal
          ((heatScale t) ^ Module.finrank ℝ V)) =
      C * (ENNReal.ofReal K *
        ENNReal.ofReal ((heatScale t) ^ Module.finrank ℝ V)) := by
        ac_rfl
    _ = C * ENNReal.ofReal
        (K * (heatScale t) ^ Module.finrank ℝ V) := by
      rw [ENNReal.ofReal_mul hK0]
    _ = C * nearHeatC V := by rw [hreal]; rfl
    _ = nearHeatC V * C := mul_comm _ _

end Euclidean
end Parabolic
end Analysis
end DifferentialGeometry

end
