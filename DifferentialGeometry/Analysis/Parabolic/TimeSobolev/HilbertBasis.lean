import DifferentialGeometry.Analysis.Parabolic.TimeSobolev.BochnerL2
import Mathlib.MeasureTheory.Integral.Lebesgue.Add

noncomputable section

open MeasureTheory Set Filter
open scoped ENNReal InnerProductSpace RealInnerProductSpace

namespace DifferentialGeometry.Analysis.Parabolic.TimeSobolev

variable {X : Type*} [NormedAddCommGroup X] [InnerProductSpace ℝ X]
  [CompleteSpace X]
variable {ι : Type*} [Countable ι]
variable {T : ℝ}

def hilbertBasisTimeCoeff (b : HilbertBasis ι ℝ X) (f : timeL2 X T)
    (i : ι) : timeL2 ℝ T :=
  (innerSL ℝ (b i)).compLpL 2 (timeMeasure T) f

omit [CompleteSpace X] [Countable ι] in
theorem hilbertBasisTimeCoeff_coeFn (b : HilbertBasis ι ℝ X)
    (f : timeL2 X T) (i : ι) :
    hilbertBasisTimeCoeff b f i =ᵐ[timeMeasure T]
      fun t => inner ℝ (b i) (f t) :=
  (innerSL ℝ (b i)).coeFn_compLpL f

omit [CompleteSpace X] [Countable ι] in
private theorem summable_inner_sq (b : HilbertBasis ι ℝ X) (x : X) :
    Summable fun i => (inner ℝ (b i) x) ^ 2 := by
  refine (b.summable_inner_mul_inner x x).congr fun i => ?_
  rw [real_inner_comm x (b i)]
  ring

omit [CompleteSpace X] [Countable ι] in
private theorem norm_sq_eq_tsum_inner_sq (b : HilbertBasis ι ℝ X) (x : X) :
    ‖x‖ ^ 2 = ∑' i, (inner ℝ (b i) x) ^ 2 := by
  calc
    ‖x‖ ^ 2 = inner ℝ x x := real_inner_self_eq_norm_sq x |>.symm
    _ = ∑' i, inner ℝ x (b i) * inner ℝ (b i) x :=
      (b.tsum_inner_mul_inner x x).symm
    _ = ∑' i, (inner ℝ (b i) x) ^ 2 := by
      apply tsum_congr
      intro i
      rw [real_inner_comm x (b i)]
      ring

private def hilbertBasisTimeIntegrand (b : HilbertBasis ι ℝ X)
    (f : timeL2 X T) (i : ι) (t : ℝ) : ℝ≥0∞ :=
  ENNReal.ofReal ((inner ℝ (b i) (f t)) ^ 2)

omit [CompleteSpace X] [Countable ι] in
private theorem aemeasurable_hilbertBasisTimeIntegrand
    (b : HilbertBasis ι ℝ X) (f : timeL2 X T) (i : ι) :
    AEMeasurable (hilbertBasisTimeIntegrand b f i) (timeMeasure T) := by
  let _ : MeasurableSpace ℝ := borel ℝ
  let _ : BorelSpace ℝ := ⟨rfl⟩
  have hmeas : AEMeasurable (fun t => inner ℝ (b i) (f t))
      (timeMeasure T) := by
    refine AEMeasurable.congr
      (Lp.aestronglyMeasurable (hilbertBasisTimeCoeff b f i)).aemeasurable ?_
    exact hilbertBasisTimeCoeff_coeFn b f i
  exact (hmeas.pow_const 2).ennreal_ofReal

omit [CompleteSpace X] [Countable ι] in
private theorem lintegral_hilbertBasisTimeIntegrand
    (b : HilbertBasis ι ℝ X) (f : timeL2 X T) (i : ι) :
    ∫⁻ t, hilbertBasisTimeIntegrand b f i t ∂(timeMeasure T) =
      ENNReal.ofReal (‖hilbertBasisTimeCoeff b f i‖ ^ 2) := by
  have hint : Integrable
      (fun t => (inner ℝ (b i) (f t)) ^ 2) (timeMeasure T) := by
    refine (Lp.memLp (hilbertBasisTimeCoeff b f i)).integrable_sq.congr ?_
    filter_upwards [hilbertBasisTimeCoeff_coeFn b f i] with t ht
    rw [ht]
  have hnn : 0 ≤ᵐ[timeMeasure T]
      fun t => (inner ℝ (b i) (f t)) ^ 2 :=
    Eventually.of_forall fun t => sq_nonneg _
  rw [show (∫⁻ t, hilbertBasisTimeIntegrand b f i t ∂(timeMeasure T)) =
      ENNReal.ofReal (∫ t, (inner ℝ (b i) (f t)) ^ 2 ∂(timeMeasure T)) from
    (ofReal_integral_eq_lintegral_ofReal hint hnn).symm]
  congr 1
  rw [TimeSobolev.norm_sq_eq_integral (hilbertBasisTimeCoeff b f i)]
  change (∫ t, (inner ℝ (b i) (f t)) ^ 2 ∂(timeMeasure T)) =
    ∫ t, ‖hilbertBasisTimeCoeff b f i t‖ ^ 2 ∂(timeMeasure T)
  refine integral_congr_ae ?_
  filter_upwards [hilbertBasisTimeCoeff_coeFn b f i] with t ht
  rw [ht, Real.norm_eq_abs, sq_abs]

omit [CompleteSpace X] in
private theorem ennreal_tsum_norm_hilbertBasisTimeCoeff_sq_ne_top
    (b : HilbertBasis ι ℝ X) (f : timeL2 X T) :
    (∑' i, ENNReal.ofReal (‖hilbertBasisTimeCoeff b f i‖ ^ 2)) ≠
      (⊤ : ℝ≥0∞) := by
  have hpoint : ∀ t : ℝ,
      ENNReal.ofReal (‖f t‖ ^ 2) =
        ∑' i, hilbertBasisTimeIntegrand b f i t := by
    intro t
    rw [norm_sq_eq_tsum_inner_sq b (f t),
      ENNReal.ofReal_tsum_of_nonneg (fun i => sq_nonneg _)
        (summable_inner_sq b (f t))]
    rfl
  have hlintegral_eq :
      ∫⁻ t, ENNReal.ofReal (‖f t‖ ^ 2) ∂(timeMeasure T) =
        ∑' i, ∫⁻ t, hilbertBasisTimeIntegrand b f i t ∂(timeMeasure T) := by
    rw [show (∫⁻ t, ENNReal.ofReal (‖f t‖ ^ 2) ∂(timeMeasure T)) =
        ∫⁻ t, (∑' i, hilbertBasisTimeIntegrand b f i t) ∂(timeMeasure T) from
      lintegral_congr hpoint]
    exact lintegral_tsum fun i =>
      aemeasurable_hilbertBasisTimeIntegrand b f i
  have hfint : Integrable (fun t => ‖f t‖ ^ 2) (timeMeasure T) :=
    (memLp_two_iff_integrable_sq_norm (Lp.aestronglyMeasurable f)).mp (Lp.memLp f)
  have hfnn : 0 ≤ᵐ[timeMeasure T] fun t => ‖f t‖ ^ 2 :=
    Eventually.of_forall fun t => sq_nonneg _
  rw [← tsum_congr fun i => lintegral_hilbertBasisTimeIntegrand b f i,
    ← hlintegral_eq, ← ofReal_integral_eq_lintegral_ofReal hfint hfnn]
  exact ENNReal.ofReal_ne_top

omit [CompleteSpace X] in
theorem summable_norm_hilbertBasisTimeCoeff_sq
    (b : HilbertBasis ι ℝ X) (f : timeL2 X T) :
    Summable fun i => ‖hilbertBasisTimeCoeff b f i‖ ^ 2 := by
  refine (ENNReal.summable_toReal
    (ennreal_tsum_norm_hilbertBasisTimeCoeff_sq_ne_top b f)).congr fun i => ?_
  exact ENNReal.toReal_ofReal (sq_nonneg _)

omit [CompleteSpace X] in
theorem norm_sq_eq_tsum_norm_hilbertBasisTimeCoeff
    (b : HilbertBasis ι ℝ X) (f : timeL2 X T) :
    ‖f‖ ^ 2 = ∑' i, ‖hilbertBasisTimeCoeff b f i‖ ^ 2 := by
  have hpoint : ∀ t : ℝ,
      ENNReal.ofReal (‖f t‖ ^ 2) =
        ∑' i, hilbertBasisTimeIntegrand b f i t := by
    intro t
    rw [norm_sq_eq_tsum_inner_sq b (f t),
      ENNReal.ofReal_tsum_of_nonneg (fun i => sq_nonneg _)
        (summable_inner_sq b (f t))]
    rfl
  have hlintegral_eq :
      ∫⁻ t, ENNReal.ofReal (‖f t‖ ^ 2) ∂(timeMeasure T) =
        ∑' i, ∫⁻ t, hilbertBasisTimeIntegrand b f i t ∂(timeMeasure T) := by
    rw [show (∫⁻ t, ENNReal.ofReal (‖f t‖ ^ 2) ∂(timeMeasure T)) =
        ∫⁻ t, (∑' i, hilbertBasisTimeIntegrand b f i t) ∂(timeMeasure T) from
      lintegral_congr hpoint]
    exact lintegral_tsum fun i =>
      aemeasurable_hilbertBasisTimeIntegrand b f i
  have hfint : Integrable (fun t => ‖f t‖ ^ 2) (timeMeasure T) :=
    (memLp_two_iff_integrable_sq_norm (Lp.aestronglyMeasurable f)).mp (Lp.memLp f)
  have hfnn : 0 ≤ᵐ[timeMeasure T] fun t => ‖f t‖ ^ 2 :=
    Eventually.of_forall fun t => sq_nonneg _
  calc
    ‖f‖ ^ 2 = ∫ t, ‖f t‖ ^ 2 ∂(timeMeasure T) :=
      TimeSobolev.norm_sq_eq_integral f
    _ = (∫⁻ t, ENNReal.ofReal (‖f t‖ ^ 2) ∂(timeMeasure T)).toReal :=
      integral_eq_lintegral_of_nonneg_ae hfnn
        ((Lp.aestronglyMeasurable f).norm.pow 2)
    _ = (∑' i, ∫⁻ t, hilbertBasisTimeIntegrand b f i t
        ∂(timeMeasure T)).toReal := by rw [hlintegral_eq]
    _ = (∑' i, ENNReal.ofReal
        (‖hilbertBasisTimeCoeff b f i‖ ^ 2)).toReal := by
      rw [tsum_congr fun i => lintegral_hilbertBasisTimeIntegrand b f i]
    _ = ∑' i, (ENNReal.ofReal
        (‖hilbertBasisTimeCoeff b f i‖ ^ 2)).toReal := by
      rw [ENNReal.tsum_toReal_eq fun i => ENNReal.ofReal_ne_top]
    _ = ∑' i, ‖hilbertBasisTimeCoeff b f i‖ ^ 2 := by
      apply tsum_congr
      intro i
      rw [ENNReal.toReal_ofReal (sq_nonneg _)]

end DifferentialGeometry.Analysis.Parabolic.TimeSobolev

end
