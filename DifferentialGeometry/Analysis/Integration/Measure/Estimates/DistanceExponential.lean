import DifferentialGeometry.Analysis.Integration.Gaussian.AnnularIntegral
import Mathlib.MeasureTheory.Function.L1Space.Integrable
import Mathlib.Analysis.SpecialFunctions.Exp

noncomputable section

open MeasureTheory Set
open scoped ENNReal

namespace DifferentialGeometry.Analysis.Measure

private theorem neg_mul_le_abs_of_mem_unit_interval (a x : ℝ)
    (hx0 : 0 ≤ x) (hx1 : x ≤ 1) : -a * x ≤ |a| := by
  calc
    -a * x ≤ |a| * x := mul_le_mul_of_nonneg_right (neg_le_abs a) hx0
    _ ≤ |a| * 1 := mul_le_mul_of_nonneg_left hx1 (abs_nonneg a)
    _ = |a| := mul_one _

theorem lintegral_exp_neg_mul_dist_lt_top_of_exponential_ball_growth
    {X : Type*} [PseudoMetricSpace X] [MeasurableSpace X]
    (μ : Measure X) (q : X) {C : ℝ≥0∞} (hC : C ≠ ∞) {growth decay : ℝ}
    (hdecay : growth < decay)
    (hball : ∀ r : ℝ, 1 ≤ r →
      μ (Metric.ball q r) ≤ C * ENNReal.ofReal (Real.exp (growth * r))) :
    (∫⁻ x, ENNReal.ofReal (Real.exp (-decay * dist q x)) ∂μ) < ∞ := by
  let w : ℕ → ℝ≥0∞ := fun j =>
    ENNReal.ofReal (Real.exp (|decay| - decay * ((j : ℝ) + 1)))
  have hbound :=
    DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.radial_lintegral_le_inner_add_annuli
      μ (fun x => dist q x) (r := 1) zero_lt_one
      (fun x => ENNReal.ofReal (Real.exp (-decay * dist q x)))
      (ENNReal.ofReal (Real.exp |decay|)) w
      (fun x hx => ENNReal.ofReal_le_ofReal (Real.exp_le_exp.mpr
        (neg_mul_le_abs_of_mem_unit_interval decay (dist q x) dist_nonneg hx.le)))
      (fun j x hlo hhi => by
        apply ENNReal.ofReal_le_ofReal
        apply Real.exp_le_exp.mpr
        have hy0 : 0 ≤ dist q x - ((j : ℝ) + 1) := by simpa using sub_nonneg.mpr hlo
        have hy1 : dist q x - ((j : ℝ) + 1) ≤ 1 := by
          simp only [one_mul] at hhi
          linarith
        have h := neg_mul_le_abs_of_mem_unit_interval decay _ hy0 hy1
        nlinarith)
  have hinner : μ {x | dist q x < 1} < ∞ := by
    have hset : {x | dist q x < 1} = Metric.ball q 1 := by
      ext x
      simp only [mem_ofPred_eq, Metric.mem_ball, dist_comm]
    rw [hset]
    exact (hball 1 le_rfl).trans_lt
      (ENNReal.mul_lt_top (lt_top_iff_ne_top.mpr hC) ENNReal.ofReal_lt_top)
  have hterm (j : ℕ) :
      w j * μ {x | 1 * ((j : ℝ) + 1) ≤ dist q x ∧
        dist q x < 1 * ((j : ℝ) + 2)} ≤
      (C * ENNReal.ofReal (Real.exp (|decay| + 2 * growth - decay))) *
        ENNReal.ofReal (Real.exp ((j : ℝ) * (growth - decay))) := by
    have hsub : {x | 1 * ((j : ℝ) + 1) ≤ dist q x ∧
        dist q x < 1 * ((j : ℝ) + 2)} ⊆ Metric.ball q ((j : ℝ) + 2) := by
      intro x hx
      simpa only [Metric.mem_ball, dist_comm, one_mul] using hx.2
    calc
      _ ≤ w j * μ (Metric.ball q ((j : ℝ) + 2)) :=
        mul_le_mul_right (measure_mono hsub) (w j)
      _ ≤ w j * (C * ENNReal.ofReal (Real.exp (growth * ((j : ℝ) + 2)))) :=
        mul_le_mul_right (hball _ (by linarith [(Nat.cast_nonneg j : (0 : ℝ) ≤ j)])) (w j)
      _ = _ := by
        dsimp only [w]
        have he : |decay| - decay * ((j : ℝ) + 1) + growth * ((j : ℝ) + 2) =
            (|decay| + 2 * growth - decay) + (j : ℝ) * (growth - decay) := by ring
        rw [mul_left_comm, ← ENNReal.ofReal_mul (Real.exp_pos _).le,
          ← Real.exp_add, he, Real.exp_add, ENNReal.ofReal_mul (Real.exp_pos _).le]
        ac_rfl
  have hsum : (∑' j : ℕ, ENNReal.ofReal (Real.exp ((j : ℝ) * (growth - decay)))) < ∞ :=
    (Real.summable_exp_nat_mul_iff.mpr (sub_neg.mpr hdecay)).tsum_ofReal_lt_top
  refine hbound.trans_lt (ENNReal.add_lt_top.2 ⟨?_, ?_⟩)
  · exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top hinner
  · refine (ENNReal.tsum_le_tsum hterm).trans_lt ?_
    rw [ENNReal.tsum_mul_left]
    exact ENNReal.mul_lt_top
      (ENNReal.mul_lt_top (lt_top_iff_ne_top.mpr hC) ENNReal.ofReal_lt_top) hsum

theorem integrable_exp_neg_mul_dist_of_exponential_ball_growth
    {X : Type*} [PseudoMetricSpace X] [MeasurableSpace X] [OpensMeasurableSpace X]
    (μ : Measure X) (q : X) {C : ℝ≥0∞} (hC : C ≠ ∞) {growth decay : ℝ}
    (hdecay : growth < decay)
    (hball : ∀ r : ℝ, 1 ≤ r →
      μ (Metric.ball q r) ≤ C * ENNReal.ofReal (Real.exp (growth * r))) :
    Integrable (fun x => Real.exp (-decay * dist q x)) μ := by
  have hmeas : AEStronglyMeasurable (fun x => Real.exp (-decay * dist q x)) μ :=
    (by fun_prop : Continuous (fun x => Real.exp (-decay * dist q x))).aestronglyMeasurable
  refine ⟨hmeas, ?_⟩
  rw [hasFiniteIntegral_iff_ofReal (Filter.Eventually.of_forall (fun x => (Real.exp_pos _).le))]
  exact lintegral_exp_neg_mul_dist_lt_top_of_exponential_ball_growth μ q hC hdecay hball

theorem integrable_mul_exp_neg_mul_dist_of_exponential_ball_growth
    {X : Type*} [PseudoMetricSpace X] [MeasurableSpace X] [OpensMeasurableSpace X]
    (μ : Measure X) (q : X) {C : ℝ≥0∞} (hC : C ≠ ∞) {growth decay : ℝ}
    (hdecay : growth < decay)
    (hball : ∀ r : ℝ, 1 ≤ r →
      μ (Metric.ball q r) ≤ C * ENNReal.ofReal (Real.exp (growth * r)))
    {f : X → ℝ} (hf : AEStronglyMeasurable f μ) {K : ℝ}
    (hbound : ∀ᵐ x ∂μ, ‖f x‖ ≤ K) :
    Integrable (fun x => f x * Real.exp (-decay * dist q x)) μ := by
  have hg := integrable_exp_neg_mul_dist_of_exponential_ball_growth μ q hC hdecay hball
  apply (hg.const_mul K).mono (hf.mul hg.aestronglyMeasurable)
  filter_upwards [hbound] with x hx
  change ‖f x * Real.exp (-decay * dist q x)‖ ≤ ‖K * Real.exp (-decay * dist q x)‖
  rw [norm_mul, norm_mul]
  apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
  exact hx.trans (by simpa only [Real.norm_eq_abs] using le_abs_self K)

end DifferentialGeometry.Analysis.Measure

end

noncomputable section

open MeasureTheory
open scoped ENNReal

namespace DifferentialGeometry.Analysis.Measure

theorem integrable_exp_neg_mul_of_dist_sub_le_of_exponential_ball_growth
    {X : Type*} [PseudoMetricSpace X] [MeasurableSpace X]
    (μ : Measure X) (q : X) {C : ℝ≥0∞} (hC : C ≠ ∞) {growth decay : ℝ}
    (hdecay : 0 ≤ decay) (hgap : growth < decay)
    (hball : ∀ r : ℝ, 1 ≤ r →
      μ (Metric.ball q r) ≤ C * ENNReal.ofReal (Real.exp (growth * r)))
    {ρ : X → ℝ} (hρ : AEMeasurable ρ μ) {offset : ℝ}
    (hlower : ∀ᵐ x ∂μ, dist q x - offset ≤ ρ x) :
    Integrable (fun x => Real.exp (-decay * ρ x)) μ := by
  have hdist := lintegral_exp_neg_mul_dist_lt_top_of_exponential_ball_growth μ q hC hgap hball
  have hmeas : AEStronglyMeasurable (fun x => Real.exp (-decay * ρ x)) μ :=
    (aemeasurable_const.mul hρ).exp.aestronglyMeasurable
  refine ⟨hmeas, ?_⟩
  rw [hasFiniteIntegral_iff_ofReal (Filter.Eventually.of_forall (fun x => (Real.exp_pos _).le))]
  have hbound : (∫⁻ x, ENNReal.ofReal (Real.exp (-decay * ρ x)) ∂μ) ≤
      ∫⁻ x, ENNReal.ofReal (Real.exp (decay * offset)) *
        ENNReal.ofReal (Real.exp (-decay * dist q x)) ∂μ := by
    apply lintegral_mono_ae
    filter_upwards [hlower] with x hx
    rw [← ENNReal.ofReal_mul (Real.exp_pos _).le, ← Real.exp_add]
    apply ENNReal.ofReal_le_ofReal
    apply Real.exp_le_exp.mpr
    have h := mul_le_mul_of_nonpos_left hx (neg_nonpos.mpr hdecay)
    linarith
  refine hbound.trans_lt ?_
  rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top hdist

theorem integrable_mul_exp_neg_mul_of_dist_sub_le_of_exponential_ball_growth
    {X : Type*} [PseudoMetricSpace X] [MeasurableSpace X]
    (μ : Measure X) (q : X) {C : ℝ≥0∞} (hC : C ≠ ∞) {growth decay : ℝ}
    (hdecay : 0 ≤ decay) (hgap : growth < decay)
    (hball : ∀ r : ℝ, 1 ≤ r →
      μ (Metric.ball q r) ≤ C * ENNReal.ofReal (Real.exp (growth * r)))
    {ρ : X → ℝ} (hρ : AEMeasurable ρ μ) {offset : ℝ}
    (hlower : ∀ᵐ x ∂μ, dist q x - offset ≤ ρ x)
    {f : X → ℝ} (hf : AEStronglyMeasurable f μ) {K : ℝ}
    (hbound : ∀ᵐ x ∂μ, ‖f x‖ ≤ K) :
    Integrable (fun x => f x * Real.exp (-decay * ρ x)) μ := by
  have hg := integrable_exp_neg_mul_of_dist_sub_le_of_exponential_ball_growth
    μ q hC hdecay hgap hball hρ hlower
  exact hg.bdd_mul hf hbound

end DifferentialGeometry.Analysis.Measure

end
