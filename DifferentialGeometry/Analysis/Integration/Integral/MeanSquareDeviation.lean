import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Integral.Average
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.MeasureTheory.SpecificCodomains.WithLp

noncomputable section
open MeasureTheory
open scoped ENNReal

namespace DifferentialGeometry.Analysis

theorem integral_norm_sub_average_sq_le_integral_norm_sub_sq
    {X F : Type*} [MeasurableSpace X] {μ : Measure X} [IsFiniteMeasure μ]
    [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F]
    {f : X → F} (hf : MemLp f 2 μ) (c : F) :
    (∫ x, ‖f x - ⨍ y, f y ∂μ‖ ^ 2 ∂μ) ≤ ∫ x, ‖f x - c‖ ^ 2 ∂μ := by
  let m := ⨍ y, f y ∂μ
  have hres : Integrable (fun x => f x - m) μ :=
    (hf.integrable (by norm_num)).sub (integrable_const m)
  have hresSq : Integrable (fun x => ‖f x - m‖ ^ 2) μ :=
    (hf.sub (memLp_const m)).norm.integrable_sq
  have hcross : Integrable (fun x => inner ℝ (f x - m) (m - c)) μ :=
    hres.inner_const (m - c)
  have hcrosszero : (∫ x, inner ℝ (f x - m) (m - c) ∂μ) = 0 := by
    have hh := integral_inner (𝕜 := ℝ) hres (m - c)
    simp only [real_inner_comm] at hh
    rw [hh, integral_sub_average μ f, inner_zero_right]
  have hpoint (x : X) : ‖f x - c‖ ^ 2 =
      ‖f x - m‖ ^ 2 + 2 * inner ℝ (f x - m) (m - c) + ‖m - c‖ ^ 2 := by
    have heq : f x - c = (f x - m) + (m - c) := by abel
    rw [heq, norm_add_sq_real]
  simp_rw [hpoint]
  have hsum : Integrable (fun x => ‖f x - m‖ ^ 2 +
      2 * inner ℝ (f x - m) (m - c)) μ := hresSq.add (hcross.const_mul 2)
  rw [integral_add hsum (integrable_const _),
    integral_add hresSq (hcross.const_mul 2), integral_const_mul, hcrosszero, mul_zero, add_zero]
  exact le_add_of_nonneg_right (integral_nonneg fun _ => sq_nonneg _)

theorem integral_norm_sub_const_sq_le_two_difference_add
    {X F : Type*} [MeasurableSpace X] {μ : Measure X} [IsFiniteMeasure μ]
    [NormedAddCommGroup F] {f g : X → F}
    (hf : MemLp f 2 μ) (hg : MemLp g 2 μ) (c : F) :
    (∫ x, ‖f x - c‖ ^ 2 ∂μ) ≤
      2 * (∫ x, ‖f x - g x‖ ^ 2 ∂μ) + 2 * ∫ x, ‖g x - c‖ ^ 2 ∂μ := by
  have hdiff : Integrable (fun x => ‖f x - g x‖ ^ 2) μ := (hf.sub hg).norm.integrable_sq
  have hgc : Integrable (fun x => ‖g x - c‖ ^ 2) μ := (hg.sub (memLp_const c)).norm.integrable_sq
  rw [← integral_const_mul, ← integral_const_mul,
    ← integral_add (hdiff.const_mul 2) (hgc.const_mul 2)]
  apply integral_mono_ae (hf.sub (memLp_const c)).norm.integrable_sq
    ((hdiff.const_mul 2).add (hgc.const_mul 2))
  filter_upwards with x
  have hn : ‖f x - c‖ ≤ ‖f x - g x‖ + ‖g x - c‖ := by
    simpa only [sub_add_sub_cancel] using norm_add_le (f x - g x) (g x - c)
  change ‖f x - c‖ ^ 2 ≤ 2 * ‖f x - g x‖ ^ 2 + 2 * ‖g x - c‖ ^ 2
  nlinarith [sq_nonneg (‖f x - g x‖ - ‖g x - c‖), norm_nonneg (f x - c),
    norm_nonneg (f x - g x), norm_nonneg (g x - c)]

end DifferentialGeometry.Analysis

end

noncomputable section
open MeasureTheory
open scoped ENNReal

namespace DifferentialGeometry.Analysis

theorem monotoneOn_integral_norm_sub_average_sq_ball
    {X F : Type*} [PseudoMetricSpace X] [MeasurableSpace X]
    {μ : Measure X}
    [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F]
    {f : X → F} {c : X} {R : ℝ}
    [IsFiniteMeasure (μ.restrict (Metric.ball c R))]
    (hf : MemLp f 2 (μ.restrict (Metric.ball c R))) :
    MonotoneOn (fun r => ∫ x in Metric.ball c r,
      ‖f x - ⨍ y in Metric.ball c r, f y ∂μ‖ ^ 2 ∂μ) (Set.Ioc (0 : ℝ) R) := by
  intro r hr s hs hrs
  have hrR : Metric.ball c r ⊆ Metric.ball c R := Metric.ball_subset_ball hr.2
  have hsR : Metric.ball c s ⊆ Metric.ball c R := Metric.ball_subset_ball hs.2
  have hrs' : Metric.ball c r ⊆ Metric.ball c s := Metric.ball_subset_ball hrs
  let : IsFiniteMeasure (μ.restrict (Metric.ball c s)) :=
    isFiniteMeasure_restrict.mpr
      ((measure_mono hsR).trans_lt
        (by simpa using measure_lt_top (μ.restrict (Metric.ball c R)) Set.univ)).ne
  let : IsFiniteMeasure (μ.restrict (Metric.ball c r)) :=
    isFiniteMeasure_restrict.mpr
      ((measure_mono hrR).trans_lt
        (by simpa using measure_lt_top (μ.restrict (Metric.ball c R)) Set.univ)).ne
  have hfr := hf.mono_measure (Measure.restrict_mono_set μ hrR)
  have hfs := hf.mono_measure (Measure.restrict_mono_set μ hsR)
  let m := ⨍ y in Metric.ball c s, f y ∂μ
  apply (integral_norm_sub_average_sq_le_integral_norm_sub_sq hfr m).trans
  exact setIntegral_mono_set (hfs.sub (memLp_const m)).norm.integrable_sq
    (Filter.Eventually.of_forall fun x => sq_nonneg _) (Filter.Eventually.of_forall hrs')


end DifferentialGeometry.Analysis

end

noncomputable section
open MeasureTheory
open scoped ENNReal

namespace DifferentialGeometry.Analysis

theorem integral_component_sub_average_sq_le_vector_variance
    {X ι : Type*} [MeasurableSpace X] [Fintype ι] {μ : Measure X} [IsFiniteMeasure μ]
    {f : X → EuclideanSpace ℝ ι} (hf : MemLp f 2 μ) (i : ι) :
    (∫ x, (f x i - ⨍ y, f y i ∂μ) ^ 2 ∂μ) ≤
      ∫ x, ‖f x - ⨍ y, f y ∂μ‖ ^ 2 ∂μ := by
  let m := ⨍ y, f y ∂μ
  have hfi : MemLp (fun x => f x i) 2 μ :=
    (PiLp.proj (𝕜 := ℝ) 2 (fun _ : ι => ℝ) i).comp_memLp' hf
  have hh := integral_norm_sub_average_sq_le_integral_norm_sub_sq hfi (m i)
  simp only [Real.norm_eq_abs, sq_abs] at hh
  apply hh.trans
  apply integral_mono_ae (hfi.sub (memLp_const (m i))).integrable_sq
    (hf.sub (memLp_const m)).norm.integrable_sq
  filter_upwards with x
  change (f x i - m i) ^ 2 ≤ ‖f x - m‖ ^ 2
  have hp := PiLp.norm_apply_le (f x - m) i
  simpa only [PiLp.sub_apply, Real.norm_eq_abs, sq_abs] using
    pow_le_pow_left₀ (norm_nonneg _) hp 2

end DifferentialGeometry.Analysis

end
