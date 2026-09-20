import DifferentialGeometry.Geometry.Comparison.DistanceCutoff
import Mathlib.MeasureTheory.Integral.DominatedConvergence

noncomputable section

open Filter MeasureTheory
open scoped Manifold ContDiff ENNReal NNReal Topology

namespace DifferentialGeometry.Analysis

open Geometry.Operator Geometry.Riemannian

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M]

theorem tendsto_integral_abs_inner_grad_distance_cutoff
    {Q ι : Type*} [MeasurableSpace Q] (μ : Measure Q)
    {l : Filter ι} [l.IsCountablyGenerated] (a : ι → ℝ≥0) (ha : Tendsto a l (𝓝 0))
    (g : SmoothRiemannianMetric I M) (h : Q → SmoothRiemannianMetric I M)
    (hgh : ∀ᵐ q ∂μ, ∀ x v, g.inner x v v ≤ (h q).inner x v v)
    (o : M) (x : Q → M) (V : ∀ q, TangentSpace I (x q))
    (C : ℝ≥0) {w : Q → ℝ} (hw : Integrable w μ) (hw0 : ∀ᵐ q ∂μ, 0 ≤ w q)
    (hV : ∀ᵐ q ∂μ, Real.sqrt ((h q).inner (x q) (V q) (V q)) ≤
      C * (1 + (riemannianEDistOf g o (x q)).toReal) * w q)
    (hmeas : ∀ᶠ i in l, AEStronglyMeasurable (fun q => (h q).inner (x q) (V q)
      (gradFun (h q) (fun y => CutoffProfile.evalue
        ((a i : ℝ≥0∞) * riemannianEDistOf g o y)) (x q))) μ) :
    Tendsto (fun i => ∫ q, |(h q).inner (x q) (V q)
      (gradFun (h q) (fun y => CutoffProfile.evalue
        ((a i : ℝ≥0∞) * riemannianEDistOf g o y)) (x q))| ∂μ) l (𝓝 0) := by
  have haR : Tendsto (fun i => (a i : ℝ)) l (𝓝 0) :=
    NNReal.continuous_coe.continuousAt.tendsto.comp ha
  have ha1 : ∀ᶠ i in l, (a i : ℝ) ≤ 1 :=
    (haR.eventually (gt_mem_nhds (by norm_num : (0 : ℝ) < 1))).mono fun i hi => hi.le
  have hb : ∀ᶠ i in l, ∀ᵐ q ∂μ,
      ‖(h q).inner (x q) (V q) (gradFun (h q) (fun y => CutoffProfile.evalue
        ((a i : ℝ≥0∞) * riemannianEDistOf g o y)) (x q))‖ ≤
          (3 * CutoffProfile.derivBound * C) * w q := by
    filter_upwards [ha1] with i hi
    filter_upwards [hw0, hV, hgh] with q hqw hqV hqg
    rw [Real.norm_eq_abs]
    refine (abs_inner_grad_distance_cutoff_le_of_linear_growth
      g (h q) hqg o (a i) C (x q) (V q) hqw hqV).trans ?_
    have hc : 0 ≤ CutoffProfile.derivBound * C :=
      mul_nonneg CutoffProfile.derivBound_nonneg C.coe_nonneg
    apply mul_le_mul_of_nonneg_right _ hqw
    calc
      _ ≤ CutoffProfile.derivBound * C * 3 :=
        mul_le_mul_of_nonneg_left (by linarith) hc
      _ = _ := by ring
  have hlim : ∀ᵐ q ∂μ, Tendsto (fun i => (h q).inner (x q) (V q)
      (gradFun (h q) (fun y => CutoffProfile.evalue
        ((a i : ℝ≥0∞) * riemannianEDistOf g o y)) (x q))) l (𝓝 0) := by
    filter_upwards [hgh] with q hqg
    apply squeeze_zero_norm (a := fun i => Real.sqrt ((h q).inner (x q) (V q) (V q)) *
      (CutoffProfile.derivBound * (a i : ℝ)))
    · intro i
      rw [Real.norm_eq_abs]
      exact (abs_inner_le_sqrt_mul_sqrt (h q) (x q) (V q) _).trans
        (mul_le_mul_of_nonneg_left
          (grad_norm_distance_cutoff_le g (h q) hqg o (a i) (x q)) (Real.sqrt_nonneg _))
    · simpa only [mul_zero] using (haR.const_mul CutoffProfile.derivBound).const_mul
        (Real.sqrt ((h q).inner (x q) (V q) (V q)))
  have hma := hmeas.mono fun i hi => hi.norm
  have hh := tendsto_integral_filter_of_dominated_convergence (f := fun _ : Q => (0 : ℝ))
    (fun q => (3 * CutoffProfile.derivBound * C) * w q) hma
    (by simpa only [norm_norm] using hb) (hw.const_mul _)
    (hlim.mono fun q hq => by simpa only [norm_zero] using hq.norm)
  simpa only [integral_zero, Real.norm_eq_abs] using hh

end DifferentialGeometry.Analysis
