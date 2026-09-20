import DifferentialGeometry.Analysis.Integration.Measure.Affine
import DifferentialGeometry.Analysis.Sobolev.Euclidean.WeakDerivative.Affine
import DifferentialGeometry.Analysis.Integration.LpNorm
import Mathlib.MeasureTheory.Function.ContinuousMapDense
import Mathlib.MeasureTheory.Integral.DominatedConvergence

section

noncomputable section

open Filter MeasureTheory Set
open scoped ENNReal NNReal Topology

namespace MeasureTheory

variable {d : ℕ}
local notation "E" => EuclideanSpace ℝ (Fin d)

private theorem map_affine_le_volume_of_one_le (b : E) {r : ℝ} (hr : 1 ≤ r) :
    (volume : Measure E).map (fun x => b + r • x) ≤ volume := by
  have hr0 : 0 < r := zero_lt_one.trans_le hr
  rw [Measure.map_add_smul_addHaar volume b hr0.ne']
  have hcoef : ENNReal.ofReal |(r ^ Module.finrank ℝ E)⁻¹| ≤ 1 := by
    apply ENNReal.ofReal_le_one.mpr
    rw [abs_of_nonneg (inv_nonneg.mpr (pow_nonneg hr0.le _))]
    exact inv_le_one_of_one_le₀ (one_le_pow₀ hr)
  calc
    _ ≤ (1 : ℝ≥0∞) • (volume : Measure E) := by gcongr
    _ = _ := one_smul _ _

theorem eLpNorm_comp_add_smul_le_of_one_le
    {F : Type*} [NormedAddCommGroup F] {p : ℝ≥0∞} {f : E → F}
    (hf : MemLp f p volume) (b : E) {r : ℝ} (hr : 1 ≤ r) :
    eLpNorm (fun x => f (b + r • x)) p volume ≤ eLpNorm f p volume := by
  have hm := map_affine_le_volume_of_one_le b hr
  have hfm := hf.mono_measure hm
  change eLpNorm (f ∘ fun x => b + r • x) p volume ≤ _
  rw [← eLpNorm_map_measure hfm.aestronglyMeasurable
    ((measurable_const_add b).comp (measurable_const_smul r)).aemeasurable]
  exact eLpNorm_mono_measure f hm

theorem tendsto_eLpNorm_comp_add_smul_sub_on_ball
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] {f : E → F}
    (hf : MemLp f 2 volume) (c : E) (R : ℝ)
    {rn : ℕ → ℝ} (hrn : ∀ n, 1 ≤ rn n) (hrlim : Tendsto rn atTop (𝓝 1)) :
    Tendsto (fun n => eLpNorm (fun x => f ((1 - rn n) • c + rn n • x) - f x) 2
      (volume.restrict (Metric.ball c R))) atTop (𝓝 0) := by
  let μ := volume.restrict (Metric.ball c R)
  let _ : IsFiniteMeasure μ := isFiniteMeasure_restrict.mpr measure_ball_lt_top.ne
  let S (n : ℕ) (x : E) := (1 - rn n) • c + rn n • x
  have hSc (n : ℕ) : Continuous (S n) := by dsimp only [S]; fun_prop
  have hSlim (x : E) : Tendsto (fun n => S n x) atTop (𝓝 x) := by
    simpa only [S, sub_self, zero_smul, one_smul, zero_add] using
      (((tendsto_const_nhds (x := (1 : ℝ))).sub hrlim).smul_const c).add (hrlim.smul_const x)
  have hfm (n : ℕ) : MemLp (fun x => f (S n x)) 2 volume := by
    have h := hf.mono_measure (map_affine_le_volume_of_one_le ((1 - rn n) • c) (hrn n))
    exact h.comp_of_map (hSc n).measurable.aemeasurable
  apply ENNReal.tendsto_nhds_zero.mpr
  intro ε hε
  by_cases hεtop : ε = ∞
  · simp only [hεtop, le_top, eventually_true]
  let δ : ℝ := ε.toReal / 3
  have hδ : 0 < δ := div_pos (ENNReal.toReal_pos hε.ne' hεtop) (by norm_num)
  obtain ⟨g, hfg, hgm⟩ := hf.exists_boundedContinuous_eLpNorm_sub_le
    (by norm_num) (ENNReal.ofReal_pos.mpr hδ).ne'
  have hmidInt : Tendsto (fun n => ∫ x, ‖g (S n x) - g x‖ ^ 2 ∂μ) atTop (𝓝 0) := by
    have h := tendsto_integral_of_dominated_convergence (μ := μ)
      (F := fun n x => ‖g (S n x) - g x‖ ^ 2) (f := fun _ : E => (0 : ℝ))
      (fun _ : E => (2 * ‖g‖) ^ 2)
      (fun n => (((g.continuous.comp (hSc n)).sub g.continuous).norm.pow 2).aestronglyMeasurable)
      (integrable_const _) (fun n => Eventually.of_forall fun x => ?_)
      (Eventually.of_forall fun x => ?_)
    · simpa only [integral_zero] using h
    · rw [norm_pow, norm_norm]
      apply pow_le_pow_left₀ (norm_nonneg _)
      exact (norm_sub_le _ _).trans (by
          change ‖g (S n x)‖ + ‖g x‖ ≤ 2 * ‖g‖
          linarith [g.norm_coe_le_norm (S n x), g.norm_coe_le_norm x])
    · simpa only [Function.comp_apply, sub_self, norm_zero, zero_pow (by norm_num : 2 ≠ 0)] using
        (((g.continuous.tendsto x).comp (hSlim x)).sub (tendsto_const_nhds (x := g x))).norm.pow 2
  have hmid : Tendsto (fun n => eLpNorm (fun x => g (S n x) - g x) 2 μ) atTop (𝓝 0) := by
    have hlim := (ENNReal.continuous_ofReal.tendsto (Real.sqrt 0)).comp
      (Real.continuous_sqrt.tendsto 0 |>.comp hmidInt)
    simp only [Real.sqrt_zero, ENNReal.ofReal_zero] at hlim
    apply tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hlim (fun _ => zero_le)
    intro n
    have hm : MemLp (fun x => g (S n x) - g x) 2 μ := by
      apply MemLp.of_bound
        (((g.continuous.comp (hSc n)).sub g.continuous).aestronglyMeasurable) (2 * ‖g‖)
      exact Eventually.of_forall fun x =>
        (norm_sub_le _ _).trans (by
          change ‖g (S n x)‖ + ‖g x‖ ≤ 2 * ‖g‖
          linarith [g.norm_coe_le_norm (S n x), g.norm_coe_le_norm x])
    exact DifferentialGeometry.Analysis.Integration.eLpNorm_two_le_of_integral_norm_sq_le hm le_rfl
  filter_upwards [ENNReal.tendsto_nhds_zero.mp hmid (ENNReal.ofReal δ)
    (ENNReal.ofReal_pos.mpr hδ)] with n hn
  have hfirst : eLpNorm (fun x => f (S n x) - g (S n x)) 2 μ ≤ ENNReal.ofReal δ :=
    (eLpNorm_mono_measure _ Measure.restrict_le_self).trans
      ((eLpNorm_comp_add_smul_le_of_one_le (hf.sub hgm) ((1 - rn n) • c) (hrn n)).trans hfg)
  have hlast : eLpNorm (fun x => g x - f x) 2 μ ≤ ENNReal.ofReal δ := by
    change eLpNorm ((g : E → F) - f) 2 μ ≤ _
    rw [eLpNorm_sub_comm]
    exact (eLpNorm_mono_measure _ Measure.restrict_le_self).trans hfg
  have hgmSn : MemLp (fun x => g (S n x)) 2 volume :=
    (hgm.mono_measure (map_affine_le_volume_of_one_le ((1 - rn n) • c) (hrn n))).comp_of_map
      (hSc n).measurable.aemeasurable
  have htri := eLpNorm_add_le
    (((hfm n).sub hgmSn).restrict (Metric.ball c R)).aestronglyMeasurable
    ((hgmSn.sub hgm).restrict (Metric.ball c R)).aestronglyMeasurable (by norm_num : 1 ≤ (2 : ℝ≥0∞))
  have htri' := eLpNorm_add_le
    ((((hfm n).sub hgmSn).add (hgmSn.sub hgm)).restrict (Metric.ball c R)).aestronglyMeasurable
    ((hgm.sub hf).restrict (Metric.ball c R)).aestronglyMeasurable (by norm_num : 1 ≤ (2 : ℝ≥0∞))
  have hbound : eLpNorm (fun x => f (S n x) - f x) 2 μ ≤
      ENNReal.ofReal δ + ENNReal.ofReal δ + ENNReal.ofReal δ := by
    calc
      _ = eLpNorm ((fun x => f (S n x) - g (S n x)) +
          (fun x => g (S n x) - g x) + (fun x => g x - f x)) 2 μ := by
        congr 1
        funext x
        simp only [Pi.add_apply, sub_add_sub_cancel]
      _ ≤ _ := htri'.trans (add_le_add (htri.trans (add_le_add hfirst hn)) hlast)
  apply hbound.trans
  rw [← ENNReal.ofReal_add hδ.le hδ.le, ← ENNReal.ofReal_add (by positivity) hδ.le,
    ← ENNReal.ofReal_toReal hεtop]
  apply ENNReal.ofReal_le_ofReal
  dsimp only [δ]
  linarith

end MeasureTheory

end

end
