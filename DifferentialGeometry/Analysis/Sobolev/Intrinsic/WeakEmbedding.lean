import DifferentialGeometry.Analysis.Sobolev.Intrinsic.WeakChartSobolev
import DifferentialGeometry.Analysis.Sobolev.Manifold.Embedding.Subcritical
import DifferentialGeometry.Analysis.Integration.EntropyLp

set_option autoImplicit false

noncomputable section

open Bundle Manifold Set MeasureTheory Filter
open scoped Manifold Topology ContDiff ENNReal

namespace DifferentialGeometry.Analysis.Sobolev.IntrinsicLp

open DifferentialGeometry.Integral.Measure

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [Module.Finite ℝ E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

private local instance : MeasurableSpace M := borel M
private local instance : BorelSpace M := ⟨rfl⟩

variable [CompactSpace M] [T2Space M] [I.Boundaryless]


theorem MemW1pIntrinsicLp.memLp_subcritical [NeZero (Module.finrank ℝ E)]
    {g : SmoothRiemannianMetric I M} {p : ℝ} (hp : 1 ≤ p)
    (hpdim : p < (Module.finrank ℝ E : ℝ)) {u : M → ℝ}
    (hu : MemW1pIntrinsicLp g (ENNReal.ofReal p) u) :
    MemLp u (ENNReal.ofReal
      ((Module.finrank ℝ E : ℝ) * p / ((Module.finrank ℝ E : ℝ) - p)))
      (riemannianVolumeMeasure I M g) := by
  have hpE : (1 : ℝ≥0∞) ≤ ENNReal.ofReal p := by
    simpa only [ENNReal.ofReal_one] using ENNReal.ofReal_le_ofReal hp
  obtain ⟨hu, G, hG, hGn⟩ := hu
  let v : M → ℝ := hu.aestronglyMeasurable.mk u
  have huv : u =ᵐ[riemannianVolumeMeasure I M g] v := hu.aestronglyMeasurable.ae_eq_mk
  have hvmeas : Measurable v := hu.aestronglyMeasurable.measurable_mk
  have hv : MemW1pIntrinsicLp g (ENNReal.ofReal p) v :=
    ⟨hu.ae_eq huv, G, hG.congr_fun_ae huv, hGn⟩
  have hchart := hv.memWkpChart hpE
  obtain ⟨C, _hC, hbound⟩ := Chart.sobolev_closed g hp hpdim
  have hvLp : MemLp v (ENNReal.ofReal
      ((Module.finrank ℝ E : ℝ) * p / ((Module.finrank ℝ E : ℝ) - p)))
      (riemannianVolumeMeasure I M g) := by
    refine ⟨hvmeas.aestronglyMeasurable, ?_⟩
    exact (hbound hvmeas hchart).trans_lt
      (ENNReal.mul_lt_top ENNReal.ofReal_lt_top (Chart.wkpNormChart_lt_top_of_memWkpChart hpE hchart))
  exact hvLp.ae_eq huv.symm


theorem MemW1pIntrinsicLp.exists_memLp_gt_two
    {g : SmoothRiemannianMetric I M} (hdim : 2 ≤ Module.finrank ℝ E)
    {u : M → ℝ} (hu : MemW1pIntrinsicLp g 2 u) :
    ∃ q : ℝ, 2 < q ∧ MemLp u (ENNReal.ofReal q) (riemannianVolumeMeasure I M g) := by
  let n : ℝ := Module.finrank ℝ E
  have hn : 2 ≤ n := by
    change (2 : ℝ) ≤ (Module.finrank ℝ E : ℝ)
    exact_mod_cast hdim
  let p : ℝ := 2 * n / (n + 1)
  have hden : 0 < n + 1 := by linarith
  have hp : 1 ≤ p := (le_div_iff₀ hden).2 (by nlinarith)
  have hp2 : p ≤ 2 := (div_le_iff₀ hden).2 (by nlinarith)
  have hpdim : p < n := (div_lt_iff₀ hden).2 (by nlinarith)
  have hnd : 0 < n - p := sub_pos.mpr hpdim
  have hq : 2 < n * p / (n - p) := by
    apply (lt_div_iff₀ hnd).2
    have hpgt : 2 * n / (n + 2) < p := by
      dsimp only [p]
      apply (div_lt_div_iff₀ (by linarith) hden).2
      nlinarith
    have := (div_lt_iff₀ (by linarith : 0 < n + 2)).1 hpgt
    nlinarith
  let : NeZero (Module.finrank ℝ E) := ⟨by omega⟩
  let : IsFiniteMeasure (riemannianVolumeMeasure I M g) :=
    riemannianVolumeMeasure_isFiniteMeasure_of_compactSpace g
  have hpE : ENNReal.ofReal p ≤ (2 : ℝ≥0∞) := by
    simpa only [ENNReal.ofReal_ofNat] using ENNReal.ofReal_le_ofReal hp2
  obtain ⟨hu, G, hG, hGn⟩ := hu
  have hup : MemW1pIntrinsicLp g (ENNReal.ofReal p) u :=
    ⟨hu.mono_exponent hpE, G, hG, hGn.mono_exponent hpE⟩
  exact ⟨_, hq, hup.memLp_subcritical hp hpdim⟩


theorem MemW1pIntrinsicLp.integrable_sq_mul_log_sq
    {g : SmoothRiemannianMetric I M} (hdim : 2 ≤ Module.finrank ℝ E)
    {u : M → ℝ} (hu : MemW1pIntrinsicLp g 2 u) :
    Integrable (fun x => u x ^ 2 * Real.log (u x ^ 2)) (riemannianVolumeMeasure I M g) := by
  let : IsFiniteMeasure (riemannianVolumeMeasure I M g) :=
    riemannianVolumeMeasure_isFiniteMeasure_of_compactSpace g
  obtain ⟨q, hq, huq⟩ := hu.exists_memLp_gt_two hdim
  exact Integration.integrable_sq_mul_log_sq_of_memLp hq huq

end DifferentialGeometry.Analysis.Sobolev.IntrinsicLp
