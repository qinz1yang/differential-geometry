import DifferentialGeometry.Analysis.Integration.Lp.FiniteCover
import Mathlib.Analysis.Calculus.LineDeriv.Measurable
import Mathlib.Topology.MetricSpace.Lipschitz
import Mathlib.MeasureTheory.Function.LocallyIntegrable

noncomputable section

open MeasureTheory Set Filter
open scoped Topology ENNReal

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [MeasurableSpace E] [OpensMeasurableSpace E] {μ : Measure E}

theorem LocallyLipschitzOn.memLp_top_lineDeriv_of_isCompact
    {f : E → ℝ} {Ω B : Set E} (hf : LocallyLipschitzOn Ω f)
    (hΩ : IsOpen Ω) (hB : IsCompact B) (hBΩ : B ⊆ Ω) (v : E) :
    MemLp (fun x => lineDeriv ℝ f x v) ∞ (μ.restrict B) := by
  classical
  have hlocal (x : B) : ∃ V : Set E, IsOpen V ∧ x.1 ∈ V ∧
      MemLp (fun y => lineDeriv ℝ f y v) ∞ (μ.restrict V) := by
    obtain ⟨K, T, hT, hK⟩ := hf (hBΩ x.2)
    rw [hΩ.nhdsWithin_eq (hBΩ x.2)] at hT
    obtain ⟨V, hVT, hV, hxV⟩ := mem_nhds_iff.mp hT
    obtain ⟨g, hg, hfg⟩ := hK.extend_real
    refine ⟨V, hV, hxV, ?_⟩
    have hgLp : MemLp (fun y => lineDeriv ℝ g y v) ∞ (μ.restrict V) :=
      memLp_top_of_bound (aestronglyMeasurable_lineDeriv hg.continuous _)
        (K * ‖v‖) (.of_forall fun _ => norm_lineDeriv_le_of_lipschitz ℝ hg)
    apply MemLp.ae_eq _ hgLp
    filter_upwards [ae_restrict_mem hV.measurableSet] with y hy
    have heq : f =ᶠ[𝓝 y] g := by
      filter_upwards [hV.mem_nhds hy] with z hz
      exact hfg (hVT hz)
    exact heq.lineDeriv_eq.symm
  choose V hV hxV hLp using hlocal
  obtain ⟨s, hs⟩ := hB.elim_finite_subcover V hV (fun x hx => mem_iUnion_of_mem ⟨x, hx⟩ (hxV ⟨x, hx⟩))
  apply memLp_of_finite_ae_cover (fun i : s => V i.1) (fun i => (hV i.1).measurableSet)
  · filter_upwards [ae_restrict_mem hB.measurableSet] with x hx
    obtain ⟨y, hy, hxy⟩ := mem_iUnion₂.mp (hs hx)
    exact mem_iUnion_of_mem ⟨y, hy⟩ hxy
  · intro i
    exact (hLp i.1).mono_measure (Measure.restrict_mono_measure Measure.restrict_le_self _)

theorem LocallyLipschitzOn.memLp_lineDeriv_of_isCompact
    {f : E → ℝ} {Ω B : Set E} (hf : LocallyLipschitzOn Ω f)
    (hΩ : IsOpen Ω) (hB : IsCompact B) (hBΩ : B ⊆ Ω) (hμB : μ B ≠ ∞)
    (v : E) (p : ℝ≥0∞) :
    MemLp (fun x => lineDeriv ℝ f x v) p (μ.restrict B) := by
  let : IsFiniteMeasure (μ.restrict B) := isFiniteMeasure_restrict.mpr hμB
  exact (hf.memLp_top_lineDeriv_of_isCompact hΩ hB hBΩ v).mono_exponent le_top

theorem LocallyLipschitzOn.integrable_lineDeriv_mul_of_hasCompactSupport
    [IsFiniteMeasureOnCompacts μ] {f φ : E → ℝ} {Ω : Set E}
    (hf : LocallyLipschitzOn Ω f) (hφ : Continuous φ)
    (hφc : HasCompactSupport φ) (hφs : tsupport φ ⊆ Ω) (v : E) :
    Integrable (fun x => lineDeriv ℝ f x v * φ x) μ := by
  obtain ⟨C, hC⟩ := (hf.mono hφs).exists_lipschitzOnWith_of_compact hφc
  obtain ⟨g, hg, hfg⟩ := hC.extend_real
  have hgLp : MemLp (fun x => lineDeriv ℝ g x v) ∞ μ :=
    memLp_top_of_bound (aestronglyMeasurable_lineDeriv hg.continuous μ)
      (C * ‖v‖) (.of_forall fun _ => norm_lineDeriv_le_of_lipschitz ℝ hg)
  have hint : Integrable (fun x => lineDeriv ℝ g x v * φ x) μ :=
    (hφ.integrable_of_hasCompactSupport hφc).mul_of_top_right hgLp
  apply hint.congr
  filter_upwards with x
  by_cases hx : φ x = 0
  · rw [hx, mul_zero, mul_zero]
  · have heq : f =ᶠ[𝓝 x] g := by
      filter_upwards [hφ.continuousAt.eventually_ne hx] with y hy
      exact hfg (subset_tsupport φ hy)
    rw [heq.lineDeriv_eq]
