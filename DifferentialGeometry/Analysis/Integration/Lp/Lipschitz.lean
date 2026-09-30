import DifferentialGeometry.Analysis.Calculus.Rademacher
import DifferentialGeometry.Analysis.Integration.Lp.FiniteCover
import Mathlib.Analysis.Calculus.LineDeriv.Measurable
import DifferentialGeometry.Topology.MetricSpace.Lipschitz
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

theorem LocallyLipschitzOn.integrable_fderiv_fderiv_mul_of_hasCompactSupport
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [MeasurableSpace E] [BorelSpace E] {μ : Measure E} [μ.IsAddHaarMeasure]
    {u ψ : E → ℝ} {Ω : Set E} (hdu : LocallyLipschitzOn Ω (fderiv ℝ u)) (hΩ : IsOpen Ω)
    (hψ : Continuous ψ) (hψc : HasCompactSupport ψ) (hψs : tsupport ψ ⊆ Ω) (v w : E) :
    Integrable (fun x => fderiv ℝ (fderiv ℝ u) x v w * ψ x) μ := by
  apply (integrableOn_iff_integrable_of_support_subset
    ((subset_tsupport _).trans (tsupport_mul_subset_right.trans hψs))).mp
  have hw : LocallyLipschitzOn Ω (fun x => fderiv ℝ u x w) :=
    ((ContinuousLinearMap.apply ℝ ℝ w).lipschitzWith.locallyLipschitz.locallyLipschitzOn).comp
      hdu (Set.mapsTo_univ _ _)
  apply (hw.integrable_lineDeriv_mul_of_hasCompactSupport hψ hψc hψs v).integrableOn.congr
  filter_upwards [hdu.ae_differentiableAt hΩ] with x hx
  rw [(hx.clm_apply (differentiableAt_const w)).lineDeriv_eq_fderiv,
    fderiv_clm_apply hx (differentiableAt_const w)]
  simp

theorem MeasureTheory.LocallyIntegrableOn.integrable_mul_fderiv_of_hasCompactSupport
    {b φ : E → ℝ} {Ω : Set E} (hb : LocallyIntegrableOn b Ω μ)
    (hΩ : IsOpen Ω) (hφ : LocallyLipschitzOn Ω φ)
    (hφc : HasCompactSupport φ) (hφs : tsupport φ ⊆ Ω) (v : E) :
    Integrable (fun x => b x * fderiv ℝ φ x v) μ := by
  obtain ⟨C, hC⟩ := hφ.exists_lipschitzWith_of_hasCompactSupport hΩ hφc hφs
  have hs : Function.support (fun x => b x * fderiv ℝ φ x v) ⊆ tsupport φ :=
    (subset_tsupport _).trans (tsupport_mul_subset_right.trans (tsupport_fderiv_apply_subset ℝ v))
  apply (integrableOn_iff_integrable_of_support_subset hs).mp
  apply (hb.integrableOn_compact_subset hφs hφc).mul_bdd (c := (C : ℝ) * ‖v‖)
    (measurable_fderiv_apply_const ℝ φ v).aestronglyMeasurable
  filter_upwards [] with x
  exact ((fderiv ℝ φ x).le_opNorm v).trans
    (mul_le_mul_of_nonneg_right (norm_fderiv_le_of_lipschitz ℝ hC) (norm_nonneg _))
