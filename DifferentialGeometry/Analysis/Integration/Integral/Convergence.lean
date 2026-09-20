import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Topology.UniformSpace.UniformConvergence

noncomputable section
open Filter MeasureTheory
open scoped Topology

private theorem integral_le_of_tendsto_ae_of_nonneg
    {α ι : Type*} [MeasurableSpace α] {μ : Measure α}
    {l : Filter ι} [l.NeBot] [l.IsCountablyGenerated]
    {F : ι → α → ℝ} {f : α → ℝ} {L : ℝ}
    (hFi : ∀ i, Integrable (F i) μ) (hF0 : ∀ i, 0 ≤ᵐ[μ] F i)
    (hlim : ∀ᵐ x ∂μ, Tendsto (fun i => F i x) l (𝓝 (f x)))
    (hint : Tendsto (fun i => ∫ x, F i x ∂μ) l (𝓝 L)) :
    Integrable f μ ∧ ∫ x, f x ∂μ ≤ L := by
  have hfm : AEStronglyMeasurable f μ :=
    aestronglyMeasurable_of_tendsto_ae l (fun i => (hFi i).aestronglyMeasurable) hlim
  obtain ⟨seq, hseq⟩ := l.exists_seq_tendsto
  have hf0 : 0 ≤ᵐ[μ] f := by
    filter_upwards [hlim, ae_all_iff.mpr (fun n => hF0 (seq n))] with x hx hpos
    exact ge_of_tendsto (hx.comp hseq) (Eventually.of_forall hpos)
  have hL0 : 0 ≤ L := ge_of_tendsto hint
    (Eventually.of_forall fun i => integral_nonneg_of_ae (hF0 i))
  have hfatou : (∫⁻ x, ENNReal.ofReal (f x) ∂μ) ≤ ENNReal.ofReal L := by
    calc
      _ = ∫⁻ x, liminf (fun i => ENNReal.ofReal (F i x)) l ∂μ := by
        apply lintegral_congr_ae
        filter_upwards [hlim] with x hx
        exact (ENNReal.tendsto_ofReal hx).liminf_eq.symm
      _ ≤ liminf (fun i => ∫⁻ x, ENNReal.ofReal (F i x) ∂μ) l :=
        lintegral_liminf_le' (fun i => (hFi i).aestronglyMeasurable.aemeasurable.ennreal_ofReal)
      _ = ENNReal.ofReal L := by
        simp_rw [← ofReal_integral_eq_lintegral_ofReal (hFi _) (hF0 _)]
        exact (ENNReal.tendsto_ofReal hint).liminf_eq
  have hfi : Integrable f μ := (lintegral_ofReal_ne_top_iff_integrable hfm hf0).mp
    (ne_top_of_le_ne_top ENNReal.ofReal_ne_top hfatou)
  refine ⟨hfi, ?_⟩
  rw [← ofReal_integral_eq_lintegral_ofReal hfi hf0] at hfatou
  exact (ENNReal.ofReal_le_ofReal_iff hL0).mp hfatou

theorem MeasureTheory.integrable_and_integral_le_of_tendsto_ae
    {α ι : Type*} [MeasurableSpace α] {μ : Measure α}
    {l : Filter ι} [l.NeBot] [l.IsCountablyGenerated]
    {F : ι → α → ℝ} {f g : α → ℝ} {L : ℝ}
    (hFi : ∀ i, Integrable (F i) μ) (hg : Integrable g μ)
    (hFg : ∀ i, g ≤ᵐ[μ] F i)
    (hlim : ∀ᵐ x ∂μ, Tendsto (fun i => F i x) l (𝓝 (f x)))
    (hint : Tendsto (fun i => ∫ x, F i x ∂μ) l (𝓝 L)) :
    Integrable f μ ∧ ∫ x, f x ∂μ ≤ L := by
  have hi (i : ι) : Integrable (fun x => F i x - g x) μ := (hFi i).sub hg
  have hpos (i : ι) : 0 ≤ᵐ[μ] (fun x => F i x - g x) :=
    (hFg i).mono fun x hx => sub_nonneg.mpr hx
  have hp : ∀ᵐ x ∂μ, Tendsto (fun i => F i x - g x) l (𝓝 (f x - g x)) :=
    hlim.mono fun x hx => hx.sub_const (g x)
  have hI : Tendsto (fun i => ∫ x, F i x - g x ∂μ) l (𝓝 (L - ∫ x, g x ∂μ)) := by
    simp_rw [integral_sub (hFi _) hg]
    exact hint.sub_const _
  obtain ⟨hfg, hle⟩ := integral_le_of_tendsto_ae_of_nonneg hi hpos hp hI
  have hf : Integrable f μ := by
    have h : Integrable (fun x => (f x - g x) + g x) μ := hfg.add hg
    simpa only [sub_add_cancel] using h
  rw [integral_sub hf hg] at hle
  exact ⟨hf, by linarith⟩

theorem TendstoUniformlyOn.integral_smul
    {α E ι : Type*} [MeasurableSpace α]
    [NormedAddCommGroup E] [NormedSpace ℝ E] {μ : Measure α}
    {l : Filter ι} {F : ι → α → E} {f : α → E} {w : α → ℝ}
    (h : TendstoUniformlyOn F f l (Function.support w)) (hw : Integrable w μ)
    (hFi : ∀ᶠ i in l, Integrable (fun x => w x • F i x) μ)
    (hfi : Integrable (fun x => w x • f x) μ) :
    Tendsto (fun i => ∫ x, w x • F i x ∂μ) l (𝓝 (∫ x, w x • f x ∂μ)) := by
  rw [Metric.tendsto_nhds]
  intro ε hε
  let I := ∫ x, ‖w x‖ ∂μ
  have hI : 0 ≤ I := integral_nonneg (fun x => norm_nonneg _)
  let η := ε / (I + 1)
  have hη : 0 < η := div_pos hε (by positivity)
  filter_upwards [hFi, Metric.tendstoUniformlyOn_iff.mp h η hη] with i hi hclose
  rw [dist_eq_norm, ← integral_sub hi hfi]
  have hb (x : α) : ‖w x • F i x - w x • f x‖ ≤ η * ‖w x‖ := by
    by_cases hx : w x = 0
    · simp only [hx, zero_smul, sub_self, norm_zero, mul_zero, le_refl]
    rw [← smul_sub, norm_smul]
    have hn : ‖F i x - f x‖ ≤ η := by
      rw [norm_sub_rev]
      simpa only [dist_eq_norm] using (hclose x hx).le
    exact (mul_le_mul_of_nonneg_left hn (norm_nonneg _)).trans_eq (mul_comm _ _)
  have hnorm := norm_integral_le_of_norm_le (hw.norm.const_mul η) (ae_of_all μ hb)
  rw [integral_const_mul] at hnorm
  refine hnorm.trans_lt ?_
  change η * I < ε
  have heq : η * (I + 1) = ε := div_mul_cancel₀ ε (by positivity : I + 1 ≠ 0)
  nlinarith
