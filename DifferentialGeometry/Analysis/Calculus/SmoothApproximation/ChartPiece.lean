import DifferentialGeometry.Analysis.Calculus.SmoothApproximation.ChartApproximation

set_option autoImplicit false

noncomputable section

open Set Function Filter
open scoped Topology ContDiff

namespace DifferentialGeometry.Analysis

private theorem support_chart_piece_subset {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (e : OpenPartialHomeomorph E E) {σ : E → ℝ} {K : Set E}
    (hσK : ∀ y ∈ e.target, e.symm y ∉ K → σ y = 0) :
    support (e.target.indicator (fun y => σ y • e.symm y)) ⊆ e '' K := by
  intro y hy
  by_cases hyt : y ∈ e.target
  · have hσy : σ y ≠ 0 := by
      intro h0
      apply hy
      rw [indicator_of_mem hyt, h0, zero_smul]
    by_cases hyK : e.symm y ∈ K
    · exact ⟨e.symm y, hyK, e.right_inv hyt⟩
    · exact absurd (hσK y hyt hyK) hσy
  · exact absurd (indicator_of_notMem hyt (fun y => σ y • e.symm y)) hy

private theorem support_chart_piece_comp_subset {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (e : OpenPartialHomeomorph E E) {σ : E → ℝ} {K : Set E}
    (hσK : ∀ y ∈ e.target, e.symm y ∉ K → σ y = 0) :
    support (e.source.indicator (fun z => σ (e z) • z)) ⊆ K := by
  intro x hx
  by_cases hxs : x ∈ e.source
  · by_contra hxK
    apply hx
    rw [indicator_of_mem hxs]
    have hnot : e.symm (e x) ∉ K := by
      rw [e.left_inv hxs]
      exact hxK
    rw [hσK (e x) (e.map_source hxs) hnot, zero_smul]
  · exact absurd (indicator_of_notMem hxs (fun z => σ (e z) • z)) hx

private theorem chart_piece_indicator_comp_eq {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (e : OpenPartialHomeomorph E E) (σ : E → ℝ) :
    e.source.indicator (e.target.indicator (fun y => σ y • e.symm y) ∘ e) =
      e.source.indicator (fun z => σ (e z) • z) := by
  funext x
  by_cases hx : x ∈ e.source
  · rw [indicator_of_mem hx, indicator_of_mem hx]
    change e.target.indicator (fun y => σ y • e.symm y) (e x) = σ (e x) • x
    rw [indicator_of_mem (e.map_source hx), e.left_inv hx]
  · rw [indicator_of_notMem hx, indicator_of_notMem hx]

theorem exists_chart_piece_approximation {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] (e : OpenPartialHomeomorph E E) (r : ℕ)
    (he : ContDiffOn ℝ r e e.source) (hesymm : ContDiffOn ℝ r e.symm e.target)
    {σ : E → ℝ} (hσ : ContDiffOn ℝ r σ e.target)
    {K : Set E} (hK : IsCompact K) (hKs : K ⊆ e.source)
    (hσK : ∀ y ∈ e.target, e.symm y ∉ K → σ y = 0)
    {ε : E → ℝ} (hε : ContinuousOn ε e.source) (hεpos : ∀ x ∈ e.source, 0 < ε x) :
    ∃ g : E → E, ContDiff ℝ ∞ g ∧
      ContDiff ℝ r (e.source.indicator (g ∘ e)) ∧
      tsupport (e.source.indicator (g ∘ e)) ⊆ e.source ∧
      ContDiff ℝ r (e.source.indicator (fun z => σ (e z) • z)) ∧
      tsupport (e.source.indicator (fun z => σ (e z) • z)) ⊆ e.source ∧
      ∀ j, j ≤ r → ∀ x ∈ e.source,
        ‖iteratedFDeriv ℝ j (e.source.indicator (g ∘ e)) x -
          iteratedFDeriv ℝ j (e.source.indicator (fun z => σ (e z) • z)) x‖ < ε x := by
  have hKe : IsCompact (e '' K) := hK.image_of_continuousOn (e.continuousOn.mono hKs)
  have hKet : e '' K ⊆ e.target := by
    rintro _ ⟨x, hx, rfl⟩
    exact e.map_source (hKs hx)
  have htsf : tsupport (e.target.indicator (fun y => σ y • e.symm y)) ⊆ e '' K :=
    closure_minimal (support_chart_piece_subset e hσK) hKe.isClosed
  have hfon : ContDiffOn ℝ r (e.target.indicator (fun y => σ y • e.symm y)) e.target :=
    (hσ.smul hesymm).congr fun y hy => indicator_of_mem hy (fun y => σ y • e.symm y)
  have hf : ContDiff ℝ r (e.target.indicator (fun y => σ y • e.symm y)) :=
    hfon.contDiff_of_tsupport_subset e.open_target (htsf.trans hKet)
  have hfc : HasCompactSupport (e.target.indicator (fun y => σ y • e.symm y)) :=
    hKe.of_isClosed_subset (isClosed_tsupport _) htsf
  obtain ⟨g, hg, _, _, hgreg, _, hgs, hgbound⟩ :=
    exists_smooth_chart_approx_with_original_pointwise_finite_jets e r he hf hfc
      (htsf.trans hKet) hε hεpos
  have hqts : tsupport (e.source.indicator (fun z => σ (e z) • z)) ⊆ K :=
    closure_minimal (support_chart_piece_comp_subset e hσK) hK.isClosed
  have hqon : ContDiffOn ℝ r (e.source.indicator (fun z => σ (e z) • z)) e.source :=
    ((hσ.comp he e.mapsTo).smul contDiffOn_id).congr fun x hx =>
      indicator_of_mem hx (fun z => σ (e z) • z)
  have hqreg : ContDiff ℝ r (e.source.indicator (fun z => σ (e z) • z)) :=
    hqon.contDiff_of_tsupport_subset e.open_source (hqts.trans hKs)
  refine ⟨g, hg, hgreg, hgs, hqreg, hqts.trans hKs, ?_⟩
  intro j hj x hx
  rw [← chart_piece_indicator_comp_eq e σ]
  exact hgbound j hj x hx

end DifferentialGeometry.Analysis
