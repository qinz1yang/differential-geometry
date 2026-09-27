import DifferentialGeometry.Analysis.Sobolev.Intrinsic.WeakChartTest

set_option autoImplicit false

noncomputable section

open Bundle Manifold Set MeasureTheory Filter
open scoped Manifold Topology ContDiff ENNReal

namespace DifferentialGeometry.Analysis.Sobolev.IntrinsicLp

open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Integral.DivergenceTheorem

private lemma memLp_of_withDensity_lower_bound
    {A : Type*} [MeasurableSpace A] {μ : Measure A} {w : A → ℝ≥0∞}
    {s : Set A} (hs : MeasurableSet s) {c : ℝ≥0∞} (hc : c ≠ 0) (hct : c ≠ ⊤)
    (hbound : ∀ x ∈ s, c ≤ w x) {f : A → ℝ} {p : ℝ≥0∞}
    (hf : MemLp f p (μ.withDensity w))
    (hzero : ∀ᵐ x ∂μ, x ∉ s → f x = 0) : MemLp f p μ := by
  have hmeasure : μ.restrict s ≤ c⁻¹ • μ.withDensity w := by
    rw [← withDensity_indicator_one hs, ← withDensity_smul' c⁻¹ w (by simpa using hc)]
    apply withDensity_mono
    filter_upwards [] with x
    by_cases hx : x ∈ s
    · simp only [Set.indicator_of_mem hx, Pi.one_apply, Pi.smul_apply, smul_eq_mul]
      calc
        1 = c⁻¹ * c := (ENNReal.inv_mul_cancel hc hct).symm
        _ ≤ c⁻¹ * w x := mul_le_mul le_rfl (hbound x hx) zero_le zero_le
    · simp only [Set.indicator_of_notMem hx, Pi.smul_apply, smul_eq_mul]
      exact zero_le
  have hlocal : MemLp f p (μ.restrict s) := hf.of_measure_le_smul (by simpa using hc) hmeasure
  apply ((memLp_indicator_iff_restrict hs).2 hlocal).ae_eq
  filter_upwards [hzero] with x hx
  by_cases hxs : x ∈ s
  · exact Set.indicator_of_mem hxs f
  · rw [Set.indicator_of_notMem hxs, hx hxs]

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [Module.Finite ℝ E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

private local instance : MeasurableSpace E := borel E
private local instance : BorelSpace E := ⟨rfl⟩
private local instance : MeasurableSpace M := borel M
private local instance : BorelSpace M := ⟨rfl⟩


theorem memLp_scalarOnE_of_support [CompactSpace M] [T2Space M]
    (g : SmoothRiemannianMetric I M) (α : M) {f : M → ℝ} {p : ℝ≥0∞}
    (hf : MemLp f p (riemannianVolumeMeasure I M g))
    (hsupp : tsupport f ⊆ (chartAt H α).source) :
    MemLp (scalarOnE (I := I) α f) p
      ((modelHaar (E := E)).restrict (extChartAt I α).target) := by
  classical
  have hzero : ∀ x, x ∉ (chartAt H α).source → f x = 0 := by
    intro x hx
    exact image_eq_zero_of_notMem_tsupport (fun h => hx (hsupp h))
  have hchart : MemLp f p (chartLocalMeasure g α) := by
    have hlocal : MemLp f p ((chartLocalMeasure g α).restrict (chartAt H α).source) := by
      rw [← Chart.volume_restrict_eq g α]
      exact hf.restrict _
    apply ((memLp_indicator_iff_restrict (chartAt H α).open_source.measurableSet).2 hlocal).ae_eq
    filter_upwards [] with x
    by_cases hx : x ∈ (chartAt H α).source
    · exact Set.indicator_of_mem hx f
    · rw [Set.indicator_of_notMem hx, hzero x hx]
  let ν := (modelHaar (E := E)).restrict (extChartAt I α).target
  let w : E → ℝ≥0∞ := fun y => ENNReal.ofReal (chartDensity g α ((extChartAt I α).symm y))
  have hweighted : MemLp (scalarOnE (I := I) α f) p (ν.withDensity w) := by
    exact hchart.comp_of_map
      ((aemeasurable_extChartAt_symm_restrict_target (I := I) (E := E) α).mono_ac
        (withDensity_absolutelyContinuous ν w))
  let K := (extChartAt I α) '' tsupport f
  obtain ⟨hK, hKT⟩ := Chart.image_extChartAt_tsupport_compact_subset_target (I := I) hsupp
  have hzeroK : ∀ᵐ y ∂ν, y ∉ K → scalarOnE (I := I) α f y = 0 := by
    filter_upwards [ae_restrict_mem (measurableSet_extChartAt_target (I := I) α)] with y hy
    intro hyK
    change f ((extChartAt I α).symm y) = 0
    apply image_eq_zero_of_notMem_tsupport
    intro hfK
    apply hyK
    exact ⟨(extChartAt I α).symm y, hfK, (extChartAt I α).right_inv hy⟩
  by_cases hKne : K.Nonempty
  · obtain ⟨c, hc, hbound⟩ := Chart.exists_inf_chartDensity_on_compact g α hK hKne hKT
    exact memLp_of_withDensity_lower_bound hK.measurableSet
      (ENNReal.ofReal_ne_zero_iff.mpr hc) ENNReal.ofReal_ne_top
      (fun y hy => ENNReal.ofReal_le_ofReal (hbound y hy)) hweighted hzeroK
  · have hKe : K = ∅ := Set.not_nonempty_iff_eq_empty.mp hKne
    apply (MemLp.zero).ae_eq
    filter_upwards [hzeroK] with y hy
    exact (hy (by simp only [hKe, Set.mem_empty_iff_false, not_false_eq_true])).symm


theorem memLp_chartPushedRaw_of_support [CompactSpace M] [T2Space M]
    (g : SmoothRiemannianMetric I M) (α : M) {f : M → ℝ} {p : ℝ≥0∞}
    (hf : MemLp f p (riemannianVolumeMeasure I M g))
    (hsupp : tsupport f ⊆ (chartAt H α).source) :
    MemLp (Chart.chartPushedRaw I α f) p
      (volume.restrict (Chart.chartTargetEuclid (I := I) α)) := by
  have hmeas : MeasurableEmbedding (toEuclidean (E := E)) :=
    (toEuclidean (E := E)).toHomeomorph.toMeasurableEquiv.measurableEmbedding
  have hpres : MeasurePreserving (toEuclidean (E := E)) (modelHaar (E := E)) volume :=
    ⟨hmeas.measurable, map_toEuclidean_modelHaar_eq_volume⟩
  unfold Chart.chartTargetEuclid
  rw [← (hpres.restrict_image_emb hmeas (extChartAt I α).target).map_eq,
    hmeas.memLp_map_measure_iff]
  apply (memLp_scalarOnE_of_support g α hf hsupp).ae_eq
  filter_upwards [ae_restrict_mem (measurableSet_extChartAt_target (I := I) α)] with y hy
  have hyE : toEuclidean y ∈ Chart.chartTargetEuclid (I := I) α := ⟨y, hy, rfl⟩
  dsimp only [Function.comp_apply]
  rw [Chart.chartPushedRaw_apply_of_mem α f hyE, ContinuousLinearEquiv.symm_apply_apply]
  rfl

end DifferentialGeometry.Analysis.Sobolev.IntrinsicLp
