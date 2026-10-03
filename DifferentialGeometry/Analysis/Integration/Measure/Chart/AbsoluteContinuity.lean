import DifferentialGeometry.Analysis.Integration.Measure.Riemannian.Invariance

set_option autoImplicit false
noncomputable section
open Bundle Manifold Set MeasureTheory Filter
open scoped Manifold Topology ContDiff ENNReal
namespace DifferentialGeometry.Geometry.Measure
open DifferentialGeometry DifferentialGeometry.Integral.Measure

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

private local instance : MeasurableSpace E := borel E
private local instance : BorelSpace E := ⟨rfl⟩
private local instance : MeasurableSpace M := borel M
private local instance : BorelSpace M := ⟨rfl⟩

private theorem ae_chartLocalMeasure_mem_source
    (g : SmoothRiemannianMetric I M) (α : M) :
    ∀ᵐ x ∂chartLocalMeasure g α, x ∈ (chartAt H α).source := by
  have hnull := chartLocalMeasure_apply_of_disjoint_source g α
    (chartAt H α).open_source.measurableSet.compl
    (show Disjoint ((chartAt H α).source)ᶜ (chartAt H α).source from disjoint_compl_left)
  simpa only [mem_compl_iff, not_not] using measure_eq_zero_iff_ae_notMem.mp hnull

theorem chartLocalMeasure_absolutelyContinuous_riemannianVolumeMeasure
    [T2Space M] [SigmaCompactSpace M] (g : SmoothRiemannianMetric I M) (α : M) :
    chartLocalMeasure g α ≪ riemannianVolumeMeasure I M g := by
  intro N hN
  rw [measure_eq_zero_iff_ae_notMem]
  let ρ := chartAtlasPOU I M
  let S : Set M := {β : M | (Function.support (ρ β)).Nonempty}
  have : Countable S := (countable_nonempty_support_of_pou ρ).to_subtype
  have hglobal : ∀ᵐ x ∂riemannianVolumeMeasure I M g, x ∉ N :=
    measure_eq_zero_iff_ae_notMem.mp hN
  have hweighted (β : M) : ∀ᵐ x ∂chartLocalMeasure g β,
      ENNReal.ofReal (ρ β x) ≠ 0 → x ∉ N := by
    apply (ae_withDensity_iff (measurable_ofReal_pou_weight ρ β)).mp
    exact (Measure.absolutelyContinuous_of_le
      (chartLocalMeasure_withDensity_le_riemannianMeasure g ρ β)).ae_le hglobal
  have hlocal (β : S) : ∀ᵐ x ∂chartLocalMeasure g α,
      x ∈ (chartAt H α).source ∩ (chartAt H (β : M)).source →
        ENNReal.ofReal (ρ β x) ≠ 0 → x ∉ N := by
    apply (ae_restrict_iff' (measurableSet_chartAt_source_inter α (β : M))).mp
    rw [chartLocalMeasure_restrict_overlap_eq g α (β : M)]
    exact ae_restrict_of_ae (hweighted β)
  filter_upwards [ae_all_iff.mpr hlocal, ae_chartLocalMeasure_mem_source g α] with x hx hxs
  obtain ⟨β, hβ⟩ := ρ.exists_pos_of_mem (mem_univ x)
  have hβsrc : x ∈ (chartAt H β).source :=
    chartAtlasPOU_isSubordinate I M β (subset_tsupport (ρ β) (ne_of_gt hβ))
  exact hx ⟨β, ⟨x, ne_of_gt hβ⟩⟩ ⟨hxs, hβsrc⟩
    (ne_of_gt (ENNReal.ofReal_pos.mpr hβ))

theorem ae_extChartAt_symm_of_riemannianVolumeMeasure
    [T2Space M] [SigmaCompactSpace M] (g : SmoothRiemannianMetric I M) (α : M)
    {P : M → Prop} (hP : ∀ᵐ x ∂riemannianVolumeMeasure I M g, P x) :
    ∀ᵐ y ∂(modelHaar (E := E)).restrict (extChartAt I α).target,
      P ((extChartAt I α).symm y) := by
  have hlocal : ∀ᵐ x ∂chartLocalMeasure g α, P x :=
    (chartLocalMeasure_absolutelyContinuous_riemannianVolumeMeasure g α).ae_le hP
  have hdensity := aemeasurable_chartDensity_symm_pullback g α
  have hsymm := (aemeasurable_extChartAt_symm_restrict_target (I := I) α).mono_ac
    (withDensity_absolutelyContinuous _
      (fun y : E => ENNReal.ofReal (chartDensity g α ((extChartAt I α).symm y))))
  have hpull := Measure.tendsto_ae_map hsymm hlocal
  have hcancel := (ae_withDensity_iff' hdensity).mp hpull
  filter_upwards [hcancel, ae_restrict_mem (measurableSet_extChartAt_target (I := I) α)] with y hy hyt
  apply hy
  exact ne_of_gt (ENNReal.ofReal_pos.mpr
    (chartDensity_pos g α (by
      simpa only [trivializationAt_baseSet_eq_chartAt_source,
        extChartAt_source_eq_chartAt_source] using (extChartAt I α).map_target hyt)))

theorem riemannianVolumeMeasure_eq_zero_of_chart_preimages
    [T2Space M] [SigmaCompactSpace M] (g : SmoothRiemannianMetric I M)
    {S : Set M} (hS : MeasurableSet S)
    (hchart : ∀ α : M, modelHaar (E := E)
      ((extChartAt I α).symm ⁻¹' S ∩ (extChartAt I α).target) = 0) :
    riemannianVolumeMeasure I M g S = 0 := by
  have hlocal (α : M) : chartLocalMeasure g α S = 0 := by
    unfold chartLocalMeasure
    have hac := withDensity_absolutelyContinuous
      ((modelHaar (E := E)).restrict (extChartAt I α).target)
      (fun y : E => ENNReal.ofReal (chartDensity g α ((extChartAt I α).symm y)))
    have hsymm := (aemeasurable_extChartAt_symm_restrict_target (I := I) α).mono_ac hac
    rw [Measure.map_apply_of_aemeasurable hsymm hS]
    apply hac
    rw [Measure.restrict_apply' (measurableSet_extChartAt_target (I := I) α)]
    exact hchart α
  rw [riemannianVolumeMeasure_def, riemannianMeasure_def,
    Measure.sum_apply_eq_zero' hS]
  intro α
  exact (withDensity_absolutelyContinuous (chartLocalMeasure g α)
    (fun x : M => ENNReal.ofReal (chartAtlasPOU I M α x))) (hlocal α)

end DifferentialGeometry.Geometry.Measure
