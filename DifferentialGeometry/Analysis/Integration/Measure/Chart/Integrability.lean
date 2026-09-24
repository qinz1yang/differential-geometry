import DifferentialGeometry.Analysis.Integration.Measure.ChartIntegral
import Mathlib.Topology.PartialHomeomorph.Basic
import Mathlib.MeasureTheory.Function.L1Space.Integrable

noncomputable section

open Bundle Filter Manifold MeasureTheory Set
open scoped ContDiff Manifold ENNReal

namespace DifferentialGeometry.Integral.Measure

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

private local instance : MeasurableSpace E := borel E
private local instance : BorelSpace E := ⟨rfl⟩
private local instance : MeasurableSpace M := borel M
private local instance : BorelSpace M := ⟨rfl⟩

omit [FiniteDimensional ℝ E] [IsManifold I ∞ M] in
private theorem integrable_map_extChartAt_symm_iff
    {F : Type*} [NormedAddCommGroup F]
    (alpha : M) (μ : MeasureTheory.Measure E)
    (hμ : ∀ᵐ y ∂μ, y ∈ (extChartAt I alpha).target) {f : M → F} :
    Integrable f (MeasureTheory.Measure.map (extChartAt I alpha).symm μ) ↔
      Integrable (fun y => f ((extChartAt I alpha).symm y)) μ := by
  let T : Set E := (extChartAt I alpha).target
  have hT : MeasurableSet T := measurableSet_extChartAt_target (I := I) alpha
  let p : PartialHomeomorph M E :=
    { toPartialEquiv := extChartAt I alpha
      continuousOn_toFun := continuousOn_extChartAt alpha
      continuousOn_invFun := continuousOn_extChartAt_symm alpha }
  let s : T → M := fun y => (extChartAt I alpha).symm y
  have hs : MeasurableEmbedding s := by
    apply p.symm.isEmbedding_restrict.measurableEmbedding
    have hrange : Set.range s = (extChartAt I alpha).source := by
      ext x
      constructor
      · rintro ⟨y, rfl⟩
        exact (extChartAt I alpha).map_target y.property
      · intro hx
        exact ⟨⟨extChartAt I alpha x, (extChartAt I alpha).map_source hx⟩,
          (extChartAt I alpha).left_inv hx⟩
    change MeasurableSet (Set.range s)
    rw [hrange, extChartAt_source]
    exact (chartAt H alpha).open_source.measurableSet
  let η : MeasureTheory.Measure T := MeasureTheory.Measure.comap Subtype.val μ
  have hmap : MeasureTheory.Measure.map (Subtype.val : T → E) η = μ := by
    rw [map_comap_subtype_coe hT]
    exact MeasureTheory.Measure.restrict_eq_self_of_ae_mem hμ
  have hsymm : AEMeasurable (extChartAt I alpha).symm μ := by
    have ht : AEMeasurable (extChartAt I alpha).symm (μ.restrict T) :=
      (continuousOn_extChartAt_symm alpha).aemeasurable hT
    rwa [MeasureTheory.Measure.restrict_eq_self_of_ae_mem hμ] at ht
  have hsymmMap : AEMeasurable (extChartAt I alpha).symm
      (MeasureTheory.Measure.map (Subtype.val : T → E) η) := by
    simpa only [hmap] using hsymm
  have hsmap : MeasureTheory.Measure.map s η =
      MeasureTheory.Measure.map (extChartAt I alpha).symm μ := by
    calc
      _ = (MeasureTheory.Measure.map (Subtype.val : T → E) η).map
          (extChartAt I alpha).symm :=
        (AEMeasurable.map_map_of_aemeasurable hsymmMap
          measurable_subtype_coe.aemeasurable).symm
      _ = _ := by rw [hmap]
  calc
    Integrable f (MeasureTheory.Measure.map (extChartAt I alpha).symm μ) ↔
        Integrable (fun y : T => f (s y)) η := by
      rw [← hsmap]
      exact hs.integrable_map_iff
    _ ↔ Integrable (fun y => f ((extChartAt I alpha).symm y)) μ := by
      rw [← hmap]
      exact ((MeasurableEmbedding.subtype_coe hT).integrable_map_iff
        (μ := η) (g := fun y => f ((extChartAt I alpha).symm y))).symm

theorem integrable_chartLocalMeasure_iff
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (g : SmoothRiemannianMetric I M) (alpha : M) {f : M → F} :
    Integrable f (chartLocalMeasure g alpha) ↔
      Integrable (fun y => chartDensity g alpha ((extChartAt I alpha).symm y) •
        f ((extChartAt I alpha).symm y))
        ((modelHaar (E := E)).restrict (extChartAt I alpha).target) := by
  let μ : MeasureTheory.Measure E :=
    (modelHaar (E := E)).restrict (extChartAt I alpha).target
  let d : E → ℝ≥0∞ := fun y =>
    ENNReal.ofReal (chartDensity g alpha ((extChartAt I alpha).symm y))
  have hd : AEMeasurable d μ := aemeasurable_chartDensity_symm_pullback g alpha
  have hdfinite : ∀ᵐ y ∂μ, d y < ⊤ :=
    Eventually.of_forall fun _ => ENNReal.ofReal_lt_top
  have htarget : ∀ᵐ y ∂μ.withDensity d, y ∈ (extChartAt I alpha).target :=
    (withDensity_absolutelyContinuous μ d).ae_le
      (ae_restrict_mem (measurableSet_extChartAt_target (I := I) alpha))
  change Integrable f (MeasureTheory.Measure.map (extChartAt I alpha).symm
    (μ.withDensity d)) ↔ _
  rw [integrable_map_extChartAt_symm_iff alpha _ htarget]
  rw [integrable_withDensity_iff_integrable_smul₀' hd hdfinite]
  apply integrable_congr
  filter_upwards [ae_restrict_mem (measurableSet_extChartAt_target (I := I) alpha)] with y hy
  have hpos : 0 < chartDensity g alpha ((extChartAt I alpha).symm y) :=
    chartDensity_pos g alpha
      (DifferentialGeometry.Tensor.Coordinates.extChartAt_symm_mem_trivializationAt_baseSet
        (I := I) alpha hy)
  dsimp only [d]
  rw [ENNReal.toReal_ofReal hpos.le]

theorem integrable_riemannianVolumeMeasure_iff_chartLocalMeasure_of_tsupport_subset
    {F : Type*} [NormedAddCommGroup F]
    [T2Space M] [SigmaCompactSpace M]
    (g : SmoothRiemannianMetric I M) (alpha : M)
    {f : M → F} (hf : HasCompactSupport f)
    (hs : tsupport f ⊆ (extChartAt I alpha).source) :
    Integrable f (riemannianVolumeMeasure (I := I) (M := M) g) ↔
      Integrable f (chartLocalMeasure g alpha) := by
  have hs' : tsupport f ⊆ (chartAt H alpha).source := by
    simpa only [extChartAt_source] using hs
  calc
    Integrable f (riemannianVolumeMeasure (I := I) (M := M) g) ↔
        IntegrableOn f (tsupport f) (riemannianVolumeMeasure (I := I) (M := M) g) :=
      (integrableOn_iff_integrable_of_support_subset (subset_tsupport f)).symm
    _ ↔ IntegrableOn f (tsupport f) (chartLocalMeasure g alpha) := by
      rw [IntegrableOn,
        riemannianVolumeMeasure_restrict_eq_chartLocalMeasure_restrict g alpha hf hs']
      rfl
    _ ↔ Integrable f (chartLocalMeasure g alpha) :=
      integrableOn_iff_integrable_of_support_subset (subset_tsupport f)

theorem integrable_riemannianVolumeMeasure_iff_chartDensity_of_tsupport_subset
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    [T2Space M] [SigmaCompactSpace M]
    (g : SmoothRiemannianMetric I M) (alpha : M)
    {f : M → F} (hf : HasCompactSupport f)
    (hs : tsupport f ⊆ (extChartAt I alpha).source) :
    Integrable f (riemannianVolumeMeasure (I := I) (M := M) g) ↔
      Integrable (fun y => chartDensity g alpha ((extChartAt I alpha).symm y) •
        f ((extChartAt I alpha).symm y))
        ((modelHaar (E := E)).restrict (extChartAt I alpha).target) :=
  (integrable_riemannianVolumeMeasure_iff_chartLocalMeasure_of_tsupport_subset
    g alpha hf hs).trans (integrable_chartLocalMeasure_iff g alpha)

end DifferentialGeometry.Integral.Measure
