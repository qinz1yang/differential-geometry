import DifferentialGeometry.Analysis.Integration.Measure.Riemannian.Invariance
import DifferentialGeometry.Geometry.Geodesic.Naturality.OpenSubtype
import DifferentialGeometry.Geometry.Metric.Coordinates.ChartGram
import Mathlib.MeasureTheory.Measure.Restrict
import Mathlib.Topology.Compactness.Lindelof

set_option autoImplicit false

noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions

open Bundle Manifold Set MeasureTheory TopologicalSpace
open DifferentialGeometry.Integral.Measure
open scoped Manifold ContDiff ENNReal Topology

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [T2Space M] [SigmaCompactSpace M]

private local instance openRestrictionVolumeModelMeasurable : MeasurableSpace E := borel E
private local instance openRestrictionVolumeModelBorel : BorelSpace E := ⟨rfl⟩
private local instance openRestrictionVolumeMeasurable : MeasurableSpace M := borel M
private local instance openRestrictionVolumeBorel : BorelSpace M := ⟨rfl⟩
private local instance openRestrictionVolumeSubtypeMeasurable (U : Opens M) :
    MeasurableSpace U := borel U
private local instance openRestrictionVolumeSubtypeBorel (U : Opens M) :
    BorelSpace U := ⟨rfl⟩

private theorem openRestrictionVolume_lintegral_eq_chart
    (g : SmoothRiemannianMetric I M) (a : M)
    {F : M → ℝ≥0∞} (hF : Measurable F)
    (hvanish : ∀ x, x ∉ (chartAt H a).source → F x = 0) :
    ∫⁻ x, F x ∂riemannianVolumeMeasure (I := I) (M := M) g =
      ∫⁻ x, F x ∂chartLocalMeasure (I := I) g a := by
  classical
  let rho := chartAtlasPOU I M
  let S : Set M := {b | (Function.support (rho b)).Nonempty}
  let _ : Countable S := (countable_nonempty_support_of_pou rho).to_subtype
  have hsum (x : M) : ∑' b : S, ENNReal.ofReal (rho b.val x) = 1 := by
    have hsub :
        ∑' b : M, ENNReal.ofReal (rho b x) =
          ∑' b : S, ENNReal.ofReal (rho b.val x) := by
      apply DifferentialGeometry.Integral.Measure.tsum_subtype_eq_of_support_subset
      intro b hb
      refine ⟨x, ?_⟩
      intro hzero
      exact hb (by
        change ENNReal.ofReal (rho b x) = 0
        rw [hzero, ENNReal.ofReal_zero])
    rw [← hsub, tsum_ofReal_pou_eq_one]
  change (∫⁻ x, F x ∂riemannianMeasure (I := I) g rho) = _
  rw [riemannianMeasure_lintegral_eq g rho hF,
    tsum_integral_pou_eq_subtype rho (chartLocalMeasure (I := I) g) F]
  calc
    (∑' b : S, ∫⁻ x, ENNReal.ofReal (rho b.val x) * F x
        ∂chartLocalMeasure (I := I) g b.val) =
        ∑' b : S, ∫⁻ x, ENNReal.ofReal (rho b.val x) * F x
          ∂chartLocalMeasure (I := I) g a := by
      refine tsum_congr fun b => ?_
      apply chartLocalMeasure_lintegral_eq_of_support_in_overlap g b.val a
      · exact (measurable_ofReal_pou_weight rho b.val).mul hF
      · intro x hx
        by_cases hb : x ∈ (chartAt H b.val).source
        · have ha : x ∉ (chartAt H a).source := fun ha => hx ⟨hb, ha⟩
          rw [hvanish x ha, mul_zero]
        · have hzero : rho b.val x = 0 :=
            image_eq_zero_of_notMem_tsupport
              (fun hs => hb ((chartAtlasPOU_isSubordinate I M) b.val hs))
          rw [hzero, ENNReal.ofReal_zero, zero_mul]
    _ = ∫⁻ x, ∑' b : S, ENNReal.ofReal (rho b.val x) * F x
        ∂chartLocalMeasure (I := I) g a := by
      symm
      exact lintegral_tsum fun b =>
        ((measurable_ofReal_pou_weight rho b.val).mul hF).aemeasurable
    _ = ∫⁻ x, F x ∂chartLocalMeasure (I := I) g a := by
      apply lintegral_congr
      intro x
      rw [ENNReal.tsum_mul_right, hsum x, one_mul]

theorem riemannianVolumeMeasure_restrict_chartSource
    (g : SmoothRiemannianMetric I M) (a : M) :
    (riemannianVolumeMeasure (I := I) (M := M) g).restrict (chartAt H a).source =
      (chartLocalMeasure (I := I) g a).restrict (chartAt H a).source := by
  apply Measure.ext_of_lintegral
  intro F hF
  have hs : MeasurableSet (chartAt H a).source := (chartAt H a).open_source.measurableSet
  have h := openRestrictionVolume_lintegral_eq_chart g a (hF.indicator hs)
    (fun x hx => Set.indicator_of_notMem hx F)
  simpa only [lintegral_indicator hs] using h

theorem riemannianVolumeMeasure_apply_eq_chart_of_subset_source
    (g : SmoothRiemannianMetric I M) (a : M)
    {A : Set M} (hA : A ⊆ (chartAt H a).source) :
    riemannianVolumeMeasure (I := I) (M := M) g A = chartLocalMeasure (I := I) g a A := by
  calc
    riemannianVolumeMeasure (I := I) (M := M) g A =
        (riemannianVolumeMeasure (I := I) (M := M) g).restrict (chartAt H a).source A :=
      (Measure.restrict_eq_self _ hA).symm
    _ = (chartLocalMeasure (I := I) g a).restrict (chartAt H a).source A :=
      congrArg (fun mu : Measure M => mu A)
        (riemannianVolumeMeasure_restrict_chartSource g a)
    _ = chartLocalMeasure (I := I) g a A := Measure.restrict_eq_self _ hA

omit [FiniteDimensional ℝ E] [IsManifold I ∞ M] [T2Space M] [SigmaCompactSpace M] in
private theorem openRestrictionVolume_chart_source
    (U : Opens M) (a x : U) :
    x ∈ (chartAt H a).source ↔ (x : M) ∈ (chartAt H (a : M)).source := by
  let _ : Nonempty U := ⟨a⟩
  rw [TopologicalSpace.Opens.chartAt_eq, OpenPartialHomeomorph.subtypeRestr_source]
  rfl

omit [FiniteDimensional ℝ E] [IsManifold I ∞ M] [T2Space M] [SigmaCompactSpace M] in
private theorem openRestrictionVolume_inverse_chart
    (U : Opens M) (a : U) {y : E} (hy : y ∈ (extChartAt I a).target) :
    (((extChartAt I a).symm y : U) : M) = (extChartAt I (a : M)).symm y := by
  have hxU : (extChartAt I a).symm y ∈ (chartAt H a).source := by
    rw [← extChartAt_source (I := I) a]
    exact (extChartAt I a).map_target hy
  have hxM : (((extChartAt I a).symm y : U) : M) ∈
      (extChartAt I (a : M)).source := by
    rw [extChartAt_source]
    exact (openRestrictionVolume_chart_source U a _).mp hxU
  have hforward :
      (extChartAt I (a : M)) (((extChartAt I a).symm y : U) : M) = y :=
    (extChartAt I a).right_inv hy
  calc
    (((extChartAt I a).symm y : U) : M) =
        (extChartAt I (a : M)).symm
          ((extChartAt I (a : M)) (((extChartAt I a).symm y : U) : M)) :=
      ((extChartAt I (a : M)).left_inv hxM).symm
    _ = (extChartAt I (a : M)).symm y := congrArg _ hforward

omit [FiniteDimensional ℝ E] [IsManifold I ∞ M] [T2Space M] [SigmaCompactSpace M] in
private theorem openRestrictionVolume_chart_target_subset
    (U : Opens M) (a : U) :
    (extChartAt I a).target ⊆ (extChartAt I (a : M)).target := by
  intro y hy
  have hxU : (extChartAt I a).symm y ∈ (chartAt H a).source := by
    rw [← extChartAt_source (I := I) a]
    exact (extChartAt I a).map_target hy
  have hxM : (((extChartAt I a).symm y : U) : M) ∈
      (extChartAt I (a : M)).source := by
    rw [extChartAt_source]
    exact (openRestrictionVolume_chart_source U a _).mp hxU
  have hforward :
      (extChartAt I (a : M)) (((extChartAt I a).symm y : U) : M) = y :=
    (extChartAt I a).right_inv hy
  rw [← hforward]
  exact (extChartAt I (a : M)).map_source hxM

omit [SigmaCompactSpace M] in
private theorem openRestrictionVolume_chart_density
    (g : SmoothRiemannianMetric I M) (U : Opens M) (a x : U)
    (hx : x ∈ (chartAt H a).source) :
    chartDensity (I := I) (g.restrictOpen U) a x =
      chartDensity (I := I) g (a : M) (x : M) := by
  have hGram :
      DifferentialGeometry.Tensor.Coordinates.chartGramMatrix
          (I := I) (g.restrictOpen U) a x =
        DifferentialGeometry.Tensor.Coordinates.chartGramMatrix
          (I := I) g (a : M) (x : M) := by
    ext i j
    exact Geometry.Riemannian.Geodesic.chartGram_open g U a x
      ((openRestrictionVolume_chart_source U a x).mp hx) i j
  unfold chartDensity
  rw [hGram]

omit [SigmaCompactSpace M] in
private theorem openRestrictionVolume_chart_apply
    (g : SmoothRiemannianMetric I M) (U : Opens M) (a : U)
    {A : Set U} (hA : MeasurableSet A) (hsource : A ⊆ (chartAt H a).source) :
    chartLocalMeasure (I := I) (g.restrictOpen U) a A =
      chartLocalMeasure (I := I) g (a : M) ((Subtype.val : U → M) '' A) := by
  classical
  have hval : MeasurableEmbedding (Subtype.val : U → M) :=
    U.isOpenEmbedding'.measurableEmbedding
  have himage : MeasurableSet ((Subtype.val : U → M) '' A) :=
    hval.measurableSet_image' hA
  have hleft : chartLocalMeasure (I := I) (g.restrictOpen U) a A =
      ∫⁻ y in (extChartAt I a).target,
        ENNReal.ofReal (chartDensity (I := I) (g.restrictOpen U) a
          ((extChartAt I a).symm y)) *
          A.indicator (1 : U → ℝ≥0∞) ((extChartAt I a).symm y)
        ∂modelHaar (E := E) := by
    rw [← lintegral_indicator_one hA]
    exact chartLocalMeasure_lintegral (g.restrictOpen U) a (measurable_const.indicator hA)
  have hright :
      chartLocalMeasure (I := I) g (a : M) ((Subtype.val : U → M) '' A) =
      ∫⁻ y in (extChartAt I (a : M)).target,
        ENNReal.ofReal (chartDensity (I := I) g (a : M)
          ((extChartAt I (a : M)).symm y)) *
          ((Subtype.val : U → M) '' A).indicator (1 : M → ℝ≥0∞)
            ((extChartAt I (a : M)).symm y)
        ∂modelHaar (E := E) := by
    rw [← lintegral_indicator_one himage]
    exact chartLocalMeasure_lintegral g (a : M) (measurable_const.indicator himage)
  rw [hleft, hright]
  have hTU : MeasurableSet (extChartAt I a).target :=
    measurableSet_extChartAt_target a
  have hTM : MeasurableSet (extChartAt I (a : M)).target :=
    measurableSet_extChartAt_target (a : M)
  have hsub := openRestrictionVolume_chart_target_subset (I := I) U a
  have hextend (f : E → ℝ≥0∞) :
      ∫⁻ y in (extChartAt I a).target, f y ∂modelHaar (E := E) =
        ∫⁻ y in (extChartAt I (a : M)).target,
          (extChartAt I a).target.indicator f y ∂modelHaar (E := E) := by
    rw [setLIntegral_indicator hTU, Set.inter_eq_left.mpr hsub]
  rw [hextend]
  apply setLIntegral_congr_fun hTM
  intro y hy
  dsimp only
  by_cases hyU : y ∈ (extChartAt I a).target
  · rw [Set.indicator_of_mem hyU]
    have hxU : (extChartAt I a).symm y ∈ (chartAt H a).source := by
      rw [← extChartAt_source (I := I) a]
      exact (extChartAt I a).map_target hyU
    have hsymm := openRestrictionVolume_inverse_chart (I := I) U a hyU
    rw [openRestrictionVolume_chart_density g U a _ hxU, ← hsymm]
    have hmem : (((extChartAt I a).symm y : U) : M) ∈
        (Subtype.val : U → M) '' A ↔ (extChartAt I a).symm y ∈ A := by
      constructor
      · rintro ⟨z, hz, hzx⟩
        exact (Subtype.val_injective hzx) ▸ hz
      · intro hx
        exact ⟨_, hx, rfl⟩
    by_cases hx : (extChartAt I a).symm y ∈ A
    · rw [Set.indicator_of_mem hx, Set.indicator_of_mem (hmem.mpr hx)]
      rfl
    · rw [Set.indicator_of_notMem hx, Set.indicator_of_notMem (mt hmem.mp hx)]
  · rw [Set.indicator_of_notMem hyU]
    have hnot : (extChartAt I (a : M)).symm y ∉ (Subtype.val : U → M) '' A := by
      rintro ⟨x, hx, hxy⟩
      have hxsource : x ∈ (extChartAt I a).source := by
        rw [extChartAt_source]
        exact hsource hx
      have hforward : (extChartAt I a) x = y := by
        change (extChartAt I (a : M)) (x : M) = y
        rw [hxy]
        exact (extChartAt I (a : M)).right_inv hy
      exact hyU (hforward ▸ (extChartAt I a).map_source hxsource)
    rw [Set.indicator_of_notMem hnot, mul_zero]

theorem riemannianVolumeMeasure_restrictOpen_eq_comap
    (g : SmoothRiemannianMetric I M) (U : Opens M) [SigmaCompactSpace U] :
    riemannianVolumeMeasure (I := I) (M := U) (g.restrictOpen U) =
      Measure.comap (Subtype.val : U → M) (riemannianVolumeMeasure (I := I) (M := M) g) := by
  have hval : MeasurableEmbedding (Subtype.val : U → M) :=
    U.isOpenEmbedding'.measurableEmbedding
  obtain ⟨S, hScount, hScover⟩ :=
    isLindelof_univ.elim_countable_subcover (fun a : U => (chartAt H a).source)
      (fun a => (chartAt H a).open_source) (by rw [iUnion_source_chartAt])
  apply Measure.ext_of_biUnion_eq_univ hScount (Set.eq_univ_of_univ_subset hScover)
  intro a _ha
  ext A hA
  rw [Measure.restrict_apply hA, Measure.restrict_apply hA, hval.comap_apply]
  have hB : MeasurableSet (A ∩ (chartAt H a).source) :=
    hA.inter (chartAt H a).open_source.measurableSet
  have hsource : A ∩ (chartAt H a).source ⊆ (chartAt H a).source := inter_subset_right
  have hsourceM : (Subtype.val : U → M) '' (A ∩ (chartAt H a).source) ⊆
      (chartAt H (a : M)).source := by
    rintro _ ⟨x, hx, rfl⟩
    exact (openRestrictionVolume_chart_source U a x).mp hx.2
  calc
    riemannianVolumeMeasure (I := I) (M := U) (g.restrictOpen U) (A ∩ (chartAt H a).source) =
        chartLocalMeasure (I := I) (g.restrictOpen U) a (A ∩ (chartAt H a).source) :=
      riemannianVolumeMeasure_apply_eq_chart_of_subset_source (g.restrictOpen U) a hsource
    _ = chartLocalMeasure (I := I) g (a : M)
        ((Subtype.val : U → M) '' (A ∩ (chartAt H a).source)) :=
      openRestrictionVolume_chart_apply g U a hB hsource
    _ = riemannianVolumeMeasure (I := I) (M := M) g
        ((Subtype.val : U → M) '' (A ∩ (chartAt H a).source)) :=
      (riemannianVolumeMeasure_apply_eq_chart_of_subset_source g (a : M) hsourceM).symm

theorem riemannianVolumeMeasure_restrictOpen_apply
    (g : SmoothRiemannianMetric I M) (U : Opens M) [SigmaCompactSpace U]
    (A : Set U) :
    riemannianVolumeMeasure (I := I) (M := U) (g.restrictOpen U) A =
      riemannianVolumeMeasure (I := I) (M := M) g ((Subtype.val : U → M) '' A) := by
  rw [riemannianVolumeMeasure_restrictOpen_eq_comap]
  exact U.isOpenEmbedding'.measurableEmbedding.comap_apply _ A

theorem map_riemannianVolumeMeasure_restrictOpen
    (g : SmoothRiemannianMetric I M) (U : Opens M) [SigmaCompactSpace U] :
    Measure.map (Subtype.val : U → M)
        (riemannianVolumeMeasure (I := I) (M := U) (g.restrictOpen U)) =
      (riemannianVolumeMeasure (I := I) (M := M) g).restrict (U : Set M) := by
  rw [riemannianVolumeMeasure_restrictOpen_eq_comap,
    U.isOpenEmbedding'.measurableEmbedding.map_comap, Subtype.range_coe]

end DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions

end
