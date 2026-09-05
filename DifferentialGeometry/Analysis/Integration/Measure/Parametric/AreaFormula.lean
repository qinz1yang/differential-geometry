import DifferentialGeometry.Analysis.Integration.Measure.Jacobian.ImageIntegralBound
import DifferentialGeometry.Analysis.Integration.Measure.Parametric.Density
import DifferentialGeometry.Analysis.Integration.Measure.Riemannian.Invariance

noncomputable section

open Set Filter Manifold MeasureTheory
open scoped Topology Manifold ContDiff ENNReal

namespace DifferentialGeometry.Integral.Measure

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [Module.Finite ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [T2Space M] [SigmaCompactSpace M]

private local instance : MeasurableSpace E := borel E
private local instance : BorelSpace E := ⟨rfl⟩
private local instance : MeasurableSpace M := borel M
private local instance : BorelSpace M := ⟨rfl⟩

omit [Module.Finite ℝ E] [T2Space M] [SigmaCompactSpace M] in
private lemma contDiffOn_extChartAt_comp
    {f : E → M} {U s : Set E} (hf : ContMDiffOn 𝓘(ℝ, E) I 1 f U)
    (hsU : s ⊆ U) (y₀ : M) (hs_chart : ∀ x ∈ s, f x ∈ (chartAt H y₀).source) :
    ContDiffOn ℝ 1 (fun x : E => extChartAt I y₀ (f x)) s := by
  exact contMDiffOn_iff_contDiffOn.mp
    ((contMDiffOn_extChartAt (I := I) (x := y₀) (n := 1)).comp (hf.mono hsU) hs_chart)

private lemma pou_term_map_le
    (g : SmoothRiemannianMetric I M) {f : E → M} {U K : Set E}
    (hU : IsOpen U) (hK : MeasurableSet K) (hKU : K ⊆ U)
    (hf : ContMDiffOn (modelWithCornersSelf ℝ E) I 1 f U)
    (himg : MeasurableSet (f '' K)) (a : M) :
    ((chartLocalMeasure (I := I) g a).withDensity
        (fun y : M => ENNReal.ofReal (chartAtlasPOU I M a y))) (f '' K) ≤
      ∫⁻ x in K, ENNReal.ofReal (chartAtlasPOU I M a (f x)) *
        ENNReal.ofReal (paramDensity (I := I) g f x) ∂(modelHaar (E := E)) := by
  classical
  let S : Set M := (chartAt H a).source
  let V : Set E := U ∩ f ⁻¹' S
  let Ka : Set E := K ∩ V
  have hVopen : IsOpen V := by
    dsimp only [V, S]
    exact hf.continuousOn.isOpen_inter_preimage hU (chartAt H a).open_source
  have hVU : V ⊆ U := by
    dsimp only [V]
    exact inter_subset_left
  have hVchart : ∀ x ∈ V, f x ∈ (chartAt H a).source := by
    intro x hx
    exact hx.2
  have hKa : MeasurableSet Ka := hK.inter hVopen.measurableSet
  let fa : E → E := V.piecewise (fun x => extChartAt I a (f x)) 0
  let fa' : E → (E →L[ℝ] E) :=
    fun x => fderiv ℝ (fun z => extChartAt I a (f z)) x
  let Wa : E → ℝ≥0∞ := (extChartAt I a).target.piecewise
    (fun q => ENNReal.ofReal (chartDensity g a ((extChartAt I a).symm q) *
      chartAtlasPOU I M a ((extChartAt I a).symm q))) 0
  have hfa : ∀ x ∈ V, fa x = extChartAt I a (f x) := by
    intro x hx
    dsimp only [fa]
    exact Set.piecewise_eq_of_mem _ _ _ hx
  have hWa : ∀ q ∈ (extChartAt I a).target,
      Wa q = ENNReal.ofReal (chartDensity g a ((extChartAt I a).symm q) *
        chartAtlasPOU I M a ((extChartAt I a).symm q)) := by
    intro q hq
    dsimp only [Wa]
    exact Set.piecewise_eq_of_mem _ _ _ hq
  have hcoord : ContDiffOn ℝ 1 (fun x : E => extChartAt I a (f x)) V :=
    contDiffOn_extChartAt_comp (I := I) hf hVU a hVchart
  have hfa_meas : Measurable fa := by
    refine ContinuousOn.measurable_piecewise ?_ continuous_const.continuousOn
      hVopen.measurableSet
    exact (continuousOn_extChartAt (I := I) a).comp
      ((hf.mono hVU).continuousOn) (fun x hx => by
        rw [extChartAt_source]
        exact hVchart x hx)
  have htarget_meas : MeasurableSet (extChartAt I a).target :=
    measurableSet_extChartAt_target (I := I) a
  have hsymm : ContinuousOn (extChartAt I a).symm (extChartAt I a).target :=
    continuousOn_extChartAt_symm (I := I) a
  have hsymm_maps : MapsTo (extChartAt I a).symm (extChartAt I a).target S := by
    intro q hq
    dsimp only [S]
    rw [← extChartAt_source (I := I)]
    exact (extChartAt I a).map_target hq
  have hWa_meas : Measurable Wa := by
    refine ContinuousOn.measurable_piecewise ?_ continuous_const.continuousOn htarget_meas
    refine ENNReal.continuous_ofReal.comp_continuousOn (ContinuousOn.mul ?_ ?_)
    · refine (chartDensity_continuousOn (I := I) g a).comp hsymm (fun q hq => ?_)
      rw [trivializationAt_baseSet_eq_chartAt_source (I := I) a]
      exact hsymm_maps hq
    · exact (chartAtlasPOU I M a).contMDiff.continuous.comp_continuousOn hsymm
  have hderiv : ∀ x ∈ Ka, HasFDerivWithinAt fa (fa' x) Ka x := by
    intro x hx
    have hxV : x ∈ V := hx.2
    have hcd : ContDiffAt ℝ 1 (fun z : E => extChartAt I a (f z)) x :=
      (hcoord x hxV).contDiffAt (hVopen.mem_nhds hxV)
    have hfd : HasFDerivAt (fun z : E => extChartAt I a (f z)) (fa' x) x :=
      (hcd.differentiableAt (by norm_num)).hasFDerivAt
    have heq : fa =ᶠ[nhds x] (fun z : E => extChartAt I a (f z)) :=
      eventuallyEq_of_mem (hVopen.mem_nhds hxV) (fun z hz => hfa z hz)
    exact (hfd.congr_of_eventuallyEq heq).hasFDerivWithinAt
  have hpoU_meas : Measurable (fun y : M => ENNReal.ofReal (chartAtlasPOU I M a y)) :=
    ENNReal.measurable_ofReal.comp (chartAtlasPOU I M a).contMDiff.continuous.measurable
  have heq : ∀ q ∈ (extChartAt I a).target,
      ENNReal.ofReal (chartDensity g a ((extChartAt I a).symm q)) *
          (f '' K).indicator (fun y : M =>
            ENNReal.ofReal (chartAtlasPOU I M a y)) ((extChartAt I a).symm q) =
        (fa '' Ka).indicator Wa q := by
    intro q hq
    by_cases hqimg : q ∈ fa '' Ka
    · have hqmem := hqimg
      obtain ⟨x, hxKa, hxq⟩ := hqimg
      have hxV : x ∈ V := hxKa.2
      have hfxS : f x ∈ S := hxV.2
      have hfax : fa x = extChartAt I a (f x) := hfa x hxV
      have hsymmq : (extChartAt I a).symm q = f x := by
        rw [← hxq, hfax]
        exact (extChartAt I a).left_inv (by rw [extChartAt_source]; exact hfxS)
      have hfximg : f x ∈ f '' K := ⟨x, hxKa.1, rfl⟩
      have hcdnn : 0 ≤ chartDensity g a (f x) := Real.sqrt_nonneg _
      rw [hsymmq, Set.indicator_of_mem hfximg, Set.indicator_of_mem hqmem,
        hWa q hq, hsymmq]
      exact (ENNReal.ofReal_mul hcdnn).symm
    · rw [Set.indicator_of_notMem hqimg]
      by_contra hne
      refine hqimg ?_
      have hind : (f '' K).indicator (fun y : M =>
          ENNReal.ofReal (chartAtlasPOU I M a y)) ((extChartAt I a).symm q) ≠ 0 :=
        fun hz => hne (by rw [hz, mul_zero])
      have himgmem : (extChartAt I a).symm q ∈ f '' K := by
        by_contra hnot
        exact hind (Set.indicator_of_notMem hnot _)
      have hpou_ne : ENNReal.ofReal
          (chartAtlasPOU I M a ((extChartAt I a).symm q)) ≠ 0 := by
        rwa [Set.indicator_of_mem himgmem] at hind
      have hpou_pos : 0 < chartAtlasPOU I M a ((extChartAt I a).symm q) :=
        ENNReal.ofReal_pos.mp (pos_iff_ne_zero.mpr hpou_ne)
      have hsymmS : (extChartAt I a).symm q ∈ S :=
        (chartAtlasPOU_isSubordinate I M) a
          (subset_tsupport _ (Function.mem_support.mpr hpou_pos.ne'))
      obtain ⟨x, hxK, hfx⟩ := himgmem
      have hxV : x ∈ V := ⟨hKU hxK, by change f x ∈ S; rw [hfx]; exact hsymmS⟩
      refine ⟨x, ⟨hxK, hxV⟩, ?_⟩
      rw [hfa x hxV, hfx]
      exact (extChartAt I a).right_inv hq
  rw [withDensity_apply _ himg,
    chartLocalMeasure_setLintegral_indicator (I := I) g a himg hpoU_meas]
  calc
    ∫⁻ q in (extChartAt I a).target,
        ENNReal.ofReal (chartDensity g a ((extChartAt I a).symm q)) *
          (f '' K).indicator (fun y : M => ENNReal.ofReal (chartAtlasPOU I M a y))
            ((extChartAt I a).symm q) ∂(modelHaar (E := E))
        = ∫⁻ q in (extChartAt I a).target, (fa '' Ka).indicator Wa q
            ∂(modelHaar (E := E)) :=
          setLIntegral_congr_fun htarget_meas heq
    _ ≤ ∫⁻ q, (fa '' Ka).indicator Wa q ∂(modelHaar (E := E)) :=
      setLIntegral_le_lintegral _ _
    _ ≤ ∫⁻ q in fa '' Ka, Wa q ∂(modelHaar (E := E)) :=
      lintegral_indicator_le _ _
    _ ≤ ∫⁻ x in Ka, Wa (fa x) * ENNReal.ofReal |(fa' x).det|
        ∂(modelHaar (E := E)) :=
      image_lintegral_le (modelHaar (E := E)) hKa hfa_meas hderiv hWa_meas
    _ = ∫⁻ x in Ka, ENNReal.ofReal (chartAtlasPOU I M a (f x)) *
        ENNReal.ofReal (paramDensity (I := I) g f x) ∂(modelHaar (E := E)) := by
      refine setLIntegral_congr_fun hKa (fun x hx => ?_)
      have hxV : x ∈ V := hx.2
      have hfxS : f x ∈ S := hxV.2
      have hfax : fa x = extChartAt I a (f x) := hfa x hxV
      have hmap : extChartAt I a (f x) ∈ (extChartAt I a).target :=
        (extChartAt I a).map_source (by rw [extChartAt_source]; exact hfxS)
      have hsymm : (extChartAt I a).symm (extChartAt I a (f x)) = f x :=
        (extChartAt I a).left_inv (by rw [extChartAt_source]; exact hfxS)
      have hWat : Wa (fa x) = ENNReal.ofReal
          (chartDensity g a (f x) * chartAtlasPOU I M a (f x)) := by
        rw [hfax, hWa _ hmap, hsymm]
      have hmdiff : MDifferentiableAt (modelWithCornersSelf ℝ E) I f x :=
        (((hf.mono hVU) x hxV).contMDiffAt (hVopen.mem_nhds hxV)).mdifferentiableAt
          (by norm_num)
      have hbase : f x ∈ (trivializationAt E (TangentSpace I) a).baseSet := by
        rw [trivializationAt_baseSet_eq_chartAt_source (I := I) a]
        exact hfxS
      have hjac := paramDensity_eq_abs_det_mul_chartDensity_of_mdifferentiableAt
        (I := I) g f hmdiff a hbase
      have hcdnn : 0 ≤ chartDensity g a (f x) := Real.sqrt_nonneg _
      rw [hWat, ← ENNReal.ofReal_mul (mul_nonneg hcdnn
        ((chartAtlasPOU I M).nonneg a (f x))),
        ← ENNReal.ofReal_mul ((chartAtlasPOU I M).nonneg a (f x))]
      dsimp only [fa']
      rw [hjac]
      ring_nf
    _ ≤ ∫⁻ x in K, ENNReal.ofReal (chartAtlasPOU I M a (f x)) *
        ENNReal.ofReal (paramDensity (I := I) g f x) ∂(modelHaar (E := E)) :=
      lintegral_mono_set inter_subset_left

private lemma pou_term_map_eq
    (g : SmoothRiemannianMetric I M) {f : E → M} {U K : Set E}
    (hU : IsOpen U) (hK : MeasurableSet K) (hKU : K ⊆ U)
    (hf : ContMDiffOn (modelWithCornersSelf ℝ E) I 1 f U)
    (hinj : Set.InjOn f K) (himg : MeasurableSet (f '' K)) (a : M) :
    ((chartLocalMeasure (I := I) g a).withDensity
        (fun y : M => ENNReal.ofReal (chartAtlasPOU I M a y))) (f '' K) =
      ∫⁻ x in K, ENNReal.ofReal (chartAtlasPOU I M a (f x)) *
        ENNReal.ofReal (paramDensity (I := I) g f x)
        ∂(modelHaar (E := E)) := by
  classical
  let S : Set M := (chartAt H a).source
  let V : Set E := U ∩ f ⁻¹' S
  let Ka : Set E := K ∩ V
  have hVopen : IsOpen V := by
    dsimp only [V, S]
    exact hf.continuousOn.isOpen_inter_preimage hU (chartAt H a).open_source
  have hVU : V ⊆ U := by
    dsimp only [V]
    exact inter_subset_left
  have hVchart : ∀ x ∈ V, f x ∈ (chartAt H a).source := by
    intro x hx
    exact hx.2
  have hKa : MeasurableSet Ka := hK.inter hVopen.measurableSet
  let fa : E → E := V.piecewise (fun x => extChartAt I a (f x)) 0
  let fa' : E → (E →L[ℝ] E) :=
    fun x => fderiv ℝ (fun z : E => extChartAt I a (f z)) x
  let Wa : E → ℝ≥0∞ := (extChartAt I a).target.piecewise
    (fun q => ENNReal.ofReal
      (chartDensity g a ((extChartAt I a).symm q) *
        chartAtlasPOU I M a ((extChartAt I a).symm q))) 0
  have hfa : ∀ x ∈ V, fa x = extChartAt I a (f x) := by
    intro x hx
    dsimp only [fa]
    exact Set.piecewise_eq_of_mem _ _ _ hx
  have hWa : ∀ q ∈ (extChartAt I a).target,
      Wa q = ENNReal.ofReal
        (chartDensity g a ((extChartAt I a).symm q) *
          chartAtlasPOU I M a ((extChartAt I a).symm q)) := by
    intro q hq
    dsimp only [Wa]
    exact Set.piecewise_eq_of_mem _ _ _ hq
  have hcoord : ContDiffOn ℝ 1 (fun x : E => extChartAt I a (f x)) V :=
    contDiffOn_extChartAt_comp (I := I) hf hVU a hVchart
  have htarget_meas : MeasurableSet (extChartAt I a).target :=
    measurableSet_extChartAt_target (I := I) a
  have hderiv : ∀ x ∈ Ka, HasFDerivWithinAt fa (fa' x) Ka x := by
    intro x hx
    have hxV : x ∈ V := hx.2
    have hcd : ContDiffAt ℝ 1 (fun z : E => extChartAt I a (f z)) x :=
      (hcoord x hxV).contDiffAt (hVopen.mem_nhds hxV)
    have hfd : HasFDerivAt (fun z : E => extChartAt I a (f z))
        (fa' x) x :=
      (hcd.differentiableAt (by norm_num)).hasFDerivAt
    have heq : fa =ᶠ[nhds x] (fun z : E => extChartAt I a (f z)) :=
      eventuallyEq_of_mem (hVopen.mem_nhds hxV) (fun z hz => hfa z hz)
    exact (hfd.congr_of_eventuallyEq heq).hasFDerivWithinAt
  have hfainj : Set.InjOn fa Ka := by
    intro x hx y hy hxy
    apply hinj hx.1 hy.1
    have hfx : f x ∈ (extChartAt I a).source := by
      rw [extChartAt_source]
      exact hx.2.2
    have hfy : f y ∈ (extChartAt I a).source := by
      rw [extChartAt_source]
      exact hy.2.2
    apply (extChartAt I a).injOn hfx hfy
    rw [← hfa x hx.2, ← hfa y hy.2]
    exact hxy
  have hImgMeas : MeasurableSet (fa '' Ka) :=
    measurable_image_of_fderivWithin hKa hderiv hfainj
  have hImgTarget : fa '' Ka ⊆ (extChartAt I a).target := by
    rintro q ⟨x, hx, rfl⟩
    rw [hfa x hx.2]
    apply (extChartAt I a).map_source
    rw [extChartAt_source]
    exact hx.2.2
  have hpoU_meas : Measurable
      (fun y : M => ENNReal.ofReal (chartAtlasPOU I M a y)) :=
    ENNReal.measurable_ofReal.comp
      (chartAtlasPOU I M a).contMDiff.continuous.measurable
  have heq : ∀ q ∈ (extChartAt I a).target,
      ENNReal.ofReal (chartDensity g a ((extChartAt I a).symm q)) *
          (f '' K).indicator
            (fun y : M => ENNReal.ofReal (chartAtlasPOU I M a y))
            ((extChartAt I a).symm q) =
        (fa '' Ka).indicator Wa q := by
    intro q hq
    by_cases hqimg : q ∈ fa '' Ka
    · have hqmem := hqimg
      obtain ⟨x, hxKa, hxq⟩ := hqimg
      have hxV : x ∈ V := hxKa.2
      have hfxS : f x ∈ S := hxV.2
      have hfax : fa x = extChartAt I a (f x) := hfa x hxV
      have hsymmq : (extChartAt I a).symm q = f x := by
        rw [← hxq, hfax]
        exact (extChartAt I a).left_inv
          (by rw [extChartAt_source]; exact hfxS)
      have hfximg : f x ∈ f '' K := ⟨x, hxKa.1, rfl⟩
      have hcdnn : 0 ≤ chartDensity g a (f x) := Real.sqrt_nonneg _
      rw [hsymmq, Set.indicator_of_mem hfximg,
        Set.indicator_of_mem hqmem, hWa q hq, hsymmq]
      exact (ENNReal.ofReal_mul hcdnn).symm
    · rw [Set.indicator_of_notMem hqimg]
      by_contra hne
      refine hqimg ?_
      have hind : (f '' K).indicator
          (fun y : M => ENNReal.ofReal (chartAtlasPOU I M a y))
          ((extChartAt I a).symm q) ≠ 0 :=
        fun hz => hne (by rw [hz, mul_zero])
      have himgmem : (extChartAt I a).symm q ∈ f '' K := by
        by_contra hnot
        exact hind (Set.indicator_of_notMem hnot _)
      have hpou_ne : ENNReal.ofReal
          (chartAtlasPOU I M a ((extChartAt I a).symm q)) ≠ 0 := by
        rwa [Set.indicator_of_mem himgmem] at hind
      have hpou_pos :
          0 < chartAtlasPOU I M a ((extChartAt I a).symm q) :=
        ENNReal.ofReal_pos.mp (pos_iff_ne_zero.mpr hpou_ne)
      have hsymmS : (extChartAt I a).symm q ∈ S :=
        (chartAtlasPOU_isSubordinate I M) a
          (subset_tsupport _ (Function.mem_support.mpr hpou_pos.ne'))
      obtain ⟨x, hxK, hfx⟩ := himgmem
      have hxV : x ∈ V :=
        ⟨hKU hxK, by change f x ∈ S; rw [hfx]; exact hsymmS⟩
      refine ⟨x, ⟨hxK, hxV⟩, ?_⟩
      rw [hfa x hxV, hfx]
      exact (extChartAt I a).right_inv hq
  rw [withDensity_apply _ himg,
    chartLocalMeasure_setLintegral_indicator
      (I := I) g a himg hpoU_meas]
  calc
    ∫⁻ q in (extChartAt I a).target,
          ENNReal.ofReal
              (chartDensity g a ((extChartAt I a).symm q)) *
            (f '' K).indicator
                (fun y : M => ENNReal.ofReal (chartAtlasPOU I M a y))
                ((extChartAt I a).symm q)
          ∂(modelHaar (E := E)) =
        ∫⁻ q in (extChartAt I a).target,
            (fa '' Ka).indicator Wa q ∂(modelHaar (E := E)) :=
      setLIntegral_congr_fun htarget_meas heq
    _ = ∫⁻ q in fa '' Ka, Wa q ∂(modelHaar (E := E)) := by
      rw [setLIntegral_indicator hImgMeas,
        inter_eq_left.mpr hImgTarget]
    _ = ∫⁻ x in Ka,
          ENNReal.ofReal |(fa' x).det| * Wa (fa x)
          ∂(modelHaar (E := E)) :=
      lintegral_image_eq_lintegral_abs_det_fderiv_mul
        (μ := modelHaar (E := E)) hKa hderiv hfainj Wa
    _ = ∫⁻ x in Ka,
          Wa (fa x) * ENNReal.ofReal |(fa' x).det|
          ∂(modelHaar (E := E)) := by
      refine setLIntegral_congr_fun hKa (fun x _ => ?_)
      exact mul_comm _ _
    _ = ∫⁻ x in Ka,
          ENNReal.ofReal (chartAtlasPOU I M a (f x)) *
            ENNReal.ofReal (paramDensity (I := I) g f x)
          ∂(modelHaar (E := E)) := by
      refine setLIntegral_congr_fun hKa (fun x hx => ?_)
      have hxV : x ∈ V := hx.2
      have hfxS : f x ∈ S := hxV.2
      have hfax : fa x = extChartAt I a (f x) := hfa x hxV
      have hmap : extChartAt I a (f x) ∈ (extChartAt I a).target :=
        (extChartAt I a).map_source
          (by rw [extChartAt_source]; exact hfxS)
      have hsymm :
          (extChartAt I a).symm (extChartAt I a (f x)) = f x :=
        (extChartAt I a).left_inv
          (by rw [extChartAt_source]; exact hfxS)
      have hWat : Wa (fa x) = ENNReal.ofReal
          (chartDensity g a (f x) * chartAtlasPOU I M a (f x)) := by
        rw [hfax, hWa _ hmap, hsymm]
      have hmdiff :
          MDifferentiableAt (modelWithCornersSelf ℝ E) I f x :=
        (((hf.mono hVU) x hxV).contMDiffAt
          (hVopen.mem_nhds hxV)).mdifferentiableAt (by norm_num)
      have hbase :
          f x ∈ (trivializationAt E (TangentSpace I) a).baseSet := by
        rw [trivializationAt_baseSet_eq_chartAt_source (I := I) a]
        exact hfxS
      have hjac := paramDensity_eq_abs_det_mul_chartDensity_of_mdifferentiableAt
        (I := I) g f hmdiff a hbase
      have hcdnn : 0 ≤ chartDensity g a (f x) := Real.sqrt_nonneg _
      rw [hWat,
        ← ENNReal.ofReal_mul
          (mul_nonneg hcdnn ((chartAtlasPOU I M).nonneg a (f x))),
        ← ENNReal.ofReal_mul ((chartAtlasPOU I M).nonneg a (f x))]
      dsimp only [fa']
      rw [hjac]
      ring_nf
    _ = ∫⁻ x in K,
          ENNReal.ofReal (chartAtlasPOU I M a (f x)) *
            ENNReal.ofReal (paramDensity (I := I) g f x)
          ∂(modelHaar (E := E)) := by
      rw [show Ka = K ∩ V from rfl, inter_comm,
        ← setLIntegral_indicator hVopen.measurableSet]
      refine setLIntegral_congr_fun hK (fun x hxK => ?_)
      by_cases hxV : x ∈ V
      · rw [Set.indicator_of_mem hxV]
      · rw [Set.indicator_of_notMem hxV]
        have hpou_zero : chartAtlasPOU I M a (f x) = 0 := by
          by_contra hne
          apply hxV
          exact ⟨hKU hxK,
            (chartAtlasPOU_isSubordinate I M) a
              (subset_tsupport _ (Function.mem_support.mpr hne))⟩
        rw [hpou_zero, ENNReal.ofReal_zero, zero_mul]

private lemma tsum_setLIntegral_paramDensity
    (g : SmoothRiemannianMetric I M) {f : E → M} {U K : Set E}
    (hU : IsOpen U) (hKmeas : MeasurableSet K) (hKU : K ⊆ U)
    (hf : ContMDiffOn 𝓘(ℝ, E) I 1 f U) :
    (∑' a : M, ∫⁻ x in K,
      ENNReal.ofReal (chartAtlasPOU I M a (f x)) *
        ENNReal.ofReal (paramDensity (I := I) g f x) ∂(modelHaar (E := E))) =
      ∫⁻ x in K, ENNReal.ofReal (paramDensity (I := I) g f x)
        ∂(modelHaar (E := E)) := by
  classical
  have hfK : ContinuousOn f K := hf.continuousOn.mono hKU
  have hJacK : ContinuousOn (paramDensity (I := I) g f) K :=
    (continuousOn_paramDensity (I := I) g hU hf).mono hKU
  have hsm : ∀ a : M, AEMeasurable (fun x : E =>
      ENNReal.ofReal (chartAtlasPOU I M a (f x)) *
        ENNReal.ofReal (paramDensity (I := I) g f x))
      ((modelHaar (E := E)).restrict K) := by
    intro a
    have hpou : ContinuousOn (fun x : E => chartAtlasPOU I M a (f x)) K :=
      (chartAtlasPOU I M a).contMDiff.continuous.comp_continuousOn hfK
    have hreal : ContinuousOn (fun x : E =>
        chartAtlasPOU I M a (f x) * paramDensity (I := I) g f x) K :=
      hpou.mul hJacK
    have hae : AEMeasurable (fun x : E => ENNReal.ofReal
        (chartAtlasPOU I M a (f x) * paramDensity (I := I) g f x))
        ((modelHaar (E := E)).restrict K) :=
      (ENNReal.measurable_ofReal.comp_aemeasurable (hreal.aemeasurable hKmeas))
    refine hae.congr (Filter.Eventually.of_forall (fun x => ?_))
    change ENNReal.ofReal
        (chartAtlasPOU I M a (f x) * paramDensity (I := I) g f x) =
      ENNReal.ofReal (chartAtlasPOU I M a (f x)) *
        ENNReal.ofReal (paramDensity (I := I) g f x)
    rw [ENNReal.ofReal_mul ((chartAtlasPOU I M).nonneg a (f x))]
  let T : Set M := {a : M | (Function.support (chartAtlasPOU I M a)).Nonempty}
  have hT_count : T.Countable := countable_nonempty_support_of_pou (I := I) (chartAtlasPOU I M)
  let _ : Countable T := hT_count.to_subtype
  have hsupp : Function.support (fun a : M => ∫⁻ x in K,
      ENNReal.ofReal (chartAtlasPOU I M a (f x)) *
        ENNReal.ofReal (paramDensity (I := I) g f x) ∂(modelHaar (E := E))) ⊆ T := by
    intro a ha
    by_contra haT
    refine ha ?_
    have hzero : Function.support (chartAtlasPOU I M a) = ∅ := by
      change ¬ (Function.support (chartAtlasPOU I M a)).Nonempty at haT
      exact Set.not_nonempty_iff_eq_empty.mp haT
    have hpou_zero : ∀ x : E, chartAtlasPOU I M a (f x) = 0 := by
      intro x
      by_contra hne
      have : f x ∈ Function.support (chartAtlasPOU I M a) := hne
      rw [hzero] at this
      exact this
    simp only [hpou_zero, ENNReal.ofReal_zero, zero_mul, lintegral_zero]
  have hsupp_pou : ∀ x : E, Function.support (fun a : M =>
      ENNReal.ofReal (chartAtlasPOU I M a (f x))) ⊆ T := by
    intro x a ha
    refine Set.nonempty_iff_ne_empty.mpr ?_
    intro hempty
    have hzero : chartAtlasPOU I M a (f x) = 0 := by
      by_contra hne
      have : f x ∈ Function.support (chartAtlasPOU I M a) := hne
      rw [hempty] at this
      exact this
    simp only [Function.mem_support, ne_eq, hzero, ENNReal.ofReal_zero,
      not_true_eq_false] at ha
  rw [tsum_subtype_eq_of_support_subset hsupp,
    ← lintegral_tsum (fun a : T => hsm a.val)]
  refine lintegral_congr (fun x => ?_)
  rw [ENNReal.tsum_mul_right]
  have hone : (∑' a : T, ENNReal.ofReal (chartAtlasPOU I M a.val (f x))) = 1 := by
    rw [← tsum_subtype_eq_of_support_subset (hsupp_pou x)]
    exact tsum_ofReal_pou_eq_one (I := I) (chartAtlasPOU I M) (f x)
  rw [hone, one_mul]

theorem riemannianVolumeMeasure_image_le
    (g : SmoothRiemannianMetric I M) {f : E → M} {U K : Set E}
    (hU : IsOpen U) (hKmeas : MeasurableSet K) (hKU : K ⊆ U)
    (hf : ContMDiffOn (modelWithCornersSelf ℝ E) I 1 f U)
    (himg : MeasurableSet (f '' K)) :
    riemannianVolumeMeasure (I := I) (M := M) g (f '' K) ≤
      ∫⁻ x in K, ENNReal.ofReal (paramDensity (I := I) g f x)
        ∂(modelHaar (E := E)) := by
  rw [riemannianVolumeMeasure_def, riemannianMeasure_def, Measure.sum_apply _ himg]
  exact (ENNReal.tsum_le_tsum (fun a =>
    pou_term_map_le (I := I) g hU hKmeas hKU hf himg a)).trans_eq
      (tsum_setLIntegral_paramDensity (I := I) g hU hKmeas hKU hf)

theorem riemannianVolumeMeasure_image_le_of_isCompact
    (g : SmoothRiemannianMetric I M) {f : E → M} {U K : Set E}
    (hU : IsOpen U) (hK : IsCompact K) (hKU : K ⊆ U)
    (hf : ContMDiffOn 𝓘(ℝ, E) I 1 f U) :
    riemannianVolumeMeasure (I := I) (M := M) g (f '' K) ≤
      ∫⁻ x in K, ENNReal.ofReal (paramDensity (I := I) g f x)
        ∂(modelHaar (E := E)) := by
  exact riemannianVolumeMeasure_image_le (I := I) g hU hK.measurableSet hKU hf
    (hK.image_of_continuousOn (hf.continuousOn.mono hKU)).measurableSet

theorem riemannianVolumeMeasure_image_eq
    (g : SmoothRiemannianMetric I M) {f : E → M} {U K : Set E}
    (hU : IsOpen U) (hK : MeasurableSet K) (hKU : K ⊆ U)
    (hf : ContMDiffOn (modelWithCornersSelf ℝ E) I 1 f U)
    (hinj : Set.InjOn f K) :
    riemannianVolumeMeasure (I := I) (M := M) g (f '' K) =
      ∫⁻ x in K, ENNReal.ofReal (paramDensity (I := I) g f x)
        ∂(modelHaar (E := E)) := by
  have himg : MeasurableSet (f '' K) :=
    hK.image_of_continuousOn_injOn (hf.continuousOn.mono hKU) hinj
  rw [riemannianVolumeMeasure_def, riemannianMeasure_def, Measure.sum_apply _ himg]
  exact (tsum_congr (fun a =>
    pou_term_map_eq (I := I) g hU hK hKU hf hinj himg a)).trans
      (tsum_setLIntegral_paramDensity (I := I) g hU hK hKU hf)

end DifferentialGeometry.Integral.Measure
