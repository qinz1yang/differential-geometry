import DifferentialGeometry.Geometry.Comparison.Volume.SegmentDensity
import DifferentialGeometry.Analysis.Integration.Measure.JacobianImageLe
import DifferentialGeometry.Analysis.Integration.Measure.Invariance

set_option autoImplicit false

noncomputable section

open Set Function Filter Bundle Manifold MeasureTheory
open scoped Topology Manifold ContDiff ENNReal

namespace DifferentialGeometry.Geometry.Riemannian.VolumeComparison

open DifferentialGeometry.Geometry.Riemannian.Exponential
open DifferentialGeometry.Geometry.Riemannian.Variation
open DifferentialGeometry.Integral.Measure

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]
  [NeZero (Module.finrank ℝ E)] [CompleteSpace E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [I.Boundaryless]
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [T2Space M] [T2Space (TangentBundle I M)] [SigmaCompactSpace M]
variable [RiemannianBundle (fun (x : M) ↦ TangentSpace I x)]

private local instance : MeasurableSpace E := borel E
private local instance : BorelSpace E := ⟨rfl⟩
private local instance : MeasurableSpace M := borel M
private local instance : BorelSpace M := ⟨rfl⟩

attribute [-instance] Tensor0SBundle.tangentSpace_normedAddCommGroup
  Tensor0SBundle.tangentSpace_normedSpace in
def expJacDensity
    [PseudoEMetricSpace M] [IsRiemannianManifold I M] [CompleteSpace M]
    [IsContinuousRiemannianBundle E (fun (x : M) ↦ TangentSpace I x)]
    (g : SmoothRiemannianMetric I M)
    (hEnorm : ∀ (y : M) (w : TangentSpace I y),
      ‖w‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner y w w)))
    (x : M) (v : E) : ℝ :=
  curveDensity (I := I) g
    (intrinsicGeodesic (I := I) g hEnorm x (show TangentSpace I x from v))
    (fun (i : Fin (Module.finrank ℝ E)) (t : ℝ) =>
      intrinsicJacobi g hEnorm x (show TangentSpace I x from v)
        (show TangentSpace I x from (chartModelBasis E i)) t) 1

attribute [-instance] Tensor0SBundle.tangentSpace_normedAddCommGroup
  Tensor0SBundle.tangentSpace_normedSpace in
omit [CompleteSpace E] [T2Space (TangentBundle I M)] in
private theorem pou_term_exp_eq
    [ConnectedSpace M] [PseudoEMetricSpace M] [IsRiemannianManifold I M] [CompleteSpace M]
    [IsContinuousRiemannianBundle E (fun (x : M) ↦ TangentSpace I x)]
    (g : SmoothRiemannianMetric I M)
    (hEnorm : ∀ (y : M) (w : TangentSpace I y),
      ‖w‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner y w w)))
    (x : M) {K : Set E} (hK : MeasurableSet K)
    (hKimg : MeasurableSet
      ((fun b : E => expMapIntrinsic (I := I) g hEnorm x
        (show TangentSpace I x from b)) '' K))
    (hinj : Set.InjOn
      (fun b : E => expMapIntrinsic (I := I) g hEnorm x
        (show TangentSpace I x from b)) K)
    (α : M) :
    ((chartLocalMeasure (I := I) g α).withDensity
        (fun y : M => ENNReal.ofReal (chartAtlasPOU I M α y)))
        ((fun b : E => expMapIntrinsic (I := I) g hEnorm x
          (show TangentSpace I x from b)) '' K)
      = ∫⁻ v in K,
          ENNReal.ofReal (chartAtlasPOU I M α
            (expMapIntrinsic (I := I) g hEnorm x
              (show TangentSpace I x from v)))
            * ENNReal.ofReal (expJacDensity (I := I) g hEnorm x v)
          ∂(modelHaar (E := E)) := by
  classical
  set Fmap : E → M :=
    fun b => expMapIntrinsic (I := I) g hEnorm x
      (show TangentSpace I x from b) with hFmap
  set S : Set M := (chartAt H α).source with hS
  set Uα : Set E := Fmap ⁻¹' S with hUα
  set Kα : Set E := K ∩ Uα with hKα
  have hFcont : Continuous Fmap :=
    (intrinsicFiber_smooth (I := I) g hEnorm x).continuous
  have hUαopen : IsOpen Uα :=
    (chartAt H α).open_source.preimage hFcont
  have hKαmeas : MeasurableSet Kα :=
    hK.inter hUαopen.measurableSet
  have hTmeas : MeasurableSet (extChartAt I α).target :=
    measurableSet_extChartAt_target (I := I) α
  set fα : E → E :=
    Uα.piecewise (fun b => extChartAt I α (Fmap b)) 0 with hfα
  set fα' : E → (E →L[ℝ] E) :=
    fun v => fderiv ℝ (fun b => extChartAt I α (Fmap b)) v with hfα'
  set Wα : E → ℝ≥0∞ :=
    (extChartAt I α).target.piecewise
      (fun q => ENNReal.ofReal
        (chartDensity g α ((extChartAt I α).symm q)
          * chartAtlasPOU I M α ((extChartAt I α).symm q))) 0 with hWα
  have hFmapeq : ∀ w : E, Fmap w =
      expMapIntrinsic (I := I) g hEnorm x
        (show TangentSpace I x from w) := fun _ => rfl
  have hcdnn : ∀ y : M, (0 : ℝ) ≤ chartDensity g α y :=
    fun _ => Real.sqrt_nonneg _
  have hpw : ∀ w ∈ Uα, fα w = extChartAt I α (Fmap w) :=
    fun w hw => by
      rw [hfα]
      exact Set.piecewise_eq_of_mem _ _ _ hw
  have hWpw : ∀ q ∈ (extChartAt I α).target,
      Wα q = ENNReal.ofReal
        (chartDensity g α ((extChartAt I α).symm q)
          * chartAtlasPOU I M α ((extChartAt I α).symm q)) :=
    fun q hq => by
      rw [hWα]
      exact Set.piecewise_eq_of_mem _ _ _ hq
  have hderiv :
      ∀ v ∈ Kα, HasFDerivWithinAt fα (fα' v) Kα v := by
    intro v hv
    have hvUα : v ∈ Uα := hv.2
    have hFvS : Fmap v ∈ S := hvUα
    have hcd :
        ContDiffAt ℝ ∞ (fun b => extChartAt I α (Fmap b)) v :=
      expChart_contDiffAt (I := I) g hEnorm x v α hFvS
    have hHF :
        HasFDerivAt (fun b => extChartAt I α (Fmap b))
          (fα' v) v :=
      (hcd.differentiableAt (by simp)).hasFDerivAt
    have hEq :
        fα =ᶠ[𝓝 v] (fun b => extChartAt I α (Fmap b)) := by
      filter_upwards [hUαopen.mem_nhds hvUα] with b hb using hpw b hb
    exact (hHF.congr_of_eventuallyEq hEq).hasFDerivWithinAt
  have hfαinj : Set.InjOn fα Kα := by
    intro v hv w hw hvw
    apply hinj hv.1 hw.1
    have hvS : Fmap v ∈ (extChartAt I α).source := by
      rw [extChartAt_source]
      exact hv.2
    have hwS : Fmap w ∈ (extChartAt I α).source := by
      rw [extChartAt_source]
      exact hw.2
    apply (extChartAt I α).injOn hvS hwS
    rw [← hpw v hv.2, ← hpw w hw.2]
    exact hvw
  have hImgMeas : MeasurableSet (fα '' Kα) :=
    measurable_image_of_fderivWithin hKαmeas hderiv hfαinj
  have hImgTarget : fα '' Kα ⊆ (extChartAt I α).target := by
    rintro q ⟨v, hv, rfl⟩
    rw [hpw v hv.2]
    apply (extChartAt I α).map_source
    rw [extChartAt_source]
    exact hv.2
  have hραmeas :
      Measurable (fun y : M =>
        ENNReal.ofReal (chartAtlasPOU I M α y)) :=
    ENNReal.measurable_ofReal.comp
      (chartAtlasPOU I M α).contMDiff.continuous.measurable
  have hHeq : ∀ p ∈ (extChartAt I α).target,
      ENNReal.ofReal
          (chartDensity g α ((extChartAt I α).symm p))
        * (Fmap '' K).indicator
            (fun y : M => ENNReal.ofReal (chartAtlasPOU I M α y))
            ((extChartAt I α).symm p)
      = (fα '' Kα).indicator Wα p := by
    intro p hp
    by_cases hpimg : p ∈ fα '' Kα
    · obtain ⟨v, hvKα, hvp⟩ := hpimg
      have hvUα : v ∈ Uα := hvKα.2
      have hFvS : Fmap v ∈ S := hvUα
      have hfαv : fα v = extChartAt I α (Fmap v) :=
        hpw v hvUα
      have hsymmp :
          (extChartAt I α).symm p = Fmap v := by
        rw [← hvp, hfαv]
        exact (extChartAt I α).left_inv
          (by rw [extChartAt_source]; exact hFvS)
      have himgmem : Fmap v ∈ Fmap '' K :=
        ⟨v, hvKα.1, rfl⟩
      rw [Set.indicator_of_mem
          (show p ∈ fα '' Kα from ⟨v, hvKα, hvp⟩),
        hWpw p hp, hsymmp, Set.indicator_of_mem himgmem,
        ENNReal.ofReal_mul (hcdnn (Fmap v))]
    · rw [Set.indicator_of_notMem hpimg]
      by_contra hne
      refine hpimg ?_
      have hind :
          (Fmap '' K).indicator
              (fun y : M =>
                ENNReal.ofReal (chartAtlasPOU I M α y))
              ((extChartAt I α).symm p) ≠ 0 :=
        fun h => hne (by rw [h, mul_zero])
      have hmemImg :
          (extChartAt I α).symm p ∈ Fmap '' K := by
        by_contra hnm
        exact hind (Set.indicator_of_notMem hnm _)
      have hρne :
          ENNReal.ofReal
              (chartAtlasPOU I M α ((extChartAt I α).symm p)) ≠ 0 := by
        rwa [Set.indicator_of_mem hmemImg] at hind
      have hρpos :
          0 < chartAtlasPOU I M α ((extChartAt I α).symm p) :=
        ENNReal.ofReal_pos.mp (pos_iff_ne_zero.mpr hρne)
      have hsymmS : (extChartAt I α).symm p ∈ S :=
        (chartAtlasPOU_isSubordinate I M) α
          (subset_tsupport _
            (Function.mem_support.mpr hρpos.ne'))
      obtain ⟨v, hvK, hFv⟩ := hmemImg
      have hvUα : v ∈ Uα := by
        change Fmap v ∈ S
        rw [hFv]
        exact hsymmS
      refine ⟨v, ⟨hvK, hvUα⟩, ?_⟩
      rw [hpw v hvUα, hFv]
      exact (extChartAt I α).right_inv hp
  rw [withDensity_apply _ hKimg,
    chartLocalMeasure_setLintegral_indicator
      (I := I) g α hKimg hραmeas]
  calc
    ∫⁻ p in (extChartAt I α).target,
          ENNReal.ofReal
              (chartDensity g α ((extChartAt I α).symm p))
            * (Fmap '' K).indicator
                (fun y : M =>
                  ENNReal.ofReal (chartAtlasPOU I M α y))
                ((extChartAt I α).symm p)
          ∂(modelHaar (E := E))
        = ∫⁻ p in (extChartAt I α).target,
            (fα '' Kα).indicator Wα p
          ∂(modelHaar (E := E)) :=
      setLIntegral_congr_fun hTmeas hHeq
    _ = ∫⁻ p in fα '' Kα, Wα p
          ∂(modelHaar (E := E)) := by
      rw [setLIntegral_indicator hImgMeas,
        inter_eq_left.mpr hImgTarget]
    _ = ∫⁻ v in Kα,
          ENNReal.ofReal |(fα' v).det| * Wα (fα v)
          ∂(modelHaar (E := E)) :=
      lintegral_image_eq_lintegral_abs_det_fderiv_mul
        (μ := modelHaar (E := E)) hKαmeas hderiv hfαinj Wα
    _ = ∫⁻ v in Kα,
          Wα (fα v) * ENNReal.ofReal |(fα' v).det|
          ∂(modelHaar (E := E)) := by
      refine setLIntegral_congr_fun hKαmeas (fun v _ => ?_)
      exact mul_comm _ _
    _ = ∫⁻ v in Kα,
          ENNReal.ofReal (chartAtlasPOU I M α
            (expMapIntrinsic (I := I) g hEnorm x
              (show TangentSpace I x from v)))
            * ENNReal.ofReal
                (expJacDensity (I := I) g hEnorm x v)
          ∂(modelHaar (E := E)) := by
      refine setLIntegral_congr_fun hKαmeas (fun v hv => ?_)
      have hvUα : v ∈ Uα := hv.2
      have hFvS : Fmap v ∈ S := hvUα
      have hfαv : fα v = extChartAt I α (Fmap v) :=
        hpw v hvUα
      have hmap :
          extChartAt I α (Fmap v) ∈ (extChartAt I α).target :=
        (extChartAt I α).map_source
          (by rw [extChartAt_source]; exact hFvS)
      have hsymmv :
          (extChartAt I α).symm
              (extChartAt I α (Fmap v)) = Fmap v :=
        (extChartAt I α).left_inv
          (by rw [extChartAt_source]; exact hFvS)
      have hWαv :
          Wα (fα v) =
            ENNReal.ofReal
              (chartDensity g α (Fmap v)
                * chartAtlasPOU I M α (Fmap v)) := by
        rw [hfαv, hWpw _ hmap, hsymmv]
      have hden :
          chartDensity g α (Fmap v) * |(fα' v).det| =
            expJacDensity (I := I) g hEnorm x v :=
        exp_density_curve (I := I) g hEnorm x v α hFvS
      rw [hWαv,
        ← ENNReal.ofReal_mul
          (mul_nonneg (hcdnn (Fmap v))
            ((chartAtlasPOU I M).nonneg α (Fmap v))),
        ← ENNReal.ofReal_mul
          ((chartAtlasPOU I M).nonneg α _)]
      congr 1
      rw [← hden]
      simp only [hFmapeq]
      ring
    _ = ∫⁻ v in K,
          ENNReal.ofReal (chartAtlasPOU I M α
            (expMapIntrinsic (I := I) g hEnorm x
              (show TangentSpace I x from v)))
            * ENNReal.ofReal
                (expJacDensity (I := I) g hEnorm x v)
          ∂(modelHaar (E := E)) := by
      rw [hKα, inter_comm,
        ← setLIntegral_indicator hUαopen.measurableSet]
      refine setLIntegral_congr_fun hK (fun v _ => ?_)
      by_cases hvUα : v ∈ Uα
      · rw [Set.indicator_of_mem hvUα]
      · rw [Set.indicator_of_notMem hvUα]
        have hρzero :
            chartAtlasPOU I M α
              (expMapIntrinsic (I := I) g hEnorm x
                (show TangentSpace I x from v)) = 0 := by
          by_contra hne
          apply hvUα
          change Fmap v ∈ S
          exact (chartAtlasPOU_isSubordinate I M) α
            (subset_tsupport _ (Function.mem_support.mpr hne))
        rw [hρzero, ENNReal.ofReal_zero, zero_mul]

omit [CompleteSpace E] [T2Space (TangentBundle I M)] in
attribute [-instance] Tensor0SBundle.tangentSpace_normedAddCommGroup
  Tensor0SBundle.tangentSpace_normedSpace in
theorem expJac_continuous
    [PseudoEMetricSpace M] [IsRiemannianManifold I M] [CompleteSpace M]
    [IsContinuousRiemannianBundle E (fun (x : M) ↦ TangentSpace I x)]
    (g : SmoothRiemannianMetric I M)
    (hEnorm : ∀ (y : M) (w : TangentSpace I y),
      ‖w‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner y w w)))
    (x : M) :
    Continuous (fun v : E => expJacDensity (I := I) g hEnorm x v) := by
  rw [continuous_iff_continuousAt]
  intro v₀
  set F : E → M := fun b => expMapIntrinsic (I := I) g hEnorm x (show TangentSpace I x from b)
    with hF
  have hFcont : Continuous F := (intrinsicFiber_smooth (I := I) g hEnorm x).continuous
  set y₀ : M := F v₀ with hy₀
  have hsrc0 : F v₀ ∈ (chartAt H y₀).source := mem_chart_source H y₀
  set φ : E → E := fun b => extChartAt I y₀ (F b) with hφ
  set ψ : E → ℝ := fun v => chartDensity g y₀ (F v) * |(fderiv ℝ φ v).det| with hψ
  have hUnhds : F ⁻¹' (chartAt H y₀).source ∈ 𝓝 v₀ :=
    hFcont.continuousAt.preimage_mem_nhds ((chartAt H y₀).open_source.mem_nhds hsrc0)
  have heq : (fun v : E => expJacDensity (I := I) g hEnorm x v) =ᶠ[𝓝 v₀] ψ := by
    filter_upwards [hUnhds] with v hv
    change expJacDensity (I := I) g hEnorm x v = chartDensity g y₀ (F v) * |(fderiv ℝ φ v).det|
    exact (exp_density_curve (I := I) g hEnorm x v y₀ hv).symm
  have hcd : ContinuousAt (fun v : E => chartDensity g y₀ (F v)) v₀ := by
    have h1 : ContinuousAt (chartDensity g y₀) (F v₀) := by
      refine (chartDensity_continuousOn (I := I) g y₀).continuousAt ?_
      refine (trivializationAt E (TangentSpace I) y₀).open_baseSet.mem_nhds ?_
      rw [trivializationAt_baseSet_eq_chartAt_source (I := I) y₀]
      exact hsrc0
    exact h1.comp hFcont.continuousAt
  have hdet : ContinuousAt (fun v : E => |(fderiv ℝ φ v).det|) v₀ := by
    have hφc : ContDiffAt ℝ ∞ φ v₀ := expChart_contDiffAt (I := I) g hEnorm x v₀ y₀ hsrc0
    have hfd : ContinuousAt (fun v : E => fderiv ℝ φ v) v₀ :=
      hφc.continuousAt_fderiv (by simp)
    exact continuous_abs.continuousAt.comp
      (ContinuousLinearMap.continuous_det.continuousAt.comp hfd)
  exact (hcd.mul hdet).congr heq.symm

omit [CompleteSpace E] [T2Space (TangentBundle I M)] in
attribute [-instance] Tensor0SBundle.tangentSpace_normedAddCommGroup
  Tensor0SBundle.tangentSpace_normedSpace in
private theorem pou_term_exp_le
    [ConnectedSpace M] [PseudoEMetricSpace M] [IsRiemannianManifold I M] [CompleteSpace M]
    [IsContinuousRiemannianBundle E (fun (x : M) ↦ TangentSpace I x)]
    (g : SmoothRiemannianMetric I M)
    (hEnorm : ∀ (y : M) (w : TangentSpace I y),
      ‖w‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner y w w)))
    (x : M) {K : Set E} (hK : MeasurableSet K)
    (hKimg : MeasurableSet
      ((fun b : E => expMapIntrinsic (I := I) g hEnorm x (show TangentSpace I x from b)) '' K))
    (α : M) :
    ((chartLocalMeasure (I := I) g α).withDensity
        (fun y : M => ENNReal.ofReal (chartAtlasPOU I M α y)))
        ((fun b : E => expMapIntrinsic (I := I) g hEnorm x (show TangentSpace I x from b)) '' K)
      ≤ ∫⁻ v in K,
          ENNReal.ofReal (chartAtlasPOU I M α
            (expMapIntrinsic (I := I) g hEnorm x (show TangentSpace I x from v)))
            * ENNReal.ofReal (expJacDensity (I := I) g hEnorm x v) ∂(modelHaar (E := E)) := by
  classical
  set Fmap : E → M :=
    fun b => expMapIntrinsic (I := I) g hEnorm x (show TangentSpace I x from b) with hFmap
  set S : Set M := (chartAt H α).source with hS
  set Uα : Set E := Fmap ⁻¹' S with hUα
  set Kα : Set E := K ∩ Uα with hKα
  have hFcont : Continuous Fmap := (intrinsicFiber_smooth (I := I) g hEnorm x).continuous
  have hUαopen : IsOpen Uα := (chartAt H α).open_source.preimage hFcont
  have hKαmeas : MeasurableSet Kα := hK.inter hUαopen.measurableSet
  have hTmeas : MeasurableSet (extChartAt I α).target :=
    measurableSet_extChartAt_target (I := I) α
  set fα : E → E := Uα.piecewise (fun b => extChartAt I α (Fmap b)) 0 with hfα
  set fα' : E → (E →L[ℝ] E) := fun v => fderiv ℝ (fun b => extChartAt I α (Fmap b)) v with hfα'
  set Wα : E → ℝ≥0∞ := (extChartAt I α).target.piecewise
    (fun q => ENNReal.ofReal (chartDensity g α ((extChartAt I α).symm q)
      * chartAtlasPOU I M α ((extChartAt I α).symm q))) 0 with hWα
  have hFmapeq : ∀ w : E, Fmap w
      = expMapIntrinsic (I := I) g hEnorm x (show TangentSpace I x from w) := fun _ => rfl
  have hcdnn : ∀ y : M, (0 : ℝ) ≤ chartDensity g α y := fun _ => Real.sqrt_nonneg _
  have hpw : ∀ w ∈ Uα, fα w = extChartAt I α (Fmap w) := fun w hw => by
    rw [hfα]; exact Set.piecewise_eq_of_mem _ _ _ hw
  have hWpw : ∀ q ∈ (extChartAt I α).target,
      Wα q = ENNReal.ofReal (chartDensity g α ((extChartAt I α).symm q)
        * chartAtlasPOU I M α ((extChartAt I α).symm q)) := fun q hq => by
    rw [hWα]; exact Set.piecewise_eq_of_mem _ _ _ hq
  have hfα_meas : Measurable fα := by
    refine ContinuousOn.measurable_piecewise ?_ continuous_const.continuousOn
      hUαopen.measurableSet
    refine (continuousOn_extChartAt (I := I) α).comp hFcont.continuousOn (fun b hb => ?_)
    rw [extChartAt_source]; exact hb
  have hsymmOn : ContinuousOn (extChartAt I α).symm (extChartAt I α).target :=
    continuousOn_extChartAt_symm (I := I) α
  have hsymm_maps : MapsTo (extChartAt I α).symm (extChartAt I α).target S := by
    intro q hq
    rw [hS, ← extChartAt_source (I := I)]; exact (extChartAt I α).map_target hq
  have hWα_meas : Measurable Wα := by
    refine ContinuousOn.measurable_piecewise ?_ continuous_const.continuousOn hTmeas
    refine ENNReal.continuous_ofReal.comp_continuousOn (ContinuousOn.mul ?_ ?_)
    · refine (chartDensity_continuousOn (I := I) g α).comp hsymmOn (fun q hq => ?_)
      rw [trivializationAt_baseSet_eq_chartAt_source (I := I) α]; exact hsymm_maps hq
    · exact (chartAtlasPOU I M α).contMDiff.continuous.comp_continuousOn hsymmOn
  have hderiv : ∀ v ∈ Kα, HasFDerivWithinAt fα (fα' v) Kα v := by
    intro v hv
    have hvUα : v ∈ Uα := hv.2
    have hFvS : Fmap v ∈ S := hvUα
    have hcd : ContDiffAt ℝ ∞ (fun b => extChartAt I α (Fmap b)) v :=
      expChart_contDiffAt (I := I) g hEnorm x v α hFvS
    have hHF : HasFDerivAt (fun b => extChartAt I α (Fmap b)) (fα' v) v :=
      (hcd.differentiableAt (by simp)).hasFDerivAt
    have hEq : fα =ᶠ[𝓝 v] (fun b => extChartAt I α (Fmap b)) := by
      filter_upwards [hUαopen.mem_nhds hvUα] with b hb using hpw b hb
    exact (hHF.congr_of_eventuallyEq hEq).hasFDerivWithinAt
  have hραmeas : Measurable (fun y : M => ENNReal.ofReal (chartAtlasPOU I M α y)) :=
    ENNReal.measurable_ofReal.comp (chartAtlasPOU I M α).contMDiff.continuous.measurable
  have hHeq : ∀ p ∈ (extChartAt I α).target,
      ENNReal.ofReal (chartDensity g α ((extChartAt I α).symm p))
        * (Fmap '' K).indicator (fun y : M => ENNReal.ofReal (chartAtlasPOU I M α y))
            ((extChartAt I α).symm p)
      = (fα '' Kα).indicator Wα p := by
    intro p hp
    by_cases hpimg : p ∈ fα '' Kα
    · obtain ⟨v, hvKα, hvp⟩ := hpimg
      have hvUα : v ∈ Uα := hvKα.2
      have hFvS : Fmap v ∈ S := hvUα
      have hfαv : fα v = extChartAt I α (Fmap v) := hpw v hvUα
      have hsymmp : (extChartAt I α).symm p = Fmap v := by
        rw [← hvp, hfαv]
        exact (extChartAt I α).left_inv (by rw [extChartAt_source]; exact hFvS)
      have himgmem : Fmap v ∈ Fmap '' K := ⟨v, hvKα.1, rfl⟩
      rw [Set.indicator_of_mem (show p ∈ fα '' Kα from ⟨v, hvKα, hvp⟩), hWpw p hp, hsymmp,
        Set.indicator_of_mem himgmem, ENNReal.ofReal_mul (hcdnn (Fmap v))]
    · rw [Set.indicator_of_notMem hpimg]
      by_contra hne
      refine hpimg ?_
      have hind : (Fmap '' K).indicator (fun y : M => ENNReal.ofReal (chartAtlasPOU I M α y))
          ((extChartAt I α).symm p) ≠ 0 := fun h => hne (by rw [h, mul_zero])
      have hmemImg : (extChartAt I α).symm p ∈ Fmap '' K := by
        by_contra hnm; exact hind (Set.indicator_of_notMem hnm _)
      have hρne : ENNReal.ofReal (chartAtlasPOU I M α ((extChartAt I α).symm p)) ≠ 0 := by
        rwa [Set.indicator_of_mem hmemImg] at hind
      have hρpos : 0 < chartAtlasPOU I M α ((extChartAt I α).symm p) :=
        ENNReal.ofReal_pos.mp (pos_iff_ne_zero.mpr hρne)
      have hsymmS : (extChartAt I α).symm p ∈ S :=
        (chartAtlasPOU_isSubordinate I M) α
          (subset_tsupport _ (Function.mem_support.mpr hρpos.ne'))
      obtain ⟨v, hvK, hFv⟩ := hmemImg
      have hvUα : v ∈ Uα := by change Fmap v ∈ S; rw [hFv]; exact hsymmS
      refine ⟨v, ⟨hvK, hvUα⟩, ?_⟩
      rw [hpw v hvUα, hFv]
      exact (extChartAt I α).right_inv hp
  rw [withDensity_apply _ hKimg,
    chartLocalMeasure_setLintegral_indicator (I := I) g α hKimg hραmeas]
  calc ∫⁻ p in (extChartAt I α).target,
          ENNReal.ofReal (chartDensity g α ((extChartAt I α).symm p))
            * (Fmap '' K).indicator (fun y : M => ENNReal.ofReal (chartAtlasPOU I M α y))
                ((extChartAt I α).symm p) ∂(modelHaar (E := E))
      = ∫⁻ p in (extChartAt I α).target, (fα '' Kα).indicator Wα p ∂(modelHaar (E := E)) :=
        setLIntegral_congr_fun hTmeas hHeq
    _ ≤ ∫⁻ p, (fα '' Kα).indicator Wα p ∂(modelHaar (E := E)) :=
        setLIntegral_le_lintegral _ _
    _ ≤ ∫⁻ q in fα '' Kα, Wα q ∂(modelHaar (E := E)) := lintegral_indicator_le _ _
    _ ≤ ∫⁻ v in Kα, Wα (fα v) * ENNReal.ofReal |(fα' v).det| ∂(modelHaar (E := E)) :=
        image_lintegral_le (modelHaar (E := E)) hKαmeas hfα_meas hderiv hWα_meas
    _ = ∫⁻ v in Kα, ENNReal.ofReal (chartAtlasPOU I M α
            (expMapIntrinsic (I := I) g hEnorm x (show TangentSpace I x from v)))
          * ENNReal.ofReal (expJacDensity (I := I) g hEnorm x v) ∂(modelHaar (E := E)) := by
        refine setLIntegral_congr_fun hKαmeas (fun v hv => ?_)
        have hvUα : v ∈ Uα := hv.2
        have hFvS : Fmap v ∈ S := hvUα
        have hfαv : fα v = extChartAt I α (Fmap v) := hpw v hvUα
        have hmap : extChartAt I α (Fmap v) ∈ (extChartAt I α).target :=
          (extChartAt I α).map_source (by rw [extChartAt_source]; exact hFvS)
        have hsymmv : (extChartAt I α).symm (extChartAt I α (Fmap v)) = Fmap v :=
          (extChartAt I α).left_inv (by rw [extChartAt_source]; exact hFvS)
        have hWαv : Wα (fα v)
            = ENNReal.ofReal (chartDensity g α (Fmap v) * chartAtlasPOU I M α (Fmap v)) := by
          rw [hfαv, hWpw _ hmap, hsymmv]
        have hden : chartDensity g α (Fmap v) * |(fα' v).det|
            = expJacDensity (I := I) g hEnorm x v :=
          exp_density_curve (I := I) g hEnorm x v α hFvS
        rw [hWαv,
          ← ENNReal.ofReal_mul (mul_nonneg (hcdnn (Fmap v)) ((chartAtlasPOU I M).nonneg α (Fmap v))),
          ← ENNReal.ofReal_mul ((chartAtlasPOU I M).nonneg α _)]
        congr 1
        rw [← hden]
        simp only [hFmapeq]
        ring
    _ ≤ ∫⁻ v in K, ENNReal.ofReal (chartAtlasPOU I M α
            (expMapIntrinsic (I := I) g hEnorm x (show TangentSpace I x from v)))
          * ENNReal.ofReal (expJacDensity (I := I) g hEnorm x v) ∂(modelHaar (E := E)) :=
        lintegral_mono_set Set.inter_subset_left

omit [CompleteSpace E] [T2Space (TangentBundle I M)] in
attribute [-instance] Tensor0SBundle.tangentSpace_normedAddCommGroup
  Tensor0SBundle.tangentSpace_normedSpace in
theorem riemVol_exp_image_le
    [ConnectedSpace M] [PseudoEMetricSpace M] [IsRiemannianManifold I M] [CompleteSpace M]
    [IsContinuousRiemannianBundle E (fun (x : M) ↦ TangentSpace I x)]
    (g : SmoothRiemannianMetric I M)
    (hEnorm : ∀ (y : M) (w : TangentSpace I y),
      ‖w‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner y w w)))
    (x : M) {K : Set E} (hK : IsCompact K) :
    riemannianVolumeMeasure (I := I) (M := M) g
        ((fun b : E => expMapIntrinsic (I := I) g hEnorm x (show TangentSpace I x from b)) '' K)
      ≤ ∫⁻ v in K, ENNReal.ofReal (expJacDensity (I := I) g hEnorm x v) ∂(modelHaar (E := E)) := by
  classical
  have hFcont : Continuous
      (fun b : E => expMapIntrinsic (I := I) g hEnorm x (show TangentSpace I x from b)) :=
    (intrinsicFiber_smooth (I := I) g hEnorm x).continuous
  have hDcont : Continuous (fun v : E => expJacDensity (I := I) g hEnorm x v) :=
    expJac_continuous (I := I) g hEnorm x
  have himg : MeasurableSet
      ((fun b : E => expMapIntrinsic (I := I) g hEnorm x (show TangentSpace I x from b)) '' K) :=
    (hK.image hFcont).measurableSet
  have hρcont : ∀ α : M, Continuous (chartAtlasPOU I M α) :=
    fun α => (chartAtlasPOU I M α).contMDiff.continuous
  have hsm : ∀ α : M, Measurable (fun v : E =>
      ENNReal.ofReal (chartAtlasPOU I M α
          (expMapIntrinsic (I := I) g hEnorm x (show TangentSpace I x from v)))
        * ENNReal.ofReal (expJacDensity (I := I) g hEnorm x v)) := fun α =>
    (ENNReal.measurable_ofReal.comp ((hρcont α).comp hFcont).measurable).mul
      (ENNReal.measurable_ofReal.comp hDcont.measurable)
  set Tρ : Set M := {α : M | (Function.support (chartAtlasPOU I M α)).Nonempty} with hTρ
  have hCρ : Tρ.Countable := countable_nonempty_support_of_pou (I := I) (chartAtlasPOU I M)
  haveI : Countable Tρ := hCρ.to_subtype
  have hsupp : Function.support (fun α : M => ∫⁻ v in K,
      ENNReal.ofReal (chartAtlasPOU I M α
          (expMapIntrinsic (I := I) g hEnorm x (show TangentSpace I x from v)))
        * ENNReal.ofReal (expJacDensity (I := I) g hEnorm x v) ∂(modelHaar (E := E))) ⊆ Tρ := by
    intro α hα
    by_contra hαT
    refine hα ?_
    have hz : Function.support (chartAtlasPOU I M α) = ∅ := by
      rw [hTρ, Set.mem_setOf_eq, Set.not_nonempty_iff_eq_empty] at hαT; exact hαT
    have hzero : ∀ v : E, chartAtlasPOU I M α
        (expMapIntrinsic (I := I) g hEnorm x (show TangentSpace I x from v)) = 0 := by
      intro v
      by_contra hne
      have hmem : _ ∈ Function.support (chartAtlasPOU I M α) := hne
      rw [hz] at hmem; exact hmem
    simp only [hzero, ENNReal.ofReal_zero, zero_mul, lintegral_zero]
  have hsuppρ : ∀ v : E, Function.support (fun α : M => ENNReal.ofReal
      (chartAtlasPOU I M α
        (expMapIntrinsic (I := I) g hEnorm x (show TangentSpace I x from v)))) ⊆ Tρ := by
    intro v α hα
    rw [hTρ, Set.mem_setOf_eq]
    refine Set.nonempty_iff_ne_empty.2 (fun hempty => ?_)
    have hval : chartAtlasPOU I M α
        (expMapIntrinsic (I := I) g hEnorm x (show TangentSpace I x from v)) = 0 := by
      by_contra hne
      have hmem : _ ∈ Function.support (chartAtlasPOU I M α) := hne
      rw [hempty] at hmem; exact hmem
    simp only [Function.mem_support, ne_eq, hval, ENNReal.ofReal_zero, not_true_eq_false] at hα
  rw [riemannianVolumeMeasure_def, riemannianMeasure_def, Measure.sum_apply _ himg]
  refine le_trans (ENNReal.tsum_le_tsum (fun α =>
    pou_term_exp_le (I := I) g hEnorm x hK.measurableSet himg α)) ?_
  rw [DifferentialGeometry.Integral.Measure.tsum_subtype_eq_of_support_subset hsupp,
    ← lintegral_tsum (fun α : Tρ => (hsm α.val).aemeasurable)]
  refine le_of_eq (lintegral_congr (fun v => ?_))
  rw [ENNReal.tsum_mul_right]
  have h1 : (∑' α : Tρ, ENNReal.ofReal (chartAtlasPOU I M α.val
      (expMapIntrinsic (I := I) g hEnorm x (show TangentSpace I x from v)))) = 1 := by
    rw [← DifferentialGeometry.Integral.Measure.tsum_subtype_eq_of_support_subset (hsuppρ v)]
    exact tsum_ofReal_pou_eq_one (I := I) (chartAtlasPOU I M)
      (expMapIntrinsic (I := I) g hEnorm x (show TangentSpace I x from v))
  rw [h1, one_mul]

attribute [-instance] Tensor0SBundle.tangentSpace_normedAddCommGroup
  Tensor0SBundle.tangentSpace_normedSpace in
omit [T2Space (TangentBundle I M)] in
theorem riemVol_exp_image_eq
    [ConnectedSpace M] [PseudoEMetricSpace M]
    [IsRiemannianManifold I M] [CompleteSpace M]
    [IsContinuousRiemannianBundle E
      (fun (x : M) ↦ TangentSpace I x)]
    (g : SmoothRiemannianMetric I M)
    (hEnorm : ∀ (y : M) (w : TangentSpace I y),
      ‖w‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner y w w)))
    (x : M) {K : Set E} (hK : MeasurableSet K)
    (hinj : Set.InjOn
      (fun b : E => expMapIntrinsic (I := I) g hEnorm x
        (show TangentSpace I x from b)) K) :
    riemannianVolumeMeasure (I := I) (M := M) g
        ((fun b : E => expMapIntrinsic (I := I) g hEnorm x
          (show TangentSpace I x from b)) '' K)
      = ∫⁻ v in K,
          ENNReal.ofReal (expJacDensity (I := I) g hEnorm x v)
        ∂(modelHaar (E := E)) := by
  classical
  have hFcont : Continuous
      (fun b : E => expMapIntrinsic (I := I) g hEnorm x
        (show TangentSpace I x from b)) :=
    (intrinsicFiber_smooth (I := I) g hEnorm x).continuous
  have hDcont : Continuous
      (fun v : E => expJacDensity (I := I) g hEnorm x v) :=
    expJac_continuous (I := I) g hEnorm x
  have himg : MeasurableSet
      ((fun b : E => expMapIntrinsic (I := I) g hEnorm x
        (show TangentSpace I x from b)) '' K) :=
    hK.image_of_continuousOn_injOn hFcont.continuousOn hinj
  have hρcont : ∀ α : M, Continuous (chartAtlasPOU I M α) :=
    fun α => (chartAtlasPOU I M α).contMDiff.continuous
  have hsm : ∀ α : M, Measurable (fun v : E =>
      ENNReal.ofReal (chartAtlasPOU I M α
          (expMapIntrinsic (I := I) g hEnorm x
            (show TangentSpace I x from v)))
        * ENNReal.ofReal
            (expJacDensity (I := I) g hEnorm x v)) :=
    fun α =>
      (ENNReal.measurable_ofReal.comp
          ((hρcont α).comp hFcont).measurable).mul
        (ENNReal.measurable_ofReal.comp hDcont.measurable)
  set Tρ : Set M :=
    {α : M | (Function.support
      (chartAtlasPOU I M α)).Nonempty} with hTρ
  have hCρ : Tρ.Countable :=
    countable_nonempty_support_of_pou
      (I := I) (chartAtlasPOU I M)
  haveI : Countable Tρ := hCρ.to_subtype
  have hsupp : Function.support (fun α : M =>
      ∫⁻ v in K,
        ENNReal.ofReal (chartAtlasPOU I M α
            (expMapIntrinsic (I := I) g hEnorm x
              (show TangentSpace I x from v)))
          * ENNReal.ofReal
              (expJacDensity (I := I) g hEnorm x v)
        ∂(modelHaar (E := E))) ⊆ Tρ := by
    intro α hα
    by_contra hαT
    refine hα ?_
    have hz : Function.support (chartAtlasPOU I M α) = ∅ := by
      rw [hTρ, Set.mem_setOf_eq,
        Set.not_nonempty_iff_eq_empty] at hαT
      exact hαT
    have hzero : ∀ v : E,
        chartAtlasPOU I M α
          (expMapIntrinsic (I := I) g hEnorm x
            (show TangentSpace I x from v)) = 0 := by
      intro v
      by_contra hne
      have hmem : _ ∈
          Function.support (chartAtlasPOU I M α) := hne
      rw [hz] at hmem
      exact hmem
    simp only [hzero, ENNReal.ofReal_zero, zero_mul,
      lintegral_zero]
  have hsuppρ : ∀ v : E,
      Function.support (fun α : M =>
        ENNReal.ofReal (chartAtlasPOU I M α
          (expMapIntrinsic (I := I) g hEnorm x
            (show TangentSpace I x from v)))) ⊆ Tρ := by
    intro v α hα
    rw [hTρ, Set.mem_setOf_eq]
    refine Set.nonempty_iff_ne_empty.2 (fun hempty => ?_)
    have hval :
        chartAtlasPOU I M α
          (expMapIntrinsic (I := I) g hEnorm x
            (show TangentSpace I x from v)) = 0 := by
      by_contra hne
      have hmem : _ ∈
          Function.support (chartAtlasPOU I M α) := hne
      rw [hempty] at hmem
      exact hmem
    simp only [Function.mem_support, ne_eq, hval,
      ENNReal.ofReal_zero, not_true_eq_false] at hα
  rw [riemannianVolumeMeasure_def, riemannianMeasure_def,
    Measure.sum_apply _ himg]
  calc
    _ = ∑' α : M,
        ∫⁻ v in K,
          ENNReal.ofReal (chartAtlasPOU I M α
              (expMapIntrinsic (I := I) g hEnorm x
                (show TangentSpace I x from v)))
            * ENNReal.ofReal
                (expJacDensity (I := I) g hEnorm x v)
          ∂(modelHaar (E := E)) :=
      tsum_congr fun α =>
        pou_term_exp_eq (I := I) g hEnorm x hK himg hinj α
    _ = ∫⁻ v in K,
          ENNReal.ofReal
            (expJacDensity (I := I) g hEnorm x v)
        ∂(modelHaar (E := E)) := by
      rw [DifferentialGeometry.Integral.Measure.tsum_subtype_eq_of_support_subset
          hsupp,
        ← lintegral_tsum
          (fun α : Tρ => (hsm α.val).aemeasurable)]
      refine lintegral_congr (fun v => ?_)
      rw [ENNReal.tsum_mul_right]
      have h1 :
          (∑' α : Tρ,
            ENNReal.ofReal (chartAtlasPOU I M α.val
              (expMapIntrinsic (I := I) g hEnorm x
                (show TangentSpace I x from v)))) = 1 := by
        rw [← DifferentialGeometry.Integral.Measure.tsum_subtype_eq_of_support_subset
          (hsuppρ v)]
        exact tsum_ofReal_pou_eq_one
          (I := I) (chartAtlasPOU I M)
          (expMapIntrinsic (I := I) g hEnorm x
            (show TangentSpace I x from v))
      rw [h1, one_mul]

omit [NeZero (Module.finrank ℝ E)] [CompleteSpace E] [T2Space M] [SigmaCompactSpace M] in
private theorem exists_inj_parts
    {F : E → M} {U : Set E} (hU : MeasurableSet U)
    (hloc : IsLocalHomeomorphOn F U) :
    ∃ P : ℕ → Set E,
      (∀ n, MeasurableSet (P n)) ∧
      Pairwise (Disjoint on P) ∧
      (⋃ n, P n) = U ∧
      ∀ n, Set.InjOn F (P n) := by
  classical
  choose e he hFe using hloc
  let V : E → Set E := fun x =>
    if hx : x ∈ U then (e x hx).source else ∅
  have hVopen : ∀ x, IsOpen (V x) := by
    intro x
    by_cases hx : x ∈ U
    · simpa only [V, dif_pos hx] using (e x hx).open_source
    · simp only [V, dif_neg hx, isOpen_empty]
  have hxV : ∀ x (hx : x ∈ U), x ∈ V x := by
    intro x hx
    simpa only [V, dif_pos hx] using he x hx
  have hVinj : ∀ x, Set.InjOn F (V x) := by
    intro x
    by_cases hx : x ∈ U
    · simpa only [V, dif_pos hx, hFe x hx] using (e x hx).injOn
    · simp only [V, dif_neg hx, Set.injOn_empty]
  have hVnhds : ∀ x ∈ U, V x ∈ 𝓝[U] x := by
    intro x hx
    exact mem_nhdsWithin_of_mem_nhds ((hVopen x).mem_nhds (hxV x hx))
  obtain ⟨t, _htU, htc, hcover⟩ :=
    TopologicalSpace.countable_cover_nhdsWithin hVnhds
  let enum : ℕ → E := Set.enumerateCountable htc 0
  have ht_range : t ⊆ Set.range enum := by
    intro x hx
    simpa only [enum] using Set.subset_range_enumerate htc 0 hx
  have hcoverV : U ⊆ ⋃ n, V (enum n) := by
    intro x hx
    rcases Set.mem_iUnion.mp (hcover hx) with ⟨z, hz⟩
    rcases Set.mem_iUnion.mp hz with ⟨hzt, hxVz⟩
    rcases ht_range hzt with ⟨n, hn⟩
    exact Set.mem_iUnion.mpr ⟨n, hn ▸ hxVz⟩
  let W : ℕ → Set E := fun n => V (enum n)
  let P : ℕ → Set E := fun n => U ∩ disjointed W n
  refine ⟨P, ?_, ?_, ?_, ?_⟩
  · intro n
    exact hU.inter
      (MeasurableSet.disjointed
        (fun k => (hVopen (enum k)).measurableSet) n)
  · exact (disjoint_disjointed W).mono fun _ _ hij =>
      hij.mono inter_subset_right inter_subset_right
  · change (⋃ n, U ∩ disjointed W n) = U
    rw [← Set.inter_iUnion, iUnion_disjointed,
      Set.inter_eq_left]
    simpa only [W] using hcoverV
  · intro n
    exact (hVinj (enum n)).mono
      (inter_subset_right.trans (disjointed_subset W n))

attribute [-instance] Tensor0SBundle.tangentSpace_normedAddCommGroup
  Tensor0SBundle.tangentSpace_normedSpace in
omit [T2Space (TangentBundle I M)] in
theorem riemVol_mul_le_area
    [ConnectedSpace M] [PseudoEMetricSpace M]
    [IsRiemannianManifold I M] [CompleteSpace M]
    [IsContinuousRiemannianBundle E
      (fun (x : M) ↦ TangentSpace I x)]
    (g : SmoothRiemannianMetric I M)
    (hEnorm : ∀ (y : M) (w : TangentSpace I y),
      ‖w‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner y w w)))
    (x : M) {U : Set E} (hU : MeasurableSet U)
    {S : Set M} (hS : MeasurableSet S) {m : ENat}
    (hloc : IsLocalHomeomorphOn
      (fun b : E => expMapIntrinsic (I := I) g hEnorm x
        (show TangentSpace I x from b)) U)
    (hcount : ∀ y ∈ S, m ≤
      {v : E | v ∈ U ∧
        expMapIntrinsic (I := I) g hEnorm x
          (show TangentSpace I x from v) = y}.encard) :
    m.toENNReal *
        riemannianVolumeMeasure (I := I) (M := M) g S
      ≤ ∫⁻ v in U,
          ENNReal.ofReal (expJacDensity (I := I) g hEnorm x v)
        ∂(modelHaar (E := E)) := by
  classical
  let F : E → M := fun b =>
    expMapIntrinsic (I := I) g hEnorm x
      (show TangentSpace I x from b)
  change IsLocalHomeomorphOn F U at hloc
  change ∀ y ∈ S, m ≤ {v : E | v ∈ U ∧ F v = y}.encard at hcount
  obtain ⟨P, hPmeas, hPdisj, hPcover, hPinj⟩ :=
    exists_inj_parts hU hloc
  have hFcont : Continuous F :=
    (intrinsicFiber_smooth (I := I) g hEnorm x).continuous
  have hQmeas : ∀ n, MeasurableSet (F '' P n) := fun n =>
    (hPmeas n).image_of_continuousOn_injOn
      hFcont.continuousOn (hPinj n)
  have hpoint : ∀ y ∈ S,
      m.toENNReal ≤ ∑' n : ℕ, (F '' P n).indicator 1 y := by
    intro y hy
    let Fib : Set E := {v : E | v ∈ U ∧ F v = y}
    let J : Set ℕ := {n : ℕ | y ∈ F '' P n}
    have hvpart : ∀ v : Fib, ∃ n, v.1 ∈ P n := by
      intro v
      have hv : v.1 ∈ ⋃ n, P n := hPcover.symm ▸ v.2.1
      exact Set.mem_iUnion.mp hv
    let idx : Fib → ℕ := fun v => Classical.choose (hvpart v)
    have hidx : ∀ v : Fib, v.1 ∈ P (idx v) := fun v =>
      Classical.choose_spec (hvpart v)
    let emb : Fib ↪ J :=
      { toFun := fun v =>
          ⟨idx v, ⟨v.1, hidx v, v.2.2⟩⟩
        inj' := by
          intro v w hvw
          have hn : idx v = idx w := congrArg Subtype.val hvw
          apply Subtype.ext
          apply hPinj (idx v) (hidx v)
          · simpa only [hn] using hidx w
          · exact v.2.2.trans w.2.2.symm }
    have hcard : m.toENNReal ≤ J.encard.toENNReal :=
      (ENat.toENNReal_mono (hcount y hy)).trans
        (ENat.toENNReal_mono emb.encard_le)
    calc
      m.toENNReal ≤ J.encard.toENNReal := hcard
      _ = ∑' _ : J, (1 : ENNReal) :=
        (ENNReal.tsum_set_one J).symm
      _ = ∑' n : ℕ, J.indicator 1 n :=
        tsum_subtype J (fun _ : ℕ => (1 : ENNReal))
      _ = ∑' n : ℕ, (F '' P n).indicator 1 y := by
        apply tsum_congr
        intro n
        simp only [J, Set.indicator, Set.mem_setOf_eq, Pi.one_apply]
  calc
    m.toENNReal *
          riemannianVolumeMeasure (I := I) (M := M) g S =
        ∫⁻ _y in S, m.toENNReal
          ∂(riemannianVolumeMeasure (I := I) (M := M) g) :=
      (setLIntegral_const S m.toENNReal).symm
    _ ≤ ∫⁻ y in S, ∑' n : ℕ, (F '' P n).indicator 1 y
          ∂(riemannianVolumeMeasure (I := I) (M := M) g) :=
      setLIntegral_mono' hS hpoint
    _ ≤ ∫⁻ y, ∑' n : ℕ, (F '' P n).indicator 1 y
          ∂(riemannianVolumeMeasure (I := I) (M := M) g) :=
      setLIntegral_le_lintegral S _
    _ = ∑' n : ℕ,
        ∫⁻ y, (F '' P n).indicator 1 y
          ∂(riemannianVolumeMeasure (I := I) (M := M) g) := by
      simpa only using
        (lintegral_tsum
          (μ := riemannianVolumeMeasure (I := I) (M := M) g)
          (f := fun n y =>
            (F '' P n).indicator (fun _ => (1 : ENNReal)) y)
          (fun n =>
            (measurable_const.indicator (hQmeas n)).aemeasurable))
    _ = ∑' n : ℕ,
        riemannianVolumeMeasure (I := I) (M := M) g (F '' P n) := by
      apply tsum_congr
      intro n
      exact lintegral_indicator_one (hQmeas n)
    _ = ∑' n : ℕ,
        ∫⁻ v in P n,
          ENNReal.ofReal (expJacDensity (I := I) g hEnorm x v)
        ∂(modelHaar (E := E)) := by
      apply tsum_congr
      intro n
      simpa only [F] using
        riemVol_exp_image_eq (I := I) g hEnorm x
          (hPmeas n) (hPinj n)
    _ = ∫⁻ v in ⋃ n, P n,
          ENNReal.ofReal (expJacDensity (I := I) g hEnorm x v)
        ∂(modelHaar (E := E)) :=
      (lintegral_iUnion hPmeas hPdisj _).symm
    _ = ∫⁻ v in U,
          ENNReal.ofReal (expJacDensity (I := I) g hEnorm x v)
        ∂(modelHaar (E := E)) := by
      rw [hPcover]

omit [CompleteSpace E] [T2Space (TangentBundle I M)] in
attribute [-instance] Tensor0SBundle.tangentSpace_normedAddCommGroup
  Tensor0SBundle.tangentSpace_normedSpace in
theorem expJacDensity_continuous
    [PseudoEMetricSpace M] [IsRiemannianManifold I M] [CompleteSpace M]
    [IsContinuousRiemannianBundle E (fun (x : M) ↦ TangentSpace I x)]
    (g : SmoothRiemannianMetric I M)
    (hEnorm : IsMetricNorm (I := I) (M := M) g)
    (x : M) :
    Continuous (fun v : E => expJacDensity (I := I) g hEnorm x v) :=
  expJac_continuous (I := I) g hEnorm x

end DifferentialGeometry.Geometry.Riemannian.VolumeComparison
