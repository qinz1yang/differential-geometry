import DifferentialGeometry.Geometry.Comparison.Volume.SegmentDensity
import DifferentialGeometry.Analysis.Integration.Measure.JacobianImageLe
import DifferentialGeometry.Analysis.Integration.Measure.Invariance

set_option autoImplicit false
set_option linter.unusedSectionVars false

/-!
# Manifold-valued non-injective area inequality for the intrinsic exponential (L5)

**Deliverable L5** of the A0′ `VolumeComparisonInput` lane
(`HCGCompactness/C4/A0PRIME_VOLUME_PLAN.md`).  This is the missing bridge the B2
lane flagged as its frontier: a *non-injective* change-of-variables **inequality**
for `expMapIntrinsic x : E → M` into a Riemannian manifold, past the cut locus.

For a compact launch set `K ⊆ T_xM` (`≅ E`),

`riemannianVolumeMeasure g (expMapIntrinsic x '' K)`
`  ≤ ∫⁻ v in K, ofReal (curveDensity g (intrinsicGeodesic x v) (intrinsic Jacobi frame) 1) ∂modelHaar`.

## Route (POU-weighted decomposition — orchestrator design note, plan §8)

`riemannianVolumeMeasure g = Measure.sum (α ↦ (chartLocalMeasure g α).withDensity
(ofReal ∘ ρ α))` with `ρ = chartAtlasPOU`.  On the compact `K` the image is
measurable, so `Measure.sum_apply` gives an EQUALITY over the weighted summands.
Each summand is pulled back to the chart target and bounded by the weighted
Euclidean area inequality `MeasureTheory.image_lintegral_le` (L3) applied to the
chart-composed map `extChartAt α ∘ expMapIntrinsic x` with weight
`ofReal ∘ (ρ α · chartDensity g α)`; the resulting integrand is rewritten by the
density identity `exp_density_curve` (L2) to `ρ α (exp v) · curveDensity v`.
Summing over the countable POU support and collapsing `Σ_α ρ α (exp v) = 1`
(`tsum_ofReal_pou_eq_one`) leaves exactly `∫⁻ v in K, ofReal (curveDensity v)`.

No injectivity, no cut-locus restriction: the exponential is globally `C^∞`
(`intrinsicFiber_smooth`), the density identity holds for all `v`, and the
Euclidean inequality (L3) needs no injectivity.
-/

noncomputable section

open Set Function Filter Bundle Manifold MeasureTheory
open scoped Topology Manifold ContDiff ENNReal

namespace DifferentialGeometry.Geometry.Riemannian.VolumeComparison

open DifferentialGeometry.Geometry.Riemannian.Exponential
open DifferentialGeometry.Geometry.Riemannian.Variation
open DifferentialGeometry.Integral.Measure

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [InnerProductSpace ℝ E] [Module.Finite ℝ E] [FiniteDimensional ℝ E]
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
/-- The intrinsic Jacobi endpoint density along the radial geodesic in direction
`v` — the RHS integrand of the area inequality `L5`, equal to the pointwise
Riemannian Jacobian of `expMapIntrinsic x` at `v` (`exp_density_curve`). -/
private def expJacDensity
    [ConnectedSpace M] [PseudoEMetricSpace M] [IsRiemannianManifold I M] [CompleteSpace M]
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
/-- The intrinsic Jacobi endpoint density is continuous in the launch velocity.
Local consequence of the density identity `exp_density_curve` (`= chartDensity ·
|det (chart ∘ exp)|`) together with continuity of the chart density and of the
Euclidean differential of the globally-`C^∞` chart-composed exponential. -/
private theorem expJacDensity_continuous
    [ConnectedSpace M] [PseudoEMetricSpace M] [IsRiemannianManifold I M] [CompleteSpace M]
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
  -- `expJacDensity` agrees with `ψ` on the open neighbourhood where `exp v` stays in the chart.
  have hUnhds : F ⁻¹' (chartAt H y₀).source ∈ 𝓝 v₀ :=
    hFcont.continuousAt.preimage_mem_nhds ((chartAt H y₀).open_source.mem_nhds hsrc0)
  have heq : (fun v : E => expJacDensity (I := I) g hEnorm x v) =ᶠ[𝓝 v₀] ψ := by
    filter_upwards [hUnhds] with v hv
    show expJacDensity (I := I) g hEnorm x v = chartDensity g y₀ (F v) * |(fderiv ℝ φ v).det|
    exact (exp_density_curve (I := I) g hEnorm x v y₀ hv).symm
  -- `ψ` is continuous at `v₀`.
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

attribute [-instance] Tensor0SBundle.tangentSpace_normedAddCommGroup
  Tensor0SBundle.tangentSpace_normedSpace in
/-- Per-chart summand bound (the crux of L5): the `α`-summand of the POU-weighted
Riemannian volume of `expMapIntrinsic x '' K` is at most the `K`-integral of
`ρ α (exp v) · expJacDensity v` against `modelHaar`. -/
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
  -- The chart-composed exponential, made global by a piecewise definition.
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
  -- Measurability of the pieces.
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
  -- Derivative of `fα` on `Kα` (via `expChart_contDiffAt` and the eventual equality with the
  -- non-piecewise chart-composed exponential).
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
  -- The pulled-back integrand agrees with the image indicator on the chart target.
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
  -- Main chain.
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

attribute [-instance] Tensor0SBundle.tangentSpace_normedAddCommGroup
  Tensor0SBundle.tangentSpace_normedSpace in
/-- **Non-injective area inequality for the intrinsic exponential** (L5).

For a compact launch set `K ⊆ E`, the Riemannian volume of the image
`expMapIntrinsic x '' K` is at most the `modelHaar`-integral over `K` of the
intrinsic Jacobi endpoint density `expJacDensity`.  No injectivity or cut-locus
hypothesis; the density integrand is `exp_density_curve`'s value. -/
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
    expJacDensity_continuous (I := I) g hEnorm x
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
  -- the summand vanishes off the countable POU support
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
  -- POU support subset for the pointwise collapse
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

end DifferentialGeometry.Geometry.Riemannian.VolumeComparison
