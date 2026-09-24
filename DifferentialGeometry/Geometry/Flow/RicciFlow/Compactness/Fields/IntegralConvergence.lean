import DifferentialGeometry.Geometry.Flow.RicciFlow.Compactness.Fields.VolumeConvergence
import Mathlib.MeasureTheory.Integral.Lebesgue.DominatedConvergence

noncomputable section

open Filter MeasureTheory Set
open scoped ContDiff Manifold _root_.Topology

namespace DifferentialGeometry.CheegerGromovCompactness

open DifferentialGeometry.Integral.Measure

universe u uE uH

variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace Real E]
  [FiniteDimensional Real E]
variable {H : Type uH} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H}

private local instance : MeasurableSpace E := borel E
private local instance : BorelSpace E := ⟨rfl⟩

theorem FlowMetricConvergenceData.tendsto_lintegral_mul_chartDensity_mul_density
    {X : PointedFlowSeq.{u, uE, uH} (I := I)}
    {P : PointedRiemannianManifold.{u, uE, uH} (I := I)}
    {subseq : Nat → Nat}
    (Phi : PointedCGHMaps (I := I) X P subseq)
    (R : let : TopologicalSpace P.M := P.topology
      let : ChartedSpace H P.M := P.charted
      let : IsManifold I ∞ P.M := P.smooth
      SmoothRiemannianMetric I P.M)
    (bf : BumpFamily (I := I) Phi)
    (hSrc : SourceIsSigmaCompact Phi) (hTgt : TargetIsSigmaCompact Phi)
    (beta psi : Real) (co : FlowMetricConvergenceData (I := I) Phi R bf hSrc hTgt beta psi)
    (t : Real) (alpha : P.M) {B : Set E}
    (density : ∀ k, (X.term (subseq (co.φ k))).M → Real) (densityLim : P.M → Real)
    (hTime : t ∈ Icc beta psi)
    (hBChart : let : TopologicalSpace P.M := P.topology
      let : ChartedSpace H P.M := P.charted
      B ⊆ (extChartAt I alpha).target)
    (hBc : IsCompact B)
    (w : E → ENNReal)
    (hw : AEMeasurable w ((modelHaar (E := E)).restrict B))
    (hwInt : ∫⁻ z in B, w z ∂(modelHaar (E := E)) < ⊤)
    (hDensityMeas : let : TopologicalSpace P.M := P.topology
      let : ChartedSpace H P.M := P.charted
      let : IsManifold I ∞ P.M := P.smooth
      ∀ᶠ k in atTop, AEMeasurable
        (fun z : E ↦
          let : TopologicalSpace (X.term (subseq (co.φ k))).M := (X.term (subseq (co.φ k))).topology
          let : ChartedSpace H (X.term (subseq (co.φ k))).M :=
            (X.term (subseq (co.φ k))).charted
          let : IsManifold I ∞ (X.term (subseq (co.φ k))).M :=
            (X.term (subseq (co.φ k))).smooth
          ENNReal.ofReal (density k (Phi.map (co.φ k) ((extChartAt I alpha).symm z))))
        ((modelHaar (E := E)).restrict B))
    (hDensityLim : let : TopologicalSpace P.M := P.topology
      let : ChartedSpace H P.M := P.charted
      let : IsManifold I ∞ P.M := P.smooth
      ∀ᵐ z ∂((modelHaar (E := E)).restrict B), Tendsto
        (fun k ↦
          let : TopologicalSpace (X.term (subseq (co.φ k))).M := (X.term (subseq (co.φ k))).topology
          let : ChartedSpace H (X.term (subseq (co.φ k))).M :=
            (X.term (subseq (co.φ k))).charted
          let : IsManifold I ∞ (X.term (subseq (co.φ k))).M :=
            (X.term (subseq (co.φ k))).smooth
          density k (Phi.map (co.φ k) ((extChartAt I alpha).symm z)))
        atTop (nhds (densityLim ((extChartAt I alpha).symm z))))
    (Cdensity : NNReal)
    (hDensityBd : let : TopologicalSpace P.M := P.topology
      let : ChartedSpace H P.M := P.charted
      ∀ᶠ k in atTop, ∀ᵐ z ∂((modelHaar (E := E)).restrict B),
        let : TopologicalSpace (X.term (subseq (co.φ k))).M := (X.term (subseq (co.φ k))).topology
        let : ChartedSpace H (X.term (subseq (co.φ k))).M :=
          (X.term (subseq (co.φ k))).charted
        let : IsManifold I ∞ (X.term (subseq (co.φ k))).M :=
          (X.term (subseq (co.φ k))).smooth
        ENNReal.ofReal (density k (Phi.map (co.φ k) ((extChartAt I alpha).symm z))) ≤
            (Cdensity : ENNReal)) :
    let : TopologicalSpace P.M := P.topology
    let : ChartedSpace H P.M := P.charted
    let : IsManifold I ∞ P.M := P.smooth
    Tendsto
      (fun k ↦ ∫⁻ z in B,
        w z * (ENNReal.ofReal (chartDensity (I := I)
          (gSeqExt (I := I) Phi R bf hSrc hTgt (co.φ k) t) alpha
          ((extChartAt I alpha).symm z)) *
        (let : TopologicalSpace (X.term (subseq (co.φ k))).M := (X.term (subseq (co.φ k))).topology
         let : ChartedSpace H (X.term (subseq (co.φ k))).M :=
            (X.term (subseq (co.φ k))).charted
         let : IsManifold I ∞ (X.term (subseq (co.φ k))).M :=
            (X.term (subseq (co.φ k))).smooth
         ENNReal.ofReal (density k (Phi.map (co.φ k) ((extChartAt I alpha).symm z)))))
        ∂(modelHaar (E := E)))
      atTop
      (nhds (∫⁻ z in B,
        w z * (ENNReal.ofReal (chartDensity (I := I) (co.gInf t) alpha
          ((extChartAt I alpha).symm z)) *
        ENNReal.ofReal (densityLim ((extChartAt I alpha).symm z)))
        ∂(modelHaar (E := E)))) := by
  let : TopologicalSpace P.M := P.topology
  let : ChartedSpace H P.M := P.charted
  let : IsManifold I ∞ P.M := P.smooth
  let vol : Nat → E → Real := fun k z ↦ chartDensity (I := I)
    (gSeqExt (I := I) Phi R bf hSrc hTgt (co.φ k) t) alpha
    ((extChartAt I alpha).symm z)
  let volLim : E → Real := fun z ↦ chartDensity (I := I)
    (co.gInf t) alpha ((extChartAt I alpha).symm z)
  let red : Nat → E → Real := fun k z ↦
    let : TopologicalSpace (X.term (subseq (co.φ k))).M := (X.term (subseq (co.φ k))).topology
    let : ChartedSpace H (X.term (subseq (co.φ k))).M :=
      (X.term (subseq (co.φ k))).charted
    let : IsManifold I ∞ (X.term (subseq (co.φ k))).M :=
      (X.term (subseq (co.φ k))).smooth
    density k (Phi.map (co.φ k) ((extChartAt I alpha).symm z))
  let redLim : E → Real := fun z ↦
    densityLim ((extChartAt I alpha).symm z)
  have hVolU := FlowMetricConvergenceData.tendstoUniformlyOn_chartDensity
    Phi R bf hSrc hTgt beta psi co alpha hBChart hBc hTime
  have hVolCont : ContinuousOn volLim B :=
    (chartDensityOnE_contDiffOn (co.gInf t) alpha).continuousOn.mono hBChart
  obtain ⟨Mvol, hMvol⟩ := hBc.bddAbove_image hVolCont
  let Cvol : NNReal := Real.toNNReal (max Mvol 0 + 1)
  have hNear := (Metric.tendstoUniformlyOn_iff.1 hVolU) 1 zero_lt_one
  have hVolBd : ∀ᶠ k in atTop, ∀ᵐ z ∂((modelHaar (E := E)).restrict B),
      ENNReal.ofReal (vol k z) ≤ (Cvol : ENNReal) := by
    filter_upwards [hNear] with k hk
    filter_upwards [ae_restrict_mem hBc.measurableSet] with z hz
    have hdist : |vol k z - volLim z| < 1 := by
      simpa only [Real.dist_eq, abs_sub_comm, vol, volLim] using! hk z hz
    have hseq : vol k z ≤ max Mvol 0 + 1 := by
      linarith [le_abs_self (vol k z - volLim z), hMvol ⟨z, hz, rfl⟩, le_max_left Mvol (0 : Real)]
    change ENNReal.ofReal (vol k z) ≤ ENNReal.ofReal (max Mvol 0 + 1)
    exact ENNReal.ofReal_le_ofReal hseq
  have hVolLim : ∀ z ∈ B, Tendsto (fun k ↦ vol k z) atTop (nhds (volLim z)) := by
    intro z hz
    exact hVolU.tendsto_at hz
  have hVolMeas (k : Nat) : AEMeasurable
      (fun z ↦ ENNReal.ofReal (vol k z)) ((modelHaar (E := E)).restrict B) := by
    have hc := ((chartDensityOnE_contDiffOn
      (gSeqExt (I := I) Phi R bf hSrc hTgt (co.φ k) t) alpha).continuousOn.mono hBChart)
    exact ENNReal.measurable_ofReal.comp_aemeasurable (hc.aemeasurable hBc.measurableSet)
  have hDensityMeas' : ∀ᶠ k in atTop, AEMeasurable
      (fun z ↦ ENNReal.ofReal (red k z)) ((modelHaar (E := E)).restrict B) := by
    filter_upwards [hDensityMeas] with k hk
    simpa only [red] using hk
  have hDensityLim' : ∀ᵐ z ∂((modelHaar (E := E)).restrict B),
      Tendsto (fun k ↦ red k z) atTop (nhds (redLim z)) := by
    simpa only [red, redLim] using hDensityLim
  let μ : Measure E := (modelHaar (E := E)).restrict B
  let F : Nat → E → ENNReal := fun k z =>
    w z * (ENNReal.ofReal (vol k z) * ENNReal.ofReal (red k z))
  let f : E → ENNReal := fun z =>
    w z * (ENNReal.ofReal (volLim z) * ENNReal.ofReal (redLim z))
  let C : E → ENNReal := fun z => ((Cvol : ENNReal) * (Cdensity : ENNReal)) * w z
  have hFMeas : ∀ᶠ k in atTop, AEMeasurable (F k) μ := by
    filter_upwards [hDensityMeas'] with k hk
    convert hw.mul ((hVolMeas k).mul hk) using 1 <;> rfl
  have hBound : ∀ᶠ k in atTop, F k ≤ᵐ[μ] C := by
    filter_upwards [hVolBd, hDensityBd] with k hkVol hkRed
    filter_upwards [hkVol, hkRed] with z hzVol hzRed
    exact (mul_le_mul' (le_refl (w z)) (mul_le_mul' hzVol hzRed)).trans_eq (mul_comm _ _)
  have hFin : ∫⁻ z, C z ∂μ ≠ ⊤ := by
    rw [lintegral_const_mul'' _ hw]
    exact ENNReal.mul_ne_top (ENNReal.mul_ne_top (by simp) (by simp)) hwInt.ne
  have hLim : ∀ᵐ z ∂μ, Tendsto (fun k => F k z) atTop (nhds (f z)) := by
    filter_upwards [ae_restrict_mem hBc.measurableSet, hDensityLim',
      ae_lt_top' hw hwInt.ne] with z hz hr hwz
    have hp : Tendsto
        (fun k => ENNReal.ofReal (vol k z) * ENNReal.ofReal (red k z)) atTop
        (nhds (ENNReal.ofReal (volLim z) * ENNReal.ofReal (redLim z))) := by
      apply ENNReal.Tendsto.mul
      · exact (ENNReal.continuous_ofReal.tendsto _).comp (hVolLim z hz)
      · exact Or.inr ENNReal.ofReal_ne_top
      · exact (ENNReal.continuous_ofReal.tendsto _).comp hr
      · exact Or.inr ENNReal.ofReal_ne_top
    exact ENNReal.Tendsto.mul tendsto_const_nhds (Or.inr
      (ENNReal.mul_ne_top ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top)) hp (Or.inr hwz.ne)
  simpa only [F, f, μ, vol, volLim, red, redLim] using
    (tendsto_lintegral_filter_of_dominated_convergence' C hFMeas hBound hFin hLim)


end DifferentialGeometry.CheegerGromovCompactness

end


noncomputable section

open Set Filter MeasureTheory
open scoped Manifold ContDiff _root_.Topology

namespace DifferentialGeometry.CheegerGromovCompactness

open Integral.Measure

universe u uE uH

section Chart

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [T2Space M] [SigmaCompactSpace M]

private local instance : MeasurableSpace E := borel E
private local instance : BorelSpace E := ⟨rfl⟩

private theorem chart_weighted_integral (g : SmoothRiemannianMetric I M) (alpha : M)
    (F : M → ENNReal) (w : E → ENNReal) {B : Set E}
    (hB : MeasurableSet B) (hBt : B ⊆ (extChartAt I alpha).target) :
    ∫⁻ y in (extChartAt I alpha).symm '' B,
      w (extChartAt I alpha y) * F y ∂riemannianVolumeMeasure (I := I) (M := M) g =
      ∫⁻ z in B, w z * (ENNReal.ofReal (chartDensity g alpha
        ((extChartAt I alpha).symm z)) * F ((extChartAt I alpha).symm z))
        ∂(modelHaar (E := E)) := by
  have h := riemVol_param_lint g (PartialDiffeomorph.extChartAt I 1 alpha).symm
    (fun y => w (extChartAt I alpha y) * F y) hB hBt
  refine h.trans (setLIntegral_congr_fun hB fun z hz => ?_)
  change ENNReal.ofReal (paramDensity g (PartialDiffeomorph.extChartAt I 1 alpha).symm z) *
    (w (extChartAt I alpha ((extChartAt I alpha).symm z)) *
      F ((extChartAt I alpha).symm z)) = _
  rw [paramDensity_extChartAt_symm g alpha (hBt hz), (extChartAt I alpha).right_inv (hBt hz)]
  ac_rfl

end Chart

section Source

variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
variable {H : Type uH} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
variable {X : PointedFlowSeq.{u, uE, uH} (I := I)}
variable {P : PointedRiemannianManifold.{u, uE, uH} (I := I)} {subseq : ℕ → ℕ}

private local instance : MeasurableSpace E := borel E
private local instance : BorelSpace E := ⟨rfl⟩

private theorem eventually_source_weighted_integral
    (Phi : PointedCGHMaps (I := I) X P subseq)
    (R : let : TopologicalSpace P.M := P.topology
      let : ChartedSpace H P.M := P.charted
      let : IsManifold I ∞ P.M := P.smooth
      SmoothRiemannianMetric I P.M)
    (bf : BumpFamily (I := I) Phi) (hSrc : SourceIsSigmaCompact Phi)
    (hTgt : TargetIsSigmaCompact Phi) (φ : ℕ → ℕ) (hφ : StrictMono φ)
    (t : ℝ) (alpha : P.M) {B : Set E} (hBc : IsCompact B)
    (hBt : let : TopologicalSpace P.M := P.topology
      let : ChartedSpace H P.M := P.charted
      B ⊆ (extChartAt I alpha).target)
    (w : E → ENNReal) (F : ∀ k, (X.term (subseq (φ k))).M → ENNReal) :
    let : TopologicalSpace P.M := P.topology
    let : ChartedSpace H P.M := P.charted
    let : IsManifold I ∞ P.M := P.smooth
    ∀ᶠ k in atTop,
      let : TopologicalSpace (X.term (subseq (φ k))).M := (X.term (subseq (φ k))).topology
      let : ChartedSpace H (X.term (subseq (φ k))).M := (X.term (subseq (φ k))).charted
      let : IsManifold I ∞ (X.term (subseq (φ k))).M := (X.term (subseq (φ k))).smooth
      let : T2Space (X.term (subseq (φ k))).M := (X.term (subseq (φ k))).t2
      let : SigmaCompactSpace (X.term (subseq (φ k))).M := (X.term (subseq (φ k))).sigmaCompact
      ∫⁻ y in (Phi.chartParametrization (φ k) alpha) '' B,
        w ((Phi.chartParametrization (φ k) alpha).symm y) * F k y
          ∂riemannianVolumeMeasure (I := I) (M := (X.term (subseq (φ k))).M)
            ((X.term (subseq (φ k))).S.base.metric t) =
        ∫⁻ z in B, w z * (ENNReal.ofReal (chartDensity
          (gSeqExt Phi R bf hSrc hTgt (φ k) t) alpha ((extChartAt I alpha).symm z)) *
          F k (Phi.map (φ k) ((extChartAt I alpha).symm z))) ∂(modelHaar (E := E)) := by
  let : TopologicalSpace P.M := P.topology
  let : ChartedSpace H P.M := P.charted
  let : IsManifold I ∞ P.M := P.smooth
  let : T2Space P.M := P.t2
  let : SigmaCompactSpace P.M := P.sigmaCompact
  have hK : IsCompact ((extChartAt I alpha).symm '' B) :=
    hBc.image_of_continuousOn ((continuousOn_extChartAt_symm (I := I) alpha).mono hBt)
  obtain ⟨k₀, hk₀⟩ := bf.grow_cover _ hK
  filter_upwards [eventually_ge_atTop k₀] with k hk
  let : TopologicalSpace (X.term (subseq (φ k))).M := (X.term (subseq (φ k))).topology
  let : ChartedSpace H (X.term (subseq (φ k))).M := (X.term (subseq (φ k))).charted
  let : IsManifold I ∞ (X.term (subseq (φ k))).M := (X.term (subseq (φ k))).smooth
  let : T2Space (X.term (subseq (φ k))).M := (X.term (subseq (φ k))).t2
  let : SigmaCompactSpace (X.term (subseq (φ k))).M := (X.term (subseq (φ k))).sigmaCompact
  have hGrow : ∀ z ∈ B, (extChartAt I alpha).symm z ∈ bf.grow (φ k) :=
    fun z hz => hk₀ (φ k) (hk.trans (hφ.id_le k)) ⟨z, hz, rfl⟩
  have hSource : B ⊆ (Phi.chartParametrization (φ k) alpha).source := by
    intro z hz
    change z ∈ (extChartAt I alpha).target ∩
      (extChartAt I alpha).symm ⁻¹' Phi.source (φ k)
    exact ⟨hBt hz, bf.grow_subset (φ k) (hGrow z hz)⟩
  obtain ⟨W, _, hGrowW, hOne⟩ := bf.chi_one (φ k)
  have h := riemVol_param_lint ((X.term (subseq (φ k))).S.base.metric t)
    (Phi.chartParametrization (φ k) alpha)
    (fun y => w ((Phi.chartParametrization (φ k) alpha).symm y) * F k y)
    hBc.measurableSet hSource
  refine h.trans (setLIntegral_congr_fun hBc.measurableSet fun z hz => ?_)
  have hleft : (Phi.chartParametrization (φ k) alpha).symm.toPartialEquiv
      ((Phi.chartParametrization (φ k) alpha).toPartialEquiv z) = z :=
    (Phi.chartParametrization (φ k) alpha).left_inv (hSource hz)
  rw [hleft]
  rw [paramDensity_chartParametrization Phi R bf hSrc hTgt (φ k) t alpha
    (hSource hz) (hOne _ (hGrowW (hGrow z hz)))]
  change _ * (w z * F k (Phi.map (φ k) ((extChartAt I alpha).symm z))) = _
  ac_rfl

end Source


variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
variable {H : Type uH} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]

private local instance : MeasurableSpace E := borel E
private local instance : BorelSpace E := ⟨rfl⟩

theorem FlowMetricConvergenceData.tendsto_lintegral_mul_density_chartParametrization
    {X : PointedFlowSeq.{u, uE, uH} (I := I)}
    {P : PointedRiemannianManifold.{u, uE, uH} (I := I)}
    {subseq : Nat → Nat}
    (Phi : PointedCGHMaps (I := I) X P subseq)
    (R : let : TopologicalSpace P.M := P.topology
      let : ChartedSpace H P.M := P.charted
      let : IsManifold I ∞ P.M := P.smooth
      SmoothRiemannianMetric I P.M)
    (bf : BumpFamily (I := I) Phi)
    (hSrc : SourceIsSigmaCompact Phi) (hTgt : TargetIsSigmaCompact Phi)
    (beta psi : Real) (co : FlowMetricConvergenceData (I := I) Phi R bf hSrc hTgt beta psi)
    (t : Real) (alpha : P.M) {B : Set E}
    (density : ∀ k, (X.term (subseq (co.φ k))).M → Real) (densityLim : P.M → Real)
    (hTime : t ∈ Icc beta psi)
    (hBChart : let : TopologicalSpace P.M := P.topology
      let : ChartedSpace H P.M := P.charted
      B ⊆ (extChartAt I alpha).target)
    (hBc : IsCompact B)
    (w : E → ENNReal)
    (hw : AEMeasurable w ((modelHaar (E := E)).restrict B))
    (hwInt : ∫⁻ z in B, w z ∂(modelHaar (E := E)) < ⊤)
    (hDensityMeas : let : TopologicalSpace P.M := P.topology
      let : ChartedSpace H P.M := P.charted
      let : IsManifold I ∞ P.M := P.smooth
      ∀ᶠ k in atTop, AEMeasurable
        (fun z : E ↦
          let : TopologicalSpace (X.term (subseq (co.φ k))).M := (X.term (subseq (co.φ k))).topology
          let : ChartedSpace H (X.term (subseq (co.φ k))).M :=
            (X.term (subseq (co.φ k))).charted
          let : IsManifold I ∞ (X.term (subseq (co.φ k))).M :=
            (X.term (subseq (co.φ k))).smooth
          ENNReal.ofReal (density k (Phi.map (co.φ k) ((extChartAt I alpha).symm z))))
        ((modelHaar (E := E)).restrict B))
    (hDensityLim : let : TopologicalSpace P.M := P.topology
      let : ChartedSpace H P.M := P.charted
      let : IsManifold I ∞ P.M := P.smooth
      ∀ᵐ z ∂((modelHaar (E := E)).restrict B), Tendsto
        (fun k ↦
          let : TopologicalSpace (X.term (subseq (co.φ k))).M := (X.term (subseq (co.φ k))).topology
          let : ChartedSpace H (X.term (subseq (co.φ k))).M :=
            (X.term (subseq (co.φ k))).charted
          let : IsManifold I ∞ (X.term (subseq (co.φ k))).M :=
            (X.term (subseq (co.φ k))).smooth
          density k (Phi.map (co.φ k) ((extChartAt I alpha).symm z)))
        atTop (nhds (densityLim ((extChartAt I alpha).symm z))))
    (Cdensity : NNReal)
    (hDensityBd : let : TopologicalSpace P.M := P.topology
      let : ChartedSpace H P.M := P.charted
      ∀ᶠ k in atTop, ∀ᵐ z ∂((modelHaar (E := E)).restrict B),
        let : TopologicalSpace (X.term (subseq (co.φ k))).M := (X.term (subseq (co.φ k))).topology
        let : ChartedSpace H (X.term (subseq (co.φ k))).M :=
          (X.term (subseq (co.φ k))).charted
        let : IsManifold I ∞ (X.term (subseq (co.φ k))).M :=
          (X.term (subseq (co.φ k))).smooth
        ENNReal.ofReal (density k (Phi.map (co.φ k) ((extChartAt I alpha).symm z))) ≤
            (Cdensity : ENNReal)) :
    let : TopologicalSpace P.M := P.topology
    let : ChartedSpace H P.M := P.charted
    let : IsManifold I ∞ P.M := P.smooth
    let : T2Space P.M := P.t2
    let : SigmaCompactSpace P.M := P.sigmaCompact
    Tendsto
      (fun k =>
        let : TopologicalSpace (X.term (subseq (co.φ k))).M := (X.term (subseq (co.φ k))).topology
        let : ChartedSpace H (X.term (subseq (co.φ k))).M := (X.term (subseq (co.φ k))).charted
        let : IsManifold I ∞ (X.term (subseq (co.φ k))).M := (X.term (subseq (co.φ k))).smooth
        let : T2Space (X.term (subseq (co.φ k))).M := (X.term (subseq (co.φ k))).t2
        let : SigmaCompactSpace (X.term (subseq (co.φ k))).M :=
          (X.term (subseq (co.φ k))).sigmaCompact
        ∫⁻ y in (Phi.chartParametrization (co.φ k) alpha) '' B,
          w ((Phi.chartParametrization (co.φ k) alpha).symm y) *
            ENNReal.ofReal (density k y)
            ∂riemannianVolumeMeasure (I := I) (M := (X.term (subseq (co.φ k))).M)
              ((X.term (subseq (co.φ k))).S.base.metric t))
      atTop (nhds (∫⁻ y in (extChartAt I alpha).symm '' B,
        w (extChartAt I alpha y) * ENNReal.ofReal (densityLim y)
          ∂riemannianVolumeMeasure (I := I) (M := P.M) (co.gInf t))) := by
  let : TopologicalSpace P.M := P.topology
  let : ChartedSpace H P.M := P.charted
  let : IsManifold I ∞ P.M := P.smooth
  let : T2Space P.M := P.t2
  let : SigmaCompactSpace P.M := P.sigmaCompact
  have hCommon := co.tendsto_lintegral_mul_chartDensity_mul_density Phi R bf hSrc hTgt
    beta psi t alpha density densityLim hTime hBChart hBc w hw hwInt
    hDensityMeas hDensityLim Cdensity hDensityBd
  let F : ∀ k, (X.term (subseq (co.φ k))).M → ENNReal := fun k =>
    let : TopologicalSpace (X.term (subseq (co.φ k))).M := (X.term (subseq (co.φ k))).topology
    let : ChartedSpace H (X.term (subseq (co.φ k))).M := (X.term (subseq (co.φ k))).charted
    let : IsManifold I ∞ (X.term (subseq (co.φ k))).M := (X.term (subseq (co.φ k))).smooth
    fun y => ENNReal.ofReal (density k y)
  have hTerm := eventually_source_weighted_integral Phi R bf hSrc hTgt
    co.φ co.strictMono t alpha hBc hBChart w F
  let gLim : SmoothRiemannianMetric I P.M := co.gInf t
  have hLimit := chart_weighted_integral gLim alpha
    (fun y => ENNReal.ofReal (densityLim y)) w hBc.measurableSet hBChart
  have hResult := Filter.Tendsto.congr' (Filter.EventuallyEq.symm hTerm) hCommon
  convert hResult using 1
  exact congrArg nhds hLimit


end DifferentialGeometry.CheegerGromovCompactness

end
