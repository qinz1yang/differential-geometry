import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.LGeometry.ReducedVolume.IntegralConvergence

noncomputable section

open Set Filter MeasureTheory
open scoped Manifold ContDiff Topology

namespace DifferentialGeometry.CheegerGromovCompactness

open Integral.Measure PDE.RicciFlow.Perelman

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

theorem FlowMetricConvergenceData.tendsto_lintegral_mul_redDensity_chartParametrization
    {X : PointedFlowSeq.{u, uE, uH} (I := I)}
    {L : PointedFlowData.{u, uE, uH} (I := I) X.D}
    {subseq : Nat → Nat}
    (Phi : PointedCGHMaps (I := I) X (L.atTime 0) subseq)
    (R : let : TopologicalSpace (L.atTime 0).M := (L.atTime 0).topology
      let : ChartedSpace H (L.atTime 0).M := (L.atTime 0).charted
      let : IsManifold I ∞ (L.atTime 0).M := (L.atTime 0).smooth
      SmoothRiemannianMetric I (L.atTime 0).M)
    (bf : BumpFamily (I := I) Phi) (hSrc : SourceIsSigmaCompact Phi) (hTgt : TargetIsSigmaCompact Phi)
    (beta psi : Real) (co : FlowMetricConvergenceData (I := I) Phi R bf hSrc hTgt beta psi)
    (T tau : Real) (x alpha : L.M) {B : Set E}
    (hTime : T - tau ∈ Icc beta psi)
    (hBChart : let : TopologicalSpace L.M := L.topology
      let : ChartedSpace H L.M := L.charted
      B ⊆ (extChartAt I alpha).target)
    (hBc : IsCompact B)
    (w : E → ENNReal)
    (hw : AEMeasurable w ((modelHaar (E := E)).restrict B))
    (hwInt : ∫⁻ z in B, w z ∂(modelHaar (E := E)) < ⊤)
    (hRedMeas : let : TopologicalSpace L.M := L.topology
      let : ChartedSpace H L.M := L.charted
      let : IsManifold I ∞ L.M := L.smooth
      ∀ᶠ k in atTop, AEMeasurable
        (fun z : E ↦
          let : TopologicalSpace (X.term (subseq (co.φ k))).M := (X.term (subseq (co.φ k))).topology
          let : ChartedSpace H (X.term (subseq (co.φ k))).M :=
            (X.term (subseq (co.φ k))).charted
          let : IsManifold I ∞ (X.term (subseq (co.φ k))).M :=
            (X.term (subseq (co.φ k))).smooth
          ENNReal.ofReal (redDensity (X.term (subseq (co.φ k))).S T
            (Phi.map (co.φ k) x)
            (Phi.map (co.φ k) ((extChartAt I alpha).symm z)) tau))
        ((modelHaar (E := E)).restrict B))
    (hRedLim : let : TopologicalSpace L.M := L.topology
      let : ChartedSpace H L.M := L.charted
      let : IsManifold I ∞ L.M := L.smooth
      ∀ᵐ z ∂((modelHaar (E := E)).restrict B), Tendsto
        (fun k ↦
          let : TopologicalSpace (X.term (subseq (co.φ k))).M := (X.term (subseq (co.φ k))).topology
          let : ChartedSpace H (X.term (subseq (co.φ k))).M :=
            (X.term (subseq (co.φ k))).charted
          let : IsManifold I ∞ (X.term (subseq (co.φ k))).M :=
            (X.term (subseq (co.φ k))).smooth
          redDensity (X.term (subseq (co.φ k))).S T
            (Phi.map (co.φ k) x)
            (Phi.map (co.φ k) ((extChartAt I alpha).symm z)) tau)
        atTop (nhds (redDensity L.S T x ((extChartAt I alpha).symm z) tau)))
    (Cred : NNReal)
    (hRedBd : let : TopologicalSpace L.M := L.topology
      let : ChartedSpace H L.M := L.charted
      ∀ᶠ k in atTop, ∀ᵐ z ∂((modelHaar (E := E)).restrict B),
        let : TopologicalSpace (X.term (subseq (co.φ k))).M := (X.term (subseq (co.φ k))).topology
        let : ChartedSpace H (X.term (subseq (co.φ k))).M :=
          (X.term (subseq (co.φ k))).charted
        let : IsManifold I ∞ (X.term (subseq (co.φ k))).M :=
          (X.term (subseq (co.φ k))).smooth
        ENNReal.ofReal (redDensity (X.term (subseq (co.φ k))).S T
          (Phi.map (co.φ k) x)
          (Phi.map (co.φ k) ((extChartAt I alpha).symm z)) tau) ≤
            (Cred : ENNReal)) :
    let : TopologicalSpace (L.atTime 0).M := (L.atTime 0).topology
    let : ChartedSpace H (L.atTime 0).M := (L.atTime 0).charted
    let : IsManifold I ∞ (L.atTime 0).M := (L.atTime 0).smooth
    let : TopologicalSpace L.M := L.topology
    let : ChartedSpace H L.M := L.charted
    let : IsManifold I ∞ L.M := L.smooth
    let : T2Space L.M := L.t2
    let : SigmaCompactSpace L.M := L.sigmaCompact
    Tendsto
      (fun k =>
        let : TopologicalSpace (X.term (subseq (co.φ k))).M := (X.term (subseq (co.φ k))).topology
        let : ChartedSpace H (X.term (subseq (co.φ k))).M := (X.term (subseq (co.φ k))).charted
        let : IsManifold I ∞ (X.term (subseq (co.φ k))).M := (X.term (subseq (co.φ k))).smooth
        let : T2Space (X.term (subseq (co.φ k))).M := (X.term (subseq (co.φ k))).t2
        let : SigmaCompactSpace (X.term (subseq (co.φ k))).M := (X.term (subseq (co.φ k))).sigmaCompact
        ∫⁻ y in (Phi.chartParametrization (co.φ k) alpha) '' B,
          w ((Phi.chartParametrization (co.φ k) alpha).symm y) *
            ENNReal.ofReal (redDensity (X.term (subseq (co.φ k))).S T (Phi.map (co.φ k) x) y tau)
            ∂riemannianVolumeMeasure (I := I) (M := (X.term (subseq (co.φ k))).M)
              ((X.term (subseq (co.φ k))).S.base.metric (T - tau)))
      atTop (nhds (∫⁻ y in (extChartAt I alpha).symm '' B,
        w (extChartAt I alpha y) * ENNReal.ofReal (redDensity L.S T x y tau)
          ∂riemannianVolumeMeasure (I := I) (M := L.M) (co.gInf (T - tau)))) := by
  let : TopologicalSpace (L.atTime 0).M := (L.atTime 0).topology
  let : ChartedSpace H (L.atTime 0).M := (L.atTime 0).charted
  let : IsManifold I ∞ (L.atTime 0).M := (L.atTime 0).smooth
  let : TopologicalSpace L.M := L.topology
  let : ChartedSpace H L.M := L.charted
  let : IsManifold I ∞ L.M := L.smooth
  let : T2Space L.M := L.t2
  let : SigmaCompactSpace L.M := L.sigmaCompact
  have hCommon := co.tendsto_lintegral_mul_chartDensity_mul_redDensity Phi R bf hSrc hTgt
    beta psi T tau x alpha hTime hBChart hBc w hw hwInt hRedMeas hRedLim Cred hRedBd
  let F : ∀ k, (X.term (subseq (co.φ k))).M → ENNReal := fun k =>
    let : TopologicalSpace (X.term (subseq (co.φ k))).M := (X.term (subseq (co.φ k))).topology
    let : ChartedSpace H (X.term (subseq (co.φ k))).M := (X.term (subseq (co.φ k))).charted
    let : IsManifold I ∞ (X.term (subseq (co.φ k))).M := (X.term (subseq (co.φ k))).smooth
    fun y => ENNReal.ofReal (redDensity (X.term (subseq (co.φ k))).S T (Phi.map (co.φ k) x) y tau)
  have hTerm := eventually_source_weighted_integral Phi R bf hSrc hTgt
    co.φ co.strictMono (T - tau) alpha hBc hBChart w F
  let gLim : SmoothRiemannianMetric I L.M := co.gInf (T - tau)
  have hLimit := chart_weighted_integral gLim alpha
    (fun y => ENNReal.ofReal (redDensity L.S T x y tau)) w hBc.measurableSet hBChart
  have hResult := Filter.Tendsto.congr' (Filter.EventuallyEq.symm hTerm) hCommon
  convert hResult using 1
  exact congrArg nhds hLimit

theorem FlowMetricConvergenceData.lintegral_mul_redDensity_lt_top
    {X : PointedFlowSeq.{u, uE, uH} (I := I)}
    {L : PointedFlowData.{u, uE, uH} (I := I) X.D}
    {subseq : Nat → Nat}
    (Phi : PointedCGHMaps (I := I) X (L.atTime 0) subseq)
    (R : let : TopologicalSpace (L.atTime 0).M := (L.atTime 0).topology
      let : ChartedSpace H (L.atTime 0).M := (L.atTime 0).charted
      let : IsManifold I ∞ (L.atTime 0).M := (L.atTime 0).smooth
      SmoothRiemannianMetric I (L.atTime 0).M)
    (bf : BumpFamily (I := I) Phi) (hSrc : SourceIsSigmaCompact Phi) (hTgt : TargetIsSigmaCompact Phi)
    (beta psi : Real) (co : FlowMetricConvergenceData (I := I) Phi R bf hSrc hTgt beta psi)
    (T tau : Real) (x alpha : L.M) {B : Set E}
    (hBChart : let : TopologicalSpace L.M := L.topology
      let : ChartedSpace H L.M := L.charted
      B ⊆ (extChartAt I alpha).target)
    (hBc : IsCompact B)
    (w : E → ENNReal)
    (hwInt : ∫⁻ z in B, w z ∂(modelHaar (E := E)) < ⊤)
    (hRedLim : let : TopologicalSpace L.M := L.topology
      let : ChartedSpace H L.M := L.charted
      let : IsManifold I ∞ L.M := L.smooth
      ∀ᵐ z ∂((modelHaar (E := E)).restrict B), Tendsto
        (fun k ↦
          let : TopologicalSpace (X.term (subseq (co.φ k))).M := (X.term (subseq (co.φ k))).topology
          let : ChartedSpace H (X.term (subseq (co.φ k))).M :=
            (X.term (subseq (co.φ k))).charted
          let : IsManifold I ∞ (X.term (subseq (co.φ k))).M :=
            (X.term (subseq (co.φ k))).smooth
          redDensity (X.term (subseq (co.φ k))).S T
            (Phi.map (co.φ k) x)
            (Phi.map (co.φ k) ((extChartAt I alpha).symm z)) tau)
        atTop (nhds (redDensity L.S T x ((extChartAt I alpha).symm z) tau)))
    (Cred : NNReal)
    (hRedBd : let : TopologicalSpace L.M := L.topology
      let : ChartedSpace H L.M := L.charted
      ∀ᶠ k in atTop, ∀ᵐ z ∂((modelHaar (E := E)).restrict B),
        let : TopologicalSpace (X.term (subseq (co.φ k))).M := (X.term (subseq (co.φ k))).topology
        let : ChartedSpace H (X.term (subseq (co.φ k))).M :=
          (X.term (subseq (co.φ k))).charted
        let : IsManifold I ∞ (X.term (subseq (co.φ k))).M :=
          (X.term (subseq (co.φ k))).smooth
        ENNReal.ofReal (redDensity (X.term (subseq (co.φ k))).S T
          (Phi.map (co.φ k) x)
          (Phi.map (co.φ k) ((extChartAt I alpha).symm z)) tau) ≤
            (Cred : ENNReal)) :
    let : TopologicalSpace (L.atTime 0).M := (L.atTime 0).topology
    let : ChartedSpace H (L.atTime 0).M := (L.atTime 0).charted
    let : IsManifold I ∞ (L.atTime 0).M := (L.atTime 0).smooth
    let : TopologicalSpace L.M := L.topology
    let : ChartedSpace H L.M := L.charted
    let : IsManifold I ∞ L.M := L.smooth
    let : T2Space L.M := L.t2
    let : SigmaCompactSpace L.M := L.sigmaCompact
    (∫⁻ y in (extChartAt I alpha).symm '' B,
      w (extChartAt I alpha y) * ENNReal.ofReal (redDensity L.S T x y tau)
        ∂riemannianVolumeMeasure (I := I) (M := L.M) (co.gInf (T - tau))) < ⊤ := by
  let : TopologicalSpace (L.atTime 0).M := (L.atTime 0).topology
  let : ChartedSpace H (L.atTime 0).M := (L.atTime 0).charted
  let : IsManifold I ∞ (L.atTime 0).M := (L.atTime 0).smooth
  let : TopologicalSpace L.M := L.topology
  let : ChartedSpace H L.M := L.charted
  let : IsManifold I ∞ L.M := L.smooth
  let : T2Space L.M := L.t2
  let : SigmaCompactSpace L.M := L.sigmaCompact
  let μ : Measure E := (modelHaar (E := E)).restrict B
  let r : ℕ → E → ENNReal := fun k z =>
    let : TopologicalSpace (X.term (subseq (co.φ k))).M := (X.term (subseq (co.φ k))).topology
    let : ChartedSpace H (X.term (subseq (co.φ k))).M := (X.term (subseq (co.φ k))).charted
    let : IsManifold I ∞ (X.term (subseq (co.φ k))).M := (X.term (subseq (co.φ k))).smooth
    ENNReal.ofReal (redDensity (X.term (subseq (co.φ k))).S T (Phi.map (co.φ k) x)
      (Phi.map (co.φ k) ((extChartAt I alpha).symm z)) tau)
  let rInf : E → ENNReal := fun z =>
    ENNReal.ofReal (redDensity L.S T x ((extChartAt I alpha).symm z) tau)
  have hRBd : ∀ᶠ k in atTop, ∀ᵐ z ∂μ, r k z ≤ (Cred : ENNReal) := hRedBd
  have hRLim : ∀ᵐ z ∂μ, Tendsto (fun k => r k z) atTop (nhds (rInf z)) := by
    filter_upwards [hRedLim] with z hz
    exact (ENNReal.continuous_ofReal.tendsto _).comp hz
  have hRInf : ∀ᵐ z ∂μ, rInf z ≤ (Cred : ENNReal) := by
    obtain ⟨N, hN⟩ := eventually_atTop.1 hRBd
    have hAll : ∀ᵐ z ∂μ, ∀ n : ℕ, r (n + N) z ≤ (Cred : ENNReal) :=
      ae_all_iff.2 fun n => hN (n + N) (Nat.le_add_left _ _)
    filter_upwards [hAll, hRLim] with z hz hlim
    exact le_of_tendsto' (hlim.comp (tendsto_add_atTop_nat N)) hz
  let gLim : SmoothRiemannianMetric I L.M := co.gInf (T - tau)
  let v : E → ℝ := fun z => chartDensity gLim alpha ((extChartAt I alpha).symm z)
  have hv : ContinuousOn v B :=
    (chartDensityOnE_contDiffOn gLim alpha).continuousOn.mono hBChart
  obtain ⟨C, hC⟩ := hBc.bddAbove_image hv
  have hvBd : ∀ z ∈ B, ENNReal.ofReal (v z) ≤ ENNReal.ofReal C :=
    fun z hz => ENNReal.ofReal_le_ofReal (hC ⟨z, hz, rfl⟩)
  have hIntBound : ∫⁻ z, w z * (ENNReal.ofReal (v z) * rInf z) ∂μ ≤
      ∫⁻ z, (ENNReal.ofReal C * (Cred : ENNReal)) * w z ∂μ := by
    apply lintegral_mono_ae
    filter_upwards [ae_restrict_mem hBc.measurableSet, hRInf] with z hz hr
    exact (mul_le_mul' (le_refl (w z)) (mul_le_mul' (hvBd z hz) hr)).trans_eq (mul_comm _ _)
  have hFinite : ∫⁻ z, w z * (ENNReal.ofReal (v z) * rInf z) ∂μ < ⊤ := by
    apply hIntBound.trans_lt
    rw [lintegral_const_mul' _ _ (ENNReal.mul_ne_top ENNReal.ofReal_ne_top (by simp))]
    exact (ENNReal.mul_ne_top (ENNReal.mul_ne_top ENNReal.ofReal_ne_top (by simp)) hwInt.ne).lt_top
  have hArea := chart_weighted_integral gLim alpha
    (fun y => ENNReal.ofReal (redDensity L.S T x y tau)) w hBc.measurableSet hBChart
  exact hArea.trans_lt hFinite

end DifferentialGeometry.CheegerGromovCompactness
