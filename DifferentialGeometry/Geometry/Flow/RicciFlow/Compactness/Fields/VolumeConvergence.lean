import DifferentialGeometry.Geometry.Flow.RicciFlow.Compactness.Fields.GramConvergence
import DifferentialGeometry.Geometry.Measure.Chart.GramOperator
import DifferentialGeometry.Geometry.Measure.Chart.Parametrization
import DifferentialGeometry.Topology.Manifold.PartialDiffeomorph.Basic

noncomputable section

open Set Filter Bundle
open scoped Manifold Topology ContDiff

namespace DifferentialGeometry.CheegerGromovCompactness

open Geometry.Curvature Geometry.Operator Integral.Measure Tensor.Coordinates

universe u uE uH

section Gram

variable {E : Type uE} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]
variable {H : Type uH} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {X : PointedFlowSeq.{u, uE, uH} (I := I)}
variable {P : PointedRiemannianManifold.{u, uE, uH} (I := I)}
variable {subseq : ℕ → ℕ}
variable (Φ : PointedCGHMaps (I := I) X P subseq)

theorem FlowMetricConvergenceData.tendstoUniformly_chartDensity
    (R : let : TopologicalSpace P.M := P.topology
      let : ChartedSpace H P.M := P.charted
      let : IsManifold I ∞ P.M := P.smooth
      SmoothRiemannianMetric I P.M)
    (bf : BumpFamily (I := I) Φ) (hsrc : SourceIsSigmaCompact Φ) (htgt : TargetIsSigmaCompact Φ)
    (beta psi : ℝ) (co : FlowMetricConvergenceData (I := I) Φ R bf hsrc htgt beta psi)
    (alpha : P.M) {K : Set E}
    (hKchart : let : TopologicalSpace P.M := P.topology
      let : ChartedSpace H P.M := P.charted
      K ⊆ (extChartAt I alpha).target) (hKc : IsCompact K)
    (hcont : let : TopologicalSpace P.M := P.topology
      let : ChartedSpace H P.M := P.charted
      let : T2Space P.M := P.t2
      let : IsManifold I ∞ P.M := P.smooth
      let : SigmaCompactSpace P.M := P.sigmaCompact
      ContinuousOn (chartGramOp (I := I)
        ((lcMetricFamily (I := I) (M := P.M) co.gInf).restrict X.D) alpha) (Icc beta psi ×ˢ K))
    {Q : Type*} {tau : Q → ℝ} {u : ℕ → Q → E} {uLim : Q → E}
    (htau : ∀ q, tau q ∈ Icc beta psi)
    (huK : ∀ᶠ k in atTop, ∀ q, u k q ∈ K)
    (hlimK : ∀ q, uLim q ∈ K) (hu : TendstoUniformly u uLim atTop) :
    let : TopologicalSpace P.M := P.topology
    let : ChartedSpace H P.M := P.charted
    let : T2Space P.M := P.t2
    let : IsManifold I ∞ P.M := P.smooth
    let : SigmaCompactSpace P.M := P.sigmaCompact
    TendstoUniformly
      (fun k q => chartDensity (gSeqExt (I := I) Φ R bf hsrc htgt (co.φ k) (tau q))
        alpha ((extChartAt I alpha).symm (u k q)))
      (fun q => chartDensity (co.gInf (tau q)) alpha ((extChartAt I alpha).symm (uLim q)))
      atTop := by
  let : TopologicalSpace P.M := P.topology
  let : ChartedSpace H P.M := P.charted
  let : T2Space P.M := P.t2
  let : IsManifold I ∞ P.M := P.smooth
  let : SigmaCompactSpace P.M := P.sigmaCompact
  let GSeq : ℕ → MetricConnectionFamilyOn (I := I) (M := P.M) X.D := fun k =>
    (lcMetricFamily (I := I) (M := P.M)
      (fun t => gSeqExt (I := I) Φ R bf hsrc htgt (co.φ k) t)).restrict X.D
  let GInf : MetricConnectionFamilyOn (I := I) (M := P.M) X.D :=
    (lcMetricFamily (I := I) (M := P.M) co.gInf).restrict X.D
  apply tendstoUniformly_chartDensity_of_chartGramOp GSeq GInf alpha
    (co.tendstoUniformly_chartGramOp Φ R bf hsrc htgt beta psi alpha
      hKchart hKc hcont htau huK hlimK hu)
  exact ((isCompact_Icc.prod hKc).image_of_continuousOn hcont).isBounded.subset (by
    rintro A ⟨q, rfl⟩
    exact ⟨(tau q, uLim q), ⟨htau q, hlimK q⟩, rfl⟩)

theorem FlowMetricConvergenceData.tendstoUniformly_chartDensity_of_subset_carrier [I.Boundaryless]
    (R : let : TopologicalSpace P.M := P.topology
      let : ChartedSpace H P.M := P.charted
      let : IsManifold I ∞ P.M := P.smooth
      SmoothRiemannianMetric I P.M)
    (bf : BumpFamily (I := I) Φ) (hsrc : SourceIsSigmaCompact Φ) (htgt : TargetIsSigmaCompact Φ)
    (beta psi : ℝ) (co : FlowMetricConvergenceData (I := I) Φ R bf hsrc htgt beta psi)
    (alpha : P.M) {K : Set E}
    (hKchart : let : TopologicalSpace P.M := P.topology
      let : ChartedSpace H P.M := P.charted
      K ⊆ (extChartAt I alpha).target) (hKc : IsCompact K)
    (hcarrier : Icc beta psi ⊆ X.D.carrier)
    {Q : Type*} {tau : Q → ℝ} {u : ℕ → Q → E} {uLim : Q → E}
    (htau : ∀ q, tau q ∈ Icc beta psi)
    (huK : ∀ᶠ k in atTop, ∀ q, u k q ∈ K)
    (hlimK : ∀ q, uLim q ∈ K) (hu : TendstoUniformly u uLim atTop) :
    let : TopologicalSpace P.M := P.topology
    let : ChartedSpace H P.M := P.charted
    let : T2Space P.M := P.t2
    let : IsManifold I ∞ P.M := P.smooth
    let : SigmaCompactSpace P.M := P.sigmaCompact
    TendstoUniformly
      (fun k q => chartDensity (gSeqExt (I := I) Φ R bf hsrc htgt (co.φ k) (tau q))
        alpha ((extChartAt I alpha).symm (u k q)))
      (fun q => chartDensity (co.gInf (tau q)) alpha ((extChartAt I alpha).symm (uLim q)))
      atTop := by
  exact co.tendstoUniformly_chartDensity Φ R bf hsrc htgt beta psi alpha hKchart hKc
    (co.continuousOn_chartGramOp Φ R bf hsrc htgt beta psi alpha hKchart hKc hcarrier)
    htau huK hlimK hu

end Gram

section Parametrization

variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
variable {H : Type uH} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
variable {X : PointedFlowSeq.{u, uE, uH} (I := I)}
variable {P : PointedRiemannianManifold.{u, uE, uH} (I := I)}
variable {subseq : ℕ → ℕ}
variable (Φ : PointedCGHMaps (I := I) X P subseq)

def PointedCGHMaps.chartParametrization (k : ℕ) (alpha : P.M) :
    let : TopologicalSpace P.M := P.topology
    let : ChartedSpace H P.M := P.charted
    let : TopologicalSpace (X.term (subseq k)).M := (X.term (subseq k)).topology
    let : ChartedSpace H (X.term (subseq k)).M := (X.term (subseq k)).charted
    PartialDiffeomorph 𝓘(ℝ, E) I E (X.term (subseq k)).M 1 := by
  let : TopologicalSpace P.M := P.topology
  let : ChartedSpace H P.M := P.charted
  let : IsManifold I ∞ P.M := P.smooth
  let : TopologicalSpace (X.term (subseq k)).M := (X.term (subseq k)).topology
  let : ChartedSpace H (X.term (subseq k)).M := (X.term (subseq k)).charted
  exact (PartialDiffeomorph.extChartAt I 1 alpha).symm.trans
    (PartialDiffeomorph.ofLE (Φ.partialDiffeomorph k) (by norm_num))

theorem PointedCGHMaps.chartParametrization_toPartialEquiv (k : ℕ) (alpha : P.M) :
    let : TopologicalSpace P.M := P.topology
    let : ChartedSpace H P.M := P.charted
    let : TopologicalSpace (X.term (subseq k)).M := (X.term (subseq k)).topology
    let : ChartedSpace H (X.term (subseq k)).M := (X.term (subseq k)).charted
    (Φ.chartParametrization k alpha).toPartialEquiv =
      (extChartAt I alpha).symm.trans (Φ.partialDiffeomorph k).toPartialEquiv := rfl

theorem paramDensity_chartParametrization
    (R : let : TopologicalSpace P.M := P.topology
      let : ChartedSpace H P.M := P.charted
      let : IsManifold I ∞ P.M := P.smooth
      SmoothRiemannianMetric I P.M)
    (bf : BumpFamily (I := I) Φ) (hsrc : SourceIsSigmaCompact Φ) (htgt : TargetIsSigmaCompact Φ)
    (k : ℕ) (t : ℝ) (alpha : P.M) {w : E}
    (hw : let : TopologicalSpace P.M := P.topology
      let : ChartedSpace H P.M := P.charted
      let : TopologicalSpace (X.term (subseq k)).M :=
        (X.term (subseq k)).topology
      let : ChartedSpace H (X.term (subseq k)).M :=
        (X.term (subseq k)).charted
      w ∈ (PointedCGHMaps.chartParametrization (I := I) Φ k alpha).source)
    (hOne : let : TopologicalSpace P.M := P.topology
      let : ChartedSpace H P.M := P.charted
      bf.chi k ((extChartAt I alpha).symm w) = 1) :
    let : TopologicalSpace P.M := P.topology
    let : ChartedSpace H P.M := P.charted
    let : T2Space P.M := P.t2
    let : IsManifold I ∞ P.M := P.smooth
    let : SigmaCompactSpace P.M := P.sigmaCompact
    let : TopologicalSpace (X.term (subseq k)).M :=
      (X.term (subseq k)).topology
    let : ChartedSpace H (X.term (subseq k)).M :=
      (X.term (subseq k)).charted
    let : T2Space (X.term (subseq k)).M := (X.term (subseq k)).t2
    let : IsManifold I ∞ (X.term (subseq k)).M :=
      (X.term (subseq k)).smooth
    let : SigmaCompactSpace (X.term (subseq k)).M :=
      (X.term (subseq k)).sigmaCompact
    paramDensity (I := I) ((X.term (subseq k)).S.base.metric t)
        (PointedCGHMaps.chartParametrization (I := I) Φ k alpha) w =
      chartDensity (I := I) (gSeqExt (I := I) Φ R bf hsrc htgt k t) alpha
        ((extChartAt I alpha).symm w) := by
  classical
  let : TopologicalSpace P.M := P.topology
  let : ChartedSpace H P.M := P.charted
  let : T2Space P.M := P.t2
  let : IsManifold I ∞ P.M := P.smooth
  let : SigmaCompactSpace P.M := P.sigmaCompact
  let : TopologicalSpace (X.term (subseq k)).M :=
    (X.term (subseq k)).topology
  let : ChartedSpace H (X.term (subseq k)).M :=
    (X.term (subseq k)).charted
  let : T2Space (X.term (subseq k)).M := (X.term (subseq k)).t2
  let : IsManifold I ∞ (X.term (subseq k)).M :=
    (X.term (subseq k)).smooth
  let : SigmaCompactSpace (X.term (subseq k)).M :=
    (X.term (subseq k)).sigmaCompact
  let chart := (PartialDiffeomorph.extChartAt I 1 alpha).symm
  let pointMap := PartialDiffeomorph.ofLE (Φ.partialDiffeomorph k) (m := 1) (by norm_num)
  let x : P.M := chart w
  have hwParts : w ∈ chart.source ∩ (chart : E → P.M) ⁻¹' pointMap.source := by
    change w ∈ chart.source ∩ (chart : E → P.M) ⁻¹' pointMap.source at hw
    exact hw
  have hwChart : w ∈ chart.source := hwParts.1
  have hxSrc : x ∈ Φ.source k := hwParts.2
  let xsrc : SourceDomain (I := I) Φ k := ⟨x, hxSrc⟩
  let : TopologicalSpace (SourceDomain (I := I) Φ k) :=
    sourceDomTop (I := I) Φ k
  let : ChartedSpace H (SourceDomain (I := I) Φ k) :=
    sourceDomCharted (I := I) Φ k
  let : T2Space (SourceDomain (I := I) Φ k) := sourceDomT2 (I := I) Φ k
  let : IsManifold I ∞ (SourceDomain (I := I) Φ k) :=
    sourceDomSmooth (I := I) Φ k
  let : SigmaCompactSpace (SourceDomain (I := I) Φ k) :=
    sourceDomSigmaOf (I := I) Φ k (hsrc k)
  have hMap : PointedCGHMaps.chartParametrization (I := I) Φ k alpha w = Φ.map k x := by
    rfl
  have hChartDiff : MDifferentiableAt (modelWithCornersSelf ℝ E) I chart w :=
    chart.mdifferentiableAt one_ne_zero hwChart
  have hPointDiff : MDifferentiableAt I I pointMap x :=
    pointMap.mdifferentiableAt one_ne_zero hxSrc
  have hDeriv :
      mfderiv (modelWithCornersSelf ℝ E) I
          (PointedCGHMaps.chartParametrization (I := I) Φ k alpha) w =
        (mfderiv I I pointMap x).comp
          (mfderiv (modelWithCornersSelf ℝ E) I chart w) := by
    change mfderiv 𝓘(ℝ, E) I (pointMap ∘ chart) w =
      (mfderiv I I pointMap x).comp (mfderiv 𝓘(ℝ, E) I chart w)
    exact mfderiv_comp w hPointDiff hChartDiff
  have hRestrict (v : TangentSpace I xsrc) :
      mfderiv I I (fun y : SourceDomain (I := I) Φ k ↦
        Φ.map k (y : P.M)) xsrc v =
        mfderiv I I pointMap x v := by
    have hVal : MDifferentiableAt I I
        (fun y : SourceDomain (I := I) Φ k ↦ (y : P.M)) xsrc :=
      ContMDiffAt.mdifferentiableAt
        ((contMDiff_subtype_val (I := I) (n := 1)
          (U := sourceOpen (I := I) Φ k)).contMDiffAt) (by norm_num)
    have hComp := mfderiv_comp xsrc hPointDiff hVal
    have hvinc :
        mfderiv I I (fun y : SourceDomain (I := I) Φ k ↦ (y : P.M)) xsrc v = v := by
      simpa only using
        mfderiv_subtype_val_apply (I := I) (sourceOpen (I := I) Φ k) xsrc v
    change mfderiv I I
      (pointMap ∘ (fun y : SourceDomain (I := I) Φ k ↦ (y : P.M))) xsrc v =
        mfderiv I I pointMap x v
    rw [congrArg (fun L ↦ L v) hComp]
    change mfderiv I I pointMap (xsrc : P.M)
      (mfderiv I I (fun y : SourceDomain (I := I) Φ k ↦ (y : P.M)) xsrc v) =
        mfderiv I I pointMap x v
    rw [hvinc]
  let D := SourceDomainMetricData.ofRestrictPullback (I := I)
    (Φ := Φ) (k := k) (hsrc k)
    (fun _ ↦ sourceMetricRestriction (I := I) Φ R k) (fun _ ↦ R)
  have hMetric : sourceMetric (I := I) Φ hsrc htgt k t = D.pullbackMetric t := by
    simpa only [sourceMetric, D] using
      sourceFlow_metric_eq (I := I) Φ k (hsrc k) (htgt k)
        (fun _ ↦ sourceMetricRestriction (I := I) Φ R k) (fun _ ↦ R) t
  have hSrcInner (v q : TangentSpace I xsrc) :
      (sourceMetric (I := I) Φ hsrc htgt k t).inner xsrc v q =
        ((X.term (subseq k)).S.family.metric t).inner (Φ.map k x)
          (mfderiv I I pointMap x v) (mfderiv I I pointMap x q) := by
    rw [hMetric]
    have hpull := D.pullback_inner t xsrc v q
    exact hpull.trans (congrArg₂
      (fun a b => ((X.term (subseq k)).S.family.metric t).inner (Φ.map k x) a b)
      (hRestrict v) (hRestrict q))
  have hGram :
      paramGramMatrix (I := I) ((X.term (subseq k)).S.base.metric t)
          (PointedCGHMaps.chartParametrization (I := I) Φ k alpha) w =
        paramGramMatrix (I := I) (gSeqExt (I := I) Φ R bf hsrc htgt k t)
          chart w := by
    ext i j
    simp only [paramGramMatrix_apply]
    let v := mfderiv (modelWithCornersSelf ℝ E) I chart w (chartModelBasis E i)
    let q := mfderiv (modelWithCornersSelf ℝ E) I chart w (chartModelBasis E j)
    rw [hMap, hDeriv]
    change ((X.term (subseq k)).S.base.metric t).inner (Φ.map k x)
        (mfderiv I I pointMap x v) (mfderiv I I pointMap x q) =
      (gSeqExt (I := I) Φ R bf hsrc htgt k t).inner (chart w) v q
    have hExt := gSeqExt_inner_of_mem (I := I) Φ R bf hsrc htgt k t x hxSrc v q
    have hOne' : bf.chi k x = 1 := hOne
    rw [hOne'] at hExt
    simp only [one_smul, sub_self, zero_smul, add_zero] at hExt
    exact (hSrcInner v q).symm.trans hExt.symm
  have hParam :
      paramDensity (I := I) ((X.term (subseq k)).S.base.metric t)
          (PointedCGHMaps.chartParametrization (I := I) Φ k alpha) w =
        paramDensity (I := I) (gSeqExt (I := I) Φ R bf hsrc htgt k t)
          chart w := by
    unfold paramDensity
    rw [hGram]
  exact hParam.trans (paramDensity_extChartAt_symm
    (gSeqExt (I := I) Φ R bf hsrc htgt k t) alpha hwChart)

end Parametrization

end DifferentialGeometry.CheegerGromovCompactness
