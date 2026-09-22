import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.PoleEndpointSpatialDerivativeLpConvergence
import DifferentialGeometry.Analysis.Integration.Lp.CompactQuadraticConvergence
import DifferentialGeometry.Analysis.Integration.Lp.CompactBilinearConvergence
import DifferentialGeometry.Analysis.Integration.Lp.ContinuousOn
import DifferentialGeometry.Geometry.Flow.RicciFlow.Compactness.Fields.WeightedGradientCoefficients
import DifferentialGeometry.Geometry.Flow.RicciFlow.Compactness.Fields.Open.HalfLineWindow

noncomputable section

namespace DifferentialGeometry.CheegerGromovCompactness

open Filter Set TopologicalSpace MeasureTheory
open DifferentialGeometry.Analysis.Calculus
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Operator
open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Geometry.Connection
open DifferentialGeometry.Geometry.Riemannian.Geodesic
open DifferentialGeometry.PDE.RicciFlow.Perelman
open DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions
open CanonicalNeighborhood
open scoped _root_.Manifold ContDiff _root_.Topology ENNReal

universe u uE uH

variable {E : Type uE} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]
  {H : Type uH} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {D : RealTimeInterval} (F : PointedFlowData.{u, uE, uH} (I := I) D)
  (hcar : D.carrier = Iic 0) (hreg : D.regular = Iio 0)
  (b : ℝ) (hbmem : b ∈ D.carrier) (tau : ℕ → ℝ) (q : ℕ → F.M)
  (hsigma : ∀ i, 0 < tau i + b)
  {P : PointedRiemannianManifold.{u, uE, uH} (I := I)} {phi : ℕ → ℕ}

private local instance : TopologicalSpace F.M := F.topology
private local instance : ChartedSpace H F.M := F.charted
private local instance : IsManifold I ∞ F.M := F.smooth
private local instance : SigmaCompactSpace F.M := F.sigmaCompact
private local instance : T2Space F.M := F.t2

attribute [local instance] PointedRiemannianManifold.topology
  PointedRiemannianManifold.charted PointedRiemannianManifold.smooth
  PointedRiemannianManifold.t2 PointedRiemannianManifold.sigmaCompact

local notation "U" => poleRescaledFlowSeq F hcar hreg b hbmem tau q hsigma
local notation "Y" => poleEndpointRescaledFlowSeq F hcar hreg b hbmem tau q hsigma

private local instance : MeasurableSpace E := borel E
private local instance : BorelSpace E := ⟨rfl⟩

private local instance cotangentNormedAddCommGroup : NormedAddCommGroup (E →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedAddCommGroup

private local instance cotangentNormedSpace : NormedSpace ℝ (E →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedSpace

private local instance cotangentDualNormedAddCommGroup : NormedAddCommGroup ((E →L[ℝ] ℝ) →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedAddCommGroup

private local instance cotangentDualNormedSpace : NormedSpace ℝ ((E →L[ℝ] ℝ) →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedSpace

private local instance cotangentBilinearNormedAddCommGroup :
    NormedAddCommGroup ((E →L[ℝ] ℝ) →L[ℝ] (E →L[ℝ] ℝ) →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedAddCommGroup

private local instance cotangentBilinearNormedSpace :
    NormedSpace ℝ ((E →L[ℝ] ℝ) →L[ℝ] (E →L[ℝ] ℝ) →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedSpace

namespace HalfLineMetricConvergenceData

theorem integrable_and_tendsto_integral_poleEndpoint_redLength_gradient_bilinear
    [ConnectedSpace P.M]
    (Phi : PointedCGHMaps Y P phi)
    (R : SmoothRiemannianMetric I P.M) (hR : RiemannianMetricComplete R)
    (bf : BumpFamily Phi) (hsrc : SourceIsSigmaCompact Phi) (htgt : TargetIsSigmaCompact Phi)
    (co : HalfLineMetricConvergenceData Phi R bf hsrc htgt)
    (hcomplete : MetricComplete
      ({ P with metric := co.gInf 0 } : PointedRiemannianManifold I))
    (hboundary : BoundarylessManifold I P.M)
    (kappa : ℕ → ℝ) (hF : ∀ i, IsAncientKappaSolution (kappa i) ((U).term i))
    (p : F.M) {J : Set P.M} (hJ : IsCompact J) {a c A : ℝ}
    (ha : 1 < a)
    (hbase : ∀ᶠ k in atTop, redLength ((U).term (phi (co.φ k))).S 0
      p (q (phi (co.φ k))) 1 ≤ A)
    (rho : ℕ → ℕ) (hrho : Tendsto rho atTop atTop)
    (ell : P.M × ℝ → ℝ)
    (hconv : ∀ y ∈ J, ∀ t ∈ Icc a c,
      Tendsto (fun k => redLength ((U).term (phi (co.φ (rho k)))).S 0 p
        (Phi.map (co.φ (rho k)) y) t) atTop (𝓝 (ell (y, t))))
    (x : P.M) {W K : Set E} (hW : IsOpen W)
    (hK : IsCompact K) (hKW : K ⊆ W)
    (hWt : W ⊆ (extChartAt I x).target)
    (hWJ : MapsTo (extChartAt I x).symm W J)
    {a' c' : ℝ} (haa : a < a') (hcc : c' < c)
    (w : E × ℝ → ℝ) (hw : ContinuousOn w (K ×ˢ Icc a' c'))
    (v : E × ℝ → E →L[ℝ] ℝ) (hv : ContinuousOn v (K ×ˢ Icc a' c')) :
    let ν := (DifferentialGeometry.Integral.Measure.modelHaar (E := E)).prod
      (volume : Measure ℝ)
    let d : ℕ → E × ℝ → E →L[ℝ] ℝ := fun k z =>
      (fderiv ℝ (fun v : E × ℝ => redLength ((U).term (phi (co.φ (rho k)))).S 0 p
        (Phi.map (co.φ (rho k)) ((extChartAt I x).symm v.1)) v.2) z).comp
          (ContinuousLinearMap.inl ℝ E ℝ)
    let d₀ : E × ℝ → E →L[ℝ] ℝ := fun z =>
      (fderiv ℝ (fun v : E × ℝ => ell ((extChartAt I x).symm v.1, v.2)) z).comp
        (ContinuousLinearMap.inl ℝ E ℝ)
    let B := fun k (z : E × ℝ) =>
      (w z * chartDensity (gSeqExt Phi R bf hsrc htgt (co.φ (rho k)) (1 - z.2)) x
        ((extChartAt I x).symm z.1)) •
      chartGradientBilin (gSeqExt Phi R bf hsrc htgt (co.φ (rho k)) (1 - z.2)) x
        ((extChartAt I x).symm z.1)
    let B₀ := fun z : E × ℝ =>
      (w z * chartDensity (co.gInf (1 - z.2)) x ((extChartAt I x).symm z.1)) •
        chartGradientBilin (co.gInf (1 - z.2)) x ((extChartAt I x).symm z.1)
    (∀ᶠ k in atTop,
      IntegrableOn (fun z => B k z (d k z) (v z)) (K ×ˢ Icc a' c') ν ∧
      IntegrableOn (fun z => B k z (d k z) (d k z)) (K ×ˢ Icc a' c') ν) ∧
    IntegrableOn (fun z => B₀ z (d₀ z) (v z)) (K ×ˢ Icc a' c') ν ∧
    IntegrableOn (fun z => B₀ z (d₀ z) (d₀ z)) (K ×ˢ Icc a' c') ν ∧
    Tendsto (fun k => ∫ z in K ×ˢ Icc a' c', B k z (d k z) (v z) ∂ν) atTop
      (𝓝 (∫ z in K ×ˢ Icc a' c', B₀ z (d₀ z) (v z) ∂ν)) ∧
    Tendsto (fun k => ∫ z in K ×ˢ Icc a' c', B k z (d k z) (d k z) ∂ν) atTop
      (𝓝 (∫ z in K ×ˢ Icc a' c', B₀ z (d₀ z) (d₀ z) ∂ν)) := by
  let _ : NeZero (Module.finrank ℝ E) := ⟨by
    obtain ⟨t, ht, y, hy⟩ := (hF 0).notFlat
    exact DifferentialGeometry.Tensor0SBundle.finrank_ne_zero_of_normSq0S_ne_zero
      (((U).term 0).S.base.metric t) y (by norm_num : 0 < 4)
      (((U).term 0).S.base.rm04 t y) hy⟩
  let ν := (DifferentialGeometry.Integral.Measure.modelHaar (E := E)).prod (volume : Measure ℝ)
  let d : ℕ → E × ℝ → E →L[ℝ] ℝ := fun k z =>
      (fderiv ℝ (fun v : E × ℝ => redLength ((U).term (phi (co.φ (rho k)))).S 0 p
        (Phi.map (co.φ (rho k)) ((extChartAt I x).symm v.1)) v.2) z).comp
          (ContinuousLinearMap.inl ℝ E ℝ)
  let d₀ : E × ℝ → E →L[ℝ] ℝ := fun z =>
      (fderiv ℝ (fun v : E × ℝ => ell ((extChartAt I x).symm v.1, v.2)) z).comp
        (ContinuousLinearMap.inl ℝ E ℝ)
  let B := fun k (z : E × ℝ) =>
      (w z * chartDensity (gSeqExt Phi R bf hsrc htgt (co.φ (rho k)) (1 - z.2)) x
        ((extChartAt I x).symm z.1)) •
      chartGradientBilin (gSeqExt Phi R bf hsrc htgt (co.φ (rho k)) (1 - z.2)) x
        ((extChartAt I x).symm z.1)
  let B₀ := fun z : E × ℝ =>
      (w z * chartDensity (co.gInf (1 - z.2)) x ((extChartAt I x).symm z.1)) •
        chartGradientBilin (co.gInf (1 - z.2)) x ((extChartAt I x).symm z.1)
  let C : Set (E × ℝ) := K ×ˢ Icc a' c'
  let T : Set (ℝ × E) := Icc (1 - c') (1 - a') ×ˢ K
  let r : E × ℝ → ℝ × E := fun z => (1 - z.2, z.1)
  let r' : ℝ × E → E × ℝ := fun z => (z.2, 1 - z.1)
  have hr : Continuous r := (continuous_const.sub continuous_snd).prodMk continuous_fst
  have hr' : Continuous r' := continuous_snd.prodMk (continuous_const.sub continuous_fst)
  have hrC : MapsTo r C T := by
    intro z hz
    exact ⟨⟨by dsimp [r]; linarith [hz.2.2], by dsimp [r]; linarith [hz.2.1]⟩, hz.1⟩
  have hrT : MapsTo r' T C := by
    intro z hz
    exact ⟨hz.2, ⟨by dsimp [r']; linarith [hz.1.2],
      by dsimp [r']; linarith [hz.1.1]⟩⟩
  let w' : ℝ × E → ℝ := fun z => w (r' z)
  have hw' : ContinuousOn w' T := hw.comp hr'.continuousOn hrT
  obtain ⟨n, hn⟩ := exists_nat_ge (c' - 1)
  have hwindow : Icc (1 - c') (1 - a') ⊆ Icc (-(n : ℝ)) 0 := by
    intro t ht
    constructor <;> linarith [ht.1, ht.2]
  let cw := (flowMetricConvergenceDataOfHalfLineWindow Phi R bf hsrc htgt
    co.φ co.strictMono co.gInf n (co.convergenceOn n).convergence).restrict Phi hwindow
  have hcwMetric : cw.gInf = co.gInf := rfl
  have hcwIndex : cw.φ = co.φ := rfl
  have hcarrier : Icc (1 - c') (1 - a') ⊆ (Y).D.carrier := by
    intro t ht
    change t ≤ 0
    linarith [ht.2]
  have hKT : K ⊆ (extChartAt I x).target := hKW.trans hWt
  have hTcarrier : T ⊆ (Y).D.carrier ×ˢ K := fun _ hz => ⟨hcarrier hz.1, hz.2⟩
  have hB (k : ℕ) : ContinuousOn (B k) C := by
    let Gk : MetricConnectionFamilyOn (I := I) (M := P.M) (Y).D :=
      (lcMetricFamily (I := I) (M := P.M)
        (fun t => gSeqExt Phi R bf hsrc htgt (co.φ (rho k)) t)).restrict (Y).D
    have hGk (t : ℝ) : Gk.metric t =
        gSeqExt Phi R bf hsrc htgt (co.φ (rho k)) t := rfl
    have hgram := continuousOn_chartGramOp_gSeqExt
      Phi R bf hsrc htgt (co.φ (rho k)) x hKT
    have h := (Geometry.Curvature.continuousOn_chartDensity_smul_chartGradientBilin
      Gk x (fun z hz => hKT hz.2) (hgram.mono hTcarrier) w' hw').comp
        hr.continuousOn hrC
    simpa only [B, hGk, w', r, r', Function.comp_def, sub_sub_cancel, Prod.eta] using h
  have hB₀ : ContinuousOn B₀ C := by
    have h := (cw.continuousOn_chartDensity_smul_chartGradientBilin
      Phi R bf hsrc htgt (1 - c') (1 - a') x hKT hK hcarrier w' hw').comp
        hr.continuousOn hrC
    simpa only [B₀, hcwMetric, w', r, r', Function.comp_def, sub_sub_cancel, Prod.eta] using h
  have hBconv : TendstoUniformlyOn B B₀ atTop C := by
    have h := ((cw.tendstoUniformlyOn_chartDensity_smul_chartGradientBilin
      Phi R bf hsrc htgt (1 - c') (1 - a') x hKT hK hcarrier w' hw').comp r).mono hrC
    simpa only [B, B₀, hcwMetric, hcwIndex, w', r, r', Function.comp_def,
      sub_sub_cancel, Prod.eta] using
      h.seq_tendstoUniformlyOn rho hrho
  obtain ⟨N, hd, hd₀, hstrong⟩ := exists_tendsto_toLp_fderiv_poleEndpoint_redLength_chart
    F hcar hreg b hbmem tau q hsigma Phi R hR bf hsrc htgt co hcomplete hboundary
    kappa hF p hJ ha hbase rho hrho ell hconv x hW hK hKW hWt hWJ haa hcc 2 (by norm_num)
  have hC : IsCompact C := hK.prod isCompact_Icc
  let _ : IsFiniteMeasure (ν.restrict C) := isFiniteMeasure_restrict.mpr hC.measure_ne_top
  have hv₂ : MemLp v 2 (ν.restrict C) :=
    (hv.memLp_top_of_isCompact hC hC.measurableSet).mono_exponent (by simp)
  have hdevent : ∀ᶠ k in atTop, MemLp (d k) 2 (ν.restrict C) := by
    refine eventually_atTop.mpr ⟨N, fun k hk => ?_⟩
    have hdk : MemLp (d ((k - N) + N)) 2 (ν.restrict C) := hd (k - N)
    rw [Nat.sub_add_cancel hk] at hdk
    exact hdk
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · filter_upwards [hdevent] with k hk
    exact ⟨integrableOn_bilinear_of_continuousOn_of_isCompact hC (B k) (hB k) hk hv₂,
      integrableOn_bilinear_of_continuousOn_of_isCompact hC (B k) (hB k) hk hk⟩
  · exact integrableOn_bilinear_of_continuousOn_of_isCompact hC B₀ hB₀ hd₀ hv₂
  · exact integrableOn_bilinear_of_continuousOn_of_isCompact hC B₀ hB₀ hd₀ hd₀
  · apply (tendsto_add_atTop_iff_nat N).mp
    exact tendsto_setIntegral_bilinear_of_tendstoUniformlyOn_of_isCompact
      (μ := ν) hC (fun k => B (k + N)) B₀
      (fun k => hB (k + N)) hB₀
      (hBconv.seq_tendstoUniformlyOn (fun k => k + N) (tendsto_add_atTop_nat N))
      (fun k => d (k + N)) d₀ v hd hd₀ hv₂ hstrong
  · apply (tendsto_add_atTop_iff_nat N).mp
    exact tendsto_setIntegral_quadratic_of_tendstoUniformlyOn_of_isCompact
      (μ := ν) hC (fun k => B (k + N)) B₀
      (fun k => hB (k + N)) hB₀
      (hBconv.seq_tendstoUniformlyOn (fun k => k + N) (tendsto_add_atTop_nat N))
      (fun k => d (k + N)) d₀ hd hd₀ hstrong

end HalfLineMetricConvergenceData

end DifferentialGeometry.CheegerGromovCompactness
