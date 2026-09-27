import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.PoleEndpointSpatialDerivativeConvergence
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.PoleEndpointSpatialDerivativeBound
import DifferentialGeometry.Analysis.Integration.Lp.CovectorConvergence

noncomputable section

namespace DifferentialGeometry.CheegerGromovCompactness

open Filter Set TopologicalSpace MeasureTheory
open DifferentialGeometry.Analysis.Calculus
open DifferentialGeometry.Geometry.Curvature
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

namespace HalfLineMetricConvergenceData

theorem exists_tendsto_toLp_fderiv_poleEndpoint_redLength_chart
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
    (pExp : ℝ≥0∞) [Fact (1 ≤ pExp)] (hpExp : pExp ≠ (⊤ : ℝ≥0∞)) :
    let μ :=
      ((DifferentialGeometry.Integral.Measure.modelHaar (E := E)).prod
        (volume : Measure ℝ)).restrict (K ×ˢ Icc a' c')
    let d : ℕ → E × ℝ → E →L[ℝ] ℝ := fun k z =>
      (fderiv ℝ (fun w : E × ℝ => redLength ((U).term (phi (co.φ (rho k)))).S 0 p
        (Phi.map (co.φ (rho k)) ((extChartAt I x).symm w.1)) w.2) z).comp
          (ContinuousLinearMap.inl ℝ E ℝ)
    let d₀ : E × ℝ → E →L[ℝ] ℝ := fun z =>
      (fderiv ℝ (fun w : E × ℝ => ell ((extChartAt I x).symm w.1, w.2)) z).comp
        (ContinuousLinearMap.inl ℝ E ℝ)
    ∃ N : ℕ, ∃ hd : ∀ k, MemLp (d (k + N)) pExp μ, ∃ hd₀ : MemLp d₀ pExp μ,
      Tendsto (fun k => (hd k).toLp (d (k + N))) atTop (𝓝 (hd₀.toLp d₀)) := by
  let ν := (DifferentialGeometry.Integral.Measure.modelHaar (E := E)).prod (volume : Measure ℝ)
  let μ := ν.restrict (K ×ˢ Icc a' c')
  let _ : IsFiniteMeasure μ := isFiniteMeasure_restrict.mpr
    (hK.prod isCompact_Icc).measure_ne_top
  let d : ℕ → E × ℝ → E →L[ℝ] ℝ := fun k z =>
    (fderiv ℝ (fun w : E × ℝ => redLength ((U).term (phi (co.φ (rho k)))).S 0 p
      (Phi.map (co.φ (rho k)) ((extChartAt I x).symm w.1)) w.2) z).comp
        (ContinuousLinearMap.inl ℝ E ℝ)
  let d₀ : E × ℝ → E →L[ℝ] ℝ := fun z =>
    (fderiv ℝ (fun w : E × ℝ => ell ((extChartAt I x).symm w.1, w.2)) z).comp
      (ContinuousLinearMap.inl ℝ E ℝ)
  have ha' : 1 ≤ a' := (ha.trans haa).le
  have hinterval : Icc a' c' ⊆ Icc a c := fun _ ht =>
    ⟨haa.le.trans ht.1, ht.2.trans hcc.le⟩
  have hmem : ∀ᶠ k in atTop, MemLp (d k) pExp μ := by
    exact hrho.eventually (eventually_memLp_fderiv_poleEndpoint_redLength_chart
      F hcar hreg b hbmem tau q hsigma Phi R hR co kappa hF p hJ ha' hbase
      x hW hK hKW hWt hWJ ν pExp)
  have hmem₀ : MemLp d₀ pExp μ :=
    memLp_fderiv_poleEndpoint_redLength_limit_chart
      F hcar hreg b hbmem tau q hsigma Phi R hR co kappa hF p hJ ha' hbase
      rho hrho ell (fun y hy t ht => hconv y hy t (hinterval ht))
      x hW hK hKW hWt hWJ ν pExp
  obtain ⟨B, _hB, hbound⟩ := exists_eventually_norm_fderiv_poleEndpoint_redLength_chart_le
    F hcar hreg b hbmem tau q hsigma Phi R hR co kappa hF p hJ (c := c') ha' hbase
    x hW hK hKW hWt hWJ
  have hbound' : ∀ᶠ k in atTop, ∀ᵐ z ∂μ, ‖d k z‖ ≤ B := by
    filter_upwards [hrho.eventually hbound] with k hk
    filter_upwards [ae_restrict_mem (hK.measurableSet.prod measurableSet_Icc)] with z hz
    exact hk z.1 hz.1 z.2 hz.2
  obtain ⟨N, hN⟩ := eventually_atTop.mp (hmem.and hbound')
  let hd : ∀ k, MemLp (d (k + N)) pExp μ := fun k =>
    (hN (k + N) (Nat.le_add_left N k)).1
  refine ⟨N, hd, hmem₀, ?_⟩
  apply MemLp.tendsto_toLp_of_ae_tendsto_apply_of_ae_norm_le hpExp
    (fun k => d (k + N)) d₀ hd hmem₀
    (fun k => (hN (k + N) (Nat.le_add_left N k)).2)
  have hae := ae_tendsto_fderiv_poleEndpoint_redLength_chart_apply
    F hcar hreg b hbmem tau q hsigma Phi R hR bf hsrc htgt co hcomplete hboundary
    kappa hF p hJ ha hbase rho hrho ell hconv x hW hWt hWJ
  filter_upwards [ae_restrict_of_ae hae,
    ae_restrict_mem (hK.measurableSet.prod measurableSet_Icc)] with z hz hzs
  intro v
  exact (hz ⟨hKW hzs.1, haa.trans_le hzs.2.1, hzs.2.2.trans_lt hcc⟩ v).comp
    (tendsto_add_atTop_nat N)

end HalfLineMetricConvergenceData

end DifferentialGeometry.CheegerGromovCompactness
