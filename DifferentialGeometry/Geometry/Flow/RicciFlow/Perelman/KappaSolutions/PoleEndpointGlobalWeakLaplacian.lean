import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.SelectedPoleEndpointWeakLaplacian
import DifferentialGeometry.Analysis.Parabolic.WeakEquation.EventualLocalInequality
import DifferentialGeometry.Topology.Manifold.CompactChartBall

noncomputable section

namespace DifferentialGeometry.CheegerGromovCompactness

open Filter Set _root_.MeasureTheory
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Operator
open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Tensor.Coordinates
open DifferentialGeometry.PDE.RicciFlow.Perelman
open DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood
open DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions
open DifferentialGeometry.Tensor0SBundle
open DifferentialGeometry.Analysis.Calculus
open scoped ContDiff _root_.Manifold _root_.Topology BigOperators

universe u uE uH

variable {E : Type uE} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]
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

namespace HalfLineMetricConvergenceData

theorem eventually_integrable_integral_poleEndpoint_redLength_chart_laplacian_nonneg
    [ConnectedSpace P.M]
    (Phi : PointedCGHMaps Y P phi) (R : SmoothRiemannianMetric I P.M)
    (hR : RiemannianMetricComplete R)
    (bf : BumpFamily Phi) (hsrc : SourceIsSigmaCompact Phi) (htgt : TargetIsSigmaCompact Phi)
    (co : HalfLineMetricConvergenceData Phi R bf hsrc htgt)
    (hcomplete : MetricComplete
      ({ P with metric := co.gInf 0 } : PointedRiemannianManifold I))
    (hboundary : BoundarylessManifold I P.M)
    (hb : b < 0) {kappa : ℝ} (hF : IsAncientKappaSolution kappa F)
    (kappaSeq : ℕ → ℝ) (hseq : ∀ i, IsAncientKappaSolution (kappaSeq i) ((U).term i))
    (p0 : F.M) (a : P.M) {δ T A0 : ℝ} (hδ : 1 < δ)
    (hbase : ∀ᶠ k in atTop, redLength ((U).term (phi (co.φ k))).S 0
      p0 (q (phi (co.φ k))) 1 ≤ A0)
    (rho : ℕ → ℕ) (hrho : Tendsto rho atTop atTop)
    {W : Set E} (hW : IsOpen W) (hWt : W ⊆ (extChartAt I a).target)
    {μ : Measure E} [Measure.IsAddHaarMeasure μ]
    {test : ℝ × E → ℝ} (htest : ContDiff ℝ 2 test) (htestc : HasCompactSupport test)
    (hsupport : tsupport test ⊆ Ioo δ T ×ˢ W) (htestn : ∀ p, 0 ≤ test p) :
    ∀ᶠ k in atTop,
      let metric : ℝ → SmoothRiemannianMetric I P.M :=
        fun s => gSeqExt Phi R bf hsrc htgt (co.φ (rho k)) (1 - s)
      let ell : ℝ → P.M → ℝ := fun s y =>
        redLength ((U).term (phi (co.φ (rho k)))).S 0 p0 (Phi.map (co.φ (rho k)) y) s
      let f : ℝ × E → ℝ := fun p => scalarOnE (I := I) a (ell p.1) p.2
      let B : ℝ × E → ℝ := fun p => chartDensityOnE (metric p.1) a p.2 *
        ((1 / 2 : ℝ) * normGradSqFun (metric p.1) (ell p.1) ((extChartAt I a).symm p.2) -
          (1 / 2 : ℝ) * ((U).term (phi (co.φ (rho k)))).S.scalar (-p.1)
            (Phi.map (co.φ (rho k)) ((extChartAt I a).symm p.2)) +
          ((Module.finrank ℝ E : ℝ) - f p) / (2 * p.1))
      let Q : ℝ × E → ℝ := fun p => B p * test p +
          ∑ ij : Fin (Module.finrank ℝ E) × Fin (Module.finrank ℝ E),
            (chartDensityOnE (metric p.1) a p.2 *
              chartInvGramOnE (metric p.1) a ij.1 ij.2 p.2) *
              fderiv ℝ (fun z => f (p.1, z)) p.2 (chartModelBasis E ij.1) *
              fderiv ℝ test p (0, chartModelBasis E ij.2)
      Integrable Q (volume.prod μ) ∧ 0 ≤ ∫ p, Q p ∂volume.prod μ := by
  let metric : ℕ → ℝ → SmoothRiemannianMetric I P.M :=
    fun k s => gSeqExt Phi R bf hsrc htgt (co.φ (rho k)) (1 - s)
  let ell : ℕ → ℝ → P.M → ℝ := fun k s y =>
    redLength ((U).term (phi (co.φ (rho k)))).S 0 p0 (Phi.map (co.φ (rho k)) y) s
  let f : ℕ → ℝ × E → ℝ := fun k p => scalarOnE (I := I) a (ell k p.1) p.2
  let B : ℕ → ℝ × E → ℝ := fun k p => chartDensityOnE (metric k p.1) a p.2 *
    ((1 / 2 : ℝ) * normGradSqFun (metric k p.1) (ell k p.1) ((extChartAt I a).symm p.2) -
      (1 / 2 : ℝ) * ((U).term (phi (co.φ (rho k)))).S.scalar (-p.1)
        (Phi.map (co.φ (rho k)) ((extChartAt I a).symm p.2)) +
      ((Module.finrank ℝ E : ℝ) - f k p) / (2 * p.1))
  let A : ℕ → Fin (Module.finrank ℝ E) × Fin (Module.finrank ℝ E) → ℝ × E → ℝ :=
    fun k ij p => (chartDensityOnE (metric k p.1) a p.2 *
      chartInvGramOnE (metric k p.1) a ij.1 ij.2 p.2) *
      fderiv ℝ (fun z => f k (p.1, z)) p.2 (chartModelBasis E ij.1)
  let v : Fin (Module.finrank ℝ E) × Fin (Module.finrank ℝ E) → ℝ × E :=
    fun ij => (0, chartModelBasis E ij.2)
  apply Analysis.eventually_integrable_integral_mul_add_sum_mul_fderiv_nonneg_of_local
    B A v (Ω := Ioo δ T ×ˢ W) ?_ htest htestc hsupport htestn
  intro z hz
  obtain ⟨r, hr, hrW, hK, hKchart, hballK⟩ :=
    DifferentialGeometry.Topology.Manifold.exists_extChartAt_symm_image_closedBall_subset
      a (hW.mem_nhds hz.2) hWt
  let K : Set P.M := (extChartAt I a).symm '' Metric.closedBall z.2 r
  have hchart : K ⊆ (chartAt H a).source := by
    simpa only [extChartAt_source] using hKchart
  have hballW : Metric.ball z.2 r ⊆ W := Metric.ball_subset_closedBall.trans hrW
  refine ⟨Ioo δ T ×ˢ Metric.ball z.2 r, isOpen_Ioo.prod Metric.isOpen_ball,
    ⟨hz.1, Metric.mem_ball_self hr⟩, Set.prod_mono Subset.rfl hballW, ?_⟩
  have hselected := eventually_exists_nhds_integral_poleEndpoint_redLength_chart_laplacian_nonneg
    F hcar hreg b hbmem tau q hsigma Phi R hR bf hsrc htgt co hcomplete hboundary
    hb hF kappaSeq hseq p0 a hK hchart hδ hbase rho hrho
    Metric.isOpen_ball (convex_ball _ _) hballK isOpen_Ioo Ioo_subset_Icc_self
      (S := Ioo δ T) (T := T) (μ := μ)
  filter_upwards [hselected] with k hk
  obtain ⟨_, hB, hA, hlocal⟩ := hk
  intro ψ hψ hψc hψV hψn
  have hAi : ∀ ij : Fin (Module.finrank ℝ E) × Fin (Module.finrank ℝ E),
      LocallyIntegrableOn (A k ij) (Ioo δ T ×ˢ Metric.ball z.2 r) (volume.prod μ) :=
    fun ij => hA ij.1 ij.2
  refine ⟨DifferentialGeometry.Analysis.integrable_mul_add_sum_mul_fderiv
    (B k) (A k) v hB hAi (hψ.of_le (by norm_num)) hψc hψV, ?_⟩
  apply DifferentialGeometry.Analysis.integral_mul_add_sum_mul_fderiv_nonneg_of_local
    (B k) (A k) v hB hAi ?_ hψ hψc hψV hψn
  intro y hy
  obtain ⟨J', r', hJ', hyJ', hJ'S, hr', hball', hineq⟩ := hlocal y hy
  exact ⟨J' ×ˢ Metric.ball y.2 r', hJ'.prod Metric.isOpen_ball,
    ⟨hyJ', Metric.mem_ball_self hr'⟩, Set.prod_mono hJ'S hball', hineq⟩

end HalfLineMetricConvergenceData

end DifferentialGeometry.CheegerGromovCompactness
