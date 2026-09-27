import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.AncientPoleEndpointWeakLaplacian
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.PoleEndpointChartRegularity
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.PoleEndpointLaplacianIntegrability

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

theorem eventually_exists_nhds_integral_poleEndpoint_redLength_chart_laplacian_nonneg
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
    (p0 : F.M) (a : P.M) {K : Set P.M} (hK : IsCompact K)
    (hchart : K ⊆ (chartAt H a).source) {δ T A0 : ℝ} (hδ : 1 < δ)
    (hbase : ∀ᶠ k in atTop, redLength ((U).term (phi (co.φ k))).S 0
      p0 (q (phi (co.φ k))) 1 ≤ A0)
    (rho : ℕ → ℕ) (hrho : Tendsto rho atTop atTop)
    {W : Set E} (hW : IsOpen W) (hWconv : Convex ℝ W)
    (hWK : W ⊆ (extChartAt I a) '' K)
    {S : Set ℝ} (hS : IsOpen S) (hST : S ⊆ Icc δ T)
    {μ : Measure E} [Measure.IsAddHaarMeasure μ] :
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
      LocallyLipschitzOn (S ×ˢ W) f ∧
      LocallyIntegrableOn B (S ×ˢ W) (volume.prod μ) ∧
      (∀ i j : Fin (Module.finrank ℝ E),
        LocallyIntegrableOn
          (fun p : ℝ × E => chartDensityOnE (metric p.1) a p.2 *
            chartInvGramOnE (metric p.1) a i j p.2 *
              fderiv ℝ (fun z => f (p.1, z)) p.2 (chartModelBasis E i))
          (S ×ˢ W) (volume.prod μ)) ∧
      ∀ q0 : ℝ × E, q0 ∈ S ×ˢ W →
      ∃ (J' : Set ℝ) (r : ℝ), IsOpen J' ∧ q0.1 ∈ J' ∧ J' ⊆ S ∧
        0 < r ∧ Metric.ball q0.2 r ⊆ W ∧
        ∀ φ : ℝ × E → ℝ, ContDiff ℝ 2 φ → HasCompactSupport φ →
        tsupport φ ⊆ J' ×ˢ Metric.ball q0.2 r → (∀ p, 0 ≤ φ p) →
        0 ≤ ∫ p, B p * φ p +
          ∑ ij : Fin (Module.finrank ℝ E) × Fin (Module.finrank ℝ E),
            (chartDensityOnE (metric p.1) a p.2 *
              chartInvGramOnE (metric p.1) a ij.1 ij.2 p.2) *
              fderiv ℝ (fun z => f (p.1, z)) p.2 (chartModelBasis E ij.1) *
              fderiv ℝ φ p (0, chartModelBasis E ij.2) ∂volume.prod μ := by
  have hWt : W ⊆ (extChartAt I a).target := by
    intro z hz
    obtain ⟨y, hy, rfl⟩ := hWK hz
    exact (extChartAt I a).map_source (by simpa only [extChartAt_source] using hchart hy)
  have hWInv : MapsTo (extChartAt I a).symm W K := by
    intro z hz
    obtain ⟨y, hy, rfl⟩ := hWK hz
    rw [(extChartAt I a).left_inv (by simpa only [extChartAt_source] using hchart hy)]
    exact hy
  have hSpos : S ⊆ Ioi 1 := fun s hs => lt_of_lt_of_le hδ (hST hs).1
  have hraw : Tendsto (fun k => co.φ (rho k)) atTop atTop :=
    co.strictMono.tendsto_atTop.comp hrho
  obtain ⟨A, hregular⟩ :=
    exists_eventually_locallyLipschitzOn_concaveOn_poleEndpoint_redLength_chart
    F hcar hreg b hbmem tau q hsigma Phi R hR bf hsrc htgt co hcomplete hboundary
    kappaSeq hseq p0 a hK hchart hδ hbase rho hrho hWconv hWK hST
  have hlocal :=
    eventually_exists_nhds_integral_poleEndpoint_redLength_chart_laplacian_nonneg_of_ancient
      F hcar hreg b hbmem tau q hsigma Phi R bf hsrc htgt p0 a hb hF hK (μ := μ)
  have hintegrable := eventually_locallyIntegrableOn_poleEndpoint_redLength_chart_laplacian_rhs
    F hcar hreg b hbmem tau q hsigma Phi R bf hsrc htgt p0 a hK (μ := μ)
  filter_upwards [hregular, hraw.eventually hlocal, hraw.eventually hintegrable]
    with k hkregular hklocal hkB
  intro metric ell f B
  have hlip : LocallyLipschitzOn (S ×ˢ W) f := by
    simpa only [f, ell, scalarOnE_def] using hkregular.1
  have hconc : ∀ s ∈ S, ConcaveOn ℝ W (fun z => f (s, z) - A z z / 2) := by
    simpa only [f, ell, scalarOnE_def] using hkregular.2
  have hB : LocallyIntegrableOn B (S ×ˢ W) (volume.prod μ) :=
    hkB S W hS hW hSpos hWt hWInv hlip
  refine ⟨hlip, hB, ?_, ?_⟩
  · intro i j
    exact locallyIntegrableOn_poleEndpoint_redLength_chart_laplacian_flux
      F hcar hreg b hbmem tau q hsigma Phi R bf hsrc htgt p0 a (co.φ (rho k))
      hS hW (fun s hs => mem_Ici.mpr (le_of_lt (mem_Ioi.mp (hSpos hs)))) hWt hlip i j
  · exact hklocal S W hS hW hSpos hWt hWInv hlip A hconc hB

end HalfLineMetricConvergenceData

end DifferentialGeometry.CheegerGromovCompactness
