import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.PoleEndpointLogarithmicLimit
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.PoleEndpointGlobalWeakLaplacian

noncomputable section

namespace DifferentialGeometry.CheegerGromovCompactness

open Filter Set TopologicalSpace _root_.MeasureTheory
open DifferentialGeometry.Analysis.Calculus
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Operator
open DifferentialGeometry.Tensor.Coordinates
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

private local instance spacetimeCotangentNormedAddCommGroup :
    NormedAddCommGroup ((E × ℝ) →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedAddCommGroup

private local instance spacetimeCotangentNormedSpace : NormedSpace ℝ ((E × ℝ) →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedSpace

namespace HalfLineMetricConvergenceData

theorem integrable_and_integral_poleEndpoint_logarithmic_nonneg
    [ConnectedSpace P.M]
    (Phi : PointedCGHMaps Y P phi)
    (R : SmoothRiemannianMetric I P.M) (hR : RiemannianMetricComplete R)
    (bf : BumpFamily Phi) (hsrc : SourceIsSigmaCompact Phi) (htgt : TargetIsSigmaCompact Phi)
    (co : HalfLineMetricConvergenceData Phi R bf hsrc htgt)
    (hcomplete : MetricComplete
      ({ P with metric := co.gInf 0 } : PointedRiemannianManifold I))
    (hboundary : BoundarylessManifold I P.M)
    (hb : b < 0) {kappa0 : ℝ} (hAncient : IsAncientKappaSolution kappa0 F)
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
    (x : P.M) {W : Set E} (hW : IsOpen W)
    (hWt : W ⊆ (extChartAt I x).target)
    (hWJ : MapsTo (extChartAt I x).symm W J)
    (test : ℝ × E → ℝ) (htest : ContDiff ℝ 2 test)
    (htestc : HasCompactSupport test) (hsupport : tsupport test ⊆ Ioo a c ×ˢ W)
    (htestn : ∀ z, 0 ≤ test z) :
    let f := fun z : ℝ × E => ell ((extChartAt I x).symm z.2, z.1)
    let d := fun z => fderiv ℝ (fun y : E => f (z.1, y)) z.2
    let B := fun z => chartGradientBilin (co.gInf (1 - z.1)) x ((extChartAt I x).symm z.2)
    let density := fun z => chartDensity (co.gInf (1 - z.1)) x ((extChartAt I x).symm z.2)
    let S := fun z => metricScalarAt (co.gInf (1 - z.1)) ((extChartAt I x).symm z.2)
    let Q := fun z => density z *
      (((1 / 2 : ℝ) * B z (d z) (d z) - (1 / 2 : ℝ) * S z +
        ((Module.finrank ℝ E : ℝ) - f z) / (2 * z.1)) * test z +
          B z (d z) (fderiv ℝ (fun y => test (z.1, y)) z.2))
    Integrable Q ((volume : Measure ℝ).prod (modelHaar (E := E))) ∧
      0 ≤ ∫ z, Q z ∂(volume : Measure ℝ).prod (modelHaar (E := E)) := by
  apply integrable_and_integral_poleEndpoint_logarithmic_nonneg_of_source_inequalities
    F hcar hreg b hbmem tau q hsigma Phi R hR bf hsrc htgt co hcomplete hboundary
    kappa hF p hJ ha hbase rho hrho ell hconv x hW hWt hWJ test htest htestc hsupport
  have hsource := eventually_integrable_integral_poleEndpoint_redLength_chart_laplacian_nonneg
    F hcar hreg b hbmem tau q hsigma Phi R hR bf hsrc htgt co hcomplete hboundary
    (hb := hb) (kappa := kappa0) (hF := hAncient) (kappaSeq := kappa) (hseq := hF)
    (p0 := p) (a := x) (hδ := ha) hbase rho hrho hW hWt
    (μ := modelHaar (E := E)) htest htestc hsupport htestn
  have hscalar_generic (L : P.M → ℝ) (z : E) :
      scalarOnE (I := I) x L z = L ((extChartAt I x).symm z) := rfl
  have hfd_generic (L : P.M → ℝ) :
      fderiv ℝ (fun z : E => scalarOnE (I := I) x L z) =
        fderiv ℝ (fun z : E => L ((extChartAt I x).symm z)) := by
    rfl
  filter_upwards [hsource] with k hk
  simpa only [hscalar_generic, hfd_generic, sub_eq_add_neg, neg_mul, add_assoc] using hk.2

theorem integrable_and_integral_poleEndpoint_logarithmic_nonneg_of_isCompact_closure
    [ConnectedSpace P.M]
    (Phi : PointedCGHMaps Y P phi)
    (R : SmoothRiemannianMetric I P.M) (hR : RiemannianMetricComplete R)
    (bf : BumpFamily Phi) (hsrc : SourceIsSigmaCompact Phi) (htgt : TargetIsSigmaCompact Phi)
    (co : HalfLineMetricConvergenceData Phi R bf hsrc htgt)
    (hcomplete : MetricComplete
      ({ P with metric := co.gInf 0 } : PointedRiemannianManifold I))
    (hboundary : BoundarylessManifold I P.M)
    (hb : b < 0) {kappa0 : ℝ} (hAncient : IsAncientKappaSolution kappa0 F)
    (kappa : ℕ → ℝ) (hF : ∀ i, IsAncientKappaSolution (kappa i) ((U).term i))
    (p : F.M) {a c A : ℝ}
    (ha : 1 < a)
    (hbase : ∀ᶠ k in atTop, redLength ((U).term (phi (co.φ k))).S 0
      p (q (phi (co.φ k))) 1 ≤ A)
    (rho : ℕ → ℕ) (hrho : Tendsto rho atTop atTop)
    (ell : P.M × ℝ → ℝ)
    (hconv : ∀ y : P.M, ∀ t ∈ Icc a c,
      Tendsto (fun k => redLength ((U).term (phi (co.φ (rho k)))).S 0 p
        (Phi.map (co.φ (rho k)) y) t) atTop (𝓝 (ell (y, t))))
    (x : P.M) {W : Set E} (hW : IsOpen W)
    (hWc : IsCompact (closure W))
    (hWt : closure W ⊆ (extChartAt I x).target)
    (test : ℝ × E → ℝ) (htest : ContDiff ℝ 2 test)
    (htestc : HasCompactSupport test) (hsupport : tsupport test ⊆ Ioo a c ×ˢ W)
    (htestn : ∀ z, 0 ≤ test z) :
    let f := fun z : ℝ × E => ell ((extChartAt I x).symm z.2, z.1)
    let d := fun z => fderiv ℝ (fun y : E => f (z.1, y)) z.2
    let B := fun z => chartGradientBilin (co.gInf (1 - z.1)) x ((extChartAt I x).symm z.2)
    let density := fun z => chartDensity (co.gInf (1 - z.1)) x ((extChartAt I x).symm z.2)
    let S := fun z => metricScalarAt (co.gInf (1 - z.1)) ((extChartAt I x).symm z.2)
    let Q := fun z => density z *
      (((1 / 2 : ℝ) * B z (d z) (d z) - (1 / 2 : ℝ) * S z +
        ((Module.finrank ℝ E : ℝ) - f z) / (2 * z.1)) * test z +
          B z (d z) (fderiv ℝ (fun y => test (z.1, y)) z.2))
    Integrable Q ((volume : Measure ℝ).prod (modelHaar (E := E))) ∧
      0 ≤ ∫ z, Q z ∂(volume : Measure ℝ).prod (modelHaar (E := E)) := by
  let J : Set P.M := (extChartAt I x).symm '' closure W
  have hJ : IsCompact J := hWc.image_of_continuousOn
    ((continuousOn_extChartAt_symm x).mono hWt)
  have hWJ : MapsTo (extChartAt I x).symm W J := fun z hz =>
    mem_image_of_mem _ (subset_closure hz)
  exact integrable_and_integral_poleEndpoint_logarithmic_nonneg
    F hcar hreg b hbmem tau q hsigma Phi R hR bf hsrc htgt co hcomplete hboundary
    hb hAncient kappa hF p hJ ha hbase rho hrho ell (fun y _ t ht => hconv y t ht)
    x hW (subset_closure.trans hWt) hWJ test htest htestc hsupport htestn

end HalfLineMetricConvergenceData

end DifferentialGeometry.CheegerGromovCompactness
