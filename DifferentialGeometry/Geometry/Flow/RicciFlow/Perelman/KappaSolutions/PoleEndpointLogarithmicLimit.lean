import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.PoleEndpointLogarithmicResidualConvergence
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.PoleEndpointGradientResidual
import DifferentialGeometry.Topology.Compactness.ProductInterval

noncomputable section

namespace DifferentialGeometry.CheegerGromovCompactness

open Filter Set TopologicalSpace MeasureTheory
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

theorem integrable_and_integral_poleEndpoint_logarithmic_nonneg_of_source_inequalities
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
    (x : P.M) {W : Set E} (hW : IsOpen W)
    (hWt : W ⊆ (extChartAt I x).target)
    (hWJ : MapsTo (extChartAt I x).symm W J)
    (test : ℝ × E → ℝ) (htest : ContDiff ℝ 2 test)
    (htestc : HasCompactSupport test) (hsupport : tsupport test ⊆ Ioo a c ×ˢ W)
    (hsource :
      let μ := modelHaar (E := E)
      let g := fun k s => gSeqExt Phi R bf hsrc htgt (co.φ (rho k)) (1 - s)
      let l := fun k y s => redLength ((U).term (phi (co.φ (rho k)))).S 0 p
        (Phi.map (co.φ (rho k)) y) s
      let r := fun k (z : ℝ × E) =>
        -(1 / 2 : ℝ) * ((U).term (phi (co.φ (rho k)))).S.scalar (-z.1)
          (Phi.map (co.φ (rho k)) ((extChartAt I x).symm z.2)) +
          ((Module.finrank ℝ E : ℝ) - l k ((extChartAt I x).symm z.2) z.1) / (2 * z.1)
      ∀ᶠ k in atTop, 0 ≤ ∫ z : ℝ × E,
        chartDensityOnE (g k z.1) x z.2 *
            ((1 / 2 : ℝ) * normGradSqFun (g k z.1) (fun y => l k y z.1)
              ((extChartAt I x).symm z.2) + r k z) * test z +
          (∑ ij : Fin (Module.finrank ℝ E) × Fin (Module.finrank ℝ E),
            (chartDensityOnE (g k z.1) x z.2 *
              chartInvGramOnE (g k z.1) x ij.1 ij.2 z.2) *
              fderiv ℝ (scalarOnE (I := I) x (fun y => l k y z.1)) z.2
                (DifferentialGeometry.Tensor.Coordinates.chartModelBasis E ij.1) *
              fderiv ℝ test z (0, DifferentialGeometry.Tensor.Coordinates.chartModelBasis E ij.2))
                ∂volume.prod μ) :
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
  obtain ⟨a', c', K, haa, hcc, hK, hKW, hsupp⟩ :=
    htestc.exists_subset_closed_interval_prod hsupport
  let w : E × ℝ → ℝ := fun z => test z.swap
  let v : E × ℝ → E →L[ℝ] ℝ := fun z =>
    (fderiv ℝ w z).comp (ContinuousLinearMap.inl ℝ E ℝ)
  have hwSmooth : ContDiff ℝ 2 w := htest.comp (contDiff_snd.prodMk contDiff_fst)
  have hw : ContinuousOn w (K ×ˢ Icc a' c') := hwSmooth.continuous.continuousOn
  have hv : ContinuousOn v (K ×ˢ Icc a' c') :=
    ((hwSmooth.continuous_fderiv (by norm_num)).clm_comp continuous_const).continuousOn
  have hlim := integral_poleEndpoint_logarithmic_residual_nonneg_of_source_inequalities
    F hcar hreg b hbmem tau q hsigma Phi R hR bf hsrc htgt co hcomplete hboundary
    kappa hF p hJ ha hbase rho hrho ell hconv x hW hK hKW hWt hWJ haa hcc w hw v hv
  have hsourceEq := eventually_integral_poleEndpoint_redLength_chart_laplacian_eq_gradient
    F hcar hreg b hbmem tau q hsigma Phi R hR co kappa hF p hJ ha.le hbase
    rho hrho x hW hK hKW hWt hWJ haa hcc
  have htarget := integrable_poleEndpoint_logarithmic_residual_iff_and_integral_eq_joint
    F hcar hreg b hbmem tau q hsigma Phi R hR co kappa hF p hJ ha.le hbase
    rho hrho ell hconv x hW hK hKW hWt hWJ haa hcc test
      (htest.differentiable (by norm_num)) hsupp
  have hselected := hlim (by
    filter_upwards [hsource, hsourceEq] with k hk heq
    rw [heq test (htest.differentiable (by norm_num)) hsupp] at hk
    simpa only [w, v, chartDensityOnE, sub_eq_add_neg, neg_mul, add_assoc,
      Prod.fst_swap, Prod.snd_swap] using hk)
  refine ⟨htarget.1.mpr hselected.1, ?_⟩
  rw [htarget.2]
  exact hselected.2

end HalfLineMetricConvergenceData

end DifferentialGeometry.CheegerGromovCompactness
