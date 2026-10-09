import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.PoleEndpointHamiltonJacobiLimitAE
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.PoleEndpointJointDifferentiability

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

private local instance covectorNormedAddCommGroup : NormedAddCommGroup (E →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedAddCommGroup

private local instance covectorNormedSpace : NormedSpace ℝ (E →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedSpace

private local instance covectorDualNormedAddCommGroup : NormedAddCommGroup ((E →L[ℝ] ℝ) →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedAddCommGroup

private local instance covectorDualNormedSpace : NormedSpace ℝ ((E →L[ℝ] ℝ) →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedSpace

private local instance covectorBilinNormedAddCommGroup :
    NormedAddCommGroup ((E →L[ℝ] ℝ) →L[ℝ] (E →L[ℝ] ℝ) →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedAddCommGroup

private local instance covectorBilinNormedSpace :
    NormedSpace ℝ ((E →L[ℝ] ℝ) →L[ℝ] (E →L[ℝ] ℝ) →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedSpace

namespace HalfLineMetricConvergenceData

theorem ae_poleEndpoint_redLength_limit_hamilton_jacobi_time_chart
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
    (hWJ : MapsTo (extChartAt I x).symm W J) :
    let ν := (volume : Measure ℝ).prod
      (DifferentialGeometry.Integral.Measure.modelHaar (E := E))
    let f := fun z : ℝ × E => ell ((extChartAt I x).symm z.2, z.1)
    let d := fun z => fderiv ℝ (fun y : E => f (z.1, y)) z.2
    ∀ᵐ z ∂ν, z ∈ Ioo a c ×ˢ W →
      deriv (fun t : ℝ => f (t, z.2)) z.1 + (1 / 2 : ℝ) *
        chartGradientBilin (co.gInf (1 - z.1)) x
          ((extChartAt I x).symm z.2) (d z) (d z) -
      (1 / 2 : ℝ) *
        metricScalarAt (co.gInf (1 - z.1)) ((extChartAt I x).symm z.2) +
      f z / (2 * z.1) = 0 := by
  let f : E × ℝ → ℝ := fun z => ell ((extChartAt I x).symm z.1, z.2)
  have hEq := ae_poleEndpoint_redLength_limit_hamilton_jacobi
    F hcar hreg b hbmem tau q hsigma Phi R hR bf hsrc htgt co hcomplete hboundary
    kappa hF p hJ ha hbase rho hrho ell hconv x hW hWt hWJ
  have hDiff := ae_differentiableAt_poleEndpoint_redLength_limit_chart
    F hcar hreg b hbmem tau q hsigma Phi R hR co kappa hF p hJ ha.le hbase
    rho hrho ell hconv x hW hWt hWJ
  have hswap := (Measure.measurePreserving_swap
    (μ := (volume : Measure ℝ))
    (ν := DifferentialGeometry.Integral.Measure.modelHaar (E := E))).quasiMeasurePreserving
  filter_upwards [hswap.ae hEq, hswap.ae hDiff] with z heq hdiff hzo
  have hzOld : (z.2, z.1) ∈ W ×ˢ Ioo a c := ⟨hzo.2, hzo.1⟩
  have hd : DifferentiableAt ℝ f (z.2, z.1) := hdiff hzOld
  have ht : deriv (fun t : ℝ => ell ((extChartAt I x).symm z.2, t)) z.1 =
      fderiv ℝ f (z.2, z.1) (0, 1) := by
    simpa only [f, Function.comp_def, ContinuousLinearMap.comp_apply,
      ContinuousLinearMap.inr_apply] using
      (hd.hasFDerivAt.comp z.1
        (hasFDerivAt_prodMk_right (𝕜 := ℝ) z.2 z.1)).hasDerivAt.deriv
  have hs : fderiv ℝ (fun y : E => ell ((extChartAt I x).symm y, z.1)) z.2 =
      (fderiv ℝ f (z.2, z.1)).comp (ContinuousLinearMap.inl ℝ E ℝ) := by
    exact (hd.hasFDerivAt.comp z.2
      (hasFDerivAt_prodMk_left (𝕜 := ℝ) z.2 z.1)).fderiv
  change deriv (fun t : ℝ => ell ((extChartAt I x).symm z.2, t)) z.1 +
      (1 / 2 : ℝ) * chartGradientBilin (co.gInf (1 - z.1)) x
        ((extChartAt I x).symm z.2)
        (fderiv ℝ (fun y : E => ell ((extChartAt I x).symm y, z.1)) z.2)
        (fderiv ℝ (fun y : E => ell ((extChartAt I x).symm y, z.1)) z.2) -
      (1 / 2 : ℝ) * metricScalarAt (co.gInf (1 - z.1)) ((extChartAt I x).symm z.2) +
      ell ((extChartAt I x).symm z.2, z.1) / (2 * z.1) = 0
  rw [ht, hs]
  exact heq hzOld

end HalfLineMetricConvergenceData

end DifferentialGeometry.CheegerGromovCompactness
