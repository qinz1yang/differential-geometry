import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.PoleEndpointSmoothHamiltonJacobi
import DifferentialGeometry.Topology.Manifold.CompactChartNeighborhood

noncomputable section

namespace DifferentialGeometry.CheegerGromovCompactness

open Filter Set TopologicalSpace _root_.MeasureTheory
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

theorem poleEndpoint_redLength_limit_hamilton_jacobi
    [ConnectedSpace P.M]
    (Phi : PointedCGHMaps Y P phi)
    (R : SmoothRiemannianMetric I P.M) (hR : RiemannianMetricComplete R)
    (bf : BumpFamily Phi) (hsrc : SourceIsSigmaCompact Phi) (htgt : TargetIsSigmaCompact Phi)
    (co : HalfLineMetricConvergenceData Phi R bf hsrc htgt)
    (hcomplete : MetricComplete
      ({ P with metric := co.gInf 0 } : PointedRiemannianManifold I))
    (hboundary : BoundarylessManifold I P.M)
    (kappa : ℕ → ℝ) (hF : ∀ i, IsAncientKappaSolution (kappa i) ((U).term i))
    (p : F.M) {A : ℝ}
    (hbase : ∀ᶠ k in atTop, redLength ((U).term (phi (co.φ k))).S 0
      p (q (phi (co.φ k))) 1 ≤ A)
    (rho : ℕ → ℕ) (hrho : Tendsto rho atTop atTop)
    (ell : P.M × ℝ → ℝ)
    (hconv : ∀ y : P.M, ∀ t ∈ Ioi (1 : ℝ),
      Tendsto (fun k => redLength ((U).term (phi (co.φ (rho k)))).S 0 p
        (Phi.map (co.φ (rho k)) y) t) atTop (𝓝 (ell (y, t))))
    (hell : ContMDiffOn (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) ∞
      (fun z : ℝ × P.M => ell (z.2, z.1)) (Ioi (1 : ℝ) ×ˢ univ)) :
    ∀ t ∈ Ioi (1 : ℝ), ∀ x : P.M,
      2 * deriv (fun s => ell (x, s)) t +
        (co.gInf (1 - t)).inner x
          (gradientFun (I := I) (co.gInf (1 - t)) (fun z => ell (z, t)) x)
          (gradientFun (I := I) (co.gInf (1 - t)) (fun z => ell (z, t)) x) -
        metricScalarAt (co.gInf (1 - t)) x + ell (x, t) / t = 0 := by
  intro t ht x
  obtain ⟨a, ha, hat⟩ := exists_between (show (1 : ℝ) < t from ht)
  have hxsrc : x ∈ (extChartAt I x).source := by
    rw [extChartAt_source_eq_chartAt_source (I := I)]
    exact mem_chart_source H x
  obtain ⟨W, hW, hWimage, hWclosure, _, hJ, _, hWJ⟩ :=
    exists_open_extChartAt_image_isCompact_closure (I := I) x
      (isCompact_singleton : IsCompact ({x} : Set P.M))
      (by simpa only [singleton_subset_iff] using hxsrc)
  let J := (extChartAt I x).symm '' closure W
  have hWtarget : W ⊆ (extChartAt I x).target := subset_closure.trans hWclosure
  have hchartx : extChartAt I x x ∈ W := hWimage (mem_image_of_mem _ (mem_singleton x))
  have hlocalconv : ∀ y ∈ J, ∀ s ∈ Icc a (t + 1),
      Tendsto (fun k => redLength ((U).term (phi (co.φ (rho k)))).S 0 p
        (Phi.map (co.φ (rho k)) y) s) atTop (𝓝 (ell (y, s))) := by
    intro y _ s hs
    exact hconv y s (ha.trans_le hs.1)
  have hlocalSmooth : ContMDiffOn (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) ∞
      (fun z : ℝ × P.M => ell (z.2, z.1)) (Ioo a (t + 1) ×ˢ univ) :=
    hell.mono (Set.prod_mono (fun s hs => ha.trans hs.1) Subset.rfl)
  have heq := poleEndpoint_redLength_limit_hamilton_jacobi_of_contMDiffOn
    F hcar hreg b hbmem tau q hsigma Phi R hR bf hsrc htgt co hcomplete hboundary
    kappa hF p hJ ha hbase rho hrho ell hlocalconv x hW hWtarget hWJ hlocalSmooth
    t ⟨hat, lt_add_one t⟩ (extChartAt I x x) hchartx
  have hnorm := congrArg (fun z : P.M => (co.gInf (1 - t)).inner z
    (gradientFun (I := I) (co.gInf (1 - t)) (fun w => ell (w, t)) z)
    (gradientFun (I := I) (co.gInf (1 - t)) (fun w => ell (w, t)) z))
    ((extChartAt I x).left_inv hxsrc)
  rw [hnorm] at heq
  simpa only [(extChartAt I x).left_inv hxsrc] using heq

end HalfLineMetricConvergenceData

end DifferentialGeometry.CheegerGromovCompactness
