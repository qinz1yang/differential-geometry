import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.PoleEndpointDensityAncientSmoothness
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.PoleEndpointChartGlobalResidual
import DifferentialGeometry.Analysis.Parabolic.WeakEquation.NormalizedDensity
import DifferentialGeometry.Geometry.Flow.RicciFlow.Compactness.Fields.Open.HalfLineWeakHeatPotential
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.PoleEndpointLimitCompleteness

noncomputable section

namespace DifferentialGeometry.CheegerGromovCompactness

open Filter _root_.MeasureTheory Set
open DifferentialGeometry.Geometry.Connection
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Operator
open DifferentialGeometry.Geometry.Riemannian
open DifferentialGeometry.Integral.Measure
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

private local instance : CompleteSpace E := FiniteDimensional.complete ℝ E
private local instance : MeasurableSpace E := borel E
private local instance : BorelSpace E := ⟨rfl⟩
private local instance : TopologicalSpace F.M := F.topology
private local instance : ChartedSpace H F.M := F.charted
private local instance : IsManifold I ∞ F.M := F.smooth
private local instance : SigmaCompactSpace F.M := F.sigmaCompact
private local instance : T2Space F.M := F.t2
private local instance : MeasurableSpace F.M := borel F.M
private local instance : BorelSpace F.M := ⟨rfl⟩

attribute [local instance] PointedRiemannianManifold.topology
  PointedRiemannianManifold.charted PointedRiemannianManifold.smooth
  PointedRiemannianManifold.t2 PointedRiemannianManifold.sigmaCompact

private local instance : MeasurableSpace P.M := borel P.M
private local instance : BorelSpace P.M := ⟨rfl⟩

local notation "U" => poleRescaledFlowSeq F hcar hreg b hbmem tau q hsigma
local notation "Y" => poleEndpointRescaledFlowSeq F hcar hreg b hbmem tau q hsigma

attribute [local instance] MeasureTheory.Measure.Subtype.measureSpace

namespace HalfLineMetricConvergenceData

open DifferentialGeometry.Analysis.Laplacian.MetricExtension
open DifferentialGeometry.Analysis.Sobolev.Chart
open DifferentialGeometry.Analysis.Sobolev.Euclidean
open DifferentialGeometry.Analysis.Parabolic

theorem isHeatPotOn_poleEndpoint_redDensity_limit_of_ancient
    [ConnectedSpace P.M]
    (Phi : PointedCGHMaps Y P phi)
    (R : SmoothRiemannianMetric I P.M) (hR : RiemannianMetricComplete R)
    (bf : BumpFamily Phi) (hsrc : SourceIsSigmaCompact Phi) (htgt : TargetIsSigmaCompact Phi)
    (co : HalfLineMetricConvergenceData Phi R bf hsrc htgt)
    (hcomplete : MetricComplete
      ({ P with metric := co.gInf 0 } : PointedRiemannianManifold I))
    (hboundary : BoundarylessManifold I P.M)
    (kappa : ℕ → ℝ) (hF : ∀ i, IsAncientKappaSolution (kappa i) ((U).term i))
    (hb : b < 0) {kappa0 : ℝ}
    (hAncient : IsAncientKappaSolution kappa0 F)
    (p : F.M) {A : ℝ}
    (hbase : ∀ i, redLength ((U).term i).S 0 p (q i) 1 ≤ A)
    (hescape : Tendsto tau atTop atTop) (hphi : StrictMono phi)
    (psi : ℕ → ℕ) (hpsi : StrictMono psi) (ellC : C(P.M × Ici (1 : ℝ), ℝ))
    (hconv : TendstoLocallyUniformly
      (fun k (z : P.M × Ici (1 : ℝ)) =>
        redLength ((U).term (phi (co.φ (psi k)))).S 0 p
          (Phi.map (co.φ (psi k)) z.1) z.2) ellC atTop)
    (ell : P.M × ℝ → ℝ)
    (hagree : ∀ (y : P.M) (t : ℝ) (ht : 1 ≤ t), ell (y, t) = ellC (y, ⟨t, ht⟩))
    (Dsol : RealTimeInterval) (hcarrier : Dsol.carrier ⊆ Ioi (1 : ℝ)) :
    let u : ℝ → P.M → ℝ := fun t x => Real.exp (-ell (x, t) -
      (Module.finrank ℝ E : ℝ) / 2 * Real.log t -
      (Module.finrank ℝ E : ℝ) / 2 * Real.log (4 * Real.pi))
    let G : MetricConnectionFamily (I := I) (M := P.M) ℝ :=
      { metric := fun t => co.gInf (1 - t)
        connection := fun t => leviCivitaConnectionOfMetric (I := I) (co.gInf (1 - t))
        metricCompatible := fun t =>
          leviCivitaConnectionOfMetric_isMetricCompatible (I := I) (co.gInf (1 - t)) }
    IsHeatPotOn Dsol G (fun t x => -metricScalarAt (co.gInf (1 - t)) x) u := by
  intro u G
  have hcompleteOn : ∀ t ∈ Ioi (1 : ℝ), MetricComplete (I := I)
      ({ P with metric := co.gInf (1 - t) } : PointedRiemannianManifold (I := I)) := by
    intro t ht
    exact metric_complete_poleEndpoint_limit_time_sub_of_ancient
      F hcar hreg b hbmem tau q hsigma Phi R co hAncient hcomplete ht.le
  have hu := contMDiffOn_poleEndpoint_redDensity_limit_of_ancient
    F hcar hreg b hbmem tau q hsigma Phi R hR bf hsrc htgt co
    hcomplete hboundary kappa hF hb hAncient p hbase hescape hphi
    psi hpsi ellC hconv ell hagree hcompleteOn
  let Dg := RealTimeInterval.openInfinite (1 : ℝ) 2 (by norm_num)
  have hYreg : Iio 0 ⊆ (Y).D.regular := fun _ ht => ht
  have hg : MetricFamilySmoothOn (I := I) Dg (fun t => co.gInf (1 - t)) :=
    co.metric_smooth_time_sub (Φ := Phi) hYreg 1 (fun _ ht => ht)
  apply co.isHeatPotOn_time_sub_of_chart_weighted_weak_equation
    (μ := (volume : Measure ℝ).prod (modelHaar (E := E))) Phi hYreg 1 Dsol
      isOpen_Ioi Subset.rfl hcarrier u hu
  intro α φ hφ hφc hφs
  apply chart_weighted_weak_equation_of_normalized_exponential_residual_eq_zero
    (μ := (volume : Measure ℝ).prod (modelHaar (E := E))) hg isOpen_Ioi
    (show Ioi (1 : ℝ) ⊆ Dg.regular from Subset.rfl)
    (fun t ht => show 0 < t from zero_lt_one.trans (show 1 < t from ht))
    ell (Module.finrank ℝ E) hu α φ hφ hφc hφs
  exact co.integral_poleEndpoint_redDensity_limit_chart_residual_eq_zero_on_Ioi_of_ancient
    F hcar hreg b hbmem tau q hsigma Phi R hR bf hsrc htgt
    hcomplete hboundary kappa hF hb hAncient p hbase hescape hphi
    psi hpsi ellC hconv ell hagree hcompleteOn α φ hφ hφc hφs

end HalfLineMetricConvergenceData

end DifferentialGeometry.CheegerGromovCompactness
