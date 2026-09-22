import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.PoleEndpointRadialCutoffTimeIntegral
import DifferentialGeometry.Analysis.Integration.Integral.WeightedFluxLimit


noncomputable section

namespace DifferentialGeometry.CheegerGromovCompactness

open Filter MeasureTheory Set
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Operator
open DifferentialGeometry.Geometry.Riemannian
open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.PDE.RicciFlow.Perelman
open DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions
open CanonicalNeighborhood
open scoped _root_.Manifold ContDiff _root_.Topology ENNReal

universe u uE uH

variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]
  {H : Type uH} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {D : RealTimeInterval} (F : PointedFlowData.{u, uE, uH} (I := I) D)
  (hcar : D.carrier = Iic 0) (hreg : D.regular = Iio 0)
  (b : ℝ) (hbmem : b ∈ D.carrier) (tau : ℕ → ℝ) (q : ℕ → F.M)
  (hsigma : ∀ i, 0 < tau i + b)
  {P : PointedRiemannianManifold.{u, uE, uH} (I := I)} {phi : ℕ → ℕ}

private local instance : CompleteSpace E := FiniteDimensional.complete ℝ E
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

theorem tendsto_integral_mul_redDensity_limit_radialDistanceCutoff_flux
    [ConnectedSpace P.M]
    (Phi : PointedCGHMaps Y P phi) {R : SmoothRiemannianMetric I P.M}
    {bf : BumpFamily Phi} {hsrc : SourceIsSigmaCompact Phi} {htgt : TargetIsSigmaCompact Phi}
    (co : HalfLineMetricConvergenceData Phi R bf hsrc htgt)
    (kappa : ℕ → ℝ) (hancient : ∀ i, IsAncientKappaSolution (kappa i) ((U).term i))
    (p : F.M) {A : ℝ}
    (hbase : ∀ i, redLength ((U).term i).S 0 p (q i) 1 ≤ A)
    (psi : ℕ → ℕ) (hpsi : StrictMono psi) (ell : C(P.M × Ici (1 : ℝ), ℝ))
    (hconv : TendstoLocallyUniformly
      (fun k (z : P.M × Ici (1 : ℝ)) =>
        redLength ((U).term (phi (co.φ (psi k)))).S 0 p
          (Phi.map (co.φ (psi k)) z.1) z.2) ell atTop)
    {a c : ℝ} (ha : 1 ≤ a) (hac : a ≤ c)
    (hcomplete : ∀ s ∈ Icc a c, MetricComplete (I := I)
      ({ P with metric := co.gInf (1 - s) } : PointedRiemannianManifold (I := I)))
    (z : P.M) (eta : Ioo a c → ℝ) (heta : AEStronglyMeasurable eta volume)
    {K : ℝ} (hetabound : ∀ᵐ s ∂volume, |eta s| ≤ K)
    {ι : Type*} {l : Filter ι} {radii : ι → ℝ} (hradii : Tendsto radii l atTop) :
    let flux := fun (r : ℝ) (s : Ioo a c) (y : P.M) =>
        Real.exp (-ell (y, (⟨(s : ℝ), ha.trans s.property.1.le⟩ : Ici (1 : ℝ))) -
          ((Module.finrank ℝ E : ℝ) / 2) * Real.log (s : ℝ) -
          ((Module.finrank ℝ E : ℝ) / 2) * Real.log (4 * Real.pi)) *
        (co.gInf (1 - (s : ℝ))).inner y
          (gradientFun (co.gInf (1 - (s : ℝ)))
            (fun x => ell (x, (⟨(s : ℝ), ha.trans s.property.1.le⟩ : Ici (1 : ℝ)))) y)
          (gradientFun (co.gInf (1 - (s : ℝ)))
            (radialDistanceCutoff (co.gInf (1 - a)) z r) y)
    Tendsto (fun i => ∫ s : Ioo a c, eta s *
      ∫ y, flux (radii i) s y
        ∂riemannianVolumeMeasure (I := I) (M := P.M) (co.gInf (1 - (s : ℝ)))) l (𝓝 0) := by
  intro flux
  obtain ⟨_, _, htime⟩ :=
    co.exists_uniform_redDensity_limit_radialDistanceCutoff_time_integral_bound
      F hcar hreg b hbmem tau q hsigma Phi kappa hancient p hbase psi hpsi ell hconv
      ha hac hcomplete
  obtain ⟨C, _, hspatial⟩ :=
    co.exists_uniform_redDensity_limit_radialDistanceCutoff_flux_integral_bound
      F hcar hreg b hbmem tau q hsigma Phi kappa hancient p hbase psi hpsi ell hconv
      ha hac hcomplete
  let innerFlux : ℝ → Ioo a c → ℝ := fun r s => ∫ y, flux r s y
    ∂riemannianVolumeMeasure (I := I) (M := P.M) (co.gInf (1 - (s : ℝ)))
  have hF (r : ℝ) (hr : 0 < r) : Integrable (innerFlux r) volume :=
    (htime z r hr).2.1
  have hb (r : ℝ) (hr : 0 < r) : ∀ᵐ s ∂volume, |innerFlux r s| ≤ C / r := by
    filter_upwards [] with s
    exact (hspatial z ⟨(s : ℝ), ha.trans s.property.1.le⟩
      ⟨s.property.1.le, s.property.2.le⟩ r hr).2
  let : IsFiniteMeasure (volume : Measure (Ioo a c)) := ⟨by
    rw [MeasureTheory.Measure.Subtype.volume_univ measurableSet_Ioo.nullMeasurableSet]
    exact measure_Ioo_lt_top⟩
  exact tendsto_integral_mul_of_uniform_abs_bound_div hF hb heta hetabound hradii

end HalfLineMetricConvergenceData

end DifferentialGeometry.CheegerGromovCompactness

end
