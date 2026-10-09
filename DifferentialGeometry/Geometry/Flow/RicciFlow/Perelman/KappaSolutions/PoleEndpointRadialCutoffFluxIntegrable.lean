import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.PoleEndpointIntegratedRadialCutoffFlux
import DifferentialGeometry.Analysis.Integration.Measure.GradientPairing


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

namespace HalfLineMetricConvergenceData

theorem exists_uniform_redDensity_limit_radialDistanceCutoff_flux_integral_bound
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
      ({ P with metric := co.gInf (1 - s) } : PointedRiemannianManifold (I := I))) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ z : P.M,
      ∀ s : Ici (1 : ℝ), (s : ℝ) ∈ Icc a c → ∀ r : ℝ, 0 < r →
        Integrable (fun y => Real.exp (-ell (y, s) -
            ((Module.finrank ℝ E : ℝ) / 2) * Real.log (s : ℝ) -
            ((Module.finrank ℝ E : ℝ) / 2) * Real.log (4 * Real.pi)) *
          (co.gInf (1 - s)).inner y
            (gradientFun (co.gInf (1 - s)) (fun x => ell (x, s)) y)
            (gradientFun (co.gInf (1 - s))
              (radialDistanceCutoff (co.gInf (1 - a)) z r) y))
          (riemannianVolumeMeasure (I := I) (M := P.M) (co.gInf (1 - s))) ∧
        |∫ y, Real.exp (-ell (y, s) -
            ((Module.finrank ℝ E : ℝ) / 2) * Real.log (s : ℝ) -
            ((Module.finrank ℝ E : ℝ) / 2) * Real.log (4 * Real.pi)) *
          (co.gInf (1 - s)).inner y
            (gradientFun (co.gInf (1 - s)) (fun x => ell (x, s)) y)
            (gradientFun (co.gInf (1 - s))
              (radialDistanceCutoff (co.gInf (1 - a)) z r) y)
          ∂riemannianVolumeMeasure (I := I) (M := P.M) (co.gInf (1 - s))| ≤ C / r := by
  obtain ⟨C, hC, hbound⟩ :=
    co.exists_uniform_redDensity_limit_radialDistanceCutoff_flux_lintegral_bound
      F hcar hreg b hbmem tau q hsigma Phi kappa hancient p hbase psi hpsi ell hconv
      ha hac hcomplete
  refine ⟨C, hC, ?_⟩
  intro z s hs r hr
  let flux : P.M → ℝ := fun y => Real.exp (-ell (y, s) -
            ((Module.finrank ℝ E : ℝ) / 2) * Real.log (s : ℝ) -
            ((Module.finrank ℝ E : ℝ) / 2) * Real.log (4 * Real.pi)) *
          (co.gInf (1 - s)).inner y
            (gradientFun (co.gInf (1 - s)) (fun x => ell (x, s)) y)
            (gradientFun (co.gInf (1 - s))
              (radialDistanceCutoff (co.gInf (1 - a)) z r) y)
  let μ := riemannianVolumeMeasure (I := I) (M := P.M) (co.gInf (1 - s))
  change Integrable flux μ ∧ |∫ y, flux y ∂μ| ≤ C / r
  have hell : Continuous (fun y : P.M => ell (y, s)) :=
    ell.continuous.comp (continuous_id.prodMk continuous_const)
  have hdensity : Measurable (fun y : P.M => Real.exp (-ell (y, s) -
      ((Module.finrank ℝ E : ℝ) / 2) * Real.log (s : ℝ) -
      ((Module.finrank ℝ E : ℝ) / 2) * Real.log (4 * Real.pi))) :=
    (Real.continuous_exp.comp
      ((hell.neg.sub continuous_const).sub continuous_const)).measurable
  have hmeas : AEStronglyMeasurable flux μ := by
    have hm := hdensity.mul (measurable_inner_gradientFun (co.gInf (1 - s))
      (fun y => ell (y, s)) (radialDistanceCutoff (co.gInf (1 - a)) z r))
    exact hm.aemeasurable.aestronglyMeasurable
  have hlintegral : (∫⁻ y, ENNReal.ofReal |flux y| ∂μ) ≤ ENNReal.ofReal (C / r) :=
    hbound z s hs r hr
  have hintegrable : Integrable flux μ := by
    refine ⟨hmeas, (hasFiniteIntegral_iff_norm flux).mpr ?_⟩
    simpa only [Real.norm_eq_abs] using hlintegral.trans_lt ENNReal.ofReal_lt_top
  refine ⟨hintegrable, ?_⟩
  have hreal := ENNReal.toReal_mono ENNReal.ofReal_ne_top hlintegral
  rw [ENNReal.toReal_ofReal (div_nonneg hC hr.le)] at hreal
  have hnorm := norm_integral_le_lintegral_norm (μ := μ) flux
  rw [Real.norm_eq_abs] at hnorm
  exact hnorm.trans hreal

end HalfLineMetricConvergenceData

end DifferentialGeometry.CheegerGromovCompactness

end
