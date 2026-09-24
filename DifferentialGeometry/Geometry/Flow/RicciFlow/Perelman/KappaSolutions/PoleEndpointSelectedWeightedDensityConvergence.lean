import DifferentialGeometry.Geometry.Flow.RicciFlow.Compactness.Fields.Open.HalfLineConvergence
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.PoleEndpointDensityConvergence
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.PoleEndpointWeightedDensityConvergence
import Mathlib.Topology.ContinuousMap.CompactlySupported


noncomputable section

namespace DifferentialGeometry.CheegerGromovCompactness

open Filter MeasureTheory Set
open DifferentialGeometry.Geometry.Curvature
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

theorem tendsto_lintegral_poleEndpoint_sqrt_redLength_mul_redDensity_of_redLength
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
    {t : ℝ} (ht : t ≤ 0)
    (hcomplete : MetricComplete (I := I)
      ({ P with metric := co.gInf t } : PointedRiemannianManifold (I := I))) :
    let lag : Ici (1 : ℝ) := ⟨1 - t, by change 1 ≤ 1 - t; linarith⟩
    (∀ y, 0 ≤ ell (y, lag)) ∧
    Integrable (fun y => Real.sqrt (ell (y, lag)) * Real.exp (-ell (y, lag) -
      ((Module.finrank ℝ E : ℝ) / 2) * Real.log (1 - t) -
      ((Module.finrank ℝ E : ℝ) / 2) * Real.log (4 * Real.pi)))
      (riemannianVolumeMeasure (I := I) (M := P.M) (co.gInf t)) ∧
    Tendsto (fun k => ∫⁻ y : F.M,
      ENNReal.ofReal (Real.sqrt (redLength ((U).term (phi (co.φ (psi k)))).S 0 p y (1 - t)) *
        redDensity ((U).term (phi (co.φ (psi k)))).S 0 p y (1 - t))
        ∂riemannianVolumeMeasure (I := I) (M := F.M)
          (((U).term (phi (co.φ (psi k)))).S.base.metric (-(1 - t)))) atTop
      (𝓝 (∫⁻ y, ENNReal.ofReal (Real.sqrt (ell (y, lag)) * Real.exp (-ell (y, lag) -
        ((Module.finrank ℝ E : ℝ) / 2) * Real.log (1 - t) -
        ((Module.finrank ℝ E : ℝ) / 2) * Real.log (4 * Real.pi)))
        ∂riemannianVolumeMeasure (I := I) (M := P.M) (co.gInf t))) := by
  dsimp only
  let lag : Ici (1 : ℝ) := ⟨1 - t, by change 1 ≤ 1 - t; linarith⟩
  let co' := co.compSubseq Phi psi hpsi
  have hslice : Continuous (fun y : P.M => (y, lag)) :=
    continuous_id.prodMk continuous_const
  have hell : Continuous (fun y : P.M => ell (y, lag)) := ell.continuous.comp hslice
  have hcost : TendstoLocallyUniformly
      (fun k y => redLength ((U).term (phi (co'.φ k))).S 0 p
        (Phi.map (co'.φ k) y) (1 - t)) (fun y => ell (y, lag)) atTop := by
    simpa only [Function.comp_def, co', HalfLineMetricConvergenceData.compSubseq, lag]
      using hconv.comp (fun y : P.M => (y, lag)) hslice
  have hmain :=
    HalfLineMetricConvergenceData.tendsto_lintegral_poleEndpoint_sqrt_redLength_mul_redDensity
      F hcar hreg b hbmem tau q hsigma Phi co' kappa hancient p hbase ht hcomplete
      (fun y => ell (y, lag)) hell hcost
  simpa only [co', HalfLineMetricConvergenceData.compSubseq, Function.comp_apply, lag] using hmain

end HalfLineMetricConvergenceData

end DifferentialGeometry.CheegerGromovCompactness

end
