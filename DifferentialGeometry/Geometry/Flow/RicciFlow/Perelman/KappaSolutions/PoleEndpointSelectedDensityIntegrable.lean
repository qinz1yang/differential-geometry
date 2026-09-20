import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.PoleEndpointSelectedMassConvergence
import Mathlib.MeasureTheory.Function.L1Space.Integrable


noncomputable section

namespace DifferentialGeometry.CheegerGromovCompactness

open Filter MeasureTheory Set
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.PDE.RicciFlow.Perelman
open DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions
open CanonicalNeighborhood
open scoped Manifold ContDiff _root_.Topology ENNReal

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

theorem HalfLineMetricConvergenceData.integrable_poleEndpoint_redDensity_of_redLength
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
    {s : ℝ} (hs : 1 ≤ s)
    (hcomplete : MetricComplete (I := I)
      ({ P with metric := co.gInf (1 - s) } : PointedRiemannianManifold (I := I))) :
    Integrable (fun y : P.M => Real.exp (-ell (y, ⟨s, hs⟩) -
      ((Module.finrank ℝ E : ℝ) / 2) * Real.log s -
      ((Module.finrank ℝ E : ℝ) / 2) * Real.log (4 * Real.pi)))
      (riemannianVolumeMeasure (I := I) (M := P.M) (co.gInf (1 - s))) := by
  have hell : Continuous (fun y : P.M => ell (y, ⟨s, hs⟩)) :=
    ell.continuous.comp (continuous_id.prodMk continuous_const)
  have hdensity : Continuous (fun y : P.M => Real.exp (-ell (y, ⟨s, hs⟩) -
      ((Module.finrank ℝ E : ℝ) / 2) * Real.log s -
      ((Module.finrank ℝ E : ℝ) / 2) * Real.log (4 * Real.pi))) :=
    Real.continuous_exp.comp ((hell.neg.sub continuous_const).sub continuous_const)
  refine ⟨hdensity.aestronglyMeasurable, ?_⟩
  apply (hasFiniteIntegral_iff_ofReal
    (Eventually.of_forall (fun y => Real.exp_nonneg _))).2
  have hmass := co.tendsto_poleEndpoint_redVolume_of_redLength
    F hcar hreg b hbmem tau q hsigma Phi kappa hancient p hbase psi hpsi ell hconv
    (sub_nonpos.mpr hs) hcomplete
  dsimp only at hmass
  have htime : 1 - (1 - s) = s := by ring
  simpa only [htime] using hmass.1

end DifferentialGeometry.CheegerGromovCompactness

end
