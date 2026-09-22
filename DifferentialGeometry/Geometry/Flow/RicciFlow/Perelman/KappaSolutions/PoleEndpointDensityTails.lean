import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.RegularPoleRescalings
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.AncientReducedDensityTails
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.AncientReducedLengthTimeRatio
import DifferentialGeometry.Geometry.Flow.RicciFlow.Compactness.Fields.Open.HalfLineConvergence


noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions

open Filter MeasureTheory Set
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.CheegerGromovCompactness
open DifferentialGeometry.Integral.Measure
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

private local instance endpointTailComplete : CompleteSpace E :=
  FiniteDimensional.complete ℝ E
private local instance endpointTailTopology : TopologicalSpace F.M := F.topology
private local instance endpointTailCharted : ChartedSpace H F.M := F.charted
private local instance endpointTailSmooth : IsManifold I ∞ F.M := F.smooth
private local instance endpointTailSigma : SigmaCompactSpace F.M := F.sigmaCompact
private local instance endpointTailT2 : T2Space F.M := F.t2
private local instance endpointTailMeasurable : MeasurableSpace F.M := borel F.M
private local instance endpointTailBorel : BorelSpace F.M := ⟨rfl⟩

local notation "U" => poleRescaledFlowSeq F hcar hreg b hbmem tau q hsigma
local notation "Y" => poleEndpointRescaledFlowSeq F hcar hreg b hbmem tau q hsigma

theorem exists_uniform_poleEndpoint_redDensity_ball_tail
    (kappa : ℕ → ℝ) (hancient : ∀ i, IsAncientKappaSolution (kappa i) ((U).term i))
    (p : F.M) {A : ℝ}
    (hbase : ∀ i, redLength ((U).term i).S 0 p (q i) 1 ≤ A)
    {t : ℝ} (ht : t ≤ 0) {ε : ℝ≥0∞} (hε : 0 < ε) :
    ∃ r : ℝ, 0 ≤ r ∧ ∀ i,
      (∫⁻ y in (riemannianClosedBallOf (I := I) (M := F.M)
          (((Y).term i).S.base.metric t) (q i) r)ᶜ,
        ENNReal.ofReal (redDensity ((U).term i).S 0 p y (1 - t))
          ∂riemannianVolumeMeasure (I := I) (M := F.M)
            (((Y).term i).S.base.metric t)) < ε := by
  have hlag : 0 < 1 - t := by linarith
  let C : ℝ := max ((1 - t) ^ 2) ((1 / (1 - t)) ^ 2)
  have hC : 0 ≤ C := (sq_nonneg (1 - t)).trans (le_max_left _ _)
  have hcost (i : ℕ) : redLength ((U).term i).S 0 p (q i) (1 - t) ≤ C * A := by
    have hratio := ancient_redLength_le_mul_time_ratio ((U).term i) (hancient i)
      p (q i) zero_lt_one hlag
    simp only [div_one] at hratio
    exact hratio.trans (mul_le_mul_of_nonneg_left (hbase i) hC)
  obtain ⟨N, hN⟩ := exists_uniform_ancient_redDensity_closedBall_compl_bound
    (I := I) (a := 1 - t) (b := 1 - t) (B := C * A) hlag le_rfl hε
  refine ⟨(N : ℝ), Nat.cast_nonneg N, ?_⟩
  intro i
  have htail := hN ((U).term i) (hancient i) p (q i) ⟨le_rfl, le_rfl⟩ (hcost i)
  have htime : -(1 - t) = t - 1 := by ring
  rw [poleEndpointRescaledFlowSeq_metric_eq_shift, ← htime]
  exact htail

end DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions

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

private local instance endpointSourceTailComplete : CompleteSpace E :=
  FiniteDimensional.complete ℝ E
private local instance endpointSourceTailTopology : TopologicalSpace F.M := F.topology
private local instance endpointSourceTailCharted : ChartedSpace H F.M := F.charted
private local instance endpointSourceTailSmooth : IsManifold I ∞ F.M := F.smooth
private local instance endpointSourceTailSigma : SigmaCompactSpace F.M := F.sigmaCompact
private local instance endpointSourceTailT2 : T2Space F.M := F.t2
private local instance endpointSourceTailMeasurable : MeasurableSpace F.M := borel F.M
private local instance endpointSourceTailBorel : BorelSpace F.M := ⟨rfl⟩

attribute [local instance] PointedRiemannianManifold.topology
  PointedRiemannianManifold.charted PointedRiemannianManifold.smooth
  PointedRiemannianManifold.t2 PointedRiemannianManifold.sigmaCompact

local notation "U" => poleRescaledFlowSeq F hcar hreg b hbmem tau q hsigma
local notation "Y" => poleEndpointRescaledFlowSeq F hcar hreg b hbmem tau q hsigma

theorem HalfLineMetricConvergenceData.exists_poleEndpoint_redDensity_ball_tail
    (Phi : PointedCGHMaps Y P phi) {R : SmoothRiemannianMetric I P.M}
    {bf : BumpFamily Phi} {hsrc : SourceIsSigmaCompact Phi} {htgt : TargetIsSigmaCompact Phi}
    (co : HalfLineMetricConvergenceData Phi R bf hsrc htgt)
    (kappa : ℕ → ℝ) (hancient : ∀ i, IsAncientKappaSolution (kappa i) ((U).term i))
    (p : F.M) {A : ℝ}
    (hbase : ∀ i, redLength ((U).term i).S 0 p (q i) 1 ≤ A)
    {t : ℝ} (ht : t ≤ 0) {ε : ℝ≥0∞} (hε : 0 < ε) :
    ∃ r : ℝ, 0 ≤ r ∧ ∀ᶠ k in atTop,
      (∫⁻ y in (riemannianClosedBallOf (I := I) (M := F.M)
          (((Y).term (phi (co.φ k))).S.base.metric t)
          (Phi.map (co.φ k) P.basepoint) r)ᶜ,
        ENNReal.ofReal (redDensity ((U).term (phi (co.φ k))).S 0 p y (1 - t))
          ∂riemannianVolumeMeasure (I := I) (M := ((Y).term (phi (co.φ k))).M)
            (((Y).term (phi (co.φ k))).S.base.metric t)) < ε := by
  obtain ⟨r, hr, htail⟩ := exists_uniform_poleEndpoint_redDensity_ball_tail
    F hcar hreg b hbmem tau q hsigma kappa hancient p hbase ht hε
  refine ⟨r, hr, Filter.Eventually.of_forall ?_⟩
  intro k
  have hcenter : Phi.map (co.φ k) P.basepoint = q (phi (co.φ k)) :=
    Phi.basepoint_map (co.φ k)
  rw [hcenter]
  exact htail (phi (co.φ k))

end DifferentialGeometry.CheegerGromovCompactness

end
