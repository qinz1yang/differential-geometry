import DifferentialGeometry.Geometry.Flow.RicciFlow.Compactness.Fields.Open.HalfLineConvergence
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.PoleEndpointDensityConvergence
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.PoleEndpointWeightedDensityConvergence
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.PoleEndpointSelectedWeightedDensityConvergence
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.AncientUniformTimeRatio
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

theorem exists_uniform_poleEndpoint_sqrt_redLength_limit_integral_bound
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
    ∃ C : ℝ≥0∞, C < ⊤ ∧ ∀ s : Ici (1 : ℝ), (s : ℝ) ∈ Icc a c →
      (∫⁻ y, ENNReal.ofReal (Real.sqrt (ell (y, s)) * Real.exp (-ell (y, s) -
        ((Module.finrank ℝ E : ℝ) / 2) * Real.log (s : ℝ) -
        ((Module.finrank ℝ E : ℝ) / 2) * Real.log (4 * Real.pi)))
        ∂riemannianVolumeMeasure (I := I) (M := P.M) (co.gInf (1 - s))) ≤ C := by
  let K : ℝ := max (c ^ 2) ((1 / a) ^ 2)
  have ha0 : 0 < a := zero_lt_one.trans_le ha
  obtain ⟨C, hC, hbound⟩ :=
    exists_uniform_ancient_sqrt_redLength_mul_redDensity_integral_bound
      (I := I) (a := a) (b := c) (B := K * A) ha0 hac
  refine ⟨C, hC, ?_⟩
  intro s hs
  have ht : 1 - (s : ℝ) ≤ 0 := sub_nonpos.mpr s.property
  have hmass := tendsto_lintegral_poleEndpoint_sqrt_redLength_mul_redDensity_of_redLength
    F hcar hreg b hbmem tau q hsigma Phi co kappa hancient p hbase psi hpsi ell hconv
    ht (hcomplete s hs)
  have hlag : (1 : ℝ) - (1 - (s : ℝ)) = (s : ℝ) := by ring
  dsimp only at hmass
  have hmassConv := hmass.2.2
  simp only [hlag] at hmassConv
  apply le_of_tendsto hmassConv
  apply Eventually.of_forall
  intro k
  apply hbound ((U).term (phi (co.φ (psi k)))) (hancient (phi (co.φ (psi k))))
    p (q (phi (co.φ (psi k)))) hs
  exact ancient_redLength_le_uniform_time_ratio
    ((U).term (phi (co.φ (psi k)))) (hancient (phi (co.φ (psi k))))
    p (q (phi (co.φ (psi k)))) ha0 hs (hbase (phi (co.φ (psi k))))

end HalfLineMetricConvergenceData

end DifferentialGeometry.CheegerGromovCompactness

end
