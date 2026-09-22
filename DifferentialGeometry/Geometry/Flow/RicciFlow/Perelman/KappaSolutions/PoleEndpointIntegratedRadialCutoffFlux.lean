import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.PoleEndpointRadialCutoffFlux
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.PoleEndpointUniformWeightedDensityLimit


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

theorem exists_uniform_redDensity_limit_radialDistanceCutoff_flux_lintegral_bound
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
        (∫⁻ y, ENNReal.ofReal |Real.exp (-ell (y, s) -
            ((Module.finrank ℝ E : ℝ) / 2) * Real.log (s : ℝ) -
            ((Module.finrank ℝ E : ℝ) / 2) * Real.log (4 * Real.pi)) *
          (co.gInf (1 - s)).inner y
            (gradientFun (co.gInf (1 - s)) (fun x => ell (x, s)) y)
            (gradientFun (co.gInf (1 - s))
              (radialDistanceCutoff (co.gInf (1 - a)) z r) y)|
          ∂riemannianVolumeMeasure (I := I) (M := P.M) (co.gInf (1 - s))) ≤
        ENNReal.ofReal (C / r) := by
  obtain ⟨C, hC, hweight⟩ :=
    HalfLineMetricConvergenceData.exists_uniform_poleEndpoint_sqrt_redLength_limit_integral_bound
      F hcar hreg b hbmem tau q hsigma Phi co kappa hancient p hbase psi hpsi ell hconv
      ha hac hcomplete
  let K : ℝ := Real.sqrt 3 / Real.sqrt a
  have hK : 0 ≤ K := by positivity
  refine ⟨K * C.toReal, mul_nonneg hK ENNReal.toReal_nonneg, ?_⟩
  intro z s hs r hr
  have hpointConv (x : P.M) : Tendsto
      (fun k => redLength ((U).term (phi (co.φ (psi k)))).S 0 p
        (Phi.map (co.φ (psi k)) x) (s : ℝ)) atTop (𝓝 (ell (x, s))) := by
    have hp := hconv.tendstoLocallyUniformlyOn.tendsto_at
      (a := (x, s)) (mem_univ (x, s))
    exact hp
  have hpoint (y : P.M) :=
    HalfLineMetricConvergenceData.abs_redDensity_limit_mul_inner_radialDistanceCutoff_le
      F hcar hreg b hbmem tau q hsigma Phi co kappa hancient p
      (a := a) (s := (s : ℝ)) ha hs.1 psi hpsi.tendsto_atTop
      (fun x => ell (x, s)) hpointConv (hcomplete s hs) z hr y
  have hKR : 0 ≤ K / r := div_nonneg hK hr.le
  calc
    _ ≤ ∫⁻ y, ENNReal.ofReal ((K / r) *
        (Real.sqrt (ell (y, s)) * Real.exp (-ell (y, s) -
          ((Module.finrank ℝ E : ℝ) / 2) * Real.log (s : ℝ) -
          ((Module.finrank ℝ E : ℝ) / 2) * Real.log (4 * Real.pi))))
        ∂riemannianVolumeMeasure (I := I) (M := P.M) (co.gInf (1 - s)) :=
      lintegral_mono fun y => ENNReal.ofReal_le_ofReal (hpoint y)
    _ = ENNReal.ofReal (K / r) *
        (∫⁻ y, ENNReal.ofReal (Real.sqrt (ell (y, s)) * Real.exp (-ell (y, s) -
          ((Module.finrank ℝ E : ℝ) / 2) * Real.log (s : ℝ) -
          ((Module.finrank ℝ E : ℝ) / 2) * Real.log (4 * Real.pi)))
        ∂riemannianVolumeMeasure (I := I) (M := P.M) (co.gInf (1 - s))) := by
      simp_rw [ENNReal.ofReal_mul hKR]
      exact lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
    _ ≤ ENNReal.ofReal (K / r) * C := mul_le_mul_right (hweight s hs) _
    _ = ENNReal.ofReal (K / r) * ENNReal.ofReal C.toReal := by
      rw [ENNReal.ofReal_toReal hC.ne]
    _ = ENNReal.ofReal ((K / r) * C.toReal) := (ENNReal.ofReal_mul hKR).symm
    _ = ENNReal.ofReal ((K * C.toReal) / r) := congrArg ENNReal.ofReal (by ring)

end HalfLineMetricConvergenceData

end DifferentialGeometry.CheegerGromovCompactness

end
