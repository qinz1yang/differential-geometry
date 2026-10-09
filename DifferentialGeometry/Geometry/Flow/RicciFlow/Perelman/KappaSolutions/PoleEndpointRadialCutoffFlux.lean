import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.PoleEndpointGradientBound
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.PoleEndpointMetricOrder
import DifferentialGeometry.Geometry.Metric.Distance.RadialCutoff
import DifferentialGeometry.Geometry.Operator.Gradient.ChartPairing

noncomputable section

namespace DifferentialGeometry.CheegerGromovCompactness

open Filter Set
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.PDE.RicciFlow.Perelman
open DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions
open CanonicalNeighborhood
open DifferentialGeometry.Geometry.Operator
open DifferentialGeometry.Geometry.Riemannian
open DifferentialGeometry.Integral.DivergenceTheorem
open Tensor.Coordinates
open scoped _root_.Manifold ContDiff _root_.Topology ENNReal NNReal

universe u uE uH

variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace ℝ E]
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
private local instance : T2Space F.M := F.t2
private local instance : SigmaCompactSpace F.M := F.sigmaCompact

attribute [local instance] PointedRiemannianManifold.topology
  PointedRiemannianManifold.charted PointedRiemannianManifold.smooth
  PointedRiemannianManifold.t2 PointedRiemannianManifold.sigmaCompact

local notation "U" => poleRescaledFlowSeq F hcar hreg b hbmem tau q hsigma
local notation "Y" => poleEndpointRescaledFlowSeq F hcar hreg b hbmem tau q hsigma

theorem HalfLineMetricConvergenceData.abs_inner_redLength_limit_gradient_radialDistanceCutoff_le
    [ConnectedSpace P.M]
    (Phi : PointedCGHMaps Y P phi) {R : SmoothRiemannianMetric I P.M}
    {bf : BumpFamily Phi} {hsrc : SourceIsSigmaCompact Phi} {htgt : TargetIsSigmaCompact Phi}
    (co : HalfLineMetricConvergenceData Phi R bf hsrc htgt)
    (kappa : ℕ → ℝ) (hancient : ∀ i, IsAncientKappaSolution (kappa i) ((U).term i))
    (p : F.M) {a s : ℝ} (ha : 1 ≤ a) (has : a ≤ s)
    (rho : ℕ → ℕ) (hrho : Tendsto rho atTop atTop) (ell : P.M → ℝ)
    (hconv : ∀ y, Tendsto (fun k => redLength ((U).term (phi (co.φ (rho k)))).S 0 p
      (Phi.map (co.φ (rho k)) y) s) atTop (𝓝 (ell y)))
    (hcomplete : MetricComplete (I := I)
      ({ P with metric := co.gInf (1 - s) } : PointedRiemannianManifold (I := I)))
    (z : P.M) {r : ℝ} (hr : 0 < r) (x : P.M) :
    |(co.gInf (1 - s)).inner x
        (gradientFun (co.gInf (1 - s)) ell x)
        (gradientFun (co.gInf (1 - s))
          (radialDistanceCutoff (co.gInf (1 - a)) z r) x)| ≤
      (Real.sqrt 3 / Real.sqrt a / r) * Real.sqrt (ell x) := by
  have hg := co.redLength_limit_gradient_norm_le F hcar hreg b hbmem tau q hsigma
    Phi kappa hancient p (ha.trans has) rho hrho ell hconv hcomplete x
  have hc := gradient_radialDistanceCutoff_norm_le_of_metric_le
    (co.gInf (1 - a)) (co.gInf (1 - s))
    (co.metric_inner_le_at_reflected_times F hcar hreg b hbmem tau q hsigma
      Phi kappa hancient ha has) z hr x
  have hinner := DifferentialGeometry.SmoothRiemannianMetric.abs_metric_inner_le_sqrt_metric_quadratic
    (co.gInf (1 - s)) x
    (gradientFun (co.gInf (1 - s)) ell x)
    (gradientFun (co.gInf (1 - s)) (radialDistanceCutoff (co.gInf (1 - a)) z r) x)
  have ha0 : 0 < a := zero_lt_one.trans_le ha
  have hcoef : Real.sqrt 3 / Real.sqrt s ≤ Real.sqrt 3 / Real.sqrt a :=
    div_le_div_of_nonneg_left (Real.sqrt_nonneg 3) (Real.sqrt_pos.mpr ha0)
      (Real.sqrt_le_sqrt has)
  calc
    _ ≤ _ := hinner
    _ ≤ (Real.sqrt 3 / Real.sqrt s * Real.sqrt (ell x)) * (1 / r) :=
      mul_le_mul hg hc (Real.sqrt_nonneg _) (by positivity)
    _ ≤ (Real.sqrt 3 / Real.sqrt a * Real.sqrt (ell x)) * (1 / r) :=
      mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right hcoef (Real.sqrt_nonneg _)) (by positivity)
    _ = _ := by ring

theorem HalfLineMetricConvergenceData.abs_redDensity_limit_mul_inner_radialDistanceCutoff_le
    [ConnectedSpace P.M]
    (Phi : PointedCGHMaps Y P phi) {R : SmoothRiemannianMetric I P.M}
    {bf : BumpFamily Phi} {hsrc : SourceIsSigmaCompact Phi} {htgt : TargetIsSigmaCompact Phi}
    (co : HalfLineMetricConvergenceData Phi R bf hsrc htgt)
    (kappa : ℕ → ℝ) (hancient : ∀ i, IsAncientKappaSolution (kappa i) ((U).term i))
    (p : F.M) {a s : ℝ} (ha : 1 ≤ a) (has : a ≤ s)
    (rho : ℕ → ℕ) (hrho : Tendsto rho atTop atTop) (ell : P.M → ℝ)
    (hconv : ∀ y, Tendsto (fun k => redLength ((U).term (phi (co.φ (rho k)))).S 0 p
      (Phi.map (co.φ (rho k)) y) s) atTop (𝓝 (ell y)))
    (hcomplete : MetricComplete (I := I)
      ({ P with metric := co.gInf (1 - s) } : PointedRiemannianManifold (I := I)))
    (z : P.M) {r : ℝ} (hr : 0 < r) (x : P.M) :
    |Real.exp (-ell x - ((Module.finrank ℝ E : ℝ) / 2) * Real.log s -
        ((Module.finrank ℝ E : ℝ) / 2) * Real.log (4 * Real.pi)) *
      (co.gInf (1 - s)).inner x
        (gradientFun (co.gInf (1 - s)) ell x)
        (gradientFun (co.gInf (1 - s))
          (radialDistanceCutoff (co.gInf (1 - a)) z r) x)| ≤
      (Real.sqrt 3 / Real.sqrt a / r) *
        (Real.sqrt (ell x) * Real.exp (-ell x - ((Module.finrank ℝ E : ℝ) / 2) *
          Real.log s - ((Module.finrank ℝ E : ℝ) / 2) * Real.log (4 * Real.pi))) := by
  rw [abs_mul, abs_of_pos (Real.exp_pos _)]
  have hb := co.abs_inner_redLength_limit_gradient_radialDistanceCutoff_le
    F hcar hreg b hbmem tau q hsigma Phi kappa hancient p ha has rho hrho ell
    hconv hcomplete z hr x
  calc
    _ ≤ Real.exp (-ell x - ((Module.finrank ℝ E : ℝ) / 2) * Real.log s -
        ((Module.finrank ℝ E : ℝ) / 2) * Real.log (4 * Real.pi)) *
        ((Real.sqrt 3 / Real.sqrt a / r) * Real.sqrt (ell x)) :=
      mul_le_mul_of_nonneg_left hb (Real.exp_nonneg _)
    _ = _ := by ring

theorem HalfLineMetricConvergenceData.abs_chartGradientBilin_redLength_limit_radialDistanceCutoff_le
    [ConnectedSpace P.M]
    (Phi : PointedCGHMaps Y P phi) {R : SmoothRiemannianMetric I P.M}
    {bf : BumpFamily Phi} {hsrc : SourceIsSigmaCompact Phi} {htgt : TargetIsSigmaCompact Phi}
    (co : HalfLineMetricConvergenceData Phi R bf hsrc htgt)
    (kappa : ℕ → ℝ) (hancient : ∀ i, IsAncientKappaSolution (kappa i) ((U).term i))
    (p : F.M) {a s : ℝ} (ha : 1 ≤ a) (has : a ≤ s)
    (rho : ℕ → ℕ) (hrho : Tendsto rho atTop atTop) (ell : P.M → ℝ)
    (hconv : ∀ y, Tendsto (fun k => redLength ((U).term (phi (co.φ (rho k)))).S 0 p
      (Phi.map (co.φ (rho k)) y) s) atTop (𝓝 (ell y)))
    (hcomplete : MetricComplete (I := I)
      ({ P with metric := co.gInf (1 - s) } : PointedRiemannianManifold (I := I)))
    (z alpha : P.M) {r : ℝ} (hr : 0 < r) (x : P.M)
    (hell : MDifferentiableAt I 𝓘(ℝ, ℝ) ell x)
    (hcut : MDifferentiableAt I 𝓘(ℝ, ℝ)
      (radialDistanceCutoff (co.gInf (1 - a)) z r) x)
    (hx : x ∈ (chartAt H alpha).source) :
    |chartGradientBilin (co.gInf (1 - s)) alpha x
        (fderiv ℝ (scalarOnE (I := I) alpha ell) (extChartAt I alpha x))
        (fderiv ℝ (scalarOnE (I := I) alpha
          (radialDistanceCutoff (co.gInf (1 - a)) z r)) (extChartAt I alpha x))| ≤
      (Real.sqrt 3 / Real.sqrt a / r) * Real.sqrt (ell x) := by
  rw [← inner_gradientFun_eq_chartGradientBilin (co.gInf (1 - s)) alpha hell hcut hx]
  exact co.abs_inner_redLength_limit_gradient_radialDistanceCutoff_le
    F hcar hreg b hbmem tau q hsigma Phi kappa hancient p ha has rho hrho ell
    hconv hcomplete z hr x

namespace HalfLineMetricConvergenceData

theorem abs_redDensity_limit_mul_chartGradientBilin_radialDistanceCutoff_le
    [ConnectedSpace P.M]
    (Phi : PointedCGHMaps Y P phi) {R : SmoothRiemannianMetric I P.M}
    {bf : BumpFamily Phi} {hsrc : SourceIsSigmaCompact Phi} {htgt : TargetIsSigmaCompact Phi}
    (co : HalfLineMetricConvergenceData Phi R bf hsrc htgt)
    (kappa : ℕ → ℝ) (hancient : ∀ i, IsAncientKappaSolution (kappa i) ((U).term i))
    (p : F.M) {a s : ℝ} (ha : 1 ≤ a) (has : a ≤ s)
    (rho : ℕ → ℕ) (hrho : Tendsto rho atTop atTop) (ell : P.M → ℝ)
    (hconv : ∀ y, Tendsto (fun k => redLength ((U).term (phi (co.φ (rho k)))).S 0 p
      (Phi.map (co.φ (rho k)) y) s) atTop (𝓝 (ell y)))
    (hcomplete : MetricComplete (I := I)
      ({ P with metric := co.gInf (1 - s) } : PointedRiemannianManifold (I := I)))
    (z alpha : P.M) {r : ℝ} (hr : 0 < r) (x : P.M)
    (hell : MDifferentiableAt I 𝓘(ℝ, ℝ) ell x)
    (hcut : MDifferentiableAt I 𝓘(ℝ, ℝ)
      (radialDistanceCutoff (co.gInf (1 - a)) z r) x)
    (hx : x ∈ (chartAt H alpha).source) :
    |Real.exp (-ell x - ((Module.finrank ℝ E : ℝ) / 2) * Real.log s -
        ((Module.finrank ℝ E : ℝ) / 2) * Real.log (4 * Real.pi)) *
      chartGradientBilin (co.gInf (1 - s)) alpha x
        (fderiv ℝ (scalarOnE (I := I) alpha ell) (extChartAt I alpha x))
        (fderiv ℝ (scalarOnE (I := I) alpha
          (radialDistanceCutoff (co.gInf (1 - a)) z r)) (extChartAt I alpha x))| ≤
      (Real.sqrt 3 / Real.sqrt a / r) *
        (Real.sqrt (ell x) * Real.exp (-ell x - ((Module.finrank ℝ E : ℝ) / 2) *
          Real.log s - ((Module.finrank ℝ E : ℝ) / 2) * Real.log (4 * Real.pi))) := by
  rw [abs_mul, abs_of_pos (Real.exp_pos _)]
  have hb := co.abs_chartGradientBilin_redLength_limit_radialDistanceCutoff_le
    F hcar hreg b hbmem tau q hsigma Phi kappa hancient p ha has rho hrho ell
    hconv hcomplete z alpha hr x hell hcut hx
  calc
    _ ≤ Real.exp (-ell x - ((Module.finrank ℝ E : ℝ) / 2) * Real.log s -
        ((Module.finrank ℝ E : ℝ) / 2) * Real.log (4 * Real.pi)) *
        ((Real.sqrt 3 / Real.sqrt a / r) * Real.sqrt (ell x)) :=
      mul_le_mul_of_nonneg_left hb (Real.exp_nonneg _)
    _ = _ := by ring

end HalfLineMetricConvergenceData

end DifferentialGeometry.CheegerGromovCompactness
