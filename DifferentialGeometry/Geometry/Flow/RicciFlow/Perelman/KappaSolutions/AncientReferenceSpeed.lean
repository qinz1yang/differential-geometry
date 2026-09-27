import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.AncientTailSpeed
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.AncientMetricMonotonicity

noncomputable section
namespace DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions
open Set
open DifferentialGeometry.CheegerGromovCompactness CanonicalNeighborhood
open DifferentialGeometry.Geometry.Curvature
open scoped _root_.Manifold ContDiff
universe u uE uH
variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] {H : Type uH} [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  (F : PointedFlowData.{u, uE, uH} (I := I) ancientTimeInterval)
local instance topology : TopologicalSpace F.M := F.topology
local instance charted : ChartedSpace H F.M := F.charted
local instance smooth : IsManifold I ∞ F.M := F.smooth
local instance t2 : T2Space F.M := F.t2
local instance sigma : SigmaCompactSpace F.M := F.sigmaCompact

theorem lVelocity_norm_le_on_half_tail_of_ancient
    {kappa : ℝ} (hF : IsAncientKappaSolution kappa F)
    (g : SmoothRiemannianMetric I F.M)
    (alpha : ℝ → F.M) (halpha : ContMDiff 𝓘(ℝ, ℝ) I 1 alpha)
    (p : F.M) {tau s mu A : ℝ} (htau : 0 < tau)
    (hs : s ∈ Icc (Real.sqrt tau / 2) (Real.sqrt tau))
    (hgeo : IsLRegularizedGeodesicOn F.S 0 alpha (Ioo 0 (Real.sqrt tau)))
    (hcost : lRegularizedAction F.S 0 alpha 0 (Real.sqrt tau) =
      lCost F.S 0 p (alpha (Real.sqrt tau)) tau)
    (hmu : 0 ≤ mu)
    (hmetric : ∀ v : TangentSpace I (alpha s),
      g.inner (alpha s) v v ≤ mu * (F.S.base.metric (-s ^ 2)).inner (alpha s) v v)
    (hA : redLength F.S 0 p (alpha (Real.sqrt tau)) tau ≤ A) :
    Real.sqrt (g.inner (alpha s) (lVelocity (I := I) alpha s)
      (lVelocity (I := I) alpha s)) ≤ Real.sqrt mu * Real.sqrt (24 * A) := by
  have hspeed := lRegularizedSpeedSq_le_twenty_four_mul_redLength_on_half_tail_of_ancient
    F hF alpha halpha p htau hs hgeo hcost
  have hspeedA : lRegularizedSpeedSq F.S 0 alpha s ≤ 24 * A :=
    hspeed.trans (mul_le_mul_of_nonneg_left hA (by norm_num))
  have hm := hmetric (lVelocity (I := I) alpha s)
  have hbound : g.inner (alpha s) (lVelocity (I := I) alpha s)
      (lVelocity (I := I) alpha s) ≤ mu * (24 * A) := by
    apply hm.trans
    apply mul_le_mul_of_nonneg_left _ hmu
    simpa only [lRegularizedSpeedSq, zero_sub] using hspeedA
  calc
    _ ≤ Real.sqrt (mu * (24 * A)) := Real.sqrt_le_sqrt hbound
    _ = _ := Real.sqrt_mul hmu _

theorem lVelocity_terminal_norm_le_on_half_tail_of_ancient
    {kappa : ℝ} (hF : IsAncientKappaSolution kappa F)
    (alpha : ℝ → F.M) (halpha : ContMDiff 𝓘(ℝ, ℝ) I 1 alpha)
    (p : F.M) {tau s A : ℝ} (htau : 0 < tau)
    (hs : s ∈ Icc (Real.sqrt tau / 2) (Real.sqrt tau))
    (hgeo : IsLRegularizedGeodesicOn F.S 0 alpha (Ioo 0 (Real.sqrt tau)))
    (hcost : lRegularizedAction F.S 0 alpha 0 (Real.sqrt tau) =
      lCost F.S 0 p (alpha (Real.sqrt tau)) tau)
    (hA : redLength F.S 0 p (alpha (Real.sqrt tau)) tau ≤ A) :
    Real.sqrt ((F.S.base.metric 0).inner (alpha s) (lVelocity (I := I) alpha s)
      (lVelocity (I := I) alpha s)) ≤ Real.sqrt (24 * A) := by
  have hmetric : ∀ v : TangentSpace I (alpha s),
      (F.S.base.metric 0).inner (alpha s) v v ≤
        1 * (F.S.base.metric (-s ^ 2)).inner (alpha s) v v := by
    intro v
    simpa only [one_mul] using ancientModel_metric_zero_le F hF
      (neg_nonpos.mpr (sq_nonneg s)) (alpha s) v
  simpa only [Real.sqrt_one, one_mul] using
    lVelocity_norm_le_on_half_tail_of_ancient F hF (F.S.base.metric 0)
      alpha halpha p htau hs hgeo hcost (by norm_num : (0 : ℝ) ≤ 1) hmetric hA
end DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions
