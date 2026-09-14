import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHornBarriersRadialNesting
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.EndChartTipSideDiameter

set_option autoImplicit false
noncomputable section
open scoped Topology

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn

open DifferentialGeometry.Geometry.Curvature DifferentialGeometry.CheegerGromovCompactness
open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
open scoped Manifold ContDiff ENNReal

universe u

attribute [local instance] RealizedFiniteHorn.metric_space RealizedFiniteHorn.charted
  RealizedFiniteHorn.smooth RealizedFiniteHorn.sigmaCompact

variable {W : Type u} [MetricSpace W] [ChartedSpace ThreeSpace W]
  [IsManifold I3 ∞ W] [SigmaCompactSpace W]


theorem hornRadialPosition_of_hornRadialOuterPosition {g : SmoothRiemannianMetric I3 W}
    (H : FiniteHorn g) (ray : EndRay H.endpoint) (d : ℕ → ℝ)
    (hd : ∀ i, d i ∈ Set.Ioc 0 ray.length)
    (hzero : Filter.Tendsto d Filter.atTop (nhds 0))
    (hlarge : Filter.Tendsto (fun i => metricScalarAt g (ray.point (d i)) * d i ^ 2)
      Filter.atTop Filter.atTop)
    (houter : HornRadialOuterPosition g H ray d) : HornRadialPosition g H ray d :=
  (hornRadialPosition_iff_hornRadialOuterPosition H ray d hd hzero hlarge).mpr houter


theorem hornRadialOuterPosition_of_hornRadialExitPositionAtEndChart
    {g : SmoothRiemannianMetric I3 W} (H : FiniteHorn g) (ray : EndRay H.endpoint)
    (d : ℕ → ℝ) (hd : ∀ i, d i ∈ Set.Ioc 0 ray.length)
    (hzero : Filter.Tendsto d Filter.atTop (nhds 0))
    (hlarge : Filter.Tendsto (fun i => metricScalarAt g (ray.point (d i)) * d i ^ 2)
      Filter.atTop Filter.atTop)
    (hexit : HornRadialExitPositionAtEndChart g H ray d) :
    HornRadialOuterPosition g H ray d :=
  (hornRadialPosition_iff_hornRadialOuterPosition H ray d hd hzero hlarge).mp
    (hornRadialPosition_of_hornRadialExitPositionAtEndChart g H ray d hd hzero hlarge hexit)


theorem hornRadialOuterPosition_of_endChartTipSideDiameterBound
    {g : SmoothRiemannianMetric I3 W} (H : FiniteHorn g) (ray : EndRay H.endpoint)
    (d : ℕ → ℝ) (hd : ∀ i, d i ∈ Set.Ioc 0 ray.length)
    (hzero : Filter.Tendsto d Filter.atTop (nhds 0))
    (hlarge : Filter.Tendsto (fun i => metricScalarAt g (ray.point (d i)) * d i ^ 2)
      Filter.atTop Filter.atTop)
    (hdiam : EndChartTipSideDiameterBound g H ray d) : HornRadialOuterPosition g H ray d :=
  hornRadialOuterPosition_of_hornRadialExitPositionAtEndChart H ray d hd hzero hlarge
    (hornRadialExitPositionAtEndChart_of_endChartTipSideDiameterBound g H ray d hd hlarge hdiam)


theorem hornRadialOuterPosition_of_neckEndScaleWindow {g : SmoothRiemannianMetric I3 W}
    (H : FiniteHorn g) (ray : EndRay H.endpoint) (d : ℕ → ℝ)
    (hd : ∀ i, d i ∈ Set.Ioc 0 ray.length)
    (hzero : Filter.Tendsto d Filter.atTop (nhds 0))
    (hlarge : Filter.Tendsto (fun i => metricScalarAt g (ray.point (d i)) * d i ^ 2)
      Filter.atTop Filter.atTop)
    (hscale : NeckEndScaleWindow g H ray d) : HornRadialOuterPosition g H ray d :=
  (hornRadialPosition_iff_hornRadialOuterPosition H ray d hd hzero hlarge).mp
    (hornRadialPosition_of_neckEndScaleWindow g H ray d hd hzero hlarge hscale)


theorem hornRadialOuterPosition_of_neckEndScale {g : SmoothRiemannianMetric I3 W}
    (H : FiniteHorn g) (ray : EndRay H.endpoint) (d : ℕ → ℝ)
    (hd : ∀ i, d i ∈ Set.Ioc 0 ray.length)
    (hzero : Filter.Tendsto d Filter.atTop (nhds 0))
    (hlarge : Filter.Tendsto (fun i => metricScalarAt g (ray.point (d i)) * d i ^ 2)
      Filter.atTop Filter.atTop)
    (hscale : NeckEndScale g H ray d) : HornRadialOuterPosition g H ray d :=
  hornRadialOuterPosition_of_neckEndScaleWindow H ray d hd hzero hlarge
    (neckEndScaleWindow_of_neckEndScale g H ray d hscale)


theorem nonempty_hornBarriers_of_hornRadialExitPositionAtEndChart
    {g : SmoothRiemannianMetric I3 W} (H : FiniteHorn g) (ray : EndRay H.endpoint)
    (d : ℕ → ℝ) (hd : ∀ i, d i ∈ Set.Ioc 0 ray.length)
    (hzero : Filter.Tendsto d Filter.atTop (nhds 0))
    (hlarge : Filter.Tendsto (fun i => metricScalarAt g (ray.point (d i)) * d i ^ 2)
      Filter.atTop Filter.atTop)
    (hexit : HornRadialExitPositionAtEndChart g H ray d) : Nonempty (HornBarriers H ray d) :=
  nonempty_hornBarriers_of_hornRadialPosition g H ray d hd hzero
    (hornRadialPosition_of_hornRadialExitPositionAtEndChart g H ray d hd hzero hlarge hexit)


theorem nonempty_hornBarriers_of_endChartTipSideDiameterBound
    {g : SmoothRiemannianMetric I3 W} (H : FiniteHorn g) (ray : EndRay H.endpoint)
    (d : ℕ → ℝ) (hd : ∀ i, d i ∈ Set.Ioc 0 ray.length)
    (hzero : Filter.Tendsto d Filter.atTop (nhds 0))
    (hlarge : Filter.Tendsto (fun i => metricScalarAt g (ray.point (d i)) * d i ^ 2)
      Filter.atTop Filter.atTop)
    (hdiam : EndChartTipSideDiameterBound g H ray d) : Nonempty (HornBarriers H ray d) :=
  nonempty_hornBarriers_of_hornRadialPosition g H ray d hd hzero
    (hornRadialPosition_of_hornRadialExitPositionAtEndChart g H ray d hd hzero hlarge
      (hornRadialExitPositionAtEndChart_of_endChartTipSideDiameterBound g H ray d hd hlarge
        hdiam))


theorem eventually_div_sqrt_lt_scale_of_scale_diverges {d s : ℕ → ℝ} (hd : ∀ i, 0 < d i)
    (hlarge : Filter.Tendsto (fun i => s i * d i ^ 2) Filter.atTop Filter.atTop)
    {L e : ℝ} (hL : 0 < L) (he : 0 < e) :
    ∀ᶠ i in Filter.atTop, L / Real.sqrt (s i) < e * d i := by
  have hLe : 0 < L / e := div_pos hL he
  have hd2 : ∀ i, 0 < d i ^ 2 := fun i => pow_pos (hd i) 2
  filter_upwards [hlarge.eventually_gt_atTop ((L / e) ^ 2),
    hlarge.eventually_ge_atTop 1] with i hsq hone
  have hs_pos : 0 < s i := by nlinarith [hone, hd2 i]
  have hprod : 0 < s i * d i ^ 2 := mul_pos hs_pos (hd2 i)
  have hlt : L / e < Real.sqrt (s i * d i ^ 2) := by
    rw [Real.lt_sqrt hLe.le]
    exact hsq
  have hsqrt : Real.sqrt (s i * d i ^ 2) = Real.sqrt (s i) * d i := by
    rw [Real.sqrt_mul hs_pos.le, Real.sqrt_sq (hd i).le]
  rw [hsqrt] at hlt
  have hmain : L < e * (Real.sqrt (s i) * d i) := by
    have h := mul_lt_mul_of_pos_left hlt he
    have heq : e * (L / e) = L := by field_simp
    rwa [heq] at h
  have hsq_pos : 0 < Real.sqrt (s i) := Real.sqrt_pos.mpr hs_pos
  rw [div_lt_iff₀ hsq_pos]
  calc L < e * (Real.sqrt (s i) * d i) := hmain
    _ = e * d i * Real.sqrt (s i) := by ring

theorem finite_horn_construction_of_bounded_curvature_at_distance
    {kappa sigma : ℝ} {Phi : ℝ → ℝ}
    (hkappa : 0 < kappa) (hsigma : 0 < sigma) (hPhi : AdmissiblePinchingFunction Phi) :
    ∃ alphaMax collarMin : ℝ, 0 < alphaMax ∧ alphaMax < 1 / 11 ∧ 0 < collarMin ∧
      ∀ alpha : ℝ, 0 < alpha → alpha ≤ alphaMax → ∀ collar : ℝ, collarMin ≤ collar →
        ∃ epsStar : ℝ, 0 < epsStar ∧ ∀ eps : ℝ, 0 < eps → eps ≤ epsStar →
          ∀ X : NormalizedSequence.{u} eps kappa sigma Phi,
            FiniteControlledRadius X → ∃ H : RealizedFiniteHorn X.toFlowSequence,
              H.horn.neck_precision = alpha ∧ collar ≤ H.horn.collar_depth :=
  finite_horn_construction_of_boundedAtDistanceShell hkappa hsigma hPhi
    (by
      obtain ⟨e, he, hb⟩ := bounded_curvature_at_distance (kappa := kappa) (sigma := sigma)
        (Phi := Phi) hkappa hsigma hPhi
      exact ⟨e, he, fun eps hp hle X => (hb eps hp hle X).1⟩)

end DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn
