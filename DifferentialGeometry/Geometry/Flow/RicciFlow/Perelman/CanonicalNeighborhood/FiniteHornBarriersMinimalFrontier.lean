import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.BoundedAtDistanceFromRmBallBound
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.EndChartTipSideDiameterRefutation
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHornBarriersRadialNesting
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHornConstruction

set_option autoImplicit false
noncomputable section
open scoped Topology

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn

open DifferentialGeometry.Geometry.Curvature DifferentialGeometry.CheegerGromovCompactness
open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
open scoped Manifold ContDiff ENNReal

universe u

attribute [local instance] PointedFlowData.topology PointedFlowData.charted
  PointedFlowData.smooth PointedFlowData.t2 PointedFlowData.sigmaCompact
  RealizedFiniteHorn.metric_space RealizedFiniteHorn.charted RealizedFiniteHorn.smooth
  RealizedFiniteHorn.sigmaCompact

variable {W : Type u} [MetricSpace W] [ChartedSpace ThreeSpace W]
  [IsManifold I3 ∞ W] [SigmaCompactSpace W]

theorem not_endChartTipSideDiameterBound {g : SmoothRiemannianMetric I3 W} (H : FiniteHorn g)
    (ray : EndRay H.endpoint) (d : ℕ → ℝ) (hd : ∀ i, d i ∈ Set.Ioc 0 ray.length)
    (hzero : Filter.Tendsto d Filter.atTop (nhds 0))
    (hlarge : Filter.Tendsto (fun i => metricScalarAt g (ray.point (d i)) * d i ^ 2)
      Filter.atTop Filter.atTop) :
    ¬ EndChartTipSideDiameterBound g H ray d := by
  rintro ⟨L, hL, hbound⟩
  obtain ⟨i, hrest⟩ :=
    ((((endChart_tipSide_pair_height_and_dist H ray d hd hzero hlarge (3 / 4)
        (by norm_num) (by norm_num)).and hbound).and
      (eventually_mem_tail g H ray d hd hzero)).and
      (hlarge.eventually_ge_atTop (max 1 ((L / (3 / 4)) ^ 2 + 1)))).exists
  obtain ⟨⟨⟨hpair, hb⟩, hgood⟩, hbig⟩ := hrest
  obtain ⟨hxle, hyeq, hdist⟩ := hpair hgood (endChart g H (ray.point (d i)) hgood)
  have hle := hb hgood (endChart g H (ray.point (d i)) hgood)
    (ray.point ((1 - 3 / 4) * d i)) (ray.point (d i)) hxle hyeq.le
  have hdpos : 0 < d i := (hd i).1
  have hs_pos : 0 < metricScalarAt g (ray.point (d i)) := by
    have hone : 1 ≤ metricScalarAt g (ray.point (d i)) * d i ^ 2 :=
      le_trans (le_max_left _ _) hbig
    nlinarith [hone, sq_nonneg (d i), sq_pos_of_pos hdpos]
  have hchain : (3 / 4) * d i ≤ L / Real.sqrt (metricScalarAt g (ray.point (d i))) :=
    le_trans hdist hle
  have hmul : (3 / 4) * (d i * Real.sqrt (metricScalarAt g (ray.point (d i)))) ≤ L := by
    have h := (le_div_iff₀ (Real.sqrt_pos.mpr hs_pos)).mp hchain
    nlinarith [h]
  have hroot : L / (3 / 4) < Real.sqrt (metricScalarAt g (ray.point (d i))) * d i := by
    have hsqrt : Real.sqrt (metricScalarAt g (ray.point (d i)) * d i ^ 2) =
        Real.sqrt (metricScalarAt g (ray.point (d i))) * d i := by
      rw [Real.sqrt_mul hs_pos.le, Real.sqrt_sq hdpos.le]
    rw [← hsqrt]
    rw [Real.lt_sqrt (by positivity)]
    have hsq : (L / (3 / 4)) ^ 2 + 1 ≤ metricScalarAt g (ray.point (d i)) * d i ^ 2 :=
      le_trans (le_max_right _ _) hbig
    linarith
  have hgt : L < (3 / 4) * (d i * Real.sqrt (metricScalarAt g (ray.point (d i)))) := by
    have h := mul_lt_mul_of_pos_left hroot (by norm_num : (0 : ℝ) < 3 / 4)
    calc L = (3 / 4) * (L / (3 / 4)) := by field_simp
      _ < (3 / 4) * (Real.sqrt (metricScalarAt g (ray.point (d i))) * d i) := h
      _ = (3 / 4) * (d i * Real.sqrt (metricScalarAt g (ray.point (d i)))) := by ring
  linarith

omit [SigmaCompactSpace W] in
theorem finite_horn_barriers_of_neckEndScale {g : SmoothRiemannianMetric I3 W}
    (H : FiniteHorn g) (_endData : EndGeometry H) (ray : EndRay H.endpoint)
    (d : ℕ → ℝ) (hd : ∀ i, d i ∈ Set.Ioc 0 ray.length)
    (hzero : Filter.Tendsto d Filter.atTop (nhds 0))
    (hlarge : Filter.Tendsto (fun i => metricScalarAt g (ray.point (d i)) * d i ^ 2)
      Filter.atTop Filter.atTop)
    (hscale : NeckEndScale g H ray d) : Nonempty (HornBarriers H ray d) :=
  nonempty_hornBarriers_of_neckEndScale g H ray d hd hzero hlarge hscale

theorem boundedAtDistanceShell_of_terminalDerivativeBoundProducer
    {kappa sigma : ℝ} {Phi : ℝ → ℝ}
    (h : TerminalDerivativeBoundProducer.{u} kappa sigma Phi) :
    BoundedAtDistanceShell.{u} kappa sigma Phi := by
  obtain ⟨e, he, hb⟩ := h
  obtain ⟨e', he', hb'⟩ := bounded_curvature_at_distance_of_terminalDerivativeBoundProducer
    ⟨e, he, fun eps' hp' hle' X' => hb eps' hp' hle' X'⟩
  exact ⟨e', he', fun eps hp hle X => (hb' eps hp hle X).1⟩

theorem finite_horn_construction_of_terminalDerivativeBoundProducer
    {kappa sigma : ℝ} {Phi : ℝ → ℝ}
    (hkappa : 0 < kappa) (hsigma : 0 < sigma) (hPhi : AdmissiblePinchingFunction Phi)
    (h : TerminalDerivativeBoundProducer.{u} kappa sigma Phi) :
    ∃ alphaMax collarMin : ℝ, 0 < alphaMax ∧ alphaMax < 1 / 11 ∧ 0 < collarMin ∧
      ∀ alpha : ℝ, 0 < alpha → alpha ≤ alphaMax → ∀ collar : ℝ, collarMin ≤ collar →
        ∃ epsStar : ℝ, 0 < epsStar ∧ ∀ eps : ℝ, 0 < eps → eps ≤ epsStar →
          ∀ X : NormalizedSequence.{u} eps kappa sigma Phi,
            FiniteControlledRadius X → ∃ H : RealizedFiniteHorn X.toFlowSequence,
              H.horn.neck_precision = alpha ∧ collar ≤ H.horn.collar_depth :=
  finite_horn_construction_of_boundedAtDistanceShell hkappa hsigma hPhi
    (boundedAtDistanceShell_of_terminalDerivativeBoundProducer h)

theorem not_nonempty_finiteControlledRadius_of_boundedAtDistance
    {eps kappa sigma : ℝ} {Phi : ℝ → ℝ} (X : NormalizedSequence.{u} eps kappa sigma Phi)
    (h : BoundedAtDistance X) : ¬ Nonempty (FiniteControlledRadius X) :=
  fun hc => finiteControlledRadius_false_of_boundedAtDistance X h hc.some

end DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn
