import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.CurvatureEscape
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHornStructure
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.TerminalParabolicScalarBallProducer

set_option autoImplicit false
noncomputable section
open scoped Topology

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn

open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.CheegerGromovCompactness
open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
open scoped _root_.Manifold ContDiff ENNReal

universe u

attribute [local instance] PointedFlowData.topology PointedFlowData.charted
  PointedFlowData.smooth PointedFlowData.t2 PointedFlowData.sigmaCompact
  PointedRiemannianManifold.topology PointedRiemannianManifold.charted
  PointedRiemannianManifold.smooth PointedRiemannianManifold.t2
  PointedRiemannianManifold.sigmaCompact

theorem curvatureBoundedWithin_of_terminalParabolicScalarBallBoundAtSameTime
    {eps kappa sigma : ℝ} {Phi : ℝ → ℝ} (X : NormalizedSequence.{u} eps kappa sigma Phi)
    {start ρ : ℝ} (hstart : start ≤ 0) (hρ : 0 ≤ ρ)
    (h : TerminalParabolicScalarBallBoundAtSameTime X start ρ) :
    CurvatureBoundedWithin X ρ := by
  obtain ⟨C, _hC, hb⟩ := h
  refine ⟨C, fun i y hy => ?_⟩
  refine hb i 0 ⟨hstart, le_rfl⟩ y ?_
  have : PreconnectedSpace (X.term i).M := (X.connected i).toPreconnectedSpace
  refine (ENNReal.le_ofReal_iff_toReal_le
    (riemannianEDistOf_ne_top (I := I3) ((X.term i).S.base.metric 0)
      (X.term i).basepoint y) hρ).mpr ?_
  simpa only [metricDistance] using hy.le

theorem exists_pos_curvatureBoundedWithin_of_modelScale {kappa : ℝ}
    (hmod : ModelCurvatureBoundNearBase.{u, 0, 0} I3 kappa) :
    ∃ epsStar r : ℝ, 0 < epsStar ∧ 0 < r ∧
      ∀ eps : ℝ, 0 < eps → eps ≤ epsStar → ∀ sigma : ℝ, 0 < sigma →
        ∀ Phi : ℝ → ℝ, AdmissiblePinchingFunction Phi →
          ∀ X : NormalizedSequence.{u} eps kappa sigma Phi, CurvatureBoundedWithin X r := by
  obtain ⟨epsStar, r, _C, hepsStar, hr, _hC, hprop⟩ :=
    exists_terminalParabolicScalarBallBoundAtSameTime_baseScale (kappa := kappa) hmod
  exact ⟨epsStar, r, hepsStar, hr, fun eps heps hle sigma hsigma Phi hPhi X =>
    curvatureBoundedWithin_of_terminalParabolicScalarBallBoundAtSameTime X le_rfl hr.le
      (hprop eps heps hle sigma hsigma Phi hPhi X r hr le_rfl)⟩

theorem positiveDistanceCurvatureEscape_of_not_boundedAtDistance_of_modelScale
    {kappa : ℝ} (hmod : ModelCurvatureBoundNearBase.{u, 0, 0} I3 kappa) :
    ∃ epsStar r : ℝ, 0 < epsStar ∧ 0 < r ∧
      ∀ eps : ℝ, 0 < eps → eps ≤ epsStar → ∀ sigma : ℝ, 0 < sigma →
        ∀ Phi : ℝ → ℝ, AdmissiblePinchingFunction Phi →
          ∀ X : NormalizedSequence.{u} eps kappa sigma Phi,
            ¬ BoundedAtDistance X → PositiveDistanceCurvatureEscape X := by
  obtain ⟨epsStar, r, hepsStar, hr, hbound⟩ :=
    exists_pos_curvatureBoundedWithin_of_modelScale (kappa := kappa) hmod
  exact ⟨epsStar, r, hepsStar, hr, fun eps heps hle sigma hsigma Phi hPhi X hfail =>
    positiveDistanceCurvatureEscape_of_curvatureBoundedWithin X hfail hr
      (hbound eps heps hle sigma hsigma Phi hPhi X)⟩

theorem not_boundedAtDistance_of_distanceCurvatureEscape {eps kappa sigma : ℝ}
    {Phi : ℝ → ℝ} (X : NormalizedSequence.{u} eps kappa sigma Phi)
    (h : DistanceCurvatureEscape X) : ¬ BoundedAtDistance X := by
  obtain ⟨radius, hnonneg, _hbdd, hunbdd⟩ := h
  intro hb
  obtain ⟨C, hC⟩ := hb (radius + 1) (by linarith)
  obtain ⟨i, y, hy, hcy⟩ := hunbdd (radius + 1) (by linarith) C
  exact absurd (hC i y hy.le) (not_le.mpr hcy)

theorem distanceCurvatureEscape_iff_not_boundedAtDistance {eps kappa sigma : ℝ}
    {Phi : ℝ → ℝ} (X : NormalizedSequence.{u} eps kappa sigma Phi) :
    DistanceCurvatureEscape X ↔ ¬ BoundedAtDistance X :=
  ⟨not_boundedAtDistance_of_distanceCurvatureEscape X,
    distanceCurvatureEscape_of_not_boundedAtDistance X⟩

theorem distanceCurvatureEscape_of_positiveDistanceCurvatureEscape {eps kappa sigma : ℝ}
    {Phi : ℝ → ℝ} {X : NormalizedSequence.{u} eps kappa sigma Phi}
    (h : PositiveDistanceCurvatureEscape X) : DistanceCurvatureEscape X := by
  obtain ⟨radius, hpos, hinner, houter⟩ := h
  exact ⟨radius, hpos.le, hinner, houter⟩

theorem distanceCurvatureEscape_of_finiteControlledRadius {eps kappa sigma : ℝ}
    {Phi : ℝ → ℝ} {X : NormalizedSequence.{u} eps kappa sigma Phi}
    (h : FiniteControlledRadius X) : DistanceCurvatureEscape X := by
  refine ⟨h.radius, h.radius_pos.le, fun r hr hlt => h.inner_bound r hr hlt, ?_⟩
  intro r hr C
  have hclose : ∀ᶠ i in Filter.atTop,
      metricDistance ((X.term i).S.base.metric 0) (X.term i).basepoint (h.points i) < r :=
    h.distance_limit.eventually (eventually_lt_nhds hr)
  have hlarge : ∀ᶠ i in Filter.atTop, C < (X.term i).S.scalar 0 (h.points i) :=
    h.curvature_limit.eventually_gt_atTop C
  obtain ⟨i, hi⟩ := (hclose.and hlarge).exists
  exact ⟨i, h.points i, hi.1, hi.2⟩

theorem realizedDistanceCurvatureEscape_of_finiteControlledRadius {eps kappa sigma : ℝ}
    {Phi : ℝ → ℝ} {X : NormalizedSequence.{u} eps kappa sigma Phi}
    (h : FiniteControlledRadius X) : RealizedDistanceCurvatureEscape X :=
  ⟨h.radius, h.radius_pos, fun r hr hlt => h.inner_bound r hr hlt,
    h.points, h.distance_limit, h.curvature_limit⟩

theorem nonempty_finiteControlledRadius_iff_realizedDistanceCurvatureEscape {eps kappa sigma : ℝ}
    {Phi : ℝ → ℝ} (X : NormalizedSequence.{u} eps kappa sigma Phi) :
    Nonempty (FiniteControlledRadius X) ↔ RealizedDistanceCurvatureEscape X :=
  ⟨fun h => realizedDistanceCurvatureEscape_of_finiteControlledRadius h.some,
    fun h => by
      obtain ⟨radius, hpos, hbdd, points, hdist, hcurv⟩ := h
      exact ⟨⟨radius, hpos, hbdd, points, hdist, hcurv⟩⟩⟩

theorem boundedAtDistance_of_coneFlowLimit_of_not_boundedAtDistance {eps kappa sigma : ℝ}
    {Phi : ℝ → ℝ} (X : NormalizedSequence.{u} eps kappa sigma Phi)
    (h : ¬ BoundedAtDistance X → Nonempty (ConeFlowLimit X.toFlowSequence)) :
    BoundedAtDistance X := by
  by_contra hf
  exact coneFlowLimit_not_nonempty (h hf)

theorem coneFlowLimit_of_not_boundedAtDistance_of_boundedAtDistance {eps kappa sigma : ℝ}
    {Phi : ℝ → ℝ} (X : NormalizedSequence.{u} eps kappa sigma Phi)
    (h : BoundedAtDistance X) :
    ¬ BoundedAtDistance X → Nonempty (ConeFlowLimit X.toFlowSequence) :=
  fun hf => absurd h hf

theorem boundedAtDistance_iff_coneFlowLimit_of_not_boundedAtDistance {eps kappa sigma : ℝ}
    {Phi : ℝ → ℝ} (X : NormalizedSequence.{u} eps kappa sigma Phi) :
    BoundedAtDistance X ↔
      (¬ BoundedAtDistance X → Nonempty (ConeFlowLimit X.toFlowSequence)) :=
  ⟨coneFlowLimit_of_not_boundedAtDistance_of_boundedAtDistance X,
    boundedAtDistance_of_coneFlowLimit_of_not_boundedAtDistance X⟩

theorem boundedAtDistance_family_iff_coneFlowLimit_of_not_boundedAtDistance {kappa sigma : ℝ}
    {Phi : ℝ → ℝ} :
    (∃ epsStar : ℝ, 0 < epsStar ∧ ∀ eps : ℝ, 0 < eps → eps ≤ epsStar →
        ∀ X : NormalizedSequence.{u} eps kappa sigma Phi, BoundedAtDistance X) ↔
      (∃ epsStar : ℝ, 0 < epsStar ∧ ∀ eps : ℝ, 0 < eps → eps ≤ epsStar →
        ∀ X : NormalizedSequence.{u} eps kappa sigma Phi,
          ¬ BoundedAtDistance X → Nonempty (ConeFlowLimit X.toFlowSequence)) := by
  constructor
  · rintro ⟨e, he, hb⟩
    exact ⟨e, he, fun eps hp hle X =>
      coneFlowLimit_of_not_boundedAtDistance_of_boundedAtDistance X (hb eps hp hle X)⟩
  · rintro ⟨e, he, hc⟩
    exact ⟨e, he, fun eps hp hle X =>
      boundedAtDistance_of_coneFlowLimit_of_not_boundedAtDistance X (hc eps hp hle X)⟩

end DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn
