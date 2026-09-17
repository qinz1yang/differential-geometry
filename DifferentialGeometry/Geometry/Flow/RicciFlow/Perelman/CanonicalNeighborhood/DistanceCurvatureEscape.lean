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

def CurvatureBoundedWithin {eps kappa sigma : ℝ} {Phi : ℝ → ℝ}
    (X : NormalizedSequence.{u} eps kappa sigma Phi) (r : ℝ) : Prop :=
  ∃ C : ℝ, ∀ i : ℕ, ∀ y : (X.term i).M,
    metricDistance ((X.term i).S.base.metric 0) (X.term i).basepoint y < r →
      (X.term i).S.scalar 0 y ≤ C

def DistanceCurvatureEscape {eps kappa sigma : ℝ} {Phi : ℝ → ℝ}
    (X : NormalizedSequence.{u} eps kappa sigma Phi) : Prop :=
  ∃ radius : ℝ, 0 ≤ radius ∧
    (∀ r : ℝ, 0 < r → r < radius → CurvatureBoundedWithin X r) ∧
    (∀ r : ℝ, radius < r → ∀ C : ℝ, ∃ i : ℕ, ∃ y : (X.term i).M,
      metricDistance ((X.term i).S.base.metric 0) (X.term i).basepoint y < r ∧
        C < (X.term i).S.scalar 0 y)

def PositiveDistanceCurvatureEscape {eps kappa sigma : ℝ} {Phi : ℝ → ℝ}
    (X : NormalizedSequence.{u} eps kappa sigma Phi) : Prop :=
  ∃ radius : ℝ, 0 < radius ∧
    (∀ r : ℝ, 0 < r → r < radius → CurvatureBoundedWithin X r) ∧
    (∀ r : ℝ, radius < r → ∀ C : ℝ, ∃ i : ℕ, ∃ y : (X.term i).M,
      metricDistance ((X.term i).S.base.metric 0) (X.term i).basepoint y < r ∧
        C < (X.term i).S.scalar 0 y)

def RealizedDistanceCurvatureEscape {eps kappa sigma : ℝ} {Phi : ℝ → ℝ}
    (X : NormalizedSequence.{u} eps kappa sigma Phi) : Prop :=
  ∃ radius : ℝ, 0 < radius ∧
    (∀ r : ℝ, 0 < r → r < radius → CurvatureBoundedWithin X r) ∧
    ∃ points : ∀ i : ℕ, (X.term i).M,
      Filter.Tendsto (fun i : ℕ => metricDistance ((X.term i).S.base.metric 0)
          (X.term i).basepoint (points i)) Filter.atTop (nhds radius) ∧
      Filter.Tendsto (fun i : ℕ => (X.term i).S.scalar 0 (points i))
        Filter.atTop Filter.atTop

private theorem exists_escape_radius_core {eps kappa sigma : ℝ} {Phi : ℝ → ℝ}
    (X : NormalizedSequence.{u} eps kappa sigma Phi) (h : ¬ BoundedAtDistance X) :
    ∃ radius : ℝ,
      (∀ r : ℝ, 0 < r → r < radius → CurvatureBoundedWithin X r) ∧
      (∀ r : ℝ, radius < r → ∀ C : ℝ, ∃ i : ℕ, ∃ y : (X.term i).M,
        metricDistance ((X.term i).S.base.metric 0) (X.term i).basepoint y < r ∧
          C < (X.term i).S.scalar 0 y) := by
  classical
  simp only [BoundedAtDistance] at h
  push Not at h
  obtain ⟨rho, hrho, hfail⟩ := h
  have hfail' : ∀ C : ℝ, ∃ i : ℕ, ∃ y : (X.term i).M,
      metricDistance ((X.term i).S.base.metric 0) (X.term i).basepoint y ≤ rho ∧
        C < (X.term i).S.scalar 0 y := by
    intro C
    obtain ⟨i, y, hd, hs⟩ := hfail C
    exact ⟨i, y, hd, hs⟩
  let S : Set ℝ := {r : ℝ | CurvatureBoundedWithin X r}
  have hS0 : (0 : ℝ) ∈ S := by
    refine ⟨0, fun i y hy => ?_⟩
    exact absurd hy (not_lt_of_ge ENNReal.toReal_nonneg)
  have hSne : S.Nonempty := ⟨0, hS0⟩
  have hSbdd : BddAbove S := by
    refine ⟨rho, fun r hr => le_of_not_gt fun hlt => ?_⟩
    obtain ⟨C, hC⟩ := hr
    obtain ⟨i, y, hd, hcs⟩ := hfail' C
    exact absurd (hC i y (lt_of_le_of_lt hd hlt)) (not_le.mpr hcs)
  refine ⟨sSup S, ?_, ?_⟩
  · intro r _ hlt
    obtain ⟨s, hs, hrs⟩ := (lt_csSup_iff hSbdd hSne).mp hlt
    obtain ⟨C, hC⟩ := hs
    exact ⟨C, fun i y hy => hC i y (lt_trans hy hrs)⟩
  · intro r hlt C
    by_contra hcon
    have hmem : r ∈ S := by
      refine ⟨C, fun i y hy => ?_⟩
      by_contra hgt
      exact hcon ⟨i, y, hy, lt_of_not_ge hgt⟩
    exact absurd (le_csSup hSbdd hmem) (not_le.mpr hlt)

private theorem nonneg_of_unbounded_beyond {eps kappa sigma : ℝ} {Phi : ℝ → ℝ}
    {X : NormalizedSequence.{u} eps kappa sigma Phi} {radius : ℝ}
    (h : ∀ r : ℝ, radius < r → ∀ C : ℝ, ∃ i : ℕ, ∃ y : (X.term i).M,
      metricDistance ((X.term i).S.base.metric 0) (X.term i).basepoint y < r ∧
        C < (X.term i).S.scalar 0 y) : 0 ≤ radius := by
  by_contra hcon
  have hlt : radius < 0 := lt_of_not_ge hcon
  obtain ⟨i, y, hy, _⟩ := h (radius / 2) (by linarith) 0
  have h0 : radius / 2 ≤ metricDistance ((X.term i).S.base.metric 0)
      (X.term i).basepoint y :=
    le_trans (by linarith) ENNReal.toReal_nonneg
  exact absurd hy (not_lt_of_ge h0)

theorem curvatureBoundedWithin_mono {eps kappa sigma : ℝ} {Phi : ℝ → ℝ}
    (X : NormalizedSequence.{u} eps kappa sigma Phi) {r r' : ℝ} (hr : r' ≤ r)
    (h : CurvatureBoundedWithin X r) : CurvatureBoundedWithin X r' := by
  obtain ⟨C, hC⟩ := h
  exact ⟨C, fun i y hy => hC i y (lt_of_lt_of_le hy hr)⟩

theorem boundedAtDistance_iff_forall_curvatureBoundedWithin {eps kappa sigma : ℝ}
    {Phi : ℝ → ℝ} (X : NormalizedSequence.{u} eps kappa sigma Phi) :
    BoundedAtDistance X ↔ ∀ r : ℝ, 0 < r → CurvatureBoundedWithin X r := by
  constructor
  · intro h r hr
    obtain ⟨C, hC⟩ := h r hr
    exact ⟨C, fun i y hy => hC i y hy.le⟩
  · intro h rho hrho
    obtain ⟨C, hC⟩ := h (rho + 1) (by linarith)
    exact ⟨C, fun i y hy => hC i y (lt_of_le_of_lt hy (by linarith))⟩

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

theorem distanceCurvatureEscape_of_not_boundedAtDistance {eps kappa sigma : ℝ}
    {Phi : ℝ → ℝ} (X : NormalizedSequence.{u} eps kappa sigma Phi)
    (h : ¬ BoundedAtDistance X) : DistanceCurvatureEscape X := by
  obtain ⟨radius, hinner, houter⟩ := exists_escape_radius_core X h
  exact ⟨radius, nonneg_of_unbounded_beyond houter, hinner, houter⟩

theorem positiveDistanceCurvatureEscape_of_curvatureBoundedWithin {eps kappa sigma : ℝ}
    {Phi : ℝ → ℝ} (X : NormalizedSequence.{u} eps kappa sigma Phi)
    (h : ¬ BoundedAtDistance X) {r : ℝ} (hr : 0 < r) (hb : CurvatureBoundedWithin X r) :
    PositiveDistanceCurvatureEscape X := by
  obtain ⟨radius, hinner, houter⟩ := exists_escape_radius_core X h
  have hle : r ≤ radius := by
    by_contra hcon
    have hlt : radius < r := lt_of_not_ge hcon
    obtain ⟨C, hC⟩ := hb
    obtain ⟨i, y, hy, hcy⟩ := houter ((radius + r) / 2) (by linarith) C
    exact absurd (hC i y (lt_trans hy (by linarith))) (not_le.mpr hcy)
  exact ⟨radius, lt_of_lt_of_le hr hle, hinner, houter⟩

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
