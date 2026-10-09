import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.ExteriorDiskFlow
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.CanonicalNeighborhood.UniformEstimates
import DifferentialGeometry.Geometry.Collapse.CurvatureScale

set_option autoImplicit false
noncomputable section
open DifferentialGeometry DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Curvature.DimensionThree
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
open DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn
open DifferentialGeometry.Geometry.Collapse Set
open scoped Manifold ContDiff ENNReal
namespace GC.LongTime
universe u

def hasCommonNeckAccuracy {P : OrientedThreeStage.{u}} {g : P.Metric}
    (F : GC.Interface.RawSurgery P g) (δ : ℝ → ℝ) : Prop :=
  ∀ n : ℕ, ∃ p : CutoffParameters, p.delta = δ ∧
    ∀ i : Fin (F.tower.history n).eventCount,
      Nonempty (GeometricCutoffRecord (F.tower.history n).toHistory i p)

theorem hasCommonNeckAccuracy.bounds {P : OrientedThreeStage.{u}} {g : P.Metric}
    {F : GC.Interface.RawSurgery P g} {δ : ℝ → ℝ} (h : hasCommonNeckAccuracy F δ)
    (t : ℝ) (ht : 0 ≤ t) : 0 < δ t ∧ δ t < 1 := by
  obtain ⟨p, hp, _⟩ := h 0
  rw [← hp]
  exact ⟨p.delta_pos t ht, p.delta_lt_one t ht⟩

def hasSmallParabolicCurvature (H : ObservedHistory.{u})
    (t : Icc (0 : ℝ) H.horizon) (p : (H.stageAt t).Carrier) (r : ℝ) : Prop :=
  0 < r ∧ ∃ (a : Icc (0 : ℝ) H.horizon) (hat : a ≤ t),
    (a : ℝ) = (t : ℝ) - r ^ 2 ∧
      ∀ x ∈ riemannianBallOf (H.stageMetric (H.activeStage t) t) p r,
        ∃ trace : BackwardPointTrace H (H.activeStage a) (H.activeStage t)
            (H.activeStage_mono hat) x,
          trace.isRmControlled (hat := hat) (Real.sqrt 3 * r)

structure AnalyticSurgeryProfile {P : OrientedThreeStage.{u}} {g : P.Metric}
    (F : GC.Interface.RawSurgery P g) (δ : ℝ → ℝ) where
  parameters : CutoffParameters
  accuracy_eq : parameters.delta = δ
  records : ∀ n (i : Fin (F.tower.history n).eventCount),
    GeometricCutoffRecord (F.tower.history n).toHistory i parameters
  canonical_windows : ∀ n i b, ((records n i).static b).hasCanonicalWindow
  radius_antitone : AntitoneOn parameters.neckRadius (Ici 0)
  epsilon : ℝ
  epsilon_pos : 0 < epsilon
  epsilon_small : epsilon < 1 / 100
  C1 : ℝ
  C2 : ℝ
  C1_ge_one : 1 ≤ C1
  C2_ge_one : 1 ≤ C2
  canonical : ∀ t, 0 ≤ t → ∀ x : (postStage F.observation t).Carrier,
    (parameters.neckRadius t ^ 2)⁻¹ < metricScalarAt (postMetric F.observation t) x →
    ∃ W : SpatialCanonicalWitness (postMetric F.observation t) epsilon C1 C2 x,
      W.capTubeHasNeckChart epsilon
  kappa : ℝ → ℝ
  kappa_pos : ∀ t, 0 ≤ t → 0 < kappa t
  kappa_antitone : AntitoneOn kappa (Ici 0)
  noncollapsed : ∀ n, (F.tower.history n).NoncollapsedBefore (kappa n) epsilon n
  scalarShift : ℝ
  scalarShift_pos : 0 < scalarShift
  scalar_lower : ∀ t, 0 ≤ t → ∀ x : (postStage F.observation t).Carrier,
    -3 / (2 * (t + scalarShift)) ≤ metricScalarAt (postMetric F.observation t) x
  pinchingShift : ℝ
  pinchingShift_pos : 0 < pinchingShift
  pinching : ∀ t, 0 ≤ t → ∀ x : (postStage F.observation t).Carrier,
    InFixedHamiltonIveyRegion (postMetric F.observation t) (pinchingShift + t) x
  largerBallAccuracy : ℝ → ℝ → ℝ
  largerBallAccuracy_pos : ∀ A t, 0 < A → 0 ≤ t → 0 < largerBallAccuracy A t
  largerBallAccuracy_antitone_time : ∀ A, 0 < A → AntitoneOn (largerBallAccuracy A) (Ici 0)
  largerBallAccuracy_antitone_radius : ∀ t, 0 ≤ t →
    AntitoneOn (fun A => largerBallAccuracy A t) (Ioi 0)
  diagonal_smallness : ∀ t, 0 < t → δ t < largerBallAccuracy (2 * t) (2 * t)
  larger_ball_scalar_control : ∀ A, 0 < A → ∃ rbar K : ℝ, 0 < rbar ∧ 0 < K ∧
    ∀ n, let H := (F.tower.history n).toHistory;
    ∀ (t : Icc (0 : ℝ) H.horizon) (p : (H.stageAt t).Carrier) (r : ℝ),
      2 * r ^ 2 < (t : ℝ) →
      (∀ s ∈ Icc ((t : ℝ) / 2) t, δ s < largerBallAccuracy A s) →
      hasSmallParabolicCurvature H t p r →
      ENNReal.ofReal (A⁻¹ * r ^ 3) ≤ ballVolume (H.stageMetric (H.activeStage t) t) p r →
      r ≤ rbar * Real.sqrt t →
      ∀ q ∈ riemannianBallOf (H.stageMetric (H.activeStage t) t) p (A * r),
        metricScalarAt (H.stageMetric (H.activeStage t) t) q ≤ K * (r ^ 2)⁻¹
  recent_cutoff_smallness : ∀ ε : ℝ, 0 < ε → ∃ T : ℝ, 0 < T ∧
    ∀ t, T ≤ t → ∀ n (i : Fin (F.tower.history n).eventCount),
      (F.tower.history n).time i.succ ∈ Icc (t / 2) t →
      ∀ h, (records n i).nominalRadius h ≤ ε * parameters.neckRadius t

def hasAnalyticAdmissibility {P : OrientedThreeStage.{u}} {g : P.Metric}
    (F : GC.Interface.RawSurgery P g) (δ : ℝ → ℝ) : Prop :=
  Nonempty (AnalyticSurgeryProfile F δ)

theorem AnalyticSurgeryProfile.commonNeckAccuracy {P : OrientedThreeStage.{u}} {g : P.Metric}
    {F : GC.Interface.RawSurgery P g} {δ : ℝ → ℝ} (p : AnalyticSurgeryProfile F δ) :
    hasCommonNeckAccuracy F δ :=
  fun n => ⟨p.parameters, p.accuracy_eq, fun i => ⟨p.records n i⟩⟩

theorem AnalyticSurgeryProfile.largerBallAccuracy_on_late_half_interval
    {P : OrientedThreeStage.{u}} {g : P.Metric}
    {F : GC.Interface.RawSurgery P g} {δ : ℝ → ℝ} (p : AnalyticSurgeryProfile F δ)
    {A t s : ℝ} (hA : 0 < A) (ht : A ≤ t) (hs : s ∈ Icc (t / 2) t) :
    δ s < p.largerBallAccuracy A s := by
  have htpos : 0 < t := hA.trans_le ht
  have hspos : 0 < s := lt_of_lt_of_le (by linarith : 0 < t / 2) hs.1
  have hAs : A ≤ 2 * s := by linarith [hs.1]
  have h2s : 0 < 2 * s := by linarith
  have hrad := p.largerBallAccuracy_antitone_radius (2 * s) h2s.le
    (show A ∈ Ioi 0 from hA) (show 2 * s ∈ Ioi 0 from h2s) hAs
  have htime := p.largerBallAccuracy_antitone_time A hA
    (show s ∈ Ici 0 from hspos.le) (show 2 * s ∈ Ici 0 from h2s.le)
    (by linarith : s ≤ 2 * s)
  exact (p.diagonal_smallness s hspos).trans_le (hrad.trans htime)


end GC.LongTime
