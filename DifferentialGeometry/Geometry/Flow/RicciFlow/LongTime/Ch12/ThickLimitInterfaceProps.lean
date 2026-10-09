import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch12.ThickLimitInterface
import DifferentialGeometry.Topology.Manifold.ULift
import DifferentialGeometry.Geometry.Metric.Euclidean

/-!
# CH12-S13 / IF2 (2): the actual compactness record and the five LTF theorem shapes

Everything here is a definition (`structure` / `def … : Prop`); no theorem is asserted.
-/

set_option autoImplicit false
noncomputable section
open DifferentialGeometry DifferentialGeometry.Topology DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Hyperbolic DifferentialGeometry.Geometry.Collapse
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
open DifferentialGeometry.CheegerGromovCompactness
open GC.LongTime Set Filter DifferentialGeometry.Topology
open scoped Manifold ContDiff ENNReal Topology
namespace GC.LongTime.Ch12
universe u

/-- Actual unscathed parabolic limit of `t_j⁻¹ g(t_j s)` (review §4.1): an open (not necessarily
complete) limit manifold, a time-dependent limit metric solving Ricci flow, and for each `s` in
the time interval actual regular slices at times `t_j s` with pointed smooth convergence of the
rescaled actual metrics. -/
structure ActualUnscathedParabolicLimit_S13 {P : OrientedThreeStage.{u}} {g : P.Metric}
    (F : GC.Interface.RawSurgery P g) where
  Carrier : Type u
  [topology : TopologicalSpace Carrier]
  [charts : ChartedSpace ThreeSpace Carrier]
  [smooth : IsManifold ThreeModel ∞ Carrier]
  [hausdorff : T2Space Carrier]
  [sigmaCompact : SigmaCompactSpace Carrier]
  basepoint : Carrier
  timeInterval : Set ℝ
  interval_open : IsOpen timeInterval
  interval_pos : timeInterval ⊆ Ioi 0
  metric : ℝ → SmoothRiemannianMetric ThreeModel Carrier
  flow : ∀ s ∈ timeInterval, ∀ (x : Carrier) (v w : TangentSpace ThreeModel x),
    HasDerivAt (fun τ => (metric τ).inner x v w) (-2 * ricciTensor (metric s) x v w) s
  times : ℕ → ℝ
  times_pos : ∀ j, 0 < times j
  times_tendsto : Tendsto times atTop atTop
  slice : ℕ → ∀ s ∈ timeInterval, RegularSlice F.observation
  slice_time : ∀ j s (hs : s ∈ timeInterval), (slice j s hs).time = times j * s
  point : ∀ j, ∀ s (hs : s ∈ timeInterval), (slice j s hs).stage.Carrier
  /-- the actual rescaled slices `t_j⁻¹ g(t_j s)` pointed-converge to the limit at time `s` -/
  converges : ∀ s (hs : s ∈ timeInterval),
    ∃ Φ : PointedRiemannianConvergenceMaps
        (⟨fun j =>
          { M := (slice j s hs).stage.Carrier
            topology := inferInstance
            charted := inferInstance
            smooth := inferInstance
            sigmaCompact := inferInstance
            t2 := inferInstance
            t2TangentBundle := inferInstance
            basepoint := point j s hs
            metric := scaleMetric (times j)⁻¹ (inv_pos.mpr (times_pos j))
              (slice j s hs).metric }⟩ : PointedRiemannianSeq.{u, 0, 0} (I := ThreeModel))
        ({ M := Carrier
           topology := topology
           charted := charts
           smooth := smooth
           sigmaCompact := sigmaCompact
           t2 := hausdorff
           t2TangentBundle := inferInstance
           basepoint := basepoint
           metric := metric s } : PointedRiemannianManifold.{u, 0, 0} (I := ThreeModel)) id,
      ∃ C : MetricConvergenceData Φ,
        ∀ k, C.domain k = CanonicalMetricCompactness.canonicalSourceData Φ k

/-- Feasibility: the empty-time-interval datum exists for every `F` (flat `ℝ³`, `ULift`ed, as
limit manifold; nothing is converging).  It is the "empty family" case only: a nonempty-interval
inhabitant is exactly what actual compactness (LTF05) must produce and is not unconditional. -/
def ActualUnscathedParabolicLimit_S13.empty {P : OrientedThreeStage.{u}} {g : P.Metric}
    (F : GC.Interface.RawSurgery P g) : ActualUnscathedParabolicLimit_S13 F :=
  letI : ChartedSpace ThreeSpace (ULift.{u} ThreeSpace) := uliftChartedSpace _ _
  haveI : IsManifold ThreeModel ∞ (ULift.{u} ThreeSpace) := isManifold_ulift _ _
  { Carrier := ULift.{u} ThreeSpace
    basepoint := ULift.up 0
    timeInterval := ∅
    interval_open := isOpen_empty
    interval_pos := empty_subset _
    metric := fun _ => Diffeomorph.pullbackMetricCross euclideanMetric
      (uliftDiffeomorph ThreeModel ThreeSpace).symm
    flow := fun s hs => absurd hs (notMem_empty s)
    times := fun j => (j : ℝ) + 1
    times_pos := fun j => by positivity
    times_tendsto := tendsto_atTop_add_const_right _ 1 tendsto_natCast_atTop_atTop
    slice := fun _ s hs => absurd hs (notMem_empty s)
    slice_time := fun _ s hs => absurd hs (notMem_empty s)
    point := fun _ s hs => absurd hs (notMem_empty s)
    converges := fun s hs => absurd hs (notMem_empty s) }

/-- LTF01a (shape): uniform normalised total-volume bound on slices with `t ≥ 1`
(aligned with CH12-S10 `normalized_volume_bounded`). -/
def NormalizedVolumeBounded_S13 {P : OrientedThreeStage.{u}} {g : P.Metric}
    {F : GC.Interface.RawSurgery P g} {δ : ℝ → ℝ} (_H : AnalyticSurgeryProfile F δ) : Prop :=
  ∃ V : ℝ, 0 < V ∧ ∀ s : RegularSlice F.observation, 1 ≤ s.time →
    normalizedTotalVolume_S13 s ≤ ENNReal.ofReal V

/-- LTF01b (shape): hyperbolic rigidity of an actual local limit. -/
def VolumeDeficitHyperbolicLimit_S13 {P : OrientedThreeStage.{u}} {g : P.Metric}
    {F : GC.Interface.RawSurgery P g} {δ : ℝ → ℝ} (_H : AnalyticSurgeryProfile F δ)
    (_hdec : ∀ ε : ℝ, 0 < ε → ∃ B : ℝ, ∀ t : ℝ, B < t → δ t < ε)
    (_hneg : EventuallyNegativeScalar_S13 F) : Prop :=
  ∀ Q : ActualUnscathedParabolicLimit_S13 F, ∀ s ∈ Q.timeInterval,
    letI : TopologicalSpace Q.Carrier := Q.topology
    letI : ChartedSpace ThreeSpace Q.Carrier := Q.charts
    letI : IsManifold ThreeModel ∞ Q.Carrier := Q.smooth
    letI : T2Space Q.Carrier := Q.hausdorff
    letI : SigmaCompactSpace Q.Carrier := Q.sigmaCompact
    RicciEqualsMetricMultiple_S13 (Q.metric s) (-(2 * s)⁻¹) ∧
      hasConstantSectionalCurvature (Q.metric s) (-(4 * s)⁻¹)

/-- LTF03 (shape). -/
def SeedHyperbolicOnFixedBallsSeq_S13 {P : OrientedThreeStage.{u}} {g : P.Metric}
    {F : GC.Interface.RawSurgery P g} {δ : ℝ → ℝ} (_H : AnalyticSurgeryProfile F δ)
    (_hdec : ∀ ε : ℝ, 0 < ε → ∃ B : ℝ, ∀ t : ℝ, B < t → δ t < ε)
    (_hneg : EventuallyNegativeScalar_S13 F) (S : LatePointSequence_S13 F)
    (a v L : ℝ) : Prop :=
  0 < a → 0 < v → 0 < L →
  (∀ j, HasNormalizedSeed_S13 (S.slices j) (S.point j) a v) →
    ∀ ε : ℝ, 0 < ε → ∀ᶠ j in atTop,
      ∀ q ∈ riemannianBallOf (S.slices j).normalizedMetric (S.point j) L,
        NormalizedRicciDefect_S13 (S.slices j) q < ε

/-- LTF05a (shape): every `w`-thick actual late sequence has a hyperbolically convergent
subsequence. -/
def ThickSequenceHasHyperbolicSubsequence_S13 {P : OrientedThreeStage.{u}} {g : P.Metric}
    {F : GC.Interface.RawSurgery P g} {δ : ℝ → ℝ} (_H : AnalyticSurgeryProfile F δ)
    (_hdec : ∀ ε : ℝ, 0 < ε → ∃ B : ℝ, ∀ t : ℝ, B < t → δ t < ε)
    (_hneg : EventuallyNegativeScalar_S13 F) (w : ℝ) : Prop :=
  0 < w → ∀ S : LatePointSequence_S13 F, IsWThickSequence_S13 S w →
    ∃ σ : ℕ → ℕ, ∃ hσ : StrictMono σ, ∃ M : FiniteVolumeHyperbolicModel.{u},
      PointedSmoothConverges_S13 (S.subsequence σ hσ) M

/-- LTF05b (shape): sequential compactness of actual `w`-thick limits. -/
def ActualThickLimitsSequentiallyCompact_S13 {P : OrientedThreeStage.{u}} {g : P.Metric}
    {F : GC.Interface.RawSurgery P g} {δ : ℝ → ℝ} (_H : AnalyticSurgeryProfile F δ)
    (_hdec : ∀ ε : ℝ, 0 < ε → ∃ B : ℝ, ∀ t : ℝ, B < t → δ t < ε)
    (_hneg : EventuallyNegativeScalar_S13 F) (w : ℝ) : Prop :=
  0 < w → ∀ models : ℕ → FiniteVolumeHyperbolicModel.{u},
    (∀ j, IsActualWThickLimit_S13 F w (models j)) →
    ∃ σ : ℕ → ℕ, StrictMono σ ∧ ∃ M : FiniteVolumeHyperbolicModel.{u},
      IsActualWThickLimit_S13 F w M ∧ PointedModelsConverge_S13 (fun j => models (σ j)) M

end GC.LongTime.Ch12
