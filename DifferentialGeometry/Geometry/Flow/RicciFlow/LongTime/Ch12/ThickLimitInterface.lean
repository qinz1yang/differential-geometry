import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.AnalyticAdmissibility
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.RegularSlice
import DifferentialGeometry.Geometry.Hyperbolic.FiniteVolumeModel
import DifferentialGeometry.Geometry.Compactness.CheegerGromov.Pointed.Convergence.Defs
import DifferentialGeometry.Geometry.Compactness.CheegerGromov.Pointed.ModelChange
import DifferentialGeometry.Geometry.Compactness.CheegerGromov.Pointed.Compactness.Construction

/-!
# CH12-S13 / IF2: interface layer for LTF01, LTF03, LTF05

Transparent definitions and theorem-shaped `Prop`s (no proofs of LTF) following review CH12-R1 Q4.
Normalisation: `ḡ_t = t⁻¹ g(t)`, `sec(h_H) = -1/4`.
-/

set_option autoImplicit false
noncomputable section
open DifferentialGeometry DifferentialGeometry.Topology DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Hyperbolic DifferentialGeometry.Geometry.Collapse
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
open DifferentialGeometry.CheegerGromovCompactness
open GC.LongTime Set Filter
open scoped Manifold ContDiff ENNReal Topology
namespace GC.LongTime.Ch12
universe u

/-- Total volume of the normalised slice `t⁻¹ g(t)`. -/
def normalizedTotalVolume_S13 {P : OrientedThreeStage.{u}} {g : P.Metric}
    {T : ObservationTower P g} (s : RegularSlice T) : ℝ≥0∞ :=
  Integral.Measure.riemannianVolumeMeasure ThreeModel s.stage.Carrier s.normalizedMetric univ

/-- `Ric_g = c g` pointwise. -/
def RicciEqualsMetricMultiple_S13 {M : Type*} [TopologicalSpace M]
    [ChartedSpace ThreeSpace M] [IsManifold ThreeModel ∞ M] [T2Space M] [SigmaCompactSpace M]
    (g : SmoothRiemannianMetric ThreeModel M) (c : ℝ) : Prop :=
  ∀ (p : M) (v w : TangentSpace ThreeModel p),
    ricciTensor g p v w = c * g.inner p v w

/-- Sectional curvature lower bound `-a⁻²` on `B(p,a)` and volume `≥ v a³` of the normalised
slice metric. -/
def HasNormalizedSeed_S13 {P : OrientedThreeStage.{u}} {g : P.Metric}
    {T : ObservationTower P g} (s : RegularSlice T) (p : s.stage.Carrier) (a v : ℝ) : Prop :=
  (∀ q ∈ riemannianBallOf s.normalizedMetric p a,
      DifferentialGeometry.Geometry.Riemannian.SectionalBoundedBelowAt s.normalizedMetric q (-(a ^ 2)⁻¹)) ∧
    ENNReal.ofReal (v * a ^ 3) ≤ ballVolume s.normalizedMetric p a

/-- `‖2 Ric(ḡ) + ḡ‖_ḡ (p)`, as the operator norm over `ḡ`-unit-ball vectors. -/
def NormalizedRicciDefect_S13 {P : OrientedThreeStage.{u}} {g : P.Metric}
    {T : ObservationTower P g} (s : RegularSlice T) (p : s.stage.Carrier) : ℝ :=
  sSup {r : ℝ | ∃ v w : TangentSpace ThreeModel p,
    s.normalizedMetric.inner p v v ≤ 1 ∧ s.normalizedMetric.inner p w w ≤ 1 ∧
      r = |2 * ricciTensor s.normalizedMetric p v w + s.normalizedMetric.inner p v w|}

/-- Actual late point sequence (review §4.1). -/
structure LatePointSequence_S13 {P : OrientedThreeStage.{u}} {g : P.Metric}
    (F : GC.Interface.RawSurgery P g) where
  slices : ℕ → RegularSlice F.observation
  times_tendsto : Tendsto (fun j => (slices j).time) atTop atTop
  point : (j : ℕ) → (slices j).stage.Carrier

namespace LatePointSequence_S13
variable {P : OrientedThreeStage.{u}} {g : P.Metric} {F : GC.Interface.RawSurgery P g}

def subsequence (S : LatePointSequence_S13 F) (σ : ℕ → ℕ) (hσ : StrictMono σ) :
    LatePointSequence_S13 F where
  slices j := S.slices (σ j)
  times_tendsto := S.times_tendsto.comp hσ.tendsto_atTop
  point j := S.point (σ j)

/-- The pointed Riemannian sequence of normalised slices `(M_j, ḡ_{t_j}, p_j)`. -/
def pointedSeq (S : LatePointSequence_S13 F) :
    PointedRiemannianSeq.{u, 0, 0} (I := ThreeModel) where
  obj j :=
    { M := (S.slices j).stage.Carrier
      topology := inferInstance
      charted := inferInstance
      smooth := inferInstance
      sigmaCompact := inferInstance
      t2 := inferInstance
      t2TangentBundle := inferInstance
      basepoint := S.point j
      metric := (S.slices j).normalizedMetric }

end LatePointSequence_S13

/-- `IsWThickSequence S w`: each point has finite positive curvature radius `r` and normalised ball
volume `≥ w r³`. -/
def IsWThickSequence_S13 {P : OrientedThreeStage.{u}} {g : P.Metric}
    {F : GC.Interface.RawSurgery P g} (S : LatePointSequence_S13 F) (w : ℝ) : Prop :=
  ∀ j, ∃ r : ℝ, 0 < r ∧
    curvatureRadius (S.slices j).normalizedMetric (S.point j) = ENNReal.ofReal r ∧
      ENNReal.ofReal (w * r ^ 3) ≤ ballVolume (S.slices j).normalizedMetric (S.point j) r

/-- The pointed Riemannian manifold underlying a finite-volume hyperbolic model. -/
def modelPointed_S13 (M : FiniteVolumeHyperbolicModel.{u}) :
    PointedRiemannianManifold.{u, 0, 0} (I := ThreeModel) where
  M := M.Carrier
  topology := inferInstance
  charted := inferInstance
  smooth := inferInstance
  sigmaCompact := inferInstance
  t2 := inferInstance
  t2TangentBundle := inferInstance
  basepoint := M.basepoint
  metric := M.metric

/-- Pointed smooth convergence: exhausting pointed partial diffeomorphisms and `C^p`-convergence
of the pullback metrics on compacta for every `p`.  The convergence is *canonical*
(`C.domain k = canonicalSourceData Φ k`, reference metric = limit metric); with a free reference
metric `MetricConvergenceData` carries no information (CH12-S17, finding F1 of CH12-O5). -/
def PointedSmoothConverges_S13 {P : OrientedThreeStage.{u}} {g : P.Metric}
    {F : GC.Interface.RawSurgery P g} (S : LatePointSequence_S13 F)
    (M : FiniteVolumeHyperbolicModel.{u}) : Prop :=
  ∃ Φ : PointedRiemannianConvergenceMaps S.pointedSeq (modelPointed_S13 M) id,
    ∃ C : MetricConvergenceData Φ,
      ∀ k, C.domain k = CanonicalMetricCompactness.canonicalSourceData Φ k

def IsActualWThickLimit_S13 {P : OrientedThreeStage.{u}} {g : P.Metric}
    (F : GC.Interface.RawSurgery P g) (w : ℝ) (M : FiniteVolumeHyperbolicModel.{u}) : Prop :=
  ∃ S : LatePointSequence_S13 F, IsWThickSequence_S13 S w ∧ PointedSmoothConverges_S13 S M

def PointedModelsConverge_S13 (models : ℕ → FiniteVolumeHyperbolicModel.{u})
    (M : FiniteVolumeHyperbolicModel.{u}) : Prop :=
  ∃ Φ : PointedRiemannianConvergenceMaps
      (⟨fun j => modelPointed_S13 (models j)⟩ : PointedRiemannianSeq.{u, 0, 0} (I := ThreeModel))
      (modelPointed_S13 M) id,
    ∃ C : MetricConvergenceData Φ,
      ∀ k, C.domain k = CanonicalMetricCompactness.canonicalSourceData Φ k

/-- Negative-scalar branch: eventually every nonempty regular slice has a point of negative scalar
curvature (`R_min(t) < 0`). -/
def EventuallyNegativeScalar_S13 {P : OrientedThreeStage.{u}} {g : P.Metric}
    (F : GC.Interface.RawSurgery P g) : Prop :=
  ∃ B : ℝ, ∀ s : RegularSlice F.observation, B < s.time → Nonempty s.stage.Carrier →
    ∃ x : s.stage.Carrier, metricScalarAt s.metric x < 0

end GC.LongTime.Ch12
