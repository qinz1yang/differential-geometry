import DifferentialGeometry.Geometry.Curvature.Metric.LeviCivita
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.AncientCanonicalNeighborhood
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.ConeConvergence
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHornDirectionCompactness
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHornStructureHonest
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.SameManifoldWindowCompactness
import DifferentialGeometry.Geometry.Flow.RicciFlow.Solution.Stationary
import DifferentialGeometry.Geometry.Metric.RicciSoliton.Models

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
  PointedRiemannianManifold.topology PointedRiemannianManifold.charted
  PointedRiemannianManifold.smooth PointedRiemannianManifold.t2
  PointedRiemannianManifold.sigmaCompact

structure CheegerGromovLimit (X : FlowSequence.{u}) where
  space : Type u
  [metric_space : MetricSpace space]
  [charted : ChartedSpace ThreeSpace space]
  [smooth : IsManifold I3 ∞ space]
  [sigmaCompact : SigmaCompactSpace space]
  metric : SmoothRiemannianMetric I3 space
  subseq : ℕ → ℕ
  strictMono : StrictMono subseq
  maps : ∀ i, PartialDiffeomorph I3 I3 space ((X.term (subseq i)).M) ∞
  exhaustion : ExhaustsByOpen (fun i => (maps i).source)
  convergence : ∀ K : Set space, IsCompact K → ∀ m : ℕ, ∀ eta : ℝ, 0 < eta →
    ∀ᶠ i in Filter.atTop, K ⊆ (maps i).source ∧
      Nonempty (MetricComparisonOn (fun _ => metric)
        (fun _ => (X.term (subseq i)).S.base.metric 0) (maps i) K {0} m eta)

attribute [local instance] CheegerGromovLimit.metric_space CheegerGromovLimit.charted
  CheegerGromovLimit.smooth CheegerGromovLimit.sigmaCompact

structure HornOnLimit (X : FlowSequence.{u}) (L : CheegerGromovLimit X) where
  horn : FiniteHorn L.metric
  radii : ℕ → ℝ
  radii_mem : ∀ i, radii i ∈ Set.Ioc 0 horn.axial.length
  radii_zero : Filter.Tendsto radii Filter.atTop (nhds 0)
  directionNet : ScaleDirectionNet L.metric horn
  separatedRays : ScaleSeparatedEndRays L.metric horn
  coneRealization : ∀ (angles : EndAngles horn) (ray : EndRay horn.endpoint) (d : ℕ → ℝ),
    (∀ i, d i ∈ Set.Ioc 0 ray.length) → Filter.Tendsto d Filter.atTop (nhds 0) →
    ConeDistanceRealization horn angles ray d
  depth_ok : hornDepthThreshold L.space ≤ horn.collar_depth
  curvatureUpper : ScaleCurvatureUpperBound horn horn.axial radii

namespace RealizedFiniteHorn

def toCheegerGromovLimit {X : FlowSequence.{u}} (H : RealizedFiniteHorn X) :
    CheegerGromovLimit X where
  space := H.space
  metric_space := H.metric_space
  charted := H.charted
  smooth := H.smooth
  sigmaCompact := H.sigmaCompact
  metric := H.metric
  subseq := H.subseq
  strictMono := H.strictMono
  maps := H.maps
  exhaustion := H.exhaustion
  convergence := H.convergence

def toHornOnLimit {X : FlowSequence.{u}} (H : RealizedFiniteHorn X) :
    HornOnLimit X H.toCheegerGromovLimit where
  horn := H.horn
  radii := H.radii
  radii_mem := H.radii_mem
  radii_zero := H.radii_zero
  directionNet := H.directionNet
  separatedRays := H.separatedRays
  coneRealization := H.coneRealization
  depth_ok := H.depth_ok
  curvatureUpper := H.curvatureUpper

def ofParts {X : FlowSequence.{u}} (L : CheegerGromovLimit X) (K : HornOnLimit X L) :
    RealizedFiniteHorn X where
  space := L.space
  metric_space := L.metric_space
  charted := L.charted
  smooth := L.smooth
  sigmaCompact := L.sigmaCompact
  metric := L.metric
  horn := K.horn
  subseq := L.subseq
  strictMono := L.strictMono
  maps := L.maps
  exhaustion := L.exhaustion
  convergence := L.convergence
  radii := K.radii
  radii_mem := K.radii_mem
  radii_zero := K.radii_zero
  directionNet := K.directionNet
  separatedRays := K.separatedRays
  coneRealization := K.coneRealization
  depth_ok := K.depth_ok
  curvatureUpper := K.curvatureUpper

theorem ofParts_toCheegerGromovLimit {X : FlowSequence.{u}} (L : CheegerGromovLimit X)
    (K : HornOnLimit X L) : (ofParts L K).toCheegerGromovLimit = L := rfl

theorem ofParts_toHornOnLimit {X : FlowSequence.{u}} (L : CheegerGromovLimit X)
    (K : HornOnLimit X L) :
    (ofParts L K).toHornOnLimit = K := rfl

end RealizedFiniteHorn

theorem nonempty_realizedFiniteHorn_iff_exists_cheegerGromovLimit_horn
    {X : FlowSequence.{u}} :
    Nonempty (RealizedFiniteHorn X) ↔
      ∃ L : CheegerGromovLimit X, Nonempty (HornOnLimit X L) := by
  constructor
  · rintro ⟨H⟩
    exact ⟨H.toCheegerGromovLimit, ⟨H.toHornOnLimit⟩⟩
  · rintro ⟨L, ⟨K⟩⟩
    exact ⟨RealizedFiniteHorn.ofParts L K⟩

theorem exhaustsByOpen_diffeomorphFamily_sources {X : FlowSequence.{u}}
    {space : Type u} [MetricSpace space] [ChartedSpace ThreeSpace space]
    [IsManifold I3 ∞ space] [SigmaCompactSpace space] (subseq : ℕ → ℕ)
    (phi : ∀ i, Diffeomorph I3 I3 space ((X.term (subseq i)).M) ∞) :
    ExhaustsByOpen (fun i => ((phi i).toPartialDiffeomorph :
      PartialDiffeomorph I3 I3 space ((X.term (subseq i)).M) ∞).source) := by
  have hsrc : (fun i => ((phi i).toPartialDiffeomorph :
      PartialDiffeomorph I3 I3 space ((X.term (subseq i)).M) ∞).source) =
      fun _ : ℕ => (Set.univ : Set space) := by
    funext i
    simp [Diffeomorph.toPartialDiffeomorph]
  rw [hsrc]
  exact exhaustsByOpen_univ space

theorem nonempty_cheegerGromovLimit_of_diffeomorphFamily {X : FlowSequence.{u}}
    {space : Type u} [MetricSpace space] [ChartedSpace ThreeSpace space]
    [IsManifold I3 ∞ space] [SigmaCompactSpace space]
    (metric : SmoothRiemannianMetric I3 space) {subseq : ℕ → ℕ} (hmono : StrictMono subseq)
    (phi : ∀ i, Diffeomorph I3 I3 space ((X.term (subseq i)).M) ∞)
    (hconv : ∀ K : Set space, IsCompact K → ∀ m : ℕ, ∀ eta : ℝ, 0 < eta →
      ∀ᶠ i in Filter.atTop, Nonempty (MetricComparisonOn (fun _ => metric)
        (fun _ => (X.term (subseq i)).S.base.metric 0)
        ((phi i).toPartialDiffeomorph :
          PartialDiffeomorph I3 I3 space ((X.term (subseq i)).M) ∞) K {0} m eta)) :
    Nonempty (CheegerGromovLimit X) := by
  let L : CheegerGromovLimit X :=
    { space := space
      metric := metric
      subseq := subseq
      strictMono := hmono
      maps := fun i => (phi i).toPartialDiffeomorph
      exhaustion := exhaustsByOpen_diffeomorphFamily_sources subseq phi
      convergence := by
        intro K hK m eta heta
        filter_upwards [hconv K hK m eta heta] with i hi
        exact ⟨fun _ hx => Set.mem_univ _, hi⟩ }
  exact ⟨L⟩

def HornOnLimitRealization.{v} (kappa sigma : ℝ) (Phi : ℝ → ℝ) : Prop :=
  ∃ epsStar : ℝ, 0 < epsStar ∧ ∀ eps : ℝ, 0 < eps → eps ≤ epsStar →
    ∀ X : NormalizedSequence.{v} eps kappa sigma Phi,
      RealizedDistanceCurvatureEscape X →
        ∃ L : CheegerGromovLimit X.toFlowSequence, Nonempty (HornOnLimit X.toFlowSequence L)

theorem escapeFiniteHornRealization_iff_hornOnLimitRealization
    {kappa sigma : ℝ} {Phi : ℝ → ℝ} :
    EscapeFiniteHornRealization.{u} kappa sigma Phi ↔
      HornOnLimitRealization.{u} kappa sigma Phi := by
  constructor
  · rintro ⟨e, he, hmain⟩
    exact ⟨e, he, fun eps hp hle X hX =>
      nonempty_realizedFiniteHorn_iff_exists_cheegerGromovLimit_horn.mp
        (hmain eps hp hle X hX)⟩
  · rintro ⟨e, he, hmain⟩
    exact ⟨e, he, fun eps hp hle X hX =>
      nonempty_realizedFiniteHorn_iff_exists_cheegerGromovLimit_horn.mpr
        (hmain eps hp hle X hX)⟩

theorem not_nonempty_finiteHorn_of_ricciTensor_eq_zero
    {W : Type u} [MetricSpace W] [ChartedSpace ThreeSpace W] [IsManifold I3 ∞ W]
    [SigmaCompactSpace W] (g : SmoothRiemannianMetric I3 W)
    (hric : ∀ x (v w : TangentSpace I3 x), ricciTensor g x v w = 0) :
    ¬ Nonempty (FiniteHorn g) := by
  rintro ⟨H⟩
  obtain ⟨i, hi⟩ := H.curvature_diverges 0
  obtain ⟨d, hd, hdle, htail⟩ := H.cofinal_axial i
  have hs : d / 2 ∈ Set.Ioc (0 : ℝ) d := ⟨by linarith, by linarith⟩
  have hmem : H.axial.point (d / 2) ∈ H.subend i := htail (d / 2) hs
  have hpos : 0 < metricScalarAt g (H.axial.point (d / 2)) := hi _ hmem
  have hzero : metricScalarAt g (H.axial.point (d / 2)) = 0 :=
    metricScalarAt_eq_zero_of_ricciTensor_eq_zero g _ (hric _)
  rw [hzero] at hpos
  exact lt_irrefl 0 hpos

theorem not_nonempty_finiteHorn_euclideanMetric :
    ¬ Nonempty (FiniteHorn (euclideanMetric (E := ThreeSpace))) :=
  not_nonempty_finiteHorn_of_ricciTensor_eq_zero (euclideanMetric (E := ThreeSpace))
    (fun x v w => _root_.DifferentialGeometry.Geometry.euclideanMetric_ricciTensor x v w)

theorem not_nonempty_hornOnLimit_of_ricciTensor_eq_zero {X : FlowSequence.{u}}
    (L : CheegerGromovLimit X)
    (hric : ∀ x (v w : TangentSpace I3 x), ricciTensor L.metric x v w = 0) :
    ¬ Nonempty (HornOnLimit X L) := by
  rintro ⟨K⟩
  exact not_nonempty_finiteHorn_of_ricciTensor_eq_zero L.metric hric ⟨K.horn⟩

theorem hornOnLimit_annularConvergence {X : FlowSequence.{u}} (L : CheegerGromovLimit X)
    (K : HornOnLimit X L) (endData : EndGeometry K.horn) (angles : EndAngles K.horn)
    (ray : EndRay K.horn.endpoint) (d : ℕ → ℝ) (hd : ∀ i, d i ∈ Set.Ioc 0 ray.length)
    (hzero : Filter.Tendsto d Filter.atTop (nhds 0)) :
    Nonempty (AnnularConvergence K.horn angles ray d) :=
  (RealizedFiniteHorn.ofParts L K).cone_convergence endData angles ray d hd hzero

def euclideanFlowSequence : FlowSequence.{0} where
  interval _ := RealTimeInterval.closed (-1) 0 (by norm_num)
  term _ :=
    { M := ThreeSpace
      basepoint := 0
      S := SolutionOn.const (euclideanMetric (E := ThreeSpace))
        (RealTimeInterval.closed (-1) 0 (by norm_num))
      isSolution := isSolutionOn_const_of_ricciTensor_eq_zero
        (euclideanMetric (E := ThreeSpace))
        (fun x v w => _root_.DifferentialGeometry.Geometry.euclideanMetric_ricciTensor x v w)
        (RealTimeInterval.closed (-1) 0 (by norm_num)) }

def cheegerGromovLimitEuclidean : CheegerGromovLimit euclideanFlowSequence where
  space := ThreeSpace
  metric := euclideanMetric (E := ThreeSpace)
  subseq := id
  strictMono := strictMono_id
  maps := fun _ => PartialDiffeomorph.refl (I := I3) ThreeSpace
  exhaustion := exhaustsByOpen_univ ThreeSpace
  convergence := by
    intro K _hK m eta heta
    filter_upwards with i
    refine ⟨Set.subset_univ K, ?_⟩
    simpa only [euclideanFlowSequence, SolutionOn.const_metric] using
      (⟨metricComparisonOnRefl (fun _ => euclideanMetric (E := ThreeSpace)) K {0} m heta⟩ :
        Nonempty (MetricComparisonOn (fun _ => euclideanMetric (E := ThreeSpace))
          (fun _ => euclideanMetric (E := ThreeSpace))
          (PartialDiffeomorph.refl (I := I3) ThreeSpace) K {0} m eta))

theorem nonempty_cheegerGromovLimit_euclideanFlowSequence :
    Nonempty (CheegerGromovLimit euclideanFlowSequence) :=
  ⟨cheegerGromovLimitEuclidean⟩

@[simp] theorem cheegerGromovLimitEuclidean_metric :
    cheegerGromovLimitEuclidean.metric = euclideanMetric (E := ThreeSpace) :=
  rfl

theorem not_nonempty_hornOnLimit_euclideanFlowSequence :
    ¬ Nonempty (HornOnLimit euclideanFlowSequence cheegerGromovLimitEuclidean) := by
  rintro ⟨K⟩
  exact not_nonempty_finiteHorn_euclideanMetric ⟨K.horn⟩

end DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn
