import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHornGeometry
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.OrientedBadPointSelection
import DifferentialGeometry.Geometry.Compactness.CheegerGromov.Pointed.Compactness.Construction

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
  PointedFlowData.t2TangentBundle PointedRiemannianManifold.topology
  PointedRiemannianManifold.charted PointedRiemannianManifold.smooth
  PointedRiemannianManifold.t2 PointedRiemannianManifold.sigmaCompact
  PointedRiemannianManifold.t2TangentBundle


structure FlowSequence where
  interval : ℕ → RealTimeInterval
  term : ∀ i, PointedFlowData.{u, 0, 0} I3 (interval i)

def FlowSequence.atTime (X : FlowSequence.{u}) (t : ℝ) : PointedRiemannianSeq I3 :=
  ⟨fun i => (X.term i).atTime t⟩

structure NormalizedSequence (eps kappa sigma : ℝ) (Phi : ℝ → ℝ)
    extends FlowSequence.{u} where
  depth : ℕ → ℝ
  scale : ℕ → ℝ
  depth_pos : ∀ i, 0 < depth i
  depth_buffer : ∀ i, modelDepth eps ≤ depth i
  scale_pos : ∀ i, 0 < scale i
  depth_tendsto : Filter.Tendsto depth Filter.atTop Filter.atTop
  scale_tendsto : Filter.Tendsto scale Filter.atTop Filter.atTop
  carrier_eq : ∀ i, (interval i).carrier = Set.Icc (-(2 * depth i)) 0
  regular_eq : ∀ i, (interval i).regular = Set.Ioo (-(2 * depth i)) 0
  connected : ∀ i, ConnectedSpace (term i).M
  orientation : ∀ i, TangentOrientationSection (term i).M
  complete : ∀ i t, t ∈ (interval i).carrier → MetricComplete ((term i).atTime t)
  source_bound : ∀ i, ∃ C : ℝ, PointedFlowRmNormSqBounded (term i) C
  base_one : ∀ i, PointedFlowScalarAtBase (term i) 1
  noncollapse : ∀ i, SpatiallyKappaNoncollapsedBelowScale
    (term i).S kappa (Real.sqrt (scale i) * sigma)
  pinching : ∀ i, PhiAlmostNonnegative (term i).S (interval i).carrier
    (rescalePinchingFunction (scale i) Phi)
  higher_good : ∀ i t, t ∈ Set.Icc (-depth i) 0 → ∀ x,
    2 ≤ (term i).S.scalar t x → OrientedWitness (term i).S (orientation i) eps kappa x t


def BoundedAtDistance {eps kappa sigma : ℝ} {Phi : ℝ → ℝ}
    (X : NormalizedSequence.{u} eps kappa sigma Phi) : Prop :=
  ∀ rho : ℝ, 0 < rho → ∃ C : ℝ, ∀ i, ∀ y,
    metricDistance ((X.term i).S.base.metric 0) (X.term i).basepoint y ≤ rho →
      (X.term i).S.scalar 0 y ≤ C


def TerminalDerivativeBounds {eps kappa sigma : ℝ} {Phi : ℝ → ℝ}
    (X : NormalizedSequence.{u} eps kappa sigma Phi) : Prop :=
  ∀ rho : ℝ, 0 < rho → ∀ a : ℕ, ∃ C : ℝ, ∀ i, ∀ y,
    metricDistance ((X.term i).S.base.metric 0) (X.term i).basepoint y ≤ rho →
      curvDerivNorm (I := I3) a ((X.term i).S.base.metric 0) y ≤ C


def MetricSourceCapture {X : PointedRiemannianSeq.{u, 0, 0} I3}
    {P : PointedRiemannianManifold.{u, 0, 0} I3} {f : ℕ → ℕ}
    (F : PointedRiemannianConvergenceMaps X P f) : Prop :=
  ∀ r : ℝ, 0 < r → ∀ᶠ i in Filter.atTop,
    riemannianBallOf (I := I3) (X.obj (f i)).metric (X.obj (f i)).basepoint r ⊆
      (F.partialDiffeomorph i) '' (F.partialDiffeomorph i).source


def subsequenceMaps {X : PointedRiemannianSeq.{u, 0, 0} I3}
    {P : PointedRiemannianManifold.{u, 0, 0} I3} {f : ℕ → ℕ}
    (F : PointedRiemannianConvergenceMaps X P f) (k : ℕ → ℕ) (hk : StrictMono k) :
    PointedRiemannianConvergenceMaps X P (f ∘ k) where
  partialDiffeomorph i := F.partialDiffeomorph (k i)
  source_exhausts := F.source_exhausts.comp_subseq hk
  base_mem i := F.base_mem (k i)
  basepoint_map i := F.basepoint_map (k i)


def MetricNoncollapsed (P : PointedRiemannianManifold.{u, 0, 0} I3)
    (kappa : ℝ) (scales : Set ℝ) : Prop :=
  ∀ x : P.M, ∀ r ∈ scales, 0 < r →
    (∀ y ∈ riemannianBallOf (I := I3) P.metric x r,
      r ^ 4 * Tensor0SBundle.normSq0S (I := I3) P.metric y 4 (metricRm04At P.metric y) ≤ 1) →
    ENNReal.ofReal (kappa * r ^ 3) ≤
      riemannianVolumeMeasure I3 P.M P.metric (riemannianBallOf (I := I3) P.metric x r)

theorem noncollapse_passes_to_limit (X : PointedRiemannianSeq.{u, 0, 0} I3)
    (P : PointedRiemannianManifold.{u, 0, 0} I3) (f : ℕ → ℕ) (hf : StrictMono f)
    (F : PointedRiemannianConvergenceMaps X P f) (conv : MetricConvergenceData F)
    (canonical_domains : ∀ k,
      conv.domain k = CanonicalMetricCompactness.canonicalSourceData F k)
    (capture : MetricSourceCapture F) (complete : MetricComplete P)
    {kappa : ℝ} (hkappa : 0 < kappa) (radii : ℕ → ℝ)
    (hradii : Filter.Tendsto radii Filter.atTop Filter.atTop)
    (hsource : ∀ i, MetricNoncollapsed (X.obj i) kappa (Set.Ioc 0 (radii i))) :
    MetricNoncollapsed P kappa Set.univ := by
  sorry

theorem blowup_limit_nonnegative {eps kappa sigma : ℝ} {Phi : ℝ → ℝ}
    (X : NormalizedSequence.{u} eps kappa sigma Phi) (hPhi : AdmissiblePinchingFunction Phi)
    (P : PointedRiemannianManifold.{u, 0, 0} I3) (f : ℕ → ℕ) (hf : StrictMono f)
    (F : PointedRiemannianConvergenceMaps (X.toFlowSequence.atTime 0) P f)
    (conv : MetricConvergenceData F)
    (canonical_domains : ∀ k,
      conv.domain k = CanonicalMetricCompactness.canonicalSourceData F k) :
    SecLower P.metric 0 Set.univ := by
  sorry

structure TerminalLimit {eps kappa sigma : ℝ} {Phi : ℝ → ℝ}
    (X : NormalizedSequence.{u} eps kappa sigma Phi) where
  space : PointedRiemannianManifold.{u, 0, 0} I3
  subseq : ℕ → ℕ
  strictMono : StrictMono subseq
  maps : PointedRiemannianConvergenceMaps (X.toFlowSequence.atTime 0) space subseq
  converges : MetricConvergenceData maps
  canonical_domains : ∀ k,
    converges.domain k = CanonicalMetricCompactness.canonicalSourceData maps k
  capture : MetricSourceCapture maps
  precompact : ∀ i, IsCompact (closure (maps.partialDiffeomorph i).source)
  connected_domains : ∀ i, IsConnected (maps.partialDiffeomorph i).source
  nested : ∀ i, closure (maps.partialDiffeomorph i).source ⊆ (maps.partialDiffeomorph (i + 1)).source
  connected : ConnectedSpace space.M
  orientation : TangentOrientationSection space.M
  orientation_preserved : ∀ i y, y ∈ (maps.partialDiffeomorph i).source →
    ∃ hf : Function.Bijective (mfderiv I3 I3 (maps.partialDiffeomorph i) y),
      PreservesTangentOrientationAt orientation (X.orientation (subseq i))
        (maps.partialDiffeomorph i) y hf
  complete : MetricComplete space
  nonnegative : SecLower space.metric 0 Set.univ
  scalar_one : metricScalarAt space.metric space.basepoint = 1
  scalar_bound : ∃ C : ℝ, ∀ x, metricScalarAt space.metric x ≤ C
  noncollapse : MetricNoncollapsed space kappa Set.univ

def ConvergesOn {X : FlowSequence.{u}} {P : PointedRiemannianManifold.{u, 0, 0} I3}
    {f : ℕ → ℕ} (F : PointedRiemannianConvergenceMaps (X.atTime 0) P f)
    {D : RealTimeInterval} (S : SolutionOn (I := I3) (M := P.M) D) : Prop :=
  ∀ K : Set P.M, IsCompact K → ∀ a b : ℝ, a ≤ b → Set.Icc a b ⊆ D.carrier →
    ∀ order : ℕ, ∀ eps : ℝ, 0 < eps → ∀ᶠ i in Filter.atTop,
      Set.Icc a b ⊆ (X.interval (f i)).carrier ∧
      K ⊆ (F.partialDiffeomorph i).source ∧
      Nonempty (MetricComparisonOn (fun s => S.base.metric s)
        (fun s => (X.term (f i)).S.base.metric s) (F.partialDiffeomorph i)
        K (Set.Icc a b) order eps)


structure BackwardExtension {eps kappa sigma : ℝ} {Phi : ℝ → ℝ}
    {X : NormalizedSequence.{u} eps kappa sigma Phi} (L : TerminalLimit X)
    (D : RealTimeInterval) where
  solution : SolutionOn (I := I3) (M := L.space.M) D
  isSolution : IsSolutionOn solution
  terminal : solution.base.metric 0 = L.space.metric
  subseq : ℕ → ℕ
  strictMono : StrictMono subseq
  convergence : ConvergesOn (subsequenceMaps L.maps subseq strictMono) solution
  complete : ∀ t ∈ D.carrier,
    MetricComplete { L.space with metric := solution.base.metric t }
  nonnegative : ∀ t ∈ D.carrier, SecLower (solution.base.metric t) 0 Set.univ
  compact_time_bound : ∀ a b : ℝ, a ≤ b → Set.Icc a b ⊆ D.carrier →
    ∃ C : ℝ, ∀ t ∈ Set.Icc a b, ∀ x, FlowMetricBall.rmNormSq solution t x ≤ C

end DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn
