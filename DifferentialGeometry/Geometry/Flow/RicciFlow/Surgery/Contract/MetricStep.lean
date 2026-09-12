import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.FiniteHistory
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.StandardCap.Metric
import DifferentialGeometry.Geometry.Metric.Sphere.Round.Metric
import DifferentialGeometry.Geometry.Metric.Convergence.Defs
import DifferentialGeometry.Geometry.Curvature.DimensionThree.CurvatureOperator.Metric
import DifferentialGeometry.Analysis.TimeInterval
import Mathlib.Data.ENNReal.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
import Mathlib.Topology.Algebra.Order.LiminfLimsup
import Mathlib.MeasureTheory.Measure.Haar.Basic
import Mathlib.Topology.Covering.Basic

set_option autoImplicit false

noncomputable section

open Bundle Manifold Set Topology Filter
open DifferentialGeometry.CheegerGromovCompactness
open DifferentialGeometry.Geometry.Curvature
open scoped Manifold ContDiff Topology ENNReal

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

open DifferentialGeometry (SmoothRiemannianMetric)

universe u

def curvatureNormSq {M : Type u} [TopologicalSpace M]
    [ChartedSpace ThreeSpace M] [IsManifold ThreeModel ∞ M]
    (g : SmoothRiemannianMetric ThreeModel M) (x : M)
    (A : DifferentialGeometry.Geometry.Curvature.Tensor04At (I := ThreeModel) (M := M) x) : ℝ :=
  DifferentialGeometry.Tensor0SBundle.normSq0S (I := ThreeModel) (M := M) g x 4 A

abbrev ModelBall (L : ℝ) : TopologicalSpace.Opens ThreeSpace :=
  ⟨Metric.ball (0 : ThreeSpace) L, Metric.isOpen_ball⟩

def isLocalStabilityInput : Prop :=
  ∀ θ : ℝ, 0 < θ → θ < 1 → ∀ K : ℝ, 0 < K →
    ∀ L : ℝ, 0 < L →
      ∀ (v : ℕ → ℝ) (hv : ∀ i, 0 < v i) (_hvθ : ∀ i, v i ≤ θ)
        (γ : SmoothRiemannianMetric ThreeModel ThreeSpace)
        (ℓ : (i : ℕ) → SolutionOn (I := ThreeModel) (M := ↥(ModelBall L))
          (RealTimeInterval.closed (0 : ℝ) (v i) (le_of_lt (hv i)))),
      (∀ i, DifferentialGeometry.PDE.RicciFlow.IsSolutionOn (ℓ i)) →
      (∀ i, ∀ x : ↥(ModelBall L),
        curvatureNormSq ((ℓ i).base.metric (v i)) x
          (DifferentialGeometry.Geometry.Curvature.metricRm04At (I := ThreeModel)
            (M := ↥(ModelBall L)) ((ℓ i).base.metric (v i)) x) ≤ K ^ 2) →
      (∀ A : Set ThreeSpace, IsCompact A →
        MetricCPConvergenceOn (Subtype.val ⁻¹' A) 0 (fun i => (ℓ i).base.metric 0)
          (γ.restrictOpen (ModelBall L)) (γ.restrictOpen (ModelBall L))) →
      ∀ A : Set ThreeSpace, IsCompact A → ∀ m : ℕ, 4 ≤ m →
        Tendsto (fun i => sSup {r : ℝ | ∃ u ∈ Set.Icc (0 : ℝ) (v i),
          metricDerivNormSupOn (Subtype.val ⁻¹' A) m ((ℓ i).base.metric u)
            (γ.restrictOpen (ModelBall L)) (γ.restrictOpen (ModelBall L)) = r})
          atTop (𝓝 0)

structure StandardCapModel where
  solution : SmoothRiemannianMetric ThreeModel ThreeSpace
  initial : solution = standardCapMetric
  tip : ThreeSpace

structure CapClass where
  horizon : ℝ
  horizon_pos : 0 < horizon
  initialParameter : ℝ
  initialParameter_pos : 0 < initialParameter
  epsilon : ℝ
  epsilon_pos : 0 < epsilon
  comparisonConstant : ℝ
  comparisonConstant_pos : 0 < comparisonConstant
  volumeConstant : ℝ
  volumeConstant_pos : 0 < volumeConstant
  scaleLower : ℝ
  scaleLower_pos : 0 < scaleLower
  scaleUpper : ℝ
  scale_lt : scaleLower < scaleUpper

structure OldData where
  horizon : ℝ
  horizon_pos : 0 < horizon
  initialParameter : ℝ
  initialParameter_pos : 0 < initialParameter
  epsilon : ℝ
  epsilon_pos : 0 < epsilon
  comparisonConstant : ℝ
  comparisonConstant_pos : 0 < comparisonConstant
  volumeConstant : ℝ
  volumeConstant_pos : 0 < volumeConstant
  scaleLower : ℝ
  scaleLower_pos : 0 < scaleLower
  noncollapsing : ℝ
  noncollapsing_pos : 0 < noncollapsing
  olderLength : ℝ
  olderLength_pos : 0 < olderLength
  energyBound : ℝ
  olderLength_le_energy : olderLength ≤ energyBound

structure PreparedCapSeed (H : ObservedHistory.{u}) (L : ℝ) (N : ℕ) (ζ : ℝ) where
  chart : PartialDiffeomorph ThreeModel ThreeModel ThreeSpace (H.stage 0).Carrier ∞
  ball_subset_source : Metric.ball (0 : ThreeSpace) L ⊆ chart.source
  scale : ℝ
  scale_pos : 0 < scale
  order : ℕ
  order_lower : N ≤ order
  accuracy_pos : 0 < ζ

structure TrackedChart (P : OrientedThreeStage.{u}) (G : ℝ → P.Metric) (q L K : ℝ) where
  time : ℝ
  time_nonneg : 0 ≤ time
  time_le : time ≤ q
  flow : ℝ → ThreeSpace → P.Carrier
  flow_injective : ∀ s ∈ Icc (0 : ℝ) time, Function.Injective (flow s)
  domain : Set ThreeSpace
  domain_open : IsOpen domain
  wide : ∀ x : ThreeSpace, ‖x‖ ≤ L → x ∈ domain
  normalized_metric : ℝ → SmoothRiemannianMetric ThreeModel ThreeSpace
  normalized_metric_eq : ∀ s ∈ Icc (0 : ℝ) time,
    ∀ (x : ThreeSpace) (V W : TangentSpace ThreeModel x),
      (normalized_metric s).inner x V W = (q - s)⁻¹ *
        (G (q - s)).inner (flow s x)
          (mfderiv ThreeModel ThreeModel (flow s) x V)
          (mfderiv ThreeModel ThreeModel (flow s) x W)
  curvature_bound : ∀ s ∈ Icc (0 : ℝ) time, ∀ x : ThreeSpace,
    curvatureNormSq (normalized_metric s) x
      (DifferentialGeometry.Geometry.Curvature.metricRm04At (I := ThreeModel)
        (M := ThreeSpace) (normalized_metric s) x) ≤ K ^ 2

structure AdmissibleDatum (c : CapClass) where
  history : ObservedHistory.{u}
  eventCount_pos : 0 < history.eventCount
  horizon_le : history.horizon ≤ c.horizon
  ambientMetric : ℝ → (history.stage 0).Metric
  precision : ℝ
  precision_pos : 0 < precision
  lossTime : ℝ
  lossTime_mem : Icc 0 history.horizon

def isBufferedControlInput : Prop :=
  ∀ c : CapClass, ∀ θ : ℝ, 0 < θ → θ < 1 →
    ∃ K : ℝ, 1 ≤ K ∧
      ∀ a : ℝ, 1 < a → ∀ L : ℝ, a + 3 < L →
        ∃ L₀ : ℝ, L + 2 < L₀ ∧ ∃ N₀ : ℕ, 4 ≤ N₀ ∧ ∃ ζ₀ : ℝ, 0 < ζ₀ ∧
          ∃ δ₀ : ℝ, 0 < δ₀ ∧
            ∀ D : AdmissibleDatum.{u} c, D.precision ≤ δ₀ →
              ∀ _seed : PreparedCapSeed D.history L₀ N₀ ζ₀,
                ∃ T : ℝ, T ∈ Icc a (a + (K + 1) * θ) ∧
                  Nonempty (TrackedChart (D.history.stage 0) D.ambientMetric T L K)

structure CapEscapeModel where
  horizon : ℝ
  horizon_pos : 0 < horizon
  radius : ℝ
  radius_pos : 0 < radius
  tolerance : ℝ
  tolerance_pos : 0 < tolerance
  action : ℝ → (ℝ → ThreeSpace) → ℝ≥0∞

def isCapEscapeCostBarrier (C : CapEscapeModel) : Prop :=
  ∀ H : ℝ, 0 < H →
    ∃ A : ℝ, A < C.radius ∧ ∃ θ : ℝ, 0 < θ ∧ θ < 1 ∧
      ∀ v : ℝ, 0 < v → v ≤ θ →
      ∀ ξ : ℝ → ThreeSpace,
        (∀ u ∈ Icc 0 v, dist (ξ u) (0 : ThreeSpace) ≤ C.radius) →
        ENNReal.ofReal H < C.action v ξ

structure CapEscapeTransfer (H : ObservedHistory.{u}) where
  insertionTime : ℝ
  duration : ℝ
  duration_pos : 0 < duration
  depth : ℝ
  depth_pos : 0 < depth
  comparison : CapEscapeModel
  barrier : isCapEscapeCostBarrier comparison

structure VariationalStrip (H : ObservedHistory.{u}) where
  start : ℝ
  finish : ℝ
  start_nonneg : 0 ≤ start
  finish_le_horizon : finish ≤ H.horizon
  start_lt_finish : start < finish
  pole : (H.stage 0).Carrier
  radius : ℝ
  radius_pos : 0 < radius

structure ReducedLengthFunction {H : ObservedHistory.{u}}
    (S : VariationalStrip H) where
  value : (H.stage 0).Carrier → ℝ → ℝ
  admissible : (ℝ → (H.stage 0).Carrier) → Prop
  cost : (ℝ → (H.stage 0).Carrier) → ℝ

def IsMinimizingCurve {H : ObservedHistory.{u}}
    {S : VariationalStrip H}
    (L : ReducedLengthFunction S) (u : ℝ) (_hu : u ∈ Ioo S.start S.finish)
    (x : (H.stage 0).Carrier) (γ : ℝ → (H.stage 0).Carrier) : Prop :=
  L.admissible γ ∧ γ u = x ∧ L.cost γ = L.value x u ∧
  ∀ δ : ℝ → (H.stage 0).Carrier, L.admissible δ → δ u = x → L.cost γ ≤ L.cost δ

structure ReducedGeometry {H : ObservedHistory.{u}}
    (S : VariationalStrip H) where
  reducedLength : (H.stage 0).Carrier → ℝ → ℝ
  admissible : (ℝ → (H.stage 0).Carrier) → Prop
  lengthFunctional : (ℝ → (H.stage 0).Carrier) → ℝ
  ambientDerivative : ((H.stage 0).Carrier → ℝ) → (H.stage 0).Carrier → ℝ
  supportOperator : ((H.stage 0).Carrier → ℝ) → (H.stage 0).Carrier → ℝ
  spatialNorm : (H.stage 0).Carrier → ℝ → ℝ
  timeDerivative : ((H.stage 0).Carrier → ℝ) → (H.stage 0).Carrier → ℝ

def isSurgeryVariationalInput : Prop :=
  ∀ (H : ObservedHistory.{u}) (S : VariationalStrip H),
    ∃ G : ReducedGeometry S,
      (∀ u ∈ Ioo S.start S.finish,
        LowerSemicontinuousOn (fun x => G.reducedLength x u) (univ : Set (H.stage 0).Carrier) ∧
        ∃ x : (H.stage 0).Carrier, IsLeast (range (G.reducedLength · u)) (G.reducedLength x u)) ∧
      (∀ u ∈ Ioo S.start S.finish, ∀ x : (H.stage 0).Carrier,
        IsLeast (range (G.reducedLength · u)) (G.reducedLength x u) →
        ∀ η : ℝ, 0 < η →
          ∃ F : (H.stage 0).Carrier → ℝ,
            F x = G.reducedLength x u ∧
            (∀ y : (H.stage 0).Carrier, y ≠ x → F y < G.reducedLength y u) ∧
            G.timeDerivative F x + G.supportOperator F x ≤ 6 + η ∧
            G.spatialNorm x (G.ambientDerivative F x) ≤ η) ∧
      (∃ u : ℝ, u ∈ Ioo S.start S.finish ∧
        ∃ x : (H.stage 0).Carrier, IsLeast (range (G.reducedLength · u))
          (G.reducedLength x u) ∧
        G.reducedLength x u < 0)

structure JacobianStrip (H : ObservedHistory.{u}) where
  pole : (H.stage 0).Carrier
  start : ℝ
  poleTime : ℝ
  start_nonneg : 0 ≤ start
  start_lt : start < poleTime
  poleTime_le_horizon : poleTime ≤ H.horizon
  radius : ℝ
  radius_pos : 0 < radius
  density : (H.stage 0).Carrier → ℝ

def isJacobianInput : Prop :=
  ∃ modul : ℝ → ℝ, (∀ v : ℝ, 0 < v → 0 < modul v) ∧
    Monotone modul ∧
    (∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧ ∀ v : ℝ, 0 < v → v < δ → modul v < ε) ∧
    ∀ (H : ObservedHistory.{u}) (S : JacobianStrip H),
      letI : MeasurableSpace (H.stage 0).Carrier := borel (H.stage 0).Carrier
      ∀ μ : MeasureTheory.Measure (H.stage 0).Carrier,
        (μ Set.univ).toReal ≤ (modul S.radius).toNNReal

structure BackwardRealization {M : Type u} [TopologicalSpace M]
    [ChartedSpace ThreeSpace M] [IsManifold ThreeModel ∞ M]
    (metric : ℝ → SmoothRiemannianMetric ThreeModel M) (t s : ℝ) where
  chart : PartialDiffeomorph ThreeModel ThreeModel ThreeSpace M ∞
  zero_mem_source : (0 : ThreeSpace) ∈ chart.source
  ball_subset_source : Metric.ball (0 : ThreeSpace) (4 * s) ⊆ chart.source
  curvature_bound : ∀ u ∈ Icc (t - 4 * s ^ 2) t,
    ∀ x ∈ Metric.ball (0 : ThreeSpace) (4 * s),
      curvatureNormSq (metric u) (chart x)
        (DifferentialGeometry.Geometry.Curvature.metricRm04At (I := ThreeModel)
          (M := M) (metric u) (chart x)) ≤ (s ^ 2)⁻¹

def isOldTubeInput (d : OldData) : Prop :=
  ∀ ρ : ℝ, 0 < ρ →
    ∃ s : ℝ, 0 < s ∧ 2 * s ≤ d.epsilon ∧ 24 * s ^ 2 ≤ d.energyBound ∧
      ∀ (H : ObservedHistory.{u}) (i : Fin H.eventCount) (t : ℝ)
        (x : (H.stage i.castSucc).Carrier),
        H.time i.castSucc + (H.time i.succ - H.time i.castSucc) / 3 ≤ t →
        t ≤ H.time i.castSucc + 2 * (H.time i.succ - H.time i.castSucc) / 3 →
        metricScalarAt ((H.event i).incoming.flow.base.metric t) x ≤ ρ →
        Nonempty (BackwardRealization
          (fun u => (H.event i).incoming.flow.base.metric u) t s)

structure EnlargementStrip (H : ObservedHistory.{u}) where
  pole : (H.stage 0).Carrier
  poleTime : ℝ
  poleTime_nonneg : 0 ≤ poleTime
  poleTime_le_horizon : poleTime ≤ H.horizon
  radius : ℝ
  radius_pos : 0 < radius

structure SourceGeometry where
  carrier : Type u
  [topology : TopologicalSpace carrier]
  [charts : ChartedSpace ThreeSpace carrier]
  [smooth : IsManifold ThreeModel ∞ carrier]
  metric : SmoothRiemannianMetric ThreeModel carrier

attribute [instance] SourceGeometry.topology SourceGeometry.charts SourceGeometry.smooth

structure SourcePatch {H : ObservedHistory.{u}}
    (S : EnlargementStrip H) where
  geometry : SourceGeometry.{u}
  embedding : geometry.carrier → (H.stage 0).Carrier
  embedding_injective : Function.Injective embedding
  metric_bound : ∀ x : geometry.carrier, ∀ v : TangentSpace ThreeModel x,
    2 * geometry.metric.inner x v v
      ≤ (H.initialMetric 0).inner (embedding x)
        (mfderiv ThreeModel ThreeModel embedding x v)
        (mfderiv ThreeModel ThreeModel embedding x v)

inductive SourceCause where
  | frontier
  | curvatureContact

structure EnlargementConclusion {H : ObservedHistory.{u}}
    (S : EnlargementStrip H) where
  patch : SourcePatch S
  cause : SourceCause

def isEnlargementInput : Prop :=
  ∀ d : OldData, 0 < d.noncollapsing →
    ∃ α : ℝ, 0 < α ∧ α ≤ 1 / 100 ∧ ∃ sstar : ℝ, 0 < sstar ∧
      sstar ≤ d.epsilon / 2 ∧
        ∀ (H : ObservedHistory.{u}) (S : EnlargementStrip H),
          S.radius < min (α * d.scaleLower) (sstar / 4) →
          Nonempty (EnlargementConclusion S)

structure RoundCovering (Z : Type u) [TopologicalSpace Z] [ChartedSpace ThreeSpace Z]
    [IsManifold ThreeModel ∞ Z] (k : SmoothRiemannianMetric ThreeModel Z) where
  degree : ℕ
  degree_pos : 0 < degree
  cover : C(Sphere 3, Z)
  cover_isCoveringMap : IsCoveringMap (cover : Sphere 3 → Z)
  isRound : ∀ x : Z, ∃ e : PartialDiffeomorph (𝓡 3) (𝓡 3) (Sphere 3) Z ∞,
    x ∈ e.target ∧ ∀ y ∈ e.source, ∀ (V W : TangentSpace (𝓡 3) y),
      k.inner (e y) (mfderiv (𝓡 3) (𝓡 3) e y V) (mfderiv (𝓡 3) (𝓡 3) e y W) =
        (DifferentialGeometry.Geometry.roundMetric
          (E := EuclideanSpace ℝ (Fin 4)) (n := 3)).inner y V W

def isRoundDegreeInput : Prop :=
  ∀ _d : OldData, ∃ Nold : ℕ, 1 ≤ Nold ∧
    ∀ (H : ObservedHistory.{u}) (_S : EnlargementStrip H), ∀ Z : Type u,
      ∀ [TopologicalSpace Z] [ChartedSpace ThreeSpace Z] [IsManifold ThreeModel ∞ Z],
        ∀ k : SmoothRiemannianMetric ThreeModel Z,
          Nonempty (RoundCovering Z k) → ∃ C : RoundCovering Z k, C.degree ≤ Nold

def isCommonLocalRealization : Prop :=
  isLocalStabilityInput ∧ isBufferedControlInput.{u} ∧ isSurgeryVariationalInput.{u} ∧
    isJacobianInput.{u} ∧ (∃ d : OldData, isOldTubeInput.{u} d) ∧
      isEnlargementInput.{u} ∧ isRoundDegreeInput.{u}

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
