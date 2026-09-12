import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.FiniteHistory
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.GeometricCutoff
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.StandardCap.Metric
import DifferentialGeometry.Geometry.Metric.Sphere.Round.Metric
import DifferentialGeometry.Geometry.Metric.Convergence.Defs
import DifferentialGeometry.Geometry.Metric.Distance.Ball
import DifferentialGeometry.Geometry.Metric.CurveSpeedCalculus
import DifferentialGeometry.Geometry.Curvature.DimensionThree.CurvatureOperator.Metric
import DifferentialGeometry.Geometry.Operator.Laplacian.Basic
import DifferentialGeometry.Geometry.Operator.Gradient.NormSquared
import DifferentialGeometry.Analysis.Integration.Measure.Riemannian.Invariance
import DifferentialGeometry.Topology.Manifold.PartialDiffeomorph.Composition
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

noncomputable def riemannianBallVolume {M : Type u} [TopologicalSpace M]
    [ChartedSpace ThreeSpace M] [IsManifold ThreeModel ∞ M]
    [T2Space M] [SigmaCompactSpace M]
    (g : SmoothRiemannianMetric ThreeModel M) (p : M) (r : ℝ) : ℝ :=
  ((DifferentialGeometry.Integral.Measure.riemannianVolumeMeasure (I := ThreeModel) (M := M) g)
    (DifferentialGeometry.riemannianBallOf (I := ThreeModel) g p r)).toReal

noncomputable def reducedAction {M : Type u} [TopologicalSpace M]
    [ChartedSpace ThreeSpace M] [IsManifold ThreeModel ∞ M]
    (g : ℝ → SmoothRiemannianMetric ThreeModel M) (t₀ : ℝ) (τ : ℝ) (γ : ℝ → M) : ℝ :=
  ∫ s in (0 : ℝ)..τ,
    Real.sqrt s *
      (metricScalarAt (g (t₀ - s)) (γ s) +
        DifferentialGeometry.Geometry.riemannianCurveSpeed (g (t₀ - s)) γ s ^ 2)

noncomputable def reducedLength {M : Type u} [TopologicalSpace M]
    [ChartedSpace ThreeSpace M] [IsManifold ThreeModel ∞ M]
    (g : ℝ → SmoothRiemannianMetric ThreeModel M) (t₀ : ℝ)
    (admissible : (ℝ → M) → Prop) (p : M) (τ : ℝ) (x : M) : ℝ :=
  sInf {r : ℝ | ∃ γ : ℝ → M,
    admissible γ ∧ γ 0 = p ∧ γ τ = x ∧ reducedAction g t₀ τ γ = r}

noncomputable def reducedVolume {M : Type u} [TopologicalSpace M]
    [ChartedSpace ThreeSpace M] [IsManifold ThreeModel ∞ M]
    [T2Space M] [SigmaCompactSpace M]
    (g : ℝ → SmoothRiemannianMetric ThreeModel M) (t₀ : ℝ)
    (admissible : (ℝ → M) → Prop) (p : M) (τ : ℝ) (V : Set M) : ℝ≥0∞ :=
  ∫⁻ x in V, ENNReal.ofReal
    ((4 * Real.pi * τ) ^ (-(3 / 2 : ℝ)) *
      Real.exp (-(reducedLength g t₀ admissible p τ x) / (2 * Real.sqrt τ)))
    ∂(DifferentialGeometry.Integral.Measure.riemannianVolumeMeasure (I := ThreeModel) (M := M)
      (g (t₀ - τ)))

def isLocalStabilityInput : Prop :=
  ∀ θ : ℝ, 0 < θ → θ < 1 → ∀ K : ℝ, 0 < K →
    ∀ (L : ℕ → ℝ) (_hLpos : ∀ i, 0 < L i) (_hLtop : Tendsto L atTop atTop)
      (v : ℕ → ℝ) (hv : ∀ i, 0 < v i) (_hvθ : ∀ i, v i ≤ θ)
      (γ : SmoothRiemannianMetric ThreeModel ThreeSpace)
      (ℓ : (i : ℕ) → SolutionOn (I := ThreeModel) (M := ↥(ModelBall (L i)))
        (RealTimeInterval.closed (0 : ℝ) (v i) (le_of_lt (hv i)))),
      (∀ i, DifferentialGeometry.PDE.RicciFlow.IsSolutionOn (ℓ i)) →
      (∀ i, ∀ x : ↥(ModelBall (L i)),
        curvatureNormSq ((ℓ i).base.metric (v i)) x
          (DifferentialGeometry.Geometry.Curvature.metricRm04At (I := ThreeModel)
            (M := ↥(ModelBall (L i))) ((ℓ i).base.metric (v i)) x) ≤ K ^ 2) →
      (∀ A : Set ThreeSpace, IsCompact A → ∀ p : ℕ,
        Tendsto (fun i => metricDerivNormSupOn (Subtype.val ⁻¹' A) p ((ℓ i).base.metric 0)
          (γ.restrictOpen (ModelBall (L i))) (γ.restrictOpen (ModelBall (L i))))
          atTop (𝓝 0)) →
      ∀ A : Set ThreeSpace, IsCompact A → ∀ m : ℕ, 4 ≤ m →
        Tendsto (fun i => sSup {r : ℝ | ∃ u ∈ Set.Icc (0 : ℝ) (v i),
          metricDerivNormSupOn (Subtype.val ⁻¹' A) m ((ℓ i).base.metric u)
            (γ.restrictOpen (ModelBall (L i))) (γ.restrictOpen (ModelBall (L i))) = r})
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

inductive TrackedFace where
  | incoming
  | observed

structure TrackedChart (P : OrientedThreeStage.{u}) (G : ℝ → P.Metric)
    (J : PartialDiffeomorph ThreeModel ThreeModel ThreeSpace P.Carrier ∞) (q L K : ℝ) where
  time : ℝ
  time_nonneg : 0 ≤ time
  time_le : time ≤ q
  face : TrackedFace
  flow : ℝ → ThreeSpace → P.Carrier
  flow_zero : Set.EqOn (flow 0) ⇑J (Metric.ball (0 : ThreeSpace) L)
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
  curvature_bound : ∀ s ∈ Icc (0 : ℝ) time, ∀ x : ThreeSpace, ‖x‖ ≤ L →
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
  scale : ℝ
  scale_pos : 0 < scale

def ProtectedSurvives {c : CapClass} (D : AdmissibleDatum.{u} c) (a : ℝ)
    (i : Fin D.history.eventCount) : Prop :=
  Nonempty (BackwardRealization
    (fun u => (D.history.event i).incoming.flow.base.metric u) (D.history.time i.succ) (a / 4))

def IsLossEvent {c : CapClass} (D : AdmissibleDatum.{u} c) (a : ℝ)
    (i : Fin D.history.eventCount) : Prop :=
  ¬ ProtectedSurvives D a i

def IsStoppingFace {c : CapClass} (D : AdmissibleDatum.{u} c) (a θ : ℝ) (T : ℝ) : Prop :=
  T ∈ Icc a (a + θ / D.scale) ∧
    ((∃ i : Fin D.history.eventCount, IsLossEvent D a i ∧ T = D.history.time i.succ ∧
        ∀ j : Fin D.history.eventCount, IsLossEvent D a j → a < D.history.time j.succ →
          T ≤ D.history.time j.succ) ∨
      ((¬ ∃ i : Fin D.history.eventCount, IsLossEvent D a i ∧ a < D.history.time i.succ ∧
          D.history.time i.succ ≤ a + θ / D.scale) ∧
        T = min D.history.horizon (a + θ / D.scale)))

def isBufferedControlInput : Prop :=
  ∀ c : CapClass, ∀ θ : ℝ, 0 < θ → θ < 1 →
    ∃ K : ℝ, 1 ≤ K ∧
      ∀ a : ℝ, 1 < a → ∀ L : ℝ, a + 3 < L →
        ∃ L₀ : ℝ, L + 2 < L₀ ∧ ∃ N₀ : ℕ, 4 ≤ N₀ ∧ ∃ ζ₀ : ℝ, 0 < ζ₀ ∧
          ∃ δ₀ : ℝ, 0 < δ₀ ∧
            ∀ D : AdmissibleDatum.{u} c, D.precision ≤ δ₀ →
              ∀ seed : PreparedCapSeed D.history L₀ N₀ ζ₀,
                ∀ T : ℝ, IsStoppingFace D a θ T →
                  ∃ C : TrackedChart (D.history.stage 0) D.ambientMetric seed.chart T L K,
                    ((∃ i : Fin D.history.eventCount, IsLossEvent D a i ∧
                        T = D.history.time i.succ) → C.face = TrackedFace.incoming) ∧
                    ((¬ ∃ i : Fin D.history.eventCount, IsLossEvent D a i ∧
                        T = D.history.time i.succ) → C.face = TrackedFace.observed) ∧
                    Nonempty (BackwardRealization (fun u => D.ambientMetric u) T (L / 4))

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
  pole : (H.stage 0).Carrier
  start : ℝ
  finish : ℝ
  start_nonneg : 0 ≤ start
  finish_le_horizon : finish ≤ H.horizon
  start_lt_finish : start < finish
  radius : ℝ
  radius_pos : 0 < radius
  metricAt : ℝ → (H.stage 0).Metric
  admissible : (ℝ → (H.stage 0).Carrier) → Prop
  regular : (ℝ → (H.stage 0).Carrier) → Prop
  regular_admissible : ∀ γ, regular γ → admissible γ

namespace VariationalStrip

noncomputable def reducedLength {H : ObservedHistory.{u}} (S : VariationalStrip H) (u : ℝ)
    (x : (H.stage 0).Carrier) : ℝ :=
  DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.reducedLength
    S.metricAt S.finish S.admissible S.pole (S.finish - u) x

end VariationalStrip

def isSurgeryVariationalInput : Prop :=
  ∀ (H : ObservedHistory.{u}) (S : VariationalStrip H),
    (∀ u ∈ Ioo S.start S.finish,
      LowerSemicontinuousOn (fun x => S.reducedLength u x)
        (univ : Set (H.stage 0).Carrier) ∧
      (∃ x : (H.stage 0).Carrier,
        IsLeast (range (fun y => S.reducedLength u y)) (S.reducedLength u x)) ∧
      (∀ x : (H.stage 0).Carrier,
        IsLeast (range (fun y => S.reducedLength u y)) (S.reducedLength u x) →
          ∃ γ : ℝ → (H.stage 0).Carrier,
            S.admissible γ ∧ γ 0 = S.pole ∧ γ (S.finish - u) = x ∧
              reducedAction S.metricAt S.finish (S.finish - u) γ = S.reducedLength u x)) ∧
    (∀ u ∈ Ioo S.start S.finish, ∀ x : (H.stage 0).Carrier,
      IsLeast (range (fun y => S.reducedLength u y)) (S.reducedLength u x) →
      (∀ γ : ℝ → (H.stage 0).Carrier, S.admissible γ → γ 0 = S.pole →
        γ (S.finish - u) = x →
        reducedAction S.metricAt S.finish (S.finish - u) γ = S.reducedLength u x →
        S.regular γ) →
      ∀ η : ℝ, 0 < η →
        ∃ (U : TopologicalSpace.Opens (H.stage 0).Carrier) (hxU : x ∈ U)
          (F : ℝ → ↥U → ℝ) (hF : ∀ σ : ℝ, ContMDiff ThreeModel 𝓘(ℝ, ℝ) ∞ (F σ)),
          F u ⟨x, hxU⟩ = S.reducedLength u x ∧
          (∀ y : ↥U, y ≠ ⟨x, hxU⟩ →
            F u y < S.reducedLength u (y : (H.stage 0).Carrier)) ∧
          deriv (fun σ : ℝ => F σ ⟨x, hxU⟩) u +
            DifferentialGeometry.Geometry.Operator.ΔG (I := ThreeModel) (M := ↥U)
              ((S.metricAt u).restrictOpen U) (⟨F u, hF u⟩ : C^∞⟮ThreeModel, ↥U; ℝ⟯) ⟨x, hxU⟩
            ≤ 6 + η ∧
          Real.sqrt (DifferentialGeometry.Geometry.Operator.normGradSqFun (I := ThreeModel)
            (M := ↥U) ((S.metricAt u).restrictOpen U) (F u) ⟨x, hxU⟩) ≤ η) ∧
    (∀ u ∈ Ioo S.start S.finish,
      LowerSemicontinuousWithinAt
        (fun τ : ℝ => sInf (range (fun x => S.reducedLength (S.finish - τ) x)) - 6 * τ)
        (Ioo S.start S.finish) (S.finish - u))

structure JacobianStrip (H : ObservedHistory.{u}) where
  pole : (H.stage 0).Carrier
  start : ℝ
  poleTime : ℝ
  start_nonneg : 0 ≤ start
  start_lt : start < poleTime
  poleTime_le_horizon : poleTime ≤ H.horizon
  radius : ℝ
  radius_pos : 0 < radius
  metricAt : ℝ → (H.stage 0).Metric
  admissible : (ℝ → (H.stage 0).Carrier) → Prop
  regular : (ℝ → (H.stage 0).Carrier) → Prop
  regular_admissible : ∀ γ, regular γ → admissible γ

noncomputable def regularMinimizingSet {H : ObservedHistory.{u}}
    (g : ℝ → (H.stage 0).Metric) (t₀ : ℝ)
    (admissible regular : (ℝ → (H.stage 0).Carrier) → Prop) (p : (H.stage 0).Carrier)
    (τ : ℝ) : Set (H.stage 0).Carrier :=
  {x | ∃ γ : ℝ → (H.stage 0).Carrier,
    admissible γ ∧ regular γ ∧ γ 0 = p ∧ γ τ = x ∧
      reducedAction g t₀ τ γ = reducedLength g t₀ admissible p τ x}

def isJacobianInput : Prop :=
  ∀ _d : OldData, ∃ modul : ℝ → ℝ,
    (∀ v : ℝ, 0 < v → 0 < modul v) ∧ Monotone modul ∧
    (∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧ ∀ v : ℝ, 0 < v → v < δ → modul v < ε) ∧
    ∀ (H : ObservedHistory.{u}) (S : JacobianStrip H) (s : ℝ),
      s ∈ Ioo S.start S.poleTime → S.radius ^ 2 < S.poleTime - s →
      letI : MeasurableSpace (H.stage 0).Carrier := borel (H.stage 0).Carrier
      ∀ (V : Set (H.stage 0).Carrier), MeasurableSet V →
      V ⊆ regularMinimizingSet S.metricAt S.poleTime S.admissible S.regular S.pole
        (S.poleTime - s) →
      ∀ v : ℝ, 0 < v →
        riemannianBallVolume (S.metricAt S.poleTime) S.pole S.radius < v * S.radius ^ 3 →
          reducedVolume S.metricAt S.poleTime S.admissible S.pole (S.poleTime - s) V ≤
            ENNReal.ofReal (modul v)

def isOldTubeInput (d : OldData) : Prop :=
  ∀ ρ : ℝ, 0 < ρ →
    ∃ s : ℝ, 0 < s ∧ s ≤ min (d.epsilon / 2) (Real.sqrt (d.energyBound / 24)) ∧
      ∃ dOld : ℝ, 0 < dOld ∧
        ∀ (H : ObservedHistory.{u}) (P : CutoffParameters) (i : Fin H.eventCount) (t : ℝ)
          (x : (H.stage i.castSucc).Carrier),
          P.delta t ≤ dOld →
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
  cover : C(Sphere 3, Z)
  cover_isCoveringMap : IsCoveringMap (cover : Sphere 3 → Z)
  isRound : ∀ x : Z, ∃ e : PartialDiffeomorph (𝓡 3) (𝓡 3) (Sphere 3) Z ∞,
    x ∈ e.target ∧ ∀ y ∈ e.source, ∀ (V W : TangentSpace (𝓡 3) y),
      k.inner (e y) (mfderiv (𝓡 3) (𝓡 3) e y V) (mfderiv (𝓡 3) (𝓡 3) e y W) =
        (DifferentialGeometry.Geometry.roundMetric
          (E := EuclideanSpace ℝ (Fin 4)) (n := 3)).inner y V W

def sphereThreeBasePoint : Sphere 3 :=
  ⟨EuclideanSpace.single 0 1, by simp⟩

def RoundCovering.degree {Z : Type u} [TopologicalSpace Z] [ChartedSpace ThreeSpace Z]
    [IsManifold ThreeModel ∞ Z] {k : SmoothRiemannianMetric ThreeModel Z}
    (C : RoundCovering Z k) : ℕ :=
  (C.cover ⁻¹' {C.cover sphereThreeBasePoint}).ncard

theorem RoundCovering.degree_eq_one_of_injective {Z : Type u} [TopologicalSpace Z]
    [ChartedSpace ThreeSpace Z] [IsManifold ThreeModel ∞ Z]
    {k : SmoothRiemannianMetric ThreeModel Z} (C : RoundCovering Z k)
    (h : Function.Injective C.cover) : C.degree = 1 := by
  rw [RoundCovering.degree, Set.ncard_eq_one]
  refine ⟨sphereThreeBasePoint, ?_⟩
  apply Set.eq_singleton_iff_unique_mem.mpr
  refine ⟨rfl, ?_⟩
  intro y hy
  exact h hy

def isRoundDegreeInput : Prop :=
  ∀ _d : OldData, ∃ Nold : ℕ, 1 ≤ Nold ∧
    ∀ (H : ObservedHistory.{u}) (_S : EnlargementStrip H), ∀ Z : Type u,
      ∀ [TopologicalSpace Z] [ChartedSpace ThreeSpace Z] [IsManifold ThreeModel ∞ Z],
        ∀ k : SmoothRiemannianMetric ThreeModel Z,
          Nonempty (RoundCovering Z k) →
            ∃ C : RoundCovering Z k, 1 ≤ C.degree ∧ C.degree ≤ Nold

def isCommonLocalRealization : Prop :=
  isLocalStabilityInput ∧ isBufferedControlInput.{u} ∧ isSurgeryVariationalInput.{u} ∧
    isJacobianInput.{u} ∧ (∃ d : OldData, isOldTubeInput.{u} d) ∧
      isEnlargementInput.{u} ∧ isRoundDegreeInput.{u}

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
