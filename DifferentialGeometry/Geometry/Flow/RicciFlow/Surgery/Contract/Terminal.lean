import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.GeometricCutoff
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.MetricEvent
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.ClosedOrientedStage
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.HistoryExtension
import DifferentialGeometry.Topology.ThreeManifold.CutCapReconstruction
import DifferentialGeometry.Topology.ThreeManifold.PoincareStandard
import DifferentialGeometry.Topology.ThreeManifold.StandardFactors
import DifferentialGeometry.Geometry.Curvature.Riemann.SectionalCurvature
import DifferentialGeometry.Geometry.Metric.Distance.Ball
import Mathlib.Analysis.Calculus.IteratedDeriv.Defs

set_option autoImplicit false

noncomputable section

open Bundle Manifold Set Function Filter
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.CheegerGromovCompactness
open DifferentialGeometry.Topology
open scoped Manifold ContDiff Topology

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

universe u

structure OneStepIncoming where
  stage : OrientedThreeStage.{u}
  startTime : ℝ
  endTime : ℝ
  startTime_nonneg : 0 ≤ startTime
  startTime_lt_endTime : startTime < endTime
  slab : stage.IncomingSlab startTime endTime
  terminal : slab.TerminalLimitMetric
  singular : slab.SingularEndpoint
  parameters : CutoffParameters

namespace OneStepIncoming

def ofRecord {H : ObservedHistory.{u}} {i : Fin H.eventCount} {p : CutoffParameters}
    (R : GeometricCutoffRecord H i p) : OneStepIncoming.{u} where
  stage := H.stage i.castSucc
  startTime := H.time i.castSucc
  endTime := H.time i.succ
  startTime_nonneg := by
    simpa [H.time_zero] using H.time_strictMono.le_iff_le.mpr (Fin.zero_le i.castSucc)
  startTime_lt_endTime := H.time_strictMono i.castSucc_lt_succ
  slab := (H.event i).incoming
  terminal := (H.event i).terminal
  singular := R.singular
  parameters := p

end OneStepIncoming

abbrev HalfNeckCylinder := {p : NeckCylinder // 0 ≤ p.2}

structure TerminalCorePresentation (D : OneStepIncoming.{u}) (ε Λ : ℝ) where
  epsilon_pos : 0 < ε
  Lambda_ge_one : 1 ≤ Λ
  coreRadius : ℝ
  coreRadius_pos : 0 < coreRadius
  coreRadius_eq : coreRadius =
    D.parameters.delta D.endTime * D.parameters.neckRadius D.endTime
  component : Set (ConnectedComponents ↥D.slab.terminalRegularOpen)
  component_finite : component.Finite
  core : ConnectedComponents ↥D.slab.terminalRegularOpen →
    Set ↥D.slab.terminalRegularOpen
  core_isOpen : ∀ c, IsOpen (core c)
  core_isCompact : ∀ c, IsCompact (core c)
  core_isConnected : ∀ c, IsConnected (core c)
  component_iff_meets_low : ∀ c : ConnectedComponents ↥D.slab.terminalRegularOpen,
    c ∈ component ↔ ∃ x : ↥D.slab.terminalRegularOpen, ConnectedComponents.mk x = c ∧
      metricScalarAt D.terminal.metric x ≤ (coreRadius ^ 2)⁻¹
  low_mem_interior_core : ∀ c ∈ component, ∀ x : ↥D.slab.terminalRegularOpen,
    ConnectedComponents.mk x = c →
    metricScalarAt D.terminal.metric x ≤ (coreRadius ^ 2)⁻¹ →
      x ∈ interior (core c)
  hornIndex : ConnectedComponents ↥D.slab.terminalRegularOpen → Type u
  hornIndex_finite : ∀ c, Finite (hornIndex c)
  hornIndex_empty : ∀ c, c ∉ component → IsEmpty (hornIndex c)
  horn : ∀ c, hornIndex c → NeckCylinder → ↥D.slab.terminalRegularOpen
  horn_smooth : ∀ c e, ContMDiffOn NeckCylinderModel ThreeModel ∞ (horn c e)
    (Set.univ ×ˢ Set.Ici (0 : ℝ))
  horn_injOn : ∀ c e, Set.InjOn (horn c e) (Set.univ ×ˢ Set.Ici (0 : ℝ))
  horn_proper : ∀ c e, IsProperMap fun p : HalfNeckCylinder => horn c e p.1
  horn_range_disjoint : ∀ c e e', e ≠ e' →
    Disjoint (Set.range fun p : HalfNeckCylinder => horn c e p.1)
      (Set.range fun p : HalfNeckCylinder => horn c e' p.1)
  horn_meets_core : ∀ c e,
    Set.range (fun y : Sphere 2 => horn c e (y, 0)) ∩ core c =
      Set.range fun y : Sphere 2 => horn c e (y, 0)
  horn_covers_component : ∀ c ∈ component,
    {x : ↥D.slab.terminalRegularOpen | ConnectedComponents.mk x = c} =
      core c ∪ ⋃ e : hornIndex c, Set.range fun p : HalfNeckCylinder => horn c e p.1
  horn_scalar_large : ∀ c e y u, 0 < u →
    (coreRadius ^ 2)⁻¹ < metricScalarAt D.terminal.metric (horn c e (y, u))
  horn_base_scalar : ∀ c e y,
    metricScalarAt D.terminal.metric (horn c e (y, 0)) ≤ Λ * (coreRadius ^ 2)⁻¹
  horn_scalar_diverges : ∀ (c : ConnectedComponents ↥D.slab.terminalRegularOpen)
    (e : hornIndex c) (L : ℝ), ∃ u_L : ℝ, ∀ y u, u_L ≤ u →
    L < metricScalarAt D.terminal.metric (horn c e (y, u))
  horn_spatial_neck : ∀ (c : ConnectedComponents ↥D.slab.terminalRegularOpen)
    (e : hornIndex c) (x : ↥D.slab.terminalRegularOpen),
    x ∈ interior (Set.range fun p : HalfNeckCylinder => horn c e p.1) →
    ∃ (δ : ℝ) (k : ℕ) (neck : NormalizedNeck D.terminal.metric δ k),
      neck.center = x ∧ δ ≤ ε ∧ ⌊ε⁻¹⌋₊ + 1 ≤ k

structure TerminalCorePresentationInput (τ ε : ℝ) where
  tau_pos : 0 < τ
  epsilon_pos : 0 < ε
  epsilon_lt_one : ε < 1
  lambda : ℝ
  one_le_lambda : 1 ≤ lambda
  presentation : ∀ D : OneStepIncoming.{u}, τ ≤ D.endTime →
    Nonempty (TerminalCorePresentation D ε lambda)

structure AdaptedHistoricalNeck (D : OneStepIncoming.{u})
    (horn : NeckCylinder → ↥D.slab.terminalRegularOpen) (d h : ℝ) (k : ℕ) where
  d_pos : 0 < d
  d_lt_quarter : d < 1 / 4
  h_pos : 0 < h
  order_lower : 2 * ⌊d⁻¹⌋₊ + 4 ≤ k
  depth_ge : D.startTime ≤ D.endTime - 2 * h ^ 2
  chart : NeckCylinder → ↥D.slab.terminalRegularOpen
  chart_agrees_horn : ∃ W : Set NeckCylinder,
    IsOpen W ∧ Set.range (fun y : Sphere 2 => (y, (0 : ℝ))) ⊆ W ∧ Set.EqOn chart horn W
  shift : ℝ
  shift_lower : d⁻¹ + 1 < shift
  neck : NormalizedNeck D.terminal.metric d k
  chart_eq_neck : ∀ p : neckBuffer d, chart (p.1.1, shift - p.1.2) = neck.chart p
  scale_eq : neck.scale = (h ^ 2)⁻¹
  pastMetric : ℝ → SmoothRiemannianMetric NeckCylinderModel (neckBuffer d)
  pastMetric_inner : ∀ t ∈ Set.Icc (D.endTime - 2 * h ^ 2) D.endTime,
    ∀ (x : neckBuffer d) (V W : TangentSpace NeckCylinderModel x),
      (pastMetric t).inner x V W = neck.scale *
        (D.slab.flow.base.metric t).inner (neck.chart x).1
          (mfderiv NeckCylinderModel ThreeModel
            (fun y : neckBuffer d => (neck.chart y).1) x V)
          (mfderiv NeckCylinderModel ThreeModel
            (fun y : neckBuffer d => (neck.chart y).1) x W)
  past_closeness : ∀ t ∈ Set.Icc (D.endTime - 2 * h ^ 2) D.endTime, ∀ m : ℕ, m ≤ k →
    metricDerivNormSupOn (neckClosedTest d) m (pastMetric t)
      (roundCylinderMetric.restrictOpen (neckBuffer d))
      (roundCylinderMetric.restrictOpen (neckBuffer d)) < d

def historicalNeckRecognition (τ ε d : ℝ) (k : ℕ) (Λ : ℝ) : Prop :=
  0 < d ∧ d < 1 / 4 ∧ 2 * ⌊d⁻¹⌋₊ + 4 ≤ k ∧
    ∃ H : ℝ, 0 < H ∧
      ∀ (D : OneStepIncoming.{u}) (P : TerminalCorePresentation D ε Λ)
        (c : ConnectedComponents ↥D.slab.terminalRegularOpen) (e : P.hornIndex c)
        (h : ℝ),
        0 < h → h ≤ H → 2 * h ^ 2 < τ → Λ * (P.coreRadius ^ 2)⁻¹ < (h ^ 2)⁻¹ →
          Nonempty (AdaptedHistoricalNeck D (P.horn c e) d h k)

def cylinderSlab (N : ℝ) : TopologicalSpace.Opens NeckCylinder :=
  ⟨{x : NeckCylinder | x.2 ∈ Set.Ioo (-N) N},
    isOpen_Ioo.preimage continuous_snd⟩

def backwardCylinderMetric (N : ℝ) (v : Set.Icc (-1 : ℝ) 0) :
    SmoothRiemannianMetric NeckCylinderModel (↥(cylinderSlab N)) :=
  (shrinkingCylinderMetric ⟨(v : ℝ), Set.mem_Iio.mpr (by
      have hv : (v : ℝ) ≤ 0 := v.2.2
      linarith)⟩).restrictOpen
    (cylinderSlab N)

def normalizedFlowMetricAt (D : OneStepIncoming.{u}) (Q v : ℝ) :
    SmoothRiemannianMetric ThreeModel ↥D.slab.terminalRegularOpen :=
  if v = 0 then D.terminal.metric
  else (D.slab.flow.base.metric (D.endTime + v / Q)).restrictOpen
    D.slab.terminalRegularOpen

def hornCylinderLimit (ε Λ : ℝ) : Prop :=
  ∀ (D : OneStepIncoming.{u}) (P : TerminalCorePresentation D ε Λ)
    (c : ConnectedComponents ↥D.slab.terminalRegularOpen) (e : P.hornIndex c)
    (x : ℕ → ↥D.slab.terminalRegularOpen),
    (∀ n, x n ∈ Set.range fun p : HalfNeckCylinder => P.horn c e p.1) →
    Tendsto (fun n => metricScalarAt D.terminal.metric (x n)) atTop atTop →
    ∃ block : ℕ → ℕ, StrictMono block ∧
      ∀ (N : ℝ) (_hN : 0 < N) (order : ℕ) (η : ℝ), 0 < η →
        ∀ᶠ n in atTop,
          ∃ (chart : C(↥(cylinderSlab N), ↥D.slab.terminalRegularOpen))
            (scaled : Set.Icc (-1 : ℝ) 0 →
              SmoothRiemannianMetric NeckCylinderModel (↥(cylinderSlab N))),
            (∀ (v : Set.Icc (-1 : ℝ) 0) (z : ↥(cylinderSlab N))
                (V W : TangentSpace NeckCylinderModel z),
              (scaled v).inner z V W = metricScalarAt D.terminal.metric (x (block n)) *
                (normalizedFlowMetricAt D (metricScalarAt D.terminal.metric (x (block n)))
                  (z.1.2)).inner (chart z)
                  (mfderiv NeckCylinderModel ThreeModel chart z V)
                  (mfderiv NeckCylinderModel ThreeModel chart z W)) ∧
            (∀ v : Set.Icc (-1 : ℝ) 0,
              metricDerivNormSupOn (Set.univ : Set ↥(cylinderSlab N)) order (scaled v)
                (backwardCylinderMetric N v) (backwardCylinderMetric N v) < η)

def IsConstantPositiveSectionalCurvature {M : Type u} [TopologicalSpace M]
    [ChartedSpace ThreeSpace M] [IsManifold ThreeModel ∞ M]
    (g : SmoothRiemannianMetric ThreeModel M) : Prop :=
  ∃ κ : ℝ, 0 < κ ∧ ∀ x (v w : TangentSpace ThreeModel x),
    LinearIndependent ℝ ![v, w] →
      DifferentialGeometry.Geometry.Riemannian.sectionalCurvature g x v w = κ

def IsPositiveSpaceFormModel (M : ConnectedClosedOrientedManifold.{u} 3) : Prop :=
  ∃ g : SmoothRiemannianMetric ThreeModel M.Carrier,
    IsConstantPositiveSectionalCurvature g

def sphericalSpaceFormCovering : Prop :=
  ∀ (M : ConnectedClosedOrientedManifold.{u} 3) (g : SmoothRiemannianMetric ThreeModel M.Carrier),
    IsConstantPositiveSectionalCurvature g →
    ∃ G : DifferentialGeometry.Topology.SphericalSpaceFormGroup,
      Nonempty (ClosedOrientedManifold.OrientedDiffeomorph M.toClosedOrientedManifold
        G.manifold.toClosedOrientedManifold)

structure RelativeDiscardPresentation (C : Type u) [TopologicalSpace C]
    [ChartedSpace ThreeSpace C] [IsManifold ThreeModel ∞ C] [T2Space C] [CompactSpace C] where
  vertexCount : ℕ
  vertex : Fin vertexCount → ConnectedClosedOrientedManifold.{u} 3
  vertex_elementary : ∀ i,
    DifferentialGeometry.Topology.isStandardFactor (vertex i) ∨ IsPositiveSpaceFormModel (vertex i)
  edgeCount : ℕ
  edgeSource : Fin edgeCount → Fin vertexCount
  edgeTarget : Fin edgeCount → Fin vertexCount
  graph_connected : ∀ i i' : Fin vertexCount,
    Relation.ReflTransGen (fun a b : Fin vertexCount =>
      ∃ e : Fin edgeCount,
        (edgeSource e = a ∧ edgeTarget e = b) ∨ (edgeSource e = b ∧ edgeTarget e = a)) i i'
  externalCount : ℕ
  externalSphere : Fin externalCount → C(Sphere 2, C)
  externalSphere_smooth : ∀ b, IsSmoothEmbedding (𝓡 2) ThreeModel ∞ (externalSphere b)
  externalSphere_pairwise : Pairwise fun b b' =>
    Disjoint (Set.range (externalSphere b)) (Set.range (externalSphere b'))
  edgeCollar : Fin edgeCount → C(Sphere 2 × Set.Icc (-2 : ℝ) 2, C)
  edgeCollar_smooth : ∀ e,
    letI : Fact ((-2 : ℝ) < 2) := ⟨by norm_num⟩
    IsSmoothEmbedding ((𝓡 2).prod (𝓡∂ 1)) ThreeModel ∞ (edgeCollar e)
  edgeCollar_pairwise : Pairwise fun e e' =>
    Disjoint (Set.range (edgeCollar e)) (Set.range (edgeCollar e'))
  edgeCollar_disjoint_sphere : ∀ e b,
    Disjoint (Set.range (edgeCollar e)) (Set.range (externalSphere b))
  region : Fin vertexCount → Set C
  region_compact : ∀ i, IsCompact (region i)
  region_connected : ∀ i, IsConnected (region i)
  region_frontier : ∀ i, frontier (region i) ⊆
    (⋃ b, Set.range (externalSphere b)) ∪ (⋃ e, Set.range (edgeCollar e))
  cover : ∀ x : C, (∃ i, x ∈ region i) ∨ (∃ e, x ∈ Set.range (edgeCollar e)) ∨
    (∃ b, x ∈ Set.range (externalSphere b))

def HasElementaryDiscardDecomposition (C : Type u) [TopologicalSpace C]
    [ChartedSpace ThreeSpace C] [IsManifold ThreeModel ∞ C] [T2Space C] [CompactSpace C] : Prop :=
  Nonempty (RelativeDiscardPresentation C)

structure ProtectedIncomingWitness (D : OneStepIncoming.{u})
    (X : Set ↥D.slab.terminalRegularOpen) (x : ↥D.slab.terminalRegularOpen) where
  region : Set ↥D.slab.terminalRegularOpen
  region_open : IsOpen region
  x_mem : x ∈ region
  radius : ℝ
  radius_pos : 0 < radius
  buffer : Set ↥D.slab.terminalRegularOpen
  buffer_open : IsOpen buffer
  region_subset_buffer : region ⊆ buffer
  buffer_subset_core : buffer ⊆ interior X
  bufferRadius : ℝ
  bufferRadius_gt : 2 * radius < bufferRadius
  ball_compact : IsCompact (riemannianBallOf D.terminal.metric x bufferRadius)
  ball_subset_buffer : riemannianBallOf D.terminal.metric x bufferRadius ⊆ buffer
  scale_pos : 0 < metricScalarAt D.terminal.metric x
  scalar_comparable : ∀ y ∈ region,
    metricScalarAt D.terminal.metric x / 2 ≤ metricScalarAt D.terminal.metric y ∧
      metricScalarAt D.terminal.metric y ≤ 2 * metricScalarAt D.terminal.metric x
  neckCount : ℕ
  neckPrecision : Fin neckCount → ℝ
  neckOrder : Fin neckCount → ℕ
  neckChart : (i : Fin neckCount) → C(neckBuffer (neckPrecision i),
    ↥D.slab.terminalRegularOpen)
  neckChart_smooth : ∀ i, IsSmoothEmbedding NeckCylinderModel ThreeModel ∞ (neckChart i)
  neck_range_subset : ∀ i, Set.range (neckChart i) ⊆ buffer
  neck_backward : ∀ i, ∃ (θ : NeckCylinder → ↥D.slab.terminalRegularOpen) (h : ℝ),
    0 < h ∧ Set.range θ ⊆ buffer ∧
      Nonempty (AdaptedHistoricalNeck D θ (neckPrecision i) h (neckOrder i))

def precutCanonicalCoverage (D : OneStepIncoming.{u})
    (X : Set ↥D.slab.terminalRegularOpen) (rTest : ℝ)
    (ι : Type u) (collar : ι → Set ↥D.slab.terminalRegularOpen) : Prop :=
  ∀ x ∈ X, (rTest ^ 2)⁻¹ ≤ metricScalarAt D.terminal.metric x →
    (∃ i, x ∈ collar i) ∨ Nonempty (ProtectedIncomingWitness D X x)

def protectionInput (τ ε Λ : ℝ) : Prop :=
  ∀ (D : OneStepIncoming.{u}) (P : TerminalCorePresentation D ε Λ)
    (X : Set ↥D.slab.terminalRegularOpen) (rTest : ℝ)
    (collar : (c : ConnectedComponents ↥D.slab.terminalRegularOpen) →
      P.hornIndex c → Set ↥D.slab.terminalRegularOpen),
    τ ≤ D.endTime → 0 < rTest → IsCompact X →
    (∀ c, c ∈ P.component → P.core c ⊆ X) →
    (∀ x ∈ X, (∀ c, c ∈ P.component → x ∉ P.core c) →
      ∃ (c : ConnectedComponents ↥D.slab.terminalRegularOpen) (e : P.hornIndex c),
        x ∈ collar c e) →
    (∀ c e, collar c e ⊆ P.core c) →
    precutCanonicalCoverage D X rTest
      ((c : ConnectedComponents ↥D.slab.terminalRegularOpen) × P.hornIndex c)
      (fun ie => collar ie.1 ie.2)

structure OneStepPrecision (p : CutoffParameters) (B dCap glob : ℝ) where
  precision : ℝ
  order : ℕ
  precision_pos : 0 < precision
  precision_shorter : precision < min (1 / 4) (min (p.delta B) (min dCap glob))
  order_lower : max (p.modelOrder + 6) (2 * ⌊precision⁻¹⌋₊ + 4) ≤ order

structure GlobalStepInputs (p : CutoffParameters) (τ ε d : ℝ) (k : ℕ)
    (DiscardedCutOpen : Type u → Prop) where
  endInput : TerminalCorePresentationInput.{u} τ ε
  neckInput : historicalNeckRecognition.{u} τ ε d k endInput.lambda
  pieceInput : ∀ (C : Type u) [TopologicalSpace C] [ChartedSpace ThreeSpace C]
    [IsManifold ThreeModel ∞ C] [T2Space C] [CompactSpace C],
    DiscardedCutOpen C → HasElementaryDiscardDecomposition C
  roundInput : sphericalSpaceFormCovering.{u}
  cylinderInput : hornCylinderLimit.{u} ε endInput.lambda
  protectInput : protectionInput.{u} τ ε endInput.lambda

def GlobalStepConclusion (p : CutoffParameters) (τ ε d : ℝ) (k : ℕ) (a₀ : ℝ)
    (DiscardedCutOpen : Type u → Prop)
    (inputs : GlobalStepInputs.{u} p τ ε d k DiscardedCutOpen) : Prop :=
  ∃ hstar : ℝ, 0 < hstar ∧ 2 * hstar ^ 2 < τ ∧
    ∀ (H : ObservedHistory.{u}) (i : Fin H.eventCount),
      τ ≤ H.time i.succ →
      Nonempty (GeometricCutoffRecord H i p) →
      ∃ (K : ObservedHistory.{u}) (j : Fin K.eventCount) (R : GeometricCutoffRecord K j p),
        j.val = H.eventCount ∧ ObservedHistory.IsPrefixOf H K ∧
        K.eventCount = H.eventCount + 1 ∧
        τ ≤ K.time (Fin.succ j) ∧
        Nonempty (TerminalCorePresentation (OneStepIncoming.ofRecord R) ε
          inputs.endInput.lambda) ∧
        (∀ α : (K.event j).transition.trace.tubes.Index,
          R.nominalRadius ⟨α⟩ = hstar) ∧
        DiscardedCutOpen (K.event j).discarded.Carrier ∧
        (∀ C : ConnectedComponents (K.event j).discarded.Carrier,
          componentIsPoincareStandard (K.event j).discarded.toClosedOrientedManifold C) ∧
        (∀ x : (K.stage (Fin.succ j)).Carrier,
          -3 / (a₀ + 2 * K.time (Fin.succ j)) ≤ metricScalarAt (K.event j).outputMetric x)

def globalMetricStep (p : CutoffParameters) (τ ε d : ℝ) (k : ℕ) (a₀ : ℝ)
    (DiscardedCutOpen : Type u → Prop)
    (inputs : GlobalStepInputs.{u} p τ ε d k DiscardedCutOpen) : Prop :=
  GlobalStepConclusion.{u} p τ ε d k a₀ DiscardedCutOpen inputs

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
