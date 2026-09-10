import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.StaticCap
import DifferentialGeometry.Geometry.Curvature.DimensionThree.CurvatureOperator.Metric
import Mathlib.Analysis.Calculus.IteratedDeriv.Defs

noncomputable section

open Bundle Manifold Set Filter
open DifferentialGeometry.Geometry.Curvature DifferentialGeometry.CheegerGromovCompactness
open DifferentialGeometry.Geometry.Curvature.DimensionThree
open DifferentialGeometry.Tensor0SBundle
open scoped Manifold ContDiff Topology BigOperators RealInnerProductSpace

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

universe u

def cylinderTensorCovDeriv {δ : ℝ}
    (g : SmoothRiemannianMetric NeckCylinderModel (neckBuffer δ))
    (A : Tensor0SField (I := NeckCylinderModel) (M := neckBuffer δ) ∞ 2) :
    (a : ℕ) → Tensor0SField (I := NeckCylinderModel) (M := neckBuffer δ) ∞ (a + 2)
  | 0 => A
  | a + 1 => by
    simpa only [Nat.add_assoc] using metricCovDerivStep g a (cylinderTensorCovDeriv g A a)

def InFixedHamiltonIveyRegion {X : Type*} [TopologicalSpace X]
    [ChartedSpace ThreeSpace X] [IsManifold ThreeModel ∞ X]
    [T2Space X] [SigmaCompactSpace X]
    (g : SmoothRiemannianMetric ThreeModel X) (a : ℝ) (x : X) : Prop :=
  ∀ B : Module.Basis (Fin 3) ℝ (TangentSpace ThreeModel x),
    (∀ i j, g.inner x (B i) (B j) = if i = j then 1 else 0) →
    let C := tensor04CurvatureOperatorMatrixAt B (metricRm04At g x)
    let ν := sInf {r : ℝ | ∃ v : Fin 3 → ℝ, (∑ i, (v i)^2) = 1 ∧
      r = 2 * ∑ i, ∑ j, v i * C i j * v j}
    0 ≤ ν ∨ metricScalarAt g x ≥ (-ν) * (Real.log (a * (-ν)) - 3)

variable (H : ObservedHistory.{u}) (i : Fin H.eventCount)

local instance terminalSecondCountable : SecondCountableTopology
    (H.event i).incoming.terminalRegularOpen := by
  let : SecondCountableTopology (H.stage i.castSucc).Carrier :=
    ChartedSpace.secondCountable_of_sigmaCompact ThreeSpace (H.stage i.castSucc).Carrier
  infer_instance

local instance terminalLocallyCompact : LocallyCompactSpace
    (H.event i).incoming.terminalRegularOpen :=
  ChartedSpace.locallyCompactSpace ThreeSpace (H.event i).incoming.terminalRegularOpen

structure IncomingBackwardNeck {δ : ℝ} {k : ℕ}
    (neck : NormalizedNeck (H.event i).terminal.metric δ k) (r : ℝ) where
  radius_pos : 0 < r
  left_nonneg : 0 ≤ H.time i.succ - r^2
  stageChart : (j : Fin H.eventCount) → j.val ≤ i.val →
    H.time i.succ - r^2 < H.time j.succ →
    C(neckBuffer δ, (H.stage j.castSucc).Carrier)
  stageChart_smooth : ∀ j hj ha,
    IsSmoothEmbedding NeckCylinderModel ThreeModel ∞ (stageChart j hj ha)
  terminal_chart : ∀ ha : H.time i.succ - r^2 < H.time i.succ,
    ∀ x, stageChart i le_rfl ha x = (neck.chart x).1
  crossing : ∀ (j : Fin H.eventCount) (hj : j.val < i.val),
    let next : Fin H.eventCount := ⟨j.val + 1, by omega⟩
    ∀ ha : H.time i.succ - r^2 < H.time j.succ,
    ∀ hn : H.time i.succ - r^2 < H.time next.succ,
    ∀ x : neckBuffer δ,
      (H.event j).RegularCrossing (stageChart j hj.le ha x)
        (stageChart next (by change j.val + 1 ≤ i.val; omega) hn x)
  metric : ℝ → SmoothRiemannianMetric NeckCylinderModel (neckBuffer δ)
  terminal_metric : metric 0 = neck.normalizedMetric
  metric_on_slab : ∀ (j : Fin H.eventCount) hj ha, ∀ v ∈ Ico (-1 : ℝ) 0,
    H.time j.castSucc ≤ H.time i.succ + r^2*v →
    H.time i.succ + r^2*v < H.time j.succ → ∀ x V W,
      (metric v).inner x V W = (r ^ 2)⁻¹ *
        ((H.event j).incoming.flow.base.metric (H.time i.succ + r^2*v)).inner
          (stageChart j hj ha x)
          (mfderiv NeckCylinderModel ThreeModel (stageChart j hj ha) x V)
          (mfderiv NeckCylinderModel ThreeModel (stageChart j hj ha) x W)
  timeDifferenceJet : (b : ℕ) → (v : Icc (-1 : ℝ) 0) →
    Tensor0SField (I := NeckCylinderModel) (M := neckBuffer δ) ∞ 2
  timeDifferenceJet_eq : ∀ b v x,
    timeDifferenceJet b v x =
      iteratedDerivWithin b (fun t =>
        (metricTensorField (metric t) x) -
          (metricTensorField ((shrinkingCylinderMetric
            ⟨min t 0, lt_of_le_of_lt (min_le_right (t : ℝ) 0)
              (show (0 : ℝ) < 1 by norm_num)⟩).restrictOpen
              (neckBuffer δ)) x)) (Icc (-1 : ℝ) 0) v.1
  parabolic_closeness : ∃ η : ℝ, η < δ ∧ ∀ a b : ℕ, a + 2*b ≤ k →
    ∀ v : Icc (-1 : ℝ) 0, ∀ x ∈ neckClosedTest δ,
      let g := (shrinkingCylinderMetric
        ⟨v.1, lt_of_le_of_lt v.2.2 (show (0 : ℝ) < 1 by norm_num)⟩).restrictOpen
        (neckBuffer δ)
      Real.sqrt (normSq0S g x (a + 2)
        (cylinderTensorCovDeriv g (timeDifferenceJet b v) a x)) ≤ η

theorem IncomingBackwardNeck.metric_smooth_up_to {δ : ℝ} {k : ℕ}
    {neck : NormalizedNeck (H.event i).terminal.metric δ k} {r : ℝ}
    (N : IncomingBackwardNeck H i neck r) (hscale : neck.scale = (r ^ 2)⁻¹) :
    ∀ p : neckBuffer δ, ∀ t ∈ Icc (-1 : ℝ) 0,
      ∃ U : Set (neckBuffer δ), IsOpen U ∧ p ∈ U ∧
        U ⊆ (trivializationAt (EuclideanSpace ℝ (Fin 2) × ℝ)
          (TangentSpace NeckCylinderModel) p).baseSet ∧
      ∃ V : Set ℝ, IsOpen V ∧ t ∈ V ∧
      ∃ A : ℝ × neckBuffer δ → (EuclideanSpace ℝ (Fin 2) × ℝ) →
          (EuclideanSpace ℝ (Fin 2) × ℝ) → ℝ,
        (∀ v w, ContMDiffOn (𝓘(ℝ, ℝ).prod NeckCylinderModel) 𝓘(ℝ, ℝ) ∞
          (fun z => A z v w) (V ×ˢ U)) ∧
        ∀ s ∈ V ∩ Icc (-1 : ℝ) 0, ∀ x ∈ U, ∀ v w,
          A (s, x) v w = (N.metric s).inner x
            ((trivializationAt (EuclideanSpace ℝ (Fin 2) × ℝ)
              (TangentSpace NeckCylinderModel) p).symmL ℝ x v)
            ((trivializationAt (EuclideanSpace ℝ (Fin 2) × ℝ)
              (TangentSpace NeckCylinderModel) p).symmL ℝ x w) := by
  sorry

namespace MetricCutCapEvent

variable {P Q : OrientedThreeStage.{u}} {a s : ℝ} (E : MetricCutCapEvent P Q a s)


def RetainedBoundary (b : E.transition.trace.tubes.Boundary) : Prop :=
  ∀ y, E.transition.trace.tubes.coreBoundarySphere b y ∈ E.transition.trace.retainedCore

abbrev RetainedBoundaryIndex := {b : E.transition.trace.tubes.Boundary // E.RetainedBoundary b}

end MetricCutCapEvent

structure PresentedStaticCap (fixed : StaticCapScaffold) (D : ℝ) (m : ℕ) (η : ℝ)
    (b : (H.event i).RetainedBoundaryIndex) where
  delta : ℝ
  order : ℕ
  neck : NormalizedNeck (H.event i).terminal.metric delta order
  witness : StaticCapWitness neck fixed D m η
  inclusion : C(witness.Output, (H.stage i.succ).Carrier)
  inclusion_smooth : IsSmoothEmbedding ThreeModel ThreeModel ∞ inclusion
  inclusion_metric : ∀ x V W, witness.metric.inner x V W =
    (H.event i).outputMetric.inner (inclusion x)
      (mfderiv ThreeModel ThreeModel inclusion x V)
      (mfderiv ThreeModel ThreeModel inclusion x W)
  cap_eq : ∀ x : ThreeBall,
    (H.event i).transition.trace.presentation
      ((H.event i).transition.trace.capping.cap b.1 x) = Sum.inl (inclusion (witness.cap x))
  attaching_eq : (witness.attaching : Sphere 2 → Sphere 2) =
    (H.event i).transition.trace.capping.attaching b.1
  retained_point : (x : neckRetainedCollar delta) →
    {p : (H.event i).transition.trace.tubes.core //
      p ∈ (H.event i).transition.trace.retainedCore}
  retained_point_eq : ∀ x : neckRetainedCollar delta,
    ∀ hx : x.1 ∈ neckBuffer delta,
      (retained_point x).1.1 = (neck.chart ⟨x.1, hx⟩).1
  retained_eq : ∀ x,
    (H.event i).transition.trace.presentation
      ((H.event i).transition.trace.capping.coreInclusion (retained_point x).1) =
        Sum.inl (inclusion (witness.retained x))

structure CutoffParameters where
  delta : ℝ → ℝ
  neckRadius : ℝ → ℝ
  protectedRadius : ℝ → ℝ
  delta_pos : ∀ t, 0 ≤ t → 0 < delta t
  delta_lt_one : ∀ t, 0 ≤ t → delta t < 1
  neckRadius_pos : ∀ t, 0 ≤ t → 0 < neckRadius t
  protectedRadius_pos : ∀ t, 0 ≤ t → 0 < protectedRadius t
  fixed : StaticCapScaffold
  modelRadius : ℝ
  modelRadius_pos : 0 < modelRadius
  modelOrder : ℕ
  modelAccuracy : ℝ
  modelAccuracy_pos : 0 < modelAccuracy
  recenterConstant : ℝ
  recenterConstant_ge_four : 4 ≤ recenterConstant

structure GeometricCutoffRecord (parameters : CutoffParameters) where
  singular : (H.event i).incoming.SingularEndpoint
  nominalRadius : Nonempty (H.event i).transition.trace.tubes.Index → ℝ
  nominal_pos : ∀ h, 0 < nominalRadius h
  nominal_small : ∀ h, nominalRadius h <
    (parameters.delta (H.time i.succ))^2 * parameters.neckRadius (H.time i.succ)
  nominal_time : ∀ h, (nominalRadius h)^2 ≤ H.time i.succ
  delta : (H.event i).transition.trace.tubes.Index → ℝ
  delta_pos : ∀ α, 0 < delta α
  delta_le : ∀ α, delta α ≤ parameters.delta (H.time i.succ)
  order : (H.event i).transition.trace.tubes.Index → ℕ
  order_lower : ∀ α, max (parameters.modelOrder + 6) (2 * ⌊(delta α)⁻¹⌋₊ + 4) ≤ order α
  neck : ∀ α, NormalizedNeck (H.event i).terminal.metric (delta α) (order α)
  scale_eq : ∀ α, (neck α).scale = ((nominalRadius ⟨α⟩) ^ 2)⁻¹
  buffer_disjoint : Pairwise fun α β => Disjoint (Set.range (neck α).chart) (Set.range (neck β).chart)
  tube_eq : ∀ α, ∀ x : TubeDomain, ∀ hx : (x.1, x.2.1) ∈ neckBuffer (delta α),
    (H.event i).transition.trace.tubes.tube α x = ((neck α).chart ⟨(x.1, x.2.1), hx⟩).1
  tube_in_buffer : ∀ α, ∀ x : TubeDomain, (x.1, x.2.1) ∈ neckBuffer (delta α)
  backward : ∀ α, IncomingBackwardNeck H i (neck α) (nominalRadius ⟨α⟩)
  retained_terminal : ∀ x ∈ (H.event i).transition.trace.retainedCore,
    x.1 ∈ (H.event i).incoming.terminalRegularRegion
  protected_interior : ∀ x : (H.event i).incoming.terminalRegularOpen,
    metricScalarAt (H.event i).terminal.metric x ≤ ((parameters.protectedRadius (H.time i.succ)) ^ 2)⁻¹ →
    x.1 ∈ interior (Subtype.val '' (H.event i).transition.trace.retainedCore)
  retained_meets_protected : ∀ c : ConnectedComponents (H.event i).transition.trace.tubes.core,
    (∃ x : (H.event i).transition.trace.tubes.core,
      ConnectedComponents.mk x = c ∧ x ∈ (H.event i).transition.trace.retainedCore) →
    ∃ x : (H.event i).incoming.terminalRegularOpen,
      ∃ hx : x.1 ∈ (H.event i).transition.trace.tubes.core,
        ConnectedComponents.mk ⟨x.1, hx⟩ = c ∧
          metricScalarAt (H.event i).terminal.metric x ≤
            ((parameters.protectedRadius (H.time i.succ)) ^ 2)⁻¹
  one_retained_side : ∀ α,
    (H.event i).RetainedBoundary (α, true) ↔ ¬ (H.event i).RetainedBoundary (α, false)
  no_cuts_discard : IsEmpty (H.event i).transition.trace.tubes.Index →
    ∃ x : (H.event i).transition.trace.tubes.core, x ∉ (H.event i).transition.trace.retainedCore
  static : ∀ b : (H.event i).RetainedBoundaryIndex,
    PresentedStaticCap H i parameters.fixed parameters.modelRadius parameters.modelOrder
      parameters.modelAccuracy b
  recenter_scale : ∀ b : (H.event i).RetainedBoundaryIndex,
    (static b).neck.scale = metricScalarAt (H.event i).terminal.metric ((static b).neck.center)
  recenter_mark : ∀ b : (H.event i).RetainedBoundaryIndex,
    (static b).neck.sphereMark = (neck b.1.1).sphereMark
  recenter_delta : ∀ b : (H.event i).RetainedBoundaryIndex,
    (static b).delta = parameters.recenterConstant * delta b.1.1
  recenter_scale_comparison : ∀ b : (H.event i).RetainedBoundaryIndex,
    |(static b).neck.scale / (neck b.1.1).scale - 1| ≤
      parameters.recenterConstant * delta b.1.1
  recenter_chart : ∀ b : (H.event i).RetainedBoundaryIndex,
    ∀ x : neckBuffer (static b).delta,
    ∀ hx : (x.1.1, (if b.1.2 then 1 else -1) * (1 + x.1.2)) ∈ neckBuffer (delta b.1.1),
      (static b).neck.chart x = (neck b.1.1).chart
        ⟨(x.1.1, (if b.1.2 then 1 else -1) * (1 + x.1.2)), hx⟩
  recenter_in_buffer : ∀ b : (H.event i).RetainedBoundaryIndex,
    ∀ x : neckBuffer (static b).delta,
      (x.1.1, (if b.1.2 then 1 else -1) * (1 + x.1.2)) ∈ neckBuffer (delta b.1.1)
  old_eq_retained : (H.event i).old = (H.event i).transition.trace.retainedCore
  curvature_preserving : ∀ a : ℝ, 0 < a →
    (∀ x : (H.event i).incoming.terminalRegularOpen,
      InFixedHamiltonIveyRegion (H.event i).terminal.metric a x) →
    ∀ x : (H.stage i.succ).Carrier, InFixedHamiltonIveyRegion (H.event i).outputMetric a x
  scalar_preserving : ∀ L : ℝ, L ≤ 0 →
    (∀ x : (H.event i).incoming.terminalRegularOpen,
      L ≤ metricScalarAt (H.event i).terminal.metric x) →
    ∀ x : (H.stage i.succ).Carrier, L ≤ metricScalarAt (H.event i).outputMetric x

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
