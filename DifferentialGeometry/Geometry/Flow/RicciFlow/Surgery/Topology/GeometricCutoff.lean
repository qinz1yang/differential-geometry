import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.StaticCap
import DifferentialGeometry.Geometry.Curvature.DimensionThree.CurvatureOperator.Metric
import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
import DifferentialGeometry.Geometry.Metric.Convergence.CovariantDerivative.Bounds

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

theorem cylinderTensorCovDeriv_eq_tensor02CovDeriv {δ : ℝ}
    (g : SmoothRiemannianMetric NeckCylinderModel (neckBuffer δ))
    (A : Tensor0SField (I := NeckCylinderModel) (M := neckBuffer δ) ∞ 2) (r : ℕ) :
    cylinderTensorCovDeriv g A r = tensor02CovDeriv A g r := by
  induction r with
  | zero => rfl
  | succ r ih =>
      rw [cylinderTensorCovDeriv, ih]
      rfl

def InFixedHamiltonIveyRegion {X : Type*} [TopologicalSpace X]
    [ChartedSpace ThreeSpace X] [IsManifold ThreeModel ∞ X]
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

  metric_smooth : ∀ p : neckBuffer δ, ∀ t ∈ Icc (-1 : ℝ) 0,
    ∃ U : Set (neckBuffer δ), IsOpen U ∧ p ∈ U ∧
      U ⊆ (trivializationAt (EuclideanSpace ℝ (Fin 2) × ℝ)
        (TangentSpace NeckCylinderModel) p).baseSet ∧
    ∃ V : Set ℝ, IsOpen V ∧ t ∈ V ∧
    ∃ A : ℝ × neckBuffer δ → (EuclideanSpace ℝ (Fin 2) × ℝ) →
        (EuclideanSpace ℝ (Fin 2) × ℝ) → ℝ,
      (∀ v w, ContMDiffOn (𝓘(ℝ, ℝ).prod NeckCylinderModel) 𝓘(ℝ, ℝ) ∞
        (fun z => A z v w) (V ×ˢ U)) ∧
      ∀ s ∈ V ∩ Icc (-1 : ℝ) 0, ∀ x ∈ U, ∀ v w,
        A (s, x) v w = (metric s).inner x
          ((trivializationAt (EuclideanSpace ℝ (Fin 2) × ℝ)
            (TangentSpace NeckCylinderModel) p).symmL ℝ x v)
          ((trivializationAt (EuclideanSpace ℝ (Fin 2) × ℝ)
            (TangentSpace NeckCylinderModel) p).symmL ℝ x w)

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
  let _ := hscale
  exact N.metric_smooth

namespace MetricCutCapEvent

variable {P Q : OrientedThreeStage.{u}} {a s : ℝ} (E : MetricCutCapEvent P Q a s)


def RetainedBoundary (b : E.transition.trace.tubes.Boundary) : Prop :=
  ∀ y, E.transition.trace.tubes.coreBoundarySphere b y ∈ E.transition.trace.retainedCore

abbrev RetainedBoundaryIndex := {b : E.transition.trace.tubes.Boundary // E.RetainedBoundary b}

end MetricCutCapEvent

namespace MetricCutCapEvent

variable {P Q : OrientedThreeStage.{u}} {a s : ℝ} (E : MetricCutCapEvent P Q a s)

structure PresentedStaticCap (fixed : StaticCapScaffold) (D : ℝ) (m : ℕ) (η : ℝ)
    (b : E.RetainedBoundaryIndex) where
  delta : ℝ
  order : ℕ
  neck : NormalizedNeck E.terminal.metric delta order
  witness : StaticCapWitness neck fixed D m η
  inclusion : C(witness.Output, Q.Carrier)
  inclusion_smooth : IsSmoothEmbedding ThreeModel ThreeModel ∞ inclusion
  inclusion_metric : ∀ x V W, witness.metric.inner x V W =
    E.outputMetric.inner (inclusion x)
      (mfderiv ThreeModel ThreeModel inclusion x V)
      (mfderiv ThreeModel ThreeModel inclusion x W)
  cap_eq : ∀ x : ThreeBall,
    E.transition.trace.presentation
      (E.transition.trace.capping.cap b.1 x) = Sum.inl (inclusion (witness.cap x))
  attaching_eq : (witness.attaching : Sphere 2 → Sphere 2) =
    E.transition.trace.capping.attaching b.1
  retainedPoint : (x : neckRetainedCollar delta) →
    {p : E.transition.trace.tubes.core //
      p ∈ E.transition.trace.retainedCore}
  retained_point_eq : ∀ x : neckRetainedCollar delta,
    ∀ hx : x.1 ∈ neckBuffer delta,
      (retainedPoint x).1.1 = (neck.chart ⟨x.1, hx⟩).1
  retained_eq : ∀ x,
    E.transition.trace.presentation
      (E.transition.trace.capping.coreInclusion (retainedPoint x).1) =
        Sum.inl (inclusion (witness.retained x))

end MetricCutCapEvent

abbrev PresentedStaticCap (fixed : StaticCapScaffold) (D : ℝ) (m : ℕ) (η : ℝ)
    (b : (H.event i).RetainedBoundaryIndex) :=
  MetricCutCapEvent.PresentedStaticCap (H.event i) fixed D m η b

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

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
universe u

variable {H : ObservedHistory.{u}} {i : Fin H.eventCount}

namespace GeometricCutoffRecord

def congrParameters {p q : CutoffParameters} (R : GeometricCutoffRecord H i p)
    (hdelta : p.delta (H.time i.succ) = q.delta (H.time i.succ))
    (hneck : p.neckRadius (H.time i.succ) = q.neckRadius (H.time i.succ))
    (hprotected : p.protectedRadius (H.time i.succ) = q.protectedRadius (H.time i.succ))
    (hfixed : p.fixed = q.fixed) (hradius : p.modelRadius = q.modelRadius)
    (horder : p.modelOrder = q.modelOrder) (haccuracy : p.modelAccuracy = q.modelAccuracy)
    (hrecenter : p.recenterConstant = q.recenterConstant) : GeometricCutoffRecord H i q := by
  cases p with
  | mk delta neckRadius protectedRadius delta_pos delta_lt_one neckRadius_pos
      protectedRadius_pos fixed modelRadius modelRadius_pos modelOrder modelAccuracy
      modelAccuracy_pos recenterConstant recenterConstant_ge_four =>
    cases q with
    | mk delta' neckRadius' protectedRadius' delta_pos' delta_lt_one' neckRadius_pos'
        protectedRadius_pos' fixed' modelRadius' modelRadius_pos' modelOrder' modelAccuracy'
        modelAccuracy_pos' recenterConstant' recenterConstant_ge_four' =>
      dsimp only at hfixed hradius horder haccuracy hrecenter hdelta hneck hprotected
      cases hfixed
      cases hradius
      cases horder
      cases haccuracy
      cases hrecenter
      exact {
        singular := R.singular
        nominalRadius := R.nominalRadius
        nominal_pos := R.nominal_pos
        nominal_small := fun h => by simpa only [← hdelta, ← hneck] using R.nominal_small h
        nominal_time := R.nominal_time
        delta := R.delta
        delta_pos := R.delta_pos
        delta_le := fun a => by simpa only [← hdelta] using R.delta_le a
        order := R.order
        order_lower := R.order_lower
        neck := R.neck
        scale_eq := R.scale_eq
        buffer_disjoint := R.buffer_disjoint
        tube_eq := R.tube_eq
        tube_in_buffer := R.tube_in_buffer
        backward := R.backward
        retained_terminal := R.retained_terminal
        protected_interior := by simpa only [← hprotected] using R.protected_interior
        retained_meets_protected := by simpa only [← hprotected] using R.retained_meets_protected
        one_retained_side := R.one_retained_side
        no_cuts_discard := R.no_cuts_discard
        static := R.static
        recenter_scale := R.recenter_scale
        recenter_mark := R.recenter_mark
        recenter_delta := R.recenter_delta
        recenter_scale_comparison := R.recenter_scale_comparison
        recenter_chart := R.recenter_chart
        recenter_in_buffer := R.recenter_in_buffer
        old_eq_retained := R.old_eq_retained
        curvature_preserving := R.curvature_preserving
        scalar_preserving := R.scalar_preserving }

@[simp] theorem congrParameters_delta {p q : CutoffParameters} (R : GeometricCutoffRecord H i p)
    (hdelta : p.delta (H.time i.succ) = q.delta (H.time i.succ))
    (hneck : p.neckRadius (H.time i.succ) = q.neckRadius (H.time i.succ))
    (hprotected : p.protectedRadius (H.time i.succ) = q.protectedRadius (H.time i.succ))
    (hfixed : p.fixed = q.fixed) (hradius : p.modelRadius = q.modelRadius)
    (horder : p.modelOrder = q.modelOrder) (haccuracy : p.modelAccuracy = q.modelAccuracy)
    (hrecenter : p.recenterConstant = q.recenterConstant) :
    (R.congrParameters hdelta hneck hprotected hfixed hradius horder haccuracy hrecenter).delta = R.delta := by
  cases p
  cases q
  cases hfixed
  cases hradius
  cases horder
  cases haccuracy
  cases hrecenter
  rfl

@[simp] theorem congrParameters_order {p q : CutoffParameters} (R : GeometricCutoffRecord H i p)
    (hdelta : p.delta (H.time i.succ) = q.delta (H.time i.succ))
    (hneck : p.neckRadius (H.time i.succ) = q.neckRadius (H.time i.succ))
    (hprotected : p.protectedRadius (H.time i.succ) = q.protectedRadius (H.time i.succ))
    (hfixed : p.fixed = q.fixed) (hradius : p.modelRadius = q.modelRadius)
    (horder : p.modelOrder = q.modelOrder) (haccuracy : p.modelAccuracy = q.modelAccuracy)
    (hrecenter : p.recenterConstant = q.recenterConstant) :
    (R.congrParameters hdelta hneck hprotected hfixed hradius horder haccuracy hrecenter).order = R.order := by
  cases p
  cases q
  cases hfixed
  cases hradius
  cases horder
  cases haccuracy
  cases hrecenter
  rfl

@[simp] theorem congrParameters_nominalRadius {p q : CutoffParameters} (R : GeometricCutoffRecord H i p)
    (hdelta : p.delta (H.time i.succ) = q.delta (H.time i.succ))
    (hneck : p.neckRadius (H.time i.succ) = q.neckRadius (H.time i.succ))
    (hprotected : p.protectedRadius (H.time i.succ) = q.protectedRadius (H.time i.succ))
    (hfixed : p.fixed = q.fixed) (hradius : p.modelRadius = q.modelRadius)
    (horder : p.modelOrder = q.modelOrder) (haccuracy : p.modelAccuracy = q.modelAccuracy)
    (hrecenter : p.recenterConstant = q.recenterConstant) :
    (R.congrParameters hdelta hneck hprotected hfixed hradius horder haccuracy hrecenter).nominalRadius = R.nominalRadius := by
  cases p
  cases q
  cases hfixed
  cases hradius
  cases horder
  cases haccuracy
  cases hrecenter
  rfl

theorem congrParameters_neck_heq {p q : CutoffParameters} (R : GeometricCutoffRecord H i p)
    (hdelta : p.delta (H.time i.succ) = q.delta (H.time i.succ))
    (hneck : p.neckRadius (H.time i.succ) = q.neckRadius (H.time i.succ))
    (hprotected : p.protectedRadius (H.time i.succ) = q.protectedRadius (H.time i.succ))
    (hfixed : p.fixed = q.fixed) (hradius : p.modelRadius = q.modelRadius)
    (horder : p.modelOrder = q.modelOrder) (haccuracy : p.modelAccuracy = q.modelAccuracy)
    (hrecenter : p.recenterConstant = q.recenterConstant) :
    HEq (R.congrParameters hdelta hneck hprotected hfixed hradius horder haccuracy hrecenter).neck R.neck := by
  cases p
  cases q
  cases hfixed
  cases hradius
  cases horder
  cases haccuracy
  cases hrecenter
  rfl

theorem congrParameters_static_heq {p q : CutoffParameters} (R : GeometricCutoffRecord H i p)
    (hdelta : p.delta (H.time i.succ) = q.delta (H.time i.succ))
    (hneck : p.neckRadius (H.time i.succ) = q.neckRadius (H.time i.succ))
    (hprotected : p.protectedRadius (H.time i.succ) = q.protectedRadius (H.time i.succ))
    (hfixed : p.fixed = q.fixed) (hradius : p.modelRadius = q.modelRadius)
    (horder : p.modelOrder = q.modelOrder) (haccuracy : p.modelAccuracy = q.modelAccuracy)
    (hrecenter : p.recenterConstant = q.recenterConstant) :
    HEq (R.congrParameters hdelta hneck hprotected hfixed hradius horder haccuracy hrecenter).static
      R.static := by
  cases p
  cases q
  cases hfixed
  cases hradius
  cases horder
  cases haccuracy
  cases hrecenter
  rfl


end GeometricCutoffRecord
end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology


namespace CutoffParameters

def spliceAt (p q : CutoffParameters) (s : ℝ) : CutoffParameters :=
  { p with
    delta := fun t => if t = s then q.delta t else p.delta t
    neckRadius := fun t => if t = s then q.neckRadius t else p.neckRadius t
    protectedRadius := fun t => if t = s then q.protectedRadius t else p.protectedRadius t
    delta_pos := fun t ht => by split <;> [exact q.delta_pos t ht; exact p.delta_pos t ht]
    delta_lt_one := fun t ht => by split <;> [exact q.delta_lt_one t ht; exact p.delta_lt_one t ht]
    neckRadius_pos := fun t ht => by split <;> [exact q.neckRadius_pos t ht; exact p.neckRadius_pos t ht]
    protectedRadius_pos := fun t ht => by split <;> [exact q.protectedRadius_pos t ht; exact p.protectedRadius_pos t ht] }

@[simp] theorem spliceAt_delta_self (p q : CutoffParameters) (s : ℝ) :
    (p.spliceAt q s).delta s = q.delta s := ite_eq_left rfl

@[simp] theorem spliceAt_neckRadius_self (p q : CutoffParameters) (s : ℝ) :
    (p.spliceAt q s).neckRadius s = q.neckRadius s := ite_eq_left rfl

@[simp] theorem spliceAt_protectedRadius_self (p q : CutoffParameters) (s : ℝ) :
    (p.spliceAt q s).protectedRadius s = q.protectedRadius s := ite_eq_left rfl

theorem spliceAt_delta_of_ne (p q : CutoffParameters) {s t : ℝ} (h : t ≠ s) :
    (p.spliceAt q s).delta t = p.delta t := ite_eq_right h

theorem spliceAt_neckRadius_of_ne (p q : CutoffParameters) {s t : ℝ} (h : t ≠ s) :
    (p.spliceAt q s).neckRadius t = p.neckRadius t := ite_eq_right h

theorem spliceAt_protectedRadius_of_ne (p q : CutoffParameters) {s t : ℝ} (h : t ≠ s) :
    (p.spliceAt q s).protectedRadius t = p.protectedRadius t := ite_eq_right h

end CutoffParameters

namespace GeometricCutoffRecord
universe u
variable {H : ObservedHistory.{u}} {i : Fin H.eventCount}

def spliceParametersOfNe {p q : CutoffParameters} (R : GeometricCutoffRecord H i p)
    {s : ℝ} (hs : H.time i.succ ≠ s) : GeometricCutoffRecord H i (p.spliceAt q s) :=
  R.congrParameters (p.spliceAt_delta_of_ne q hs).symm
    (p.spliceAt_neckRadius_of_ne q hs).symm
    (p.spliceAt_protectedRadius_of_ne q hs).symm rfl rfl rfl rfl rfl

def spliceParametersAt {p q : CutoffParameters} (R : GeometricCutoffRecord H i q)
    (hfixed : q.fixed = p.fixed) (hradius : q.modelRadius = p.modelRadius)
    (horder : q.modelOrder = p.modelOrder) (haccuracy : q.modelAccuracy = p.modelAccuracy)
    (hrecenter : q.recenterConstant = p.recenterConstant) :
    GeometricCutoffRecord H i (p.spliceAt q (H.time i.succ)) :=
  R.congrParameters (p.spliceAt_delta_self q _).symm
    (p.spliceAt_neckRadius_self q _).symm (p.spliceAt_protectedRadius_self q _).symm
    hfixed hradius horder haccuracy hrecenter


@[simp] theorem spliceParametersOfNe_static {p q : CutoffParameters}
    (R : GeometricCutoffRecord H i p) {s : ℝ} (hs : H.time i.succ ≠ s) :
    (R.spliceParametersOfNe (q := q) hs).static = R.static := by
  exact eq_of_heq (R.congrParameters_static_heq _ _ _ _ _ _ _ _)

theorem spliceParametersOfNe_static_heq {p q : CutoffParameters}
    (R : GeometricCutoffRecord H i p) {s : ℝ} (hs : H.time i.succ ≠ s) :
    HEq (R.spliceParametersOfNe (q := q) hs).static R.static :=
  heq_of_eq (R.spliceParametersOfNe_static hs)

theorem spliceParametersAt_static_heq {p q : CutoffParameters} (R : GeometricCutoffRecord H i q)
    (hfixed : q.fixed = p.fixed) (hradius : q.modelRadius = p.modelRadius)
    (horder : q.modelOrder = p.modelOrder) (haccuracy : q.modelAccuracy = p.modelAccuracy)
    (hrecenter : q.recenterConstant = p.recenterConstant) :
    HEq (R.spliceParametersAt hfixed hradius horder haccuracy hrecenter).static R.static := by
  exact R.congrParameters_static_heq _ _ _ _ _ _ _ _

theorem spliceParametersOfNe_neck_heq {p q : CutoffParameters}
    (R : GeometricCutoffRecord H i p) {s : ℝ} (hs : H.time i.succ ≠ s) :
    HEq (R.spliceParametersOfNe (q := q) hs).neck R.neck := by
  exact R.congrParameters_neck_heq _ _ _ _ _ _ _ _

theorem spliceParametersAt_neck_heq {p q : CutoffParameters} (R : GeometricCutoffRecord H i q)
    (hfixed : q.fixed = p.fixed) (hradius : q.modelRadius = p.modelRadius)
    (horder : q.modelOrder = p.modelOrder) (haccuracy : q.modelAccuracy = p.modelAccuracy)
    (hrecenter : q.recenterConstant = p.recenterConstant) :
    HEq (R.spliceParametersAt hfixed hradius horder haccuracy hrecenter).neck R.neck := by
  exact R.congrParameters_neck_heq _ _ _ _ _ _ _ _


def spliceParametersAtEvent {p q : CutoffParameters} (j : Fin H.eventCount)
    (old : ∀ i : Fin H.eventCount, i ≠ j → GeometricCutoffRecord H i p)
    (new : GeometricCutoffRecord H j q)
    (hfixed : q.fixed = p.fixed) (hradius : q.modelRadius = p.modelRadius)
    (horder : q.modelOrder = p.modelOrder) (haccuracy : q.modelAccuracy = p.modelAccuracy)
    (hrecenter : q.recenterConstant = p.recenterConstant) :
    ∀ i : Fin H.eventCount, GeometricCutoffRecord H i (p.spliceAt q (H.time j.succ)) := by
  classical
  intro i
  by_cases hij : i = j
  · subst i
    exact new.spliceParametersAt hfixed hradius horder haccuracy hrecenter
  · apply (old i hij).spliceParametersOfNe
    intro heq
    have hindex := H.time_strictMono.injective heq
    exact hij (Fin.succ_injective _ hindex)

end GeometricCutoffRecord

namespace CutoffParameters
universe u

def spliceEarlierRecords
    {H : ObservedHistory.{u}} {p q : CutoffParameters} {s : ℝ}
    (hs : H.time (Fin.last H.eventCount) < s)
    (records : ∀ i : Fin H.eventCount, GeometricCutoffRecord H i p) :
    ∀ i : Fin H.eventCount, GeometricCutoffRecord H i (p.spliceAt q s) := by
  intro i
  apply (records i).spliceParametersOfNe
  exact ne_of_lt ((H.time_strictMono.monotone (Fin.le_last i.succ)).trans_lt hs)


end CutoffParameters
end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.GeometricCutoffRecord

universe u

variable {H : ObservedHistory.{u}} {i : Fin H.eventCount}

@[simp] theorem spliceParametersOfNe_delta {p q : CutoffParameters}
    (R : GeometricCutoffRecord H i p) {s : ℝ} (hs : H.time i.succ ≠ s) :
    (R.spliceParametersOfNe (q := q) hs).delta = R.delta := by
  unfold spliceParametersOfNe
  apply congrParameters_delta

@[simp] theorem spliceParametersOfNe_order {p q : CutoffParameters}
    (R : GeometricCutoffRecord H i p) {s : ℝ} (hs : H.time i.succ ≠ s) :
    (R.spliceParametersOfNe (q := q) hs).order = R.order := by
  unfold spliceParametersOfNe
  apply congrParameters_order

@[simp] theorem spliceParametersAt_delta {p q : CutoffParameters}
    (R : GeometricCutoffRecord H i q)
    (hfixed : q.fixed = p.fixed) (hradius : q.modelRadius = p.modelRadius)
    (horder : q.modelOrder = p.modelOrder) (haccuracy : q.modelAccuracy = p.modelAccuracy)
    (hrecenter : q.recenterConstant = p.recenterConstant) :
    (R.spliceParametersAt hfixed hradius horder haccuracy hrecenter).delta = R.delta := by
  unfold spliceParametersAt
  apply congrParameters_delta

@[simp] theorem spliceParametersAt_order {p q : CutoffParameters}
    (R : GeometricCutoffRecord H i q)
    (hfixed : q.fixed = p.fixed) (hradius : q.modelRadius = p.modelRadius)
    (horder : q.modelOrder = p.modelOrder) (haccuracy : q.modelAccuracy = p.modelAccuracy)
    (hrecenter : q.recenterConstant = p.recenterConstant) :
    (R.spliceParametersAt hfixed hradius horder haccuracy hrecenter).order = R.order := by
  unfold spliceParametersAt
  apply congrParameters_order

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.GeometricCutoffRecord

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
universe u

private theorem exists_small_cutoff_precision
    (c ρ K : ℝ) (hc : 0 < c) (hρ : 0 < ρ) (hK : 0 < K) :
    ∃ δ : ℝ, 0 < δ ∧ c * δ ≤ 1 / 2 ∧ 2 * K * (δ ^ 2 * ρ) ^ 2 < 1 := by
  let B := max 1 (2 * K * ρ ^ 2)
  have hB : 0 < B := zero_lt_one.trans_le (le_max_left _ _)
  let δ := min (1 / (2 * c)) (min (1 / 2) (1 / (2 * B)))
  have hδ : 0 < δ := by dsimp [δ]; positivity
  have hδc : δ ≤ 1 / (2 * c) := min_le_left _ _
  have hδhalf : δ ≤ 1 / 2 := (min_le_right _ _).trans (min_le_left _ _)
  have hδB : δ ≤ 1 / (2 * B) := (min_le_right _ _).trans (min_le_right _ _)
  have hcδ : c * δ ≤ 1 / 2 := by
    have hh := (le_div_iff₀ (by positivity : 0 < 2 * c)).mp hδc
    linarith only [hh]
  have hBδ : B * δ ≤ 1 / 2 := by
    have hh := (le_div_iff₀ (by positivity : 0 < 2 * B)).mp hδB
    linarith only [hh]
  have hδ2 : δ ^ 2 ≤ δ := by nlinarith only [hδ.le, hδhalf]
  have hδ4 : δ ^ 4 ≤ δ := by
    have hh := mul_le_mul hδ2 hδ2 (sq_nonneg δ) hδ.le
    nlinarith only [hh, hδ2]
  have hk : 2 * K * ρ ^ 2 ≤ B := le_max_right _ _
  have hb := mul_le_mul_of_nonneg_left hδ4 (show 0 ≤ 2 * K * ρ ^ 2 by positivity)
  have hh := mul_le_mul_of_nonneg_right hk hδ.le
  refine ⟨δ, hδ, hcδ, ?_⟩
  nlinarith only [hb, hh, hBδ]

theorem exists_uniform_static_cap_scale_lower_bound
    (c ρ K : ℝ) (hc : 0 < c) (hρ : 0 < ρ) (hK : 0 < K) :
    ∃ δ₀ : ℝ, 0 < δ₀ ∧
      ∀ (H : ObservedHistory.{u}) (i : Fin H.eventCount) (p : CutoffParameters),
        p.recenterConstant ≤ c → p.delta (H.time i.succ) ≤ δ₀ →
        p.neckRadius (H.time i.succ) ≤ ρ →
        ∀ R : GeometricCutoffRecord H i p,
          ∀ b : (H.event i).RetainedBoundaryIndex, K < (R.static b).neck.scale := by
  obtain ⟨δ₀, hδ₀, hcδ, hsmall⟩ := exists_small_cutoff_precision c ρ K hc hρ hK
  refine ⟨δ₀, hδ₀, ?_⟩
  intro H i p hpc hδ hρp R b
  have htime : 0 ≤ H.time i.succ := by
    rw [← H.time_zero]
    exact H.time_strictMono.monotone (Fin.zero_le _)
  have hpδ : 0 < p.delta (H.time i.succ) := p.delta_pos _ htime
  have hpr : 0 < p.neckRadius (H.time i.succ) := p.neckRadius_pos _ htime
  have hδsq : (p.delta (H.time i.succ)) ^ 2 ≤ δ₀ ^ 2 :=
    pow_le_pow_left₀ hpδ.le hδ 2
  have hradius : R.nominalRadius ⟨b.val.1⟩ < δ₀ ^ 2 * ρ :=
    (R.nominal_small ⟨b.val.1⟩).trans_le
      (mul_le_mul hδsq hρp hpr.le (sq_nonneg δ₀))
  have hnom := R.nominal_pos ⟨b.val.1⟩
  have hnom2 : (R.nominalRadius ⟨b.val.1⟩) ^ 2 ≤ (δ₀ ^ 2 * ρ) ^ 2 :=
    pow_le_pow_left₀ hnom.le hradius.le 2
  have hbudget : 2 * K * (R.nominalRadius ⟨b.val.1⟩) ^ 2 < 1 :=
    (mul_le_mul_of_nonneg_left hnom2 (by positivity : 0 ≤ 2 * K)).trans_lt hsmall
  have hscale : 2 * K < (R.neck b.val.1).scale := by
    rw [R.scale_eq, inv_eq_one_div]
    exact (lt_div_iff₀ (sq_pos_of_pos hnom)).mpr hbudget
  have herror : p.recenterConstant * R.delta b.val.1 ≤ 1 / 2 := by
    have hprec : R.delta b.val.1 ≤ δ₀ := (R.delta_le _).trans hδ
    have hprod := mul_le_mul hpc hprec (R.delta_pos _).le hc.le
    exact hprod.trans hcδ
  have hcomp := (abs_le.mp (R.recenter_scale_comparison b)).1
  have hratio : 1 / 2 ≤ (R.static b).neck.scale / (R.neck b.val.1).scale := by
    linarith only [hcomp, herror]
  have hlow := (le_div_iff₀ (R.neck b.val.1).scale_pos).mp hratio
  linarith only [hscale, hlow]

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
