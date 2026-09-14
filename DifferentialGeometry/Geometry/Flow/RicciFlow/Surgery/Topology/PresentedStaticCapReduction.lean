import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.GeometricCutoffFrontier
import Mathlib.Topology.Connected.Clopen

set_option autoImplicit false

noncomputable section

open Bundle Manifold Set
open DifferentialGeometry.Geometry.Curvature
open scoped Manifold ContDiff Topology

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

universe u

namespace MetricCutCapEvent

variable {P Q : OrientedThreeStage.{u}} {a s : ℝ} (E : MetricCutCapEvent P Q a s)

theorem exists_cap_presentation_eq_sum_inl {b : E.transition.trace.tubes.Boundary}
    (hb : E.RetainedBoundary b) (x : ThreeBall) :
    ∃ q : Q.Carrier,
      E.transition.trace.presentation (E.transition.trace.capping.cap b x) = Sum.inl q := by
  classical
  have hconn : IsPreconnected (univ : Set ThreeBall) := by
    have : ConnectedSpace ThreeBall := isConnected_iff_connectedSpace.mp
      ((convex_closedBall (0 : ThreeSpace) 1).isConnected ⟨0, by simp⟩)
    exact isPreconnected_univ
  have hcont : Continuous fun y : ThreeBall =>
      E.transition.trace.presentation (E.transition.trace.capping.cap b y) :=
    E.transition.trace.presentation.continuous.comp
      (E.transition.trace.capping.cap b).continuous
  let y₀ : Sphere 2 := ⟨EuclideanSpace.single 0 1, by simp⟩
  have hcap : E.transition.trace.capping.cap b (sphereToThreeBall y₀) =
      E.transition.trace.capping.coreInclusion
        (E.transition.trace.tubes.coreBoundarySphere b
          (E.transition.trace.capping.attaching b y₀)) :=
    E.transition.trace.capping.boundary_eq b y₀
  have hpoint : (fun y : ThreeBall =>
      E.transition.trace.presentation (E.transition.trace.capping.cap b y))
        (sphereToThreeBall y₀) ∈ Set.range (Sum.inl : Q.Carrier → Q.Carrier ⊕
          E.discarded.Carrier) := by
    dsimp only
    rw [hcap]
    obtain ⟨q, hq⟩ := hb (E.transition.trace.capping.attaching b y₀)
    exact ⟨q, hq.symm⟩
  have hsub : (univ : Set ThreeBall) ⊆ (fun y : ThreeBall =>
      E.transition.trace.presentation (E.transition.trace.capping.cap b y)) ⁻¹'
        Set.range (Sum.inl : Q.Carrier → Q.Carrier ⊕ E.discarded.Carrier) :=
    hconn.subset_isClopen (isClopen_range_inl.preimage hcont)
      ⟨sphereToThreeBall y₀, mem_univ _, hpoint⟩
  obtain ⟨q, hq⟩ := hsub (mem_univ x)
  exact ⟨q, hq.symm⟩

theorem retainedCore_of_presentation_eq_sum_inl {x : E.transition.trace.tubes.core}
    {q : Q.Carrier}
    (h : E.transition.trace.presentation (E.transition.trace.capping.coreInclusion x) =
      Sum.inl q) :
    x ∈ E.transition.trace.retainedCore :=
  ⟨q, h⟩

end MetricCutCapEvent

variable (H : ObservedHistory.{u}) (i : Fin H.eventCount)

structure PresentedStaticCapFrontier (fixed : StaticCapScaffold) (D : ℝ) (m : ℕ) (η : ℝ)
    {delta : ℝ} {order : ℕ} (neck : NormalizedNeck (H.event i).terminal.metric delta order)
    (b : (H.event i).RetainedBoundaryIndex) where
  witness : StaticCapWitness neck fixed D m η
  inclusion : C(witness.Output, (H.stage i.succ).Carrier)
  inclusion_smooth : IsSmoothEmbedding ThreeModel ThreeModel ∞ inclusion
  inclusion_metric : ∀ x V W, witness.metric.inner x V W =
    (H.event i).outputMetric.inner (inclusion x)
      (mfderiv ThreeModel ThreeModel inclusion x V)
      (mfderiv ThreeModel ThreeModel inclusion x W)
  attaching_eq : (witness.attaching : Sphere 2 → Sphere 2) =
    (H.event i).transition.trace.capping.attaching b.1
  cap_presentation : ∀ x : ThreeBall,
    (H.event i).transition.trace.presentation
      ((H.event i).transition.trace.capping.cap b.1 x) =
        Sum.inl (inclusion (witness.cap x))
  retained_point : (x : neckRetainedCollar delta) →
    (H.event i).transition.trace.tubes.core
  retained_point_eq : ∀ (x : neckRetainedCollar delta) (hx : x.1 ∈ neckBuffer delta),
    (retained_point x).1 = (neck.chart ⟨x.1, hx⟩).1
  retained_presentation : ∀ x : neckRetainedCollar delta,
    (H.event i).transition.trace.presentation
      ((H.event i).transition.trace.capping.coreInclusion (retained_point x)) =
        Sum.inl (inclusion (witness.retained x))

namespace PresentedStaticCapFrontier

variable {H i}

def ofFrontier {fixed : StaticCapScaffold} {D : ℝ} {m : ℕ} {η : ℝ}
    {delta : ℝ} {order : ℕ}
    {neck : NormalizedNeck (H.event i).terminal.metric delta order}
    {b : (H.event i).RetainedBoundaryIndex}
    (F : PresentedStaticCapFrontier H i fixed D m η neck b) :
    PresentedStaticCap H i fixed D m η b where
  delta := delta
  order := order
  neck := neck
  witness := F.witness
  inclusion := F.inclusion
  inclusion_smooth := F.inclusion_smooth
  inclusion_metric := F.inclusion_metric
  cap_eq := F.cap_presentation
  attaching_eq := F.attaching_eq
  retained_point := fun x => ⟨F.retained_point x, ⟨_, F.retained_presentation x⟩⟩
  retained_point_eq := F.retained_point_eq
  retained_eq := F.retained_presentation

def toFrontier {fixed : StaticCapScaffold} {D : ℝ} {m : ℕ} {η : ℝ}
    {b : (H.event i).RetainedBoundaryIndex}
    (S : PresentedStaticCap H i fixed D m η b) :
    PresentedStaticCapFrontier H i fixed D m η S.neck b where
  witness := S.witness
  inclusion := S.inclusion
  inclusion_smooth := S.inclusion_smooth
  inclusion_metric := S.inclusion_metric
  attaching_eq := S.attaching_eq
  cap_presentation := S.cap_eq
  retained_point := fun x => (S.retained_point x).1
  retained_point_eq := S.retained_point_eq
  retained_presentation := S.retained_eq

end PresentedStaticCapFrontier

variable {H i}

theorem nonempty_presentedStaticCap_of_nonempty_frontier {fixed : StaticCapScaffold} {D : ℝ}
    {m : ℕ} {η : ℝ} {delta : ℝ} {order : ℕ}
    {neck : NormalizedNeck (H.event i).terminal.metric delta order}
    {b : (H.event i).RetainedBoundaryIndex}
    (h : Nonempty (PresentedStaticCapFrontier H i fixed D m η neck b)) :
    Nonempty (PresentedStaticCap H i fixed D m η b) :=
  h.map PresentedStaticCapFrontier.ofFrontier

theorem exists_nonempty_frontier_of_presentedStaticCap {fixed : StaticCapScaffold} {D : ℝ}
    {m : ℕ} {η : ℝ} {b : (H.event i).RetainedBoundaryIndex}
    (S : PresentedStaticCap H i fixed D m η b) :
    ∃ (delta : ℝ) (order : ℕ)
      (neck : NormalizedNeck (H.event i).terminal.metric delta order),
      Nonempty (PresentedStaticCapFrontier H i fixed D m η neck b) :=
  ⟨S.delta, S.order, S.neck, ⟨PresentedStaticCapFrontier.toFrontier S⟩⟩

variable {H : ObservedHistory.{u}} {i : Fin H.eventCount} {parameters : CutoffParameters}

theorem GeometricCutoffRecord.ofFrontier_toFrontier
    (R : GeometricCutoffRecord H i parameters) :
    GeometricCutoffRecord.ofFrontier (GeometricCutoffRecord.toFrontier R) = R := by
  rfl

theorem GeometricCutoffFrontier.toFrontier_ofFrontier
    (F : GeometricCutoffFrontier H i parameters) :
    GeometricCutoffRecord.toFrontier (GeometricCutoffRecord.ofFrontier F) = F := by
  rfl

theorem two_le_order_of_order_lower {ι : Type*} {parameters : CutoffParameters}
    {delta : ι → ℝ} {order : ι → ℕ}
    (h : ∀ α, max (parameters.modelOrder + 6) (2 * ⌊(delta α)⁻¹⌋₊ + 4) ≤ order α) :
    ∀ α, 2 ≤ order α :=
  fun α => le_trans (le_trans (by norm_num) (Nat.le_add_left 4 (2 * ⌊(delta α)⁻¹⌋₊)))
    (le_trans (le_max_right _ _) (h α))

theorem recenterBuffer {H : ObservedHistory.{u}} {i : Fin H.eventCount}
    {parameters : CutoffParameters} (h : HasRecenterConstants.{u} parameters)
    {delta : (H.event i).transition.trace.tubes.Index → ℝ}
    {order : (H.event i).transition.trace.tubes.Index → ℕ}
    (neck : ∀ α, NormalizedNeck (H.event i).terminal.metric (delta α) (order α))
    (delta_le : ∀ α, delta α ≤ parameters.delta (H.time i.succ))
    (order_lower : ∀ α, max (parameters.modelOrder + 6)
      (2 * ⌊(delta α)⁻¹⌋₊ + 4) ≤ order α)
    (b : (H.event i).RetainedBoundaryIndex) :
    ∀ x : neckBuffer (parameters.recenterConstant * delta b.1.1),
      (x.1.1, (if b.1.2 then (1 : ℝ) else -1) * (1 + x.1.2)) ∈ neckBuffer (delta b.1.1) :=
  Classical.choose (recenter_fields_of_recenterConstants (H := H) (i := i)
    (parameters := parameters) h neck (two_le_order_of_order_lower order_lower) delta_le b)

noncomputable def recenterNeck {H : ObservedHistory.{u}} {i : Fin H.eventCount}
    {parameters : CutoffParameters} (h : HasRecenterConstants.{u} parameters)
    {delta : (H.event i).transition.trace.tubes.Index → ℝ}
    {order : (H.event i).transition.trace.tubes.Index → ℕ}
    (neck : ∀ α, NormalizedNeck (H.event i).terminal.metric (delta α) (order α))
    (delta_le : ∀ α, delta α ≤ parameters.delta (H.time i.succ))
    (order_lower : ∀ α, max (parameters.modelOrder + 6)
      (2 * ⌊(delta α)⁻¹⌋₊ + 4) ≤ order α)
    (b : (H.event i).RetainedBoundaryIndex) :
    NormalizedNeck (H.event i).terminal.metric
      (parameters.recenterConstant * delta b.1.1) (order b.1.1) :=
  Classical.choose (Classical.choose_spec (recenter_fields_of_recenterConstants (H := H) (i := i)
    (parameters := parameters) h neck (two_le_order_of_order_lower order_lower) delta_le b))

theorem recenterNeck_spec {H : ObservedHistory.{u}} {i : Fin H.eventCount}
    {parameters : CutoffParameters} (h : HasRecenterConstants.{u} parameters)
    {delta : (H.event i).transition.trace.tubes.Index → ℝ}
    {order : (H.event i).transition.trace.tubes.Index → ℕ}
    (neck : ∀ α, NormalizedNeck (H.event i).terminal.metric (delta α) (order α))
    (delta_le : ∀ α, delta α ≤ parameters.delta (H.time i.succ))
    (order_lower : ∀ α, max (parameters.modelOrder + 6)
      (2 * ⌊(delta α)⁻¹⌋₊ + 4) ≤ order α)
    (b : (H.event i).RetainedBoundaryIndex) :
    (recenterNeck h neck delta_le order_lower b).sphereMark = (neck b.1.1).sphereMark ∧
    (∀ x : neckBuffer (parameters.recenterConstant * delta b.1.1),
      (recenterNeck h neck delta_le order_lower b).chart x =
        (neck b.1.1).chart
          ⟨(x.1.1, (if b.1.2 then (1 : ℝ) else -1) * (1 + x.1.2)),
            recenterBuffer h neck delta_le order_lower b x⟩) ∧
    |(recenterNeck h neck delta_le order_lower b).scale / (neck b.1.1).scale - 1| ≤
      parameters.recenterConstant * delta b.1.1 :=
  Classical.choose_spec (Classical.choose_spec (recenter_fields_of_recenterConstants
    (H := H) (i := i) (parameters := parameters)
    h neck (two_le_order_of_order_lower order_lower) delta_le b))

structure GeometricCutoffFrontierReduction (H : ObservedHistory.{u}) (i : Fin H.eventCount)
    (parameters : CutoffParameters) where
  singular : (H.event i).incoming.SingularEndpoint
  nominalRadius : Nonempty (H.event i).transition.trace.tubes.Index → ℝ
  nominal_small : ∀ h, nominalRadius h <
    (parameters.delta (H.time i.succ))^2 * parameters.neckRadius (H.time i.succ)
  nominal_time : ∀ h, (nominalRadius h)^2 ≤ H.time i.succ
  delta : (H.event i).transition.trace.tubes.Index → ℝ
  delta_le : ∀ α, delta α ≤ parameters.delta (H.time i.succ)
  order : (H.event i).transition.trace.tubes.Index → ℕ
  order_lower : ∀ α, max (parameters.modelOrder + 6)
    (2 * ⌊(delta α)⁻¹⌋₊ + 4) ≤ order α
  neck : ∀ α, NormalizedNeck (H.event i).terminal.metric (delta α) (order α)
  scale_eq : ∀ α, (neck α).scale = ((nominalRadius ⟨α⟩) ^ 2)⁻¹
  buffer_disjoint : Pairwise fun α β =>
    Disjoint (Set.range (neck α).chart) (Set.range (neck β).chart)
  tube_eq : ∀ α, ∀ x : TubeDomain, ∀ hx : (x.1, x.2.1) ∈ neckBuffer (delta α),
    (H.event i).transition.trace.tubes.tube α x = ((neck α).chart ⟨(x.1, x.2.1), hx⟩).1
  backward : ∀ α, IncomingBackwardNeck H i (neck α) (nominalRadius ⟨α⟩)
  protected_interior : ∀ x : (H.event i).incoming.terminalRegularOpen,
    metricScalarAt (H.event i).terminal.metric x ≤
      ((parameters.protectedRadius (H.time i.succ)) ^ 2)⁻¹ →
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
  old_eq_retained : (H.event i).old = (H.event i).transition.trace.retainedCore
  curvature_preserving : ∀ a : ℝ, 0 < a →
    (∀ x : (H.event i).incoming.terminalRegularOpen,
      InFixedHamiltonIveyRegion (H.event i).terminal.metric a x) →
    ∀ x : (H.stage i.succ).Carrier, InFixedHamiltonIveyRegion (H.event i).outputMetric a x
  scalar_preserving : ∀ L : ℝ, L ≤ 0 →
    (∀ x : (H.event i).incoming.terminalRegularOpen,
      L ≤ metricScalarAt (H.event i).terminal.metric x) →
    ∀ x : (H.stage i.succ).Carrier, L ≤ metricScalarAt (H.event i).outputMetric x
  recenter : HasRecenterConstants.{u} parameters
  staticFrontier : ∀ b : (H.event i).RetainedBoundaryIndex,
    PresentedStaticCapFrontier H i parameters.fixed parameters.modelRadius parameters.modelOrder
      parameters.modelAccuracy
      (recenterNeck (H := H) (i := i) (parameters := parameters) recenter neck
        (fun α => delta_le α) (fun α => order_lower α) b) b

namespace GeometricCutoffFrontierReduction

def ofReduction (R : GeometricCutoffFrontierReduction H i parameters) :
    GeometricCutoffFrontier H i parameters where
  singular := R.singular
  nominalRadius := R.nominalRadius
  nominal_small := R.nominal_small
  nominal_time := R.nominal_time
  delta := R.delta
  delta_le := R.delta_le
  order := R.order
  order_lower := R.order_lower
  neck := R.neck
  scale_eq := R.scale_eq
  buffer_disjoint := R.buffer_disjoint
  tube_eq := R.tube_eq
  backward := R.backward
  protected_interior := R.protected_interior
  retained_meets_protected := R.retained_meets_protected
  one_retained_side := R.one_retained_side
  no_cuts_discard := R.no_cuts_discard
  static := fun b => PresentedStaticCapFrontier.ofFrontier (R.staticFrontier b)
  recenter_mark := fun b => (recenterNeck_spec (H := H) (i := i) (parameters := parameters)
    R.recenter R.neck R.delta_le R.order_lower b).1
  recenter_delta := fun b => rfl
  recenter_scale_comparison := fun b => (recenterNeck_spec (H := H) (i := i)
    (parameters := parameters) R.recenter R.neck R.delta_le R.order_lower b).2.2
  recenter_chart := fun b x hx => by
    have hspec := (recenterNeck_spec (H := H) (i := i) (parameters := parameters)
      R.recenter R.neck R.delta_le R.order_lower b).2.1
    change (recenterNeck (H := H) (i := i) (parameters := parameters) R.recenter R.neck
        R.delta_le R.order_lower b).chart x =
      (R.neck b.1.1).chart
        ⟨(x.1.1, (if b.1.2 then (1 : ℝ) else -1) * (1 + x.1.2)), hx⟩
    rw [hspec x]
  recenter_in_buffer := fun b => recenterBuffer (H := H) (i := i) (parameters := parameters)
    R.recenter R.neck R.delta_le R.order_lower b
  old_eq_retained := R.old_eq_retained
  curvature_preserving := R.curvature_preserving
  scalar_preserving := R.scalar_preserving

theorem nonempty_geometricCutoffFrontier_of_reduction
    (h : Nonempty (GeometricCutoffFrontierReduction H i parameters)) :
    Nonempty (GeometricCutoffFrontier H i parameters) :=
  h.map ofReduction

end GeometricCutoffFrontierReduction

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
