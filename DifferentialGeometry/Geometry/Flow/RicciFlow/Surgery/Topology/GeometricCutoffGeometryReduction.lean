import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.PresentedStaticCapReduction
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.CapPersistence
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.StandardNeckCutCapInstance

set_option autoImplicit false

noncomputable section

open Set Bundle Manifold
open DifferentialGeometry.Geometry.Curvature
open scoped Manifold ContDiff Topology

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

universe u

namespace CutCapTopology

variable {M Q D N : Type*} [TopologicalSpace M] [TopologicalSpace Q] [TopologicalSpace D]
  [TopologicalSpace N]

theorem iUnion_range_cap_eq_empty (E : CutCapTopology M Q D N) [IsEmpty E.tubes.Index] :
    (⋃ b : E.tubes.Boundary, Set.range (E.capping.cap b)) = ∅ := by
  ext x
  simp only [Set.mem_iUnion, Set.mem_empty_iff_false, iff_false, not_exists]
  exact fun b => isEmptyElim b.1

theorem range_coreInclusion_eq_univ (E : CutCapTopology M Q D N) [IsEmpty E.tubes.Index] :
    Set.range E.capping.coreInclusion = Set.univ := by
  have h := E.capping.exhaustive
  rw [iUnion_range_cap_eq_empty E, Set.union_empty] at h
  exact h

theorem exists_notMem_retainedCore (E : CutCapTopology M Q D N) [IsEmpty E.tubes.Index] :
    ∃ x : E.tubes.core, x ∉ E.retainedCore := by
  rcases E.nontrivial with h | h
  · exact isEmptyElim h.some
  · obtain ⟨d⟩ := h
    have hsurj : Function.Surjective fun x : E.tubes.core =>
        E.presentation (E.capping.coreInclusion x) := by
      intro y
      obtain ⟨n, hn⟩ := E.presentation.surjective y
      have hnmem : n ∈ Set.range E.capping.coreInclusion := by
        rw [range_coreInclusion_eq_univ E]
        exact Set.mem_univ n
      obtain ⟨x, hx⟩ := hnmem
      exact ⟨x, by change E.presentation (E.capping.coreInclusion x) = y; rw [hx]; exact hn⟩
    obtain ⟨x, hx⟩ := hsurj (Sum.inr d)
    refine ⟨x, fun hxr => ?_⟩
    obtain ⟨q, hq⟩ := hxr
    exact Sum.inr_ne_inl (hx.symm.trans hq)

end CutCapTopology

variable (H : ObservedHistory.{u}) (i : Fin H.eventCount)

theorem geometricCutoff_no_cuts_discard
    [IsEmpty (H.event i).transition.trace.tubes.Index] :
    ∃ x : (H.event i).transition.trace.tubes.core,
      x ∉ (H.event i).transition.trace.retainedCore :=
  CutCapTopology.exists_notMem_retainedCore (H.event i).transition.trace

namespace MetricCutCapEvent

variable {P Q : OrientedThreeStage.{u}} {a s : ℝ} (E : MetricCutCapEvent P Q a s)

theorem retainedBoundary_iff_capRetained (b : E.transition.trace.tubes.Boundary) :
    E.RetainedBoundary b ↔ E.transition.trace.capRetained b :=
  (E.transition.trace.capRetained_iff_coreBoundarySphere_mem_retainedCore b).symm

theorem one_retained_side_iff_cap (α : E.transition.trace.tubes.Index) :
    (E.RetainedBoundary (α, true) ↔ ¬ E.RetainedBoundary (α, false)) ↔
      (E.transition.trace.capRetained (α, true) ↔
        E.transition.trace.capDiscarded (α, false)) := by
  rw [retainedBoundary_iff_capRetained, retainedBoundary_iff_capRetained,
    CutCapTopology.capDiscarded_iff_not_capRetained]

end MetricCutCapEvent

def canonicalNominalRadius {ι : Type*} (s : ι → ℝ) (h : Nonempty ι) : ℝ :=
  Real.sqrt ((s (Classical.choice h))⁻¹)

theorem canonicalNominalRadius_pos {ι : Type*} {s : ι → ℝ} (hpos : ∀ a, 0 < s a)
    (h : Nonempty ι) : 0 < canonicalNominalRadius s h :=
  Real.sqrt_pos.2 (inv_pos.2 (hpos _))

theorem canonicalNominalRadius_sq {ι : Type*} {s : ι → ℝ} (hpos : ∀ a, 0 < s a)
    (hconst : ∀ a b, s a = s b) (a : ι) :
    ((canonicalNominalRadius s ⟨a⟩) ^ 2)⁻¹ = s a := by
  have hchoice : s (Classical.choice (⟨a⟩ : Nonempty ι)) = s a := hconst _ _
  have hsq : (canonicalNominalRadius s ⟨a⟩) ^ 2 = (s a)⁻¹ := by
    rw [canonicalNominalRadius, hchoice,
      Real.sq_sqrt (le_of_lt (inv_pos.2 (hpos a)))]
  rw [hsq, inv_inv]

theorem scale_const_of_scale_eq_shape {ι : Type*} {s : ι → ℝ} {r : Nonempty ι → ℝ}
    (h : ∀ α, s α = ((r ⟨α⟩) ^ 2)⁻¹) : ∀ α β, s α = s β := by
  intro α β
  have hp : (⟨α⟩ : Nonempty ι) = ⟨β⟩ := Subsingleton.elim _ _
  rw [h α, h β, hp]

theorem canonicalNominalRadius_eq_of_scale_eq_shape {ι : Type*} {s : ι → ℝ}
    {r : Nonempty ι → ℝ} (hpos : ∀ h, 0 < r h) (h : ∀ α, s α = ((r ⟨α⟩) ^ 2)⁻¹)
    (hh : Nonempty ι) : canonicalNominalRadius s hh = r hh := by
  set α : ι := Classical.choice hh
  have hα : (⟨α⟩ : Nonempty ι) = hh := Subsingleton.elim _ _
  have hs : s α = ((r hh) ^ 2)⁻¹ := by rw [h α, hα]
  have hsq : (r hh) ^ 2 = (s α)⁻¹ := by rw [hs, inv_inv]
  rw [canonicalNominalRadius, ← hsq, Real.sqrt_sq (le_of_lt (hpos hh))]

namespace MetricCutCapEvent

variable {P Q : OrientedThreeStage.{u}} {a s : ℝ} (E : MetricCutCapEvent P Q a s)

def TubeBandHit (x : E.transition.trace.tubes.core) : Prop :=
  ∃ t : E.transition.trace.tubes.Index, x.1 ∈ E.transition.trace.tubes.tube t ''
    {z : TubeDomain | (-2 : ℝ) < z.2.1 ∧ z.2.1 < 2}

theorem old_eq_retained_of_old_tubeBand
    (h : ∀ x ∈ E.transition.trace.retainedCore, E.TubeBandHit x → x ∈ E.old) :
    E.old = E.transition.trace.retainedCore := by
  refine Set.Subset.antisymm E.old_retained fun x hx => ?_
  by_cases hband : E.TubeBandHit x
  · exact h x hx hband
  · exact E.old_contains_outside x hx fun t ht => hband ⟨t, ht⟩

theorem old_tubeBand_of_old_eq_retained (h : E.old = E.transition.trace.retainedCore) :
    ∀ x ∈ E.transition.trace.retainedCore, E.TubeBandHit x → x ∈ E.old := by
  intro x hx _
  rw [h]
  exact hx

theorem old_eq_retained_of_isEmpty_index [IsEmpty E.transition.trace.tubes.Index] :
    E.old = E.transition.trace.retainedCore :=
  E.old_eq_retained_of_old_tubeBand fun _ _ hb => by
    obtain ⟨t, _⟩ := hb
    exact isEmptyElim t

end MetricCutCapEvent

namespace GeometricCutoffRecord

variable {H : ObservedHistory.{u}} {i : Fin H.eventCount} {parameters : CutoffParameters}
  (G : GeometricCutoffRecord H i parameters)

theorem scale_const_of_scale_eq (α β : (H.event i).transition.trace.tubes.Index) :
    (G.neck α).scale = (G.neck β).scale :=
  scale_const_of_scale_eq_shape G.scale_eq α β

theorem nominalRadius_eq_canonical (α : (H.event i).transition.trace.tubes.Index) :
    G.nominalRadius ⟨α⟩ = canonicalNominalRadius (fun γ => (G.neck γ).scale) ⟨α⟩ :=
  (canonicalNominalRadius_eq_of_scale_eq_shape G.nominal_pos G.scale_eq ⟨α⟩).symm

end GeometricCutoffRecord

theorem tube_eq_of_abs_snd_le_two {H : ObservedHistory.{u}} {i : Fin H.eventCount}
    {parameters : CutoffParameters} (G : GeometricCutoffRecord H i parameters)
    (α : (H.event i).transition.trace.tubes.Index) (z : neckBuffer (G.delta α))
    (hz : |(z.1.2)| ≤ 2) :
    ∃ w : TubeDomain, (H.event i).transition.trace.tubes.tube α w = ((G.neck α).chart z).1 := by
  obtain ⟨hz1, hz2⟩ := abs_le.mp hz
  exact ⟨(z.1.1, ⟨z.1.2, hz1, hz2⟩),
    G.tube_eq α (z.1.1, ⟨z.1.2, hz1, hz2⟩) z.2⟩

theorem pairwise_disjoint_chart_range_central {H : ObservedHistory.{u}} {i : Fin H.eventCount}
    {parameters : CutoffParameters} (G : GeometricCutoffRecord H i parameters)
    {α β : (H.event i).transition.trace.tubes.Index} (h : α ≠ β) :
    Disjoint (Set.range fun z : {z : neckBuffer (G.delta α) | |(z.1.2)| ≤ 2} =>
        (G.neck α).chart z)
      (Set.range fun z : {z : neckBuffer (G.delta β) | |(z.1.2)| ≤ 2} =>
        (G.neck β).chart z) := by
  refine Set.disjoint_left.mpr fun p hp hq => ?_
  obtain ⟨z, rfl⟩ := hp
  obtain ⟨z', hz'⟩ := hq
  obtain ⟨w, hw⟩ := tube_eq_of_abs_snd_le_two G α z z.2
  obtain ⟨w', hw'⟩ := tube_eq_of_abs_snd_le_two G β z' z'.2
  refine Set.disjoint_left.mp ((H.event i).transition.trace.tubes.disjoint h) ⟨w, hw⟩ ?_
  exact ⟨w', hw'.trans (congrArg Subtype.val hz')⟩

theorem standardNeckCutCap_one_retained_side :
    (∀ z : Sphere 2, standardNeckCutCap.tubes.coreBoundarySphere (PUnit.unit, true) z ∈
        standardNeckCutCap.retainedCore) ↔
      ¬ (∀ z : Sphere 2,
        standardNeckCutCap.tubes.coreBoundarySphere (PUnit.unit, false) z ∈
          standardNeckCutCap.retainedCore) := by
  constructor
  · intro h
    exact absurd (h sphereNorth)
      (standardNeckCutCap_coreBoundarySphere_true_not_mem_retainedCore sphereNorth)
  · intro h
    exact absurd (fun z =>
      standardNeckCutCap_coreBoundarySphere_false_mem_retainedCore z) h

structure GeometricCutoffGeometryFrontier (H : ObservedHistory.{u}) (i : Fin H.eventCount)
    (parameters : CutoffParameters) where
  delta : (H.event i).transition.trace.tubes.Index → ℝ
  delta_le : ∀ α, delta α ≤ parameters.delta (H.time i.succ)
  order : (H.event i).transition.trace.tubes.Index → ℕ
  order_lower : ∀ α, max (parameters.modelOrder + 6)
    (2 * ⌊(delta α)⁻¹⌋₊ + 4) ≤ order α
  neck : ∀ α, NormalizedNeck (H.event i).terminal.metric (delta α) (order α)
  scale_const : ∀ α β, (neck α).scale = (neck β).scale
  nominal_small : ∀ h, canonicalNominalRadius (fun α => (neck α).scale) h <
    (parameters.delta (H.time i.succ))^2 * parameters.neckRadius (H.time i.succ)
  nominal_time : ∀ h, (canonicalNominalRadius (fun α => (neck α).scale) h)^2 ≤
    H.time i.succ
  backward : ∀ α, IncomingBackwardNeck H i (neck α)
    (canonicalNominalRadius (fun α => (neck α).scale) ⟨α⟩)
  singular : (H.event i).incoming.SingularEndpoint
  buffer_disjoint : Pairwise fun α β =>
    Disjoint (Set.range (neck α).chart) (Set.range (neck β).chart)
  tube_eq : ∀ α, ∀ x : TubeDomain, ∀ hx : (x.1, x.2.1) ∈ neckBuffer (delta α),
    (H.event i).transition.trace.tubes.tube α x = ((neck α).chart ⟨(x.1, x.2.1), hx⟩).1
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
  old_tube_band : ∀ x ∈ (H.event i).transition.trace.retainedCore,
    MetricCutCapEvent.TubeBandHit (H.event i) x → x ∈ (H.event i).old
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

namespace GeometricCutoffGeometryFrontier

variable {H : ObservedHistory.{u}} {i : Fin H.eventCount} {parameters : CutoffParameters}

def toReduction (F : GeometricCutoffGeometryFrontier H i parameters) :
    GeometricCutoffFrontierReduction H i parameters where
  singular := F.singular
  nominalRadius := canonicalNominalRadius fun α => (F.neck α).scale
  nominal_small := fun h => F.nominal_small h
  nominal_time := fun h => F.nominal_time h
  delta := F.delta
  delta_le := F.delta_le
  order := F.order
  order_lower := F.order_lower
  neck := F.neck
  scale_eq := fun α => (canonicalNominalRadius_sq
    (s := fun β => (F.neck β).scale) (fun β => (F.neck β).scale_pos) F.scale_const α).symm
  buffer_disjoint := F.buffer_disjoint
  tube_eq := F.tube_eq
  backward := fun α => F.backward α
  protected_interior := F.protected_interior
  retained_meets_protected := F.retained_meets_protected
  one_retained_side := F.one_retained_side
  no_cuts_discard := fun h => @geometricCutoff_no_cuts_discard H i h
  old_eq_retained := (H.event i).old_eq_retained_of_old_tubeBand F.old_tube_band
  curvature_preserving := F.curvature_preserving
  scalar_preserving := F.scalar_preserving
  recenter := F.recenter
  staticFrontier := F.staticFrontier

def toFrontier (F : GeometricCutoffGeometryFrontier H i parameters) :
    GeometricCutoffFrontier H i parameters :=
  GeometricCutoffFrontierReduction.ofReduction F.toReduction

def ofReduction (R : GeometricCutoffFrontierReduction H i parameters) :
    GeometricCutoffGeometryFrontier H i parameters where
  delta := R.delta
  delta_le := R.delta_le
  order := R.order
  order_lower := R.order_lower
  neck := R.neck
  scale_const := scale_const_of_scale_eq_shape R.scale_eq
  nominal_small := fun h => by
    rw [canonicalNominalRadius_eq_of_scale_eq_shape
      (nominal_pos_of_incomingBackwardNeck R.neck R.backward) R.scale_eq h]
    exact R.nominal_small h
  nominal_time := fun h => by
    rw [canonicalNominalRadius_eq_of_scale_eq_shape
      (nominal_pos_of_incomingBackwardNeck R.neck R.backward) R.scale_eq h]
    exact R.nominal_time h
  backward := fun α => by
    rw [canonicalNominalRadius_eq_of_scale_eq_shape
      (nominal_pos_of_incomingBackwardNeck R.neck R.backward) R.scale_eq ⟨α⟩]
    exact R.backward α
  singular := R.singular
  buffer_disjoint := R.buffer_disjoint
  tube_eq := R.tube_eq
  protected_interior := R.protected_interior
  retained_meets_protected := R.retained_meets_protected
  one_retained_side := R.one_retained_side
  old_tube_band := (H.event i).old_tubeBand_of_old_eq_retained R.old_eq_retained
  curvature_preserving := R.curvature_preserving
  scalar_preserving := R.scalar_preserving
  recenter := R.recenter
  staticFrontier := R.staticFrontier

theorem nonempty_geometricCutoffGeometryFrontier_iff_nonempty_reduction :
    Nonempty (GeometricCutoffGeometryFrontier H i parameters) ↔
      Nonempty (GeometricCutoffFrontierReduction H i parameters) :=
  ⟨fun ⟨F⟩ => ⟨F.toReduction⟩, fun ⟨R⟩ => ⟨ofReduction R⟩⟩

theorem nonempty_geometricCutoffRecord_of_geometryFrontier
    (h : Nonempty (GeometricCutoffGeometryFrontier H i parameters)) :
    Nonempty (GeometricCutoffRecord H i parameters) :=
  h.map fun F => GeometricCutoffRecord.ofFrontier F.toFrontier

end GeometricCutoffGeometryFrontier

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
