import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.CanonicalCapWindows
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.BackwardTraceLocalChart
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.EventRetainedInterior

set_option autoImplicit false

noncomputable section

open Set
open scoped Manifold

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

universe u

namespace MetricCutCapEvent

variable {P Q : OrientedThreeStage.{u}} {a s : ℝ} (E : MetricCutCapEvent P Q a s)

theorem regularCrossing_oldOutput_of_isInteriorPoint (w : E.old)
    (hw : letI : ChartedSpace (EuclideanHalfSpace 3) E.old := E.oldCharts
      (𝓡∂ 3).IsInteriorPoint w) :
    E.RegularCrossing w.1.1 (E.oldOutput w) :=
  ⟨w, hw, rfl, rfl⟩

theorem retainedBoundary_of_presentation_cap_eq_inl {b : E.transition.trace.tubes.Boundary}
    {z : ThreeBall} {q : Q.Carrier}
    (h : E.transition.trace.presentation (E.transition.trace.capping.cap b z) = Sum.inl q) :
    E.RetainedBoundary b := by
  intro y
  have : ConnectedSpace ThreeBall := isConnected_iff_connectedSpace.mp
    ((convex_closedBall (0 : ThreeSpace) 1).isConnected ⟨0, by simp⟩)
  have hpre : IsPreconnected (range
      (E.transition.trace.presentation ∘ E.transition.trace.capping.cap b)) :=
    isPreconnected_range
      (E.transition.trace.presentation.continuous.comp
        (E.transition.trace.capping.cap b).continuous)
  have hsub := hpre.subset_isClopen isClopen_range_inl ⟨_, ⟨z, rfl⟩, ⟨q, h.symm⟩⟩
  obtain ⟨q', hq'⟩ := hsub ⟨sphereToThreeBall ((E.transition.trace.capping.attaching b).symm y),
    rfl⟩
  refine ⟨q', ?_⟩
  rw [hq']
  change _ = E.transition.trace.presentation (E.transition.trace.capping.cap b _)
  rw [E.transition.trace.capping.boundary_eq, Homeomorph.apply_symm_apply]

theorem exists_retained_cap_of_not_regularCrossing
    (hOld : E.old = E.transition.trace.retainedCore) {q : Q.Carrier}
    (hq : ∀ p : P.Carrier, ¬ E.RegularCrossing p q) :
    ∃ (b : E.RetainedBoundaryIndex) (z : ThreeBall),
      E.transition.trace.presentation (E.transition.trace.capping.cap b.1 z) = Sum.inl q := by
  let T := E.transition.trace
  let S : Set Q.Carrier := ⋃ b : T.tubes.Boundary,
    Sum.inl ⁻¹' (T.presentation '' range (T.capping.cap b))
  have hS : IsClosed S := isClosed_iUnion_of_finite fun b =>
    ((isCompact_range (T.capping.cap b).continuous).image
      T.presentation.continuous).isClosed.preimage continuous_inl
  have hcompl : Sᶜ ⊆ range E.oldOutput := by
    intro q' hq'
    have hn : T.presentation.symm (Sum.inl q') ∈
        range T.capping.coreInclusion ∪ ⋃ b, range (T.capping.cap b) := by
      rw [T.capping.exhaustive]
      exact mem_univ _
    rcases hn with ⟨x, hx⟩ | hn
    · have hxq : T.presentation (T.capping.coreInclusion x) = Sum.inl q' := by
        rw [hx, Homeomorph.apply_symm_apply]
      have hxold : x ∈ E.old := by
        rw [hOld]
        exact ⟨q', hxq⟩
      refine ⟨⟨x, hxold⟩, ?_⟩
      have h := E.oldOutput_eq ⟨x, hxold⟩
      rw [hxq] at h
      exact (Sum.inl_injective h).symm
    · obtain ⟨b, z, hz⟩ := mem_iUnion.mp hn
      have hmem : q' ∈ S := mem_iUnion.mpr ⟨b, T.capping.cap b z, ⟨z, rfl⟩, by
        rw [hz, Homeomorph.apply_symm_apply]⟩
      exact absurd hmem hq'
  have hqS : q ∈ S := by
    by_contra hqS
    obtain ⟨p, hp⟩ := E.exists_regularCrossing_of_mem_interior_oldOutput q
      (mem_interior.mpr ⟨Sᶜ, hcompl, hS.isOpen_compl, hqS⟩)
    exact hq p hp
  obtain ⟨b, hb⟩ := mem_iUnion.mp hqS
  obtain ⟨_, ⟨z, rfl⟩, hz⟩ := hb
  exact ⟨⟨b, E.retainedBoundary_of_presentation_cap_eq_inl hz⟩, z, hz⟩

end MetricCutCapEvent

namespace GeometricCutoffRecord

variable {H : ObservedHistory.{u}} {j : Fin H.eventCount} {p : CutoffParameters}

theorem exists_cap_of_not_regularCrossing_target (R : GeometricCutoffRecord H j p)
    {q : (H.stage j.succ).Carrier}
    (hq : ∀ p' : (H.stage j.castSucc).Carrier, ¬ (H.event j).RegularCrossing p' q) :
    ∃ (b : (H.event j).RetainedBoundaryIndex) (z : ThreeBall),
      q = (R.static b).inclusion ((R.static b).witness.cap z) := by
  obtain ⟨b, z, hz⟩ := (H.event j).exists_retained_cap_of_not_regularCrossing
    R.old_eq_retained hq
  refine ⟨b, z, Sum.inl_injective (β := (H.event j).discarded.Carrier) ?_⟩
  rw [← hz]
  exact (R.static b).cap_eq z

theorem exists_regularCrossing_or_exists_cap (R : GeometricCutoffRecord H j p)
    (q : (H.stage j.succ).Carrier) :
    (∃ p' : (H.stage j.castSucc).Carrier, (H.event j).RegularCrossing p' q) ∨
      ∃ (b : (H.event j).RetainedBoundaryIndex) (z : ThreeBall),
        q = (R.static b).inclusion ((R.static b).witness.cap z) := by
  by_cases h : ∃ p' : (H.stage j.castSucc).Carrier, (H.event j).RegularCrossing p' q
  · exact Or.inl h
  · exact Or.inr (R.exists_cap_of_not_regularCrossing_target fun p' hp' => h ⟨p', hp'⟩)

end GeometricCutoffRecord

namespace ObservedHistory

theorem exists_latest_event_without_regularCrossing (H : ObservedHistory.{u})
    {first last : Fin (H.eventCount + 1)} (hle : first ≤ last) (y : (H.stage last).Carrier)
    (hy : IsEmpty (BackwardPointTrace H first last hle y)) :
    ∃ (j : Fin H.eventCount) (_ : first ≤ j.castSucc) (hl : j.succ ≤ last)
      (A : BackwardPointTrace H j.succ last hl y),
      ∀ p' : (H.stage j.castSucc).Carrier,
        ¬ (H.event j).RegularCrossing p' (A.point j.succ le_rfl hl) := by
  classical
  let good : Finset (Fin (H.eventCount + 1)) := Finset.univ.filter fun k =>
    first ≤ k ∧ ∃ hk : k ≤ last, Nonempty (BackwardPointTrace H k last hk y)
  have hlast : last ∈ good := Finset.mem_filter.mpr
    ⟨Finset.mem_univ _, hle, le_rfl, ⟨BackwardPointTrace.singleton H last y⟩⟩
  obtain ⟨k, hk, hmin⟩ : ∃ k ∈ good, ∀ k' ∈ good, k ≤ k' :=
    ⟨good.min' ⟨last, hlast⟩, good.min'_mem _, fun k' hk' => good.min'_le k' hk'⟩
  obtain ⟨-, hfk, hkl, ⟨A⟩⟩ := Finset.mem_filter.mp hk
  have hne : first ≠ k := by
    intro he
    subst he
    exact hy.false A
  have hlt : first < k := lt_of_le_of_ne hfk hne
  obtain ⟨j, rfl⟩ := Fin.eq_succ_of_ne_zero (ne_of_gt ((Fin.zero_le first).trans_lt hlt))
  have hf : first ≤ j.castSucc := Fin.le_iff_val_le_val.mpr (Nat.le_of_lt_succ hlt)
  refine ⟨j, hf, hkl, A, fun p' hp' => ?_⟩
  have hmem : j.castSucc ∈ good := Finset.mem_filter.mpr
    ⟨Finset.mem_univ _, hf, j.castSucc_lt_succ.le.trans hkl, ⟨A.prepend p' hp'⟩⟩
  exact (not_le_of_gt j.castSucc_lt_succ) (hmin _ hmem)

theorem exists_cap_capture (H : ObservedHistory.{u}) {p : CutoffParameters}
    (records : ∀ j, GeometricCutoffRecord H j p)
    (hcan : ∀ j b, ((records j).static b).hasCanonicalWindow)
    {first last : Fin (H.eventCount + 1)} (hle : first ≤ last) (y : (H.stage last).Carrier)
    (hy : IsEmpty (BackwardPointTrace H first last hle y)) :
    ∃ (j : Fin H.eventCount) (_ : first ≤ j.castSucc) (hl : j.succ ≤ last)
      (A : BackwardPointTrace H j.succ last hl y)
      (b : (H.event j).RetainedBoundaryIndex) (z : ThreeBall)
      (x : standardCapWindow p.modelRadius),
      (∀ p' : (H.stage j.castSucc).Carrier,
        ¬ (H.event j).RegularCrossing p' (A.point j.succ le_rfl hl)) ∧
      A.point j.succ le_rfl hl =
        ((records j).static b).inclusion (((records j).static b).witness.cap z) ∧
      ‖x.1‖ ≤ StandardCap.transitionEnd ∧
      A.point j.succ le_rfl hl = ((records j).static b).window x := by
  obtain ⟨j, hf, hl, A, hno⟩ := H.exists_latest_event_without_regularCrossing hle y hy
  obtain ⟨b, z, hz⟩ := (records j).exists_cap_of_not_regularCrossing_target hno
  obtain ⟨_, _, _, _, _, _, _, hwin⟩ := hcan j b
  obtain ⟨x, hxn, hx⟩ := hwin z
  exact ⟨j, hf, hl, A, b, z, x, hno, hz, hxn, hz.trans hx.symm⟩

end ObservedHistory

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
