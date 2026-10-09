import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.AnalyticAdmissibility
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.TracedRegion
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.HistoryIdentities

set_option autoImplicit false

noncomputable section

open Set Manifold DifferentialGeometry DifferentialGeometry.Topology
  DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
  DifferentialGeometry.Geometry.Curvature DifferentialGeometry.Tensor0SBundle
open scoped Manifold ContDiff

namespace GC.LongTime.Ch12

universe u

variable (H : ObservedHistory.{u}) (cut : Icc (0 : ℝ) H.horizon)

/-- The actual index embedding of a restricted history. -/
def restrictIndex_CX2 (j : Fin ((H.restrict cut).eventCount + 1)) : Fin (H.eventCount + 1) :=
  Fin.castLE (Nat.add_le_add_right (Nat.le_of_lt_succ (H.activeStage cut).isLt) 1) j

/-- An observation time of the prefix as a time of its source history. -/
def restrictTime_CX2 (t : Icc (0 : ℝ) (H.restrict cut).horizon) : Icc (0 : ℝ) H.horizon :=
  ⟨t.val, t.property.1, t.property.2.trans cut.property.2⟩

theorem restrict_active_CX2 (t : Icc (0 : ℝ) (H.restrict cut).horizon) :
    restrictIndex_CX2 H cut ((H.restrict cut).activeStage t) =
      H.activeStage (restrictTime_CX2 H cut t) := H.restrict_activeStage cut t

/-- Trace transport along equal stage indices, retaining the actual endpoint. -/
def traceReindex_CX2 {first last first' last' : Fin (H.eventCount + 1)}
    {hle : first ≤ last} {hle' : first' ≤ last'}
    {x : (H.stage last).Carrier} {x' : (H.stage last').Carrier}
    (hf : first = first') (hl : last = last') (hx : HEq x x')
    (A : BackwardPointTrace H first last hle x) :
    BackwardPointTrace H first' last' hle' x' := by
  subst first'
  subst last'
  cases hx
  exact A

/-- Extend a prefix trace to the same event-index interval in the original history. -/
def traceOfRestriction_CX2
    {first last : Fin ((H.restrict cut).eventCount + 1)} {hle : first ≤ last}
    {x : ((H.restrict cut).stage last).Carrier}
    (A : BackwardPointTrace (H.restrict cut) first last hle x) :
    BackwardPointTrace H (restrictIndex_CX2 H cut first) (restrictIndex_CX2 H cut last)
      (show restrictIndex_CX2 H cut first ≤ restrictIndex_CX2 H cut last from hle) x where
  point j hj hl := A.point ⟨j.val, by
    have h₁ : j.val ≤ last.val := hl
    have h₂ := last.isLt
    omega⟩ hj hl
  endpoint_eq := A.endpoint_eq
  crossing i hf hl := A.crossing ⟨i.val, by
    have h₁ : i.val + 1 ≤ last.val := hl
    have h₂ := last.isLt
    omega⟩ hf hl

/-- Restrict a trace whose endpoints lie before the cutoff. -/
def traceToRestriction_CX2
    {first last : Fin ((H.restrict cut).eventCount + 1)} {hle : first ≤ last}
    {x : ((H.restrict cut).stage last).Carrier}
    (A : BackwardPointTrace H (restrictIndex_CX2 H cut first) (restrictIndex_CX2 H cut last)
      (show restrictIndex_CX2 H cut first ≤ restrictIndex_CX2 H cut last from hle) x) :
    BackwardPointTrace (H.restrict cut) first last hle x where
  point j hj hl := A.point (restrictIndex_CX2 H cut j) hj hl
  endpoint_eq := A.endpoint_eq
  crossing i hf hl := A.crossing
    (Fin.castLE (Nat.le_of_lt_succ (H.activeStage cut).isLt) i) hf hl

theorem traceOfRestriction_point_CX2
    {first last : Fin ((H.restrict cut).eventCount + 1)} {hle : first ≤ last}
    {x : ((H.restrict cut).stage last).Carrier}
    (A : BackwardPointTrace (H.restrict cut) first last hle x)
    (j : Fin ((H.restrict cut).eventCount + 1)) (hf : first ≤ j) (hl : j ≤ last) :
    (traceOfRestriction_CX2 H cut A).point (restrictIndex_CX2 H cut j) hf hl = A.point j hf hl := rfl

/-- Reindexing does not replace the physical trace point. -/
theorem traceReindex_point_CX2 {first last first' last' : Fin (H.eventCount + 1)}
    {hle : first ≤ last} {hle' : first' ≤ last'}
    {x : (H.stage last).Carrier} {x' : (H.stage last').Carrier}
    (hf : first = first') (hl : last = last') (hx : HEq x x')
    (A : BackwardPointTrace H first last hle x)
    (j : Fin (H.eventCount + 1)) (hj : first ≤ j) (hjl : j ≤ last)
    (hj' : first' ≤ j) (hjl' : j ≤ last') :
    (traceReindex_CX2 H (hle' := hle') hf hl hx A).point j hj' hjl' = A.point j hj hjl := by
  subst first'
  subst last'
  cases hx
  rfl

/-- The carrier transport induced by the actual prefix's active-stage equality. -/
def restrictPoint_CX2 (t : Icc (0 : ℝ) (H.restrict cut).horizon)
    (x : ((H.restrict cut).stageAt t).Carrier) : (H.stageAt (restrictTime_CX2 H cut t)).Carrier :=
  cast (congrArg OrientedThreeStage.Carrier (H.restrict_stageAt cut t)) x

theorem restrictPoint_heq_CX2 (t : Icc (0 : ℝ) (H.restrict cut).horizon)
    (x : ((H.restrict cut).stageAt t).Carrier) : HEq (restrictPoint_CX2 H cut t x) x :=
  cast_heq _ _

/-- Lift a trace at two actual times, rather than only at two indices. -/
def traceAtOfRestriction_CX2
    {a t : Icc (0 : ℝ) (H.restrict cut).horizon} {hat : a ≤ t}
    {x : ((H.restrict cut).stageAt t).Carrier}
    (A : BackwardPointTrace (H.restrict cut) ((H.restrict cut).activeStage a)
      ((H.restrict cut).activeStage t) ((H.restrict cut).activeStage_mono hat) x) :
    BackwardPointTrace H (H.activeStage (restrictTime_CX2 H cut a))
      (H.activeStage (restrictTime_CX2 H cut t))
      (H.activeStage_mono (show restrictTime_CX2 H cut a ≤ restrictTime_CX2 H cut t from hat))
      (restrictPoint_CX2 H cut t x) :=
  traceReindex_CX2 H (restrict_active_CX2 H cut a) (restrict_active_CX2 H cut t)
    (restrictPoint_heq_CX2 H cut t x).symm (traceOfRestriction_CX2 H cut A)

/-- Equality of indices transports trace points without changing their values. -/
theorem tracePoint_heq_CX2 {first last : Fin (H.eventCount + 1)} {hle : first ≤ last}
    {x : (H.stage last).Carrier} (A : BackwardPointTrace H first last hle x)
    {j k : Fin (H.eventCount + 1)} (hjk : j = k)
    (hj : first ≤ j) (hjl : j ≤ last) (hk : first ≤ k) (hkl : k ≤ last) :
    HEq (A.point j hj hjl) (A.point k hk hkl) := by
  subst k
  rfl

theorem traceAtOfRestriction_point_heq_CX2
    {a t : Icc (0 : ℝ) (H.restrict cut).horizon} {hat : a ≤ t}
    {x : ((H.restrict cut).stageAt t).Carrier}
    (A : BackwardPointTrace (H.restrict cut) ((H.restrict cut).activeStage a)
      ((H.restrict cut).activeStage t) ((H.restrict cut).activeStage_mono hat) x)
    (v : Icc (0 : ℝ) (H.restrict cut).horizon) (hav : a ≤ v) (hvt : v ≤ t) :
    HEq ((traceAtOfRestriction_CX2 H cut (hat := hat) A).point
      (H.activeStage (restrictTime_CX2 H cut v))
      (H.activeStage_mono (show restrictTime_CX2 H cut a ≤ restrictTime_CX2 H cut v from hav))
      (H.activeStage_mono (show restrictTime_CX2 H cut v ≤ restrictTime_CX2 H cut t from hvt)))
      (A.point ((H.restrict cut).activeStage v)
        ((H.restrict cut).activeStage_mono hav) ((H.restrict cut).activeStage_mono hvt)) := by
  let B := traceAtOfRestriction_CX2 H cut (hat := hat) A
  have hf : H.activeStage (restrictTime_CX2 H cut a) ≤
      restrictIndex_CX2 H cut ((H.restrict cut).activeStage v) := by
    rw [restrict_active_CX2]
    exact H.activeStage_mono hav
  have hl : restrictIndex_CX2 H cut ((H.restrict cut).activeStage v) ≤
      H.activeStage (restrictTime_CX2 H cut t) := by
    rw [restrict_active_CX2]
    exact H.activeStage_mono hvt
  apply (tracePoint_heq_CX2 H B (restrict_active_CX2 H cut v).symm _ _ hf hl).trans
  apply heq_of_eq
  exact traceReindex_point_CX2 H
      (hle' := H.activeStage_mono (show restrictTime_CX2 H cut a ≤ restrictTime_CX2 H cut t from hat))
      (restrict_active_CX2 H cut a) (restrict_active_CX2 H cut t)
    (restrictPoint_heq_CX2 H cut t x).symm (traceOfRestriction_CX2 H cut A)
    (restrictIndex_CX2 H cut ((H.restrict cut).activeStage v))
    ((H.restrict cut).activeStage_mono hav) ((H.restrict cut).activeStage_mono hvt) hf hl

/-- Curvature norms commute with the stage and metric equalities of a prefix. -/
theorem rmNormSq_heq_CX2 {P Q : OrientedThreeStage.{u}} {g : P.Metric} {h : Q.Metric}
    (hPQ : P = Q) (hgh : HEq g h) {x : P.Carrier} {y : Q.Carrier} (hxy : HEq x y) :
    normSq0S g x 4 (metricRm04At g x) = normSq0S h y 4 (metricRm04At h y) := by
  subst Q
  cases hgh
  cases hxy
  rfl

theorem terminalRmNormSq_congr_CX2 (i : Fin H.eventCount)
    {x y : (H.stage i.castSucc).Carrier}
    (hx : x ∈ (H.event i).incoming.terminalRegularRegion)
    (hy : y ∈ (H.event i).incoming.terminalRegularRegion) (hxy : x = y) :
    normSq0S (H.event i).terminal.metric ⟨x, hx⟩ 4
        (metricRm04At (H.event i).terminal.metric ⟨x, hx⟩) =
      normSq0S (H.event i).terminal.metric ⟨y, hy⟩ 4
        (metricRm04At (H.event i).terminal.metric ⟨y, hy⟩) := by
  subst y
  rfl

/-- Prefix transport preserves both ordinary-time and incoming-terminal
curvature bounds; the second clause is needed at every surgery seam. -/
theorem traceAtOfRestriction_bounded_CX2
    {a t : Icc (0 : ℝ) (H.restrict cut).horizon} {hat : a ≤ t}
    {x : ((H.restrict cut).stageAt t).Carrier}
    (A : BackwardPointTrace (H.restrict cut) ((H.restrict cut).activeStage a)
      ((H.restrict cut).activeStage t) ((H.restrict cut).activeStage_mono hat) x)
    {K : ℝ} (hA : A.isRmBoundedBy (hat := hat) K) :
    (traceAtOfRestriction_CX2 H cut (hat := hat) A).isRmBoundedBy
      (hat := show restrictTime_CX2 H cut a ≤ restrictTime_CX2 H cut t from hat) K := by
  constructor
  · intro v hav hvt
    let v' : Icc (0 : ℝ) (H.restrict cut).horizon :=
      ⟨v.val, v.property.1, (show v.val ≤ t.val from hvt).trans t.property.2⟩
    have hav' : a ≤ v' := hav
    have hvt' : v' ≤ t := hvt
    have hmetric := H.restrict_sliceMetric cut v'
    have hpoint := traceAtOfRestriction_point_heq_CX2 H cut (hat := hat) A v' hav' hvt'
    have heq := rmNormSq_heq_CX2 (H.restrict_stageAt cut v') hmetric hpoint.symm
    exact heq.symm.trans_le (hA.1 v' hav' hvt')
  · intro i hf hl
    let i' : Fin (H.restrict cut).eventCount := ⟨i.val, by
      have hlast := congrArg Fin.val (restrict_active_CX2 H cut t)
      have hi : i.val + 1 ≤ (H.activeStage (restrictTime_CX2 H cut t)).val := hl
      have ht := ((H.restrict cut).activeStage t).isLt
      change i.val < (H.activeStage cut).val
      change ((H.restrict cut).activeStage t).val < (H.activeStage cut).val + 1 at ht
      change ((H.restrict cut).activeStage t).val = _ at hlast
      omega⟩
    have hf' : (H.restrict cut).activeStage a ≤ i'.castSucc := by
      have h := congrArg Fin.val (restrict_active_CX2 H cut a)
      change ((H.restrict cut).activeStage a).val = _ at h
      exact Fin.le_iff_val_le_val.mpr (h.trans_le (show (H.activeStage (restrictTime_CX2 H cut a)).val ≤ i.val from hf))
    have hl' : i'.succ ≤ (H.restrict cut).activeStage t := by
      have h := congrArg Fin.val (restrict_active_CX2 H cut t)
      change ((H.restrict cut).activeStage t).val = _ at h
      exact Fin.le_iff_val_le_val.mpr ((show i.val + 1 ≤ (H.activeStage (restrictTime_CX2 H cut t)).val from hl).trans_eq h.symm)
    have hp := traceReindex_point_CX2 H
      (hle' := H.activeStage_mono (show restrictTime_CX2 H cut a ≤ restrictTime_CX2 H cut t from hat))
      (restrict_active_CX2 H cut a) (restrict_active_CX2 H cut t)
      (restrictPoint_heq_CX2 H cut t x).symm (traceOfRestriction_CX2 H cut A)
      i.castSucc hf' (i'.castSucc_lt_succ.le.trans hl') hf (i.castSucc_lt_succ.le.trans hl)
    change (traceAtOfRestriction_CX2 H cut (hat := hat) A).point i.castSucc hf
      (i.castSucc_lt_succ.le.trans hl) = A.point i'.castSucc hf'
      (i'.castSucc_lt_succ.le.trans hl') at hp
    exact (terminalRmNormSq_congr_CX2 H i _ _ hp).trans_le (hA.2 i' hf' hl')

end GC.LongTime.Ch12
