import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.RetainedCoreHistoryRestriction
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.HistoryNoncollapsingPresentation.Basic
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.HistoryExtension

set_option autoImplicit false
noncomputable section

open Set
open DifferentialGeometry DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Tensor0SBundle DifferentialGeometry.Integral.Measure
open scoped Manifold ContDiff ENNReal

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

universe u

private def cast_point {P Q : OrientedThreeStage.{u}} (h : P = Q) (p : P.Carrier) :
    Q.Carrier := h ▸ p

private theorem cast_point_heq {P Q : OrientedThreeStage.{u}} (h : P = Q) (p : P.Carrier) :
    HEq (cast_point h p) p := by
  cases h
  exact HEq.rfl

private theorem ball_mem_iff_of_metric_heq
    {P Q : OrientedThreeStage.{u}} (hP : P = Q) (g : P.Metric) (h : Q.Metric)
    (hg : HEq g h) {p x : P.Carrier} {p' x' : Q.Carrier}
    (hp : HEq p p') (hx : HEq x x') (r : ℝ) :
    x ∈ riemannianBallOf g p r ↔ x' ∈ riemannianBallOf h p' r := by
  cases hP
  cases eq_of_heq hg
  cases eq_of_heq hp
  cases eq_of_heq hx
  rfl

private theorem ball_volume_eq_of_metric_heq
    {P Q : OrientedThreeStage.{u}} (hP : P = Q) (g : P.Metric) (h : Q.Metric)
    (hg : HEq g h) {p : P.Carrier} {p' : Q.Carrier} (hp : HEq p p') (r : ℝ) :
    riemannianVolumeMeasure ThreeModel P.Carrier g (riemannianBallOf g p r) =
      riemannianVolumeMeasure ThreeModel Q.Carrier h (riemannianBallOf h p' r) := by
  cases hP
  cases eq_of_heq hg
  cases eq_of_heq hp
  rfl

private theorem curvature_sq_eq_of_metric_heq
    {P Q : OrientedThreeStage.{u}} (hP : P = Q) (g : P.Metric) (h : Q.Metric)
    (hg : HEq g h) {x : P.Carrier} {x' : Q.Carrier} (hx : HEq x x') :
    normSq0S g x 4 (metricRm04At g x) =
      normSq0S h x' 4 (metricRm04At h x') := by
  cases hP
  cases eq_of_heq hg
  cases eq_of_heq hx
  rfl

private theorem trace_point_heq_of_index_eq
    {H : ObservedHistory.{u}} {first last : Fin (H.eventCount + 1)} {hle : first ≤ last}
    {p : (H.stage last).Carrier} (A : BackwardPointTrace H first last hle p)
    {j k : Fin (H.eventCount + 1)} (hjk : j = k)
    (hjf : first ≤ j) (hjl : j ≤ last) (hkf : first ≤ k) (hkl : k ≤ last) :
    HEq (A.point j hjf hjl) (A.point k hkf hkl) := by
  cases hjk
  exact HEq.rfl

private def lift_restricted_time (H : ObservedHistory.{u})
    (a : Icc (0 : ℝ) H.horizon) (t : Icc (0 : ℝ) (H.restrict a).horizon) :
    Icc (0 : ℝ) H.horizon := ⟨t.1, t.2.1, t.2.2.trans a.2.2⟩

private def restrict_trace (H : ObservedHistory.{u}) (a : Icc (0 : ℝ) H.horizon)
    (s t : Icc (0 : ℝ) (H.restrict a).horizon) (hst : s ≤ t)
    {x : ((H.restrict a).stageAt t).Carrier}
    {x' : (H.stageAt (lift_restricted_time H a t)).Carrier} (hx : HEq x x')
    (A : BackwardPointTrace H (H.activeStage (lift_restricted_time H a s))
      (H.activeStage (lift_restricted_time H a t)) (H.activeStage_mono (by exact hst)) x') :
    BackwardPointTrace (H.restrict a) ((H.restrict a).activeStage s)
      ((H.restrict a).activeStage t) ((H.restrict a).activeStage_mono hst) x := by
  let cast : Fin ((H.restrict a).eventCount + 1) → Fin (H.eventCount + 1) :=
    Fin.castLE (Nat.add_le_add_right (Nat.le_of_lt_succ (H.activeStage a).isLt) 1)
  have hs : cast ((H.restrict a).activeStage s) =
      H.activeStage (lift_restricted_time H a s) := H.restrict_activeStage a s
  have ht : cast ((H.restrict a).activeStage t) =
      H.activeStage (lift_restricted_time H a t) := H.restrict_activeStage a t
  have hfirst (j : Fin ((H.restrict a).eventCount + 1))
      (hj : (H.restrict a).activeStage s ≤ j) :
      H.activeStage (lift_restricted_time H a s) ≤ cast j := by
    rw [← hs]
    exact hj
  have hlast (j : Fin ((H.restrict a).eventCount + 1))
      (hj : j ≤ (H.restrict a).activeStage t) :
      cast j ≤ H.activeStage (lift_restricted_time H a t) := by
    rw [← ht]
    exact hj
  refine {
    point := fun j hf hl => A.point (cast j) (hfirst j hf) (hlast j hl)
    endpoint_eq := ?_
    crossing := ?_ }
  · exact eq_of_heq ((trace_point_heq_of_index_eq A ht
      (hfirst _ ((H.restrict a).activeStage_mono hst)) (hlast _ le_rfl)
      (H.activeStage_mono (by exact hst)) le_rfl).trans
      ((heq_of_eq A.endpoint_eq).trans hx.symm))
  · intro i hf hl
    exact A.crossing (Fin.castLE (Nat.le_of_lt_succ (H.activeStage a).isLt) i)
      (hfirst i.castSucc hf) (hlast i.succ hl)

private theorem restrict_trace_controlled (H : ObservedHistory.{u})
    (a : Icc (0 : ℝ) H.horizon) (s t : Icc (0 : ℝ) (H.restrict a).horizon) (hst : s ≤ t)
    {x : ((H.restrict a).stageAt t).Carrier}
    {x' : (H.stageAt (lift_restricted_time H a t)).Carrier} (hx : HEq x x')
    (A : BackwardPointTrace H (H.activeStage (lift_restricted_time H a s))
      (H.activeStage (lift_restricted_time H a t)) (H.activeStage_mono (by exact hst)) x')
    {r : ℝ}
    (hA : A.isRmControlled (a := lift_restricted_time H a s)
      (t := lift_restricted_time H a t) (hat := by exact hst) r) :
    (restrict_trace H a s t hst hx A).isRmControlled (a := s) (t := t) (hat := hst) r := by
  let B := restrict_trace H a s t hst hx A
  let cast : Fin ((H.restrict a).eventCount + 1) → Fin (H.eventCount + 1) :=
    Fin.castLE (Nat.add_le_add_right (Nat.le_of_lt_succ (H.activeStage a).isLt) 1)
  constructor
  · intro v hsv hvt
    have hp : HEq
        (B.point ((H.restrict a).activeStage v)
          ((H.restrict a).activeStage_mono hsv) ((H.restrict a).activeStage_mono hvt))
        (A.point (H.activeStage (lift_restricted_time H a v))
          (H.activeStage_mono (by exact hsv)) (H.activeStage_mono (by exact hvt))) :=
      trace_point_heq_of_index_eq A (H.restrict_activeStage a v)
        (by rw [H.restrict_activeStage a v]; exact H.activeStage_mono (by exact hsv))
        (by rw [H.restrict_activeStage a v]; exact H.activeStage_mono (by exact hvt))
        (H.activeStage_mono (by exact hsv)) (H.activeStage_mono (by exact hvt))
    have hm := curvature_sq_eq_of_metric_heq (H.restrict_stageAt a v)
      ((H.restrict a).stageMetric ((H.restrict a).activeStage v) v)
      (H.stageMetric (H.activeStage (lift_restricted_time H a v)) v)
      (H.restrict_sliceMetric a v) hp
    change r ^ 4 * normSq0S ((H.restrict a).stageMetric ((H.restrict a).activeStage v) v)
      (B.point ((H.restrict a).activeStage v)
        ((H.restrict a).activeStage_mono hsv) ((H.restrict a).activeStage_mono hvt)) 4
      (metricRm04At ((H.restrict a).stageMetric ((H.restrict a).activeStage v) v)
        (B.point ((H.restrict a).activeStage v)
          ((H.restrict a).activeStage_mono hsv) ((H.restrict a).activeStage_mono hvt))) ≤ 1
    rw [hm]
    exact hA.1 (lift_restricted_time H a v) hsv hvt
  · intro i hf hl
    have hs : cast ((H.restrict a).activeStage s) =
        H.activeStage (lift_restricted_time H a s) := H.restrict_activeStage a s
    have ht : cast ((H.restrict a).activeStage t) =
        H.activeStage (lift_restricted_time H a t) := H.restrict_activeStage a t
    have hf' : H.activeStage (lift_restricted_time H a s) ≤ cast i.castSucc := by
      rw [← hs]
      exact hf
    have hl' : cast i.succ ≤ H.activeStage (lift_restricted_time H a t) := by
      rw [← ht]
      exact hl
    exact hA.2 (Fin.castLE (Nat.le_of_lt_succ (H.activeStage a).isLt) i) hf' hl'

private theorem restricted_controlled_ball (H : ObservedHistory.{u})
    (a : Icc (0 : ℝ) H.horizon) (t : Icc (0 : ℝ) (H.restrict a).horizon)
    (p : ((H.restrict a).stageAt t).Carrier)
    (p' : (H.stageAt (lift_restricted_time H a t)).Carrier) (hp : HEq p p')
    {r : ℝ} (hball : H.isParabolicallyRmControlledBall (lift_restricted_time H a t) p' r) :
    (H.restrict a).isParabolicallyRmControlledBall t p r := by
  obtain ⟨hr, s, hst, hleft, htraces⟩ := hball
  let s' : Icc (0 : ℝ) (H.restrict a).horizon :=
    ⟨s.1, s.2.1, hst.trans t.2.2⟩
  have hs't : s' ≤ t := hst
  refine ⟨hr, s', hs't, hleft, ?_⟩
  intro x hx
  let x' := cast_point (H.restrict_stageAt a t) x
  have hxx' : HEq x x' := (cast_point_heq (H.restrict_stageAt a t) x).symm
  have hx' : x' ∈ riemannianBallOf
      (H.stageMetric (H.activeStage (lift_restricted_time H a t)) t) p' r :=
    (ball_mem_iff_of_metric_heq (H.restrict_stageAt a t)
      ((H.restrict a).stageMetric ((H.restrict a).activeStage t) t)
      (H.stageMetric (H.activeStage (lift_restricted_time H a t)) t)
      (H.restrict_sliceMetric a t) hp hxx' r).mp hx
  obtain ⟨A, hA⟩ := htraces x' hx'
  exact ⟨restrict_trace H a s' t hs't hxx' A,
    restrict_trace_controlled H a s' t hs't hxx' A hA⟩

namespace RetainedCoreHistory

/-- Noncollapse on an actual prefix controls all the same earlier balls in an
extension. Restriction retains both active-stage and crossed-terminal curvature
control, including observations at surgery times. -/
theorem noncollapsedBefore_of_isPrefixOf
    {H J : RetainedCoreHistory.{u}} (hp : H.toHistory.IsPrefixOf J.toHistory)
    {κ ρ t₀ : ℝ} (ht : t₀ ≤ H.horizon) (hnc : H.NoncollapsedBefore κ ρ t₀) :
    J.NoncollapsedBefore κ ρ t₀ := by
  let a : Icc (0 : ℝ) J.horizon := ⟨H.horizon, H.horizon_nonneg, hp.horizon_le⟩
  let R := J.restrict a
  have hncR : R.NoncollapsedBefore κ ρ t₀ :=
    (noncollapsedBefore_iff_of_samePresentation (H := R) (K := H)
      hp.presentation κ ρ t₀).mpr hnc
  intro t p r htt hr hball
  let tR : Icc (0 : ℝ) R.horizon := ⟨t.1, t.2.1, htt.trans ht⟩
  have hstage : (R.toHistory.stageAt tR) = J.toHistory.stageAt t :=
    J.toHistory.restrict_stageAt a tR
  let pR := cast_point hstage.symm p
  have hpR : HEq pR p := cast_point_heq hstage.symm p
  have hballR : R.toHistory.isParabolicallyRmControlledBall tR pR r :=
    restricted_controlled_ball J.toHistory a tR pR p hpR hball
  have hv := hncR tR pR r htt hr hballR
  exact hv.trans_eq (ball_volume_eq_of_metric_heq hstage
    (R.toHistory.stageMetric (R.toHistory.activeStage tR) tR)
    (J.toHistory.stageMetric (J.toHistory.activeStage t) t)
    (J.toHistory.restrict_sliceMetric a tR) hpR r)

end RetainedCoreHistory
end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
