import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.External.DeepRecordC12X
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.External.DeepTranslateC12X
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.CutoffRecordModelRestriction.Basic

/-!
# Deep cut necks of the joined record family (C12X, S16 round 3 G2c, O-C12X-S16L G4)

Lead ruling (S16 round 3): the deep backward necks of the *old* records come from the previous
state's invariant `nativeRecordHyp` and are moved to the current history by transports; the
Poincaré layer only certifies the record of the new event.  At the actual-history join
(NC/CommonScaffoldExtensionPortC11P, history `J` = old history `H` followed by the affinely
translated tower `K`) the joined records are identified with the old records (`castLE`) and with
the tower records (`A.eventIndex`) only through `HEq` of their fields.  This file turns exactly
those `HEq` facts into deep necks:

* `GeometricCutoffRecord.deepNecks_restrictModelWindow_C12X`: restricting the static model window
  keeps deep necks (necks and radii are untouched);
* `GeometricCutoffRecord.deepNecks_rawInitialPrefix_C12X`: old part, along a raw initial prefix
  (`IncomingBackwardNeckDeep_C12X.ofInitialEmbedding_C12X`);
* `GeometricCutoffRecord.deepNecks_affineEventPrefix_C12X`: translated part, along an affine event
  prefix (`AffineEventPrefix.translateBackwardNeckDeep_C12X`, S16K G2a), through the translated
  terminal neck `translate_terminal_neck`;
* **`deepNecks_join_C12X`**: the joined family has deep necks once the old family and the tower
  family have them (the implication form of the lead ruling, Deep half).
-/

set_option autoImplicit false

noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

open GC.GeneralFlow

universe u

/-- Restricting the static model window keeps deep necks (necks and nominal radii are the same). -/
theorem GeometricCutoffRecord.deepNecks_restrictModelWindow_C12X {H : ObservedHistory.{u}}
    {i : Fin H.eventCount} {p : CutoffParameters} {D ε θ : ℝ} {m : ℕ}
    (R : GeometricCutoffRecord H i p) (hR : ∀ b, (R.static b).hasCanonicalWindow)
    (hD : 0 < D) (hDp : D ≤ p.modelRadius) (hm : m ≤ p.modelOrder)
    (hε : p.modelAccuracy ≤ ε) (h : R.DeepNecks_C12X θ) :
    (R.restrictModelWindow hR hD hDp hm hε).DeepNecks_C12X θ :=
  h

private theorem metric_event_heq_C12X
    {P Q P' Q' : OrientedThreeStage.{u}} {a s a' s' : ℝ}
    (hP : P = P') (hQ : Q = Q') (ha : a = a') (hs : s = s')
    {E : RetainedCoreEvent P Q a s} {E' : RetainedCoreEvent P' Q' a' s'}
    (hE : HEq E E') : HEq E.toMetricCutCapEvent E'.toMetricCutCapEvent := by
  cases hP
  cases hQ
  cases ha
  cases hs
  cases eq_of_heq hE
  exact HEq.rfl

private theorem deep_join_family_aux_C12X
    {P Q P' Q' : OrientedThreeStage.{u}} {a s a' s' : ℝ}
    {E : MetricCutCapEvent P Q a s} {E' : MetricCutCapEvent P' Q' a' s'}
    (hP : P' = P) (hQ : Q' = Q) (ha : a' = a) (hs : s' = s) (hE : HEq E' E)
    {d : E.transition.trace.tubes.Index → ℝ} {o : E.transition.trace.tubes.Index → ℕ}
    {d' : E'.transition.trace.tubes.Index → ℝ} {o' : E'.transition.trace.tubes.Index → ℕ}
    (nom : Nonempty E.transition.trace.tubes.Index → ℝ)
    (nom' : Nonempty E'.transition.trace.tubes.Index → ℝ)
    (F : ∀ α, NormalizedNeck E.terminal.metric (d α) (o α))
    (F' : ∀ α, NormalizedNeck E'.terminal.metric (d' α) (o' α))
    (hnom : HEq nom' nom) (hd : HEq d' d) (ho : HEq o' o) (hF : HEq F' F)
    (M : ∀ {δ : ℝ} {k : ℕ}, NormalizedNeck E.terminal.metric δ k → ℝ → Prop)
    (M' : ∀ {δ : ℝ} {k : ℕ}, NormalizedNeck E'.terminal.metric δ k → ℝ → Prop)
    (T : ∀ {δ : ℝ} {k : ℕ} (N : NormalizedNeck E.terminal.metric δ k)
      (N' : NormalizedNeck E'.terminal.metric δ k) (r : ℝ), HEq N' N → M N r → M' N' r)
    (h : ∀ α, M (F α) (nom ⟨α⟩)) : ∀ α', M' (F' α') (nom' ⟨α'⟩) := by
  cases hP
  cases hQ
  cases ha
  cases hs
  cases eq_of_heq hE
  cases eq_of_heq hd
  cases eq_of_heq ho
  cases eq_of_heq hF
  cases eq_of_heq hnom
  exact fun α => T (F α) (F α) _ HEq.rfl (h α)

/-- Old part of a join: a record of `H` and the record of the same event of `J` (raw initial
prefix, fields identified by `HEq`) have the same deep necks. -/
theorem GeometricCutoffRecord.deepNecks_rawInitialPrefix_C12X {H J : RetainedCoreHistory.{u}}
    (I : RawInitialPrefix H J) {θ : ℝ} {p p' : CutoffParameters} (i : Fin H.eventCount)
    (old : GeometricCutoffRecord H.toHistory i p)
    (R : GeometricCutoffRecord J.toHistory (i.castLE I.count_le) p')
    (hnom : HEq R.nominalRadius old.nominalRadius) (hd : HEq R.delta old.delta)
    (ho : HEq R.order old.order) (hN : HEq R.neck old.neck)
    (h : old.DeepNecks_C12X θ) : R.DeepNecks_C12X θ := by
  have hevent (j : Fin H.eventCount) :
      HEq (J.toHistory.event (j.castLE I.count_le)) (H.toHistory.event j) :=
    metric_event_heq_C12X (I.stage_eq j.castSucc) (I.stage_eq j.succ)
      (I.time_eq j.castSucc) (I.time_eq j.succ) (I.event_heq j)
  exact deep_join_family_aux_C12X (I.stage_eq i.castSucc) (I.stage_eq i.succ)
    (I.time_eq i.castSucc) (I.time_eq i.succ) (hevent i)
    old.nominalRadius R.nominalRadius old.neck R.neck hnom hd ho hN
    (fun N r => Nonempty (IncomingBackwardNeckDeep_C12X H.toHistory i N r θ))
    (fun N' r => Nonempty (IncomingBackwardNeckDeep_C12X J.toHistory (i.castLE I.count_le) N' r θ))
    (fun _ _ _ hN' hD => hD.map (IncomingBackwardNeckDeep_C12X.ofInitialEmbedding_C12X
      (H := H.toHistory) (J := J.toHistory) I.count_le I.time_eq I.stage_eq hevent hN'))
    h

/-- Translated part of a join: a tower record and the record of the translated event of `J`
(affine event prefix, fields identified by `HEq`) have the same deep necks. -/
theorem GeometricCutoffRecord.deepNecks_affineEventPrefix_C12X {K J : RetainedCoreHistory.{u}}
    {c : ℝ} {offset : ℕ} (A : AffineEventPrefix K J c offset (Fin.last K.eventCount))
    (hc : 0 ≤ c) {θ : ℝ} {p p' : CutoffParameters} (i : Fin K.eventCount)
    (tail : GeometricCutoffRecord K.toHistory i p)
    (R : GeometricCutoffRecord J.toHistory (A.eventIndex i) p')
    (hnom : HEq R.nominalRadius tail.nominalRadius) (hd : HEq R.delta tail.delta)
    (ho : HEq R.order tail.order) (hN : HEq R.neck tail.neck)
    (h : tail.DeepNecks_C12X θ) : R.DeepNecks_C12X θ := by
  have hE : HEq (J.toHistory.event (A.eventIndex i))
      (translate_retained_event (K.coreEvent i) c).toMetricCutCapEvent :=
    metric_event_heq_C12X (A.stage_eq i.castSucc) (A.stage_eq i.succ)
      (A.time_eq i.castSucc) (A.time_eq i.succ) (A.event_heq i)
  let F : ∀ α, NormalizedNeck (translate_retained_event (K.coreEvent i) c).terminal.metric
      (tail.delta α) (tail.order α) :=
    fun α => translate_terminal_neck (K.coreEvent i) c (tail.neck α)
  have hFK : HEq F tail.neck := by
    refine Function.hfunext rfl fun α α' hα => ?_
    cases eq_of_heq hα
    exact translate_terminal_neck_heq (K.coreEvent i) c (tail.neck α)
  exact deep_join_family_aux_C12X (A.stage_eq i.castSucc) (A.stage_eq i.succ)
    (A.time_eq i.castSucc) (A.time_eq i.succ) hE
    tail.nominalRadius R.nominalRadius F R.neck hnom hd ho (hN.trans hFK.symm)
    (fun {δ} {k} N r => ∃ N₀ : NormalizedNeck (K.coreEvent i).terminal.metric δ k,
      HEq N N₀ ∧ Nonempty (IncomingBackwardNeckDeep_C12X K.toHistory i N₀ r θ))
    (fun N' r => Nonempty (IncomingBackwardNeckDeep_C12X J.toHistory (A.eventIndex i) N' r θ))
    (fun _ _ _ hN' ⟨_, h₀, hD⟩ =>
      hD.map (AffineEventPrefix.translateBackwardNeckDeep_C12X A hc (hN'.trans h₀)))
    (fun α => ⟨tail.neck α, translate_terminal_neck_heq (K.coreEvent i) c (tail.neck α), h α⟩)

/-- **Deep half of the join implication.**  The records of the joined history `J` (old history `H`
at `castLE`, translated tower `K` at `A.eventIndex`, fields identified by `HEq` as produced by the
concatenation and the common scaffold extension) have deep necks once the old records and the
tower records have them. -/
theorem deepNecks_join_C12X {H K J : RetainedCoreHistory.{u}} {c : ℝ}
    (A : AffineEventPrefix K J c H.eventCount (Fin.last K.eventCount)) (hc : 0 ≤ c)
    (I : RawInitialPrefix H J) (hn : H.eventCount ≤ J.eventCount) {θ : ℝ}
    {pH pK q : CutoffParameters}
    (old : ∀ i : Fin H.eventCount, GeometricCutoffRecord H.toHistory i pH)
    (tail : ∀ i : Fin K.eventCount, GeometricCutoffRecord K.toHistory i pK)
    (records : ∀ j : Fin J.eventCount, GeometricCutoffRecord J.toHistory j q)
    (hOld : ∀ i : Fin H.eventCount,
      HEq (records (i.castLE hn)).nominalRadius (old i).nominalRadius ∧
      HEq (records (i.castLE hn)).delta (old i).delta ∧
      HEq (records (i.castLE hn)).order (old i).order ∧
      HEq (records (i.castLE hn)).neck (old i).neck)
    (hTail : ∀ i : Fin K.eventCount,
      HEq (records (A.eventIndex i)).nominalRadius (tail i).nominalRadius ∧
      HEq (records (A.eventIndex i)).delta (tail i).delta ∧
      HEq (records (A.eventIndex i)).order (tail i).order ∧
      HEq (records (A.eventIndex i)).neck (tail i).neck)
    (hold : ∀ i, (old i).DeepNecks_C12X θ) (htail : ∀ i, (tail i).DeepNecks_C12X θ) :
    ∀ j, (records j).DeepNecks_C12X θ := by
  rintro ⟨j, hj⟩
  by_cases hjH : j < H.eventCount
  · let i : Fin H.eventCount := ⟨j, hjH⟩
    exact GeometricCutoffRecord.deepNecks_rawInitialPrefix_C12X I i (old i) (records ⟨j, hj⟩)
      (hOld i).1 (hOld i).2.1 (hOld i).2.2.1 (hOld i).2.2.2 (hold i)
  · have hcount := A.count_eq
    have hjK : j - H.eventCount < K.eventCount := by
      simp only [Fin.val_last] at hcount
      omega
    let i : Fin K.eventCount := ⟨j - H.eventCount, hjK⟩
    have hji : A.eventIndex i = ⟨j, hj⟩ := by
      apply Fin.ext
      change H.eventCount + (j - H.eventCount) = j
      omega
    rw [← hji]
    exact GeometricCutoffRecord.deepNecks_affineEventPrefix_C12X A hc i (tail i)
      (records (A.eventIndex i)) (hTail i).1 (hTail i).2.1 (hTail i).2.2.1 (hTail i).2.2.2
      (htail i)

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

end
