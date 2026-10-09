import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.External.StrongChainAffineC12X

/-!
# The extended old native inside the new full history (C12X, S16 G4: join affine prefix)

In a prepared successor step (`Surgery/History/PreparedSpatialStep`, data of
`exists_prepared_two_overlap_extension_with_closed_seam…`): the old native `K` sits in the old
full history `H` (`AL : AffineEventPrefix K H c offset`), the new native piece `N` is appended to
`H` and to `K` (`AJ : AffineEventPrefix N J b H.eventCount`, `AK : AffineEventPrefix N Kp a
K.eventCount`), with structural prefixes `IH : RawInitialPrefix H J`, `IK : RawInitialPrefix K Kp`
and `b = a + c`. Then the extended old native `Kp` (astra `Kplus`, retention `oldNative`) is an
affine tail of `J` with the old shift and offset:

`affineEventPrefix_join_C12X : AffineEventPrefix Kp J c offset (Fin.last Kp.eventCount)`.

Together with `AffineEventPrefix.historyStrongNeckFull_affine_C12X` (TC) this carries the
`strongControl` output on `Kp` to the new full history (producer spec v2 §3.5, new window).
Events of the appended piece are translated twice (`a`, then `c`); `s16d_translate_translate`
identifies this with one translation by `a + c` (`oldTerminal` is determined by its values).
-/

set_option autoImplicit false

noncomputable section

open Set TopologicalSpace
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
open scoped Manifold ContDiff

namespace GC.GeneralFlow

universe u

/-- Two incoming slabs with the same metric family are `HEq` across equal endpoints. -/
theorem s16d_incomingSlab_heq {P : OrientedThreeStage.{u}} {a e a' e' : ℝ} (ha : a = a')
    (he : e = e') (G : P.IncomingSlab a e) (G' : P.IncomingSlab a' e')
    (hm : ∀ t, G.flow.base.metric t = G'.flow.base.metric t) : HEq G G' := by
  subst ha he
  rcases G with ⟨lt, ⟨⟨m⟩⟩, eq, sm⟩
  rcases G' with ⟨lt', ⟨⟨m'⟩⟩, eq', sm'⟩
  obtain rfl : m = m' := funext hm
  rfl

/-- Two retained events with the same discrete data, incoming slab, terminal metric, output
metric and old output map are `HEq` (the old terminal map is determined by its values). -/
theorem s16d_retainedEvent_heq {P Q : OrientedThreeStage.{u}} {a s a' s' : ℝ} (ha : a = a')
    (hs : s = s') {E : RetainedCoreEvent P Q a s} {E' : RetainedCoreEvent P Q a' s'}
    (hd : E.discarded = E'.discarded) (hc : E.capped = E'.capped)
    (htr : HEq E.transition E'.transition) (hin : HEq E.incoming E'.incoming)
    (hterm : HEq E.terminal.metric E'.terminal.metric) (hout : E.outputMetric = E'.outputMetric)
    (hoo : HEq E.oldOutput E'.oldOutput) : HEq E E' := by
  subst ha hs
  rcases E with ⟨d, cp, tr, inc, ⟨tm, tconv⟩, out, oT, hoT, oO, hoO, hom, hev⟩
  rcases E' with ⟨d', cp', tr', inc', ⟨tm', tconv'⟩, out', oT', hoT', oO', hoO', hom', hev'⟩
  dsimp only at hd hc htr hin hterm hout hoo
  subst hd hc
  cases eq_of_heq htr
  cases eq_of_heq hin
  cases eq_of_heq hterm
  subst hout
  cases eq_of_heq hoo
  obtain rfl : oT = oT' := ContinuousMap.ext fun x => Subtype.ext ((hoT x).trans (hoT' x).symm)
  rfl

/-- Translating by `a` and then by `c` is translating by `a + c`. -/
theorem s16d_translate_translate {P Q : OrientedThreeStage.{u}} {a₀ s₀ : ℝ}
    (E : RetainedCoreEvent P Q a₀ s₀) (a c : ℝ) :
    HEq (translate_retained_event (translate_retained_event E a) c)
      (translate_retained_event E (a + c)) := by
  refine s16d_retainedEvent_heq (add_assoc a₀ a c) (add_assoc s₀ a c) rfl rfl HEq.rfl
    (s16d_incomingSlab_heq (add_assoc a₀ a c) (add_assoc s₀ a c) _ _ fun t => ?_) ?_ rfl HEq.rfl
  · change E.incoming.flow.base.metric (t - c - a) = E.incoming.flow.base.metric (t - (a + c))
    congr 1
    ring
  · exact (s16d_rec_heq (translated_terminal_open (E.incoming.timeTranslate a) c).symm
      (translate_terminal_metric E.terminal a).metric).trans
      ((s16d_rec_heq (translated_terminal_open E.incoming a).symm E.terminal.metric).trans
        (s16d_rec_heq (translated_terminal_open E.incoming (a + c)).symm
          E.terminal.metric).symm)

/-- Translation respects `HEq` of events (with matching stages and times). -/
theorem s16d_translate_congr {P Q P' Q' : OrientedThreeStage.{u}} {a s a' s' : ℝ}
    {E : RetainedCoreEvent P Q a s} {E' : RetainedCoreEvent P' Q' a' s'} (hP : P' = P)
    (hQ : Q' = Q) (ha : a' = a) (hs : s' = s) (hE : HEq E' E) (c : ℝ) :
    HEq (translate_retained_event E' c) (translate_retained_event E c) := by
  subst hP hQ ha hs
  cases eq_of_heq hE
  rfl

/-- The initial metric at the start of an event is carried by a structural prefix. -/
theorem s16d_rawPrefix_initial_heq {X Y : RetainedCoreHistory.{u}} (I : RawInitialPrefix X Y)
    (i : Fin X.eventCount) :
    HEq (Y.initialMetric (i.castSucc.castLE (Nat.succ_le_succ I.count_le)))
      (X.initialMetric i.castSucc) := by
  have key : ∀ {P Q P' Q' : OrientedThreeStage.{u}} {a s a' s' : ℝ}
      {E : RetainedCoreEvent P Q a s} {E' : RetainedCoreEvent P' Q' a' s'}, P' = P → Q' = Q →
      a' = a → s' = s → HEq E' E →
      HEq (E'.incoming.flow.base.metric a') (E.incoming.flow.base.metric a) := by
    intro P Q P' Q' a s a' s' E E' hP hQ ha hs hE
    subst hP hQ ha hs
    cases eq_of_heq hE
    rfl
  exact (heq_of_eq (Y.event_initial (i.castLE I.count_le))).symm.trans
    ((key (I.stage_eq i.castSucc) (I.stage_eq i.succ) (I.time_eq i.castSucc) (I.time_eq i.succ)
      (I.event_heq i)).trans (heq_of_eq (X.event_initial i)))

/-- **Join**：the extended old native `Kp` is an affine tail of the new full history `J`. -/
theorem affineEventPrefix_join_C12X {K H N Kp J : RetainedCoreHistory.{u}} {c a b : ℝ}
    {offset : ℕ} (AL : AffineEventPrefix K H c offset (Fin.last K.eventCount))
    (IH : RawInitialPrefix H J) (AJ : AffineEventPrefix N J b H.eventCount (Fin.last N.eventCount))
    (IK : RawInitialPrefix K Kp)
    (AK : AffineEventPrefix N Kp a K.eventCount (Fin.last N.eventCount)) (hb : b = a + c) :
    AffineEventPrefix Kp J c offset (Fin.last Kp.eventCount) := by
  subst hb
  have hH : H.eventCount = offset + K.eventCount := AL.count_eq
  have hJ : J.eventCount = H.eventCount + N.eventCount := AJ.count_eq
  have hKp : Kp.eventCount = K.eventCount + N.eventCount := AK.count_eq
  refine
    { count_eq := by change J.eventCount = offset + Kp.eventCount; omega
      time_eq := fun j => ?_
      stage_eq := fun j => ?_
      initialMetric_heq := fun j => ?_
      event_heq := fun j => ?_ }
  · have hj : j.val ≤ Kp.eventCount := Nat.le_of_lt_succ j.isLt
    by_cases hA : j.val ≤ K.eventCount
    · exact (IH.time_eq ⟨offset + j.val, by omega⟩).trans ((AL.time_eq ⟨j.val, by
        change j.val < K.eventCount + 1; omega⟩).trans
        (congrArg (· + c) (IK.time_eq ⟨j.val, by omega⟩).symm))
    · have e1 : (⟨offset + j.val, by omega⟩ : Fin (J.eventCount + 1)) =
          ⟨H.eventCount + (j.val - K.eventCount), by omega⟩ := Fin.ext (by
        change offset + j.val = H.eventCount + (j.val - K.eventCount); omega)
      have e2 : (j.castLE (Nat.succ_le_succ (Nat.le_of_eq rfl)) : Fin (Kp.eventCount + 1)) =
          ⟨K.eventCount + (j.val - K.eventCount), by omega⟩ := Fin.ext (by
        change j.val = K.eventCount + (j.val - K.eventCount); omega)
      have h1 := AJ.time_eq ⟨j.val - K.eventCount, by change _ < N.eventCount + 1; omega⟩
      have h2 := AK.time_eq ⟨j.val - K.eventCount, by change _ < N.eventCount + 1; omega⟩
      rw [congrArg J.time e1, congrArg Kp.time e2]
      change J.time ⟨H.eventCount + (j.val - K.eventCount), _⟩ =
        Kp.time ⟨K.eventCount + (j.val - K.eventCount), _⟩ + c
      rw [h1, h2]
      ring
  · have hj : j.val ≤ Kp.eventCount := Nat.le_of_lt_succ j.isLt
    by_cases hA : j.val ≤ K.eventCount
    · exact (IH.stage_eq ⟨offset + j.val, by omega⟩).trans ((AL.stage_eq ⟨j.val, by
        change j.val < K.eventCount + 1; omega⟩).trans (IK.stage_eq ⟨j.val, by omega⟩).symm)
    · have e1 : (⟨offset + j.val, by omega⟩ : Fin (J.eventCount + 1)) =
          ⟨H.eventCount + (j.val - K.eventCount), by omega⟩ := Fin.ext (by
        change offset + j.val = H.eventCount + (j.val - K.eventCount); omega)
      have e2 : (j.castLE (Nat.succ_le_succ (Nat.le_of_eq rfl)) : Fin (Kp.eventCount + 1)) =
          ⟨K.eventCount + (j.val - K.eventCount), by omega⟩ := Fin.ext (by
        change j.val = K.eventCount + (j.val - K.eventCount); omega)
      exact (congrArg J.stage e1).trans ((AJ.stage_eq ⟨j.val - K.eventCount, by
        change _ < N.eventCount + 1; omega⟩).trans ((AK.stage_eq ⟨j.val - K.eventCount, by
        change _ < N.eventCount + 1; omega⟩).symm.trans (congrArg Kp.stage e2).symm))
  · have hj : j.val ≤ Kp.eventCount := Nat.le_of_lt_succ j.isLt
    by_cases hA : j.val < K.eventCount
    · exact (s16d_rawPrefix_initial_heq IH ⟨offset + j.val, by omega⟩).trans
        ((AL.initialMetric_heq ⟨j.val, by change j.val < K.eventCount + 1; omega⟩).trans
          (s16d_rawPrefix_initial_heq IK ⟨j.val, hA⟩).symm)
    · have e1 : (⟨offset + j.val, by omega⟩ : Fin (J.eventCount + 1)) =
          ⟨H.eventCount + (j.val - K.eventCount), by omega⟩ := Fin.ext (by
        change offset + j.val = H.eventCount + (j.val - K.eventCount); omega)
      have e2 : (j.castLE (Nat.succ_le_succ (Nat.le_of_eq rfl)) : Fin (Kp.eventCount + 1)) =
          ⟨K.eventCount + (j.val - K.eventCount), by omega⟩ := Fin.ext (by
        change j.val = K.eventCount + (j.val - K.eventCount); omega)
      exact (congr_arg_heq J.initialMetric e1).trans
        ((AJ.initialMetric_heq ⟨j.val - K.eventCount, by change _ < N.eventCount + 1; omega⟩).trans
          ((AK.initialMetric_heq ⟨j.val - K.eventCount, by
            change _ < N.eventCount + 1; omega⟩).symm.trans
            (congr_arg_heq Kp.initialMetric e2).symm))
  · have hj : j.val < Kp.eventCount := j.isLt
    by_cases hA : j.val < K.eventCount
    · let i : Fin K.eventCount := ⟨j.val, hA⟩
      exact (IH.event_heq ⟨offset + j.val, by omega⟩).trans
        ((AL.event_heq i).trans (s16d_translate_congr (IK.stage_eq i.castSucc)
          (IK.stage_eq i.succ) (IK.time_eq i.castSucc) (IK.time_eq i.succ)
          (IK.event_heq i) c).symm)
    · let jN : Fin (Fin.last N.eventCount).val := ⟨j.val - K.eventCount, by
        change _ < N.eventCount; omega⟩
      have e1 : (⟨offset + j.val, by omega⟩ : Fin J.eventCount) =
          ⟨H.eventCount + jN.val, by omega⟩ := Fin.ext (by
        change offset + j.val = H.eventCount + (j.val - K.eventCount); omega)
      have e2 : (j.castLE (Nat.le_of_eq rfl) : Fin Kp.eventCount) =
          ⟨K.eventCount + jN.val, by omega⟩ := Fin.ext (by
        change j.val = K.eventCount + (j.val - K.eventCount); omega)
      have hK := s16d_translate_congr (AK.stage_eq jN.castSucc) (AK.stage_eq jN.succ)
        (AK.time_eq jN.castSucc) (AK.time_eq jN.succ) (AK.event_heq jN) c
      exact (congr_arg_heq J.coreEvent e1).trans ((AJ.event_heq jN).trans
        ((s16d_translate_translate (N.coreEvent (jN.castLE (Nat.le_of_eq rfl))) a c).symm.trans
          (hK.symm.trans (congr_arg_heq (fun i => translate_retained_event (Kp.coreEvent i) c)
            e2).symm)))

end GC.GeneralFlow

end
