import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.External.RecordHypFarC12X
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.History.CutoffRecordConcatenation

/-!
# Deep backward necks under affine event prefixes (C12X, S16 round 3, O-C12X-S16K G2a)

Joined native histories `J` carry the events of a new native history `K` translated by the join
time `c ≥ 0` (`AffineEventPrefix K J c offset last`, SH/CutoffRecordConcatenation); their
records' backward necks are `AffineEventPrefix.translateBackwardNeck`.  This file gives the deep
analogue `AffineEventPrefix.translateBackwardNeckDeep_C12X` (depth factor `θ`; its depth-one part
is `translateBackwardNeck`).  The deep window stays in the translated tail because
`0 ≤ time i.succ - θ r²` (`deep_left_nonneg`).
-/

set_option autoImplicit false

noncomputable section

open Set Manifold DifferentialGeometry
open DifferentialGeometry.Geometry.Neck DifferentialGeometry.Geometry.Curvature
open scoped Manifold ContDiff

namespace GC.GeneralFlow

open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

universe u

/-- As in SH/CutoffRecordConcatenation: unfold `Fin.last` / `Fin.succ` values before `omega`. -/
local macro "omega_fin" : tactic =>
  `(tactic| ((try simp only [Fin.val_last, Fin.val_succ, Fin.val_castSucc] at *) <;> omega))

open private castStageMap castStageMap_smooth from
  DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.CutoffRecordEventExtension

open private translated_crossing_transport translated_metric_transport from
  DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.History.CutoffRecordConcatenation

/-- Deep analogue of `AffineEventPrefix.translateBackwardNeck`. -/
def AffineEventPrefix.translateBackwardNeckDeep_C12X
    {K J : RetainedCoreHistory.{u}} {c : ℝ} {offset : ℕ}
    (A : AffineEventPrefix K J c offset (Fin.last K.eventCount)) (hc : 0 ≤ c)
    {i : Fin K.eventCount} {δ r θ : ℝ} {k : ℕ}
    {N : NormalizedNeck (K.coreEvent i).terminal.metric δ k}
    {N' : NormalizedNeck (J.coreEvent (A.eventIndex i)).terminal.metric δ k}
    (hneck : HEq N' N) (D : IncomingBackwardNeckDeep_C12X K.toHistory i N r θ) :
    IncomingBackwardNeckDeep_C12X J.toHistory (A.eventIndex i) N' r θ := by
  have hcount := A.count_eq
  have htime (j : Fin K.eventCount) :
      J.time (A.eventIndex j).succ = K.time j.succ + c := A.time_eq j.succ
  have hjoin : J.time ⟨offset, by omega⟩ = c := by
    simpa only [Fin.val_zero, Nat.add_zero, Fin.castLE_zero, K.time_zero, zero_add]
      using A.time_eq 0
  have hleft : c ≤ J.time (A.eventIndex i).succ - θ * r ^ 2 := by
    rw [htime]
    linarith [D.deep_left_nonneg]
  have after (j : Fin J.eventCount)
      (ha : J.time (A.eventIndex i).succ - θ * r ^ 2 < J.time j.succ) : offset ≤ j.val := by
    by_contra h
    have hj : j.succ ≤ (⟨offset, by omega⟩ : Fin (J.eventCount + 1)) := by
      change j.val + 1 ≤ offset
      omega
    have hb := J.time_strictMono.monotone hj
    rw [hjoin] at hb
    linarith
  let old (j : Fin J.eventCount) (hj : j.val ≤ (A.eventIndex i).val)
      (ha : J.time (A.eventIndex i).succ - θ * r ^ 2 < J.time j.succ) : Fin K.eventCount :=
    ⟨j.val - offset, by have := after j ha; change j.val ≤ offset + i.val at hj; omega⟩
  have index_old (j : Fin J.eventCount) (hj : j.val ≤ (A.eventIndex i).val)
      (ha : J.time (A.eventIndex i).succ - θ * r ^ 2 < J.time j.succ) :
      A.eventIndex (old j hj ha) = j := by
    apply Fin.ext
    have := after j ha
    simp only [AffineEventPrefix.eventIndex, old, Fin.val_mk]
    omega
  have old_le (j : Fin J.eventCount) (hj : j.val ≤ (A.eventIndex i).val)
      (ha : J.time (A.eventIndex i).succ - θ * r ^ 2 < J.time j.succ) :
      (old j hj ha).val ≤ i.val := by
    have := after j ha
    change j.val ≤ offset + i.val at hj
    change j.val - offset ≤ i.val
    omega
  have old_time (j : Fin J.eventCount) (hj : j.val ≤ (A.eventIndex i).val)
      (ha : J.time (A.eventIndex i).succ - θ * r ^ 2 < J.time j.succ) :
      J.time j.succ = K.time (old j hj ha).succ + c := by
    have h := htime (old j hj ha)
    rw [index_old j hj ha] at h
    exact h
  have old_left (j : Fin J.eventCount) (hj : j.val ≤ (A.eventIndex i).val)
      (ha : J.time (A.eventIndex i).succ - θ * r ^ 2 < J.time j.succ) :
      K.time i.succ - θ * r ^ 2 < K.time (old j hj ha).succ := by
    have h1 := old_time j hj ha
    have h2 := htime i
    linarith
  let deepChart (j : Fin J.eventCount) (hj : j.val ≤ (A.eventIndex i).val)
      (ha : J.time (A.eventIndex i).succ - θ * r ^ 2 < J.time j.succ) :
      C(neckBuffer δ, (J.stage j.castSucc).Carrier) :=
    castStageMap
      ((congrArg (fun l : Fin J.eventCount => J.stage l.castSucc)
        (index_old j hj ha)).symm.trans (A.stage_eq (old j hj ha).castSucc)).symm
      (D.deepChart (old j hj ha) (old_le j hj ha) (old_left j hj ha))
  refine {
    toIncomingBackwardNeck := A.translateBackwardNeck hc hneck D.toIncomingBackwardNeck
    one_le_depth := D.one_le_depth
    deep_left_nonneg := hc.trans hleft
    deepChart := deepChart
    deepChart_smooth := fun j hj ha => castStageMap_smooth _ _ (D.deepChart_smooth _ _ _)
    deepChart_eq := ?_
    deep_crossing := ?_
    deep_metric_on_slab := ?_
    deepJet := D.deepJet
    deepJet_eq := D.deepJet_eq
    deep_closeness := D.deep_closeness
    deep_metric_smooth := D.deep_metric_smooth }
  · intro j hj ha ha'
    exact congrArg (castStageMap _) (D.deepChart_eq _ _ _ _)
  · intro j hj
    dsimp only
    intro ha hn
    let j₀ := old j hj.le ha
    let next : Fin J.eventCount := ⟨j.val + 1, by
      have h1 : j.val < (A.eventIndex i).val := hj
      have h2 := (A.eventIndex i).isLt
      omega⟩
    let next₀ : Fin K.eventCount := ⟨j₀.val + 1, by
      have := after j ha
      change j.val < offset + i.val at hj
      dsimp [j₀, old]
      omega⟩
    have hj₀ : j₀.val < i.val := by
      have := after j ha
      change j.val < offset + i.val at hj
      dsimp [j₀, old]
      omega
    have hn₀ : old next (by
        have h1 : j.val < (A.eventIndex i).val := hj
        have h2 : (A.eventIndex i).val = offset + i.val := rfl
        change j.val + 1 ≤ offset + i.val; omega) hn = next₀ := by
      apply Fin.ext
      have := after j ha
      dsimp [old, next, next₀, j₀]
      omega
    have heqj := index_old j hj.le ha
    have heqn : A.eventIndex next₀ = next := by
      rw [← hn₀]
      exact index_old next (by
        have h1 : j.val < (A.eventIndex i).val := hj
        change j.val + 1 ≤ (A.eventIndex i).val
        omega) hn
    have hstagej : J.stage j.castSucc = K.stage j₀.castSucc :=
      (congrArg (fun l : Fin J.eventCount => J.stage l.castSucc) heqj).symm.trans
        (A.stage_eq j₀.castSucc)
    have hstagen : J.stage next.castSucc = K.stage next₀.castSucc :=
      (congrArg (fun l : Fin J.eventCount => J.stage l.castSucc) heqn).symm.trans
        (A.stage_eq next₀.castSucc)
    have hev : HEq (J.coreEvent j) (translate_retained_event (K.coreEvent j₀) c) :=
      (heq_apply_of_eq J.coreEvent heqj).symm.trans (A.event_heq j₀)
    have hstart : J.time j.castSucc = K.time j₀.castSucc + c :=
      (congrArg (fun l : Fin J.eventCount => J.time l.castSucc) heqj).symm.trans
        (A.time_eq j₀.castSucc)
    have hend : J.time j.succ = K.time j₀.succ + c := old_time j hj.le ha
    have hnextleft : K.time i.succ - θ * r ^ 2 < K.time next₀.succ := by
      have hh := old_left next (by
        have h1 : j.val < (A.eventIndex i).val := hj
        have h2 : (A.eventIndex i).val = offset + i.val := rfl
        change j.val + 1 ≤ offset + i.val; omega) hn
      rwa [hn₀] at hh
    change ∀ x, (J.toHistory.event j).RegularCrossing (deepChart j hj.le ha x)
      (deepChart next (by
        have h1 : j.val < (A.eventIndex i).val := hj
        have h2 : (A.eventIndex i).val = offset + i.val := rfl
        change j.val + 1 ≤ offset + i.val; omega) hn x)
    have hnle : next.val ≤ (A.eventIndex i).val := by
      have h1 : j.val < (A.eventIndex i).val := hj
      change j.val + 1 ≤ (A.eventIndex i).val
      omega
    have key : ∀ (o : Fin K.eventCount) (ho : next₀ = o) (h1 : o.val ≤ i.val)
        (h2 : K.time i.succ - θ * r ^ 2 < K.time o.succ)
        (hst : J.stage next.castSucc = K.stage o.castSucc),
        ∀ x, (J.toHistory.event j).RegularCrossing
          (castStageMap hstagej.symm
            (D.deepChart j₀ (old_le j hj.le ha) (old_left j hj.le ha)) x)
          (castStageMap hst.symm (D.deepChart o h1 h2) x) := by
      intro o ho h1 h2 hst
      subst ho
      exact translated_crossing_transport (K.coreEvent j₀) c
        hstagej hstagen hstart hend hev
        (D.deepChart j₀ hj₀.le (old_left j hj.le ha))
        (D.deepChart next₀ h1 h2)
        (D.deep_crossing j₀ hj₀ (old_left j hj.le ha) hnextleft)
    dsimp only [deepChart]
    exact key _ hn₀.symm (old_le next hnle hn) (old_left next hnle hn)
      ((congrArg (fun l : Fin J.eventCount => J.stage l.castSucc)
        (index_old next hnle hn)).symm.trans (A.stage_eq (old next hnle hn).castSucc))
  · intro j hj ha v hv hlo hhi x V W
    let j₀ := old j hj ha
    have hindex := index_old j hj ha
    have hstage : J.stage j.castSucc = K.stage j₀.castSucc :=
      (congrArg (fun l : Fin J.eventCount => J.stage l.castSucc) hindex).symm.trans
        (A.stage_eq j₀.castSucc)
    have hstage' : J.stage j.succ = K.stage j₀.succ :=
      (congrArg (fun l : Fin J.eventCount => J.stage l.succ) hindex).symm.trans
        (A.stage_eq j₀.succ)
    have hstart : J.time j.castSucc = K.time j₀.castSucc + c :=
      (congrArg (fun l : Fin J.eventCount => J.time l.castSucc) hindex).symm.trans
        (A.time_eq j₀.castSucc)
    have hend : J.time j.succ = K.time j₀.succ + c := old_time j hj ha
    have hev : HEq (J.coreEvent j) (translate_retained_event (K.coreEvent j₀) c) :=
      (heq_apply_of_eq J.coreEvent hindex).symm.trans (A.event_heq j₀)
    have hlo₀ : K.time j₀.castSucc ≤ K.time i.succ + r ^ 2 * v := by
      change J.time j.castSucc ≤ J.time (A.eventIndex i).succ + r ^ 2 * v at hlo
      rw [hstart, htime] at hlo
      linarith
    have hhi₀ : K.time i.succ + r ^ 2 * v < K.time j₀.succ := by
      change J.time (A.eventIndex i).succ + r ^ 2 * v < J.time j.succ at hhi
      rw [hend, htime] at hhi
      linarith
    have hmetric := translated_metric_transport (K.coreEvent j₀) c
      hstage hstage' hstart hend hev
      (D.deepChart j₀ (old_le j hj ha) (old_left j hj ha))
      (J.time (A.eventIndex i).succ + r ^ 2 * v) x V W
    rw [show J.time (A.eventIndex i).succ + r ^ 2 * v - c =
      K.time i.succ + r ^ 2 * v by rw [htime]; ring] at hmetric
    exact (D.deep_metric_on_slab j₀ (old_le j hj ha) (old_left j hj ha)
      v hv hlo₀ hhi₀ x V W).trans (congrArg ((r ^ 2)⁻¹ * ·) hmetric.symm)

end GC.GeneralFlow

end
