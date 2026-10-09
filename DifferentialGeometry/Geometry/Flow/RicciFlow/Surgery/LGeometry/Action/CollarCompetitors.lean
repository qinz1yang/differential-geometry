import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.LGeometry.Action.ClosedIntervalRegularity
import Mathlib.Algebra.BigOperators.Fin

set_option autoImplicit false

noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory

open Set Filter _root_.MeasureTheory
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.PDE.RicciFlow.Perelman
open scoped _root_.Manifold ContDiff _root_.Topology BigOperators Interval

universe u

theorem exists_three_piece_stage_curve
    (H : ObservedHistory.{u}) (j : Fin (H.eventCount + 1)) (T : ℝ)
    (alpha beta gamma : ℝ → (H.stage j).Carrier) {a b c d : ℝ}
    (hab : a ≤ b) (hbc : b ≤ c) (hcd : c ≤ d)
    (ha : Manifold.absolutelyContinuousOnInterval ThreeModel alpha a b)
    (hb : Manifold.absolutelyContinuousOnInterval ThreeModel beta b c)
    (hc : Manifold.absolutelyContinuousOnInterval ThreeModel gamma c d)
    (hia : IntervalIntegrable (H.stageRegularizedLagrangian j T alpha) volume a b)
    (hib : IntervalIntegrable (H.stageRegularizedLagrangian j T beta) volume b c)
    (hic : IntervalIntegrable (H.stageRegularizedLagrangian j T gamma) volume c d)
    (habc : alpha b = beta b) (hbcd : beta c = gamma c) :
    ∃ delta : ℝ → (H.stage j).Carrier,
      Manifold.absolutelyContinuousOnInterval ThreeModel delta a d ∧
      IntervalIntegrable (H.stageRegularizedLagrangian j T delta) volume a d ∧
      EqOn delta alpha (Icc a b) ∧ EqOn delta beta (Icc b c) ∧
      EqOn delta gamma (Icc c d) ∧
      H.stageRegularizedAction j T delta a d =
        H.stageRegularizedAction j T alpha a b +
        H.stageRegularizedAction j T beta b c + H.stageRegularizedAction j T gamma c d := by
  classical
  let eta : ℝ → (H.stage j).Carrier := (Iic b).piecewise alpha beta
  obtain ⟨hetaAC, hetaInt, hetaLeft, hetaRight, hetaAction⟩ :=
    H.stageRegularizedAction_piecewise_Iic j T hab hbc alpha beta ha hb hia hib habc
  let delta : ℝ → (H.stage j).Carrier := (Iic c).piecewise eta gamma
  obtain ⟨hdeltaAC, hdeltaInt, hdeltaLeft, hdeltaRight, hdeltaAction⟩ :=
    H.stageRegularizedAction_piecewise_Iic j T (hab.trans hbc) hcd eta gamma
      hetaAC hc hetaInt hic ((hetaRight ⟨hbc, le_rfl⟩).trans hbcd)
  refine ⟨delta, hdeltaAC, hdeltaInt, ?_, ?_, hdeltaRight, ?_⟩
  · intro r hr
    exact (hdeltaLeft ⟨hr.1, hr.2.trans hbc⟩).trans (hetaLeft hr)
  · intro r hr
    exact (hdeltaLeft ⟨hab.trans hr.1, hr.2⟩).trans (hetaRight hr)
  · exact hdeltaAction.trans (congrArg
      (fun A => A + H.stageRegularizedAction j T gamma c d) hetaAction)

theorem sum_stage_parts_eq_endpoints_add_events
    (H : ObservedHistory.{u}) (first last : Fin (H.eventCount + 1)) (hle : first ≤ last)
    (L M R : H.StageInterval first last → ℝ) :
    (∑ j : H.StageInterval first last, (L j + M j + R j)) =
      L ⟨last, hle, le_rfl⟩ + (∑ j, M j) +
      (∑ i : {i : Fin H.eventCount // first ≤ i.castSucc ∧ i.succ ≤ last},
        (R ⟨i.val.succ, i.property.1.trans i.val.castSucc_le_succ, i.property.2⟩ +
          L ⟨i.val.castSucc, i.property.1, i.val.castSucc_le_succ.trans i.property.2⟩)) +
      R ⟨first, le_rfl, hle⟩ := by
  classical
  let jf : H.StageInterval first last := ⟨first, le_rfl, hle⟩
  let jl : H.StageInterval first last := ⟨last, hle, le_rfl⟩
  let E := {i : Fin H.eventCount // first ≤ i.castSucc ∧ i.succ ≤ last}
  let eo : {j : H.StageInterval first last // j ≠ jl} ≃ E :=
    { toFun := fun j =>
        ⟨⟨j.val.val.val, by
          have hj := j.val.property.2
          have hn : j.val.val ≠ last := fun he => j.property (Subtype.ext he)
          have hl := last.isLt
          omega⟩, j.val.property.1, by
            have hj := j.val.property.2
            have hn : j.val.val ≠ last := fun he => j.property (Subtype.ext he)
            change j.val.val.val + 1 ≤ last.val
            have hneq : j.val.val.val ≠ last.val := fun he => hn (Fin.ext he)
            omega⟩
      invFun := fun i => ⟨⟨i.val.castSucc, i.property.1,
        i.val.castSucc_le_succ.trans i.property.2⟩, by
          intro he
          have hv := congrArg (fun j : H.StageInterval first last => j.val.val) he
          have hi := i.property.2
          change i.val.val + 1 ≤ last.val at hi
          change i.val.val = last.val at hv
          omega⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  let en : {j : H.StageInterval first last // j ≠ jf} ≃ E :=
    { toFun := fun j =>
        ⟨⟨j.val.val.val - 1, by
          have hj := j.val.val.isLt
          have hf := j.val.property.1
          have hn : first.val ≠ j.val.val.val := by
            intro he
            exact j.property (Subtype.ext (Fin.ext he.symm))
          omega⟩, by
            have hj := j.val.property.1
            have hn : first.val ≠ j.val.val.val := by
              intro he
              exact j.property (Subtype.ext (Fin.ext he.symm))
            change first.val ≤ j.val.val.val - 1
            omega, by
            have hj := j.val.property.2
            change j.val.val.val - 1 + 1 ≤ last.val
            have hpos : 0 < j.val.val.val := by
              have hjf := j.val.property.1
              have hn : first.val ≠ j.val.val.val := by
                intro he
                exact j.property (Subtype.ext (Fin.ext he.symm))
              omega
            omega⟩
      invFun := fun i => ⟨⟨i.val.succ,
        i.property.1.trans i.val.castSucc_le_succ, i.property.2⟩, by
          intro he
          have hv := congrArg (fun j : H.StageInterval first last => j.val.val) he
          have hi := i.property.1
          change first.val ≤ i.val.val at hi
          change i.val.val + 1 = first.val at hv
          omega⟩
      left_inv := fun j => by
        apply Subtype.ext
        apply Subtype.ext
        apply Fin.ext
        change j.val.val.val - 1 + 1 = j.val.val.val
        have hjf := j.val.property.1
        have hn : first.val ≠ j.val.val.val := by
          intro he
          exact j.property (Subtype.ext (Fin.ext he.symm))
        omega
      right_inv := fun i => by
        apply Subtype.ext
        apply Fin.ext
        change i.val.val + 1 - 1 = i.val.val
        omega }
  have hL := Fintype.sum_equiv eo (fun j => L j.val)
    (fun i => L ⟨i.val.castSucc, i.property.1, i.val.castSucc_le_succ.trans i.property.2⟩)
    (fun _ => rfl)
  have hR := Fintype.sum_equiv en (fun j => R j.val)
    (fun i => R ⟨i.val.succ, i.property.1.trans i.val.castSucc_le_succ, i.property.2⟩)
    (fun j => by
      congr 1
      apply Subtype.ext
      apply Fin.ext
      change j.val.val.val = j.val.val.val - 1 + 1
      have hjf := j.val.property.1
      have hn : first.val ≠ j.val.val.val := by
        intro he
        exact j.property (Subtype.ext (Fin.ext he.symm))
      omega)
  simp only [Finset.sum_add_distrib]
  rw [Fintype.sum_eq_add_sum_subtype_ne L jl, hL,
    Fintype.sum_eq_add_sum_subtype_ne R jf, hR]
  ring

theorem exists_stage_family_of_collar_pieces
    (H : ObservedHistory.{u}) (first last : Fin (H.eventCount + 1)) (hle : first ≤ last)
    {T v : ℝ} (hv : 0 ≤ v)
    (hupper : T ∈ Icc (H.time last) (H.stageEndTime last))
    (hpast : T - v ^ 2 ∈ H.stageDomain first) :
    let J := H.StageInterval first last;
    let E := {i : Fin H.eventCount // first ≤ i.castSucc ∧ i.succ ≤ last};
    let jo (i : E) : J := ⟨i.val.castSucc, i.property.1,
      i.val.castSucc_le_succ.trans i.property.2⟩;
    let jn (i : E) : J := ⟨i.val.succ,
      i.property.1.trans i.val.castSucc_le_succ, i.property.2⟩;
    ∀ (lo hi : J → ℝ) (left middle right : (j : J) → ℝ → (H.stage j.val).Carrier),
      (∀ j, H.regularizedStageStart T 0 j.val ≤ lo j ∧ lo j ≤ hi j ∧
        hi j ≤ H.regularizedStageEnd T v j.val) →
      (∀ j, Manifold.absolutelyContinuousOnInterval ThreeModel (left j)
        (H.regularizedStageStart T 0 j.val) (lo j)) →
      (∀ j, Manifold.absolutelyContinuousOnInterval ThreeModel (middle j) (lo j) (hi j)) →
      (∀ j, Manifold.absolutelyContinuousOnInterval ThreeModel (right j)
        (hi j) (H.regularizedStageEnd T v j.val)) →
      (∀ j, IntervalIntegrable (H.stageRegularizedLagrangian j.val T (left j)) volume
        (H.regularizedStageStart T 0 j.val) (lo j)) →
      (∀ j, IntervalIntegrable (H.stageRegularizedLagrangian j.val T (middle j)) volume
        (lo j) (hi j)) →
      (∀ j, IntervalIntegrable (H.stageRegularizedLagrangian j.val T (right j)) volume
        (hi j) (H.regularizedStageEnd T v j.val)) →
      (∀ j, left j (lo j) = middle j (lo j)) →
      (∀ j, middle j (hi j) = right j (hi j)) →
    ∀ (W : (i : E) → TopologicalSpace.Opens (H.event i.val).incoming.terminalRegularOpen)
      (F : (i : E) → PartialDiffeomorph ThreeModel ThreeModel
        (H.event i.val).incoming.terminalRegularOpen (H.stage i.val.succ).Carrier ∞)
      (D : E → RealTimeInterval)
      (S : (i : E) → SolutionOn (I := ThreeModel) (M := W i) (D i))
      (eta : (i : E) → ℝ → W i),
      (∀ i z, (H.event i.val).RegularCrossing (z : W i).val.val (F i z.val)) →
      (∀ i, left (jo i) (Real.sqrt (T - H.time i.val.succ)) =
        (eta i (Real.sqrt (T - H.time i.val.succ))).val.val) →
      (∀ i, right (jn i) (Real.sqrt (T - H.time i.val.succ)) =
        F i (eta i (Real.sqrt (T - H.time i.val.succ))).val) →
      (∀ i, lRegularizedAction (S i) T (eta i) (hi (jn i)) (lo (jo i)) =
        H.stageRegularizedAction i.val.succ T (right (jn i)) (hi (jn i))
          (Real.sqrt (T - H.time i.val.succ)) +
        H.stageRegularizedAction i.val.castSucc T (left (jo i))
          (Real.sqrt (T - H.time i.val.succ)) (lo (jo i))) →
    ∃ delta : (j : J) → ℝ → (H.stage j.val).Carrier,
      (∀ j, Manifold.absolutelyContinuousOnInterval ThreeModel (delta j)
        (H.regularizedStageStart T 0 j.val) (H.regularizedStageEnd T v j.val)) ∧
      (∀ j, IntervalIntegrable (H.stageRegularizedLagrangian j.val T (delta j)) volume
        (H.regularizedStageStart T 0 j.val) (H.regularizedStageEnd T v j.val)) ∧
      (∀ j, EqOn (delta j) (left j) (Icc (H.regularizedStageStart T 0 j.val) (lo j)) ∧
        EqOn (delta j) (middle j) (Icc (lo j) (hi j)) ∧
        EqOn (delta j) (right j) (Icc (hi j) (H.regularizedStageEnd T v j.val))) ∧
      EqOn (delta ⟨last, hle, le_rfl⟩) (left ⟨last, hle, le_rfl⟩)
        (Icc 0 (lo ⟨last, hle, le_rfl⟩)) ∧
      delta ⟨last, hle, le_rfl⟩ 0 = left ⟨last, hle, le_rfl⟩ 0 ∧
      delta ⟨first, le_rfl, hle⟩ v = right ⟨first, le_rfl, hle⟩ v ∧
      (∀ (i : Fin H.eventCount) (hf : first ≤ i.castSucc) (hl : i.succ ≤ last),
        ∃ z : (H.event i).old,
          z.val.val = delta ⟨i.castSucc, hf, i.castSucc_le_succ.trans hl⟩
            (Real.sqrt (T - H.time i.succ)) ∧
          (H.event i).oldOutput z =
            delta ⟨i.succ, hf.trans i.castSucc_le_succ, hl⟩
              (Real.sqrt (T - H.time i.succ))) ∧
      (∑ j : J, H.stageRegularizedAction j.val T (delta j)
        (H.regularizedStageStart T 0 j.val) (H.regularizedStageEnd T v j.val)) =
        H.stageRegularizedAction last T (left ⟨last, hle, le_rfl⟩)
          0 (lo ⟨last, hle, le_rfl⟩) +
        (∑ j : J, H.stageRegularizedAction j.val T (middle j) (lo j) (hi j)) +
        (∑ i : E, lRegularizedAction (S i) T (eta i) (hi (jn i)) (lo (jo i))) +
        H.stageRegularizedAction first T (right ⟨first, le_rfl, hle⟩)
          (hi ⟨first, le_rfl, hle⟩) v := by
  classical
  intro J E jo jn lo hi left middle right hbounds hleftAC hmidAC hrightAC
    hleftInt hmidInt hrightInt hmatchL hmatchR W F D S eta hcross hnodeL hnodeR hseam
  have hpieces (j : J) := H.exists_three_piece_stage_curve j.val T
    (left j) (middle j) (right j) (hbounds j).1 (hbounds j).2.1 (hbounds j).2.2
    (hleftAC j) (hmidAC j) (hrightAC j) (hleftInt j) (hmidInt j) (hrightInt j)
    (hmatchL j) (hmatchR j)
  choose delta hAC hint hleft hmid hright haction using hpieces
  have hupper0 : T - (0 : ℝ) ^ 2 ∈ Icc (H.time last) (H.stageEndTime last) := by
    simpa only [zero_pow two_ne_zero, sub_zero] using hupper
  have hstart : H.regularizedStageStart T 0 last = 0 :=
    H.regularizedStageStart_eq_of_mem_Icc (show (0 : ℝ) ≤ 0 from le_rfl) hupper0
  have hend : H.regularizedStageEnd T v first = v :=
    H.regularizedStageEnd_eq_of_mem_stageDomain hv hpast
  have ho (i : E) : H.regularizedStageStart T 0 i.val.castSucc =
      Real.sqrt (T - H.time i.val.succ) :=
    H.regularizedStageStart_castSucc_eq_event_clock hupper0 i.val i.property.2
  have hn (i : E) : H.regularizedStageEnd T v i.val.succ =
      Real.sqrt (T - H.time i.val.succ) :=
    H.regularizedStageEnd_succ_eq_event_clock hpast i.val i.property.1
  have hprefix : EqOn (delta ⟨last, hle, le_rfl⟩) (left ⟨last, hle, le_rfl⟩)
      (Icc 0 (lo ⟨last, hle, le_rfl⟩)) := by
    simpa only [hstart] using hleft ⟨last, hle, le_rfl⟩
  refine ⟨delta, hAC, hint, fun j => ⟨hleft j, hmid j, hright j⟩, hprefix,
    hprefix ⟨le_rfl, ?_⟩, ?_, ?_, ?_⟩
  · simpa only [hstart] using (hbounds ⟨last, hle, le_rfl⟩).1
  · apply hright ⟨first, le_rfl, hle⟩
    constructor
    · simpa only [hend] using (hbounds ⟨first, le_rfl, hle⟩).2.2
    · exact hend.ge
  · intro i hf hl
    let k : E := ⟨i, hf, hl⟩
    have hoEq : delta (jo k) (Real.sqrt (T - H.time i.succ)) =
        (eta k (Real.sqrt (T - H.time i.succ))).val.val := by
      rw [← hnodeL k]
      apply hleft (jo k)
      constructor
      · exact (ho k).le
      · simpa only [jo, ho k] using (hbounds (jo k)).1
    have hnEq : delta (jn k) (Real.sqrt (T - H.time i.succ)) =
        F k (eta k (Real.sqrt (T - H.time i.succ))).val := by
      rw [← hnodeR k]
      apply hright (jn k)
      constructor
      · simpa only [jn, hn k] using (hbounds (jn k)).2.2
      · exact (hn k).ge
    obtain ⟨z, _, hzOld, hzNew⟩ := hcross k (eta k (Real.sqrt (T - H.time i.succ)))
    exact ⟨z, hzOld.trans hoEq.symm, hzNew.trans hnEq.symm⟩
  · calc
      _ = ∑ j : J, (H.stageRegularizedAction j.val T (left j)
          (H.regularizedStageStart T 0 j.val) (lo j) +
          H.stageRegularizedAction j.val T (middle j) (lo j) (hi j) +
          H.stageRegularizedAction j.val T (right j)
            (hi j) (H.regularizedStageEnd T v j.val)) :=
        Finset.sum_congr rfl (fun j _ => haction j)
      _ = _ := by
        rw [H.sum_stage_parts_eq_endpoints_add_events first last hle]
        simp only [hstart, hend]
        congr 2
        apply Finset.sum_congr rfl
        intro i _
        change H.stageRegularizedAction i.val.succ T (right (jn i))
          (hi (jn i)) (H.regularizedStageEnd T v i.val.succ) +
          H.stageRegularizedAction i.val.castSucc T (left (jo i))
            (H.regularizedStageStart T 0 i.val.castSucc) (lo (jo i)) = _
        rw [ho, hn]
        exact (hseam i).symm

theorem extend_stage_family_by_zero_pole_stage
    (H : ObservedHistory.{u}) (first : Fin (H.eventCount + 1)) (i : Fin H.eventCount)
    (hf : first ≤ i.castSucc) (v : ℝ)
    (gamma : (j : H.StageInterval first i.succ) → ℝ → (H.stage j.val).Carrier)
    (delta : (j : H.StageInterval first i.castSucc) → ℝ → (H.stage j.val).Carrier)
    (hAC : ∀ j, Manifold.absolutelyContinuousOnInterval ThreeModel (delta j)
      (H.regularizedStageStart (H.time i.succ) 0 j.val)
      (H.regularizedStageEnd (H.time i.succ) v j.val))
    (hint : ∀ j, IntervalIntegrable
      (H.stageRegularizedLagrangian j.val (H.time i.succ) (delta j)) volume
      (H.regularizedStageStart (H.time i.succ) 0 j.val)
      (H.regularizedStageEnd (H.time i.succ) v j.val))
    (hnodes : ∀ (k : Fin H.eventCount) (hkf : first ≤ k.castSucc) (hkl : k.succ ≤ i.castSucc),
      ∃ z : (H.event k).old,
        z.val.val = delta ⟨k.castSucc, hkf, k.castSucc_le_succ.trans hkl⟩
          (Real.sqrt (H.time i.succ - H.time k.succ)) ∧
        (H.event k).oldOutput z = delta ⟨k.succ, hkf.trans k.castSucc_le_succ, hkl⟩
          (Real.sqrt (H.time i.succ - H.time k.succ)))
    (hstart : delta ⟨i.castSucc, hf, le_rfl⟩ 0 =
      gamma ⟨i.castSucc, hf, i.castSucc_le_succ⟩ 0)
    (hpole : ∃ z : (H.event i).old,
      z.val.val = gamma ⟨i.castSucc, hf, i.castSucc_le_succ⟩ 0 ∧
      (H.event i).oldOutput z = gamma ⟨i.succ, hf.trans i.castSucc_le_succ, le_rfl⟩ 0) :
    ∃ beta : (j : H.StageInterval first i.succ) → ℝ → (H.stage j.val).Carrier,
      (∀ j, Manifold.absolutelyContinuousOnInterval ThreeModel (beta j)
        (H.regularizedStageStart (H.time i.succ) 0 j.val)
        (H.regularizedStageEnd (H.time i.succ) v j.val)) ∧
      (∀ j, IntervalIntegrable
        (H.stageRegularizedLagrangian j.val (H.time i.succ) (beta j)) volume
        (H.regularizedStageStart (H.time i.succ) 0 j.val)
        (H.regularizedStageEnd (H.time i.succ) v j.val)) ∧
      (∀ j : H.StageInterval first i.castSucc,
        beta ⟨j.val, j.property.1, j.property.2.trans i.castSucc_le_succ⟩ = delta j) ∧
      beta ⟨i.succ, hf.trans i.castSucc_le_succ, le_rfl⟩ =
        gamma ⟨i.succ, hf.trans i.castSucc_le_succ, le_rfl⟩ ∧
      (∀ (k : Fin H.eventCount) (hkf : first ≤ k.castSucc) (hkl : k.succ ≤ i.succ),
        ∃ z : (H.event k).old,
          z.val.val = beta ⟨k.castSucc, hkf, k.castSucc_le_succ.trans hkl⟩
            (Real.sqrt (H.time i.succ - H.time k.succ)) ∧
          (H.event k).oldOutput z = beta ⟨k.succ, hkf.trans k.castSucc_le_succ, hkl⟩
            (Real.sqrt (H.time i.succ - H.time k.succ))) ∧
      (∑ j : H.StageInterval first i.succ,
        H.stageRegularizedAction j.val (H.time i.succ) (beta j)
          (H.regularizedStageStart (H.time i.succ) 0 j.val)
          (H.regularizedStageEnd (H.time i.succ) v j.val)) =
        ∑ j : H.StageInterval first i.castSucc,
          H.stageRegularizedAction j.val (H.time i.succ) (delta j)
            (H.regularizedStageStart (H.time i.succ) 0 j.val)
            (H.regularizedStageEnd (H.time i.succ) v j.val) := by
  classical
  let beta (j : H.StageInterval first i.succ) : ℝ → (H.stage j.val).Carrier :=
    if hj : j.val ≤ i.castSucc then delta ⟨j.val, j.property.1, hj⟩ else gamma j
  have hbetaOld (j : H.StageInterval first i.castSucc) :
      beta ⟨j.val, j.property.1, j.property.2.trans i.castSucc_le_succ⟩ = delta j := by
    simp only [beta, dite_eq_left j.property.2]
  have hbetaLast : beta ⟨i.succ, hf.trans i.castSucc_le_succ, le_rfl⟩ =
      gamma ⟨i.succ, hf.trans i.castSucc_le_succ, le_rfl⟩ := by
    simp only [beta, dite_eq_right (not_le_of_gt i.castSucc_lt_succ)]
  have hs : H.regularizedStageStart (H.time i.succ) 0 i.succ = 0 := by
    apply H.regularizedStageStart_eq_of_mem_Icc le_rfl
    simpa only [zero_pow two_ne_zero, sub_zero] using
      (show H.time i.succ ∈ Icc (H.time i.succ) (H.stageEndTime i.succ) from
        ⟨le_rfl, H.time_le_stageEndTime i.succ⟩)
  have he : H.regularizedStageEnd (H.time i.succ) v i.succ = 0 := by
    simp only [regularizedStageEnd, max_eq_right (sub_le_self _ (sq_nonneg v)),
      sub_self, Real.sqrt_zero]
  have hjLast (j : H.StageInterval first i.succ) (hj : ¬j.val ≤ i.castSucc) :
      j = ⟨i.succ, hf.trans i.castSucc_le_succ, le_rfl⟩ := by
    apply Subtype.ext
    apply Fin.ext
    have hh := j.property.2
    change j.val.val ≤ i.val + 1 at hh
    change ¬j.val.val ≤ i.val at hj
    change j.val.val = i.val + 1
    omega
  have hbetaAC (j : H.StageInterval first i.succ) :
      Manifold.absolutelyContinuousOnInterval ThreeModel (beta j)
        (H.regularizedStageStart (H.time i.succ) 0 j.val)
        (H.regularizedStageEnd (H.time i.succ) v j.val) := by
    by_cases hj : j.val ≤ i.castSucc
    · simpa only [beta, dite_eq_left hj] using hAC ⟨j.val, j.property.1, hj⟩
    · rw [hjLast j hj, hs, he]
      apply Manifold.absolutelyContinuousOnInterval_of_contMDiffOn
      apply (contMDiffOn_const (c := beta ⟨i.succ, hf.trans i.castSucc_le_succ, le_rfl⟩ 0)).congr
      intro r hr
      have hr0 : r = 0 := by simpa only [uIcc_self, mem_singleton_iff] using hr
      simp only [hr0]
  have hbetaInt (j : H.StageInterval first i.succ) :
      IntervalIntegrable (H.stageRegularizedLagrangian j.val (H.time i.succ) (beta j)) volume
        (H.regularizedStageStart (H.time i.succ) 0 j.val)
        (H.regularizedStageEnd (H.time i.succ) v j.val) := by
    by_cases hj : j.val ≤ i.castSucc
    · simpa only [beta, dite_eq_left hj] using hint ⟨j.val, j.property.1, hj⟩
    · rw [hjLast j hj, hs, he]
  refine ⟨beta, hbetaAC, hbetaInt, hbetaOld, hbetaLast, ?_, ?_⟩
  · intro k hkf hkl
    by_cases hki : k = i
    · subst k
      obtain ⟨z, hzOld, hzNew⟩ := hpole
      simp only [sub_self, Real.sqrt_zero]
      refine ⟨z, ?_, ?_⟩
      · rw [hbetaOld ⟨i.castSucc, hf, le_rfl⟩]
        exact hzOld.trans hstart.symm
      · rw [hbetaLast]
        exact hzNew
    · have hkOld : k.succ ≤ i.castSucc := by
        have hval : k.val ≠ i.val := fun h => hki (Fin.ext h)
        change k.val + 1 ≤ i.val
        change k.val + 1 ≤ i.val + 1 at hkl
        omega
      obtain ⟨z, hzOld, hzNew⟩ := hnodes k hkf hkOld
      refine ⟨z, ?_, ?_⟩
      · rw [hbetaOld ⟨k.castSucc, hkf, k.castSucc_le_succ.trans hkOld⟩]
        exact hzOld
      · rw [hbetaOld ⟨k.succ, hkf.trans k.castSucc_le_succ, hkOld⟩]
        exact hzNew
  · let jl : H.StageInterval first i.succ := ⟨i.succ, hf.trans i.castSucc_le_succ, le_rfl⟩
    let action (j : H.StageInterval first i.succ) :=
      H.stageRegularizedAction j.val (H.time i.succ) (beta j)
        (H.regularizedStageStart (H.time i.succ) 0 j.val)
        (H.regularizedStageEnd (H.time i.succ) v j.val)
    have hzero : action jl = 0 := by
      dsimp only [action, jl]
      rw [hs, he]
      exact intervalIntegral.integral_same
    let e : {j : H.StageInterval first i.succ // j ≠ jl} ≃
        H.StageInterval first i.castSucc :=
      { toFun := fun j => ⟨j.val.val, j.val.property.1, by
          by_contra hj
          exact j.property (hjLast j.val hj)⟩
        invFun := fun j => ⟨⟨j.val, j.property.1, j.property.2.trans i.castSucc_le_succ⟩, by
          intro h
          have hv := congrArg (fun j : H.StageInterval first i.succ => j.val.val) h
          have hj := j.property.2
          change j.val.val ≤ i.val at hj
          change j.val.val = i.val + 1 at hv
          omega⟩
        left_inv := fun _ => rfl
        right_inv := fun _ => rfl }
    change (∑ j, action j) = _
    rw [Fintype.sum_eq_add_sum_subtype_ne action jl, hzero, zero_add]
    exact Fintype.sum_equiv e (fun j => action j.val) _ (fun j => by
      have hbj := hbetaOld (e j)
      change beta j.val = delta (e j) at hbj
      dsimp only [action]
      rw [hbj]
      rfl)

/-- An AC stage family with its actual old-output witnesses is an admissible
competitor for the same history. The scalar floor is global on each actual stage
domain; integrability identifies its extended action with its finite action. -/
private theorem regularizedCost_le_sum_action_of_ac_stage_family
    (H : ObservedHistory.{u}) (first last : Fin (H.eventCount + 1)) (hle : first ≤ last)
    {T v : ℝ} (hv : 0 ≤ v)
    (hupper : T ∈ Icc (H.time last) (H.stageEndTime last))
    (hpast : T - v ^ 2 ∈ H.stageDomain first) (B : ℝ)
    (hscalar : ∀ j (t : ℝ), t ∈ H.stageDomain j →
      ∀ x : (H.stage j).Carrier, -B ≤ metricScalarAt (H.stageMetric j t) x)
    (delta : (j : H.StageInterval first last) → ℝ → (H.stage j.val).Carrier)
    (hAC : ∀ j, Manifold.absolutelyContinuousOnInterval ThreeModel (delta j)
      (H.regularizedStageStart T 0 j.val) (H.regularizedStageEnd T v j.val))
    (hint : ∀ j, IntervalIntegrable (H.stageRegularizedLagrangian j.val T (delta j)) volume
      (H.regularizedStageStart T 0 j.val) (H.regularizedStageEnd T v j.val))
    (hnodes : ∀ (i : Fin H.eventCount) (hf : first ≤ i.castSucc) (hl : i.succ ≤ last),
      ∃ z : (H.event i).old,
        z.val.val = delta ⟨i.castSucc, hf, i.castSucc_le_succ.trans hl⟩
          (Real.sqrt (T - H.time i.succ)) ∧
        (H.event i).oldOutput z = delta ⟨i.succ, hf.trans i.castSucc_le_succ, hl⟩
          (Real.sqrt (T - H.time i.succ))) :
    H.regularizedCost first last hle T B 0 v
      (delta ⟨last, hle, le_rfl⟩ 0) (delta ⟨first, le_rfl, hle⟩ v) ≤
        ((∑ j : H.StageInterval first last,
          H.stageRegularizedAction j.val T (delta j)
            (H.regularizedStageStart T 0 j.val) (H.regularizedStageEnd T v j.val) : ℝ) :
          WithTop ℝ) := by
  have hupper0 : T - (0 : ℝ) ^ 2 ∈ Icc (H.time last) (H.stageEndTime last) := by
    simpa only [zero_pow two_ne_zero, sub_zero] using hupper
  have hmember : H.regularizedExtendedAction first last T B 0 v delta ∈
      H.regularizedActionValues first last hle T B 0 v
        (delta ⟨last, hle, le_rfl⟩ 0) (delta ⟨first, le_rfl, hle⟩ v) :=
    ⟨le_rfl, hv, hupper0, hpast, delta, hAC, rfl, rfl, hnodes, rfl⟩
  have hfull := H.regularizedExtendedAction_eq_sum_action first last le_rfl hv
    hupper0 hpast delta hint (fun j => by
      filter_upwards [ae_restrict_mem measurableSet_Ioo] with r hr
      exact hscalar j.val (T - r ^ 2) (H.mapsTo_regularizedStage_Ioo T 0 v j.val hr)
        (delta j r))
  exact (H.regularizedCost_le_of_competitor first last hle T B 0 v _ _ hmember).trans_eq hfull

/-- Assemble the actual AC collar pieces before taking the history cost
infimum. The bound is the action of those same pieces and collar flows. -/
theorem regularizedCost_le_collar_piece_action
    (H : ObservedHistory.{u}) (first last : Fin (H.eventCount + 1)) (hle : first ≤ last)
    {T v : ℝ} (hv : 0 ≤ v)
    (hupper : T ∈ Icc (H.time last) (H.stageEndTime last))
    (hpast : T - v ^ 2 ∈ H.stageDomain first) (B : ℝ)
    (hscalar : ∀ j (t : ℝ), t ∈ H.stageDomain j →
      ∀ x : (H.stage j).Carrier, -B ≤ metricScalarAt (H.stageMetric j t) x) :
    let J := H.StageInterval first last;
    let E := {i : Fin H.eventCount // first ≤ i.castSucc ∧ i.succ ≤ last};
    let jo (i : E) : J := ⟨i.val.castSucc, i.property.1,
      i.val.castSucc_le_succ.trans i.property.2⟩;
    let jn (i : E) : J := ⟨i.val.succ,
      i.property.1.trans i.val.castSucc_le_succ, i.property.2⟩;
    ∀ (lo hi : J → ℝ) (left middle right : (j : J) → ℝ → (H.stage j.val).Carrier),
      (∀ j, H.regularizedStageStart T 0 j.val ≤ lo j ∧ lo j ≤ hi j ∧
        hi j ≤ H.regularizedStageEnd T v j.val) →
      (∀ j, Manifold.absolutelyContinuousOnInterval ThreeModel (left j)
        (H.regularizedStageStart T 0 j.val) (lo j)) →
      (∀ j, Manifold.absolutelyContinuousOnInterval ThreeModel (middle j) (lo j) (hi j)) →
      (∀ j, Manifold.absolutelyContinuousOnInterval ThreeModel (right j)
        (hi j) (H.regularizedStageEnd T v j.val)) →
      (∀ j, IntervalIntegrable (H.stageRegularizedLagrangian j.val T (left j)) volume
        (H.regularizedStageStart T 0 j.val) (lo j)) →
      (∀ j, IntervalIntegrable (H.stageRegularizedLagrangian j.val T (middle j)) volume
        (lo j) (hi j)) →
      (∀ j, IntervalIntegrable (H.stageRegularizedLagrangian j.val T (right j)) volume
        (hi j) (H.regularizedStageEnd T v j.val)) →
      (∀ j, left j (lo j) = middle j (lo j)) →
      (∀ j, middle j (hi j) = right j (hi j)) →
    ∀ (W : (i : E) → TopologicalSpace.Opens (H.event i.val).incoming.terminalRegularOpen)
      (F : (i : E) → PartialDiffeomorph ThreeModel ThreeModel
        (H.event i.val).incoming.terminalRegularOpen (H.stage i.val.succ).Carrier ∞)
      (D : E → RealTimeInterval)
      (S : (i : E) → SolutionOn (I := ThreeModel) (M := W i) (D i))
      (eta : (i : E) → ℝ → W i),
      (∀ i z, (H.event i.val).RegularCrossing (z : W i).val.val (F i z.val)) →
      (∀ i, left (jo i) (Real.sqrt (T - H.time i.val.succ)) =
        (eta i (Real.sqrt (T - H.time i.val.succ))).val.val) →
      (∀ i, right (jn i) (Real.sqrt (T - H.time i.val.succ)) =
        F i (eta i (Real.sqrt (T - H.time i.val.succ))).val) →
      (∀ i, lRegularizedAction (S i) T (eta i) (hi (jn i)) (lo (jo i)) =
        H.stageRegularizedAction i.val.succ T (right (jn i)) (hi (jn i))
          (Real.sqrt (T - H.time i.val.succ)) +
        H.stageRegularizedAction i.val.castSucc T (left (jo i))
          (Real.sqrt (T - H.time i.val.succ)) (lo (jo i))) →
    H.regularizedCost first last hle T B 0 v
      (left ⟨last, hle, le_rfl⟩ 0) (right ⟨first, le_rfl, hle⟩ v) ≤
        ((H.stageRegularizedAction last T (left ⟨last, hle, le_rfl⟩)
            0 (lo ⟨last, hle, le_rfl⟩) +
          (∑ j : J, H.stageRegularizedAction j.val T (middle j) (lo j) (hi j)) +
          (∑ i : E, lRegularizedAction (S i) T (eta i) (hi (jn i)) (lo (jo i))) +
          H.stageRegularizedAction first T (right ⟨first, le_rfl, hle⟩)
            (hi ⟨first, le_rfl, hle⟩) v : ℝ) : WithTop ℝ) := by
  classical
  intro J E jo jn lo hi left middle right hbounds hleftAC hmidAC hrightAC
    hleftInt hmidInt hrightInt hmatchL hmatchR W F D S eta hcross hnodeL hnodeR hseam
  obtain ⟨delta, hAC, hint, _hpieces, _hprefix, hstart, hend, hnodes, haction⟩ :=
    H.exists_stage_family_of_collar_pieces first last hle hv hupper hpast
      lo hi left middle right hbounds hleftAC hmidAC hrightAC
      hleftInt hmidInt hrightInt hmatchL hmatchR W F D S eta hcross hnodeL hnodeR hseam
  have hcost := H.regularizedCost_le_sum_action_of_ac_stage_family first last hle
    hv hupper hpast B hscalar delta hAC hint hnodes
  rw [hstart, hend] at hcost
  exact hcost.trans_eq (congrArg (fun A : ℝ => (A : WithTop ℝ)) haction)

/-- Attach the original zero-clock event node to an assembled older competitor.
The node is the actual old/output witness; no regular crossing at clock zero is
required, and the added pole stage contributes zero action. -/
theorem regularizedCost_le_of_zero_pole_stage_extension
    (H : ObservedHistory.{u}) (first : Fin (H.eventCount + 1)) (i : Fin H.eventCount)
    (hf : first ≤ i.castSucc) (v : ℝ) (hv : 0 ≤ v)
    (hpast : H.time i.succ - v ^ 2 ∈ H.stageDomain first) (B : ℝ)
    (hscalar : ∀ j (t : ℝ), t ∈ H.stageDomain j →
      ∀ x : (H.stage j).Carrier, -B ≤ metricScalarAt (H.stageMetric j t) x)
    (gamma : (j : H.StageInterval first i.succ) → ℝ → (H.stage j.val).Carrier)
    (delta : (j : H.StageInterval first i.castSucc) → ℝ → (H.stage j.val).Carrier)
    (hAC : ∀ j, Manifold.absolutelyContinuousOnInterval ThreeModel (delta j)
      (H.regularizedStageStart (H.time i.succ) 0 j.val)
      (H.regularizedStageEnd (H.time i.succ) v j.val))
    (hint : ∀ j, IntervalIntegrable
      (H.stageRegularizedLagrangian j.val (H.time i.succ) (delta j)) volume
      (H.regularizedStageStart (H.time i.succ) 0 j.val)
      (H.regularizedStageEnd (H.time i.succ) v j.val))
    (hnodes : ∀ (k : Fin H.eventCount) (hkf : first ≤ k.castSucc) (hkl : k.succ ≤ i.castSucc),
      ∃ z : (H.event k).old,
        z.val.val = delta ⟨k.castSucc, hkf, k.castSucc_le_succ.trans hkl⟩
          (Real.sqrt (H.time i.succ - H.time k.succ)) ∧
        (H.event k).oldOutput z = delta ⟨k.succ, hkf.trans k.castSucc_le_succ, hkl⟩
          (Real.sqrt (H.time i.succ - H.time k.succ)))
    (hstart : delta ⟨i.castSucc, hf, le_rfl⟩ 0 =
      gamma ⟨i.castSucc, hf, i.castSucc_le_succ⟩ 0)
    (hpole : ∃ z : (H.event i).old,
      z.val.val = gamma ⟨i.castSucc, hf, i.castSucc_le_succ⟩ 0 ∧
      (H.event i).oldOutput z = gamma ⟨i.succ, hf.trans i.castSucc_le_succ, le_rfl⟩ 0) :
    H.regularizedCost first i.succ (hf.trans i.castSucc_le_succ) (H.time i.succ) B 0 v
      (gamma ⟨i.succ, hf.trans i.castSucc_le_succ, le_rfl⟩ 0)
      (delta ⟨first, le_rfl, hf⟩ v) ≤
        ((∑ j : H.StageInterval first i.castSucc,
          H.stageRegularizedAction j.val (H.time i.succ) (delta j)
            (H.regularizedStageStart (H.time i.succ) 0 j.val)
            (H.regularizedStageEnd (H.time i.succ) v j.val) : ℝ) : WithTop ℝ) := by
  obtain ⟨beta, hbetaAC, hbetaInt, hbetaOld, hbetaLast, hbetaNodes, haction⟩ :=
    H.extend_stage_family_by_zero_pole_stage first i hf v gamma delta hAC hint hnodes hstart hpole
  have hupper : H.time i.succ ∈ Icc (H.time i.succ) (H.stageEndTime i.succ) :=
    ⟨le_rfl, H.time_le_stageEndTime i.succ⟩
  have hbetaStart : beta ⟨i.succ, hf.trans i.castSucc_le_succ, le_rfl⟩ 0 =
      gamma ⟨i.succ, hf.trans i.castSucc_le_succ, le_rfl⟩ 0 :=
    congrArg (fun c : ℝ → (H.stage i.succ).Carrier => c 0) hbetaLast
  have hbetaEnd : beta ⟨first, le_rfl, hf.trans i.castSucc_le_succ⟩ v =
      delta ⟨first, le_rfl, hf⟩ v :=
    congrArg (fun c : ℝ → (H.stage first).Carrier => c v)
      (hbetaOld ⟨first, le_rfl, hf⟩)
  have hcost := H.regularizedCost_le_sum_action_of_ac_stage_family first i.succ
    (hf.trans i.castSucc_le_succ) hv hupper hpast B hscalar beta hbetaAC hbetaInt hbetaNodes
  rw [hbetaStart, hbetaEnd] at hcost
  exact hcost.trans_eq (congrArg (fun A : ℝ => (A : WithTop ℝ)) haction)

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory
