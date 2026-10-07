import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.LGeometry.Action.AbsoluteContinuity

set_option autoImplicit false
noncomputable section

open Set MeasureTheory
open DifferentialGeometry.Geometry.Curvature
open scoped Manifold BigOperators

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory

universe u

private theorem sum_dite_eq_sum_subtype {ι A : Type*} [Fintype ι] [AddCommMonoid A]
    (p : ι → Prop) [DecidablePred p] (f : ∀ j, p j → A) :
    (∑ j, if hj : p j then f j hj else 0) = ∑ j : {j // p j}, f j.val j.property := by
  classical
  let g : ι → A := fun j => if hj : p j then f j hj else 0
  change (∑ j, g j) = _
  rw [← Fintype.sum_subtype_add_sum_subtype p g]
  have hzero : (∑ j : {j // ¬p j}, g j.val) = 0 := by
    apply Finset.sum_eq_zero
    intro j _
    simp only [g, dite_eq_right j.property]
  rw [hzero, add_zero]
  apply Finset.sum_congr rfl
  intro j _
  simp only [g, dite_eq_left j.property]

private theorem stageEndTime_le_time_of_lt (H : ObservedHistory.{u})
    {i j : Fin (H.eventCount + 1)} (hij : i < j) : H.stageEndTime i ≤ H.time j := by
  cases i using Fin.lastCases with
  | last => exact False.elim ((not_lt_of_ge (Fin.le_last _)) hij)
  | cast i =>
    rw [H.stageEndTime_castSucc]
    exact H.time_strictMono.monotone (show i.succ ≤ j from hij)

private theorem exists_closed_stage_action_splice_preserving_prefix
    (H : ObservedHistory.{u})
    (first middle last : Fin (H.eventCount + 1))
    (hfm : first ≤ middle) (hml : middle ≤ last)
    (T B u w v Anew Aold : ℝ) (hu : 0 ≤ u) (huw : u ≤ w) (hwv : w ≤ v)
    (hupper : T - u ^ 2 ∈ Icc (H.time last) (H.stageEndTime last))
    (hmiddle : T - w ^ 2 ∈ H.stageDomain middle)
    (hlower : T - v ^ 2 ∈ H.stageDomain first)
    (hscalar : ∀ j : H.StageInterval first last, ∀ s ∈
      Ioo (H.regularizedStageStart T u j.val) (H.regularizedStageEnd T v j.val),
      ∀ y : (H.stage j.val).Carrier, -B ≤ metricScalarAt (H.stageMetric j.val (T - s ^ 2)) y)
    (alpha : (j : H.StageInterval middle last) → ℝ → (H.stage j.val).Carrier)
    (beta : (j : H.StageInterval first middle) → ℝ → (H.stage j.val).Carrier)
    (hAlpha : ∀ j, Manifold.absolutelyContinuousOnInterval ThreeModel (alpha j)
      (H.regularizedStageStart T u j.val) (H.regularizedStageEnd T w j.val))
    (hBeta : ∀ j, Manifold.absolutelyContinuousOnInterval ThreeModel (beta j)
      (H.regularizedStageStart T w j.val) (H.regularizedStageEnd T v j.val))
    (hmatch : alpha ⟨middle, le_rfl, hml⟩ w = beta ⟨middle, hfm, le_rfl⟩ w)
    (hAlphaNodes : ∀ (i : Fin H.eventCount) (hf : middle ≤ i.castSucc) (hl : i.succ ≤ last),
      ∃ z : (H.event i).old,
        z.val.val = alpha ⟨i.castSucc, hf, i.castSucc_lt_succ.le.trans hl⟩
          (Real.sqrt (T - H.time i.succ)) ∧
        (H.event i).oldOutput z = alpha ⟨i.succ, hf.trans i.castSucc_lt_succ.le, hl⟩
          (Real.sqrt (T - H.time i.succ)))
    (hBetaNodes : ∀ (i : Fin H.eventCount) (hf : first ≤ i.castSucc) (hl : i.succ ≤ middle),
      ∃ z : (H.event i).old,
        z.val.val = beta ⟨i.castSucc, hf, i.castSucc_lt_succ.le.trans hl⟩
          (Real.sqrt (T - H.time i.succ)) ∧
        (H.event i).oldOutput z = beta ⟨i.succ, hf.trans i.castSucc_lt_succ.le, hl⟩
          (Real.sqrt (T - H.time i.succ)))
    (hAlphaAction : H.regularizedExtendedAction middle last T B u w alpha =
      ((Anew : ℝ) : WithTop ℝ))
    (hBetaAction : H.regularizedExtendedAction first middle T B w v beta =
      ((Aold : ℝ) : WithTop ℝ)) :
    ∃ gamma : (j : H.StageInterval first last) → ℝ → (H.stage j.val).Carrier,
      (∀ j, Manifold.absolutelyContinuousOnInterval ThreeModel (gamma j)
        (H.regularizedStageStart T u j.val) (H.regularizedStageEnd T v j.val)) ∧
      gamma ⟨last, hfm.trans hml, le_rfl⟩ u = alpha ⟨last, hml, le_rfl⟩ u ∧
      gamma ⟨first, le_rfl, hfm.trans hml⟩ v = beta ⟨first, le_rfl, hfm⟩ v ∧
      (∀ (i : Fin H.eventCount) (hf : first ≤ i.castSucc) (hl : i.succ ≤ last),
        ∃ z : (H.event i).old,
          z.val.val = gamma ⟨i.castSucc, hf, i.castSucc_lt_succ.le.trans hl⟩
            (Real.sqrt (T - H.time i.succ)) ∧
          (H.event i).oldOutput z = gamma ⟨i.succ, hf.trans i.castSucc_lt_succ.le, hl⟩
            (Real.sqrt (T - H.time i.succ))) ∧
      H.regularizedExtendedAction first last T B u v gamma =
        (((Anew + Aold : ℝ)) : WithTop ℝ) ∧
      (∀ j : H.StageInterval middle last,
        EqOn (gamma ⟨j.val, hfm.trans j.property.1, j.property.2⟩) (alpha j)
          (Icc (H.regularizedStageStart T u j.val) (H.regularizedStageEnd T w j.val))) ∧
      (∀ j : H.StageInterval first middle,
        EqOn (gamma ⟨j.val, j.property.1, j.property.2.trans hml⟩) (beta j)
          (Icc (H.regularizedStageStart T w j.val) (H.regularizedStageEnd T v j.val))) := by
  classical
  have hw : 0 ≤ w := hu.trans huw
  have hMiddleIcc : T - w ^ 2 ∈ Icc (H.time middle) (H.stageEndTime middle) :=
    ⟨H.time_le_of_mem_stageDomain hmiddle, H.le_stageEndTime_of_mem_stageDomain hmiddle⟩
  have hStartMiddle : H.regularizedStageStart T w middle = w :=
    H.regularizedStageStart_eq_of_mem_Icc hw hMiddleIcc
  have hEndMiddle : H.regularizedStageEnd T w middle = w :=
    H.regularizedStageEnd_eq_of_mem_stageDomain hw hmiddle
  have hStartBelow {j : Fin (H.eventCount + 1)} (hj : j < middle) :
      H.regularizedStageStart T u j = H.regularizedStageStart T w j := by
    have hjw : H.stageEndTime j ≤ T - w ^ 2 :=
      (stageEndTime_le_time_of_lt H hj).trans hMiddleIcc.1
    have hju : H.stageEndTime j ≤ T - u ^ 2 :=
      hjw.trans (sub_le_sub_left (pow_le_pow_left₀ hu huw 2) T)
    simp only [regularizedStageStart, min_eq_right hju, min_eq_right hjw]
  have hEndAbove {j : Fin (H.eventCount + 1)} (hj : middle < j) :
      H.regularizedStageEnd T v j = H.regularizedStageEnd T w j := by
    have hwj : T - w ^ 2 ≤ H.time j :=
      hMiddleIcc.2.trans (stageEndTime_le_time_of_lt H hj)
    have hvj : T - v ^ 2 ≤ H.time j :=
      (sub_le_sub_left (pow_le_pow_left₀ hw hwv 2) T).trans hwj
    simp only [regularizedStageEnd, max_eq_right hvj, max_eq_right hwj]
  let gamma : (j : H.StageInterval first last) → ℝ → (H.stage j.val).Carrier :=
    fun j => if hNew : middle ≤ j.val then
      if hOld : j.val ≤ middle then
        (Iic w).piecewise (alpha ⟨j.val, hNew, j.property.2⟩)
          (beta ⟨j.val, j.property.1, hOld⟩)
      else alpha ⟨j.val, hNew, j.property.2⟩
    else beta ⟨j.val, j.property.1, (not_le.mp hNew).le⟩
  have hGammaAbove (j : H.StageInterval first last) (hj : middle < j.val) :
      gamma j = alpha ⟨j.val, hj.le, j.property.2⟩ := by
    simp only [gamma, dite_eq_left hj.le, dite_eq_right (not_le_of_gt hj)]
  have hGammaBelow (j : H.StageInterval first last) (hj : j.val < middle) :
      gamma j = beta ⟨j.val, j.property.1, hj.le⟩ := by
    simp only [gamma, dite_eq_right (not_le_of_gt hj)]
  have hGammaMiddle : gamma ⟨middle, hfm, hml⟩ =
      (Iic w).piecewise (alpha ⟨middle, le_rfl, hml⟩) (beta ⟨middle, hfm, le_rfl⟩) := by
    simp only [gamma, dite_eq_left le_rfl]
  have hGammaLeft (s : ℝ) (hs : s ≤ w) :
      gamma ⟨middle, hfm, hml⟩ s = alpha ⟨middle, le_rfl, hml⟩ s := by
    rw [hGammaMiddle]
    exact piecewise_eq_of_mem _ _ _ hs
  have hGammaRight (s : ℝ) (hs : w ≤ s) :
      gamma ⟨middle, hfm, hml⟩ s = beta ⟨middle, hfm, le_rfl⟩ s := by
    by_cases hsw : s = w
    · subst s
      exact (hGammaLeft w le_rfl).trans hmatch
    · rw [hGammaMiddle]
      exact piecewise_eq_of_notMem _ _ _
        (not_le.mpr (lt_of_le_of_ne hs (Ne.symm hsw)))
  have hEqAlpha : ∀ j : H.StageInterval middle last,
      EqOn (gamma ⟨j.val, hfm.trans j.property.1, j.property.2⟩) (alpha j)
        (Icc (H.regularizedStageStart T u j.val) (H.regularizedStageEnd T w j.val)) := by
    rintro ⟨j, hj⟩ s hs
    rcases eq_or_lt_of_le hj.1 with heq | hjm
    · subst j
      exact hGammaLeft s (hs.2.trans_eq hEndMiddle)
    · rw [hGammaAbove ⟨j, hfm.trans hj.1, hj.2⟩ hjm]
  have hEqBeta : ∀ j : H.StageInterval first middle,
      EqOn (gamma ⟨j.val, j.property.1, j.property.2.trans hml⟩) (beta j)
        (Icc (H.regularizedStageStart T w j.val) (H.regularizedStageEnd T v j.val)) := by
    rintro ⟨j, hj⟩ s hs
    rcases lt_or_eq_of_le hj.2 with hjm | heq
    · rw [hGammaBelow ⟨j, hj.1, hj.2.trans hml⟩ hjm]
    · subst j
      exact hGammaRight s (hStartMiddle.symm.trans_le hs.1)
  have hStartLe : H.regularizedStageStart T u middle ≤ w := by
    simpa only [hEndMiddle] using
      (H.regularizedStage_bounds hu huw hupper hmiddle ⟨middle, le_rfl, hml⟩).2.1
  have hLeEnd : w ≤ H.regularizedStageEnd T v middle := by
    simpa only [hStartMiddle] using
      (H.regularizedStage_bounds hw hwv hMiddleIcc hlower ⟨middle, hfm, le_rfl⟩).2.1
  have hGammaAC : ∀ j, Manifold.absolutelyContinuousOnInterval ThreeModel (gamma j)
      (H.regularizedStageStart T u j.val) (H.regularizedStageEnd T v j.val) := by
    rintro ⟨j, hj⟩
    rcases lt_trichotomy j middle with hjm | heq | hmj
    · rw [hGammaBelow ⟨j, hj⟩ hjm, hStartBelow hjm]
      exact hBeta ⟨j, hj.1, hjm.le⟩
    · subst j
      rw [hGammaMiddle]
      exact Manifold.absolutelyContinuousOnInterval_piecewise_Iic
        (by simpa only [hEndMiddle] using hAlpha ⟨middle, le_rfl, hml⟩)
        (by simpa only [hStartMiddle] using hBeta ⟨middle, hfm, le_rfl⟩)
        hStartLe hLeEnd hmatch
    · rw [hGammaAbove ⟨j, hj⟩ hmj, hEndAbove hmj]
      exact hAlpha ⟨j, hmj.le, hj.2⟩
  have hNodes : ∀ (i : Fin H.eventCount) (hf : first ≤ i.castSucc) (hl : i.succ ≤ last),
      ∃ z : (H.event i).old,
        z.val.val = gamma ⟨i.castSucc, hf, i.castSucc_lt_succ.le.trans hl⟩
          (Real.sqrt (T - H.time i.succ)) ∧
        (H.event i).oldOutput z = gamma ⟨i.succ, hf.trans i.castSucc_lt_succ.le, hl⟩
          (Real.sqrt (T - H.time i.succ)) := by
    intro i hf hl
    by_cases hmi : middle ≤ i.castSucc
    · obtain ⟨z, hzold, hznew⟩ := hAlphaNodes i hmi hl
      have hs := H.regularizedStageStart_castSucc_eq_event_clock hupper i hl
      have he := H.regularizedStageEnd_succ_eq_event_clock hmiddle i hmi
      have hbOld := H.regularizedStage_bounds hu huw hupper hmiddle
        ⟨i.castSucc, hmi, i.castSucc_lt_succ.le.trans hl⟩
      have hbNew := H.regularizedStage_bounds hu huw hupper hmiddle
        ⟨i.succ, hmi.trans i.castSucc_lt_succ.le, hl⟩
      have heqOld := hEqAlpha ⟨i.castSucc, hmi, i.castSucc_lt_succ.le.trans hl⟩
        (by simpa only [hs] using left_mem_Icc.mpr hbOld.2.1)
      have heqNew := hEqAlpha ⟨i.succ, hmi.trans i.castSucc_lt_succ.le, hl⟩
        (by simpa only [he] using right_mem_Icc.mpr hbNew.2.1)
      exact ⟨z, hzold.trans heqOld.symm, hznew.trans heqNew.symm⟩
    · have him : i.succ ≤ middle := by
        change i.val + 1 ≤ middle.val
        change ¬ middle.val ≤ i.val at hmi
        omega
      obtain ⟨z, hzold, hznew⟩ := hBetaNodes i hf him
      have hs := H.regularizedStageStart_castSucc_eq_event_clock hMiddleIcc i him
      have he := H.regularizedStageEnd_succ_eq_event_clock hlower i hf
      have hbOld := H.regularizedStage_bounds hw hwv hMiddleIcc hlower
        ⟨i.castSucc, hf, i.castSucc_lt_succ.le.trans him⟩
      have hbNew := H.regularizedStage_bounds hw hwv hMiddleIcc hlower
        ⟨i.succ, hf.trans i.castSucc_lt_succ.le, him⟩
      have heqOld := hEqBeta ⟨i.castSucc, hf, i.castSucc_lt_succ.le.trans him⟩
        (by simpa only [hs] using left_mem_Icc.mpr hbOld.2.1)
      have heqNew := hEqBeta ⟨i.succ, hf.trans i.castSucc_lt_succ.le, him⟩
        (by simpa only [he] using right_mem_Icc.mpr hbNew.2.1)
      exact ⟨z, hzold.trans heqOld.symm, hznew.trans heqNew.symm⟩
  have hMiddleAction :
      H.stageRegularizedExtendedAction middle T B (gamma ⟨middle, hfm, hml⟩)
        (H.regularizedStageStart T u middle) (H.regularizedStageEnd T v middle) =
      H.stageRegularizedExtendedAction middle T B (alpha ⟨middle, le_rfl, hml⟩)
          (H.regularizedStageStart T u middle) (H.regularizedStageEnd T w middle) +
        H.stageRegularizedExtendedAction middle T B (beta ⟨middle, hfm, le_rfl⟩)
          (H.regularizedStageStart T w middle) (H.regularizedStageEnd T v middle) := by
    rw [hEndMiddle, hStartMiddle]
    refine (H.stageRegularizedExtendedAction_add_of_absolutelyContinuousOnInterval
      middle T B u v w (gamma ⟨middle, hfm, hml⟩) hStartLe hLeEnd
      (hGammaAC ⟨middle, hfm, hml⟩) ?_).trans ?_
    · filter_upwards [ae_restrict_mem measurableSet_Ioo] with s hs
      exact hscalar ⟨middle, hfm, hml⟩ s hs (gamma ⟨middle, hfm, hml⟩ s)
    · apply congrArg₂ (· + ·)
      · apply H.stageRegularizedExtendedAction_congr
        intro s hs
        exact hGammaLeft s hs.2.le
      · apply H.stageRegularizedExtendedAction_congr
        intro s hs
        exact hGammaRight s hs.1.le
  let newTerm (j : H.StageInterval first last) : WithTop ℝ :=
    if hj : middle ≤ j.val then
      H.stageRegularizedExtendedAction j.val T B (alpha ⟨j.val, hj, j.property.2⟩)
        (H.regularizedStageStart T u j.val) (H.regularizedStageEnd T w j.val)
    else 0
  let oldTerm (j : H.StageInterval first last) : WithTop ℝ :=
    if hj : j.val ≤ middle then
      H.stageRegularizedExtendedAction j.val T B (beta ⟨j.val, j.property.1, hj⟩)
        (H.regularizedStageStart T w j.val) (H.regularizedStageEnd T v j.val)
    else 0
  have hPoint : ∀ j : H.StageInterval first last,
      H.stageRegularizedExtendedAction j.val T B (gamma j)
        (H.regularizedStageStart T u j.val) (H.regularizedStageEnd T v j.val) =
        newTerm j + oldTerm j := by
    rintro ⟨j, hj⟩
    rcases lt_trichotomy j middle with hjm | heq | hmj
    · simp only [newTerm, oldTerm, dite_eq_right (not_le_of_gt hjm),
        dite_eq_left hjm.le, zero_add, hGammaBelow ⟨j, hj⟩ hjm, hStartBelow hjm]
    · subst j
      simpa only [newTerm, oldTerm, dite_eq_left le_rfl] using hMiddleAction
    · simp only [newTerm, oldTerm, dite_eq_left hmj.le,
        dite_eq_right (not_le_of_gt hmj), add_zero, hGammaAbove ⟨j, hj⟩ hmj, hEndAbove hmj]
  have hNewSum : (∑ j, newTerm j) = H.regularizedExtendedAction middle last T B u w alpha := by
    let e : {j : H.StageInterval first last // middle ≤ j.val} ≃ H.StageInterval middle last :=
      { toFun := fun j => ⟨j.val.val, j.property, j.val.property.2⟩
        invFun := fun j => ⟨⟨j.val, hfm.trans j.property.1, j.property.2⟩, j.property.1⟩
        left_inv := fun _ => rfl
        right_inv := fun _ => rfl }
    change (∑ j : H.StageInterval first last, if hj : middle ≤ j.val then
      H.stageRegularizedExtendedAction j.val T B (alpha ⟨j.val, hj, j.property.2⟩)
        (H.regularizedStageStart T u j.val) (H.regularizedStageEnd T w j.val) else 0) = _
    rw [sum_dite_eq_sum_subtype]
    exact Fintype.sum_equiv e _ _ (fun _ => rfl)
  have hOldSum : (∑ j, oldTerm j) = H.regularizedExtendedAction first middle T B w v beta := by
    let e : {j : H.StageInterval first last // j.val ≤ middle} ≃ H.StageInterval first middle :=
      { toFun := fun j => ⟨j.val.val, j.val.property.1, j.property⟩
        invFun := fun j => ⟨⟨j.val, j.property.1, j.property.2.trans hml⟩, j.property.2⟩
        left_inv := fun _ => rfl
        right_inv := fun _ => rfl }
    change (∑ j : H.StageInterval first last, if hj : j.val ≤ middle then
      H.stageRegularizedExtendedAction j.val T B (beta ⟨j.val, j.property.1, hj⟩)
        (H.regularizedStageStart T w j.val) (H.regularizedStageEnd T v j.val) else 0) = _
    rw [sum_dite_eq_sum_subtype]
    exact Fintype.sum_equiv e _ _ (fun _ => rfl)
  refine ⟨gamma, hGammaAC, ?_, ?_, hNodes, ?_, hEqAlpha, hEqBeta⟩
  · apply hEqAlpha ⟨last, hml, le_rfl⟩
    have hs := H.regularizedStageStart_eq_of_mem_Icc hu hupper
    have hb := H.regularizedStage_bounds hu huw hupper hmiddle ⟨last, hml, le_rfl⟩
    simpa only [hs] using left_mem_Icc.mpr hb.2.1
  · apply hEqBeta ⟨first, le_rfl, hfm⟩
    have he := H.regularizedStageEnd_eq_of_mem_stageDomain (hw.trans hwv) hlower
    have hb := H.regularizedStage_bounds hw hwv hMiddleIcc hlower ⟨first, le_rfl, hfm⟩
    simpa only [he] using right_mem_Icc.mpr hb.2.1
  · change (∑ j : H.StageInterval first last, H.stageRegularizedExtendedAction j.val T B (gamma j)
      (H.regularizedStageStart T u j.val) (H.regularizedStageEnd T v j.val)) = _
    simp_rw [hPoint]
    rw [Finset.sum_add_distrib, hNewSum, hOldSum, hAlphaAction, hBetaAction]
    rfl

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory
