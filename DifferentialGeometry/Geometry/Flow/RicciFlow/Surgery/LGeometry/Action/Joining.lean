import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.LGeometry.Action.Basic
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.TerminalAction
import DifferentialGeometry.Analysis.Calculus.Manifold.AbsolutelyContinuous

set_option autoImplicit false
noncomputable section
open Set Function Filter Manifold MeasureTheory
open DifferentialGeometry DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.PDE.RicciFlow.Perelman
open scoped Manifold ContDiff BigOperators Topology Interval

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory
universe u
variable (H : ObservedHistory.{u})

private theorem regularizedStageEnd_eq_of_same_stage
    {first last : Fin (H.eventCount + 1)} {T w v : ℝ}
    (hw : T - w ^ 2 ∈ H.stageDomain first) (hv : T - v ^ 2 ∈ H.stageDomain first)
    (k : H.StageInterval first last) (hk : k.val ≠ first) :
    H.regularizedStageEnd T v k.val = H.regularizedStageEnd T w k.val := by
  have hfk : first < k.val := lt_of_le_of_ne k.property.1 (Ne.symm hk)
  have htime : H.stageEndTime first ≤ H.time k.val := by
    cases first using Fin.lastCases with
    | last => exact False.elim ((not_lt_of_ge (Fin.le_last _)) hfk)
    | cast i =>
      rw [H.stageEndTime_castSucc]
      exact H.time_strictMono.monotone (show i.succ ≤ k.val from hfk)
  have hwk := (H.le_stageEndTime_of_mem_stageDomain hw).trans htime
  have hvk := (H.le_stageEndTime_of_mem_stageDomain hv).trans htime
  simp only [regularizedStageEnd, max_eq_right hwk, max_eq_right hvk]

private theorem exists_regularizedC1ActionValues_of_first_stage_replacement
    (first last : Fin (H.eventCount + 1)) (hle : first ≤ last)
    {T u w v Anew B : ℝ} (hu : 0 ≤ u) (huw : u ≤ w) (hwv : w ≤ v)
    (hupper : T - u ^ 2 ∈ Icc (H.time last) (H.stageEndTime last))
    (hw : T - w ^ 2 ∈ H.stageDomain first) (hv : T - v ^ 2 ∈ H.stageDomain first)
    (p : (H.stage last).Carrier) (q : (H.stage first).Carrier)
    (α : (k : H.StageInterval first last) → ℝ → (H.stage k.val).Carrier)
    (hα : ∀ k, ContMDiff 𝓘(ℝ, ℝ) ThreeModel 1 (α k))
    (hint : ∀ k, IntervalIntegrable (H.stageRegularizedLagrangian k.val T (α k)) volume
      (H.regularizedStageStart T u k.val) (H.regularizedStageEnd T w k.val))
    (hp : α ⟨last, hle, le_rfl⟩ u = p)
    (hnode : ∀ (i : Fin H.eventCount) (hf : first ≤ i.castSucc) (hl : i.succ ≤ last),
      ∃ z : (H.event i).old,
        z.val.val = α ⟨i.castSucc, hf, i.castSucc_lt_succ.le.trans hl⟩ (Real.sqrt (T - H.time i.succ)) ∧
        (H.event i).oldOutput z = α ⟨i.succ, hf.trans i.castSucc_lt_succ.le, hl⟩ (Real.sqrt (T - H.time i.succ)))
    (hsum : (∑ k : H.StageInterval first last, H.stageRegularizedAction k.val T (α k)
      (H.regularizedStageStart T u k.val) (H.regularizedStageEnd T w k.val)) = Anew)
    (γ : ℝ → (H.stage first).Carrier) (hγ : ContMDiff 𝓘(ℝ, ℝ) ThreeModel 1 γ)
    (hγint : IntervalIntegrable (H.stageRegularizedLagrangian first T γ) volume
      (H.regularizedStageStart T u first) v)
    (hγstart : γ (H.regularizedStageStart T u first) =
      α ⟨first, le_rfl, hle⟩ (H.regularizedStageStart T u first))
    (hγend : γ v = q)
    (hγact : H.stageRegularizedAction first T γ (H.regularizedStageStart T u first) v ≤
      H.stageRegularizedAction first T (α ⟨first, le_rfl, hle⟩) (H.regularizedStageStart T u first) w + B) :
    ∃ A : ℝ, A ∈ H.regularizedC1ActionValues first last hle T u v p q ∧ A ≤ Anew + B := by
  classical
  let k₀ : H.StageInterval first last := ⟨first, le_rfl, hle⟩
  let β := Function.update α k₀ γ
  have hβ₀ : β k₀ = γ := Function.update_self _ _ _
  have hβother (k : H.StageInterval first last) (hk : k ≠ k₀) : β k = α k :=
    Function.update_of_ne hk _ _
  have hfirstendw : H.regularizedStageEnd T w first = w :=
    H.regularizedStageEnd_eq_of_mem_stageDomain (hu.trans huw) hw
  have hfirstendv : H.regularizedStageEnd T v first = v :=
    H.regularizedStageEnd_eq_of_mem_stageDomain (hu.trans (huw.trans hwv)) hv
  have hend (k : H.StageInterval first last) (hk : k ≠ k₀) :
      H.regularizedStageEnd T v k.val = H.regularizedStageEnd T w k.val :=
    H.regularizedStageEnd_eq_of_same_stage hw hv k (fun h => hk (Subtype.ext h))
  let Aval := ∑ k : H.StageInterval first last, H.stageRegularizedAction k.val T (β k)
    (H.regularizedStageStart T u k.val) (H.regularizedStageEnd T v k.val)
  refine ⟨Aval, ⟨hu, huw.trans hwv, hupper, hv, β, ?_, ?_, ?_, ?_, ?_, rfl⟩, ?_⟩
  · intro k
    by_cases hk : k = k₀
    · subst k; rw [hβ₀]; exact hγ
    · rw [hβother k hk]; exact hα k
  · intro k
    by_cases hk : k = k₀
    · subst k; rw [hβ₀]; simpa only [k₀, hfirstendv] using hγint
    · rw [hβother k hk, hend k hk]; exact hint k
  · by_cases he : first = last
    · subst last
      have hs : H.regularizedStageStart T u first = u := H.regularizedStageStart_eq_of_mem_Icc hu hupper
      have hk : (⟨first, hle, le_rfl⟩ : H.StageInterval first first) = k₀ := rfl
      change β k₀ u = p
      rw [hβ₀, ← hs]
      exact hγstart.trans (by simpa only [hs] using hp)
    · rw [hβother _ (by intro h; exact he (congrArg Subtype.val h).symm)]
      exact hp
  · rw [hβ₀]
    exact hγend
  · intro i hf hl
    obtain ⟨z, hzold, hznew⟩ := hnode i hf hl
    refine ⟨z, ?_, ?_⟩
    · by_cases hif : i.castSucc = first
      · subst first
        change z.val.val = β k₀ (Real.sqrt (T - H.time i.succ))
        rw [hβ₀]
        have hs : H.regularizedStageStart T u i.castSucc = Real.sqrt (T - H.time i.succ) :=
          H.regularizedStageStart_castSucc_eq_event_clock hupper i hl
        rw [← hs, hγstart]
        simpa only [k₀, ← hs] using hzold
      · rw [hβother _ (fun h => hif (congrArg Subtype.val h))]
        exact hzold
    · rw [hβother _ (by
        intro h
        have hh : i.succ = first := congrArg Subtype.val h
        exact (not_lt_of_ge (hh ▸ hf)) i.castSucc_lt_succ)]
      exact hznew
  · let fnew := fun k : H.StageInterval first last => H.stageRegularizedAction k.val T (β k)
      (H.regularizedStageStart T u k.val) (H.regularizedStageEnd T v k.val)
    let fold := fun k : H.StageInterval first last => H.stageRegularizedAction k.val T (α k)
      (H.regularizedStageStart T u k.val) (H.regularizedStageEnd T w k.val)
    have hpoint : ∀ k, fnew k ≤ fold k + if k = k₀ then B else 0 := by
      intro k
      by_cases hk : k = k₀
      · subst k; simp only [fnew, fold, hβ₀, k₀, hfirstendv, hfirstendw, ite_true]; exact hγact
      · simp only [fnew, fold, hβother k hk, hend k hk, ite_eq_right hk, add_zero, le_refl]
    have hh := Finset.sum_le_sum (s := Finset.univ) (fun k _ => hpoint k)
    rw [Finset.sum_add_distrib] at hh
    have hBsum : (∑ k : H.StageInterval first last, if k = k₀ then B else 0) = B := by simp
    rw [hBsum] at hh
    exact hh.trans_eq (congrArg (fun z => z + B) hsum)

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.OrientedThreeStage.IncomingSlab
universe u
variable {P : OrientedThreeStage.{u}} {a s : ℝ} {G : P.IncomingSlab a s}

private theorem TerminalLimitMetric.exists_contMDiff_action_join_lt
    (L : G.TerminalLimitMetric) {T u w v : ℝ} (hu : 0 ≤ u) (huw : u ≤ w) (hwv : w < v)
    (hupper : T - u ^ 2 ≤ s) (hlower : a ≤ T - v ^ 2)
    (α β : ℝ → P.Carrier) (hα : ContMDiff 𝓘(ℝ, ℝ) ThreeModel 1 α)
    (hβ : ContMDiff 𝓘(ℝ, ℝ) ThreeModel 1 β) (hnode : α w = β w)
    (hterminal : T - u ^ 2 = s → α u ∈ G.terminalRegularOpen)
    (hαint : IntervalIntegrable (lRegularizedLagrangian G.flow T α) volume u w)
    (hβint : IntervalIntegrable (lRegularizedLagrangian G.flow T β) volume w v)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ γ : ℝ → P.Carrier, ContMDiff 𝓘(ℝ, ℝ) ThreeModel 1 γ ∧ γ u = α u ∧ γ v = β v ∧
      IntervalIntegrable (lRegularizedLagrangian G.flow T γ) volume u v ∧
      lRegularizedAction G.flow T γ u v <
        lRegularizedAction G.flow T α u w + lRegularizedAction G.flow T β w v + ε := by
  have huv : u < v := huw.trans_lt hwv
  let : SecondCountableTopology P.Carrier := ChartedSpace.secondCountable_of_sigmaCompact ThreeSpace P.Carrier
  let : TopologicalSpace.MetrizableSpace P.Carrier := Manifold.metrizableSpace ThreeModel P.Carrier
  let : MetricSpace P.Carrier := TopologicalSpace.metrizableSpaceMetric P.Carrier
  rcases lt_or_eq_of_le hupper with hupper | hTu
  · have hclock (t : ℝ) (ht : t ∈ Icc u v) : T - t ^ 2 ∈ (RealTimeInterval.closedOpen a s G.lt).carrier := by
      change a ≤ T - t ^ 2 ∧ T - t ^ 2 < s
      constructor
      · nlinarith [sq_le_sq₀ (hu.trans ht.1) (hu.trans huv.le) |>.2 ht.2]
      · nlinarith [sq_le_sq₀ hu (hu.trans ht.1) |>.2 ht.1]
    obtain ⟨γ, hγ, hγu, hγv, hact⟩ := exists_lRegularizedAction_join_lt_on_carrier_of_contMDiff
      G.flow G.equation.smoothMetric ⟨G.equation.scalarCont⟩ T u w v huw hwv.le α β hα hβ hnode hclock hε
    have hc := lRegularizedLagrangian_continuousOn_carrier G.flow G.equation γ hγ
    exact ⟨γ, hγ, hγu, hγv,
      (hc.comp (f := fun r : ℝ => (T, r)) (continuous_const.prodMk continuous_id).continuousOn hclock).intervalIntegrable_of_Icc huv.le,
      hact⟩
  · let η := (Iic w).piecewise α β
    have hηac : Manifold.absolutelyContinuousOnInterval ThreeModel η u v := by
      apply Manifold.absolutelyContinuousOnInterval_piecewise_Iic
        (Manifold.absolutelyContinuousOnInterval_of_contMDiffOn hα.contMDiffOn)
        (Manifold.absolutelyContinuousOnInterval_of_contMDiffOn hβ.contMDiffOn) huw hwv.le hnode
    have hleft : EqOn (lRegularizedLagrangian G.flow T η) (lRegularizedLagrangian G.flow T α) (uIoo u w) := by
      intro t ht
      rw [uIoo_of_le huw] at ht
      have he : η =ᶠ[𝓝 t] α := by
        filter_upwards [Iio_mem_nhds ht.2] with z hz
        exact ite_eq_left (show z ≤ w from (show z < w from hz).le)
      have hv := he.self_of_nhds
      have hd := he.mfderiv_eq (I := 𝓘(ℝ, ℝ)) (I' := ThreeModel)
      unfold lRegularizedLagrangian lVelocity
      rw [hd, hv]
      rfl
    have hright : EqOn (lRegularizedLagrangian G.flow T η) (lRegularizedLagrangian G.flow T β) (uIoo w v) := by
      intro t ht
      rw [uIoo_of_le hwv.le] at ht
      have he : η =ᶠ[𝓝 t] β := by
        filter_upwards [Ioi_mem_nhds ht.1] with z hz
        exact ite_eq_right (not_le.mpr (show w < z from hz))
      have hv := he.self_of_nhds
      have hd := he.mfderiv_eq (I := 𝓘(ℝ, ℝ)) (I' := ThreeModel)
      unfold lRegularizedLagrangian lVelocity
      rw [hd, hv]
      rfl
    have hintLeft := hαint.congr_uIoo hleft.symm
    have hintRight := hβint.congr_uIoo hright.symm
    have hηu : η u = α u := ite_eq_left huw
    have hηv : η v = β v := ite_eq_right (not_le.mpr hwv)
    obtain ⟨γ, hγ, hγu, hγv, hγint, hact⟩ :=
      L.exists_contMDiff_action_lt_of_terminal_curve hu huv hTu hlower hηac
        (hηu ▸ hterminal hTu) (hintLeft.trans hintRight) hε
    refine ⟨γ, hγ, hγu.trans hηu, hγv.trans hηv, hγint, ?_⟩
    have hsplit := lRegularizedAction_add G.flow T η u w v hintLeft hintRight
    have hleftAct : lRegularizedAction G.flow T η u w = lRegularizedAction G.flow T α u w :=
      intervalIntegral.integral_congr_uIoo hleft
    have hrightAct : lRegularizedAction G.flow T η w v = lRegularizedAction G.flow T β w v :=
      intervalIntegral.integral_congr_uIoo hright
    rw [← hsplit, hleftAct, hrightAct] at hact
    exact hact

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.OrientedThreeStage.IncomingSlab

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory
universe u
variable (H : ObservedHistory.{u})

private theorem regularizedStageStart_time
    (T u : ℝ) (j : Fin (H.eventCount + 1)) :
    T - (H.regularizedStageStart T u j) ^ 2 = min (T - u ^ 2) (H.stageEndTime j) := by
  rw [regularizedStageStart, Real.sq_sqrt]
  · ring
  · have := min_le_left (T - u ^ 2) (H.stageEndTime j)
    nlinarith [sq_nonneg u]

theorem exists_regularizedC1ActionValues_join_same_stage
    (first last : Fin (H.eventCount + 1)) (hle : first ≤ last)
    {T u w v Anew ε : ℝ} (hwv : w < v) (hε : 0 < ε)
    (hupper : T - u ^ 2 ∈ H.stageDomain last)
    (hlower : T - v ^ 2 ∈ H.stageDomain first)
    (p : (H.stage last).Carrier) (y q : (H.stage first).Carrier)
    (hnew : Anew ∈ H.regularizedC1ActionValues first last hle T u w p y)
    (β : ℝ → (H.stage first).Carrier) (hβ : ContMDiff 𝓘(ℝ, ℝ) ThreeModel 1 β)
    (hβw : β w = y) (hβv : β v = q)
    (hβint : IntervalIntegrable (H.stageRegularizedLagrangian first T β) volume w v) :
    ∃ A : ℝ, A ∈ H.regularizedC1ActionValues first last hle T u v p q ∧
      A ≤ Anew + H.stageRegularizedAction first T β w v + ε := by
  classical
  obtain ⟨hu, huw, huppercc, hmiddle, α, hα, hint, hp, hy, hnode, hsum⟩ := hnew
  let k₀ : H.StageInterval first last := ⟨first, le_rfl, hle⟩
  let a₀ := H.regularizedStageStart T u first
  have hab : a₀ ≤ w := (H.regularizedStage_bounds hu huw huppercc hmiddle k₀).2.1.trans_eq
    (H.regularizedStageEnd_eq_of_mem_stageDomain (hu.trans huw) hmiddle)
  have ha₀ : 0 ≤ a₀ := Real.sqrt_nonneg _
  have halphaInt : IntervalIntegrable (H.stageRegularizedLagrangian first T (α k₀)) volume a₀ w := by
    simpa only [k₀, H.regularizedStageEnd_eq_of_mem_stageDomain (hu.trans huw) hmiddle] using hint k₀
  have hmatch : α k₀ w = β w := hy.trans hβw.symm
  have hjoin : ∃ γ : ℝ → (H.stage first).Carrier,
      ContMDiff 𝓘(ℝ, ℝ) ThreeModel 1 γ ∧ γ a₀ = α k₀ a₀ ∧ γ v = β v ∧
      IntervalIntegrable (H.stageRegularizedLagrangian first T γ) volume a₀ v ∧
      H.stageRegularizedAction first T γ a₀ v <
        H.stageRegularizedAction first T (α k₀) a₀ w + H.stageRegularizedAction first T β w v + ε := by
    cases first using Fin.lastCases with
    | cast i =>
      have hterminal : T - a₀ ^ 2 = H.time i.succ → α k₀ a₀ ∈ (H.event i).incoming.terminalRegularOpen := by
        intro hterm
        by_cases he : i.castSucc = last
        · subst last
          have hs : a₀ = u := H.regularizedStageStart_eq_of_mem_Icc hu huppercc
          have hstrict : T - u ^ 2 < H.time i.succ := by
            have hh : T - u ^ 2 ∈ Ico (H.time i.castSucc) (H.time i.succ) := by
              simpa only [stageDomain, Fin.lastCases_castSucc] using hupper
            exact hh.2
          exact False.elim ((not_lt_of_ge (by rw [← hterm, hs])) hstrict)
        · have hi : i.succ ≤ last := by
            exact Nat.succ_le_of_lt (show i.val < last.val from (show i.castSucc < last from lt_of_le_of_ne hle he))
          obtain ⟨z, hz, _⟩ := hnode i le_rfl hi
          have hs : a₀ = Real.sqrt (T - H.time i.succ) :=
            H.regularizedStageStart_castSucc_eq_event_clock huppercc i hi
          have hzreg := (H.event i).oldTerminal z |>.property
          rw [(H.event i).oldTerminal_eq] at hzreg
          simpa only [k₀, hs, hz] using hzreg
      have htimeupper : T - a₀ ^ 2 ≤ H.time i.succ := by
        dsimp only [a₀]
        rw [H.regularizedStageStart_time, H.stageEndTime_castSucc]
        exact min_le_right _ _
      have htimelower : H.time i.castSucc ≤ T - v ^ 2 := H.time_le_of_mem_stageDomain hlower
      obtain ⟨γ,hγ,hγa,hγv,hγint,hact⟩ := (H.event i).terminal.exists_contMDiff_action_join_lt
        ha₀ hab hwv htimeupper htimelower (α k₀) β (hα k₀) hβ hmatch hterminal
        (by simpa only [funext (H.stageRegularizedLagrangian_castSucc i T _)] using halphaInt)
        (by simpa only [funext (H.stageRegularizedLagrangian_castSucc i T _)] using hβint) hε
      exact ⟨γ,hγ,hγa,hγv,by simpa only [funext (H.stageRegularizedLagrangian_castSucc i T _)] using hγint,
        by simpa only [H.stageRegularizedAction_castSucc] using hact⟩
    | last =>
      have hlast : last = Fin.last H.eventCount := le_antisymm (Fin.le_last _) hle
      subst last
      have haeq : a₀ = u := H.regularizedStageStart_eq_of_mem_Icc hu huppercc
      have hTv : H.time (Fin.last H.eventCount) ≤ T - v ^ 2 := H.time_le_of_mem_stageDomain hlower
      have hfinal : H.time (Fin.last H.eventCount) < H.horizon := by
        have hTu := H.le_stageEndTime_of_mem_stageDomain hupper
        rw [H.stageEndTime_last] at hTu
        have huv : u < v := huw.trans_lt hwv
        nlinarith [sq_lt_sq₀ hu (hu.trans huv.le) |>.2 huv]
      let : SecondCountableTopology (H.stage (Fin.last H.eventCount)).Carrier :=
        ChartedSpace.secondCountable_of_sigmaCompact ThreeSpace _
      let : TopologicalSpace.MetrizableSpace (H.stage (Fin.last H.eventCount)).Carrier :=
        Manifold.metrizableSpace ThreeModel _
      let : MetricSpace (H.stage (Fin.last H.eventCount)).Carrier := TopologicalSpace.metrizableSpaceMetric _
      have hclock (t : ℝ) (ht : t ∈ Icc a₀ v) :
          T - t ^ 2 ∈ (RealTimeInterval.closed (H.time (Fin.last H.eventCount)) H.horizon hfinal.le).carrier := by
        rw [haeq] at ht
        have hTu := H.le_stageEndTime_of_mem_stageDomain hupper
        rw [H.stageEndTime_last] at hTu
        constructor <;> nlinarith [sq_le_sq₀ (hu.trans ht.1) (hu.trans (huw.trans hwv.le)) |>.2 ht.2,
          sq_le_sq₀ hu (hu.trans ht.1) |>.2 ht.1]
      obtain ⟨γ,hγ,hγa,hγv,hact⟩ := exists_lRegularizedAction_join_lt_on_carrier_of_contMDiff
        (H.finalSlab hfinal).flow (H.finalSlab hfinal).equation.smoothMetric
        ⟨(H.finalSlab hfinal).equation.scalarCont⟩ T a₀ w v hab hwv.le
        (α k₀) β (hα k₀) hβ hmatch hclock hε
      have hc := lRegularizedLagrangian_continuousOn_carrier (H.finalSlab hfinal).flow
        (H.finalSlab hfinal).equation γ hγ
      have hi : IntervalIntegrable (lRegularizedLagrangian (H.finalSlab hfinal).flow T γ) volume a₀ v :=
        (hc.comp (f := fun r : ℝ => (T,r))
        (continuous_const.prodMk continuous_id).continuousOn hclock).intervalIntegrable_of_Icc (hab.trans hwv.le)
      exact ⟨γ,hγ,hγa,hγv,by simpa only [funext (H.stageRegularizedLagrangian_last hfinal T γ)] using hi,
        by simpa only [H.stageRegularizedAction_last hfinal] using hact⟩
  obtain ⟨γ,hγ,hγstart,hγend,hγint,hγact⟩ := hjoin
  obtain ⟨A,hA,hAbound⟩ := H.exists_regularizedC1ActionValues_of_first_stage_replacement first last hle
    (B := H.stageRegularizedAction first T β w v + ε)
    hu huw hwv.le huppercc hmiddle hlower p q α hα hint hp hnode hsum γ hγ hγint hγstart
    (hγend.trans hβv) (by linarith only [hγact.le])
  exact ⟨A,hA,by linarith only [hAbound]⟩

theorem exists_regularizedC1ActionValues_join
    (first middle last : Fin (H.eventCount + 1)) (hfm : first ≤ middle) (hml : middle ≤ last)
    {T u w v Anew Aold ε : ℝ} (hwv : w < v) (hε : 0 < ε)
    (hupper : T - u ^ 2 ∈ H.stageDomain last)
    (hmiddle : T - w ^ 2 ∈ Ioo (H.time middle) (H.stageEndTime middle))
    (p : (H.stage last).Carrier) (y : (H.stage middle).Carrier) (q : (H.stage first).Carrier)
    (hnew : Anew ∈ H.regularizedC1ActionValues middle last hml T u w p y)
    (hold : Aold ∈ H.regularizedC1ActionValues first middle hfm T w v y q) :
    ∃ A : ℝ, A ∈ H.regularizedC1ActionValues first last (hfm.trans hml) T u v p q ∧
      A ≤ Anew + Aold + ε := by
  have hu := hnew.1
  have huw := hnew.2.1
  have huppercc := hnew.2.2.1
  have hlower := hold.2.2.2.1
  by_cases hsame : first = middle
  · subst middle
    obtain ⟨_, _, _, _, β, hβ, hβint, hβw, hβv, hβact⟩ :=
      (H.mem_regularizedC1ActionValues_self first y q).mp hold
    obtain ⟨A,hA,hbound⟩ := H.exists_regularizedC1ActionValues_join_same_stage first last hml hwv hε
      hupper hlower p y q hnew β hβ hβw hβv hβint
    exact ⟨A,hA,by rw [hβact] at hbound; exact hbound⟩
  · have hfmlt : first < middle := lt_of_le_of_ne hfm hsame
    cases middle using Fin.cases with
    | zero => exact False.elim ((not_lt_of_ge (Fin.zero_le first)) hfmlt)
    | succ i =>
      have hfi : first ≤ i.castSucc := by
        change first.val ≤ i.val
        exact Nat.lt_succ_iff.mp hfmlt
      obtain ⟨z,Alo,Ahi,hlo,hhi,hsum⟩ :=
        (H.mem_regularizedC1ActionValues_split_at_event hfm i hfi le_rfl hold.1 hold.2.1
          hold.2.2.1 hlower y q).mp hold
      obtain ⟨_, _, _, _, β, hβ, hβint, hβw, hβend, hβact⟩ :=
        (H.mem_regularizedC1ActionValues_self i.succ y ((H.event i).oldOutput z)).mp hhi
      have hw0 : 0 ≤ w := hu.trans huw
      have hwt : w < Real.sqrt (T - H.time i.succ) := by
        apply (Real.lt_sqrt hw0).mpr
        linarith [hmiddle.1]
      have hclock : T - (Real.sqrt (T - H.time i.succ)) ^ 2 = H.time i.succ := by
        rw [Real.sq_sqrt]
        · ring
        · linarith [hmiddle.1, sq_nonneg w]
      have hseam : T - (Real.sqrt (T - H.time i.succ)) ^ 2 ∈ H.stageDomain i.succ := by
        rw [hclock]
        exact H.time_mem_stageDomain i.succ
      obtain ⟨Ahi',hhiNew,hbound⟩ := H.exists_regularizedC1ActionValues_join_same_stage i.succ last hml
        hwt hε hupper hseam p y ((H.event i).oldOutput z) hnew β hβ hβw hβend hβint
      rw [hβact] at hbound
      refine ⟨Alo + Ahi', ?_, by linarith only [hbound,hsum]⟩
      apply (H.mem_regularizedC1ActionValues_split_at_event (hfm.trans hml) i hfi
        hml hu (huw.trans hwv.le) huppercc hlower p q).mpr
      exact ⟨z,Alo,Ahi',hlo,hhiNew,rfl⟩

theorem exists_regularizedC1ActionValues_join_common_curve
    {X : Type u} [TopologicalSpace X] [ChartedSpace ThreeSpace X]
    [IsManifold ThreeModel ∞ X] [T2Space X]
    (first middle last : Fin (H.eventCount + 1)) (hfm : first ≤ middle) (hml : middle ≤ last)
    {T u w v Anew Aconnector ε : ℝ} (hwv : w < v) (hε : 0 < ε)
    (hupper : T - u ^ 2 ∈ H.stageDomain last)
    (hmiddle : T - w ^ 2 ∈ Ioo (H.time middle) (H.stageEndTime middle))
    (hlower : T - v ^ 2 ∈ H.stageDomain first)
    (p : (H.stage last).Carrier) (y : (H.stage middle).Carrier) (q : (H.stage first).Carrier)
    (hnew : Anew ∈ H.regularizedC1ActionValues middle last hml T u w p y)
    (f : (j : H.StageInterval first middle) → X → (H.stage j.val).Carrier)
    (hf : ∀ j, IsLocalDiffeomorph ThreeModel ThreeModel ∞ (f j))
    (hcross : ∀ (i : Fin H.eventCount) (hi : first ≤ i.castSucc) (hl : i.succ ≤ middle), ∀ z : X,
      (H.event i).RegularCrossing
        (f ⟨i.castSucc, hi, i.castSucc_lt_succ.le.trans hl⟩ z)
        (f ⟨i.succ, hi.trans i.castSucc_lt_succ.le, hl⟩ z))
    {D : RealTimeInterval} (S : SolutionOn (I := ThreeModel) (M := X) D) (hS : IsSolutionOn S)
    (htime : ∀ t ∈ Icc w v, T - t ^ 2 ∈ D.carrier)
    (hmetric : ∀ j : H.StageInterval first middle,
      ∀ t ∈ Ioo (H.regularizedStageStart T w j.val) (H.regularizedStageEnd T v j.val),
      S.base.metric (T - t ^ 2) = localPullMetric (H.stageMetric j.val (T - t ^ 2)) (f j) (hf j))
    (α : ℝ → X) (hα : ContMDiff 𝓘(ℝ, ℝ) ThreeModel 1 α)
    (hαw : f ⟨middle,hfm,le_rfl⟩ (α w) = y) (hαv : f ⟨first,le_rfl,hfm⟩ (α v) = q)
    (hαact : lRegularizedAction S T α w v ≤ Aconnector) :
    ∃ A : ℝ, A ∈ H.regularizedC1ActionValues first last (hfm.trans hml) T u v p q ∧
      A ≤ Anew + Aconnector + ε := by
  have hw : 0 ≤ w := hnew.1.trans hnew.2.1
  have hold := H.action_mem_regularizedC1ActionValues_of_common_curve first middle hfm
    f hf hcross S hS T hw hwv.le ⟨hmiddle.1.le,hmiddle.2.le⟩ hlower htime hmetric α hα
  rw [hαw,hαv] at hold
  obtain ⟨A,hA,hbound⟩ := H.exists_regularizedC1ActionValues_join first middle last hfm hml
    hwv hε hupper hmiddle p y q hnew hold
  exact ⟨A,hA,by linarith only [hbound,hαact]⟩

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory
