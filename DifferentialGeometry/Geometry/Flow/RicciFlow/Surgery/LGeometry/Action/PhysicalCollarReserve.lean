import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.LGeometry.Action.AbsoluteContinuity
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.LGeometry.Geodesic.SmoothTail
import DifferentialGeometry.Topology.Manifold.SmoothInterval
import Mathlib.Algebra.BigOperators.Fin
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.LGeometry.Action.SmallPrefixTrace

set_option autoImplicit false

noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory

open Set Filter _root_.MeasureTheory
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.PDE.RicciFlow.Perelman
open scoped _root_.Manifold ContDiff _root_.Topology BigOperators Interval

universe u uPositiveStages

private theorem exists_positive_regularized_stage_interval
    (H : ObservedHistory.{uPositiveStages})
    (first last : Fin (H.eventCount + 1)) (hle : first ≤ last)
    {T v : ℝ} (hv : 0 < v)
    (hupper : T ∈ Icc (H.time last) (H.stageEndTime last))
    (hpast : T - v ^ 2 ∈ Ioo (H.time first) (H.stageEndTime first)) :
    ∃ lastPos : Fin (H.eventCount + 1),
      first ≤ lastPos ∧ lastPos ≤ last ∧
      (lastPos = last ↔ H.time last < T) ∧
      (T = H.time last → ∃ i : Fin H.eventCount, last = i.succ ∧ lastPos = i.castSucc) ∧
      H.regularizedStageStart T 0 lastPos = 0 ∧
      H.regularizedStageEnd T v first = v ∧
      (∀ j : Fin (H.eventCount + 1), first ≤ j → j ≤ lastPos →
        H.regularizedStageStart T 0 j < H.regularizedStageEnd T v j) ∧
      (∀ j : Fin (H.eventCount + 1), j ≤ last → lastPos < j →
        j = last ∧ H.regularizedStageStart T 0 j = 0 ∧ H.regularizedStageEnd T v j = 0) ∧
      (∀ i : Fin H.eventCount, i.succ ≤ last →
        (0 < Real.sqrt (T - H.time i.succ) ↔ i.succ ≤ lastPos)) := by
  have hfirstT : H.time first < T :=
    hpast.1.trans_le (sub_le_self _ (sq_nonneg v))
  obtain ⟨lastPos, hfirstPos, hposLast, hcharacter, hcases⟩ :
      ∃ lastPos : Fin (H.eventCount + 1), first ≤ lastPos ∧ lastPos ≤ last ∧
        (∀ j : Fin (H.eventCount + 1), j ≤ last →
          (j ≤ lastPos ↔ H.time j < T)) ∧
        (lastPos = last ∨ ∃ i : Fin H.eventCount,
          last = i.succ ∧ lastPos = i.castSucc ∧ T = H.time last) := by
    by_cases hpole : T = H.time last
    · have hfirstLast : first < last :=
        H.time_strictMono.lt_iff_lt.mp (hfirstT.trans_eq hpole)
      cases last using Fin.cases with
      | zero => exact False.elim ((not_lt_of_ge (Fin.zero_le first)) hfirstLast)
      | succ i =>
        refine ⟨i.castSucc, Fin.le_castSucc_iff.mpr hfirstLast, i.castSucc_le_succ, ?_,
          Or.inr ⟨i, rfl, rfl, hpole⟩⟩
        intro j _
        rw [hpole, H.time_strictMono.lt_iff_lt]
        exact Fin.le_castSucc_iff
    · have hlastT : H.time last < T := lt_of_le_of_ne hupper.1 (Ne.symm hpole)
      refine ⟨last, hle, le_rfl, ?_, Or.inl rfl⟩
      intro j hj
      exact iff_of_true hj ((H.time_strictMono.monotone hj).trans_lt hlastT)
  have hposT : H.time lastPos < T := (hcharacter lastPos hposLast).mp le_rfl
  have hlastStart : H.regularizedStageStart T 0 last = 0 :=
    H.regularizedStageStart_eq_of_mem_Icc (show (0 : ℝ) ≤ 0 from le_rfl)
      (by simpa only [zero_pow (by decide : (2 : ℕ) ≠ 0), sub_zero] using hupper)
  have hlastEq : lastPos = last ↔ H.time last < T := by
    constructor
    · intro heq
      simpa only [heq] using hposT
    · intro ht
      exact le_antisymm hposLast ((hcharacter last le_rfl).mpr ht)
  have hpolePred (hpole : T = H.time last) :
      ∃ i : Fin H.eventCount, last = i.succ ∧ lastPos = i.castSucc := by
    rcases hcases with heq | ⟨i, hilast, hipos, _⟩
    · exact False.elim ((hlastEq.mp heq).ne hpole.symm)
    · exact ⟨i, hilast, hipos⟩
  have hposStart : H.regularizedStageStart T 0 lastPos = 0 := by
    rcases hcases with heq | ⟨i, hilast, hipos, hpole⟩
    · simpa only [heq] using hlastStart
    · have htime : H.time i.succ = T := by simpa only [hilast] using hpole.symm
      simp only [hipos, regularizedStageStart, zero_pow (by decide : (2 : ℕ) ≠ 0), sub_zero,
        H.stageEndTime_castSucc, htime, min_self, sub_self, Real.sqrt_zero]
  have hfirstEnd : H.regularizedStageEnd T v first = v :=
    H.regularizedStageEnd_eq_of_mem_stageDomain hv.le (H.mem_stageDomain_of_mem_Ioo hpast)
  refine ⟨lastPos, hfirstPos, hposLast, hlastEq, hpolePred, hposStart, hfirstEnd, ?_, ?_, ?_⟩
  · intro j hfj hjpos
    have hjlast : j ≤ last := hjpos.trans hposLast
    have hjT : H.time j < T := (hcharacter j hjlast).mp hjpos
    have hstage : H.time j < H.stageEndTime j := by
      cases j using Fin.lastCases with
      | last =>
        have hlast : last = Fin.last H.eventCount := le_antisymm (Fin.le_last last) hjlast
        simpa only [hlast] using hjT.trans_le hupper.2
      | cast i =>
        simpa only [H.stageEndTime_castSucc] using H.time_strictMono i.castSucc_lt_succ
    have hpastEnd : T - v ^ 2 < H.stageEndTime j :=
      hpast.2.trans_le (H.stageEndTime_mono hfj)
    have hgap : max (T - v ^ 2) (H.time j) < min T (H.stageEndTime j) :=
      max_lt (lt_min (sub_lt_self T (sq_pos_of_pos hv)) hpastEnd) (lt_min hjT hstage)
    have hsqrt := Real.sqrt_lt_sqrt (sub_nonneg.mpr (min_le_left T (H.stageEndTime j)))
      (sub_lt_sub_left hgap T)
    simpa only [regularizedStageStart, regularizedStageEnd, zero_pow (by decide : (2 : ℕ) ≠ 0), sub_zero] using hsqrt
  · intro j hjlast hposj
    have hnot : ¬H.time j < T := fun h => (not_le_of_gt hposj) ((hcharacter j hjlast).mpr h)
    have hjT : H.time j = T := le_antisymm
      ((H.time_strictMono.monotone hjlast).trans hupper.1) (le_of_not_gt hnot)
    have hlastj : last ≤ j := H.time_strictMono.le_iff_le.mp (hupper.1.trans_eq hjT.symm)
    have heq : j = last := le_antisymm hjlast hlastj
    refine ⟨heq, ?_, ?_⟩
    · simpa only [heq] using hlastStart
    · simp only [regularizedStageEnd, hjT, max_eq_right (sub_le_self T (sq_nonneg v)),
        sub_self, Real.sqrt_zero]
  · intro i hilast
    rw [Real.sqrt_pos, sub_pos]
    exact (hcharacter i.succ hilast).symm


private theorem exists_smooth_terminal_stage_piece
    (H : ObservedHistory.{u}) (first last : Fin (H.eventCount + 1)) (hle : first ≤ last)
    {T B v : ℝ} (hv : 0 < v)
    (hupper : T ∈ Icc (H.time last) (H.stageEndTime last))
    (hpast : T - v ^ 2 ∈ Ioo (H.time first) (H.stageEndTime first))
    (hscalar : ∀ j : H.StageInterval first last,
      ∀ r ∈ Ioo (H.regularizedStageStart T 0 j.val) (H.regularizedStageEnd T v j.val),
      ∀ x : (H.stage j.val).Carrier, -B ≤ metricScalarAt (H.stageMetric j.val (T - r ^ 2)) x)
    (gamma : (j : H.StageInterval first last) → ℝ → (H.stage j.val).Carrier)
    (hgammaAC : ∀ j, Manifold.absolutelyContinuousOnInterval ThreeModel (gamma j)
      (H.regularizedStageStart T 0 j.val) (H.regularizedStageEnd T v j.val))
    (hgammaInt : ∀ j, IntervalIntegrable (H.stageRegularizedLagrangian j.val T (gamma j)) volume
      (H.regularizedStageStart T 0 j.val) (H.regularizedStageEnd T v j.val))
    (hgammaNodes : ∀ (i : Fin H.eventCount) (hf : first ≤ i.castSucc) (hl : i.succ ≤ last),
      ∃ z : (H.event i).old,
        z.val.val = gamma ⟨i.castSucc, hf, i.castSucc_le_succ.trans hl⟩
          (Real.sqrt (T - H.time i.succ)) ∧
        (H.event i).oldOutput z = gamma ⟨i.succ, hf.trans i.castSucc_le_succ, hl⟩
          (Real.sqrt (T - H.time i.succ)))
    (hmin : H.regularizedExtendedAction first last T B 0 v gamma =
      H.regularizedCost first last hle T B 0 v
        (gamma ⟨last, hle, le_rfl⟩ 0) (gamma ⟨first, le_rfl, hle⟩ v))
    (hC1 : ContMDiffAt 𝓘(ℝ, ℝ) ThreeModel 1 (gamma ⟨first, le_rfl, hle⟩) v) :
    ∃ (D : RealTimeInterval)
      (S : SolutionOn (I := ThreeModel) (M := (H.stage first).Carrier) D),
      IsSolutionOn S ∧
      (∀ t, S.base.metric t = H.stageMetric first t) ∧
      (∀ (eta : ℝ → (H.stage first).Carrier) (r : ℝ),
        H.stageRegularizedLagrangian first T eta r = lRegularizedLagrangian S T eta r) ∧
      (∀ (eta : ℝ → (H.stage first).Carrier) (c d : ℝ),
        H.stageRegularizedAction first T eta c d = lRegularizedAction S T eta c d) ∧
      T - v ^ 2 ∈ D.regular ∧
      ∃ cTail b lo hi : ℝ,
        cTail ∈ Ioo (H.regularizedStageStart T 0 first) v ∧
        max cTail ((H.regularizedStageStart T 0 first +
          H.regularizedStageEnd T v first) / 2) < b ∧ b < v ∧ 0 < b ∧
        lo < b ∧ v < hi ∧
        (∀ r ∈ Ioo lo hi, T - r ^ 2 ∈ D.regular) ∧
        ∃ beta : ℝ → (H.stage first).Carrier,
          ContMDiff 𝓘(ℝ, ℝ) ThreeModel ∞ beta ∧
          IsLRegularizedGeodesicOn S T beta (Icc b v) ∧
          EqOn beta (gamma ⟨first, le_rfl, hle⟩) (Icc b v) ∧
          beta =ᶠ[𝓝 b] gamma ⟨first, le_rfl, hle⟩ ∧
          beta v = gamma ⟨first, le_rfl, hle⟩ v ∧
          lVelocity (I := ThreeModel) beta v =
            lVelocity (I := ThreeModel) (gamma ⟨first, le_rfl, hle⟩) v ∧
          lRegularizedAction S T beta b v =
            H.stageRegularizedAction first T (gamma ⟨first, le_rfl, hle⟩) b v := by
  have hpastD := H.mem_stageDomain_of_mem_Ioo hpast
  have hupper0 : T - (0 : ℝ) ^ 2 ∈ Icc (H.time last) (H.stageEndTime last) := by
    simpa only [zero_pow two_ne_zero, sub_zero] using hupper
  have hend : H.regularizedStageEnd T v first = v :=
    H.regularizedStageEnd_eq_of_mem_stageDomain hv.le hpastD
  have hstartV : H.regularizedStageStart T 0 first < v := by
    have hg : T - v ^ 2 < min T (H.stageEndTime first) :=
      lt_min (sub_lt_self T (sq_pos_of_pos hv)) hpast.2
    have hs := Real.sqrt_lt_sqrt
      (sub_nonneg.mpr (min_le_left T (H.stageEndTime first)))
      (show T - min T (H.stageEndTime first) < v ^ 2 by linarith)
    simpa only [regularizedStageStart, zero_pow two_ne_zero, sub_zero,
      Real.sqrt_sq_eq_abs, abs_of_pos hv] using hs
  obtain ⟨D, S, hS, hmetric, hlag, hregv, hgeo⟩ :
      ∃ (D : RealTimeInterval)
        (S : SolutionOn (I := ThreeModel) (M := (H.stage first).Carrier) D),
        IsSolutionOn S ∧
        (∀ t, S.base.metric t = H.stageMetric first t) ∧
        (∀ (eta : ℝ → (H.stage first).Carrier) (r : ℝ),
          H.stageRegularizedLagrangian first T eta r = lRegularizedLagrangian S T eta r) ∧
        T - v ^ 2 ∈ D.regular ∧
        IsLRegularizedGeodesicOn S T (gamma ⟨first, le_rfl, hle⟩)
          (Ioo (H.regularizedStageStart T 0 first) (H.regularizedStageEnd T v first)) := by
    cases first using Fin.lastCases with
    | last =>
      have hfinal : H.time (Fin.last H.eventCount) < H.horizon := by
        simpa only [H.stageEndTime_last] using hpast.1.trans hpast.2
      have hlast : last = Fin.last H.eventCount := le_antisymm (Fin.le_last last) hle
      subst last
      refine ⟨_, (H.finalSlab hfinal).flow, (H.finalSlab hfinal).equation, ?_,
        H.stageRegularizedLagrangian_last hfinal T, ?_, ?_⟩
      · intro t
        simp only [stageMetric, Fin.lastCases_last, dite_eq_left hfinal]
      · simpa only [RealTimeInterval.closed, RealTimeInterval.regular,
          H.stageEndTime_last] using hpast
      · exact H.regularizedGeodesicOn_final_stage_of_regularizedExtendedAction_eq_regularizedCost
          (Fin.last H.eventCount) hfinal le_rfl hv.le
          (by simpa only [H.stageEndTime_last] using hupper0) hpastD hscalar gamma
          hgammaAC hgammaInt (fun i hf => hgammaNodes i hf (Fin.le_last _)) hmin
    | cast i =>
      refine ⟨_, (H.event i).incoming.flow, (H.event i).incoming.equation, ?_,
        H.stageRegularizedLagrangian_castSucc i T, ?_, ?_⟩
      · intro t
        simp only [stageMetric, Fin.lastCases_castSucc]
      · simpa only [RealTimeInterval.closedOpen, RealTimeInterval.regular,
          H.stageEndTime_castSucc] using hpast
      · exact H.regularizedGeodesicOn_incoming_stage_of_regularizedExtendedAction_eq_regularizedCost
          i.castSucc last hle le_rfl hv.le hupper0 hpastD hscalar gamma hgammaAC hgammaInt
          hgammaNodes hmin i le_rfl hle
  have haction (eta : ℝ → (H.stage first).Carrier) (c d : ℝ) :
      H.stageRegularizedAction first T eta c d = lRegularizedAction S T eta c d := by
    unfold stageRegularizedAction lRegularizedAction
    exact intervalIntegral.integral_congr (fun r _ => hlag eta r)
  rw [hend] at hgeo
  obtain ⟨cTail, hcTail, U, hU, hsub, xi, hxi, hxiGeo, hxiEq, hxiVel⟩ :=
    exists_lRegularizedGeodesic_smooth_tail_on_Ioo_of_contMDiffAt_one
      S hS T hstartV hC1 hregv hgeo
  let m := (H.regularizedStageStart T 0 first + H.regularizedStageEnd T v first) / 2
  have hmV : m < v := by dsimp only [m]; rw [hend]; linarith
  have hmaxV : max cTail m < v := max_lt hcTail.2 hmV
  let b := (max cTail m + v) / 2
  have hmaxb : max cTail m < b := by dsimp only [b]; linarith
  have hbV : b < v := by dsimp only [b]; linarith
  have hcTailb : cTail < b := (le_max_left _ _).trans_lt hmaxb
  have hb0 : 0 < b :=
    (Real.sqrt_nonneg _).trans_lt (hcTail.1.trans hcTailb)
  let V := (fun t : ℝ => b + t) ⁻¹' U
  have hV : IsOpen V := hU.preimage (continuous_const.add continuous_id)
  have hseg : Icc (0 : ℝ) (v - b) ⊆ V := by
    intro t ht
    apply hsub
    exact ⟨by linarith [ht.1], by linarith [ht.2]⟩
  have htranslated : ContMDiffOn 𝓘(ℝ, ℝ) ThreeModel ∞ (fun t => xi (b + t)) V :=
    hxi.comp (contMDiff_const.add contMDiff_id).contMDiffOn (fun _ ht => ht)
  obtain ⟨eta, heta, hetaEq⟩ :=
    DifferentialGeometry.Topology.Manifold.exists_global_smooth_curve_eq_near_interval
      (sub_nonneg.mpr hbV.le) hV hseg htranslated
  let beta : ℝ → (H.stage first).Carrier := fun t => eta (t - b)
  have hbeta : ContMDiff 𝓘(ℝ, ℝ) ThreeModel ∞ beta :=
    heta.comp (contMDiff_id.sub contMDiff_const)
  have hbetaXi (r : ℝ) (hr : r ∈ Icc b v) : beta =ᶠ[𝓝 r] xi := by
    have heq := (hetaEq (r - b) ⟨by linarith [hr.1], by linarith [hr.2]⟩).comp_tendsto
      (continuous_id.sub continuous_const).continuousAt.tendsto
    filter_upwards [heq] with t ht
    change eta (t - b) = xi (b + (t - b)) at ht
    simpa only [beta, show b + (t - b) = t by ring] using ht
  have hxiGeoClosed : IsLRegularizedGeodesicOn S T xi (Icc b v) :=
    fun r hr => hxiGeo r (hsub ⟨hcTailb.le.trans hr.1, hr.2⟩)
  have hbetaGeo : IsLRegularizedGeodesicOn S T beta (Icc b v) :=
    hxiGeoClosed.congr_of_eventuallyEq hbetaXi
  have hbetaEq : EqOn beta (gamma ⟨first, le_rfl, hle⟩) (Icc b v) :=
    fun r hr => (hbetaXi r hr).self_of_nhds.trans (hxiEq ⟨hcTailb.le.trans hr.1, hr.2⟩)
  have hxiGerm : xi =ᶠ[𝓝 b] gamma ⟨first, le_rfl, hle⟩ := by
    filter_upwards [Ioo_mem_nhds hcTailb hbV] with r hr
    exact hxiEq (Ioo_subset_Icc_self hr)
  have hvel : lVelocity (I := ThreeModel) beta v =
      lVelocity (I := ThreeModel) (gamma ⟨first, le_rfl, hle⟩) v := by
    have hm := (hbetaXi v ⟨hbV.le, le_rfl⟩).mfderiv_eq (I := 𝓘(ℝ, ℝ)) (I' := ThreeModel)
    have hbx : lVelocity (I := ThreeModel) beta v = lVelocity (I := ThreeModel) xi v := by
      exact congrArg (fun A => A (1 : ℝ)) hm
    exact hbx.trans hxiVel
  obtain ⟨epsilon, hepsilon, hepsilonU⟩ :=
    DifferentialGeometry.Topology.Manifold.exists_interval_margin
      (sub_nonneg.mpr hbV.le) hV hseg
  let lo := b - epsilon
  let hi := v + epsilon
  have hclock (r : ℝ) (hr : r ∈ Ioo lo hi) : T - r ^ 2 ∈ D.regular := by
    have hrV : r - b ∈ V := hepsilonU ⟨by dsimp only [lo] at hr; linarith [hr.1],
      by dsimp only [hi] at hr; linarith [hr.2]⟩
    have hrU : r ∈ U := by
      change b + (r - b) ∈ U at hrV
      simpa only [show b + (r - b) = r by ring] using hrV
    exact (hxiGeo r hrU).1
  refine ⟨D, S, hS, hmetric, hlag, haction, hregv, cTail, b, lo, hi, hcTail,
    hmaxb, hbV, hb0, by dsimp only [lo]; linarith,
    by dsimp only [hi]; linarith, hclock, beta, hbeta, hbetaGeo, hbetaEq,
    (hbetaXi b ⟨le_rfl, hbV.le⟩).trans hxiGerm,
    hbetaEq ⟨hbV.le, le_rfl⟩, hvel, ?_⟩
  rw [haction]
  apply lRegularizedAction_congr
  intro r hr
  rw [uIoo_of_le hbV.le] at hr
  exact hbetaEq (Ioo_subset_Icc_self hr)


private theorem exists_separated_positive_event_collars
    (H : ObservedHistory.{u}) (first last : Fin (H.eventCount + 1))
    {T v b : ℝ} (hb : b ∈ Ioo 0 v)
    (hupper : T ∈ Icc (H.time last) (H.stageEndTime last))
    (hpast : T - v ^ 2 ∈ H.stageDomain first) :
    let E := {i : Fin H.eventCount //
      first ≤ i.castSucc ∧ i.succ ≤ last ∧ 0 < Real.sqrt (T - H.time i.succ)};
    ∀ c0 d0 : E → ℝ,
      (∀ i, H.regularizedStageStart T 0 i.val.succ < c0 i ∧
        c0 i < Real.sqrt (T - H.time i.val.succ) ∧
        Real.sqrt (T - H.time i.val.succ) < d0 i ∧
        d0 i < H.regularizedStageEnd T v i.val.castSucc) →
      ∃ (c d : E → ℝ) (a0 : ℝ), 0 < a0 ∧ a0 < b ∧
        (∀ i, a0 < c i ∧ c i < Real.sqrt (T - H.time i.val.succ) ∧
          Real.sqrt (T - H.time i.val.succ) < d i ∧
          Icc (c i) (d i) ⊆ Ioo (c0 i) (d0 i) ∧
          (H.regularizedStageStart T 0 i.val.succ +
            H.regularizedStageEnd T v i.val.succ) / 2 < c i ∧
          d i < (H.regularizedStageStart T 0 i.val.castSucc +
            H.regularizedStageEnd T v i.val.castSucc) / 2 ∧
          T - (c i) ^ 2 ∈ Ioo (H.time i.val.succ) (H.stageEndTime i.val.succ) ∧
          T - (d i) ^ 2 ∈ Ioo (H.time i.val.castSucc) (H.stageEndTime i.val.castSucc)) ∧
        (∀ i j, i.val < j.val → d j < c i) ∧
        Pairwise (fun i j => Disjoint (Icc (c i) (d i)) (Icc (c j) (d j))) ∧
        ∀ a ∈ Ioo 0 a0, ∀ (i : Fin H.eventCount),
          first ≤ i.castSucc → i.succ ≤ last → a ≠ Real.sqrt (T - H.time i.succ) := by
  classical
  intro E c0 d0 hcollar
  let m (j : Fin (H.eventCount + 1)) :=
    (H.regularizedStageStart T 0 j + H.regularizedStageEnd T v j) / 2
  let w (i : E) := Real.sqrt (T - H.time i.val.succ)
  have hupper0 : T - (0 : ℝ) ^ 2 ∈ Icc (H.time last) (H.stageEndTime last) := by
    simpa only [zero_pow two_ne_zero, sub_zero] using hupper
  have hnew (i : E) : H.regularizedStageEnd T v i.val.succ = w i :=
    H.regularizedStageEnd_succ_eq_event_clock hpast i.val i.property.1
  have hold (i : E) : H.regularizedStageStart T 0 i.val.castSucc = w i :=
    H.regularizedStageStart_castSucc_eq_event_clock hupper0 i.val i.property.2.1
  have hmnew (i : E) : m i.val.succ < w i := by
    have hh := (hcollar i).1.trans (hcollar i).2.1
    change H.regularizedStageStart T 0 i.val.succ < w i at hh
    dsimp only [m]
    rw [hnew]
    linarith
  have hmold (i : E) : w i < m i.val.castSucc := by
    have hh := (hcollar i).2.2.1.trans (hcollar i).2.2.2
    change w i < H.regularizedStageEnd T v i.val.castSucc at hh
    dsimp only [m]
    rw [hold]
    linarith
  let c (i : E) := (max (c0 i) (m i.val.succ) + w i) / 2
  let d (i : E) := (w i + min (d0 i) (m i.val.castSucc)) / 2
  have hc (i : E) : c0 i < c i ∧ m i.val.succ < c i ∧ c i < w i := by
    have hw : max (c0 i) (m i.val.succ) < w i :=
      max_lt (hcollar i).2.1 (hmnew i)
    have h0 := le_max_left (c0 i) (m i.val.succ)
    have hm := le_max_right (c0 i) (m i.val.succ)
    dsimp only [c]
    constructor
    · linarith
    constructor <;> linarith
  have hd (i : E) : w i < d i ∧ d i < d0 i ∧ d i < m i.val.castSucc := by
    have hw : w i < min (d0 i) (m i.val.castSucc) :=
      lt_min (hcollar i).2.2.1 (hmold i)
    have h0 := min_le_left (d0 i) (m i.val.castSucc)
    have hm := min_le_right (d0 i) (m i.val.castSucc)
    dsimp only [d]
    constructor
    · linarith
    constructor <;> linarith
  have hcpos (i : E) : 0 < c i :=
    (Real.sqrt_nonneg _).trans_lt ((hcollar i).1.trans (hc i).1)
  have hmanti : Antitone m := by
    intro j k hjk
    have hs : H.regularizedStageStart T 0 k ≤ H.regularizedStageStart T 0 j := by
      apply Real.sqrt_le_sqrt
      exact sub_le_sub_left (min_le_min_left _ (H.stageEndTime_mono hjk)) T
    have he : H.regularizedStageEnd T v k ≤ H.regularizedStageEnd T v j := by
      apply Real.sqrt_le_sqrt
      exact sub_le_sub_left (max_le_max_left _ (H.time_strictMono.monotone hjk)) T
    dsimp only [m]
    linarith
  have hsep (i j : E) (hij : i.val < j.val) : d j < c i := by
    have hstage : i.val.succ ≤ j.val.castSucc := by
      change i.val.val + 1 ≤ j.val.val
      exact hij
    exact (hd j).2.2.trans_le (hmanti hstage) |>.trans (hc i).2.1
  let values : Finset ℝ := insert b (Finset.univ.image c)
  have hne : values.Nonempty := Finset.insert_nonempty b _
  have hvalues : ∀ y ∈ values, 0 < y := by
    intro y hy
    rcases Finset.mem_insert.mp hy with rfl | hy
    · exact hb.1
    · obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hy
      exact hcpos i
  have hmin : 0 < values.min' hne := hvalues _ (Finset.min'_mem values hne)
  let a0 := values.min' hne / 2
  have ha0 : 0 < a0 := half_pos hmin
  have hab : a0 < b := by
    have hle := Finset.min'_le values b (Finset.mem_insert_self b _)
    dsimp only [a0]
    linarith
  have hac (i : E) : a0 < c i := by
    have hmem : c i ∈ values :=
      Finset.mem_insert_of_mem (Finset.mem_image.mpr ⟨i, Finset.mem_univ i, rfl⟩)
    have hle := Finset.min'_le values (c i) hmem
    dsimp only [a0]
    linarith
  refine ⟨c, d, a0, ha0, hab, ?_, hsep, ?_, ?_⟩
  · intro i
    refine ⟨hac i, (hc i).2.2, (hd i).1, ?_, (hc i).2.1, (hd i).2.2, ?_, ?_⟩
    · intro r hr
      exact ⟨(hc i).1.trans_le hr.1, hr.2.trans_lt (hd i).2.1⟩
    · apply H.mapsTo_regularizedStage_Ioo_Ioo T 0 v i.val.succ
      exact ⟨(hcollar i).1.trans (hc i).1, (hc i).2.2.trans_eq (hnew i).symm⟩
    · apply H.mapsTo_regularizedStage_Ioo_Ioo T 0 v i.val.castSucc
      exact ⟨(hold i).trans_lt (hd i).1, (hd i).2.1.trans (hcollar i).2.2.2⟩
  · intro i j hij
    have hneval : i.val ≠ j.val := fun heq => hij (Subtype.ext heq)
    rcases lt_or_gt_of_ne hneval with hlt | hgt
    · apply Set.disjoint_left.mpr
      intro r hri hrj
      exact (not_le_of_gt (hsep i j hlt)) (hri.1.trans hrj.2)
    · apply Set.disjoint_left.mpr
      intro r hri hrj
      exact (not_le_of_gt (hsep j i hgt)) (hrj.1.trans hri.2)
  · intro a ha i hf hl
    by_cases hw : 0 < Real.sqrt (T - H.time i.succ)
    · let j : E := ⟨i, hf, hl, hw⟩
      exact ne_of_lt (ha.2.trans ((hac j).trans (hc j).2.2))
    · have hzero : Real.sqrt (T - H.time i.succ) = 0 :=
        le_antisymm (le_of_not_gt hw) (Real.sqrt_nonneg _)
      rw [hzero]
      exact ne_of_gt ha.1


private theorem exists_positive_prefix_survivor_collars
    (H : ObservedHistory.{u}) (first last : Fin (H.eventCount + 1)) (hle : first ≤ last)
    {T B v : ℝ} (hv : 0 < v)
    (hupper : T ∈ Icc (H.time last) (H.stageEndTime last))
    (hpast : T - v ^ 2 ∈ Ioo (H.time first) (H.stageEndTime first))
    (hscalar : ∀ j : H.StageInterval first last,
      ∀ r ∈ Ioo (H.regularizedStageStart T 0 j.val) (H.regularizedStageEnd T v j.val),
      ∀ x : (H.stage j.val).Carrier, -B ≤ metricScalarAt (H.stageMetric j.val (T - r ^ 2)) x)
    (gamma : (j : H.StageInterval first last) → ℝ → (H.stage j.val).Carrier)
    (hgammaAC : ∀ j, Manifold.absolutelyContinuousOnInterval ThreeModel (gamma j)
      (H.regularizedStageStart T 0 j.val) (H.regularizedStageEnd T v j.val))
    (hgammaInt : ∀ j, IntervalIntegrable (H.stageRegularizedLagrangian j.val T (gamma j)) volume
      (H.regularizedStageStart T 0 j.val) (H.regularizedStageEnd T v j.val))
    (hgammaNodes : ∀ (i : Fin H.eventCount) (hf : first ≤ i.castSucc) (hl : i.succ ≤ last),
      ∃ z : (H.event i).old,
        z.val.val = gamma ⟨i.castSucc, hf, i.castSucc_le_succ.trans hl⟩
          (Real.sqrt (T - H.time i.succ)) ∧
        (H.event i).oldOutput z = gamma ⟨i.succ, hf.trans i.castSucc_le_succ, hl⟩
          (Real.sqrt (T - H.time i.succ)))
    (hmin : H.regularizedExtendedAction first last T B 0 v gamma =
      H.regularizedCost first last hle T B 0 v
        (gamma ⟨last, hle, le_rfl⟩ 0) (gamma ⟨first, le_rfl, hle⟩ v))
    (cut : Fin (H.eventCount + 1)) (hcl : cut ≤ last)
    (hcut : T ∈ Ioc (H.time cut) (H.stageEndTime cut))
    (b : ℝ) (hb : b ∈ Ioo 0 v)
    (hmb : (H.regularizedStageStart T 0 first + H.regularizedStageEnd T v first) / 2 < b)
    (hcross : ∀ (i : Fin H.eventCount) (hf : first ≤ i.castSucc) (hl : i.succ ≤ cut),
      (H.event i).RegularCrossing
        (gamma ⟨i.castSucc, hf, i.castSucc_le_succ.trans (hl.trans hcl)⟩
          (Real.sqrt (T - H.time i.succ)))
        (gamma ⟨i.succ, hf.trans i.castSucc_le_succ, hl.trans hcl⟩
          (Real.sqrt (T - H.time i.succ)))) :
    let E := {i : Fin H.eventCount // first ≤ i.castSucc ∧ i.succ ≤ cut};
    let jo (i : E) : H.StageInterval first last :=
      ⟨i.val.castSucc, i.property.1, i.val.castSucc_le_succ.trans (i.property.2.trans hcl)⟩;
    let jn (i : E) : H.StageInterval first last :=
      ⟨i.val.succ, i.property.1.trans i.val.castSucc_le_succ, i.property.2.trans hcl⟩;
    ∃ (C D : E → ℝ) (hCs : ∀ i, C i < H.time i.val.succ)
      (hsD : ∀ i, H.time i.val.succ < D i)
      (W : (i : E) → TopologicalSpace.Opens (H.event i.val).incoming.terminalRegularOpen)
      (F : (i : E) → PartialDiffeomorph ThreeModel ThreeModel
        (H.event i.val).incoming.terminalRegularOpen (H.stage i.val.succ).Carrier ∞)
      (S : (i : E) → SolutionOn (I := ThreeModel) (M := W i)
        (RealTimeInterval.closed (C i) (D i) ((hCs i).trans (hsD i)).le))
      (hlocalOld : ∀ i, IsLocalDiffeomorph ThreeModel ThreeModel ∞ (fun z : W i => z.val.val))
      (hlocalNew : ∀ i, IsLocalDiffeomorph ThreeModel ThreeModel ∞ (fun z : W i => F i z.val))
      (c0 d0 : E → ℝ) (eta : (i : E) → ℝ → W i),
      (∀ i, 0 < Real.sqrt (T - H.time i.val.succ) ∧
        Real.sqrt (T - H.time i.val.succ) < v ∧
        H.time i.val.castSucc < C i ∧ D i < H.stageEndTime i.val.succ ∧
        (F i).source = W i ∧ IsSolutionOn (S i) ∧
        (∀ z : W i, (H.event i.val).RegularCrossing z.val.val (F i z.val)) ∧
        (∀ t ∈ Ico (C i) (H.time i.val.succ), (S i).base.metric t =
          localPullMetric (H.stageMetric i.val.castSucc t) (fun z : W i => z.val.val) (hlocalOld i)) ∧
        (∀ t ∈ Icc (H.time i.val.succ) (D i), (S i).base.metric t =
          localPullMetric (H.stageMetric i.val.succ t) (fun z : W i => F i z.val) (hlocalNew i)) ∧
        (S i).base.metric (H.time i.val.succ) = (H.event i.val).terminal.metric.restrictOpen (W i) ∧
        0 < c0 i ∧ c0 i < Real.sqrt (T - H.time i.val.succ) ∧
        Real.sqrt (T - H.time i.val.succ) < d0 i ∧ d0 i < v ∧
        H.regularizedStageStart T 0 i.val.succ < c0 i ∧
        d0 i < H.regularizedStageEnd T v i.val.castSucc ∧
        (∀ r ∈ Icc (c0 i) (d0 i), T - r ^ 2 ∈ Ioo (C i) (D i)) ∧
        Manifold.absolutelyContinuousOnInterval ThreeModel (eta i) (c0 i) (d0 i) ∧
        ContMDiffOn 𝓘(ℝ, ℝ) ThreeModel 1 (eta i) (Icc (c0 i) (d0 i)) ∧
        IsLRegularizedGeodesicOn (S i) T (eta i) (Ioo (c0 i) (d0 i)) ∧
        EqOn ((fun z : W i => F i z.val) ∘ eta i) (gamma (jn i))
          (Icc (c0 i) (Real.sqrt (T - H.time i.val.succ))) ∧
        EqOn ((fun z : W i => z.val.val) ∘ eta i) (gamma (jo i))
          (Icc (Real.sqrt (T - H.time i.val.succ)) (d0 i)) ∧
        IntervalIntegrable (lRegularizedLagrangian (S i) T (eta i)) volume (c0 i) (d0 i) ∧
        lRegularizedAction (S i) T (eta i) (c0 i) (d0 i) =
          H.stageRegularizedAction i.val.succ T (gamma (jn i)) (c0 i)
            (Real.sqrt (T - H.time i.val.succ)) +
          H.stageRegularizedAction i.val.castSucc T (gamma (jo i))
            (Real.sqrt (T - H.time i.val.succ)) (d0 i)) ∧
      ∃ (c d : E → ℝ) (a0 : ℝ), 0 < a0 ∧ a0 < b ∧
        (∀ i, a0 < c i ∧ c i < Real.sqrt (T - H.time i.val.succ) ∧
          Real.sqrt (T - H.time i.val.succ) < d i ∧ d i < b ∧
          Icc (c i) (d i) ⊆ Ioo (c0 i) (d0 i) ∧
          (H.regularizedStageStart T 0 i.val.succ + H.regularizedStageEnd T v i.val.succ) / 2 < c i ∧
          d i < (H.regularizedStageStart T 0 i.val.castSucc + H.regularizedStageEnd T v i.val.castSucc) / 2 ∧
          T - (c i) ^ 2 ∈ Ioo (H.time i.val.succ) (H.stageEndTime i.val.succ) ∧
          T - (d i) ^ 2 ∈ Ioo (H.time i.val.castSucc) (H.stageEndTime i.val.castSucc)) ∧
        (∀ i j, i.val < j.val → d j < c i) ∧
        Pairwise (fun i j => Disjoint (Icc (c i) (d i)) (Icc (c j) (d j))) := by
  classical
  intro E jo jn
  have hpastD := H.mem_stageDomain_of_mem_Ioo hpast
  have hupper0 : T - (0 : ℝ) ^ 2 ∈ Icc (H.time last) (H.stageEndTime last) := by
    simpa only [zero_pow two_ne_zero, sub_zero] using hupper
  have hw (i : E) : 0 < Real.sqrt (T - H.time i.val.succ) ∧
      Real.sqrt (T - H.time i.val.succ) < v := by
    have htime : H.time i.val.succ < T :=
      (H.time_strictMono.monotone i.property.2).trans_lt hcut.1
    have hp : T - v ^ 2 < H.time i.val.succ := by
      simpa only [H.stageEndTime_castSucc] using
        hpast.2.trans_le (H.stageEndTime_mono i.property.1)
    refine ⟨Real.sqrt_pos.mpr (sub_pos.mpr htime), ?_⟩
    have hh := Real.sqrt_lt_sqrt (sub_nonneg.mpr htime.le)
      (show T - H.time i.val.succ < v ^ 2 by linarith)
    simpa only [Real.sqrt_sq_eq_abs, abs_of_pos hv] using hh
  have hproducer (i : E) :=
    H.exists_regularizedGeodesic_survivor_lift_of_regularizedExtendedAction_eq_regularizedCost
      first last hle le_rfl hupper0 hpastD hscalar gamma hgammaAC hgammaInt hgammaNodes hmin
      i.val i.property.1 (i.property.2.trans hcl) (hw i).1 (hw i).2
      (hcross i.val i.property.1 i.property.2)
  choose C D hCs hsD W F S hlocalOld hlocalNew htimeOld htimeNew hsource hS hcrossW
    hmetricOld hmetricNew hterminal c0 d0 hc0 hcw hwd hd0 hclipNew hclipOld hclock
    eta hAC hC1 hgeo hnew hold hint haction using hproducer
  refine ⟨C, D, hCs, hsD, W, F, S, hlocalOld, hlocalNew, c0, d0, eta, ?_, ?_⟩
  · intro i
    exact ⟨(hw i).1, (hw i).2, htimeOld i, htimeNew i, hsource i, hS i, hcrossW i,
      hmetricOld i, hmetricNew i, hterminal i, hc0 i, hcw i, hwd i, hd0 i, hclipNew i,
      hclipOld i, hclock i, hAC i, hC1 i, hgeo i, hnew i, hold i, hint i, haction i⟩
  · let EP := {i : Fin H.eventCount //
        first ≤ i.castSucc ∧ i.succ ≤ cut ∧ 0 < Real.sqrt (T - H.time i.succ)}
    let ep : E ≃ EP :=
      { toFun := fun i => ⟨i.val, i.property.1, i.property.2, (hw i).1⟩
        invFun := fun i => ⟨i.val, i.property.1, i.property.2.1⟩
        left_inv := fun _ => rfl
        right_inv := fun _ => rfl }
    obtain ⟨cP, dP, a0, ha0, hab, hcollar, hsep, hdisj, _⟩ :=
      H.exists_separated_positive_event_collars first cut hb ⟨hcut.1.le, hcut.2⟩ hpastD
        (fun i => c0 (ep.symm i)) (fun i => d0 (ep.symm i))
        (fun i => ⟨hclipNew (ep.symm i), hcw (ep.symm i), hwd (ep.symm i), hclipOld (ep.symm i)⟩)
    let c : E → ℝ := fun i => cP (ep i)
    let d : E → ℝ := fun i => dP (ep i)
    have hmid (i : E) :
        (H.regularizedStageStart T 0 i.val.castSucc + H.regularizedStageEnd T v i.val.castSucc) / 2 < b := by
      have hs : H.regularizedStageStart T 0 i.val.castSucc ≤ H.regularizedStageStart T 0 first := by
        apply Real.sqrt_le_sqrt
        exact sub_le_sub_left (min_le_min_left _ (H.stageEndTime_mono i.property.1)) T
      have he : H.regularizedStageEnd T v i.val.castSucc ≤ H.regularizedStageEnd T v first := by
        apply Real.sqrt_le_sqrt
        exact sub_le_sub_left (max_le_max_left _ (H.time_strictMono.monotone i.property.1)) T
      linarith
    refine ⟨c, d, a0, ha0, hab, ?_, ?_, ?_⟩
    · intro i
      have hi := hcollar (ep i)
      simp only [ep.symm_apply_apply] at hi
      exact ⟨hi.1, hi.2.1, hi.2.2.1, hi.2.2.2.2.2.1.trans (hmid i),
        hi.2.2.2⟩
    · intro i j hij
      exact hsep (ep i) (ep j) hij
    · intro i j hij
      exact hdisj (fun heq => hij (ep.injective heq))


private theorem exists_reverse_stage_event_equivs
    (H : ObservedHistory.{u}) (first last : Fin (H.eventCount + 1)) (hle : first ≤ last) :
    let N := last.val - first.val;
    let E := {i : Fin H.eventCount // first ≤ i.castSucc ∧ i.succ ≤ last};
    ∃ (j : Fin (N + 1) ≃ H.StageInterval first last) (e : Fin N ≃ E),
      (∀ k, (j k).val.val = last.val - k.val) ∧
      (∀ k, (e k).val.val = last.val - (k.val + 1)) ∧
      (j 0).val = last ∧ (j (Fin.last N)).val = first ∧
      (∀ k, (e k).val.succ = (j k.castSucc).val ∧
        (e k).val.castSucc = (j k.succ).val) ∧
      (∀ F : H.StageInterval first last → ℝ, (∑ x, F x) = ∑ k, F (j k)) ∧
      (∀ F : E → ℝ, (∑ x, F x) = ∑ k, F (e k)) := by
  intro N E
  have hfl : first.val ≤ last.val := hle
  let j : Fin (N + 1) ≃ H.StageInterval first last :=
    { toFun := fun k => ⟨⟨last.val - k.val, by omega⟩, by
        have hk := k.isLt
        change first.val ≤ last.val - k.val ∧ last.val - k.val ≤ last.val
        dsimp only [N] at hk
        omega⟩
      invFun := fun x => ⟨last.val - x.val.val, by
        have hl := x.property.1
        have hr := x.property.2
        dsimp only [N]
        omega⟩
      left_inv := fun k => by
        apply Fin.ext
        change last.val - (last.val - k.val) = k.val
        have hk := k.isLt
        dsimp only [N] at hk
        omega
      right_inv := fun x => by
        apply Subtype.ext
        apply Fin.ext
        change last.val - (last.val - x.val.val) = x.val.val
        have hx := x.property.2
        omega }
  let e : Fin N ≃ E :=
    { toFun := fun k => ⟨⟨last.val - (k.val + 1), by
        have hk := k.isLt
        have hl := last.isLt
        dsimp only [N] at hk
        omega⟩, by
        have hk := k.isLt
        change first.val ≤ last.val - (k.val + 1) ∧ last.val - (k.val + 1) + 1 ≤ last.val
        dsimp only [N] at hk
        omega⟩
      invFun := fun i => ⟨last.val - (i.val.val + 1), by
        have hf := i.property.1
        have hl := i.property.2
        change first.val ≤ i.val.val at hf
        change i.val.val + 1 ≤ last.val at hl
        dsimp only [N]
        omega⟩
      left_inv := fun k => by
        apply Fin.ext
        change last.val - (last.val - (k.val + 1) + 1) = k.val
        have hk := k.isLt
        dsimp only [N] at hk
        omega
      right_inv := fun i => by
        apply Subtype.ext
        apply Fin.ext
        change last.val - (last.val - (i.val.val + 1) + 1) = i.val.val
        have hl := i.property.2
        change i.val.val + 1 ≤ last.val at hl
        omega }
  refine ⟨j, e, fun _ => rfl, fun _ => rfl, ?_, ?_, ?_, ?_, ?_⟩
  · apply Fin.ext
    change last.val - 0 = last.val
    omega
  · apply Fin.ext
    change last.val - N = first.val
    dsimp only [N]
    omega
  · intro k
    have hk := k.isLt
    dsimp only [N] at hk
    constructor <;> apply Fin.ext
    · change last.val - (k.val + 1) + 1 = last.val - k.val
      omega
    · rfl
  · intro F
    exact (j.sum_comp F).symm
  · intro F
    exact (e.sum_comp F).symm


private theorem exists_strict_collar_endpoint_list
    {N : ℕ} (a b v : ℝ) (c d : Fin N → ℝ)
    (hab : a < b) (hbv : b < v)
    (hac : ∀ k, a < c k) (hcd : ∀ k, c k < d k)
    (hsep : ∀ k l, k < l → d k < c l) (hdb : ∀ k, d k < b) :
    ∃ s : Fin (2 * N + 3) → ℝ,
      StrictMono s ∧ s 0 = a ∧ s (Fin.last (2 * N + 2)) = v ∧
      s ⟨2 * N + 1, by omega⟩ = b ∧
      (∀ k : Fin N,
        s ⟨2 * k.val + 1, by omega⟩ = c k ∧
        s ⟨2 * k.val + 2, by omega⟩ = d k) := by
  let s (i : Fin (2 * N + 3)) : ℝ :=
    if hzero : i.val = 0 then a else
    if hmid : i.val < 2 * N + 1 then
      if hodd : i.val % 2 = 1 then c ⟨i.val / 2, by omega⟩
      else d ⟨i.val / 2 - 1, by omega⟩
    else if i.val = 2 * N + 1 then b else v
  have hs0 : s 0 = a := by simp [s]
  have hsv : s (Fin.last (2 * N + 2)) = v := by
    simp only [s, Fin.val_last, dite_eq_right (by omega : 2 * N + 2 ≠ 0),
      dite_eq_right (by omega : ¬2 * N + 2 < 2 * N + 1),
      ite_eq_right (by omega : 2 * N + 2 ≠ 2 * N + 1)]
  have hsb : s ⟨2 * N + 1, by omega⟩ = b := by
    simp [s]
  have hsc (k : Fin N) : s ⟨2 * k.val + 1, by omega⟩ = c k := by
    have hk := k.isLt
    simp only [s, dite_eq_right (by omega : 2 * k.val + 1 ≠ 0),
      dite_eq_left (by omega : 2 * k.val + 1 < 2 * N + 1),
      dite_eq_left (by omega : (2 * k.val + 1) % 2 = 1)]
    congr 1
    apply Fin.ext
    dsimp only
    omega
  have hsd (k : Fin N) : s ⟨2 * k.val + 2, by omega⟩ = d k := by
    have hk := k.isLt
    simp only [s, dite_eq_right (by omega : 2 * k.val + 2 ≠ 0),
      dite_eq_left (by omega : 2 * k.val + 2 < 2 * N + 1),
      dite_eq_right (by omega : ¬(2 * k.val + 2) % 2 = 1)]
    congr 1
    apply Fin.ext
    dsimp only
    omega
  refine ⟨s, ?_, hs0, hsv, hsb, fun k => ⟨hsc k, hsd k⟩⟩
  apply Fin.strictMono_iff_lt_succ.mpr
  intro i
  have hi := i.isLt
  by_cases hi0 : i.val = 0
  · have hzero : i.castSucc = 0 := Fin.ext hi0
    rw [hzero, hs0]
    by_cases hN : N = 0
    · have his : i.succ = ⟨2 * N + 1, by omega⟩ := Fin.ext (by simp only [Fin.val_succ]; omega)
      rw [his, hsb]
      exact hab
    · let k : Fin N := ⟨0, by omega⟩
      have his : i.succ = ⟨2 * k.val + 1, by omega⟩ := Fin.ext (by simp only [Fin.val_succ]; dsimp only [k]; omega)
      rw [his, hsc]
      exact hac k
  · by_cases hilast : i.val = 2 * N + 1
    · have hic : i.castSucc = ⟨2 * N + 1, by omega⟩ := Fin.ext hilast
      have his : i.succ = Fin.last (2 * N + 2) := Fin.ext (by simpa only [Fin.val_succ, Fin.val_last] using congrArg (fun n => n + 1) hilast)
      rw [hic, his, hsb, hsv]
      exact hbv
    · have himid : i.val < 2 * N + 1 := by omega
      by_cases hodd : i.val % 2 = 1
      · let k : Fin N := ⟨i.val / 2, by omega⟩
        have hic : i.castSucc = ⟨2 * k.val + 1, by omega⟩ := Fin.ext (by simp only [Fin.val_castSucc]; dsimp only [k]; omega)
        have his : i.succ = ⟨2 * k.val + 2, by omega⟩ := Fin.ext (by simp only [Fin.val_succ]; dsimp only [k]; omega)
        rw [hic, his, hsc, hsd]
        exact hcd k
      · let k : Fin N := ⟨i.val / 2 - 1, by omega⟩
        have hic : i.castSucc = ⟨2 * k.val + 2, by omega⟩ := Fin.ext (by simp only [Fin.val_castSucc]; dsimp only [k]; omega)
        rw [hic, hsd]
        by_cases hk : k.val + 1 < N
        · let l : Fin N := ⟨k.val + 1, hk⟩
          have his : i.succ = ⟨2 * l.val + 1, by omega⟩ := Fin.ext (by simp only [Fin.val_succ]; dsimp only [k, l]; omega)
          rw [his, hsc]
          exact hsep k l (by change k.val < k.val + 1; omega)
        · have his : i.succ = ⟨2 * N + 1, by omega⟩ := Fin.ext (by simp only [Fin.val_succ]; dsimp only [k] at hk; omega)
          rw [his, hsb]
          exact hdb k


private theorem exists_ordered_positive_stage_pieces
    (H : ObservedHistory.{u}) (first last : Fin (H.eventCount + 1)) (hle : first ≤ last)
    {T v b : ℝ}
    (hupper : T ∈ Icc (H.time last) (H.stageEndTime last))
    (hpast : T - v ^ 2 ∈ Ioo (H.time first) (H.stageEndTime first))
    (hbv : b < v)
    (hmb : (H.regularizedStageStart T 0 first + H.regularizedStageEnd T v first) / 2 < b) :
    let E := {i : Fin H.eventCount //
      first ≤ i.castSucc ∧ i.succ ≤ last ∧ 0 < Real.sqrt (T - H.time i.succ)};
    ∀ c0 d0 : E → ℝ,
      (∀ i, H.regularizedStageStart T 0 i.val.succ < c0 i ∧
        c0 i < Real.sqrt (T - H.time i.val.succ) ∧
        Real.sqrt (T - H.time i.val.succ) < d0 i ∧
        d0 i < H.regularizedStageEnd T v i.val.castSucc) →
    ∃ lastPos : Fin (H.eventCount + 1), first ≤ lastPos ∧ lastPos ≤ last ∧
      (lastPos = last ↔ H.time last < T) ∧
      (T = H.time last → ∃ i : Fin H.eventCount, last = i.succ ∧ lastPos = i.castSucc) ∧
      H.regularizedStageStart T 0 lastPos = 0 ∧
      H.regularizedStageEnd T v first = v ∧
      (∀ j : H.StageInterval first lastPos,
        H.regularizedStageStart T 0 j.val < H.regularizedStageEnd T v j.val) ∧
      (∀ j : Fin (H.eventCount + 1), j ≤ last → lastPos < j →
        j = last ∧ H.regularizedStageStart T 0 j = 0 ∧ H.regularizedStageEnd T v j = 0) ∧
      let N := lastPos.val - first.val;
      ∃ (j : Fin (N + 1) ≃ H.StageInterval first lastPos) (e : Fin N ≃ E)
        (c d : E → ℝ) (a0 : ℝ),
        (∀ k, (j k).val.val = lastPos.val - k.val) ∧
        (∀ k, (e k).val.val = lastPos.val - (k.val + 1)) ∧
        (j 0).val = lastPos ∧ (j (Fin.last N)).val = first ∧
        (∀ k, (e k).val.succ = (j k.castSucc).val ∧
          (e k).val.castSucc = (j k.succ).val) ∧
        0 < a0 ∧ a0 < b ∧
        (∀ i, a0 < c i ∧ c i < Real.sqrt (T - H.time i.val.succ) ∧
          Real.sqrt (T - H.time i.val.succ) < d i ∧
          Icc (c i) (d i) ⊆ Ioo (c0 i) (d0 i) ∧
          (H.regularizedStageStart T 0 i.val.succ +
            H.regularizedStageEnd T v i.val.succ) / 2 < c i ∧
          d i < (H.regularizedStageStart T 0 i.val.castSucc +
            H.regularizedStageEnd T v i.val.castSucc) / 2 ∧ d i < b) ∧
        (∀ F : H.StageInterval first lastPos → ℝ, (∑ x, F x) = ∑ k, F (j k)) ∧
        (∀ F : E → ℝ, (∑ x, F x) = ∑ k, F (e k)) ∧
        ∀ a ∈ Ioo 0 a0, ∃ s : Fin (2 * N + 3) → ℝ,
          StrictMono s ∧ s 0 = a ∧ s (Fin.last (2 * N + 2)) = v ∧
          s ⟨2 * N + 1, by omega⟩ = b ∧
          (∀ k : Fin N,
            s ⟨2 * k.val + 1, by omega⟩ = c (e k) ∧
            s ⟨2 * k.val + 2, by omega⟩ = d (e k)) ∧
          (∀ k : Fin (N + 1),
            H.regularizedStageStart T 0 (j k).val < s ⟨2 * k.val, by omega⟩ ∧
            s ⟨2 * k.val + 1, by omega⟩ < H.regularizedStageEnd T v (j k).val) := by
  intro E c0 d0 hcollar
  have hb0 : 0 < b := by
    have hs := Real.sqrt_nonneg (T - min (T - (0 : ℝ) ^ 2) (H.stageEndTime first))
    have he := Real.sqrt_nonneg (T - max (T - v ^ 2) (H.time first))
    change 0 ≤ H.regularizedStageStart T 0 first at hs
    change 0 ≤ H.regularizedStageEnd T v first at he
    linarith
  obtain ⟨lastPos, hfp, hpl, hchar, hpole, hpos0, hfirstV, hpositive, hzero, hclockPos⟩ :=
    H.exists_positive_regularized_stage_interval first last hle (hb0.trans hbv) hupper hpast
  let N := lastPos.val - first.val
  let E0 := {i : Fin H.eventCount // first ≤ i.castSucc ∧ i.succ ≤ lastPos}
  obtain ⟨j, e0, hjVal, he0Val, hj0, hjLast, hjEvent, hsumJ, _⟩ :=
    H.exists_reverse_stage_event_equivs first lastPos hfp
  let ep : E0 ≃ E :=
    { toFun := fun i => ⟨i.val, i.property.1, i.property.2.trans hpl,
        (hclockPos i.val (i.property.2.trans hpl)).mpr i.property.2⟩
      invFun := fun i => ⟨i.val, i.property.1,
        (hclockPos i.val i.property.2.1).mp i.property.2.2⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  let e : Fin N ≃ E := e0.trans ep
  have heVal (k : Fin N) : (e k).val.val = lastPos.val - (k.val + 1) := he0Val k
  have hEvent (k : Fin N) : (e k).val.succ = (j k.castSucc).val ∧
      (e k).val.castSucc = (j k.succ).val := hjEvent k
  obtain ⟨c, d, a0, ha0, ha0b, hc, hsep, _, _⟩ :=
    H.exists_separated_positive_event_collars first last ⟨hb0, hbv⟩ hupper
      (H.mem_stageDomain_of_mem_Ioo hpast) c0 d0 hcollar
  have hdb (i : E) : d i < b := by
    have hs : H.regularizedStageStart T 0 i.val.castSucc ≤
        H.regularizedStageStart T 0 first := by
      apply Real.sqrt_le_sqrt
      exact sub_le_sub_left (min_le_min_left _ (H.stageEndTime_mono i.property.1)) T
    have he : H.regularizedStageEnd T v i.val.castSucc ≤
        H.regularizedStageEnd T v first := by
      apply Real.sqrt_le_sqrt
      exact sub_le_sub_left (max_le_max_left _ (H.time_strictMono.monotone i.property.1)) T
    have hd := (hc i).2.2.2.2.2.1
    linarith
  have hreverseSep (k l : Fin N) (hkl : k < l) : d (e k) < c (e l) := by
    apply hsep (e l) (e k)
    change (e l).val.val < (e k).val.val
    rw [heVal, heVal]
    have hk := k.isLt
    have hl := l.isLt
    have hfpVal : first.val ≤ lastPos.val := hfp
    change k.val < l.val at hkl
    dsimp only [N] at hk hl
    omega
  refine ⟨lastPos, hfp, hpl, hchar, hpole, hpos0, hfirstV,
    fun k => hpositive k.val k.property.1 k.property.2, hzero,
    j, e, c, d, a0, hjVal, heVal, hj0, hjLast, hEvent, ha0, ha0b,
    (fun i => ⟨(hc i).1, (hc i).2.1, (hc i).2.2.1, (hc i).2.2.2.1,
      (hc i).2.2.2.2.1, (hc i).2.2.2.2.2.1, hdb i⟩),
    hsumJ, (fun F => (e.sum_comp F).symm), ?_⟩
  intro a ha
  obtain ⟨s, hs, hs0, hsv, hsb, hscd⟩ := exists_strict_collar_endpoint_list a b v
    (fun k => c (e k)) (fun k => d (e k)) (ha.2.trans ha0b) hbv
    (fun k => ha.2.trans (hc (e k)).1)
    (fun k => (hc (e k)).2.1.trans (hc (e k)).2.2.1) hreverseSep
    (fun k => hdb (e k))
  refine ⟨s, hs, hs0, hsv, hsb, hscd, ?_⟩
  intro k
  have hk := k.isLt
  have hupper0 : T - (0 : ℝ) ^ 2 ∈ Icc (H.time last) (H.stageEndTime last) := by
    simpa only [zero_pow two_ne_zero, sub_zero] using hupper
  constructor
  · by_cases hk0 : k.val = 0
    · have hkeq : k = 0 := Fin.ext hk0
      have hsidx : (⟨2 * k.val, by omega⟩ : Fin (2 * N + 3)) = 0 := Fin.ext (by simp only [Fin.val_zero]; omega)
      rw [hsidx, hs0, hkeq, hj0, hpos0]
      exact ha.1
    · let l : Fin N := ⟨k.val - 1, by omega⟩
      have hks : l.succ = k := Fin.ext (by change k.val - 1 + 1 = k.val; omega)
      have hsidx : (⟨2 * k.val, by omega⟩ : Fin (2 * N + 3)) =
          ⟨2 * l.val + 2, by omega⟩ := Fin.ext (by change 2 * k.val = 2 * (k.val - 1) + 2; omega)
      rw [hsidx, (hscd l).2, ← hks, ← (hEvent l).2,
        H.regularizedStageStart_castSucc_eq_event_clock hupper0 (e l).val (e l).property.2.1]
      exact (hc (e l)).2.2.1
  · by_cases hkl : k.val = N
    · have hkeq : k = Fin.last N := Fin.ext hkl
      have hsidx : (⟨2 * k.val + 1, by omega⟩ : Fin (2 * N + 3)) =
          ⟨2 * N + 1, by omega⟩ := Fin.ext (by change 2 * k.val + 1 = 2 * N + 1; omega)
      rw [hsidx, hsb, hkeq, hjLast, hfirstV]
      exact hbv
    · let l : Fin N := ⟨k.val, by omega⟩
      have hkc : l.castSucc = k := Fin.ext rfl
      have hsidx : (⟨2 * k.val + 1, by omega⟩ : Fin (2 * N + 3)) =
          ⟨2 * l.val + 1, by omega⟩ := rfl
      rw [hsidx, (hscd l).1, ← hkc, ← (hEvent l).1,
        H.regularizedStageEnd_succ_eq_event_clock (H.mem_stageDomain_of_mem_Ioo hpast)
          (e l).val (e l).property.1]
      exact (hc (e l)).2.1


private theorem exists_ordered_prefix_piece_intervals
    (H : ObservedHistory.{u}) (first cut : Fin (H.eventCount + 1)) (hfc : first ≤ cut)
    {T v b : ℝ} (hcut : T ∈ Ioc (H.time cut) (H.stageEndTime cut))
    (hpast : T - v ^ 2 ∈ Ioo (H.time first) (H.stageEndTime first))
    (hbv : b < v)
    (hmb : (H.regularizedStageStart T 0 first + H.regularizedStageEnd T v first) / 2 < b) :
    let J := H.StageInterval first cut;
    let E := {i : Fin H.eventCount // first ≤ i.castSucc ∧ i.succ ≤ cut};
    let jo (i : E) : J := ⟨i.val.castSucc, i.property.1, i.val.castSucc_le_succ.trans i.property.2⟩;
    let jn (i : E) : J := ⟨i.val.succ, i.property.1.trans i.val.castSucc_le_succ, i.property.2⟩;
    let jf : J := ⟨first, le_rfl, hfc⟩;
    let jl : J := ⟨cut, hfc, le_rfl⟩;
    let N := cut.val - first.val;
    ∀ c0 d0 : E → ℝ,
      (∀ i, H.regularizedStageStart T 0 i.val.succ < c0 i ∧
        c0 i < Real.sqrt (T - H.time i.val.succ) ∧
        Real.sqrt (T - H.time i.val.succ) < d0 i ∧
        d0 i < H.regularizedStageEnd T v i.val.castSucc) →
    ∃ (j : Fin (N + 1) ≃ J) (e : Fin N ≃ E) (c d : E → ℝ) (a0 : ℝ),
      j 0 = jl ∧ j (Fin.last N) = jf ∧
      (∀ k, j k.castSucc = jn (e k) ∧ j k.succ = jo (e k)) ∧
      0 < a0 ∧ a0 < b ∧
      (∀ i, a0 < c i ∧ c i < Real.sqrt (T - H.time i.val.succ) ∧
        Real.sqrt (T - H.time i.val.succ) < d i ∧ d i < b ∧
        Icc (c i) (d i) ⊆ Ioo (c0 i) (d0 i)) ∧
      H.regularizedStageStart T 0 cut = 0 ∧ H.regularizedStageEnd T v first = v ∧
      ∀ a ∈ Ioo 0 a0,
        ∃ (lo hi : J → ℝ) (s : Fin (2 * N + 3) → ℝ),
          StrictMono s ∧ s 0 = a ∧ s (Fin.last (2 * N + 2)) = v ∧
          s ⟨2 * N + 1, by omega⟩ = b ∧
          (∀ k, s ⟨2 * k.val, by omega⟩ = lo (j k) ∧
            s ⟨2 * k.val + 1, by omega⟩ = hi (j k)) ∧
          (∀ k, s ⟨2 * k.val + 1, by omega⟩ = c (e k) ∧
            s ⟨2 * k.val + 2, by omega⟩ = d (e k)) ∧
          lo jl = a ∧ hi jf = b ∧
          (∀ i, hi (jn i) = c i ∧ lo (jo i) = d i) ∧
          (∀ x : J, H.regularizedStageStart T 0 x.val < lo x ∧ lo x < hi x ∧
            hi x < H.regularizedStageEnd T v x.val) := by
  classical
  intro J E jo jn jf jl N c0 d0 hcollar
  let EP := {i : Fin H.eventCount //
    first ≤ i.castSucc ∧ i.succ ≤ cut ∧ 0 < Real.sqrt (T - H.time i.succ)}
  have hw (i : E) : 0 < Real.sqrt (T - H.time i.val.succ) :=
    Real.sqrt_pos.mpr (sub_pos.mpr ((H.time_strictMono.monotone i.property.2).trans_lt hcut.1))
  let ep : E ≃ EP :=
    { toFun := fun i => ⟨i.val, i.property.1, i.property.2, hw i⟩
      invFun := fun i => ⟨i.val, i.property.1, i.property.2.1⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  obtain ⟨pos, hfp, hpc, hchar, _, hstart, hend, _, _, j, eP, cP, dP, a0,
      _, _, hj0, hjLast, hjEvent, ha0, ha0b, hcP, _, _, hpieces⟩ :=
    H.exists_ordered_positive_stage_pieces first cut hfc ⟨hcut.1.le, hcut.2⟩ hpast hbv hmb
      (fun i => c0 (ep.symm i)) (fun i => d0 (ep.symm i))
      (fun i => hcollar (ep.symm i))
  have hpos : pos = cut := hchar.mpr hcut.1
  subst pos
  let e : Fin N ≃ E := eP.trans ep.symm
  let c : E → ℝ := fun i => cP (ep i)
  let d : E → ℝ := fun i => dP (ep i)
  have hce (k : Fin N) : c (e k) = cP (eP k) := ep.apply_symm_apply (eP k) ▸ rfl
  have hde (k : Fin N) : d (e k) = dP (eP k) := ep.apply_symm_apply (eP k) ▸ rfl
  have hj0' : j 0 = jl := Subtype.ext hj0
  have hjLast' : j (Fin.last N) = jf := Subtype.ext hjLast
  have hjEvent' (k : Fin N) : j k.castSucc = jn (e k) ∧ j k.succ = jo (e k) :=
    ⟨Subtype.ext (hjEvent k).1.symm, Subtype.ext (hjEvent k).2.symm⟩
  refine ⟨j, e, c, d, a0, hj0', hjLast', hjEvent', ha0, ha0b, ?_, hstart, hend, ?_⟩
  · intro i
    have hi := hcP (ep i)
    simp only [ep.symm_apply_apply] at hi
    exact ⟨hi.1, hi.2.1, hi.2.2.1, hi.2.2.2.2.2.2, hi.2.2.2.1⟩
  · intro a ha
    obtain ⟨s, hs, hs0, hsv, hsb, hscd, hgap⟩ := hpieces a ha
    let lo : J → ℝ := fun x => s ⟨2 * (j.symm x).val, by have hh := (j.symm x).isLt; omega⟩
    let hi : J → ℝ := fun x => s ⟨2 * (j.symm x).val + 1, by have hh := (j.symm x).isLt; omega⟩
    have hleft (k : Fin (N + 1)) : s ⟨2 * k.val, by omega⟩ = lo (j k) := by
      simp only [lo, j.symm_apply_apply]
    have hright (k : Fin (N + 1)) : s ⟨2 * k.val + 1, by omega⟩ = hi (j k) := by
      simp only [hi, j.symm_apply_apply]
    have hcd (k : Fin N) : s ⟨2 * k.val + 1, by omega⟩ = c (e k) ∧
        s ⟨2 * k.val + 2, by omega⟩ = d (e k) :=
      ⟨(hscd k).1.trans (hce k).symm, (hscd k).2.trans (hde k).symm⟩
    refine ⟨lo, hi, s, hs, hs0, hsv, hsb, fun k => ⟨hleft k, hright k⟩,
      hcd, ?_, ?_, ?_, ?_⟩
    · rw [← hj0', ← hleft]
      exact hs0
    · rw [← hjLast', ← hright]
      exact hsb
    · intro i
      obtain ⟨k, rfl⟩ := e.surjective i
      constructor
      · rw [← (hjEvent' k).1, ← hright]
        exact (hcd k).1
      · rw [← (hjEvent' k).2, ← hleft]
        have hidx : (⟨2 * k.succ.val, by omega⟩ : Fin (2 * N + 3)) =
            ⟨2 * k.val + 2, by omega⟩ := Fin.ext (by simp only [Fin.val_succ]; omega)
        rw [hidx]
        exact (hcd k).2
    · intro x
      obtain ⟨k, rfl⟩ := j.surjective x
      rw [← hleft, ← hright]
      exact ⟨(hgap k).1, hs (by change 2 * k.val < 2 * k.val + 1; omega), (hgap k).2⟩


/-- From one original fixed-endpoint attained action, choose the actual smooth
terminal piece, original physical survivor lifts, and a positive collar reserve.
All these witnesses are fixed before the cutoff is chosen. The terminal
velocity is the original curve's velocity, obtained from its C1 germ at v. -/
theorem exists_physical_collar_reserve_of_attained_action
    (H : ObservedHistory.{u}) (first last : Fin (H.eventCount + 1)) (hle : first ≤ last)
    {T B v : ℝ} (hv : 0 < v)
    (hupper : T ∈ Ioc (H.time last) (H.stageEndTime last))
    (hpast : T - v ^ 2 ∈ Ioo (H.time first) (H.stageEndTime first))
    (hscalar : ∀ j (t : ℝ), t ∈ H.stageDomain j →
      ∀ x : (H.stage j).Carrier, -B ≤ metricScalarAt (H.stageMetric j t) x)
    (gamma : (j : H.StageInterval first last) → ℝ → (H.stage j.val).Carrier)
    (hgammaAC : ∀ j, Manifold.absolutelyContinuousOnInterval ThreeModel (gamma j)
      (H.regularizedStageStart T 0 j.val) (H.regularizedStageEnd T v j.val))
    (hgammaInt : ∀ j,
      IntervalIntegrable (H.stageRegularizedLagrangian j.val T (gamma j)) volume
        (H.regularizedStageStart T 0 j.val) (H.regularizedStageEnd T v j.val))
    (hgammaNodes : ∀ (i : Fin H.eventCount)
      (hf : first ≤ i.castSucc) (hl : i.succ ≤ last),
      ∃ z : (H.event i).old,
        z.val.val = gamma ⟨i.castSucc, hf, i.castSucc_le_succ.trans hl⟩
          (Real.sqrt (T - H.time i.succ)) ∧
        (H.event i).oldOutput z = gamma ⟨i.succ, hf.trans i.castSucc_le_succ, hl⟩
          (Real.sqrt (T - H.time i.succ)))
    (hmin : H.regularizedExtendedAction first last T B 0 v gamma =
      H.regularizedCost first last hle T B 0 v
        (gamma ⟨last, hle, le_rfl⟩ 0) (gamma ⟨first, le_rfl, hle⟩ v))
    (hC1Atv : ContMDiffAt 𝓘(ℝ, ℝ) ThreeModel 1
      (gamma ⟨first, le_rfl, hle⟩) v)
    (hcross : ∀ (i : Fin H.eventCount)
      (hf : first ≤ i.castSucc) (hl : i.succ ≤ last),
      (H.event i).RegularCrossing
        (gamma ⟨i.castSucc, hf, i.castSucc_le_succ.trans hl⟩
          (Real.sqrt (T - H.time i.succ)))
        (gamma ⟨i.succ, hf.trans i.castSucc_le_succ, hl⟩
          (Real.sqrt (T - H.time i.succ)))) :
    let J := H.StageInterval first last;
    let E := {i : Fin H.eventCount // first ≤ i.castSucc ∧ i.succ ≤ last};
    let jo (i : E) : J := ⟨i.val.castSucc, i.property.1,
      i.val.castSucc_le_succ.trans i.property.2⟩;
    let jn (i : E) : J := ⟨i.val.succ,
      i.property.1.trans i.val.castSucc_le_succ, i.property.2⟩;
    let jf : J := ⟨first, le_rfl, hle⟩;
    let jl : J := ⟨last, hle, le_rfl⟩;
    let N := last.val - first.val;
    ∃ (DT : RealTimeInterval)
      (ST : SolutionOn (I := ThreeModel) (M := (H.stage first).Carrier) DT)
      (b lowT highT : ℝ) (alphaT : ℝ → (H.stage first).Carrier),
      IsSolutionOn ST ∧
      (∀ t, ST.base.metric t = H.stageMetric first t) ∧
      0 < b ∧ b < v ∧
      (H.regularizedStageStart T 0 first + H.regularizedStageEnd T v first) / 2 < b ∧
      lowT < b ∧ v < highT ∧
      (∀ r ∈ Ioo lowT highT, T - r ^ 2 ∈ DT.regular) ∧
      ContMDiff 𝓘(ℝ, ℝ) ThreeModel ∞ alphaT ∧
      IsLRegularizedGeodesicOn ST T alphaT (Icc b v) ∧
      EqOn alphaT (gamma jf) (Icc b v) ∧
      alphaT =ᶠ[𝓝 b] gamma jf ∧
      alphaT v = gamma jf v ∧
      lVelocity (I := ThreeModel) alphaT v =
        lVelocity (I := ThreeModel) (gamma jf) v ∧
      lRegularizedAction ST T alphaT b v =
        H.stageRegularizedAction first T (gamma jf) b v ∧
      ∃ (C D : E → ℝ) (hCs : ∀ i, C i < H.time i.val.succ)
        (hsD : ∀ i, H.time i.val.succ < D i)
        (W : (i : E) → TopologicalSpace.Opens (H.event i.val).incoming.terminalRegularOpen)
        (FC : (i : E) → PartialDiffeomorph ThreeModel ThreeModel
          (H.event i.val).incoming.terminalRegularOpen (H.stage i.val.succ).Carrier ∞)
        (SS : (i : E) → SolutionOn (I := ThreeModel) (M := W i)
          (RealTimeInterval.closed (C i) (D i) ((hCs i).trans (hsD i)).le))
        (hold : ∀ i, IsLocalDiffeomorph ThreeModel ThreeModel ∞
          (fun z : W i => z.val.val))
        (hnew : ∀ i, IsLocalDiffeomorph ThreeModel ThreeModel ∞
          (fun z : W i => FC i z.val))
        (c0 d0 : E → ℝ) (eta : (i : E) → ℝ → W i),
        (∀ i,
          0 < Real.sqrt (T - H.time i.val.succ) ∧
          Real.sqrt (T - H.time i.val.succ) < v ∧
          H.time i.val.castSucc < C i ∧ D i < H.stageEndTime i.val.succ ∧
          (FC i).source = W i ∧ IsSolutionOn (SS i) ∧
          (∀ z : W i, (H.event i.val).RegularCrossing z.val.val (FC i z.val)) ∧
          (∀ t ∈ Ico (C i) (H.time i.val.succ), (SS i).base.metric t =
            localPullMetric (H.stageMetric i.val.castSucc t)
              (fun z : W i => z.val.val) (hold i)) ∧
          (∀ t ∈ Icc (H.time i.val.succ) (D i), (SS i).base.metric t =
            localPullMetric (H.stageMetric i.val.succ t)
              (fun z : W i => FC i z.val) (hnew i)) ∧
          (SS i).base.metric (H.time i.val.succ) =
            (H.event i.val).terminal.metric.restrictOpen (W i) ∧
          0 < c0 i ∧ c0 i < Real.sqrt (T - H.time i.val.succ) ∧
          Real.sqrt (T - H.time i.val.succ) < d0 i ∧ d0 i < v ∧
          H.regularizedStageStart T 0 i.val.succ < c0 i ∧
          d0 i < H.regularizedStageEnd T v i.val.castSucc ∧
          (∀ r ∈ Icc (c0 i) (d0 i), T - r ^ 2 ∈ Ioo (C i) (D i)) ∧
          Manifold.absolutelyContinuousOnInterval ThreeModel (eta i) (c0 i) (d0 i) ∧
          ContMDiffOn 𝓘(ℝ, ℝ) ThreeModel 1 (eta i) (Icc (c0 i) (d0 i)) ∧
          IsLRegularizedGeodesicOn (SS i) T (eta i) (Ioo (c0 i) (d0 i)) ∧
          EqOn ((fun z : W i => FC i z.val) ∘ eta i) (gamma (jn i))
            (Icc (c0 i) (Real.sqrt (T - H.time i.val.succ))) ∧
          EqOn ((fun z : W i => z.val.val) ∘ eta i) (gamma (jo i))
            (Icc (Real.sqrt (T - H.time i.val.succ)) (d0 i)) ∧
          IntervalIntegrable (lRegularizedLagrangian (SS i) T (eta i))
            volume (c0 i) (d0 i) ∧
          lRegularizedAction (SS i) T (eta i) (c0 i) (d0 i) =
            H.stageRegularizedAction i.val.succ T (gamma (jn i)) (c0 i)
              (Real.sqrt (T - H.time i.val.succ)) +
            H.stageRegularizedAction i.val.castSucc T (gamma (jo i))
              (Real.sqrt (T - H.time i.val.succ)) (d0 i)) ∧
        ∃ (j : Fin (N + 1) ≃ J) (e : Fin N ≃ E)
          (c d : E → ℝ) (a0 : ℝ),
          j 0 = jl ∧ j (Fin.last N) = jf ∧
          (∀ k, j k.castSucc = jn (e k) ∧ j k.succ = jo (e k)) ∧
          0 < a0 ∧ a0 < b ∧
          (∀ i, a0 < c i ∧ c i < Real.sqrt (T - H.time i.val.succ) ∧
            Real.sqrt (T - H.time i.val.succ) < d i ∧ d i < b ∧
            Icc (c i) (d i) ⊆ Ioo (c0 i) (d0 i)) ∧
          H.regularizedStageStart T 0 last = 0 ∧
          H.regularizedStageEnd T v first = v ∧
          (∀ x : J, H.regularizedStageStart T 0 x.val <
            H.regularizedStageEnd T v x.val) ∧
          ∀ a ∈ Ioo 0 a0,
            ∃ (lo hi : J → ℝ) (s : Fin (2 * N + 3) → ℝ),
              StrictMono s ∧ s 0 = a ∧ s (Fin.last (2 * N + 2)) = v ∧
              s ⟨2 * N + 1, by omega⟩ = b ∧
              (∀ k, s ⟨2 * k.val, by omega⟩ = lo (j k) ∧
                s ⟨2 * k.val + 1, by omega⟩ = hi (j k)) ∧
              (∀ k, s ⟨2 * k.val + 1, by omega⟩ = c (e k) ∧
                s ⟨2 * k.val + 2, by omega⟩ = d (e k)) ∧
              lo jl = a ∧ hi jf = b ∧
              (∀ i, hi (jn i) = c i ∧ lo (jo i) = d i) ∧
              (∀ x : J, H.regularizedStageStart T 0 x.val < lo x ∧ lo x < hi x ∧
                hi x < H.regularizedStageEnd T v x.val) ∧
              T - a ^ 2 ∈ Icc (H.time last) (H.stageEndTime last) ∧
              (∀ x : J, H.regularizedStageStart T a x.val ≤ lo x ∧ lo x ≤ hi x ∧
                hi x ≤ H.regularizedStageEnd T v x.val) ∧
              Manifold.absolutelyContinuousOnInterval ThreeModel (gamma jl) 0 a := by
  classical
  intro J E jo jn jf jl N
  have hupperClosed : T ∈ Icc (H.time last) (H.stageEndTime last) :=
    ⟨hupper.1.le, hupper.2⟩
  have hscalarClock : ∀ j : J,
      ∀ r ∈ Ioo (H.regularizedStageStart T 0 j.val) (H.regularizedStageEnd T v j.val),
      ∀ x : (H.stage j.val).Carrier,
        -B ≤ metricScalarAt (H.stageMetric j.val (T - r ^ 2)) x := by
    intro j r hr x
    exact hscalar j.val (T - r ^ 2) (H.mapsTo_regularizedStage_Ioo T 0 v j.val hr) x
  obtain ⟨DT, ST, hST, hmetricT, _, _, _, cTail, b, lowT, highT,
      _, hmaxb, hbv, hb0, hlowT, hhighT, hregT,
      alphaT, hsmoothT, hgeoT, hcenterT, hgermT, hvalueT, hvelocityT, hactionT⟩ :=
    H.exists_smooth_terminal_stage_piece first last hle hv hupperClosed hpast hscalarClock
      gamma hgammaAC hgammaInt hgammaNodes hmin hC1Atv
  have hmb :
      (H.regularizedStageStart T 0 first + H.regularizedStageEnd T v first) / 2 < b :=
    (le_max_right cTail _).trans_lt hmaxb
  obtain ⟨C, D, hCs, hsD, W, FC, SS, hold, hnew, c0, d0, eta, hphysical, _⟩ :=
    H.exists_positive_prefix_survivor_collars first last hle hv hupperClosed hpast
      hscalarClock gamma hgammaAC hgammaInt hgammaNodes hmin last le_rfl hupper
      b ⟨hb0, hbv⟩ hmb hcross
  have hclips (i : E) :
      H.regularizedStageStart T 0 i.val.succ < c0 i ∧
      c0 i < Real.sqrt (T - H.time i.val.succ) ∧
      Real.sqrt (T - H.time i.val.succ) < d0 i ∧
      d0 i < H.regularizedStageEnd T v i.val.castSucc := by
    rcases hphysical i with ⟨_, _, _, _, _, _, _, _, _, _, _,
      hcw, hwd, _, hclipNew, hclipOld, _⟩
    exact ⟨hclipNew, hcw, hwd, hclipOld⟩
  obtain ⟨j, e, c, d, a0, hj0, hjLast, hjEvent, ha0, ha0b,
      hcollar, hstart, hend, hpieces⟩ :=
    H.exists_ordered_prefix_piece_intervals first last hle hupper hpast hbv hmb
      c0 d0 hclips
  obtain ⟨lastPos, _, _, hchar, _, _, _, hpositive, _⟩ :=
    H.exists_positive_regularized_stage_interval first last hle hv hupperClosed hpast
  have hlastPos : lastPos = last := hchar.mpr hupper.1
  have hpositiveOriginal (x : J) :
      H.regularizedStageStart T 0 x.val < H.regularizedStageEnd T v x.val := by
    apply hpositive x.val x.property.1
    simpa only [hlastPos] using x.property.2
  refine ⟨DT, ST, b, lowT, highT, alphaT, hST, hmetricT, hb0, hbv, hmb,
    hlowT, hhighT, hregT, hsmoothT, hgeoT, hcenterT, hgermT, hvalueT, hvelocityT, hactionT,
    C, D, hCs, hsD, W, FC, SS, hold, hnew, c0, d0, eta, hphysical,
    j, e, c, d, a0, hj0, hjLast, hjEvent, ha0, ha0b, hcollar, hstart, hend,
    hpositiveOriginal, ?_⟩
  intro a ha
  obtain ⟨lo, hi, s, hs, hs0, hsv, hsb, hsO, hsS, hlo, hhi, hjoin, hgap⟩ := hpieces a ha
  have haInterval :
      a ∈ Ioo (H.regularizedStageStart T 0 last) (H.regularizedStageEnd T v last) := by
    rw [← hlo]
    exact ⟨(hgap jl).1, (hgap jl).2.1.trans (hgap jl).2.2⟩
  have haClock : T - a ^ 2 ∈ H.stageDomain last :=
    H.mapsTo_regularizedStage_Ioo T 0 v last haInterval
  have hupperCut : T - a ^ 2 ∈ Icc (H.time last) (H.stageEndTime last) :=
    ⟨H.time_le_of_mem_stageDomain haClock, H.le_stageEndTime_of_mem_stageDomain haClock⟩
  have haLo (x : J) : a ≤ lo x := by
    obtain ⟨k, rfl⟩ := j.surjective x
    rw [← (hsO k).1, ← hs0]
    exact hs.monotone (Fin.zero_le _)
  have hboundsCut (x : J) :
      H.regularizedStageStart T a x.val ≤ lo x ∧ lo x ≤ hi x ∧
        hi x ≤ H.regularizedStageEnd T v x.val := by
    refine ⟨?_, (hgap x).2.1.le, (hgap x).2.2.le⟩
    rw [H.regularizedStageStart_eq_max_zero T ha.1.le]
    exact max_le (haLo x) (hgap x).1.le
  have hprefixSubset : uIcc (0 : ℝ) a ⊆
      uIcc (H.regularizedStageStart T 0 last) (H.regularizedStageEnd T v last) := by
    rw [hstart, uIcc_of_le ha.1.le, uIcc_of_le (ha.1.le.trans haInterval.2.le)]
    exact Icc_subset_Icc le_rfl haInterval.2.le
  have hprefixAC : Manifold.absolutelyContinuousOnInterval ThreeModel (gamma jl) 0 a :=
    Manifold.absolutelyContinuousOnInterval_mono (hgammaAC jl) hprefixSubset
  exact ⟨lo, hi, s, hs, hs0, hsv, hsb, hsO, hsS, hlo, hhi, hjoin, hgap,
    hupperCut, hboundsCut, hprefixAC⟩

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory
