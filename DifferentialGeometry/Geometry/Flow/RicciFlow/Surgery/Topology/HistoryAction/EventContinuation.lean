import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.HistoryActionJoin
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.HistoryAction.Density
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.HistoryAction.TimeContinuity
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.TerminalClosedSolution

noncomputable section

open Set Filter MeasureTheory
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.PDE.RicciFlow.Perelman
open scoped Manifold ContDiff Topology Interval

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory

universe u
variable (H : ObservedHistory.{u})

theorem exists_regularizedC1ActionValues_extend_at_event
    (i : Fin H.eventCount) (last : Fin (H.eventCount + 1)) (hl : i.succ ≤ last)
    {T u w A : ℝ} (hevent : T - w ^ 2 = H.time i.succ)
    (p : (H.stage last).Carrier) (z : (H.event i).old)
    (hnew : A ∈ H.regularizedC1ActionValues i.succ last hl T u w p ((H.event i).oldOutput z))
    (ε : ℝ) (hε : 0 < ε) :
    ∃ d : ℝ, w < d ∧ ∀ v ∈ Ioo w d,
      ∃ A' ∈ H.regularizedC1ActionValues i.castSucc last (i.castSucc_le_succ.trans hl) T u v p z.val.val,
        A' < A + ε := by
  have hw0 : 0 ≤ w := hnew.1.trans hnew.2.1
  let E := H.event i
  let L := E.terminal
  let x := E.oldTerminal z
  have hzx : z.val.val = x.val := (E.oldTerminal_eq z).symm
  let W : TopologicalSpace.Opens E.incoming.terminalRegularOpen := ⊤
  let y : W := ⟨x, mem_univ x⟩
  let S := L.closedSolution W E.incoming.lt.le
  have hS := L.closedSolution_isSolutionOn W le_rfl E.incoming.lt
  let d := Real.sqrt (T - H.time i.castSucc)
  have hTd : 0 ≤ T - H.time i.castSucc := by
    have htime := (H.time_strictMono i.castSucc_lt_succ).le
    nlinarith [sq_nonneg w]
  have hd2 : d ^ 2 = T - H.time i.castSucc := Real.sq_sqrt hTd
  have hwd : w < d := by
    apply (Real.lt_sqrt hw0).mpr
    have htime := H.time_strictMono i.castSucc_lt_succ
    linarith
  have hclock : ∀ r ∈ Icc w d, T - r ^ 2 ∈ (RealTimeInterval.closed
      (H.time i.castSucc) (H.time i.succ) E.incoming.lt.le).carrier := by
    intro r hr
    have hr0 := hw0.trans hr.1
    have hwr := pow_le_pow_left₀ hw0 hr.1 2
    have hrd := pow_le_pow_left₀ hr0 hr.2 2
    constructor <;> linarith
  let f : ℝ → ℝ := fun r => 2 * r ^ 2 * S.scalar (T - r ^ 2) y
  have hcont : ContinuousOn f (Icc w d) := by
    apply ContinuousOn.mul
    · fun_prop
    · exact hS.scalarCont.comp
        (f := fun r : ℝ => (T - r ^ 2, y)) (by fun_prop)
        (fun r hr => ⟨hclock r hr, mem_univ y⟩)
  have hfi : IntervalIntegrable f volume w d := hcont.intervalIntegrable_of_Icc hwd.le
  let F : ℝ → ℝ := fun v => ∫ r in w..v, f r
  have hF : ContinuousOn F (Icc w d) := by
    simpa only [uIcc_of_le hwd.le] using intervalIntegral.continuousOn_primitive_interval' hfi
      (show w ∈ uIcc w d from left_mem_uIcc)
  have hF0 : F w = 0 := intervalIntegral.integral_same
  have hnear : ∀ᶠ v in 𝓝[>] w, F v < ε := by
    have hh := (hF w ⟨le_rfl, hwd.le⟩).eventually
      (Iio_mem_nhds (by simpa only [hF0] using hε))
    exact hh.filter_mono (le_inf nhdsWithin_le_nhds
      (le_principal_iff.mpr (Icc_mem_nhdsGT hwd)))
  obtain ⟨δ, hδ, hδsub⟩ := (mem_nhdsGT_iff_exists_Ioo_subset' hwd).mp
    (hnear.and (Ioo_mem_nhdsGT hwd))
  refine ⟨δ, hδ, ?_⟩
  intro v hv
  obtain ⟨hvF, hwv, hvd⟩ := hδsub hv
  have hv0 := hw0.trans hwv.le
  have hpast : T - v ^ 2 ∈ H.stageDomain i.castSucc := by
    have hvclock := hclock v ⟨hwv.le, hvd.le⟩
    have hsq := (sq_lt_sq₀ hw0 hv0).mpr hwv
    simp only [stageDomain, Fin.lastCases_castSucc]
    exact ⟨hvclock.1, by linarith⟩
  have heq : EqOn f (H.stageRegularizedLagrangian i.castSucc T (fun _ => x.val))
      (uIoo w v) := by
    intro r hr
    rw [uIoo_of_le hwv.le] at hr
    have hsq := (sq_lt_sq₀ hw0 (hw0.trans hr.1.le)).mpr hr.1
    have hrt : T - r ^ 2 < H.time i.succ := by linarith
    have hv : lVelocity (I := ThreeModel) (fun _ : ℝ => x.val) r = 0 := by
      simp only [lVelocity, mfderiv_const]
      rfl
    rw [H.stageRegularizedLagrangian_castSucc]
    dsimp only [f, S, SolutionOn.scalar, SolutionFamily.scalar]
    rw [L.closedSolution_before W E.incoming.lt.le hrt,
      DifferentialGeometry.CheegerGromovCompactness.metricScalarAt_restrictOpen, DifferentialGeometry.CheegerGromovCompactness.metricScalarAt_restrictOpen]
    simp only [lRegularizedLagrangian, hv, map_zero, mul_zero, zero_add]
    rfl
  have hfi' : IntervalIntegrable f volume w v :=
    hfi.mono_set (by rw [uIcc_of_le hwv.le, uIcc_of_le hwd.le]; exact Icc_subset_Icc le_rfl hvd.le)
  have hi := hfi'.congr_uIoo heq
  have hact : H.stageRegularizedAction i.castSucc T (fun _ => x.val) w v = F v :=
    (intervalIntegral.integral_congr_uIoo heq).symm
  have hold : H.stageRegularizedAction i.castSucc T (fun _ => x.val) w v ∈
      H.regularizedC1ActionValues i.castSucc i.castSucc le_rfl T w v z.val.val x.val := by
    apply (H.mem_regularizedC1ActionValues_self i.castSucc z.val.val x.val).mpr
    exact ⟨hw0, hwv.le, by rw [hevent, H.stageEndTime_castSucc]; exact
      ⟨(H.time_strictMono i.castSucc_lt_succ).le, le_rfl⟩,
      hpast, (fun _ => x.val), contMDiff_const, hi, hzx.symm, rfl, rfl⟩
  rw [hzx]
  refine ⟨H.stageRegularizedAction i.castSucc T (fun _ => x.val) w v + A, ?_, ?_⟩
  · apply (H.mem_regularizedC1ActionValues_split_at_event (i.castSucc_le_succ.trans hl) i le_rfl hl
      hnew.1 (hnew.2.1.trans hwv.le) hnew.2.2.1 hpast p x.val).mpr
    have hw : Real.sqrt (T - H.time i.succ) = w := by
      rw [show T - H.time i.succ = w ^ 2 by linarith, Real.sqrt_sq hw0]
    rw [hw]
    exact ⟨z, _, A, hold, hnew, rfl⟩
  · rw [hact]
    linarith

theorem exists_regularizedCost_lt_after_event
    (i : Fin H.eventCount) (last : Fin (H.eventCount + 1)) (hl : i.succ ≤ last)
    {T B u w b A : ℝ} (hwb : w < b)
    (hevent : T - w ^ 2 = H.time i.succ)
    (hupper : T - u ^ 2 ∈ H.stageDomain last)
    (hscalar : ∀ j : H.StageInterval i.castSucc last,
      ∀ t ∈ Ioo (H.regularizedStageStart T u j.val) (H.regularizedStageEnd T b j.val),
      ∀ z : (H.stage j.val).Carrier, -B ≤ metricScalarAt (H.stageMetric j.val (T - t ^ 2)) z)
    (p : (H.stage last).Carrier) (z : (H.event i).old)
    (hcost : H.regularizedCost i.succ last hl T B u w p ((H.event i).oldOutput z) = (A : WithTop ℝ))
    (ε : ℝ) (hε : 0 < ε) :
    ∃ d : ℝ, w < d ∧ d ≤ b ∧ ∀ v ∈ Ioo w d,
      H.regularizedCost i.castSucc last (i.castSucc_le_succ.trans hl) T B u v p z.val.val <
        ((A + ε : ℝ) : WithTop ℝ) := by
  have hne : (H.regularizedActionValues i.succ last hl T B u w p ((H.event i).oldOutput z)).Nonempty := by
    by_contra h
    have htop := H.regularizedCost_eq_top_of_no_competitor i.succ last hl T B u w p ((H.event i).oldOutput z)
      (Set.not_nonempty_iff_eq_empty.mp h)
    exact WithTop.coe_ne_top (hcost.symm.trans htop)
  obtain ⟨_, hvalue⟩ := hne
  have hu : 0 ≤ u := hvalue.1
  have huw : u ≤ w := hvalue.2.1
  have hw : 0 ≤ w := hu.trans huw
  have hb : 0 ≤ b := hw.trans hwb.le
  have hfloor : ∀ j : H.StageInterval i.succ last,
      ∀ t ∈ Ioo (H.regularizedStageStart T u j.val) (H.regularizedStageEnd T w j.val),
      ∀ z : (H.stage j.val).Carrier, -B ≤ metricScalarAt (H.stageMetric j.val (T - t ^ 2)) z := by
    intro j t ht z
    exact hscalar ⟨j.val, i.castSucc_le_succ.trans j.property.1, j.property.2⟩ t
      ⟨ht.1, ht.2.trans_le (H.regularizedStageEnd_monotoneOn T j.val hw hb hwb.le)⟩ z
  have hC1 : H.regularizedC1Cost i.succ last hl T u w p ((H.event i).oldOutput z) = (A : WithTop ℝ) := by
    rw [← H.regularizedCost_eq_regularizedC1Cost i.succ last hl T B u w hupper hfloor]
    exact hcost
  have hC1ne : (H.regularizedC1ActionValues i.succ last hl T u w p ((H.event i).oldOutput z)).Nonempty := by
    by_contra h
    have htop := H.regularizedC1Cost_eq_top_of_no_competitor i.succ last hl T u w p ((H.event i).oldOutput z)
      (Set.not_nonempty_iff_eq_empty.mp h)
    exact WithTop.coe_ne_top (hC1.symm.trans htop)
  have hlt : H.regularizedC1Cost i.succ last hl T u w p ((H.event i).oldOutput z) <
      ((A + ε / 2 : ℝ) : WithTop ℝ) := by
    rw [hC1]
    exact WithTop.coe_lt_coe.mpr (lt_add_of_pos_right A (half_pos hε))
  obtain ⟨_, ⟨C, hC, rfl⟩, hCA⟩ := exists_lt_of_csInf_lt
    (hC1ne.image (fun r : ℝ => (r : WithTop ℝ))) hlt
  obtain ⟨d, hwd, hd⟩ := H.exists_regularizedC1ActionValues_extend_at_event
    i last hl hevent p z hC (ε / 2) (half_pos hε)
  refine ⟨min d b, lt_min hwd hwb, min_le_right _ _, ?_⟩
  intro v hv
  have hvd : v < d := hv.2.trans_le (min_le_left _ _)
  have hvb : v ≤ b := hv.2.le.trans (min_le_right _ _)
  obtain ⟨C', hC', hsmall⟩ := hd v ⟨hv.1, hvd⟩
  have hfloorV : ∀ j : H.StageInterval i.castSucc last,
      ∀ t ∈ Ioo (H.regularizedStageStart T u j.val) (H.regularizedStageEnd T v j.val),
      ∀ z : (H.stage j.val).Carrier, -B ≤ metricScalarAt (H.stageMetric j.val (T - t ^ 2)) z := by
    intro j t ht z
    exact hscalar j t ⟨ht.1, ht.2.trans_le
      (H.regularizedStageEnd_monotoneOn T j.val (hw.trans hv.1.le) hb hvb)⟩ z
  refine (H.regularizedCost_le_of_competitor i.castSucc last (i.castSucc_le_succ.trans hl)
    T B u v p z.val.val (H.coe_mem_regularizedActionValues_of_mem_regularizedC1ActionValues
      i.castSucc last (i.castSucc_le_succ.trans hl) hfloorV p z.val.val hC')).trans_lt ?_
  apply WithTop.coe_lt_coe.mpr
  have hCA' := WithTop.coe_lt_coe.mp hCA
  linarith only [hsmall, hCA']

theorem tendsto_sInf_regularizedCost_after_event_of_minimum
    (i : Fin H.eventCount) (last : Fin (H.eventCount + 1)) (hl : i.succ ≤ last)
    {T B u w b A : ℝ} (hwb : w < b)
    (hevent : T - w ^ 2 = H.time i.succ)
    (hupper : T - u ^ 2 ∈ H.stageDomain last)
    (hscalar : ∀ j : H.StageInterval i.castSucc last,
      ∀ t ∈ Ioo (H.regularizedStageStart T u j.val) (H.regularizedStageEnd T b j.val),
      ∀ z : (H.stage j.val).Carrier, -B ≤ metricScalarAt (H.stageMetric j.val (T - t ^ 2)) z)
    (p : (H.stage last).Carrier) (z : (H.event i).old)
    (hcost : H.regularizedCost i.succ last hl T B u w p ((H.event i).oldOutput z) = (A : WithTop ℝ))
    (hmin : ∀ q : (H.stage i.succ).Carrier,
      (A : WithTop ℝ) ≤ H.regularizedCost i.succ last hl T B u w p q) :
    Tendsto (fun v : ℝ => sInf (range (H.regularizedCost i.castSucc last
      (i.castSucc_le_succ.trans hl) T B u v p))) (𝓝[>] w) (𝓝 (A : WithTop ℝ)) := by
  have hne : (H.regularizedActionValues i.succ last hl T B u w p ((H.event i).oldOutput z)).Nonempty := by
    by_contra h
    have htop := H.regularizedCost_eq_top_of_no_competitor i.succ last hl T B u w p ((H.event i).oldOutput z)
      (Set.not_nonempty_iff_eq_empty.mp h)
    exact WithTop.coe_ne_top (hcost.symm.trans htop)
  obtain ⟨_, hvalue⟩ := hne
  have hu : 0 ≤ u := hvalue.1
  have huw : u ≤ w := hvalue.2.1
  have hw : 0 ≤ w := hu.trans huw
  have hb : 0 ≤ b := hw.trans hwb.le
  have hkw : T - w ^ 2 ∈ H.stageDomain i.succ := hevent ▸ H.time_mem_stageDomain i.succ
  let value := fun v : ℝ => sInf (range (H.regularizedCost i.castSucc last
    (i.castSucc_le_succ.trans hl) T B u v p))
  have hvalue_le (v : ℝ) (q : (H.stage i.castSucc).Carrier) : value v ≤
      H.regularizedCost i.castSucc last (i.castSucc_le_succ.trans hl) T B u v p q := by
    apply csInf_le ?_ (mem_range_self q)
    refine ⟨((-(2 * B / 3) * (v ^ 3 - u ^ 3) : ℝ) : WithTop ℝ), ?_⟩
    rintro c ⟨y, rfl⟩
    exact H.regularizedCost_ge i.castSucc last (i.castSucc_le_succ.trans hl) T B u v p y
  have hvalue_lower {v : ℝ} (hv : v ∈ Ioo w b) :
      ((A - (2 * B / 3) * (v ^ 3 - w ^ 3) : ℝ) : WithTop ℝ) ≤ value v := by
    apply le_csInf ⟨_, mem_range_self z.val.val⟩
    rintro c ⟨q, rfl⟩
    apply H.regularizedCost_ge_of_prefix_lower_bound i.castSucc last
      (i.castSucc_le_succ.trans hl) hupper ?_ p q
      ⟨i.succ, i.castSucc_le_succ, hl⟩ ⟨huw, hv.1.le⟩ hkw hmin
    intro j t ht x
    exact hscalar j t ⟨ht.1, ht.2.trans_le
      (H.regularizedStageEnd_monotoneOn T j.val (hw.trans hv.1.le) hb hv.2.le)⟩ x
  change Tendsto value (𝓝[>] w) (𝓝 (A : WithTop ℝ))
  apply tendsto_order.2
  constructor
  · intro C hC
    cases C using WithTop.recTopCoe with
    | top => exact False.elim (not_lt_of_ge le_top hC)
    | coe C =>
      have hCA : C < A := WithTop.coe_lt_coe.mp hC
      have hc : ContinuousAt (fun v : ℝ => A - (2 * B / 3) * (v ^ 3 - w ^ 3)) w := by fun_prop
      have heventually : ∀ᶠ v in 𝓝[>] w, C < A - (2 * B / 3) * (v ^ 3 - w ^ 3) := by
        apply (hc.eventually (Ioi_mem_nhds (by simpa only [sub_self, mul_zero, sub_zero] using hCA))).filter_mono
        exact nhdsWithin_le_nhds
      filter_upwards [heventually, Ioo_mem_nhdsGT hwb] with v hv hvb
      exact (WithTop.coe_lt_coe.mpr hv).trans_le (hvalue_lower hvb)
  · intro C hC
    obtain ⟨r, hrA, hrC⟩ : ∃ r : ℝ, A < r ∧ (r : WithTop ℝ) < C := by
      cases C using WithTop.recTopCoe with
      | top => exact ⟨A + 1, by linarith, WithTop.coe_lt_top _⟩
      | coe C =>
        obtain ⟨r, hrA, hrC⟩ := exists_between (WithTop.coe_lt_coe.mp hC)
        exact ⟨r, hrA, WithTop.coe_lt_coe.mpr hrC⟩
    obtain ⟨d, hwd, _, hd⟩ := H.exists_regularizedCost_lt_after_event i last hl hwb hevent
      hupper hscalar p z hcost (r - A) (sub_pos.mpr hrA)
    filter_upwards [Ioo_mem_nhdsGT hwd] with v hv
    have hc := (hvalue_le v z.val.val).trans_lt (hd v hv)
    have hr : A + (r - A) = r := by ring
    rw [hr] at hc
    exact hc.trans hrC

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory

end
