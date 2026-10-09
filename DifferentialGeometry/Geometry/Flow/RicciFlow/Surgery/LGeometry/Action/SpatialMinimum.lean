import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.LGeometry.Cost.Continuity.CarrierBaseTime
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.LGeometry.Action.C1Attainment
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.LGeometry.Action.EndpointSemicontinuity
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.LGeometry.Action.Basic
set_option autoImplicit false

noncomputable section

open Set Filter MeasureTheory
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.PDE.RicciFlow.Perelman
open scoped Manifold ContDiff Topology Interval BigOperators

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory

universe u

theorem exists_spatial_regularizedCost_minimizer
    (H : ObservedHistory.{u})
    (first last : Fin (H.eventCount + 1)) (hle : first ≤ last)
    (T B u v : ℝ)
    (hupper : T - u ^ 2 ∈ H.stageDomain last)
    (hscalar : ∀ j : H.StageInterval first last,
      ∀ t ∈ Ioo (H.regularizedStageStart T u j.val) (H.regularizedStageEnd T v j.val),
      ∀ x : (H.stage j.val).Carrier, -B ≤ metricScalarAt (H.stageMetric j.val (T - t ^ 2)) x)
    (p : (H.stage last).Carrier)
    (hfinite : ∃ q : (H.stage first).Carrier,
      H.regularizedCost first last hle T B u v p q ≠ ⊤) :
    ∃ (q : (H.stage first).Carrier)
      (gamma : (j : H.StageInterval first last) → ℝ → (H.stage j.val).Carrier),
      (∀ j, ContMDiff 𝓘(ℝ, ℝ) ThreeModel 1 (gamma j)) ∧
      (∀ j, IntervalIntegrable (H.stageRegularizedLagrangian j.val T (gamma j)) volume
        (H.regularizedStageStart T u j.val) (H.regularizedStageEnd T v j.val)) ∧
      gamma ⟨last, hle, le_rfl⟩ u = p ∧ gamma ⟨first, le_rfl, hle⟩ v = q ∧
      (∀ (i : Fin H.eventCount) (hf : first ≤ i.castSucc) (hl : i.succ ≤ last),
        ∃ z : (H.event i).old,
          z.val.val = gamma ⟨i.castSucc, hf, i.castSucc_lt_succ.le.trans hl⟩
            (Real.sqrt (T - H.time i.succ)) ∧
          (H.event i).oldOutput z = gamma ⟨i.succ, hf.trans i.castSucc_lt_succ.le, hl⟩
            (Real.sqrt (T - H.time i.succ))) ∧
      let A := ∑ j : H.StageInterval first last, H.stageRegularizedAction j.val T (gamma j)
        (H.regularizedStageStart T u j.val) (H.regularizedStageEnd T v j.val);
      H.regularizedCost first last hle T B u v p q = (A : WithTop ℝ) ∧
      ∀ z : (H.stage first).Carrier,
        (A : WithTop ℝ) ≤ H.regularizedCost first last hle T B u v p z := by
  classical
  obtain ⟨q₀, hq₀⟩ := hfinite
  have hcost (q : (H.stage first).Carrier) :=
    H.regularizedCost_eq_regularizedC1Cost first last hle T B u v hupper hscalar p q
  have hq₀C1 : H.regularizedC1Cost first last hle T u v p q₀ ≠ ⊤ := by
    rwa [hcost q₀] at hq₀
  have hne : (H.regularizedC1ActionValues first last hle T u v p q₀).Nonempty := by
    by_contra hn
    exact hq₀C1 (H.regularizedC1Cost_eq_top_of_no_competitor first last hle T u v p q₀
      (Set.not_nonempty_iff_eq_empty.mp hn))
  obtain ⟨value, hvalue⟩ := hne
  have hcont := H.lowerSemicontinuous_regularizedC1Cost_past_endpoint first last hle
    hvalue.1 hvalue.2.1 hupper hvalue.2.2.2.1 hscalar p
  obtain ⟨q, _, hq⟩ := LowerSemicontinuousOn.exists_isMinOn
    (show (univ : Set (H.stage first).Carrier).Nonempty from ⟨q₀, mem_univ q₀⟩)
    isCompact_univ (hcont.lowerSemicontinuousOn univ)
  have hqfinite : H.regularizedC1Cost first last hle T u v p q ≠ ⊤ :=
    ne_top_of_le_ne_top hq₀C1 (hq (mem_univ q₀))
  obtain ⟨gamma, hgamma, hint, hrecent, hpast, hnodes, haction⟩ :=
    H.exists_regularizedC1Cost_minimizer_of_ne_top first last hle T B u v
      hupper hscalar p q hqfinite
  refine ⟨q, gamma, hgamma, hint, hrecent, hpast, hnodes, ?_, ?_⟩
  · exact (hcost q).trans haction.symm
  · intro z
    exact haction.trans_le ((hq (mem_univ z)).trans_eq (hcost z).symm)

private theorem exists_constant_tail_action_lt
    {M : Type*} [TopologicalSpace M] [ChartedSpace ThreeSpace M]
    [IsManifold ThreeModel ∞ M] [T2Space M]
    {D : RealTimeInterval} (S : SolutionOn (I := ThreeModel) (M := M) D)
    (hS : IsSolutionOn S) (T a v : ℝ) (hav : a < v)
    (gamma : ℝ → M) (hgamma : ContMDiff 𝓘(ℝ, ℝ) ThreeModel 1 gamma)
    (hreg : T - v ^ 2 ∈ D.regular) (hvel : lVelocity (I := ThreeModel) gamma v ≠ 0) :
    ∃ c ∈ Ioo a v,
      (∀ r ∈ Icc c v, T - r ^ 2 ∈ D.regular) ∧
      IntervalIntegrable (lRegularizedLagrangian S T gamma) volume c v ∧
      IntervalIntegrable (lRegularizedLagrangian S T (fun _ => gamma c)) volume c v ∧
      lRegularizedAction S T (fun _ => gamma c) c v < lRegularizedAction S T gamma c v := by
  let F : ℝ × ℝ → ℝ := fun q => lRegularizedLagrangian S T gamma q.2 -
    2 * q.2 ^ 2 * S.scalar (T - q.2 ^ 2) (gamma q.1)
  have hlag : ContinuousAt (fun r => lRegularizedLagrangian S T gamma r) v := by
    have hsub : ContinuousOn (fun q : ℝ × ℝ => lRegularizedLagrangian S q.1 gamma q.2)
        {q : ℝ × ℝ | q.1 - q.2 ^ 2 ∈ D.regular} :=
      (lRegularizedLagrangian_continuousOn_carrier S hS gamma hgamma).mono
        (fun _ h => D.regular_subset h)
    have hraw : ContinuousAt (fun q : ℝ × ℝ => lRegularizedLagrangian S q.1 gamma q.2) (T, v) :=
      hsub.continuousAt
      ((D.regular_isOpen.preimage (by fun_prop : Continuous (fun q : ℝ × ℝ =>
        q.1 - q.2 ^ 2))).mem_nhds hreg)
    exact hraw.comp (continuousAt_const.prodMk continuousAt_id)
  have hscalar : ContinuousAt (fun q : ℝ × ℝ =>
      S.scalar (T - q.2 ^ 2) (gamma q.1)) (v, v) := by
    have hraw : ContinuousAt (fun q : ℝ × M => S.scalar q.1 q.2) (T - v ^ 2, gamma v) :=
      (hS.scalarCont.mono
      (prod_mono D.regular_subset (subset_refl univ))).continuousAt
      ((D.regular_isOpen.prod isOpen_univ).mem_nhds ⟨hreg, mem_univ _⟩)
    exact hraw.comp (f := fun q : ℝ × ℝ => (T - q.2 ^ 2, gamma q.1)) ((by fun_prop : ContinuousAt
      (fun q : ℝ × ℝ => T - q.2 ^ 2) (v, v)).prodMk
        (hgamma.continuous.continuousAt.comp continuousAt_fst))
  have hF : ContinuousAt F (v, v) := by
    exact (hlag.comp continuousAt_snd).sub
      ((by fun_prop : ContinuousAt (fun q : ℝ × ℝ => 2 * q.2 ^ 2) (v, v)).mul hscalar)
  have hFpos : 0 < F (v, v) := by
    have hp := (S.base.metric (T - v ^ 2)).pos (gamma v) _ hvel
    dsimp only [F, lRegularizedLagrangian]
    linarith
  obtain ⟨U, hU, V, hV, hUV⟩ := mem_nhds_prod_iff.mp
    (hF.eventually (Ioi_mem_nhds hFpos))
  have hnear : {r : ℝ | a < r ∧ r ∈ U ∧ r ∈ V ∧ T - r ^ 2 ∈ D.regular} ∈ 𝓝 v := by
    filter_upwards [Ioi_mem_nhds hav, hU, hV,
      (D.regular_isOpen.preimage (by fun_prop : Continuous (fun r : ℝ =>
        T - r ^ 2))).mem_nhds hreg] with r hra hrU hrV hrD
    exact ⟨hra, hrU, hrV, hrD⟩
  obtain ⟨c, hcv, hc⟩ := mem_nhdsLE_iff_exists_Icc_subset.mp (nhdsWithin_le_nhds hnear)
  have hca := (hc ⟨le_rfl, hcv.le⟩).1
  have hclock (r : ℝ) (hr : r ∈ Icc c v) := (hc hr).2.2.2
  have hcont (eta : ℝ → M) (heta : ContMDiff 𝓘(ℝ, ℝ) ThreeModel 1 eta) :
      ContinuousOn (lRegularizedLagrangian S T eta) (Icc c v) := by
    exact (lRegularizedLagrangian_continuousOn_carrier S hS eta heta).comp
      (f := fun r : ℝ => (T, r))
      (continuousOn_const.prodMk continuousOn_id)
      (fun r hr => D.regular_subset (hclock r hr))
  have hconst (r : ℝ) : lRegularizedLagrangian S T (fun _ => gamma c) r =
      2 * r ^ 2 * S.scalar (T - r ^ 2) (gamma c) := by
    have hv : lVelocity (I := ThreeModel) (fun _ : ℝ => gamma c) r = 0 := by
      simp only [lVelocity, mfderiv_const]
      rfl
    simp only [lRegularizedLagrangian, hv, map_zero, mul_zero, zero_add]
  have hstrict (r : ℝ) (hr : r ∈ Icc c v) :
      lRegularizedLagrangian S T (fun _ => gamma c) r < lRegularizedLagrangian S T gamma r := by
    have hh := hUV (show (c, r) ∈ U ×ˢ V from
      ⟨(hc ⟨le_rfl, hcv.le⟩).2.1, (hc hr).2.2.1⟩)
    change 0 < F (c, r) at hh
    rw [hconst]
    exact sub_pos.mp hh
  refine ⟨c, ⟨hca, hcv⟩, hclock,
    (hcont gamma hgamma).intervalIntegrable_of_Icc hcv.le,
    (hcont (fun _ => gamma c) contMDiff_const).intervalIntegrable_of_Icc hcv.le, ?_⟩
  exact intervalIntegral.integral_lt_integral_of_continuousOn_of_le_of_exists_lt hcv
    (hcont (fun _ => gamma c) contMDiff_const) (hcont gamma hgamma)
    (fun r hr => (hstrict r (Ioc_subset_Icc_self hr)).le)
    ⟨v, ⟨hcv.le, le_rfl⟩, hstrict v ⟨hcv.le, le_rfl⟩⟩

theorem past_velocity_eq_zero_of_spatial_minimum
    (H : ObservedHistory.{u})
    (first last : Fin (H.eventCount + 1)) (hle : first ≤ last)
    {T B u v : ℝ} (hu : 0 ≤ u) (huv : u < v)
    (hupper : T - u ^ 2 ∈ Icc (H.time last) (H.stageEndTime last))
    (hpast : T - v ^ 2 ∈ Ioo (H.time first) (H.stageEndTime first))
    (hscalar : ∀ j : H.StageInterval first last,
      ∀ r ∈ Ioo (H.regularizedStageStart T u j.val) (H.regularizedStageEnd T v j.val),
      ∀ x : (H.stage j.val).Carrier, -B ≤ metricScalarAt (H.stageMetric j.val (T - r ^ 2)) x)
    (gamma : (j : H.StageInterval first last) → ℝ → (H.stage j.val).Carrier)
    (hgamma : ∀ j, Manifold.absolutelyContinuousOnInterval ThreeModel (gamma j)
      (H.regularizedStageStart T u j.val) (H.regularizedStageEnd T v j.val))
    (hgammaFirst : ContMDiff 𝓘(ℝ, ℝ) ThreeModel 1 (gamma ⟨first, le_rfl, hle⟩))
    (hint : ∀ j, IntervalIntegrable (H.stageRegularizedLagrangian j.val T (gamma j)) volume
      (H.regularizedStageStart T u j.val) (H.regularizedStageEnd T v j.val))
    (hnodes : ∀ (i : Fin H.eventCount) (hf : first ≤ i.castSucc) (hl : i.succ ≤ last),
      ∃ z : (H.event i).old,
        z.val.val = gamma ⟨i.castSucc, hf, i.castSucc_lt_succ.le.trans hl⟩
          (Real.sqrt (T - H.time i.succ)) ∧
        (H.event i).oldOutput z = gamma ⟨i.succ, hf.trans i.castSucc_lt_succ.le, hl⟩
          (Real.sqrt (T - H.time i.succ)))
    (hmin : ∀ q : (H.stage first).Carrier,
      H.regularizedExtendedAction first last T B u v gamma ≤
        H.regularizedCost first last hle T B u v (gamma ⟨last, hle, le_rfl⟩ u) q) :
    lVelocity (I := ThreeModel) (gamma ⟨first, le_rfl, hle⟩) v = 0 := by
  classical
  by_contra hvel
  let jfirst : H.StageInterval first last := ⟨first, le_rfl, hle⟩
  let a := H.regularizedStageStart T u first
  have hpastD := H.mem_stageDomain_of_mem_Ioo hpast
  have hend : H.regularizedStageEnd T v first = v :=
    H.regularizedStageEnd_eq_of_mem_stageDomain (hu.trans huv.le) hpastD
  have hbounds := H.regularizedStage_bounds hu huv.le hupper hpastD jfirst
  have havle : a ≤ v := by simpa only [a, jfirst, hend] using hbounds.2.1
  have hclocks := H.regularizedStage_endpoint_clocks hupper huv.le hu jfirst
  have hav : a < v := by
    apply lt_of_le_of_ne havle
    intro heq
    have hphysical : T - a ^ 2 = min (T - u ^ 2) (H.stageEndTime first) := hclocks.1
    have hstrict : T - v ^ 2 < min (T - u ^ 2) (H.stageEndTime first) := by
      apply lt_min _ hpast.2
      have hs := (sq_lt_sq₀ hu (hu.trans huv.le)).mpr huv
      linarith only [hs]
    rw [heq] at hphysical
    exact hstrict.ne hphysical
  obtain ⟨D, S, hS, hlag, hreg⟩ :
      ∃ (D : RealTimeInterval) (S : SolutionOn (I := ThreeModel) (M := (H.stage first).Carrier) D),
        IsSolutionOn S ∧
        (∀ eta : ℝ → (H.stage first).Carrier,
          H.stageRegularizedLagrangian first T eta = lRegularizedLagrangian S T eta) ∧
        T - v ^ 2 ∈ D.regular := by
    cases first using Fin.lastCases with
    | last =>
      have hfinal : H.time (Fin.last H.eventCount) < H.horizon := by
        simpa only [H.stageEndTime_last] using hpast.1.trans hpast.2
      refine ⟨_, (H.finalSlab hfinal).flow, (H.finalSlab hfinal).equation,
        (fun eta => funext (H.stageRegularizedLagrangian_last hfinal T eta)), ?_⟩
      simpa only [RealTimeInterval.closed, RealTimeInterval.regular, H.stageEndTime_last] using hpast
    | cast i =>
      refine ⟨_, (H.event i).incoming.flow, (H.event i).incoming.equation,
        (fun eta => funext (H.stageRegularizedLagrangian_castSucc i T eta)), ?_⟩
      simpa only [RealTimeInterval.closedOpen, RealTimeInterval.regular,
        H.stageEndTime_castSucc] using hpast
  have haction (eta : ℝ → (H.stage first).Carrier) (l r : ℝ) :
      H.stageRegularizedAction first T eta l r = lRegularizedAction S T eta l r := by
    simp only [stageRegularizedAction, lRegularizedAction, hlag]
  obtain ⟨c, hc, _hclock, htail, hconst, hstrict⟩ := exists_constant_tail_action_lt
    S hS T a v hav (gamma jfirst) hgammaFirst hreg hvel
  let beta : ℝ → (H.stage first).Carrier := (Iic c).piecewise (gamma jfirst) (fun _ => gamma jfirst c)
  have hbetaAC : Manifold.absolutelyContinuousOnInterval ThreeModel beta a v := by
    exact Manifold.absolutelyContinuousOnInterval_piecewise_Iic
      (Manifold.absolutelyContinuousOnInterval_of_contMDiffOn hgammaFirst.contMDiffOn)
      (Manifold.absolutelyContinuousOnInterval_of_contMDiffOn contMDiffOn_const)
      hc.1.le hc.2.le rfl
  have hbetaLeft (r : ℝ) (hr : r ≤ c) : beta r = gamma jfirst r :=
    piecewise_eq_of_mem (Iic c) _ _ hr
  have hwhole : IntervalIntegrable (lRegularizedLagrangian S T (gamma jfirst)) volume a v := by
    simpa only [jfirst, hend, hlag, a] using hint jfirst
  have hhead : IntervalIntegrable (lRegularizedLagrangian S T (gamma jfirst)) volume a c :=
    hwhole.mono_set (by
      simpa only [uIcc_of_le hc.1.le, uIcc_of_le hav.le] using Icc_subset_Icc le_rfl hc.2.le)
  have hheadLag : EqOn (lRegularizedLagrangian S T beta)
      (lRegularizedLagrangian S T (gamma jfirst)) (uIoo a c) := by
    intro r hr
    rw [uIoo_of_le hc.1.le] at hr
    have hev : beta =ᶠ[𝓝 r] gamma jfirst := by
      filter_upwards [Iio_mem_nhds hr.2] with t ht
      exact hbetaLeft t (show t < c from ht).le
    have hval := hev.self_of_nhds
    have hmf := Filter.EventuallyEq.mfderiv_eq (I := 𝓘(ℝ, ℝ)) (I' := ThreeModel) hev
    have hv : lVelocity (I := ThreeModel) beta r = lVelocity (I := ThreeModel) (gamma jfirst) r := by
      with_unfolding_all exact congrArg (fun F => F (1 : ℝ)) hmf
    unfold lRegularizedLagrangian
    rw [hval, hv]
  have htailLag : EqOn (lRegularizedLagrangian S T beta)
      (lRegularizedLagrangian S T (fun _ => gamma jfirst c)) (uIoo c v) := by
    intro r hr
    rw [uIoo_of_le hc.2.le] at hr
    have hev : beta =ᶠ[𝓝 r] (fun _ => gamma jfirst c) := by
      filter_upwards [Ioi_mem_nhds hr.1] with t ht
      exact piecewise_eq_of_notMem (Iic c) _ _ (not_le.mpr (show c < t from ht))
    have hval := hev.self_of_nhds
    have hmf := Filter.EventuallyEq.mfderiv_eq (I := 𝓘(ℝ, ℝ)) (I' := ThreeModel) hev
    have hv : lVelocity (I := ThreeModel) beta r =
        lVelocity (I := ThreeModel) (fun _ : ℝ => gamma jfirst c) r := by
      with_unfolding_all exact congrArg (fun F => F (1 : ℝ)) hmf
    unfold lRegularizedLagrangian
    rw [hval, hv]
  have hbetaHead := hhead.congr_uIoo hheadLag.symm
  have hbetaTail := hconst.congr_uIoo htailLag.symm
  have hbetaInt := hbetaHead.trans hbetaTail
  have hbetaStrict : H.stageRegularizedAction first T beta a v <
      H.stageRegularizedAction first T (gamma jfirst) a v := by
    rw [haction, haction,
      ← lRegularizedAction_add S T beta a c v hbetaHead hbetaTail,
      ← lRegularizedAction_add S T (gamma jfirst) a c v hhead htail]
    change (∫ r in a..c, lRegularizedLagrangian S T beta r) +
      (∫ r in c..v, lRegularizedLagrangian S T beta r) < _
    rw [intervalIntegral.integral_congr_uIoo hheadLag,
      intervalIntegral.integral_congr_uIoo htailLag]
    exact add_lt_add_right hstrict _
  let delta := Function.update gamma jfirst beta
  have hdeltaFirst : delta jfirst = beta := Function.update_self ..
  have hdeltaOther (j : H.StageInterval first last) (hj : j ≠ jfirst) :
      delta j = gamma j := Function.update_of_ne hj ..
  have hdeltaStart (j : H.StageInterval first last) :
      delta j (H.regularizedStageStart T u j.val) = gamma j (H.regularizedStageStart T u j.val) := by
    by_cases hj : j = jfirst
    · subst j
      rw [hdeltaFirst]
      exact hbetaLeft a hc.1.le
    · rw [hdeltaOther j hj]
  have hdeltaAC (j : H.StageInterval first last) :
      Manifold.absolutelyContinuousOnInterval ThreeModel (delta j)
        (H.regularizedStageStart T u j.val) (H.regularizedStageEnd T v j.val) := by
    by_cases hj : j = jfirst
    · subst j
      simpa only [hdeltaFirst, jfirst, hend, a] using hbetaAC
    · rw [hdeltaOther j hj]
      exact hgamma j
  have hdeltaInt (j : H.StageInterval first last) :
      IntervalIntegrable (H.stageRegularizedLagrangian j.val T (delta j)) volume
        (H.regularizedStageStart T u j.val) (H.regularizedStageEnd T v j.val) := by
    by_cases hj : j = jfirst
    · subst j
      simpa only [hdeltaFirst, jfirst, hend, a, hlag] using hbetaInt
    · rw [hdeltaOther j hj]
      exact hint j
  have hmember : H.regularizedExtendedAction first last T B u v delta ∈
      H.regularizedActionValues first last hle T B u v
        (gamma ⟨last, hle, le_rfl⟩ u) (delta jfirst v) := by
    refine ⟨hu, huv.le, hupper, hpastD, delta, hdeltaAC, ?_, rfl, ?_, rfl⟩
    · have hh := hdeltaStart ⟨last, hle, le_rfl⟩
      rwa [H.regularizedStageStart_eq_of_mem_Icc hu hupper] at hh
    · intro i hf hl
      obtain ⟨z, hzold, hznew⟩ := hnodes i hf hl
      have ho := hdeltaStart ⟨i.castSucc, hf, i.castSucc_lt_succ.le.trans hl⟩
      rw [H.regularizedStageStart_castSucc_eq_event_clock hupper i hl] at ho
      have hne : (⟨i.succ, hf.trans i.castSucc_lt_succ.le, hl⟩ : H.StageInterval first last) ≠ jfirst := by
        intro heq
        exact (hf.trans_lt i.castSucc_lt_succ).ne (congrArg Subtype.val heq).symm
      refine ⟨z, hzold.trans ho.symm, ?_⟩
      rw [hdeltaOther _ hne]
      exact hznew
  have hbound := (hmin (delta jfirst v)).trans
    (H.regularizedCost_le_of_competitor first last hle T B u v
      (gamma ⟨last, hle, le_rfl⟩ u) (delta jfirst v) hmember)
  rw [H.regularizedExtendedAction_eq_sum_action first last hu huv.le hupper hpastD gamma hint
      (fun j => by
        filter_upwards [ae_restrict_mem measurableSet_Ioo] with r hr
        exact hscalar j r hr (gamma j r)),
    H.regularizedExtendedAction_eq_sum_action first last hu huv.le hupper hpastD delta hdeltaInt
      (fun j => by
        filter_upwards [ae_restrict_mem measurableSet_Ioo] with r hr
        exact hscalar j r hr (delta j r))] at hbound
  have hsum := WithTop.coe_le_coe.mp hbound
  apply not_lt_of_ge hsum
  apply Finset.sum_lt_sum
  · intro j _
    by_cases hj : j = jfirst
    · subst j
      simpa only [hdeltaFirst, jfirst, hend, a] using hbetaStrict.le
    · simp only [hdeltaOther j hj, le_refl]
  · refine ⟨jfirst, Finset.mem_univ _, ?_⟩
    simpa only [hdeltaFirst, jfirst, hend, a] using hbetaStrict

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory
