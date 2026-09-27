import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.HistoryLGeometry.JacobianLimit
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.SurvivorChartMetric
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.TerminalClosedSolution

set_option autoImplicit false

noncomputable section

open Set Filter
open scoped Topology Manifold ContDiff

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory

open DifferentialGeometry.Geometry.Curvature (metricScalarAt RealTimeInterval)
open DifferentialGeometry.PDE.RicciFlow.Perelman
open DifferentialGeometry.Integral.Measure (paramDensity)
open DifferentialGeometry.Tensor.Coordinates (chartModelBasis)

open private sqrt_det_inner_comp exp_sub_log_normalization exists_contMDiff_eqOn_Icc from
  DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.HistoryLGeometry.JacobianLimit

universe u

section AnyWindow

variable {H : ObservedHistory.{u}} {lo hi : Fin (H.eventCount + 1)} {T : ℝ}
  (W : H.LWindow lo hi T) {x : W.X} {Zx : TangentSpace ThreeModel x}
  (hdom : W.b ∈ lRegularizedDomain W.S T x Zx)

include hdom in
private theorem exists_nhds_lRegularizedDomain_of_window :
    ∃ V : Set ThreeSpace, IsOpen V ∧ (Zx : ThreeSpace) ∈ V ∧
      (∀ Z ∈ V, W.b ∈ lRegularizedDomain W.S T x Z) ∧
      ∀ s ∈ Icc 0 W.b, MDifferentiableAt 𝓘(ℝ, ThreeSpace) ThreeModel
        (fun Z : ThreeSpace => lRegularizedCurve W.S T x (Z : TangentSpace ThreeModel x) s)
        (Zx : ThreeSpace) := by
  obtain ⟨α, J, hJo, hJc, h0J, hbJ, hcurve⟩ := hdom
  obtain ⟨V, hV, hZV, K, hK, hKc, h0K, hbK, fam, hfam, hfamc⟩ :=
    lRegularizedFamily_extend W.S W.solution T hJo hJc h0J hbJ hcurve
  refine ⟨V, hV, hZV, fun Z hZ => ⟨_, K, hK, hKc, h0K, hbK, hfamc Z hZ⟩, fun s hs => ?_⟩
  have hsK : s ∈ K := hKc.Icc_subset h0K hbK hs
  let z : ThreeSpace := Zx
  have hzV : z ∈ V := hZV
  have hsmooth : MDifferentiableAt 𝓘(ℝ, ThreeSpace) ThreeModel (fun Z => fam (Z, s)) z :=
    (((hfam (z, s) ⟨hzV, hsK⟩).contMDiffAt ((hV.prod hK).mem_nhds ⟨hzV, hsK⟩)).comp z
      (contMDiffAt_id.prodMk contMDiffAt_const)).mdifferentiableAt (by simp)
  refine hsmooth.congr_of_eventuallyEq ?_
  filter_upwards [hV.mem_nhds hzV] with Z hZ
  exact lRegularizedCurve_eqOn W.S W.solution T hK hKc h0K (hfamc Z hZ) hsK


include hdom in
private theorem exists_contMDiffOn_lRegularizedCurve_of_window :
    ∃ K : Set ℝ, IsOpen K ∧ IsPreconnected K ∧ Icc 0 W.b ⊆ K ∧
      ContMDiffOn 𝓘(ℝ, ℝ) ThreeModel ∞ (lRegularizedCurve W.S T x Zx) K := by
  obtain ⟨α, J, hJo, hJc, h0J, hbJ, hcurve⟩ := hdom
  obtain ⟨V, hV, hZV, K, hK, hKc, h0K, hbK, fam, hfam, hfamc⟩ :=
    lRegularizedFamily_extend W.S W.solution T hJo hJc h0J hbJ hcurve
  let z : ThreeSpace := Zx
  have hzV : z ∈ V := hZV
  refine ⟨K, hK, hKc, hKc.Icc_subset h0K hbK, ?_⟩
  have hs : ContMDiffOn 𝓘(ℝ, ℝ) ThreeModel ∞ (fun s => fam (z, s)) K :=
    hfam.comp (contMDiff_const.prodMk contMDiff_id).contMDiffOn fun s hs => ⟨hzV, hs⟩
  exact hs.congr fun s hsK => lRegularizedCurve_eqOn W.S W.solution T hK hKc h0K
    (hfamc z hzV) hsK

variable {B : ℝ} (hfloor : ∀ j, ∀ t ∈ H.stageDomain j, ∀ y : (H.stage j).Carrier,
  -B ≤ metricScalarAt (H.stageMetric j t) y)


end AnyWindow

section SeamBaseWindow

variable {H : ObservedHistory.{u}} {i : Fin H.eventCount} {T : ℝ}
  (W : H.LWindow i.castSucc i.succ T)

private theorem metric_eq_localPullMetric_of_seamBase (ha : W.a = 0) (hT : H.time i.succ = T) :
    W.S.base.metric T = localPullMetric (H.stageMetric i.succ T)
      (W.f ⟨i.succ, i.castSucc_lt_succ.le, le_rfl⟩) (W.localDiffeomorph _) := by
  ext z u w
  rw [localPullMetric_inner]
  set fo := W.f ⟨i.castSucc, le_rfl, i.castSucc_lt_succ.le⟩ with hfo
  set fn := W.f ⟨i.succ, i.castSucc_lt_succ.le, le_rfl⟩ with hfn
  have hcr := W.crossing i le_rfl le_rfl z
  obtain ⟨xo, -, hxo1, -⟩ := hcr
  set y : (H.event i).incoming.terminalRegularOpen := (H.event i).oldTerminal xo with hydef
  have hy : y.val = fo z := ((H.event i).oldTerminal_eq xo).trans hxo1
  obtain ⟨F, -, hyF, hFy, -, hFcross, hFmet⟩ :=
    MetricCutCapEvent.RegularCrossing.exists_survivor_partialDiffeomorph (H.event i) (p := y)
      (by rw [hy]; exact W.crossing i le_rfl le_rfl z)
  have hd : ∀ V : TangentSpace ThreeModel z,
      mfderiv ThreeModel ThreeModel F y (mfderiv ThreeModel ThreeModel fo z V) =
        mfderiv ThreeModel ThreeModel fn z V := fun V =>
    W.mfderiv_partialDiffeomorph_apply_eq_of_regularCrossing i le_rfl le_rfl z F hFcross hyF hy V
  have hmetT : H.stageMetric i.succ T = (H.event i).outputMetric := by
    rw [← hT, H.stageMetric_initial, H.event_output]
  set a : TangentSpace ThreeModel y := mfderiv ThreeModel ThreeModel fo z u with hadef
  set b : TangentSpace ThreeModel y := mfderiv ThreeModel ThreeModel fo z w with hbdef
  have hcont : (W.S.base.metric T).inner z u w = (H.event i).terminal.metric.inner y a b := by
    have hb : 0 < W.b := ha ▸ W.lt
    have hcs : H.time i.castSucc < T := hT ▸ H.time_strictMono i.castSucc_lt_succ
    set c := min W.b (Real.sqrt (T - H.time i.castSucc)) with hcdef
    have hc0 : 0 < c := lt_min hb (Real.sqrt_pos.2 (by linarith))
    have hcT' : c ^ 2 ≤ T - H.time i.castSucc := by
      calc c ^ 2 ≤ Real.sqrt (T - H.time i.castSucc) ^ 2 :=
            pow_le_pow_left₀ hc0.le (min_le_right _ _) 2
        _ = T - H.time i.castSucc := Real.sq_sqrt (by linarith)
    have hstart : H.regularizedStageStart T W.a i.castSucc = 0 := by
      rw [W.regularizedStageStart_castSucc_eq, hT, sub_self, Real.sqrt_zero]
    have hend : H.regularizedStageEnd T W.b i.castSucc = W.b := W.regularizedStageEnd_castSucc_eq
    have hsq : ∀ t ∈ Ioo (T - c ^ 2) T, 0 < Real.sqrt (T - t) ∧ Real.sqrt (T - t) < W.b ∧
        T - Real.sqrt (T - t) ^ 2 = t := by
      intro t ht
      have h1 : Real.sqrt (T - t) ^ 2 = T - t := Real.sq_sqrt (by linarith [ht.2])
      refine ⟨Real.sqrt_pos.2 (by linarith [ht.2]), ?_, by rw [h1]; ring⟩
      have h2 : Real.sqrt (T - t) < c := by
        rw [Real.sqrt_lt' hc0]
        linarith [ht.1]
      exact h2.trans_le (min_le_left _ _)
    have key : ∀ t ∈ Ioo (T - c ^ 2) T, (W.S.base.metric t).inner z u w =
        ((H.event i).incoming.flow.base.metric t).inner y.val a b := by
      intro t ht
      obtain ⟨h0, h1, h2⟩ := hsq t ht
      have hm := W.metric ⟨i.castSucc, le_rfl, i.castSucc_lt_succ.le⟩ (Real.sqrt (T - t))
        ⟨by rw [hstart]; exact h0, by rw [hend]; exact h1⟩
      rw [h2] at hm
      rw [hm, localPullMetric_inner]
      simp only [stageMetric, Fin.lastCases_castSucc]
      rw [hy]
    have hTc : T ∈ W.D.carrier := by
      have h := W.mem_carrier (s := 0) ⟨ha.le, hb.le⟩
      simpa using h
    have hsub : Ioo (T - c ^ 2) T ⊆ W.D.carrier := fun t ht => by
      obtain ⟨h0, h1, h2⟩ := hsq t ht
      have h := W.mem_carrier (s := Real.sqrt (T - t)) ⟨ha ▸ h0.le, h1.le⟩
      rwa [h2] at h
    have hL : ContinuousWithinAt (fun t => (W.S.base.metric t).inner z u w)
        (Ioo (T - c ^ 2) T) T :=
      (W.solution.smoothMetric.coeff_cont z u w T hTc).mono hsub
    set L := (H.event i).terminal
    set c' : ℝ := T - c ^ 2 with hc'def
    have hac : H.time i.castSucc ≤ c' := by linarith
    have hcs' : c' < H.time i.succ := by rw [hT]; linarith [pow_pos hc0 2]
    have hsol := L.closedSolution_isSolutionOn ⊤ hac hcs'
    have hR0 := hsol.smoothMetric.coeff_cont (⟨y, trivial⟩ : (⊤ : TopologicalSpace.Opens _))
      a b (H.time i.succ) ⟨hcs'.le, le_rfl⟩
    have hR : ContinuousWithinAt
        (fun t => ((L.extendedMetric t).restrictOpen ⊤).inner
          (⟨y, trivial⟩ : (⊤ : TopologicalSpace.Opens _)) a b) (Ioo (T - c ^ 2) T) T := by
      rw [← hT]
      refine hR0.mono fun t ht => ⟨?_, ht.2.le⟩
      change c' ≤ t
      linarith [ht.1, hc'def, hT]
    have hvalR : ((L.extendedMetric T).restrictOpen ⊤).inner
        (⟨y, trivial⟩ : (⊤ : TopologicalSpace.Opens _)) a b = L.metric.inner y a b := by
      rw [← hT, L.extendedMetric_terminal]
      rfl
    have hevR : ∀ t ∈ Ioo (T - c ^ 2) T, ((L.extendedMetric t).restrictOpen ⊤).inner
        (⟨y, trivial⟩ : (⊤ : TopologicalSpace.Opens _)) a b =
          ((H.event i).incoming.flow.base.metric t).inner y.val a b := by
      intro t ht
      rw [L.extendedMetric_before (ht.2.trans_eq hT.symm)]
      rfl
    have := right_nhdsWithin_Ioo_neBot (show T - c ^ 2 < T by linarith [pow_pos hc0 2])
    rw [← hvalR]
    exact tendsto_nhds_unique_of_eventuallyEq hL.tendsto hR.tendsto
      (eventually_nhdsWithin_of_forall fun t ht => (key t ht).trans (hevR t ht).symm)
  rw [hcont, ← hFmet y hyF a b, hadef, hbdef, hd u, hd w, hmetT, hFy]

variable (ha : W.a = 0) (hT : H.time i.succ = T) {x : W.X} {Zx : TangentSpace ThreeModel x}
  (hdom : W.b ∈ lRegularizedDomain W.S T x Zx)

omit hdom in
include hT in
private theorem sub_sq_mem_stageDomain_castSucc {v : ℝ} (hv : 0 < v) (hvb : v ≤ W.b) :
    T - v ^ 2 ∈ H.stageDomain i.castSucc := by
  have hlow := H.time_le_of_mem_stageDomain W.lower
  have h1 : v ^ 2 ≤ W.b ^ 2 := pow_le_pow_left₀ hv.le hvb 2
  simp only [stageDomain, Fin.lastCases_castSucc, mem_Ico]
  exact ⟨by linarith, by rw [hT]; linarith [pow_pos hv 2]⟩

omit hdom hT in
include ha in
private theorem mem_stageDomain_succ : T - (0 : ℝ) ^ 2 ∈ H.stageDomain i.succ := by
  have h := W.upper
  rwa [ha] at h

omit hdom in
include hT in
private theorem regularizedStageStart_zero_castSucc :
    H.regularizedStageStart T 0 i.castSucc = 0 := by
  simp only [regularizedStageStart, stageEndTime_castSucc, hT, sub_zero, pow_two, mul_zero,
    min_self, sub_self, Real.sqrt_zero]

omit hdom in
include hT in
private theorem regularizedStageEnd_castSucc {v : ℝ} (hv : 0 < v) (hvb : v ≤ W.b) :
    H.regularizedStageEnd T v i.castSucc = v :=
  H.regularizedStageEnd_eq_of_mem_stageDomain hv.le
    (sub_sq_mem_stageDomain_castSucc W hT hv hvb)

omit hdom in
include hT in
private theorem regularizedStageEnd_succ {v : ℝ} :
    H.regularizedStageEnd T v i.succ = 0 := by
  have : T - v ^ 2 ≤ H.time i.succ := by rw [hT]; nlinarith
  unfold regularizedStageEnd
  rw [max_eq_right this, hT, sub_self, Real.sqrt_zero]

omit hdom in
include ha in
private theorem regularizedStageStart_zero_succ :
    H.regularizedStageStart T 0 i.succ = 0 := by
  rw [H.regularizedStageStart_eq_of_mem_Icc le_rfl]
  have h := mem_stageDomain_succ W ha
  exact ⟨H.time_le_of_mem_stageDomain h, H.le_stageEndTime_of_mem_stageDomain h⟩

include ha hT hdom in
private theorem isHistoryLGeodesicOn_comp_lRegularizedCurve_seam {v : ℝ} (hv : 0 < v)
    (hvb : v < W.b) :
    H.IsHistoryLGeodesicOn i.castSucc_lt_succ.le T v
      (fun j => W.f j ∘ lRegularizedCurve W.S T x Zx) := by
  have hgeo := isLRegularizedGeodesicOn_lRegularizedCurve W.S W.solution T x Zx
  have hsub : Icc 0 W.b ⊆ lRegularizedDomain W.S T x Zx := fun s hs =>
    lRegularizedDomain_segment W.S T x Zx hdom hs.1 hs.2
  have hdown := sub_sq_mem_stageDomain_castSucc W hT hv hvb.le
  let W' := W.restrict (a' := 0) (b' := v) le_rfl le_rfl i.castSucc_lt_succ.le ha.le hv hvb.le
    (mem_stageDomain_succ W ha) hdown
  refine ⟨hdown, fun i' hf hl => W.crossing i' hf hl _, fun s hs =>
    ⟨i.castSucc, i.succ, le_rfl, le_rfl, W', hs, le_rfl, ?_⟩, ?_⟩
  · have hg1 : IsLRegularizedGeodesicOn W.S T (lRegularizedCurve W.S T x Zx) (Ioo 0 v) :=
      fun r hr => hgeo r (hsub ⟨hr.1.le, hr.2.le.trans hvb.le⟩)
    exact ⟨(lRegularizedCurve W.S T x Zx : ℝ → W.X), hg1, fun j r _ => rfl⟩
  have hd := (hgeo v (hsub ⟨hv.le, hvb.le⟩)).2.1
  exact ((W.localDiffeomorph _).contMDiff.continuous.continuousAt.comp
    hd.continuousAt).continuousWithinAt

include ha hdom in
private theorem hasHistoryLInitialVector_comp_lRegularizedCurve_seam
    {p : (H.stage i.succ).Carrier} (hx : W.f ⟨i.succ, i.castSucc_lt_succ.le, le_rfl⟩ x = p)
    {Z : TangentSpace ThreeModel p}
    (hZ : mfderiv ThreeModel ThreeModel (W.f ⟨i.succ, i.castSucc_lt_succ.le, le_rfl⟩) x Zx = Z) :
    H.HasHistoryLInitialVector (first := i.castSucc) T
      (fun j => W.f j ∘ lRegularizedCurve W.S T x Zx) p Z :=
  ⟨i.castSucc, le_rfl, W, x, Zx, ha, hx, hZ, hdom, fun _ _ _ => rfl⟩

include ha hT hdom in
private theorem mem_historyLExpDomain_of_seamWindow {p : (H.stage i.succ).Carrier}
    (hx : W.f ⟨i.succ, i.castSucc_lt_succ.le, le_rfl⟩ x = p) {Z : TangentSpace ThreeModel p}
    (hZ : mfderiv ThreeModel ThreeModel (W.f ⟨i.succ, i.castSucc_lt_succ.le, le_rfl⟩) x Zx = Z)
    {v : ℝ} (hv : 0 < v) (hvb : v < W.b) :
    Z ∈ H.historyLExpDomain i.castSucc_lt_succ.le T v p :=
  ⟨_, isHistoryLGeodesicOn_comp_lRegularizedCurve_seam W ha hT hdom hv hvb,
    hasHistoryLInitialVector_comp_lRegularizedCurve_seam W ha hdom hx hZ⟩

include ha hT hdom in
private theorem historyLCurve_eqOn_seamWindow {p : (H.stage i.succ).Carrier}
    (hx : W.f ⟨i.succ, i.castSucc_lt_succ.le, le_rfl⟩ x = p) {v : ℝ} (hv : 0 < v)
    (hvb : v < W.b) (Z : H.historyLExpDomain i.castSucc_lt_succ.le T v p)
    (hZ : mfderiv ThreeModel ThreeModel (W.f ⟨i.succ, i.castSucc_lt_succ.le, le_rfl⟩) x Zx = Z.1)
    (j : H.StageInterval i.castSucc i.succ) :
    EqOn (H.historyLCurve i.castSucc_lt_succ.le T v p Z j)
      (W.f j ∘ lRegularizedCurve W.S T x Zx)
      (Icc (H.regularizedStageStart T 0 j.val) (H.regularizedStageEnd T v j.val)) :=
  eqOn_historyLCurve hv Z (isHistoryLGeodesicOn_comp_lRegularizedCurve_seam W ha hT hdom hv hvb)
    (hasHistoryLInitialVector_comp_lRegularizedCurve_seam W ha hdom hx hZ) j

include ha hT hdom in
private theorem historyLAction_eq_seamWindow {p : (H.stage i.succ).Carrier}
    (hx : W.f ⟨i.succ, i.castSucc_lt_succ.le, le_rfl⟩ x = p) {v : ℝ} (hv : 0 < v)
    (hvb : v < W.b) (Z : H.historyLExpDomain i.castSucc_lt_succ.le T v p)
    (hZ : mfderiv ThreeModel ThreeModel (W.f ⟨i.succ, i.castSucc_lt_succ.le, le_rfl⟩) x Zx = Z.1) :
    H.historyLAction i.castSucc_lt_succ.le T v p Z =
      lRegularizedAction W.S T (lRegularizedCurve W.S T x Zx) 0 v := by
  have hgeo := isLRegularizedGeodesicOn_lRegularizedCurve W.S W.solution T x Zx
  set jo : H.StageInterval i.castSucc i.succ := ⟨i.castSucc, le_rfl, i.castSucc_lt_succ.le⟩
  have heq := historyLCurve_eqOn_seamWindow W ha hT hdom hx hv hvb Z hZ jo
  unfold historyLAction
  rw [Fintype.sum_eq_single jo ?_]
  · rw [regularizedStageStart_zero_castSucc hT, regularizedStageEnd_castSucc W hT hv hvb.le]
      at heq ⊢
    unfold stageRegularizedAction lRegularizedAction
    rw [intervalIntegral.integral_of_le hv.le, intervalIntegral.integral_of_le hv.le,
      MeasureTheory.integral_Ioc_eq_integral_Ioo, MeasureTheory.integral_Ioc_eq_integral_Ioo]
    refine MeasureTheory.setIntegral_congr_fun measurableSet_Ioo fun t ht => ?_
    have hev : H.historyLCurve i.castSucc_lt_succ.le T v p Z jo =ᶠ[𝓝 t]
        W.f jo ∘ lRegularizedCurve W.S T x Zx := by
      filter_upwards [isOpen_Ioo.mem_nhds ht] with r hr
      exact heq (Ioo_subset_Icc_self hr)
    have hvel : lVelocity (I := ThreeModel) (H.historyLCurve i.castSucc_lt_succ.le T v p Z jo) t =
        lVelocity (I := ThreeModel) (W.f jo ∘ lRegularizedCurve W.S T x Zx) t := by
      have hmf := Filter.EventuallyEq.mfderiv_eq (I := 𝓘(ℝ, ℝ)) (I' := ThreeModel) hev
      with_unfolding_all exact congrArg (fun L => L (1 : ℝ)) hmf
    have hval := hev.self_of_nhds
    have htb : t < W.b := ht.2.trans hvb
    have hstart : H.regularizedStageStart T W.a jo.val = 0 := by
      rw [ha]
      exact regularizedStageStart_zero_castSucc hT
    have hm := W.metric jo t ⟨by rw [hstart]; exact ht.1, by
      rw [W.regularizedStageEnd_castSucc_eq]; exact htb⟩
    have hdiff := (hgeo t (lRegularizedDomain_segment W.S T x Zx hdom ht.1.le htb.le)).2.1
    rw [← H.stageRegularizedLagrangian_comp_eq_of_localPullMetric jo.val W.S _
      (W.localDiffeomorph jo) T hdiff hm]
    unfold stageRegularizedLagrangian
    rw [hval, hvel]
  · intro j hj
    have hjs : j.val = i.succ := by
      obtain ⟨k, h1, h2⟩ := j
      rcases h1.lt_or_eq with h | h
      · exact le_antisymm h2 (Fin.castSucc_lt_iff_succ_le.1 h)
      · exact absurd (Subtype.ext h.symm) hj
    have h1 : H.regularizedStageStart T 0 j.val = 0 := by
      rw [hjs]
      exact regularizedStageStart_zero_succ W ha
    have h2 : H.regularizedStageEnd T v j.val = 0 := by
      rw [hjs]
      exact regularizedStageEnd_succ (v := v) hT
    unfold stageRegularizedAction
    rw [h1, h2]
    exact intervalIntegral.integral_same

include ha hT hdom in
private theorem historyLJacobianDensity_div_eq_seam {p : (H.stage i.succ).Carrier}
    (hx : W.f ⟨i.succ, i.castSucc_lt_succ.le, le_rfl⟩ x = p) {v : ℝ} (hv : 0 < v) (hvb : v < W.b)
    (Z₀ : H.historyLExpDomain i.castSucc_lt_succ.le T v p)
    (hZ : mfderiv ThreeModel ThreeModel (W.f ⟨i.succ, i.castSucc_lt_succ.le, le_rfl⟩) x Zx = Z₀.1) :
    H.historyLJacobianDensity i.castSucc_lt_succ.le T v p Z₀
      ⟨i.castSucc, le_rfl, i.castSucc_lt_succ.le⟩ v /
      H.historyLSourceDensity T p =
      paramDensity (W.S.base.metric (T - v ^ 2))
        (fun Z : ThreeSpace => lRegularizedCurve W.S T x Z v) Zx /
      Real.sqrt (Matrix.of fun m n : Fin (Module.finrank ℝ ThreeSpace) =>
        (W.S.base.metric T).inner x (chartModelBasis ThreeSpace m)
          (chartModelBasis ThreeSpace n)).det := by
  set jo : H.StageInterval i.castSucc i.succ := ⟨i.castSucc, le_rfl, i.castSucc_lt_succ.le⟩
    with hjo
  set jn : H.StageInterval i.castSucc i.succ := ⟨i.succ, i.castSucc_lt_succ.le, le_rfl⟩
    with hjn
  obtain ⟨V, hV, hZxV, hVdom, hMD⟩ := exists_nhds_lRegularizedDomain_of_window W hdom
  have hvjo : v ∈ Icc (H.regularizedStageStart T 0 jo.val) (H.regularizedStageEnd T v jo.val) := by
    change v ∈ Icc (H.regularizedStageStart T 0 i.castSucc) (H.regularizedStageEnd T v i.castSucc)
    rw [regularizedStageStart_zero_castSucc hT, regularizedStageEnd_castSucc W hT hv hvb.le]
    exact ⟨hv.le, le_rfl⟩
  let e :=
    (W.localDiffeomorph jn).mfderivToContinuousLinearEquiv (by simp) x
  let L : ThreeSpace →L[ℝ] ThreeSpace :=
    (e.symm : TangentSpace ThreeModel (W.f jn x) →L[ℝ]
      TangentSpace ThreeModel x)
  let A : ThreeSpace →L[ℝ] ThreeSpace :=
    (e : TangentSpace ThreeModel x →L[ℝ]
      TangentSpace ThreeModel (W.f jn x))
  have hLe : ∀ Z : ThreeSpace,
      mfderiv ThreeModel ThreeModel (W.f jn) x (L Z) = Z :=
    fun Z => e.apply_symm_apply Z
  have hLZ : L Z₀.1 = Zx := by
    have h : e Zx = Z₀.1 := hZ
    rw [← h]
    exact e.symm_apply_apply Zx
  have hLA : LinearMap.det (L : ThreeSpace →ₗ[ℝ] ThreeSpace) *
      LinearMap.det (A : ThreeSpace →ₗ[ℝ] ThreeSpace) = 1 := by
    rw [← LinearMap.det_comp]
    have hid :
        (L : ThreeSpace →ₗ[ℝ] ThreeSpace).comp (A : ThreeSpace →ₗ[ℝ] ThreeSpace) =
        LinearMap.id := LinearMap.ext fun Z => e.symm_apply_apply Z
    rw [hid, LinearMap.det_id]
  let Φ : ThreeSpace → W.X := fun Z => lRegularizedCurve W.S T x Z v
  let z : ThreeSpace := Zx
  have hΦ : MDifferentiableAt 𝓘(ℝ, ThreeSpace) ThreeModel Φ z := hMD v ⟨hv.le, hvb.le⟩
  have hfd : MDifferentiableAt ThreeModel ThreeModel (W.f jo) (Φ z) :=
    (W.localDiffeomorph _ _).mdifferentiableAt (by simp)
  have hev : ((W.f jo ∘ Φ) ∘ L) =ᶠ[𝓝 Z₀.1]
      H.historyLCurveMap i.castSucc_lt_succ.le T v p Z₀ jo v := by
    have hmem : L ⁻¹' V ∈ 𝓝 Z₀.1 :=
      L.continuous.continuousAt.preimage_mem_nhds (by rw [hLZ]; exact hV.mem_nhds hZxV)
    filter_upwards [hmem] with Z hZV
    have hdomZ := hVdom (L Z) hZV
    have hmemZ := mem_historyLExpDomain_of_seamWindow W ha hT hdomZ hx (hLe Z) hv hvb
    rw [historyLCurveMap_of_mem _ _ hmemZ]
    exact (historyLCurve_eqOn_seamWindow W ha hT hdomZ hx hv hvb ⟨Z, hmemZ⟩ (hLe Z) jo
      hvjo).symm
  have h1 :=
    paramDensity_eq_historyLJacobianDensity_of_eventuallyEq jo v hev
  have hstart : H.regularizedStageStart T W.a jo.val = 0 := by
    rw [ha]
    exact regularizedStageStart_zero_castSucc hT
  have hm := W.metric jo v ⟨by rw [hstart]; exact hv, by
    rw [W.regularizedStageEnd_castSucc_eq]; exact hvb⟩
  have h3 := DifferentialGeometry.Integral.Measure.paramDensity_comp_of_inner_eq
    (W.S.base.metric (T - v ^ 2)) (H.stageMetric i.castSucc (T - v ^ 2)) hfd hΦ
    (fun u u' => by rw [hm, localPullMetric_inner])
  have h2 := DifferentialGeometry.Integral.Measure.paramDensity_comp
    (H.stageMetric i.castSucc (T - v ^ 2)) (Φ := W.f jo ∘ Φ) (ψ := L)
    (x := Z₀.1)
    (by rw [hLZ]; exact hfd.comp z hΦ) L.differentiableAt
  have hLf : fderiv ℝ (⇑L) Z₀.1 = L := L.fderiv
  rw [hLf, hLZ, h3] at h2
  have hsrc : Real.sqrt (Matrix.of fun m n : Fin (Module.finrank ℝ ThreeSpace) =>
      (W.S.base.metric T).inner x (chartModelBasis ThreeSpace m)
        (chartModelBasis ThreeSpace n)).det =
      |LinearMap.det (A : ThreeSpace →ₗ[ℝ] ThreeSpace)| * H.historyLSourceDensity T p := by
    have hmat : (Matrix.of fun m n : Fin (Module.finrank ℝ ThreeSpace) =>
        (W.S.base.metric T).inner x (chartModelBasis ThreeSpace m)
          (chartModelBasis ThreeSpace n)) =
        Matrix.of fun m n : Fin (Module.finrank ℝ ThreeSpace) =>
        (H.stageMetric i.succ T).inner (W.f jn x)
          (A (chartModelBasis ThreeSpace m)) (A (chartModelBasis ThreeSpace n)) := by
      ext m n
      simp only [Matrix.of_apply]
      rw [metric_eq_localPullMetric_of_seamBase W ha hT]
      exact localPullMetric_inner (H.stageMetric i.succ T) _ _ x _ _
    rw [hmat]
    subst hx
    exact sqrt_det_inner_comp (H.stageMetric i.succ T) (W.f jn x) A
  have hA : LinearMap.det (A : ThreeSpace →ₗ[ℝ] ThreeSpace) ≠ 0 := fun h => by
    rw [h, mul_zero] at hLA
    exact zero_ne_one hLA
  rw [← h1]
  erw [h2]
  rw [hsrc, mul_comm |LinearMap.det (A : ThreeSpace →ₗ[ℝ] ThreeSpace)|,
    ← mul_div_mul_right _ _ (abs_ne_zero.2 hA)]
  change |LinearMap.det (L : ThreeSpace →ₗ[ℝ] ThreeSpace)| * _ *
    |LinearMap.det (A : ThreeSpace →ₗ[ℝ] ThreeSpace)| / _ = _
  rw [mul_right_comm, ← abs_mul, hLA, abs_one, one_mul]

variable {B : ℝ} (hfloor : ∀ j, ∀ t ∈ H.stageDomain j, ∀ y : (H.stage j).Carrier,
  -B ≤ metricScalarAt (H.stageMetric j t) y)

include ha hT hdom hfloor in
private theorem lRegularizedAction_le_of_mem_historyMinDomain_seam
    {p : (H.stage i.succ).Carrier}
    (hx : W.f ⟨i.succ, i.castSucc_lt_succ.le, le_rfl⟩ x = p) {Z : TangentSpace ThreeModel p}
    (hZ : mfderiv ThreeModel ThreeModel (W.f ⟨i.succ, i.castSucc_lt_succ.le, le_rfl⟩) x Zx = Z)
    {c : ℝ}
    (hc : 0 < c) (hcb : c < W.b)
    (hmin : Z ∈ H.historyMinDomain i.castSucc_lt_succ.le T B c p) (δ : ℝ → W.X)
    (hδ : ContMDiff 𝓘(ℝ, ℝ) ThreeModel 1 δ) (hδ0 : δ 0 = x)
    (hδc : δ c = lRegularizedCurve W.S T x Zx c) :
    lRegularizedAction W.S T (lRegularizedCurve W.S T x Zx) 0 c ≤
      lRegularizedAction W.S T δ 0 c := by
  obtain ⟨α, hgeo, hinit, hac, hp, hmin', hfin⟩ := hmin
  have huniq := IsHistoryLGeodesicOn.eqOn_of_hasHistoryLInitialVector hc hgeo
    (isHistoryLGeodesicOn_comp_lRegularizedCurve_seam W ha hT hdom hc hcb) hinit
    (hasHistoryLInitialVector_comp_lRegularizedCurve_seam W ha hdom hx hZ)
  have hup0 := mem_stageDomain_succ W ha
  have hupIcc : T - (0 : ℝ) ^ 2 ∈ Icc (H.time i.succ) (H.stageEndTime i.succ) :=
    ⟨H.time_le_of_mem_stageDomain hup0, H.le_stageEndTime_of_mem_stageDomain hup0⟩
  have hdown := sub_sq_mem_stageDomain_castSucc W hT hc hcb.le
  obtain ⟨K, -, -, hKsub, hsm⟩ := exists_contMDiffOn_lRegularizedCurve_of_window W hdom
  have hγac : Manifold.absolutelyContinuousOnInterval ThreeModel
      (lRegularizedCurve W.S T x Zx) 0 c :=
    Manifold.absolutelyContinuousOnInterval_of_contMDiffOn ((hsm.mono (by
      rw [uIcc_of_le hc.le]
      exact (Icc_subset_Icc le_rfl hcb.le).trans hKsub)).of_le (by norm_num))
  rw [← hp] at hmin'
  let W' := W.restrict (a' := 0) (b' := c) le_rfl le_rfl i.castSucc_lt_succ.le ha.le hc hcb.le
    hup0 hdown
  exact W'.lRegularizedAction_le_of_regularizedCost_eq i.castSucc_lt_succ.le le_rfl le_rfl
    (u := 0) (v := c) le_rfl le_rfl le_rfl hupIcc hdown hfloor α hac
    (fun i' hf hl => let ⟨z, _, h1, h2⟩ := hgeo.2.1 i' hf hl; ⟨z, h1, h2⟩)
    hmin' hfin (lRegularizedCurve W.S T x Zx : ℝ → W.X) hγac
    (fun j => (huniq ⟨j.val, j.2.1, j.2.2⟩).symm) δ hδ
    (hδ0.trans (lRegularizedCurve_zero W.S T x Zx).symm) hδc

include ha hT hdom hfloor in
private theorem mem_lMinDomain_of_mem_historyMinDomain_seam
    {p : (H.stage i.succ).Carrier}
    (hx : W.f ⟨i.succ, i.castSucc_lt_succ.le, le_rfl⟩ x = p) {Z : TangentSpace ThreeModel p}
    (hZ : mfderiv ThreeModel ThreeModel (W.f ⟨i.succ, i.castSucc_lt_succ.le, le_rfl⟩) x Zx = Z)
    {c : ℝ} (hc : 0 < c) (hcb : c < W.b)
    (hmin : Z ∈ H.historyMinDomain i.castSucc_lt_succ.le T B c p) :
    (Zx, c ^ 2) ∈ lMinDomain W.S T x ∧
      BddBelow {r : ℝ | ∃ α : ℝ → W.X, ContMDiff 𝓘(ℝ, ℝ) ThreeModel 1 α ∧
        α 0 = x ∧
        α (Real.sqrt (c ^ 2)) = lExp W.S T x Zx (c ^ 2) ∧
        lRegularizedAction W.S T α 0 (Real.sqrt (c ^ 2)) = r} := by
  have hsq : Real.sqrt (c ^ 2) = c := Real.sqrt_sq hc.le
  have hlow := lRegularizedAction_le_of_mem_historyMinDomain_seam W ha hT hdom hfloor hx hZ hc hcb
    hmin
  obtain ⟨K, hK, hKc, hKsub, hsm⟩ := exists_contMDiffOn_lRegularizedCurve_of_window W hdom
  obtain ⟨αe, hαe, heqe⟩ := exists_contMDiff_eqOn_Icc hK hKc hc hcb hKsub hsm
  have hαe1 : ContMDiff 𝓘(ℝ, ℝ) ThreeModel 1 αe := hαe.of_le (by norm_num)
  have hαe0 : αe 0 = x := (heqe ⟨le_rfl, hc.le⟩).trans (lRegularizedCurve_zero W.S T x Zx)
  have hαec : αe c = lRegularizedCurve W.S T x Zx c := heqe ⟨hc.le, le_rfl⟩
  have hαeA : lRegularizedAction W.S T αe 0 c =
      lRegularizedAction W.S T (lRegularizedCurve W.S T x Zx) 0 c :=
    lRegularizedAction_congr W.S T _ _ 0 c fun t ht => heqe (by
      rw [uIoo_of_le hc.le] at ht
      exact Ioo_subset_Icc_self ht)
  have hExp : lExp W.S T x Zx (c ^ 2) = lRegularizedCurve W.S T x Zx c := by
    change lRegularizedCurve W.S T x Zx (Real.sqrt (c ^ 2)) = _
    rw [hsq]
  have hLen : ∀ α : ℝ → W.X, lLength W.S T (squareRootReparametrization α) 0 (c ^ 2) =
      lRegularizedAction W.S T α 0 c := fun α => by
    rw [lLength_squareRootReparametrization_eq_lRegularizedAction W.S T α (c ^ 2) (sq_nonneg c),
      hsq]
  refine ⟨⟨⟨pow_pos hc 2, ?_⟩, ?_⟩,
    ⟨lRegularizedAction W.S T (lRegularizedCurve W.S T x Zx) 0 c, ?_⟩⟩
  · change Real.sqrt (c ^ 2) ∈ lRegularizedDomain W.S T x Zx
    rw [hsq]
    exact lRegularizedDomain_segment W.S T x Zx hdom hc.le hcb.le
  · change lLength W.S T (squareRootReparametrization (lRegularizedCurve W.S T x Zx)) 0 (c ^ 2) =
      lCost W.S T x (lExp W.S T x Zx (c ^ 2)) (c ^ 2)
    rw [hLen, lCost]
    refine le_antisymm (le_csInf ⟨_, αe, hαe1, hαe0, by rw [hsq, hExp, hαec], rfl⟩ ?_)
      (csInf_le ⟨lRegularizedAction W.S T (lRegularizedCurve W.S T x Zx) 0 c, ?_⟩
        ⟨αe, hαe1, hαe0, by rw [hsq, hExp, hαec], by rw [hLen, hαeA]⟩)
    · rintro r ⟨α, hα, h0, h1, rfl⟩
      rw [hLen]
      rw [hsq, hExp] at h1
      exact hlow α hα h0 h1
    · rintro r ⟨α, hα, h0, h1, rfl⟩
      rw [hLen]
      rw [hsq, hExp] at h1
      exact hlow α hα h0 h1
  · rintro r ⟨α, hα, h0, h1, rfl⟩
    rw [hsq] at h1 ⊢
    rw [hExp] at h1
    exact hlow α hα h0 h1

include ha hT hdom in
private theorem historyReducedJacobian_eq_of_seamWindow
    {p : (H.stage i.succ).Carrier} (hx : W.f ⟨i.succ, i.castSucc_lt_succ.le, le_rfl⟩ x = p)
    {Z : TangentSpace ThreeModel p}
    (hZ : mfderiv ThreeModel ThreeModel (W.f ⟨i.succ, i.castSucc_lt_succ.le, le_rfl⟩) x Zx = Z)
    {v : ℝ}
    (hv : 0 < v) (hvb : v < W.b)
    (hZv : Z ∈ H.historyLExpDomain i.castSucc_lt_succ.le T v p) :
    H.historyReducedJacobian i.castSucc_lt_succ.le T v p ⟨Z, hZv⟩ =
      paramDensity (W.S.base.metric (T - v ^ 2))
          (fun Z : ThreeSpace => lRegularizedCurve W.S T x Z v) Zx /
        Real.sqrt (Matrix.of fun m n : Fin (Module.finrank ℝ ThreeSpace) =>
          (W.S.base.metric T).inner x (chartModelBasis ThreeSpace m)
            (chartModelBasis ThreeSpace n)).det *
      Real.exp (-lRegularizedAction W.S T (lRegularizedCurve W.S T x Zx) 0 v / (2 * v) -
        (3 / 2 : ℝ) * Real.log (v ^ 2) - (3 / 2 : ℝ) * Real.log (4 * Real.pi)) := by
  rw [historyReducedJacobian,
    historyLJacobianDensity_div_eq_seam W ha hT hdom hx hv hvb ⟨Z, hZv⟩ hZ,
    historyLAction_eq_seamWindow W ha hT hdom hx hv hvb ⟨Z, hZv⟩ hZ]

end SeamBaseWindow

section SeamBaseLimit

variable {H : ObservedHistory.{u}} {last : Fin (H.eventCount + 1)} {T : ℝ}
  {p : (H.stage last).Carrier}

theorem exists_pos_historyReducedJacobian_le_gaussian_of_time_eq (hT : H.time last = T)
    {B v₂ : ℝ}
    (hfloor : ∀ j, ∀ t ∈ H.stageDomain j, ∀ y : (H.stage j).Carrier,
      -B ≤ metricScalarAt (H.stageMetric j t) y)
    (hv₂ : 0 < v₂) {first : Fin (H.eventCount + 1)} {hle : first ≤ last}
    {Z₀ : TangentSpace ThreeModel p} (hZ₀ : Z₀ ∈ H.historyMinDomain hle T B v₂ p) :
    ∃ (k : Fin (H.eventCount + 1)) (hkl : k ≤ last) (δ : ℝ), 0 < δ ∧ δ ≤ v₂ ∧
      ∀ v ∈ Ioo 0 δ, T - v ^ 2 ∈ H.stageDomain k ∧
        ∀ hZ : Z₀ ∈ H.historyLExpDomain hkl T v p,
          H.historyReducedJacobian hkl T v p ⟨Z₀, hZ⟩ ≤
            (Real.pi ^ ((3 : ℝ) / 2))⁻¹ *
              Real.exp (-(H.stageMetric last T).inner p Z₀ Z₀) := by
  have hZd := historyMinDomain_subset_historyLExpDomain hZ₀
  obtain ⟨lo, -, W₀, x, Zx, ha, hx, hZ, hdom, -⟩ :=
    hasHistoryLInitialVector_historyLCurve (⟨Z₀, hZd⟩ : H.historyLExpDomain hle T v₂ p)
  have hb₀ : 0 < W₀.b := ha ▸ W₀.lt
  have hlolast : lo < last := by
    have h := H.time_le_of_mem_stageDomain W₀.lower
    refine H.time_strictMono.lt_iff_lt.1 ?_
    rw [hT]
    linarith [pow_pos hb₀ 2]
  obtain ⟨i, rfl⟩ : ∃ i : Fin H.eventCount, i.succ = last :=
    Fin.exists_succ_eq.2 (ne_of_gt ((Fin.zero_le lo).trans_lt hlolast))
  have hloc : lo ≤ i.castSucc := Fin.le_castSucc_iff.2 hlolast
  have hcs : H.time i.castSucc < T := hT ▸ H.time_strictMono i.castSucc_lt_succ
  have hm0 : 0 < min W₀.b (min v₂ (Real.sqrt (T - H.time i.castSucc))) :=
    lt_min hb₀ (lt_min hv₂ (Real.sqrt_pos.2 (by linarith)))
  set b := min W₀.b (min v₂ (Real.sqrt (T - H.time i.castSucc))) / 2 with hbdef
  have hb : 0 < b := half_pos hm0
  have hbm : b < min W₀.b (min v₂ (Real.sqrt (T - H.time i.castSucc))) := half_lt_self hm0
  have hbb₀ : b ≤ W₀.b := (hbm.trans_le (min_le_left _ _)).le
  have hbv₂ : b ≤ v₂ := (hbm.trans_le ((min_le_right _ _).trans (min_le_left _ _))).le
  have hbcs : b ^ 2 < T - H.time i.castSucc :=
    (Real.lt_sqrt hb.le).1 (hbm.trans_le ((min_le_right _ _).trans (min_le_right _ _)))
  have hdown : T - b ^ 2 ∈ H.stageDomain i.castSucc := by
    simp only [stageDomain, Fin.lastCases_castSucc, mem_Ico]
    exact ⟨by linarith, by rw [hT]; linarith [pow_pos hb 2]⟩
  have hup : T - (0 : ℝ) ^ 2 ∈ H.stageDomain i.succ := by
    have h := W₀.upper
    rwa [ha] at h
  let W := W₀.restrict (a' := 0) (b' := b) hloc le_rfl i.castSucc_lt_succ.le ha.le hb hbb₀ hup
    hdown
  have hWa : W.a = 0 := rfl
  have hWdom : W.b ∈ lRegularizedDomain W.S T x Zx :=
    lRegularizedDomain_segment W₀.S T x Zx hdom hb.le hbb₀
  have hWx : W.f ⟨i.succ, i.castSucc_lt_succ.le, le_rfl⟩ x = p := hx
  have hWZ : mfderiv ThreeModel ThreeModel (W.f ⟨i.succ, i.castSucc_lt_succ.le, le_rfl⟩) x Zx =
      Z₀ := hZ
  set c := b / 2 with hcdef
  have hc : 0 < c := half_pos hb
  have hcb : c < W.b := half_lt_self hb
  have hcv₂ : c ≤ v₂ := (half_lt_self hb).le.trans hbv₂
  have hminc : Z₀ ∈ H.historyMinDomain i.castSucc_lt_succ.le T B c p :=
    mem_historyMinDomain_of_le hfloor i.castSucc_lt_succ.le hc hcv₂
      (sub_sq_mem_stageDomain_castSucc W hT hc hcb.le) hZ₀
  obtain ⟨hmin, hbdd⟩ := mem_lMinDomain_of_mem_historyMinDomain_seam W hWa hT hWdom hfloor hWx
    hWZ hc hcb hminc
  refine ⟨i.castSucc, i.castSucc_lt_succ.le, c, hc, hcv₂, fun v hv =>
    ⟨sub_sq_mem_stageDomain_castSucc W hT hv.1 (hv.2.trans hcb).le, fun hZv => ?_⟩⟩
  have hvb : v < W.b := hv.2.trans hcb
  have hvc2 : v ^ 2 < c ^ 2 := pow_lt_pow_left₀ hv.2 hv.1.le two_ne_zero
  rw [historyReducedJacobian_eq_of_seamWindow W hWa hT hWdom hWx hWZ hv.1 hvb hZv]
  let _ : TopologicalSpace.MetrizableSpace W.X := Manifold.metrizableSpace ThreeModel W.X
  let _ : MetricSpace W.X := TopologicalSpace.metrizableSpaceMetric W.X
  have hv2 : 0 < v ^ 2 := pow_pos hv.1 2
  have hsq : Real.sqrt (v ^ 2) = v := Real.sqrt_sq hv.1.le
  have hle := lReducedJacobian_le_gaussian_of_bdd W.S W.solution T x hmin hv2 hvc2 hbdd
  have hdomv : (Zx, v ^ 2) ∈ lExpPosDom W.S T x := ⟨hv2, by
    change Real.sqrt (v ^ 2) ∈ lRegularizedDomain W.S T x Zx
    rw [hsq]
    exact lRegularizedDomain_segment W.S T x Zx hWdom hv.1.le hvb.le⟩
  have hnc := lMinVec_nconj_lt_of_bdd W.S W.solution T x hmin hvc2 hbdd
  have hmv := lMinDomain_down_of_bdd W.S W.solution T x Zx hmin hv2 hvc2.le
    (lRegularizedCosts_prefix_bdd_of_min W.S W.solution T x Zx hmin hv2 hvc2.le hbdd) hbdd
  have hA : lCost W.S T x (lExp W.S T x Zx (v ^ 2)) (v ^ 2) =
      lRegularizedAction W.S T (lRegularizedCurve W.S T x Zx) 0 v := by
    rw [← ((mem_lMinDomain W.S T x Zx (v ^ 2)).1 hmv).2]
    change lLength W.S T (squareRootReparametrization (lRegularizedCurve W.S T x Zx)) 0 (v ^ 2) = _
    rw [lLength_squareRootReparametrization_eq_lRegularizedAction W.S T _ (v ^ 2) hv2.le, hsq]
  have hsrc : 0 < lSourceDensity W.S T x := lSourceDensity_pos W.S T x
  have hfun : (fun Z : ThreeSpace => lExp W.S T x Z (v ^ 2)) =
      fun Z : ThreeSpace => lRegularizedCurve W.S T x Z v :=
    funext fun Z => by
      change lRegularizedCurve W.S T x Z (Real.sqrt (v ^ 2)) = _
      rw [hsq]
  have hPE : lExpDensity W.S T x Zx (v ^ 2) = paramDensity (W.S.base.metric (T - v ^ 2))
      (fun Z : ThreeSpace => lExp W.S T x Z (v ^ 2)) Zx := rfl
  rw [hfun] at hPE
  have hRJ := lRedJac_mul_src_of_nonconj W.S T x Zx (v ^ 2) hdomv hnc
  rw [← eq_div_iff hsrc.ne'] at hRJ
  unfold redDensity redLength at hRJ
  rw [hA, hsq, hPE, finrank_euclideanSpace_fin] at hRJ
  have hgauss : (W.S.base.metric T).inner x Zx Zx =
      (H.stageMetric i.succ T).inner p Z₀ Z₀ := by
    rw [metric_eq_localPullMetric_of_seamBase W hWa hT]
    refine (localPullMetric_inner (H.stageMetric i.succ T) _ _ x Zx Zx).trans ?_
    subst hWx
    exact congrArg (fun V => (H.stageMetric i.succ T).inner _ V V) hWZ
  have h3 : ((3 : ℕ) : ℝ) / 2 = 3 / 2 := by norm_num
  rw [hRJ, finrank_euclideanSpace_fin, hgauss, h3, ← neg_div] at hle
  change _ / lSourceDensity W.S T x * _ ≤ _
  rwa [div_mul_eq_mul_div]

end SeamBaseLimit
end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory
