import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.Kappa.KappaEventInductionC11Q4
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.LGeometry.Action.EventWindowEndpointPair
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.LGeometry.Action.C1Attainment

/-!
# EventLowSublevelContact 的生产（O-CH11-KAPPA3 G2，后缀 `_C11Q4`；R-C11-4 D-3）

`EventLowSublevelContact_C11Q4`（G1 的显式 binder）由 **node 数据**（`EventNodeData_C11Q4`）+ 种子
trace 的 Rm 控制给出，无新几何缺口。证明 = donor `closed_event_weighted_restart_of_query_support`
（History/PreparedSpatialClosedEventRestart:64，construction-specific，private）的接触段对一般 history
的重写：
* 低次水平集点 `q`（`regularizedCost q = L ≤ (E_A − 1) r`）⇒ C¹ minimizer `γ`
  （`regularizedCost_eq_regularizedC1Cost` + `exists_regularizedC1Cost_minimizer_of_ne_top`），作用量 `L`；
* `hEndpoint`（低作用量 C¹ 曲线终点 ∉ cap core）⇐ EventLocal:567 的 `hWindow`（request = node 数据）；
* `O, z` 与 `hO / hz` ⇐ `exists_old_seed_and_endpoint_outside_retained_cap_windows`
  （Action/EventWindowEndpointPair:22，private，`open private`）；它要 `seedTrace.isRmControlled r`；
* `seedTrace.isRmControlled r` ⇐ `hasSmallParabolicCurvature`（`√3 r` 控制的 trace）+
  `BackwardPointTrace` 的 Subsingleton（`point_unique`）。
-/

set_option autoImplicit false

noncomputable section

open Set Filter DifferentialGeometry MeasureTheory
open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Collapse
open DifferentialGeometry.PDE.RicciFlow DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
open scoped Manifold ContDiff ENNReal NNReal Topology
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory renaming
  exists_distinct_pole_half_clock_support_with_event_local_cap_exclusion_requests_at_closed_poles
    → closedPoleSupport_C11Q4

namespace GC.LongTime.Ch11

universe u

/-- `C(A) ≥ 0` ⇒ `E_A ≥ 2`（`e^x ≥ 1 + x`，`32/√2 ≥ 16`）。 -/
theorem two_le_eventLevelE_C11Q4 {A : ℝ} (hA : 0 ≤ A) : 2 ≤ eventLevelE_C11Q4 A := by
  have hC := cutoffBarrierConst_nonneg_C11Q4 hA
  have hsqrt : 0 < Real.sqrt 2 := by positivity
  have hsqrt2 : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have hrootle : Real.sqrt 2 ≤ 2 := by nlinarith only [hsqrt2, hsqrt.le]
  have hlin : 2 ≤ 32 / Real.sqrt 2 := (le_div_iff₀ hsqrt).mpr (by linarith only [hrootle])
  have he := Real.add_one_le_exp (cutoffBarrierConst_C11Q3 A / 2 + 32 / Real.sqrt 2)
  unfold eventLevelE_C11Q4
  linarith

/-- `0 ≤ k`、`k² ≤ r²/2`（`0 < r`）⇒ `k ≤ r/√2`。 -/
theorem le_div_sqrt_two_of_sq_le_C11Q4 {k r : ℝ} (hk : 0 ≤ k) (hr : 0 < r)
    (hhalf : k ^ 2 ≤ r ^ 2 / 2) : k ≤ r / Real.sqrt 2 := by
  have hsqrt : 0 < Real.sqrt 2 := by positivity
  have hb2 : (r / Real.sqrt 2) ^ 2 = r ^ 2 / 2 := by
    rw [div_pow, Real.sq_sqrt (by norm_num)]
  exact (sq_le_sq₀ hk (div_pos hr hsqrt).le).mp (by rw [hb2]; exact hhalf)

/-- **种子 trace 的 Rm 控制**：`hasSmallParabolicCurvature H t p r` 给的 trace 是 `√3 r` 控制的，而
`BackwardPointTrace` 是 Subsingleton ⇒ 任一 seed trace 都 `r` 控制。 -/
theorem seedTrace_isRmControlled_C11Q4 {H : ObservedHistory.{u}} {t : Icc (0 : ℝ) H.horizon}
    {p : (H.stageAt t).Carrier} {r : ℝ} (hsmall : hasSmallParabolicCurvature H t p r)
    {aSeed : Icc (0 : ℝ) H.horizon} (hSeedTime : aSeed ≤ t)
    (hSeedClock : (aSeed : ℝ) = t.val - r ^ 2)
    (seedTrace : BackwardPointTrace H (H.activeStage aSeed) (H.activeStage t)
      (H.activeStage_mono hSeedTime) p) :
    seedTrace.isRmControlled (hat := hSeedTime) r := by
  obtain ⟨hr, a, hat, ha, htr⟩ := hsmall
  have hpmem : p ∈ riemannianBallOf (H.stageMetric (H.activeStage t) t) p r := by
    change riemannianEDistOf _ p p < ENNReal.ofReal r
    rw [riemannianEDistOf_self]
    exact ENNReal.ofReal_pos.mpr hr
  obtain ⟨T, hT⟩ := htr p hpmem
  have haeq : a = aSeed := Subtype.ext (ha.trans hSeedClock.symm)
  subst haeq
  have hsqrt : 1 ≤ Real.sqrt 3 := by
    nlinarith [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 3), Real.sqrt_nonneg (3 : ℝ)]
  have hrr : r ≤ Real.sqrt 3 * r := le_mul_of_one_le_left hr.le hsqrt
  have h1 := BackwardPointTrace.isRmControlled.restrictFirst T hT hr.le hrr le_rfl hSeedTime
  have heq : T.restrictFirst (H.activeStage_mono (le_refl a)) (H.activeStage_mono hSeedTime) =
      seedTrace := Subsingleton.elim _ _
  rw [heq] at h1
  exact h1

end GC.LongTime.Ch11

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory

open GC.LongTime.Ch11

universe u

open private exists_old_seed_and_endpoint_outside_retained_cap_windows from
  DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.LGeometry.Action.EventWindowEndpointPair

/-- **EventLowSublevelContact ⇐ node 数据（逐种子，G2）**：`1 ≤ A`、种子球 `p` 受控、seed trace `r`
控制、窗口 event 的 `EventNodeData_C11Q4` ⇒ `EventLowSublevelContact_C11Q4`。caps = node 数据的 uniform
family；`hz` 经 C¹ minimizer + `hWindow`，`hO` 经 seed trace 的作用量 `≤ 6k³/r² ≤ 3r ≤ nodeA`。 -/
theorem eventLowSublevelContact_of_nodeData_C11Q4 {P : OrientedThreeStage.{u}} {g : P.Metric}
    (Cderiv : ℝ≥0) (H : ObservedHistory.{u}) (identification : InitialIdentification P g H)
    (parameters : CutoffParameters) (records : ∀ j, GeometricCutoffRecord H j parameters)
    (t : Icc (0 : ℝ) H.horizon) (p x : (H.stageAt t).Carrier) {r A : ℝ}
    (hA : 1 ≤ A) (hseed : H.isParabolicallyRmControlledBall t p r)
    (aSeed : Icc (0 : ℝ) H.horizon) (hSeedTime : aSeed ≤ t)
    (hSeedClock : (aSeed : ℝ) = t.val - r ^ 2)
    (seedTrace : BackwardPointTrace H (H.activeStage aSeed) (H.activeStage t)
      (H.activeStage_mono hSeedTime) p)
    (htrace : seedTrace.isRmControlled (hat := hSeedTime) r)
    {nodeA nodeE nodeR nodeQ nodeRho : Fin H.eventCount → ℝ}
    (hnode : EventNodeData_C11Q4 P g Cderiv H parameters records t x r A
      nodeA nodeE nodeR nodeQ nodeRho) :
    EventLowSublevelContact_C11Q4 H parameters (windowBarrierA₀_C11Q2 P g) t p x r A
      aSeed hSeedTime seedTrace := by
  intro i hl k hk hk2 hevent _hfPost q L _hmin hcost hL
  have hr : 0 < r := hseed.1
  have hspec := windowBarrierA₀_spec_C11Q2 P g
  have ha₀ := hspec.1
  obtain ⟨hfixed, hscalar⟩ := hspec.2.1 H identification
  have hwin : t.val - r ^ 2 / 2 ≤ H.time i.succ := by linarith
  have hN := hnode i hl hwin
  obtain ⟨hE, hR, hQ, hRho, hEge, hRle, hball, hdelta, hneck, hlater, hderiv, hcaps, hfit⟩ := hN
  obtain ⟨Dcap, εcap, ncap, S, hD, hn, hε, hcan, hscale⟩ := hcaps
  have hex := closedPoleSupport_C11Q4.{u} (windowBarrierA₀_C11Q2 P g)
    (max parameters.recenterConstant 1) (StandardCap.transitionEnd + 10) Cderiv ha₀
    (lt_of_lt_of_le one_pos (le_max_right _ 1)) (le_add_of_nonneg_right (by norm_num))
  have hreq := Classical.choose_spec hex
  obtain ⟨hRequest, hWindow, -⟩ := hreq
  have hReqI := hRequest (nodeA i) (nodeE i) (nodeR i) (nodeQ i) (nodeRho i) hE hR hQ hRho
  obtain ⟨-, hεreq, -, hDreq, -, -⟩ := hReqI
  have hεhalf : εcap ≤ 1 / 2 := hε.trans hεreq
  have hDlarge : StandardCap.transitionEnd + 10 < Dcap := hDreq.trans_le hD
  -- 低次水平集点的 C¹ minimizer
  have hHI := (H.fixedHamiltonIveyRegion_and_scalar_lower records ha₀ hfixed hscalar).1
  have hscalarSt (j : Fin (H.eventCount + 1)) (s : ℝ) (hs : s ∈ H.stageDomain j)
      (y : (H.stage j).Carrier) :
      -(3 / windowBarrierA₀_C11Q2 P g) ≤ metricScalarAt (H.stageMetric j s) y := by
    have htime := (H.stageDomain_subset j hs).1
    have hratio : 3 / (windowBarrierA₀_C11Q2 P g + s) ≤ 3 / windowBarrierA₀_C11Q2 P g :=
      div_le_div_of_nonneg_left (by norm_num : (0 : ℝ) ≤ 3) ha₀ (le_add_of_nonneg_right htime)
    exact (show -(3 / windowBarrierA₀_C11Q2 P g) ≤ -3 / (windowBarrierA₀_C11Q2 P g + s) by
      simpa only [neg_div] using neg_le_neg hratio).trans (hHI j s hs y).2
  have hupperDomain : t.val - (0 : ℝ) ^ 2 ∈ H.stageDomain (H.activeStage t) := by
    simpa only [zero_pow two_ne_zero, sub_zero] using H.activeStage_mem t
  have hscalarClock (j : H.StageInterval i.succ (H.activeStage t)) (s : ℝ)
      (hs : s ∈ Ioo (H.regularizedStageStart t.val 0 j.val)
        (H.regularizedStageEnd t.val k j.val)) (y : (H.stage j.val).Carrier) :
      -(3 / windowBarrierA₀_C11Q2 P g) ≤ metricScalarAt (H.stageMetric j.val (t.val - s ^ 2)) y :=
    hscalarSt j.val _ (H.mapsTo_regularizedStage_Ioo t.val 0 k j.val hs) y
  have hCostC1 := H.regularizedCost_eq_regularizedC1Cost i.succ (H.activeStage t) hl
    t.val (3 / windowBarrierA₀_C11Q2 P g) 0 k hupperDomain hscalarClock x q
  have hfiniteC1 : H.regularizedC1Cost i.succ (H.activeStage t) hl t.val 0 k x q ≠ ⊤ := by
    rw [← hCostC1, hcost]
    exact WithTop.coe_ne_top
  have hMin := H.exists_regularizedC1Cost_minimizer_of_ne_top i.succ (H.activeStage t) hl
    t.val (3 / windowBarrierA₀_C11Q2 P g) 0 k hupperDomain hscalarClock x q hfiniteC1
  obtain ⟨gamma, hC1, hInt, hPole, hEnd, hNodes, hSumC1⟩ := hMin
  have hSum : (∑ j : H.StageInterval i.succ (H.activeStage t),
      H.stageRegularizedAction j.val t.val (gamma j)
        (H.regularizedStageStart t.val 0 j.val) (H.regularizedStageEnd t.val k j.val)) = L := by
    apply WithTop.coe_injective
    exact hSumC1.trans (hCostC1.symm.trans hcost)
  -- 低作用量曲线终点的 cap-core 排除（hWindow）
  have hpast : t.val - k ^ 2 ∈ H.stageDomain i.succ := by
    rw [hevent]
    exact (H.mem_stageDomain_iff (H.stageTime i.succ) i.succ).mpr
      (H.activeStage_stageTime i.succ)
  have hkE : k ≤ nodeE i := (le_div_sqrt_two_of_sq_le_C11Q4 hk.le hr hk2).trans hEge
  have hsqrtClock : Real.sqrt (t.val - H.time i.succ) = k := by
    have hclock : t.val - H.time i.succ = k ^ 2 := by linarith only [hevent]
    rw [hclock, Real.sqrt_sq hk.le]
  have hEndpoint (pole : (H.stageAt t).Carrier)
      (hballP : H.isParabolicallyRmControlledBall t pole (nodeR i))
      (Lc : ℝ) (qc : (H.stage i.succ).Carrier)
      (hCurve : Lc ∈ H.regularizedC1ActionValues i.succ (H.activeStage t) hl
        t.val 0 k pole qc) (hB : Lc ≤ nodeA i)
      (c : (H.event i).RetainedBoundaryIndex) :
      qc ∉ (S c).window ''
        {z : standardCapWindow Dcap | ‖z.val‖ ≤ StandardCap.transitionEnd + 10} := by
    obtain ⟨_hu, _huv, _hupper, _hpast, curve, hCurveC1, hCurveInt,
      hCurvePole, hCurveEnd, hCurveNodes, hCurveSum⟩ := hCurve
    have hsmall : (∑ j : H.StageInterval i.succ (H.activeStage t),
        H.stageRegularizedAction j.val t.val (curve j)
          (H.regularizedStageStart t.val 0 j.val) (H.regularizedStageEnd t.val k j.val)) ≤
        nodeA i := by
      simpa only [hCurveSum] using hB
    have hexclude := hWindow (nodeA i) (nodeE i) (nodeR i) (nodeQ i) (nodeRho i)
      hE hR hQ hRho H parameters records hfixed hscalar t i.succ hl k hk.le hkE
      hpast pole hballP curve hCurveC1 hCurveInt hCurvePole hCurveNodes hsmall
      i le_rfl hl hevent.le (le_max_left _ _) hdelta hneck hlater hderiv
      c Dcap εcap ncap (S c) hD hn hε (hcan c) (hscale c)
    simpa only [hsqrtClock, hCurveEnd] using hexclude
  -- old lifts（EventWindowEndpointPair）
  have hEtwo := two_le_eventLevelE_C11Q4 (by linarith : (0 : ℝ) ≤ A)
  have hSeedBudget : 3 * r ≤ nodeA i := by nlinarith only [hfit, hEtwo, hr]
  have hsmallGamma : (∑ j : H.StageInterval i.succ (H.activeStage t),
      H.stageRegularizedAction j.val t.val (gamma j)
        (H.regularizedStageStart t.val 0 j.val) (H.regularizedStageEnd t.val k j.val)) ≤
      nodeA i := by
    rw [hSum]
    nlinarith only [hL, hfit, hr]
  have hEP := exists_old_seed_and_endpoint_outside_retained_cap_windows H parameters records
    t p x r k (nodeA i) (nodeR i) hr hk hk2 hseed hR hRle hball hSeedBudget aSeed hSeedTime
    hSeedClock seedTrace htrace i hl hevent S hcan hEndpoint gamma hC1 hInt hPole hNodes
    hsmallGamma
  obtain ⟨hfSeed, O, z, hOin, hOout, hzout, hO, hz⟩ := hEP
  exact ⟨hfSeed, Dcap, εcap, ncap, S, hcan, hεhalf, hDlarge, O, z, hOin, hOout,
    hzout.trans hEnd, hO, hz⟩

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory

namespace GC.LongTime.Ch11

universe u

open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory
  (eventLowSublevelContact_of_nodeData_C11Q4)

/-- **全称形 contact（G2）**：有 event 种子的 node 数据（`A' = max A 1`）⇒ G1 的 `hcontact`
（`weightedMinBoundEnd_of_event_C11Q4` 的第二个 binder，逐字）。 -/
theorem eventContact_of_nodeData_C11Q4 {P : OrientedThreeStage.{u}} {g : P.Metric}
    {F : GC.Interface.RawSurgery P g} {δ : ℝ → ℝ} {α : ℝ → ℝ → ℝ} {nr : ℝ → ℝ}
    (params : CutoffParameters)
    (records : ∀ n i, GeometricCutoffRecord (F.tower.history n).toHistory i params)
    (Cderiv : ℝ≥0)
    (hnode : ∀ A, 0 < A → ∀ n, let R := F.tower.history n; let H := R.toHistory;
      ∀ (t : Icc (0 : ℝ) H.horizon) (p : (H.stageAt t).Carrier) (r : ℝ),
        2 * r ^ 2 < (t : ℝ) → (∀ s ∈ Icc ((t : ℝ) / 2) t, δ s < α A s) →
        hasSmallParabolicCurvature H t p r →
        ENNReal.ofReal (A⁻¹ * r ^ 3) ≤ ballVolume (H.stageMetric (H.activeStage t) t) p r →
        ∀ x ∈ riemannianBallOf (H.stageMetric (H.activeStage t) t) p (A * r),
        ∀ ϱ₀ : ℝ, nr t / 100 ≤ ϱ₀ → H.isParabolicallyRmControlledBall t x ϱ₀ →
        (t : ℝ) - r ^ 2 / 2 ≤ H.time (H.activeStage t) →
        ∃ nodeA nodeE nodeR nodeQ nodeRho : Fin H.eventCount → ℝ,
          EventNodeData_C11Q4 P g Cderiv H params (records n) t x r (max A 1)
            nodeA nodeE nodeR nodeQ nodeRho) :
    ∀ A, 0 < A → ∀ n, let R := F.tower.history n; let H := R.toHistory;
      ∀ (t : Icc (0 : ℝ) H.horizon) (p : (H.stageAt t).Carrier) (r : ℝ),
        2 * r ^ 2 < (t : ℝ) → (∀ s ∈ Icc ((t : ℝ) / 2) t, δ s < α A s) →
        hasSmallParabolicCurvature H t p r →
        ENNReal.ofReal (A⁻¹ * r ^ 3) ≤ ballVolume (H.stageMetric (H.activeStage t) t) p r →
        ∀ (b : Icc (0 : ℝ) H.horizon) (hbt : b ≤ t), (b : ℝ) = (t : ℝ) - r ^ 2 →
        ∀ seedTrace : BackwardPointTrace H (H.activeStage b) (H.activeStage t)
          (H.activeStage_mono hbt) p,
        ∀ x ∈ riemannianBallOf (H.stageMetric (H.activeStage t) t) p (A * r),
        ∀ ϱ₀ : ℝ, nr t / 100 ≤ ϱ₀ → H.isParabolicallyRmControlledBall t x ϱ₀ →
        (t : ℝ) - r ^ 2 / 2 ≤ H.time (H.activeStage t) →
        EventLowSublevelContact_C11Q4 H params (windowBarrierA₀_C11Q2 P g) t p x r (max A 1) b
          hbt seedTrace := by
  intro A hA n R H t p r hr hacc hsmall hvol b hbt hb seedTrace x hx ϱ₀ hϱ₀ hball hev
  have hN := hnode A hA n t p r hr hacc hsmall hvol x hx ϱ₀ hϱ₀ hball hev
  obtain ⟨nodeA, nodeE, nodeR, nodeQ, nodeRho, hN'⟩ := hN
  exact eventLowSublevelContact_of_nodeData_C11Q4 Cderiv H (F.tower.initial n) params (records n)
    t p x (le_max_right A 1) (isParabolicallyRmControlledBall_of_seed_C11Q hsmall) b hbt hb
    seedTrace (seedTrace_isRmControlled_C11Q4 hsmall hbt hb seedTrace) hN'

/-- **只差 node 数据**：`WeightedMinBoundEnd_C11Q3` ⇐ records + 有 event 种子的 node 数据
（G1 + G2；contact 已由 node 数据生产）。 -/
theorem weightedMinBoundEnd_of_nodeData_C11Q4 {P : OrientedThreeStage.{u}} {g : P.Metric}
    {F : GC.Interface.RawSurgery P g} {δ : ℝ → ℝ} {α : ℝ → ℝ → ℝ} {nr : ℝ → ℝ}
    (params : CutoffParameters)
    (records : ∀ n i, GeometricCutoffRecord (F.tower.history n).toHistory i params)
    (Cderiv : ℝ≥0)
    (hnode : ∀ A, 0 < A → ∀ n, let R := F.tower.history n; let H := R.toHistory;
      ∀ (t : Icc (0 : ℝ) H.horizon) (p : (H.stageAt t).Carrier) (r : ℝ),
        2 * r ^ 2 < (t : ℝ) → (∀ s ∈ Icc ((t : ℝ) / 2) t, δ s < α A s) →
        hasSmallParabolicCurvature H t p r →
        ENNReal.ofReal (A⁻¹ * r ^ 3) ≤ ballVolume (H.stageMetric (H.activeStage t) t) p r →
        ∀ x ∈ riemannianBallOf (H.stageMetric (H.activeStage t) t) p (A * r),
        ∀ ϱ₀ : ℝ, nr t / 100 ≤ ϱ₀ → H.isParabolicallyRmControlledBall t x ϱ₀ →
        (t : ℝ) - r ^ 2 / 2 ≤ H.time (H.activeStage t) →
        ∃ nodeA nodeE nodeR nodeQ nodeRho : Fin H.eventCount → ℝ,
          EventNodeData_C11Q4 P g Cderiv H params (records n) t x r (max A 1)
            nodeA nodeE nodeR nodeQ nodeRho) :
    WeightedMinBoundEnd_C11Q3 F δ α nr (fun A => cutoffBarrierConst_C11Q3 (max A 1)) :=
  weightedMinBoundEnd_of_event_C11Q4 params records Cderiv hnode
    (eventContact_of_nodeData_C11Q4 params records Cderiv hnode)

/-- **consumer（G2）**：node 数据 + K3（`Λ ≥ E + 1`）⇒ K4。 -/
example {P : OrientedThreeStage.{u}} {g : P.Metric}
    {F : GC.Interface.RawSurgery P g} {δ : ℝ → ℝ} {α : ℝ → ℝ → ℝ} {nr Λ : ℝ → ℝ}
    (params : CutoffParameters)
    (records : ∀ n i, GeometricCutoffRecord (F.tower.history n).toHistory i params)
    (Cderiv : ℝ≥0)
    (hnode : ∀ A, 0 < A → ∀ n, let R := F.tower.history n; let H := R.toHistory;
      ∀ (t : Icc (0 : ℝ) H.horizon) (p : (H.stageAt t).Carrier) (r : ℝ),
        2 * r ^ 2 < (t : ℝ) → (∀ s ∈ Icc ((t : ℝ) / 2) t, δ s < α A s) →
        hasSmallParabolicCurvature H t p r →
        ENNReal.ofReal (A⁻¹ * r ^ 3) ≤ ballVolume (H.stageMetric (H.activeStage t) t) p r →
        ∀ x ∈ riemannianBallOf (H.stageMetric (H.activeStage t) t) p (A * r),
        ∀ ϱ₀ : ℝ, nr t / 100 ≤ ϱ₀ → H.isParabolicallyRmControlledBall t x ϱ₀ →
        (t : ℝ) - r ^ 2 / 2 ≤ H.time (H.activeStage t) →
        ∃ nodeA nodeE nodeR nodeQ nodeRho : Fin H.eventCount → ℝ,
          EventNodeData_C11Q4 P g Cderiv H params (records n) t x r (max A 1)
            nodeA nodeE nodeR nodeQ nodeRho)
    (hK3 : SurgeryActionBarrier_C11Q F δ α nr Λ)
    (hΛ : ∀ A, 0 < A →
      weightedMinLevel_C11Q2 (fun A => cutoffBarrierConst_C11Q3 (max A 1)) A ≤ Λ A) :
    BoundedReducedLengthNearSeed_C11Q F δ α nr
      (weightedMinLengthConst_C11Q2 (fun A => cutoffBarrierConst_C11Q3 (max A 1))) :=
  boundedReducedLength_of_weightedMinBoundEnd_C11Q3
    (weightedMinBoundEnd_of_nodeData_C11Q4 params records Cderiv hnode) hK3 hΛ

end GC.LongTime.Ch11
