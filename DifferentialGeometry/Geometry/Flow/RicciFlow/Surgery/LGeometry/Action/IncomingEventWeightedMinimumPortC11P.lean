import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.LGeometry.Action.EventWeightedContinuation
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.LGeometry.Action.DistinctPoleWeightedMinimum
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.HistoryPartition
import Mathlib.Analysis.SpecialFunctions.ExpDeriv

/-!
# S-CH11-FIX8 port of astra `IncomingEventWeightedMinimum`（`PortC11P`）

来源：donor `IncomingEventWeightedMinimum.lean`（Jui-Hui `chapter11-astra` @ `a73e4bdbfd`）。
donor 文本在本树 elaboration 失败（8 个 error，其中 1 个是 parse error，其余多为它的级联）。
本 port 只有 elaboration 层面修补（no statement / definition / proof idea altered；不加 `set_option`）：
* 两处 `hmargin`：`linarith only [hL, hcube, …]` 把 `-2 * v ^ 3 / r ^ 2` 与 `2 * v ^ 3 / r ^ 2`
  当作两个不同原子 → 补 `hneg : -2 * v ^ 3 / r ^ 2 = -(2 * v ^ 3 / r ^ 2) := by ring` 给 linarith；
* `hMle` / `hMv0`：`rw [hMstage]` 的 `hMstage` 讲 `tracedPhysicalWeightedMinimum … v`，目标里是 let 变量
  `M v`，`rw` 不 zeta-delta → 先 `have hMs : M v = sInf (Set.range W) := hMstage`
  （defeq 转型）再 `rw [hMs]`；
* `hmnonneg`：`simpa only [← hvalue] using hMv0` 里 `(0 : WithTop ℝ)` 与 `↑(0 : ℝ)`（及 `LE` 实例）
  形不同 → `have h := hMv0; rw [← hvalue] at h; exact h`（`exact` 做 defeq）；
* `hgcont`：`exact ((((…` 比括号配对多开了一个 `(`（donor parse error，下一行的 `have` 被吞）；
  且 `.exp` 在本树解析成 `Tendsto.exp`（`NormedSpace.exp`）而非 `Real.exp` → 改成
  `Real.continuous_exp.continuousAt.comp harg`（`harg` 用 `fun_prop`）再 `.div continuousAt_id hk.ne'`；
* `rw [hrewrite k] at hupper`：`hupper` 是未 beta 归约的 `(fun v ↦ …) k < upper` → 先
  `replace hupper : Real.exp (…) * m k / k < upper := hupper`。
* 末尾 `rcases eq_or_lt_of_le hvk`：`hvk : v ∈ Ici k`（`self_mem_nhdsWithin` 给的成员关系），本树不再自动
  展开成 `k ≤ v` → `Set.mem_Ici.mp hvk`。
* `heq` 里 `field_simp [hgk.ne'] <;> ring`：本树 `field_simp` 已把目标关掉，`ring` never executed
  警告 → 去掉 `<;> ring`。

原路径 `IncomingEventWeightedMinimum` 是只 import 本文件的 re-export shim。
-/

set_option autoImplicit false
noncomputable section
open Set Filter
open DifferentialGeometry.Geometry.Curvature
open scoped Manifold ContDiff Topology
namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory
universe u

private theorem physicalWeightedCost_nonnegative_of_recent_half_clock
    (H : ObservedHistory.{u}) (parameters : CutoffParameters)
    (records : ∀ j : Fin H.eventCount, GeometricCutoffRecord H j parameters)
    (a₀ : ℝ) (ha₀ : 0 < a₀)
    (hfixed : ∀ y, InFixedHamiltonIveyRegion (H.initialMetric 0) a₀ y)
    (hscalar : ∀ y, -3 / a₀ ≤ metricScalarAt (H.initialMetric 0) y)
    (first last : Fin (H.eventCount + 1)) (hle : first ≤ last)
    (T r A v : ℝ) (hr : 0 < r) (hv : 0 < v)
    (hhalf : v ^ 2 ≤ r ^ 2 / 2) (hT : 2 * r ^ 2 < T)
    (x : (H.stage last).Carrier) (O : (H.stage first).Carrier) :
    ∀ q : (H.stage first).Carrier,
      (0 : WithTop ℝ) ≤ H.physicalWeightedCost first last hle T (3 / a₀) r A v x O q := by
  classical
  intro q
  have hr2 : 0 < r ^ 2 := sq_pos_of_pos hr
  have hlow := H.regularizedCost_ge_recent_half_time_of_cutoff_records records ha₀
    hfixed hscalar first last hle hr hv.le hhalf hT x q
  have hcube : 2 * v ^ 3 / r ^ 2 ≤ v := by
    apply (div_le_iff₀ hr2).mpr
    have hh := mul_le_mul_of_nonneg_right hhalf hv.le
    nlinarith only [hh]
  have hvr : v ≤ 3 * r / 4 := by
    apply (sq_le_sq₀ hv.le (by positivity : 0 ≤ 3 * r / 4)).mp
    nlinarith only [hhalf, hr2]
  by_cases hinside : riemannianEDistOf (H.stageMetric first (T - v ^ 2)) O q <
      ENNReal.ofReal (r * (A * (1 - 2 * v ^ 2 / r ^ 2) + 1 / 10))
  · have harg : (riemannianEDistOf (H.stageMetric first (T - v ^ 2)) O q).toReal / r -
        A * (1 - 2 * v ^ 2 / r ^ 2) < 1 / 10 := by
      have hd := ENNReal.toReal_lt_of_lt_ofReal hinside
      apply (sub_lt_iff_lt_add).mpr
      apply (div_lt_iff₀ hr).mpr
      nlinarith only [hd]
    cases hcost : H.regularizedCost first last hle T (3 / a₀) 0 v x q
        using WithTop.recTopCoe with
    | top =>
      simp only [physicalWeightedCost, ite_eq_left hinside, hcost, WithTop.map_top]
      exact le_top
    | coe L =>
      have hL : -2 * v ^ 3 / r ^ 2 ≤ L :=
        WithTop.coe_le_coe.mp (hlow.trans_eq hcost)
      have hneg : -2 * v ^ 3 / r ^ 2 = -(2 * v ^ 3 / r ^ 2) := by ring
      have hmargin : r / 4 ≤ L + r := by linarith only [hL, hcube, hvr, hneg]
      have hfactor : 0 < 2 * v * L + 2 * r * v := by
        have hh := mul_pos (mul_pos (by norm_num : (0 : ℝ) < 2) hv)
          ((by positivity : 0 < r / 4).trans_le hmargin)
        nlinarith only [hh]
      have hpos := mul_pos (DifferentialGeometry.Analysis.SingularBarrier.pos harg) hfactor
      simp only [physicalWeightedCost, ite_eq_left hinside, hcost, WithTop.map_coe]
      exact WithTop.coe_le_coe.mpr hpos.le
  · simp only [physicalWeightedCost, ite_eq_right hinside]
    exact le_top

private theorem exists_incoming_stage_traced_minimum_eq_at_event
    (H : ObservedHistory.{u})
    (aSeed t : Icc (0 : ℝ) H.horizon) (hSeedTime : aSeed ≤ t)
    (p x : (H.stageAt t).Carrier)
    (seedTrace : BackwardPointTrace H (H.activeStage aSeed) (H.activeStage t)
      (H.activeStage_mono hSeedTime) p)
    (B r A k b : ℝ) (hr : 0 < r) (hk : 0 < k) (hkb : k < b)
    (hSeedClock : (aSeed : ℝ) = t.val - r ^ 2)
    (hhalf : k ^ 2 < r ^ 2 / 2)
    (i : Fin H.eventCount) (hl : i.succ ≤ H.activeStage t)
    (hevent : t.val - k ^ 2 = H.time i.succ)
    (hfSeed : H.activeStage aSeed ≤ i.castSucc)
    (O : (H.event i).old)
    (hO : O.val.val = seedTrace.point i.castSucc hfSeed (i.castSucc_le_succ.trans hl)) :
    let M := H.tracedPhysicalWeightedMinimum aSeed t hSeedTime p x seedTrace B r A
    ∃ d : ℝ, k < d ∧ d ≤ b ∧ d ^ 2 < r ^ 2 / 2 ∧
      ∀ v ∈ Ioo k d,
        0 < v ∧
        H.time i.castSucc < t.val - v ^ 2 ∧
        t.val - v ^ 2 < H.time i.succ ∧
        (aSeed : ℝ) ≤ t.val - v ^ 2 ∧
        ∃ (av : Icc (0 : ℝ) H.horizon) (has : aSeed ≤ av) (hat : av ≤ t),
          (av : ℝ) = t.val - v ^ 2 ∧ H.activeStage av = i.castSucc ∧
          HEq (seedTrace.point (H.activeStage av) (H.activeStage_mono has)
            (H.activeStage_mono hat)) O.val.val ∧
          M v = sInf (Set.range
            (H.physicalWeightedCost i.castSucc (H.activeStage t)
              (i.castSucc_le_succ.trans hl) t.val B r A v x O.val.val)) := by
  classical
  dsimp only
  have hr2 : 0 < r ^ 2 := sq_pos_of_pos hr
  have hOldSq : k ^ 2 < t.val - H.time i.castSucc := by
    have htimes := H.time_strictMono i.castSucc_lt_succ
    linarith only [hevent, htimes]
  have hcap : k < min b
      (min (Real.sqrt (r ^ 2 / 2)) (Real.sqrt (t.val - H.time i.castSucc))) :=
    lt_min hkb (lt_min ((Real.lt_sqrt hk.le).2 hhalf)
      ((Real.lt_sqrt hk.le).2 hOldSq))
  obtain ⟨d, hkd, hdcap⟩ := exists_between hcap
  have hdpos : 0 < d := hk.trans hkd
  have hdb : d < b := hdcap.trans_le (min_le_left _ _)
  have hdHalf : d < Real.sqrt (r ^ 2 / 2) :=
    hdcap.trans_le ((min_le_right _ _).trans (min_le_left _ _))
  have hdOld : d < Real.sqrt (t.val - H.time i.castSucc) :=
    hdcap.trans_le ((min_le_right _ _).trans (min_le_right _ _))
  refine ⟨d, hkd, hdb.le, (Real.lt_sqrt hdpos.le).1 hdHalf, ?_⟩
  intro v hv
  have hvpos : 0 < v := hk.trans hv.1
  have hvHalf : v ^ 2 < r ^ 2 / 2 :=
    (Real.lt_sqrt hvpos.le).1 (hv.2.trans hdHalf)
  have hvOld : v ^ 2 < t.val - H.time i.castSucc :=
    (Real.lt_sqrt hvpos.le).1 (hv.2.trans hdOld)
  have hbefore : H.time i.castSucc < t.val - v ^ 2 := by
    linarith only [hvOld]
  have hafter : t.val - v ^ 2 < H.time i.succ := by
    have hsq := mul_pos (sub_pos.mpr hv.1) (add_pos hvpos hk)
    nlinarith only [hsq, hevent]
  have hseed : (aSeed : ℝ) ≤ t.val - v ^ 2 := by
    rw [hSeedClock]
    nlinarith only [hvHalf, hr2]
  have hpast : t.val - v ^ 2 ∈
      Ioo (H.time i.castSucc) (H.stageEndTime i.castSucc) := by
    rw [H.stageEndTime_castSucc]
    exact ⟨hbefore, hafter⟩
  let av : Icc (0 : ℝ) H.horizon :=
    ⟨t.val - v ^ 2, aSeed.property.1.trans hseed,
      (sub_le_self t.val (sq_nonneg v)).trans t.property.2⟩
  have has : aSeed ≤ av := hseed
  have hat : av ≤ t := sub_le_self t.val (sq_nonneg v)
  have hstage : H.activeStage av = i.castSucc :=
    (H.mem_stageDomain_iff av i.castSucc).mp
      (H.mem_stageDomain_of_mem_Ioo hpast)
  have hpoint (j : Fin (H.eventCount + 1))
      (hjs : H.activeStage aSeed ≤ j) (hjt : j ≤ H.activeStage t)
      (hj : j = i.castSucc) : HEq (seedTrace.point j hjs hjt) O.val.val := by
    subst j
    exact heq_of_eq hO.symm
  have hwhole (j : Fin (H.eventCount + 1))
      (hjs : H.activeStage aSeed ≤ j) (hjt : j ≤ H.activeStage t)
      (hj : j = i.castSucc) :
      sInf (Set.range (H.physicalWeightedCost j (H.activeStage t) hjt
        t.val B r A v x (seedTrace.point j hjs hjt))) =
      sInf (Set.range (H.physicalWeightedCost i.castSucc (H.activeStage t)
        (i.castSucc_le_succ.trans hl) t.val B r A v x O.val.val)) := by
    subst j
    rw [hO]
  refine ⟨hvpos, hbefore, hafter, hseed, av, has, hat, rfl, hstage,
    hpoint (H.activeStage av) (H.activeStage_mono has)
      (H.activeStage_mono hat) hstage, ?_⟩
  dsimp only [tracedPhysicalWeightedMinimum]
  rw [dite_eq_left hseed]
  exact hwhole (H.activeStage av) (H.activeStage_mono has)
    (H.activeStage_mono hat) hstage

theorem traced_physical_weighted_minimum_right_control_of_event_window_data
    (H : ObservedHistory.{u}) (parameters : CutoffParameters)
    (records : ∀ j : Fin H.eventCount, GeometricCutoffRecord H j parameters)
    (a₀ : ℝ) (ha₀ : 0 < a₀)
    (hfixed : ∀ y, InFixedHamiltonIveyRegion (H.initialMetric 0) a₀ y)
    (hscalar : ∀ y, -3 / a₀ ≤ metricScalarAt (H.initialMetric 0) y)
    (t : Icc (0 : ℝ) H.horizon) (p x : (H.stageAt t).Carrier)
    (r A k : ℝ) (hr : 0 < r) (hk : 0 < k)
    (hhalf : k ^ 2 < r ^ 2 / 2) (hT : 2 * r ^ 2 < t.val)
    (aSeed : Icc (0 : ℝ) H.horizon) (hSeedTime : aSeed ≤ t)
    (hSeedClock : (aSeed : ℝ) = t.val - r ^ 2)
    (seedTrace : BackwardPointTrace H (H.activeStage aSeed) (H.activeStage t)
      (H.activeStage_mono hSeedTime) p)
    (i : Fin H.eventCount) (hfSeed : H.activeStage aSeed ≤ i.castSucc)
    (hl : i.succ ≤ H.activeStage t)
    (hevent : t.val - k ^ 2 = H.time i.succ)
    {Dcap εcap : ℝ} {ncap : ℕ}
    (S : ∀ c : (H.event i).RetainedBoundaryIndex,
      (H.event i).PresentedStaticCap parameters.fixed Dcap ncap εcap c)
    (hcanonical : ∀ c, (S c).hasCanonicalWindow)
    (hε : εcap ≤ 1 / 2) (hD : StandardCap.transitionEnd + 10 < Dcap)
    (O z : (H.event i).old)
    (hOin : O.val.val = seedTrace.point i.castSucc hfSeed (i.castSucc_le_succ.trans hl))
    (hO : ∀ c, (H.event i).oldOutput O ∉ (S c).window ''
      {y : standardCapWindow Dcap | ‖y.val‖ ≤ StandardCap.transitionEnd + 10})
    (hz : ∀ c, (H.event i).oldOutput z ∉ (S c).window ''
      {y : standardCapWindow Dcap | ‖y.val‖ ≤ StandardCap.transitionEnd + 10})
    (L : ℝ)
    (hinside : riemannianEDistOf (H.event i).outputMetric
        ((H.event i).oldOutput O) ((H.event i).oldOutput z) <
      ENNReal.ofReal (r * (A * (1 - 2 * k ^ 2 / r ^ 2) + 1 / 10)))
    (hcost : H.regularizedCost i.succ (H.activeStage t) hl t.val (3 / a₀) 0 k x
      ((H.event i).oldOutput z) = (L : WithTop ℝ))
    (hcontact : H.physicalWeightedCost i.succ (H.activeStage t) hl t.val (3 / a₀) r A k x
        ((H.event i).oldOutput O) ((H.event i).oldOutput z) =
      H.tracedPhysicalWeightedMinimum aSeed t hSeedTime p x seedTrace (3 / a₀) r A k) :
    let M := H.tracedPhysicalWeightedMinimum aSeed t hSeedTime p x seedTrace (3 / a₀) r A
    let m : ℝ → ℝ := fun v => (M v).untopD 0
    M k ≠ ⊤ ∧ 0 < m k ∧
    (∀ η : ℝ, 0 < η → ∃ d : ℝ, k < d ∧ d ^ 2 < r ^ 2 / 2 ∧
      ∀ v ∈ Ioo k d,
        t.val - v ^ 2 ∈ Ioo (H.time i.castSucc) (H.time i.succ) ∧
        BddBelow (Set.range (H.physicalWeightedCost i.castSucc (H.activeStage t)
          (i.castSucc_le_succ.trans hl) t.val (3 / a₀) r A v x O.val.val)) ∧
        M v = sInf (Set.range (H.physicalWeightedCost i.castSucc (H.activeStage t)
          (i.castSucc_le_succ.trans hl) t.val (3 / a₀) r A v x O.val.val)) ∧
        M v ≠ ⊤ ∧ 0 ≤ m v ∧ M v < M k + (η : WithTop ℝ) ∧ m v < m k + η) ∧
    ∀ C : ℝ,
      UpperSemicontinuousWithinAt
        (fun v : ℝ => Real.exp (-C * v ^ 2 / r ^ 2 - 32 * v / r) * m v / v)
        (Ici k) k := by
  classical
  intro M m
  have hr2 : 0 < r ^ 2 := sq_pos_of_pos hr
  obtain ⟨b, hkb, _, hbhalf, hstage⟩ :=
    exists_incoming_stage_traced_minimum_eq_at_event H aSeed t hSeedTime p x seedTrace
      (3 / a₀) r A k (k + 1) hr hk (by linarith) hSeedClock hhalf i hl hevent hfSeed O hOin
  have hHI := (H.fixedHamiltonIveyRegion_and_scalar_lower records ha₀ hfixed hscalar).1
  have hglobal (j : H.StageInterval i.castSucc (H.activeStage t)) (s : ℝ)
      (hs : s ∈ Ioo (H.regularizedStageStart t.val 0 j.val)
        (H.regularizedStageEnd t.val b j.val)) (y : (H.stage j.val).Carrier) :
      -(3 / a₀) ≤ metricScalarAt (H.stageMetric j.val (t.val - s ^ 2)) y := by
    have htime := H.mapsTo_regularizedStage_Ioo t.val 0 b j.val hs
    have htime0 : 0 ≤ t.val - s ^ 2 := (H.stageDomain_subset j.val htime).1
    have hden : 0 < a₀ + (t.val - s ^ 2) := by linarith only [ha₀, htime0]
    have hR := (hHI j.val (t.val - s ^ 2) htime y).2
    have hfrac : 3 / (a₀ + (t.val - s ^ 2)) ≤ 3 / a₀ := by
      apply (div_le_div_iff₀ hden ha₀).mpr
      linarith only [htime0]
    exact (show -(3 / a₀) ≤ -3 / (a₀ + (t.val - s ^ 2)) by
      simpa only [neg_div] using neg_le_neg hfrac).trans hR
  have hlow := H.regularizedCost_ge_recent_half_time_of_cutoff_records records ha₀
    hfixed hscalar i.succ (H.activeStage t) hl hr hk.le hhalf.le hT x
    ((H.event i).oldOutput z)
  have hL : -2 * k ^ 3 / r ^ 2 ≤ L :=
    WithTop.coe_le_coe.mp (hlow.trans_eq hcost)
  have hcube : 2 * k ^ 3 / r ^ 2 ≤ k := by
    apply (div_le_iff₀ hr2).mpr
    have hh := mul_le_mul_of_nonneg_right hhalf.le hk.le
    nlinarith only [hh]
  have hkr : k ≤ 3 * r / 4 := by
    apply (sq_le_sq₀ hk.le (by positivity : 0 ≤ 3 * r / 4)).mp
    nlinarith only [hhalf, hr2]
  have hneg : -2 * k ^ 3 / r ^ 2 = -(2 * k ^ 3 / r ^ 2) := by ring
  have hmargin : r / 4 ≤ L + r := by linarith only [hL, hcube, hkr, hneg]
  have hpositive : 0 < 2 * k * L + 2 * r * k := by
    have hh := mul_pos (mul_pos (by norm_num : (0 : ℝ) < 2) hk)
      ((by positivity : 0 < r / 4).trans_le hmargin)
    nlinarith only [hh]
  let dPost := riemannianEDistOf (H.event i).outputMetric
    ((H.event i).oldOutput O) ((H.event i).oldOutput z)
  have harg : dPost.toReal / r - A * (1 - 2 * k ^ 2 / r ^ 2) < 1 / 10 := by
    have hd := ENNReal.toReal_lt_of_lt_ofReal hinside
    apply (sub_lt_iff_lt_add).mpr
    apply (div_lt_iff₀ hr).mpr
    dsimp only [dPost]
    nlinarith only [hd]
  let postValue : ℝ := DifferentialGeometry.Analysis.SingularBarrier.value
    (dPost.toReal / r - A * (1 - 2 * k ^ 2 / r ^ 2)) * (2 * k * L + 2 * r * k)
  have hpostpos : 0 < postValue :=
    mul_pos (DifferentialGeometry.Analysis.SingularBarrier.pos harg) hpositive
  have hpostMetric : H.stageMetric i.succ (t.val - k ^ 2) = (H.event i).outputMetric := by
    rw [hevent, H.stageMetric_initial]
    exact (H.event_output i).symm
  have hpost : H.physicalWeightedCost i.succ (H.activeStage t) hl t.val (3 / a₀) r A k x
      ((H.event i).oldOutput O) ((H.event i).oldOutput z) = (postValue : WithTop ℝ) := by
    simp only [physicalWeightedCost, hpostMetric, ite_eq_left hinside, hcost,
      WithTop.map_coe, postValue, dPost]
  have hMk : M k = (postValue : WithTop ℝ) := hcontact.symm.trans hpost
  have hmk : m k = postValue := by
    dsimp only [m]
    rw [hMk, WithTop.untopD_coe]
  have hMfinite : M k ≠ ⊤ := by rw [hMk]; exact WithTop.coe_ne_top
  have hmkpos : 0 < m k := hmk.symm ▸ hpostpos
  have htransfer := H.exists_physicalWeightedCost_lt_after_event_of_outside_canonical_cap_windows
    i (H.activeStage t) hl hr hk hkb hevent (H.activeStage_mem t) hglobal x S
    (records i).old_eq_retained hcanonical hε hD O z hO hz hinside hcost hpositive
  have hright : ∀ η : ℝ, 0 < η → ∃ d : ℝ, k < d ∧ d ^ 2 < r ^ 2 / 2 ∧
      ∀ v ∈ Ioo k d,
        t.val - v ^ 2 ∈ Ioo (H.time i.castSucc) (H.time i.succ) ∧
        BddBelow (Set.range (H.physicalWeightedCost i.castSucc (H.activeStage t)
          (i.castSucc_le_succ.trans hl) t.val (3 / a₀) r A v x O.val.val)) ∧
        M v = sInf (Set.range (H.physicalWeightedCost i.castSucc (H.activeStage t)
          (i.castSucc_le_succ.trans hl) t.val (3 / a₀) r A v x O.val.val)) ∧
        M v ≠ ⊤ ∧ 0 ≤ m v ∧ M v < M k + (η : WithTop ℝ) ∧ m v < m k + η := by
    intro η hη
    obtain ⟨d, hkd, hdb, hcomp⟩ := htransfer η hη
    have hdhalf : d ^ 2 < r ^ 2 / 2 :=
      (pow_le_pow_left₀ (hk.le.trans hkd.le) hdb 2).trans_lt hbhalf
    refine ⟨d, hkd, hdhalf, ?_⟩
    intro v hv
    have hvb : v ∈ Ioo k b := ⟨hv.1, hv.2.trans_le hdb⟩
    obtain ⟨hv0, htimeL, htimeR, _, _, _, _, _, _, _, hMstage⟩ := hstage v hvb
    have hvhalf : v ^ 2 ≤ r ^ 2 / 2 :=
      (pow_le_pow_left₀ hv0.le hv.2.le 2).trans hdhalf.le
    let W := H.physicalWeightedCost i.castSucc (H.activeStage t)
      (i.castSucc_le_succ.trans hl) t.val (3 / a₀) r A v x O.val.val
    have hWnonneg : ∀ q, (0 : WithTop ℝ) ≤ W q :=
      physicalWeightedCost_nonnegative_of_recent_half_clock H parameters records a₀ ha₀
        hfixed hscalar i.castSucc (H.activeStage t) (i.castSucc_le_succ.trans hl)
        t.val r A v hr hv0 hvhalf hT x O.val.val
    have hWbdd : BddBelow (Set.range W) := ⟨0, by
      rintro _ ⟨q, rfl⟩
      exact hWnonneg q⟩
    have hWne : (Set.range W).Nonempty := ⟨W z.val.val, ⟨z.val.val, rfl⟩⟩
    have hMs : M v = sInf (Set.range W) := hMstage
    have hMle : M v ≤ W z.val.val := by
      rw [hMs]
      exact csInf_le hWbdd ⟨z.val.val, rfl⟩
    have hMv0 : (0 : WithTop ℝ) ≤ M v := by
      rw [hMs]
      exact le_csInf hWne (by rintro _ ⟨q, rfl⟩; exact hWnonneg q)
    have hMvlt : M v < M k + (η : WithTop ℝ) := by
      have hh := hcomp v hv
      rw [hcontact] at hh
      exact hMle.trans_lt hh
    have hMvltReal : M v < ((postValue + η : ℝ) : WithTop ℝ) := by
      simpa only [hMk, WithTop.coe_add] using hMvlt
    have hfinite : M v ≠ ⊤ := ne_top_of_lt hMvltReal
    obtain ⟨value, hvalue⟩ := WithTop.ne_top_iff_exists.mp hfinite
    have hmv : m v = value := by
      dsimp only [m]
      rw [← hvalue, WithTop.untopD_coe]
    have hmnonneg : 0 ≤ m v := by
      rw [hmv]
      exact WithTop.coe_le_coe.mp (by
        have h := hMv0
        rw [← hvalue] at h
        exact h)
    have hmlt : m v < m k + η := by
      rw [hmv, hmk]
      exact WithTop.coe_lt_coe.mp (by simpa only [← hvalue] using hMvltReal)
    exact ⟨⟨htimeL, htimeR⟩, hWbdd, hMstage, hfinite, hmnonneg, hMvlt, hmlt⟩
  refine ⟨hMfinite, hmkpos, hright, ?_⟩
  intro C
  let g : ℝ → ℝ := fun v => Real.exp (-C * v ^ 2 / r ^ 2 - 32 * v / r) / v
  have hgk : 0 < g k := div_pos (Real.exp_pos _) hk
  have hgcont : ContinuousAt g k := by
    have harg : ContinuousAt (fun v : ℝ => -C * v ^ 2 / r ^ 2 - 32 * v / r) k := by
      fun_prop
    exact (Real.continuous_exp.continuousAt.comp harg).div continuousAt_id hk.ne'
  have hrewrite (v : ℝ) :
      Real.exp (-C * v ^ 2 / r ^ 2 - 32 * v / r) * m v / v = g v * m v := by
    dsimp only [g]
    ring
  intro upper hupper
  replace hupper : Real.exp (-C * k ^ 2 / r ^ 2 - 32 * k / r) * m k / k < upper := hupper
  rw [hrewrite k] at hupper
  let η : ℝ := (upper - g k * m k) / (2 * g k)
  have hη : 0 < η := div_pos (sub_pos.mpr hupper) (mul_pos (by norm_num) hgk)
  have hnearAt : g k * (m k + η) < upper := by
    have heq : g k * (m k + η) = g k * m k + (upper - g k * m k) / 2 := by
      dsimp only [η]
      field_simp [hgk.ne']
    rw [heq]
    linarith only [hupper]
  obtain ⟨d, hkd, _, hrightη⟩ := hright η hη
  have hnear : ∀ᶠ v in 𝓝 k, g v * (m k + η) < upper :=
    (hgcont.mul continuousAt_const).eventually (Iio_mem_nhds hnearAt)
  have hpos : ∀ᶠ v in 𝓝 k, 0 < v := Ioi_mem_nhds hk
  have hlt : ∀ᶠ v in 𝓝 k, v < d := Iio_mem_nhds hkd
  filter_upwards [hnear.filter_mono nhdsWithin_le_nhds,
    hpos.filter_mono nhdsWithin_le_nhds, hlt.filter_mono nhdsWithin_le_nhds,
    self_mem_nhdsWithin] with v hnearv hvpos hvd hvk
  rw [hrewrite v]
  rcases eq_or_lt_of_le (Set.mem_Ici.mp hvk) with heq | hltv
  · simpa only [← heq] using hupper
  · have hm := (hrightη v ⟨hltv, hvd⟩).2.2.2.2.2.2
    exact (mul_lt_mul_of_pos_left hm (div_pos (Real.exp_pos _) hvpos)).trans hnearv

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory
