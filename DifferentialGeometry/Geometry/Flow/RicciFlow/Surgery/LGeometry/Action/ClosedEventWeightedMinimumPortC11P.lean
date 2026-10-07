import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.LGeometry.Action.PhysicalWeightedStageAttainment
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.LGeometry.Action.Joining
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.LGeometry.Action.DistinctPoleWeightedTemporalSupport

/-!
# S-CH11-FIX9 port of astra `ClosedEventWeightedMinimum`（`PortC11P`）

来源：donor `ClosedEventWeightedMinimum.lean`（Jui-Hui `chapter11-astra` @ `a73e4bdbfd`）。
donor 文本在本树 elaboration 失败。本 port 只有 elaboration 层面修补（no statement / definition /
proof idea altered；不加 `set_option`）：
* `open private lowerSemicontinuous_variable_positive_affine_map from` 指向
  `…PhysicalWeightedSemicontinuity`：原路径已是 FIX4 的 port + shim，private 声明在 `…PortC11P` →
  改指 `…PortC11P`；
* `open scoped` 补 `NNReal ENNReal`（陈述里的 `ℝ≥0∞` 与 `ℝ≥0`，donor 漏开；`LE Type` / 令牌 `∞`）；
* `hV` 里 `ContinuousOn.comp` 的 `MapsTo` 实参：`fun z hz => …` 的 `hz` 类型未知（`MapsTo` 的绑定是
  strict-implicit）→ 给 `hz` 显式类型；
* `hVle` 里 `(by simpa … using\n hP₀ …)` 括号内多行 `by`（下一行缩进小于 tactic 列，解析中断）→
  拆成 `have h1 := hP₀ …; rw [Real.norm_eq_abs] at h1; exact …`；
* 两处 `simpa only [stageDomain, Fin.lastCases_last, H.stageEndTime_last] using And.intro …`：目标是
  `∈ Icc` 成员 → 补 `Set.mem_Icc`；
* `hwbound` 的 `rw [hMstage w hwak]`：`M` 是 let，`hwbound` 里已 zeta 成 `tracedPhysicalWeightedMinimum`
  → 先 `have hMw : tracedPhysicalWeightedMinimum … w = Mstage w := hMstage w hwak`（defeq）；
* `hV` 里 `rw [he] at hh`：`hh` 的函数是 `(fun q => scalar q.1 q.2) ∘ (fun z => …)`（`Function.comp`），
  `he` 的左端是展开形 → 先 `have hh' : ContinuousOn (展开形) … := hh`（defeq）再 `rw [he] at hh'`；
* `simpa only [WithTop.map_coe] using WithTop.coe_le_coe.mpr …`（`↑0` 与 `0`、实例 `WithTop.instLE` 与
  `instPreorder.toLE`）→ `rw [WithTop.map_coe]; exact …`；
* `hKdist` 的 `ContinuousAt.comp … (hdist.continuousAt.comp continuous_subtype_val.continuousAt)`：
  内层 `f` 被统一成 `fun z => z` → 先 `(hdist.comp continuous_subtype_val).continuousAt`；
* `exact ⟨(w, y), hy ▸ hw, rfl⟩`：`▸` 找不到目标形 → `le_trans hy.symm.le hw`；
* `htail` 里 `intervalIntegral.integral_mono_on … intervalIntegrable_const`：测度 `μ` 不再由后续实参推出
  （`IsLocallyFiniteMeasure ?m` stuck）→ 显式 `(μ := volume)`；
* `hKdist` 里 `ContinuousAt.comp` 显式 `(g := ENNReal.toReal) (f := fun z : K => dist z.val) (x := z)`；
* `letI : CompactSpace K := …`（目标是命题）→ `let : CompactSpace K := …`（linter 建议）；
* `hmargin` 的 `linarith`：`-2 * k ^ 3 / r ^ 2` 与 `2 * k ^ 3 / r ^ 2` 被当成不同原子 → 先 `hneg`。

原路径 `ClosedEventWeightedMinimum` 是只 import 本文件的 re-export shim。
-/

set_option autoImplicit false
noncomputable section
open Set Filter MeasureTheory
open DifferentialGeometry DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.PDE.RicciFlow.Perelman
open scoped Manifold ContDiff Topology BigOperators Interval NNReal ENNReal

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory
universe u

open private exists_regularizedC1Action_lt_of_regularizedCost_le from
  DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.LGeometry.Action.EndpointSemicontinuity
open private lowerSemicontinuous_variable_positive_affine_map from
  DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.LGeometry.Action.PhysicalWeightedSemicontinuityPortC11P

private theorem eventually_regularizedCost_le_at_closed_larger_clock
    (H : ObservedHistory.{u}) (first last : Fin (H.eventCount + 1)) (hle : first ≤ last)
    (T B a k : ℝ) (ha : 0 < a) (hak : a ≤ k)
    (hupper : T ∈ H.stageDomain last)
    (hclock : ∀ w ∈ Icc a k,
      T - w ^ 2 ∈ Ico (H.time first) (H.stageEndTime first))
    (hscalar : ∀ j : H.StageInterval first last,
      ∀ s ∈ Ioo (H.regularizedStageStart T 0 j.val) (H.regularizedStageEnd T k j.val),
      ∀ y : (H.stage j.val).Carrier,
        -B ≤ metricScalarAt (H.stageMetric j.val (T - s ^ 2)) y)
    (x : (H.stage last).Carrier) (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ w in 𝓝[Icc a k] k, ∀ (q : (H.stage first).Carrier) (L : ℝ),
      H.regularizedCost first last hle T B 0 w x q = (L : WithTop ℝ) →
      H.regularizedCost first last hle T B 0 k x q ≤ ((L + ε : ℝ) : WithTop ℝ) := by
  classical
  have hk0 : 0 < k := ha.trans_le hak
  have hzero : T - 0 ^ 2 ∈ H.stageDomain last := by simpa using hupper
  have hka := hclock a ⟨le_rfl, hak⟩
  obtain ⟨G, hG⟩ := H.exists_stage_incomingSlab_metric first (hka.1.trans_lt hka.2)
  let V : ℝ × (H.stage first).Carrier → ℝ := fun z =>
    2 * z.1 ^ 2 * metricScalarAt (H.stageMetric first (T - z.1 ^ 2)) z.2
  have hV : ContinuousOn V (Icc a k ×ˢ univ) := by
    have hh := G.equation.scalarCont.comp
      (f := fun z : ℝ × (H.stage first).Carrier => (T - z.1 ^ 2, z.2))
      ((continuous_const.sub (continuous_fst.pow 2)).prodMk continuous_snd).continuousOn
      (fun z (hz : z ∈ Icc a k ×ˢ (univ : Set (H.stage first).Carrier)) =>
        ⟨hclock z.1 hz.1, mem_univ _⟩)
    have he : (fun z : ℝ × (H.stage first).Carrier =>
        G.flow.scalar (T - z.1 ^ 2) z.2) =
        fun z => metricScalarAt (H.stageMetric first (T - z.1 ^ 2)) z.2 := by
      funext z
      simp only [SolutionOn.scalar, SolutionFamily.scalar, hG]
    have hh' : ContinuousOn (fun z : ℝ × (H.stage first).Carrier =>
        G.flow.scalar (T - z.1 ^ 2) z.2) (Icc a k ×ˢ univ) := hh
    rw [he] at hh'
    exact (continuous_const.mul (continuous_fst.pow 2)).continuousOn.mul hh'
  obtain ⟨P₀, hP₀⟩ := (isCompact_Icc.prod isCompact_univ).exists_bound_of_continuousOn hV
  let P : ℝ := max P₀ 0
  have hVle (s : ℝ) (hs : s ∈ Icc a k) (q : (H.stage first).Carrier) : V (s, q) ≤ P := by
    have h1 := hP₀ (s, q) ⟨hs, mem_univ _⟩
    rw [Real.norm_eq_abs] at h1
    exact (le_abs_self _).trans (h1.trans (le_max_left _ _))
  have hpast : T - k ^ 2 ∈ H.stageDomain first := by
    have hh := hclock k ⟨hak, le_rfl⟩
    cases first using Fin.lastCases with
    | last => simpa only [stageDomain, Fin.lastCases_last, H.stageEndTime_last, Set.mem_Icc] using
        And.intro hh.1 hh.2.le
    | cast i => simpa only [stageDomain, Fin.lastCases_castSucc, H.stageEndTime_castSucc] using hh
  have hsmall : ∀ᶠ w in 𝓝[Icc a k] k, P * (k - w) < ε / 3 := by
    have hc : ContinuousAt (fun w : ℝ => P * (k - w)) k := by fun_prop
    exact (hc.eventually (Iio_mem_nhds (by simpa using (show 0 < ε / 3 by positivity)))).filter_mono
      nhdsWithin_le_nhds
  filter_upwards [hsmall, self_mem_nhdsWithin] with w hw hwak
  intro q L hL
  rcases lt_or_eq_of_le hwak.2 with hwk | rfl
  · have hfloorw (j : H.StageInterval first last) (s : ℝ)
        (hs : s ∈ Ioo (H.regularizedStageStart T 0 j.val) (H.regularizedStageEnd T w j.val))
        (y : (H.stage j.val).Carrier) :=
      hscalar j s ⟨hs.1, hs.2.trans_le
        (H.regularizedStageEnd_monotoneOn T j.val (ha.le.trans hwak.1) hk0.le hwak.2)⟩ y
    obtain ⟨ell, hell, hellbound⟩ := exists_regularizedC1Action_lt_of_regularizedCost_le H
      first last hle T B 0 w hzero hfloorw x q L (ε / 3) (by positivity) hL.le
    have hconst (s : ℝ) :
        H.stageRegularizedLagrangian first T (fun _ => q) s = V (s, q) := by
      have hv : lVelocity (I := ThreeModel) (fun _ : ℝ => q) s = 0 := by
        simp only [lVelocity, mfderiv_const]
        rfl
      simp only [stageRegularizedLagrangian, hv, map_zero, mul_zero, zero_add, V]
    have hcont : ContinuousOn (fun s : ℝ => V (s, q)) (Icc w k) :=
      hV.comp (continuous_id.prodMk continuous_const).continuousOn
        (fun s hs => ⟨⟨hwak.1.trans hs.1, hs.2⟩, mem_univ _⟩)
    have hint : IntervalIntegrable (H.stageRegularizedLagrangian first T (fun _ => q)) volume w k := by
      simpa only [funext hconst] using hcont.intervalIntegrable_of_Icc hwk.le
    have htail : H.stageRegularizedAction first T (fun _ => q) w k ≤ P * (k - w) := by
      have hh := intervalIntegral.integral_mono_on (μ := volume) hwk.le
        (hcont.intervalIntegrable_of_Icc hwk.le) intervalIntegrable_const
        (fun s hs => hVle s ⟨hwak.1.trans hs.1, hs.2⟩ q)
      simpa only [stageRegularizedAction, funext hconst, intervalIntegral.integral_const,
        smul_eq_mul, mul_comm] using hh
    obtain ⟨ell', hell', hell'bound⟩ := H.exists_regularizedC1ActionValues_join_same_stage
      first last hle hwk (show 0 < ε / 3 by positivity) hzero hpast x q q hell
      (fun _ => q) contMDiff_const rfl rfl hint
    rw [H.regularizedCost_eq_regularizedC1Cost first last hle T B 0 k hzero hscalar]
    exact (H.regularizedC1Cost_le_of_competitor first last hle T 0 k B hscalar x q hell').trans
      (WithTop.coe_le_coe.mpr (by linarith only [hell'bound, hellbound, htail, hw]))
  · rw [hL]
    exact WithTop.coe_le_coe.mpr (by linarith only [hε])

private theorem physicalWeightedCost_closed_stage_lsc_and_attainment
    (H : ObservedHistory.{u}) (first last : Fin (H.eventCount + 1)) (hle : first ≤ last)
    (T B Bsharp r A a k : ℝ) (hr : 0 < r) (ha : 0 < a) (hak : a ≤ k)
    (hBsharp : 0 ≤ Bsharp) (hroom : (2 * Bsharp / 3) * k ^ 3 < r)
    (hupper : T ∈ H.stageDomain last)
    (hclock : ∀ w ∈ Icc a k,
      T - w ^ 2 ∈ Ico (H.time first) (H.stageEndTime first))
    (hscalar : ∀ j : H.StageInterval first last,
      ∀ s ∈ Ioo (H.regularizedStageStart T 0 j.val) (H.regularizedStageEnd T k j.val),
      ∀ y : (H.stage j.val).Carrier,
        -B ≤ metricScalarAt (H.stageMetric j.val (T - s ^ 2)) y)
    (hsharp : ∀ j : H.StageInterval first last,
      ∀ s ∈ Ioo (H.regularizedStageStart T 0 j.val) (H.regularizedStageEnd T k j.val),
      ∀ y : (H.stage j.val).Carrier,
        -Bsharp ≤ metricScalarAt (H.stageMetric j.val (T - s ^ 2)) y)
    (x : (H.stage last).Carrier) (O : (H.stage first).Carrier) :
    let Mstage : ℝ → WithTop ℝ := fun w => sInf (Set.range
      (H.physicalWeightedCost first last hle T B r A w x O))
    LowerSemicontinuousWithinAt Mstage (Icc a k) k ∧
    (∀ w ∈ Icc a k, 0 ≤ Mstage w) ∧
    ∃ q : (H.stage first).Carrier,
      Mstage k = H.physicalWeightedCost first last hle T B r A k x O q ∧
      ∀ y : (H.stage first).Carrier,
        H.physicalWeightedCost first last hle T B r A k x O q ≤
          H.physicalWeightedCost first last hle T B r A k x O y := by
  classical
  intro Mstage
  let X := Icc a k × (H.stage first).Carrier
  let cost : X → WithTop ℝ := fun z => H.regularizedCost first last hle T B 0 z.1.val x z.2
  let dist : X → ℝ≥0∞ := fun z =>
    riemannianEDistOf (H.stageMetric first (T - z.1.val ^ 2)) O z.2
  let shift : X → ℝ := fun z => A * (1 - 2 * z.1.val ^ 2 / r ^ 2)
  let arg : X → ℝ := fun z => (dist z).toReal / r - shift z
  let phi := DifferentialGeometry.Analysis.SingularBarrier.value
  let W : X → WithTop ℝ := fun z =>
    H.physicalWeightedCost first last hle T B r A z.1.val x O z.2
  let κ : ℝ := r - (2 * Bsharp / 3) * k ^ 3
  have hκ : 0 < κ := sub_pos.mpr hroom
  have hρ : 0 < 2 * a * κ := by positivity
  have hdist : Continuous dist := by
    have hapos := hclock a ⟨le_rfl, hak⟩
    obtain ⟨G, hG⟩ := H.exists_stage_incomingSlab_metric first (hapos.1.trans_lt hapos.2)
    let J := (RealTimeInterval.closedOpen (H.time first) (H.stageEndTime first) G.lt).carrier
    have hcont := metricTensor_cont_restrict_of_metricFamilySmoothOn
      G.flow.base.metric G.equation.smoothMetric (Subset.refl J)
    have hJ : J.OrdConnected := by
      change (Ico (H.time first) (H.stageEndTime first)).OrdConnected
      exact ordConnected_Ico
    have hd := Geometry.Riemannian.continuousOn_riemannianEDistOf
      G.flow.base.metric hJ hcont (fun _ _ => RiemannianMetricComplete.of_compact _) O
    have hm : Continuous (fun z : X => (T - z.1.val ^ 2, z.2)) :=
      (continuous_const.sub ((continuous_subtype_val.comp continuous_fst).pow 2)).prodMk
        continuous_snd
    have hc := hd.comp_continuous hm (fun z => ⟨hclock z.1.val z.1.property, mem_univ _⟩)
    simpa only [dist, Function.comp_def, hG] using hc
  have htime : Continuous (fun z : X => z.1.val) := continuous_subtype_val.comp continuous_fst
  have hshift : Continuous shift :=
    continuous_const.mul (continuous_const.sub ((continuous_const.mul (htime.pow 2)).div_const _))
  have hcost : LowerSemicontinuous cost := by
    have hzero : T - 0 ^ 2 ∈ H.stageDomain last := by simpa using hupper
    have hrestrict (w : ℝ) (hw : w ∈ Icc a k)
        (j : H.StageInterval first last) (s : ℝ)
        (hs : s ∈ Ioo (H.regularizedStageStart T 0 j.val) (H.regularizedStageEnd T w j.val))
        (y : (H.stage j.val).Carrier) :=
      hscalar j s ⟨hs.1, hs.2.trans_le
        (H.regularizedStageEnd_monotoneOn T j.val (ha.le.trans hw.1)
          (ha.le.trans hak) hw.2)⟩ y
    intro z bound hbound
    by_cases hzk : z.1.val = k
    · cases bound using WithTop.recTopCoe with
      | top => exact False.elim (not_lt_of_ge le_top hbound)
      | coe bound =>
        have hb : (bound : WithTop ℝ) < H.regularizedCost first last hle T B 0 k x z.2 := by
          simpa only [cost, hzk] using hbound
        obtain ⟨ε, hε, hgap⟩ : ∃ ε : ℝ, 0 < ε ∧
            ((bound + 3 * ε : ℝ) : WithTop ℝ) <
              H.regularizedCost first last hle T B 0 k x z.2 := by
          cases hv : H.regularizedCost first last hle T B 0 k x z.2 using WithTop.recTopCoe with
          | top => exact ⟨1, by norm_num, WithTop.coe_lt_top _⟩
          | coe value =>
            have hh : bound < value := WithTop.coe_lt_coe.mp (by simpa only [hv] using hb)
            exact ⟨(value - bound) / 4, by linarith, WithTop.coe_lt_coe.mpr (by linarith)⟩
        have hfixed := H.lowerSemicontinuous_regularizedCost first last hle T B 0 k
          hzero hscalar x z.2 ((bound + 3 * ε : ℝ) : WithTop ℝ) hgap
        have htransfer := eventually_regularizedCost_le_at_closed_larger_clock H first last hle
          T B a k ha hak hupper hclock hscalar x ε hε
        have htimek : Tendsto (fun y : X => y.1.val) (𝓝 z) (𝓝[Icc a k] k) := by
          have hh : Tendsto (fun y : X => y.1.val) (𝓝 z) (𝓝[Icc a k] z.1.val) := by
            apply tendsto_nhdsWithin_iff.mpr
            exact ⟨htime.continuousAt.tendsto, Eventually.of_forall (fun y => y.1.property)⟩
          simpa only [hzk] using hh
        filter_upwards [htimek.eventually htransfer,
          continuous_snd.continuousAt.tendsto.eventually hfixed] with y hytransfer hyfixed
        by_contra hn
        have hle : cost y ≤ (bound : WithTop ℝ) := le_of_not_gt hn
        have hfinite : cost y ≠ ⊤ := ne_top_of_le_ne_top WithTop.coe_ne_top hle
        obtain ⟨L, hL⟩ := WithTop.ne_top_iff_exists.mp hfinite
        have hLbound : L ≤ bound := WithTop.coe_le_coe.mp (hL.trans_le hle)
        have ht := hytransfer y.2 L hL.symm
        exact (not_lt_of_ge (ht.trans (WithTop.coe_le_coe.mpr (by linarith)))) hyfixed
    · have hvk : z.1.val < k := lt_of_le_of_ne z.1.property.2 hzk
      let d : ℝ := (z.1.val + k) / 2
      have hvd : z.1.val < d := by dsimp only [d]; linarith
      have hdk : d < k := by dsimp only [d]; linarith
      have had : a ≤ d := z.1.property.1.trans hvd.le
      have hstrict (w : ℝ) (hw : w ∈ Icc a d) :
          T - w ^ 2 ∈ Ioo (H.time first) (H.stageEndTime first) := by
        have hww : w ∈ Icc a k := ⟨hw.1, hw.2.trans hdk.le⟩
        have hwk : w < k := hw.2.trans_lt hdk
        have hsq := (sq_lt_sq₀ (ha.le.trans hw.1) (ha.le.trans hak)).mpr hwk
        exact ⟨by linarith only [(hclock k ⟨hak, le_rfl⟩).1, hsq], (hclock w hww).2⟩
      have hlocal := H.lowerSemicontinuousOn_regularizedCost_clock_past_endpoint
        first last hle T B a d ha had hupper hstrict
        (hrestrict d ⟨had, hdk.le⟩) x (z.1.val, z.2) ⟨⟨z.1.property.1, hvd.le⟩, mem_univ _⟩
        bound hbound
      have hm : Tendsto (fun y : X => (y.1.val, y.2)) (𝓝 z)
          (𝓝[Icc a d ×ˢ univ] (z.1.val, z.2)) := by
        apply tendsto_nhdsWithin_iff.mpr
        refine ⟨(htime.prodMk continuous_snd).continuousAt.tendsto, ?_⟩
        filter_upwards [htime.continuousAt.eventually (Iio_mem_nhds hvd)] with y hy
        exact ⟨⟨y.1.property.1, hy.le⟩, mem_univ _⟩
      exact hm.eventually hlocal
  have hcostfloor (z : X) : ((-(2 * Bsharp / 3) * z.1.val ^ 3 : ℝ) : WithTop ℝ) ≤ cost z := by
    have hrestrict (C : ℝ)
        (hC : ∀ j : H.StageInterval first last,
          ∀ s ∈ Ioo (H.regularizedStageStart T 0 j.val) (H.regularizedStageEnd T k j.val),
          ∀ y : (H.stage j.val).Carrier,
            -C ≤ metricScalarAt (H.stageMetric j.val (T - s ^ 2)) y)
        (j : H.StageInterval first last) (s : ℝ)
        (hs : s ∈ Ioo (H.regularizedStageStart T 0 j.val)
          (H.regularizedStageEnd T z.1.val j.val)) (y : (H.stage j.val).Carrier) :
        -C ≤ metricScalarAt (H.stageMetric j.val (T - s ^ 2)) y :=
      hC j s ⟨hs.1, hs.2.trans_le
        (H.regularizedStageEnd_monotoneOn T j.val (ha.le.trans z.1.property.1)
          (ha.le.trans hak) z.1.property.2)⟩ y
    dsimp only [cost]
    rw [H.regularizedCost_congr_scalar_lower_bound first last hle T B Bsharp 0 z.1.val
      (hrestrict B hscalar) (hrestrict Bsharp hsharp) x z.2]
    simpa only [zero_pow (by decide : 3 ≠ 0), sub_zero] using
      H.regularizedCost_ge first last hle T Bsharp 0 z.1.val x z.2
  have hshifted (z : X) (L : ℝ) (hL : cost z = (L : WithTop ℝ)) :
      2 * a * κ ≤ 2 * z.1.val * L + 2 * r * z.1.val := by
    have hl := hcostfloor z
    rw [hL] at hl
    have hl' := WithTop.coe_le_coe.mp hl
    have hcub := mul_le_mul_of_nonneg_left
      (pow_le_pow_left₀ (ha.le.trans z.1.property.1) z.1.property.2 3)
      (by positivity : 0 ≤ 2 * Bsharp / 3)
    have hLr : κ ≤ L + r := by dsimp only [κ]; linarith
    have hh := mul_le_mul hLr z.1.property.1 ha.le (by linarith : 0 ≤ L + r)
    nlinarith
  have hargInside (z : X) (hz : dist z < ENNReal.ofReal (r * (shift z + 1 / 10))) :
      arg z < 1 / 10 := by
    have hd := ENNReal.toReal_lt_of_lt_ofReal hz
    dsimp only [arg]
    apply (sub_lt_iff_lt_add).mpr
    apply (div_lt_iff₀ hr).mpr
    nlinarith
  have hWformula (z : X) (hz : dist z < ENNReal.ofReal (r * (shift z + 1 / 10))) :
      W z = WithTop.map (fun L : ℝ => phi (arg z) *
        (2 * z.1.val * L + 2 * r * z.1.val)) (cost z) := by
    simp only [W, physicalWeightedCost, cost, phi, arg, dist, shift, ite_eq_left hz]
  have hnonneg (z : X) : (0 : WithTop ℝ) ≤ W z := by
    by_cases hz : dist z < ENNReal.ofReal (r * (shift z + 1 / 10))
    · rw [hWformula z hz]
      cases hL : cost z using WithTop.recTopCoe with
      | top => simp only [WithTop.map_top]; exact le_top
      | coe L =>
        have hZ := hshifted z L hL
        have hp := DifferentialGeometry.Analysis.SingularBarrier.pos (hargInside z hz)
        rw [WithTop.map_coe]
        exact WithTop.coe_le_coe.mpr (mul_nonneg hp.le (hρ.le.trans hZ))
    · simp only [W, physicalWeightedCost, dist, shift, ite_eq_right hz]
      exact le_top
  have hcompact (bound : ℝ) : IsCompact {z : X | W z ≤ (bound : WithTop ℝ)} := by
    obtain ⟨θ, hθ, hphiθ⟩ : ∃ θ : ℝ, θ < 1 / 10 ∧ bound / (2 * a * κ) < phi θ := by
      have he := (DifferentialGeometry.Analysis.SingularBarrier.tendsto_at_pole.eventually
        (eventually_gt_atTop (bound / (2 * a * κ)))).and self_mem_nhdsWithin
      obtain ⟨θ, hp, hθ⟩ := he.exists
      exact ⟨θ, hθ, hp⟩
    let Rθ : X → ℝ := fun z => r * (shift z + θ)
    let K : Set X := {z | 0 ≤ Rθ z ∧ dist z ≤ ENNReal.ofReal (Rθ z)}
    have hRθ : Continuous Rθ := continuous_const.mul (hshift.add continuous_const)
    have hKclosed : IsClosed K :=
      (isClosed_le continuous_const hRθ).inter (isClosed_le hdist (ENNReal.continuous_ofReal.comp hRθ))
    have hKcompact : IsCompact K := hKclosed.isCompact
    have hcapture (z : X) (hz : W z ≤ (bound : WithTop ℝ)) : z ∈ K := by
      have hinside : dist z < ENNReal.ofReal (r * (shift z + 1 / 10)) := by
        by_contra hnot
        have htop : W z = ⊤ := by
          simp only [W, physicalWeightedCost, dist, shift, ite_eq_right hnot]
        exact WithTop.not_top_le_coe bound (htop ▸ hz)
      have harg := hargInside z hinside
      have hfinite : cost z ≠ ⊤ := by
        intro htop
        rw [hWformula z hinside, htop, WithTop.map_top] at hz
        exact WithTop.not_top_le_coe bound hz
      obtain ⟨L, hL⟩ := WithTop.ne_top_iff_exists.mp hfinite
      have hreal : phi (arg z) * (2 * z.1.val * L + 2 * r * z.1.val) ≤ bound := by
        rw [hWformula z hinside, ← hL, WithTop.map_coe] at hz
        exact WithTop.coe_le_coe.mp hz
      have hZ := hshifted z L hL.symm
      have hargθ : arg z < θ := by
        by_contra hnot
        have hp := DifferentialGeometry.Analysis.SingularBarrier.monotoneOn hθ harg
          (le_of_not_gt hnot)
        have hp0 := DifferentialGeometry.Analysis.SingularBarrier.pos harg
        have hlow := mul_le_mul_of_nonneg_left hZ hp0.le
        have hmul := mul_le_mul_of_nonneg_right hp hρ.le
        have hstrict := (div_lt_iff₀ hρ).mp hphiθ
        nlinarith
      have hrealDist : (dist z).toReal < Rθ z := by
        have hh := (div_lt_iff₀ hr).mp ((sub_lt_iff_lt_add).mp hargθ)
        dsimp only [arg, Rθ] at hh ⊢
        nlinarith
      have hRpos : 0 < Rθ z := (ENNReal.toReal_nonneg).trans_lt hrealDist
      exact ⟨hRpos.le, (ENNReal.lt_ofReal_iff_toReal_lt
        (ne_top_of_le_ne_top ENNReal.ofReal_ne_top hinside.le)).mpr hrealDist |>.le⟩
    have hKarg (z : K) : arg z.val ≤ θ := by
      have hd := ENNReal.toReal_le_of_le_ofReal z.property.1 z.property.2
      dsimp only [arg]
      apply (sub_le_iff_le_add).mpr
      apply (div_le_iff₀ hr).mpr
      dsimp only [Rθ] at hd
      nlinarith
    have hKinside (z : K) : dist z.val < ENNReal.ofReal (r * (shift z.val + 1 / 10)) := by
      have hRlt : Rθ z.val < r * (shift z.val + 1 / 10) := by
        dsimp only [Rθ]
        nlinarith
      have hRpos : 0 < r * (shift z.val + 1 / 10) := z.property.1.trans_lt hRlt
      exact z.property.2.trans_lt ((ENNReal.ofReal_lt_ofReal_iff hRpos).mpr hRlt)
    have hKdist : Continuous (fun z : K => (dist z.val).toReal) := by
      apply continuous_iff_continuousAt.mpr
      intro z
      exact ContinuousAt.comp (g := ENNReal.toReal) (f := fun z : K => dist z.val) (x := z)
        (ENNReal.continuousAt_toReal
          (ne_top_of_le_ne_top ENNReal.ofReal_ne_top z.property.2))
        (hdist.comp continuous_subtype_val).continuousAt
    have hKphi : Continuous (fun z : K => phi (arg z.val)) :=
      DifferentialGeometry.Analysis.SingularBarrier.contDiffOn.continuousOn.comp_continuous
        ((hKdist.div_const r).sub (hshift.comp continuous_subtype_val))
        (fun z => (hKarg z).trans_lt hθ)
    have hKtime : Continuous (fun z : K => z.val.1.val) := htime.comp continuous_subtype_val
    have hKlsc : LowerSemicontinuous (fun z : K => W z.val) := by
      have hh := lowerSemicontinuous_variable_positive_affine_map
        (fun z : K => cost z.val) (hcost.comp continuous_subtype_val)
        (fun z : K => phi (arg z.val) * (2 * z.val.1.val))
        (fun z : K => phi (arg z.val) * (2 * r * z.val.1.val))
        (hKphi.mul (continuous_const.mul hKtime))
        (hKphi.mul (continuous_const.mul hKtime))
        (fun z => mul_pos (DifferentialGeometry.Analysis.SingularBarrier.pos
          ((hKarg z).trans_lt hθ)) (mul_pos (by norm_num) (ha.trans_le z.val.1.property.1)))
      convert hh using 1
      funext z
      rw [hWformula z.val (hKinside z)]
      congr 1
      funext L
      ring
    have hclosed : IsClosed {z : K | W z.val ≤ (bound : WithTop ℝ)} :=
      lowerSemicontinuous_iff_isClosed_preimage.mp hKlsc _
    let : CompactSpace K := isCompact_iff_compactSpace.mp hKcompact
    have himg := hclosed.isCompact.image continuous_subtype_val
    convert himg using 1
    ext z
    constructor
    · intro hz
      exact ⟨⟨z, hcapture z hz⟩, hz, rfl⟩
    · rintro ⟨z, hz, rfl⟩
      exact hz
  have hWlsc : LowerSemicontinuous W := by
    rw [lowerSemicontinuous_iff_isClosed_preimage]
    intro bound
    cases bound using WithTop.recTopCoe with
    | top => simpa only [Iic_top, preimage_univ] using isClosed_univ
    | coe bound => exact (hcompact bound).isClosed
  have hrange (w : Icc a k) : (range (fun y => W (w, y))).Nonempty :=
    ⟨_, mem_range_self O⟩
  have hbdd (w : Icc a k) : BddBelow (range (fun y => W (w, y))) :=
    ⟨0, by rintro _ ⟨y, rfl⟩; exact hnonneg (w, y)⟩
  have hmin (w : Icc a k) : ∃ y : (H.stage first).Carrier,
      Mstage w.val = W (w, y) ∧ ∀ z, W (w, y) ≤ W (w, z) := by
    have hl := hWlsc.comp (continuous_const.prodMk continuous_id :
      Continuous (fun y : (H.stage first).Carrier => (w, y)))
    obtain ⟨y, _, hy⟩ := LowerSemicontinuousOn.exists_isMinOn
      ⟨O, mem_univ O⟩ isCompact_univ (hl.lowerSemicontinuousOn univ)
    refine ⟨y, le_antisymm (csInf_le (hbdd w) (mem_range_self y)) ?_,
      fun z => hy (mem_univ z)⟩
    apply le_csInf (hrange w)
    rintro _ ⟨z, rfl⟩
    exact hy (mem_univ z)
  have hMlsc : LowerSemicontinuous (fun w : Icc a k => Mstage w.val) := by
    rw [lowerSemicontinuous_iff_isClosed_preimage]
    intro bound
    cases bound using WithTop.recTopCoe with
    | top => simpa only [Iic_top, preimage_univ] using isClosed_univ
    | coe bound =>
      have hp := (hcompact bound).image (continuous_fst : Continuous (Prod.fst : X → Icc a k))
      convert hp.isClosed using 1
      ext w
      constructor
      · intro hw
        obtain ⟨y, hy, _⟩ := hmin w
        exact ⟨(w, y), le_trans hy.symm.le hw, rfl⟩
      · rintro ⟨⟨w, y⟩, hy, rfl⟩
        exact (csInf_le (hbdd w) (mem_range_self y)).trans hy
  refine ⟨(lowerSemicontinuous_restrict_iff.mp hMlsc) k ⟨hak, le_rfl⟩, ?_,
    hmin ⟨k, hak, le_rfl⟩⟩
  intro w hw
  apply le_csInf (hrange ⟨w, hw⟩)
  rintro _ ⟨y, rfl⟩
  exact hnonneg (⟨w, hw⟩, y)

theorem exists_closed_event_traced_weighted_minimum_of_preceding_stage_bound
    (H : ObservedHistory.{u}) (parameters : CutoffParameters)
    (records : ∀ j : Fin H.eventCount, GeometricCutoffRecord H j parameters)
    (a₀ : ℝ) (ha₀ : 0 < a₀)
    (hfixed : ∀ y, InFixedHamiltonIveyRegion (H.initialMetric 0) a₀ y)
    (hscalar : ∀ y, -3 / a₀ ≤ metricScalarAt (H.initialMetric 0) y)
    (t : Icc (0 : ℝ) H.horizon) (p x : (H.stageAt t).Carrier)
    (r A D a k : ℝ) (hr : 0 < r) (ha : 0 < a) (hak : a < k)
    (hhalf : k ^ 2 ≤ r ^ 2 / 2) (hT : 2 * r ^ 2 < t.val)
    (aSeed : Icc (0 : ℝ) H.horizon) (hSeedTime : aSeed ≤ t)
    (hSeedClock : (aSeed : ℝ) = t.val - r ^ 2)
    (seedTrace : BackwardPointTrace H (H.activeStage aSeed) (H.activeStage t)
      (H.activeStage_mono hSeedTime) p)
    (i : Fin H.eventCount) (hl : i.succ ≤ H.activeStage t)
    (hevent : t.val - k ^ 2 = H.time i.succ)
    (hentry : t.val - a ^ 2 < H.stageEndTime i.succ)
    (upper : ℝ → ℝ) (hupper : ContinuousAt upper k)
    (hbudget : upper k ≤ 2 * r * k * D)
    (hpreceding : ∀ w ∈ Ico a k,
      H.tracedPhysicalWeightedMinimum aSeed t hSeedTime p x seedTrace (3 / a₀) r A w ≤
        ((upper w : ℝ) : WithTop ℝ)) :
    let M := H.tracedPhysicalWeightedMinimum aSeed t hSeedTime p x seedTrace (3 / a₀) r A
    ∃ hfSeed : H.activeStage aSeed ≤ i.succ,
    let O := seedTrace.point i.succ hfSeed hl
    ∃ (q : (H.stage i.succ).Carrier) (L m : ℝ),
      M k = (m : WithTop ℝ) ∧
      H.physicalWeightedCost i.succ (H.activeStage t) hl t.val (3 / a₀) r A k x O q =
        (m : WithTop ℝ) ∧
      (∀ y : (H.stage i.succ).Carrier,
        H.physicalWeightedCost i.succ (H.activeStage t) hl t.val (3 / a₀) r A k x O q ≤
          H.physicalWeightedCost i.succ (H.activeStage t) hl t.val (3 / a₀) r A k x O y) ∧
      H.regularizedCost i.succ (H.activeStage t) hl t.val (3 / a₀) 0 k x q =
        (L : WithTop ℝ) ∧
      riemannianEDistOf (H.stageMetric i.succ (t.val - k ^ 2)) O q <
        ENNReal.ofReal (r * (A * (1 - 2 * k ^ 2 / r ^ 2) + 1 / 10)) ∧
      r / 4 ≤ L + r ∧ 0 < m ∧ m ≤ upper k ∧ m ≤ 2 * r * k * D ∧
      L ≤ (D - 1) * r ∧
      H.regularizedCost i.succ (H.activeStage t) hl t.val (3 / a₀) 0 k x q <
        ((D * r : ℝ) : WithTop ℝ) := by
  classical
  intro M
  let T : ℝ := t.val
  let first := i.succ
  let last := H.activeStage t
  have hk : 0 < k := ha.trans hak
  have hr2 : 0 < r ^ 2 := sq_pos_of_pos hr
  have hT0 : 0 < T := by dsimp only [T]; nlinarith only [hT, hr2]
  have hclock (w : ℝ) (hw : w ∈ Icc a k) :
      T - w ^ 2 ∈ Ico (H.time first) (H.stageEndTime first) := by
    have hwa := pow_le_pow_left₀ ha.le hw.1 2
    have hwk := pow_le_pow_left₀ (ha.le.trans hw.1) hw.2 2
    constructor <;> dsimp only [T, first] <;> linarith only [hevent, hentry, hwa, hwk]
  have hpast (w : ℝ) (hw : w ∈ Icc a k) : T - w ^ 2 ∈ H.stageDomain first := by
    have hh := hclock w hw
    generalize first = j at hh ⊢
    cases j using Fin.lastCases with
    | last => simpa only [stageDomain, Fin.lastCases_last, H.stageEndTime_last, Set.mem_Icc] using
        And.intro hh.1 hh.2.le
    | cast j => simpa only [stageDomain, Fin.lastCases_castSucc, H.stageEndTime_castSucc] using hh
  have hhalfClock (w : ℝ) (hw : w ∈ Icc a k) : w ^ 2 ≤ r ^ 2 / 2 :=
    (pow_le_pow_left₀ (ha.le.trans hw.1) hw.2 2).trans hhalf
  have hseedFirst : H.activeStage aSeed ≤ first := by
    let ak : Icc (0 : ℝ) H.horizon := ⟨T - k ^ 2, H.stageDomain_subset first (hpast k ⟨hak.le, le_rfl⟩)⟩
    have hseedAk : aSeed ≤ ak := by
      change (aSeed : ℝ) ≤ T - k ^ 2
      rw [hSeedClock]
      dsimp only [T]
      nlinarith only [hhalf, hr2]
    have hstage : H.activeStage ak = first := (H.mem_stageDomain_iff ak first).mp (hpast k ⟨hak.le, le_rfl⟩)
    simpa only [hstage] using H.activeStage_mono hseedAk
  let O := seedTrace.point first hseedFirst hl
  let Mstage : ℝ → WithTop ℝ := fun w => sInf (Set.range
    (H.physicalWeightedCost first last hl T (3 / a₀) r A w x O))
  have hMstage (w : ℝ) (hw : w ∈ Icc a k) : M w = Mstage w := by
    let aw : Icc (0 : ℝ) H.horizon := ⟨T - w ^ 2, H.stageDomain_subset first (hpast w hw)⟩
    have hawt : aw ≤ t := sub_le_self t.val (sq_nonneg w)
    have hsw : (aSeed : ℝ) ≤ t.val - w ^ 2 := by
      rw [hSeedClock]
      nlinarith only [hhalfClock w hw, hr2]
    have hawseed : aSeed ≤ aw := hsw
    have hstage : H.activeStage aw = first := (H.mem_stageDomain_iff aw first).mp (hpast w hw)
    have hwhole (j : Fin (H.eventCount + 1))
        (hjs : H.activeStage aSeed ≤ j) (hjl : j ≤ last) (hj : j = first) :
        sInf (Set.range (H.physicalWeightedCost j last hjl T (3 / a₀) r A w x
          (seedTrace.point j hjs hjl))) = Mstage w := by
      subst j
      rfl
    dsimp only [M, tracedPhysicalWeightedMinimum]
    rw [dite_eq_left hsw]
    exact hwhole (H.activeStage aw) (H.activeStage_mono hawseed) (H.activeStage_mono hawt) hstage
  let Bsharp : ℝ := 3 / (a₀ + T / 2)
  have hden : 0 < a₀ + T / 2 := by positivity
  have hBsharp : 0 < Bsharp := by dsimp only [Bsharp]; positivity
  have hBr : Bsharp * r ^ 2 < 3 := by
    dsimp only [Bsharp]
    rw [div_mul_eq_mul_div]
    apply (div_lt_iff₀ hden).mpr
    dsimp only [T]
    nlinarith only [hT, ha₀]
  have hklt : k < r := by nlinarith only [hhalf, hr, hk]
  have hroom : (2 * Bsharp / 3) * k ^ 3 < r := by
    have hh := mul_le_mul_of_nonneg_left hhalf (by positivity : 0 ≤ 2 * Bsharp / 3)
    have hcoef : (2 * Bsharp / 3) * k ^ 2 < 1 := by nlinarith only [hh, hBr]
    have hm := mul_lt_mul_of_pos_right hcoef hk
    nlinarith only [hm, hklt]
  have hHI := (H.fixedHamiltonIveyRegion_and_scalar_lower records ha₀ hfixed hscalar).1
  have hfloors (j : H.StageInterval first last) (s : ℝ)
      (hs : s ∈ Ioo (H.regularizedStageStart T 0 j.val) (H.regularizedStageEnd T k j.val))
      (y : (H.stage j.val).Carrier) :
      -(3 / a₀) ≤ metricScalarAt (H.stageMetric j.val (T - s ^ 2)) y ∧
        -Bsharp ≤ metricScalarAt (H.stageMetric j.val (T - s ^ 2)) y := by
    have hs0 : 0 ≤ s := (Real.sqrt_nonneg _).trans hs.1.le
    have hend : H.regularizedStageEnd T k j.val ≤ k := by
      have hh : T - max (T - k ^ 2) (H.time j.val) ≤ k ^ 2 := by
        have hm := le_max_left (T - k ^ 2) (H.time j.val)
        linarith
      exact (Real.sqrt_le_sqrt hh).trans_eq (Real.sqrt_sq hk.le)
    have hsk : s ^ 2 ≤ k ^ 2 := pow_le_pow_left₀ hs0 (hs.2.le.trans hend) 2
    have hrecent : T / 2 ≤ T - s ^ 2 := by dsimp only [T] at *; nlinarith only [hT, hhalf, hsk]
    have htime0 : 0 ≤ T - s ^ 2 := by linarith only [hrecent, hT0]
    have htimeDen : 0 < a₀ + (T - s ^ 2) := by linarith only [ha₀, htime0]
    have hR := (hHI j.val (T - s ^ 2) (H.mapsTo_regularizedStage_Ioo T 0 k j.val hs) y).2
    have hglobal : 3 / (a₀ + (T - s ^ 2)) ≤ 3 / a₀ := by
      apply (div_le_div_iff₀ htimeDen ha₀).mpr
      linarith only [htime0]
    have hnear : 3 / (a₀ + (T - s ^ 2)) ≤ Bsharp := by
      change 3 / (a₀ + (T - s ^ 2)) ≤ 3 / (a₀ + T / 2)
      apply (div_le_div_iff₀ htimeDen hden).mpr
      linarith only [hrecent]
    constructor
    · exact (show -(3 / a₀) ≤ -3 / (a₀ + (T - s ^ 2)) by
        simpa only [neg_div] using neg_le_neg hglobal).trans hR
    · exact (show -Bsharp ≤ -3 / (a₀ + (T - s ^ 2)) by
        simpa only [neg_div] using neg_le_neg hnear).trans hR
  obtain ⟨hLsc, _, q, hmin, hqmin⟩ := physicalWeightedCost_closed_stage_lsc_and_attainment H
    first last hl T (3 / a₀) Bsharp r A a k hr ha hak.le hBsharp.le hroom
    (H.activeStage_mem t) hclock (fun j s hs y => (hfloors j s hs y).1)
    (fun j s hs y => (hfloors j s hs y).2) x O
  have hclosedBound : Mstage k ≤ ((upper k : ℝ) : WithTop ℝ) := by
    by_contra hn
    have hgt : ((upper k : ℝ) : WithTop ℝ) < Mstage k := lt_of_not_ge hn
    obtain ⟨ε, hε, hgap⟩ : ∃ ε : ℝ, 0 < ε ∧
        ((upper k + ε : ℝ) : WithTop ℝ) < Mstage k := by
      cases hv : Mstage k using WithTop.recTopCoe with
      | top => exact ⟨1, by norm_num, WithTop.coe_lt_top _⟩
      | coe value =>
        have hh : upper k < value := WithTop.coe_lt_coe.mp (by simpa only [hv] using hgt)
        exact ⟨(value - upper k) / 2, by linarith, WithTop.coe_lt_coe.mpr (by linarith)⟩
    have hleft : 𝓝[<] k ≤ 𝓝[Icc a k] k :=
      le_inf nhdsWithin_le_nhds (le_principal_iff.mpr (Icc_mem_nhdsLT hak))
    have hlower := (hLsc _ hgap).filter_mono hleft
    have hupp := (hupper.eventually (Iio_mem_nhds (by linarith : upper k < upper k + ε))).filter_mono
      (show 𝓝[<] k ≤ 𝓝 k from nhdsWithin_le_nhds)
    have hfalse : ∀ᶠ w in 𝓝[<] k, False := by
      filter_upwards [hlower, hupp, Icc_mem_nhdsLT hak, self_mem_nhdsWithin] with w hwlow hwup hwak hwk
      have hwbound := hpreceding w ⟨hwak.1, hwk⟩
      have hMw : H.tracedPhysicalWeightedMinimum aSeed t hSeedTime p x seedTrace (3 / a₀) r A w =
          Mstage w := hMstage w hwak
      rw [hMw] at hwbound
      exact (not_lt_of_ge (hwbound.trans (WithTop.coe_le_coe.mpr hwup.le))) hwlow
    exact hfalse.exists.elim (fun _ h => h)
  have hfinite : Mstage k ≠ ⊤ := ne_top_of_le_ne_top WithTop.coe_ne_top hclosedBound
  obtain ⟨m, hm⟩ := WithTop.ne_top_iff_exists.mp hfinite
  have hWm : H.physicalWeightedCost first last hl T (3 / a₀) r A k x O q = (m : WithTop ℝ) :=
    hmin.symm.trans hm.symm
  have hmupper : m ≤ upper k := WithTop.coe_le_coe.mp (hm.trans_le hclosedBound)
  have hmbudget : m ≤ 2 * r * k * D := hmupper.trans hbudget
  have hlow := H.regularizedCost_ge_recent_half_time_of_cutoff_records records ha₀ hfixed hscalar
    first last hl hr hk.le hhalf hT x q
  have hcube : 2 * k ^ 3 / r ^ 2 ≤ k := by
    apply (div_le_iff₀ hr2).mpr
    have hh := mul_le_mul_of_nonneg_right hhalf hk.le
    nlinarith only [hh]
  have hkr : k ≤ 3 * r / 4 := by
    apply (sq_le_sq₀ hk.le (by positivity : 0 ≤ 3 * r / 4)).mp
    nlinarith only [hhalf, hr2]
  have hmargin (L : ℝ)
      (hL : H.regularizedCost first last hl T (3 / a₀) 0 k x q = (L : WithTop ℝ)) :
      r / 4 ≤ L + r := by
    have hh : -2 * k ^ 3 / r ^ 2 ≤ L := WithTop.coe_le_coe.mp (hlow.trans_eq hL)
    have hneg : -2 * k ^ 3 / r ^ 2 = -(2 * k ^ 3 / r ^ 2) := by ring
    linarith only [hh, hcube, hkr, hneg]
  have hbootstrap : H.physicalWeightedCost first last hl T (3 / a₀) r A k x O q ≤
      ((2 * r * k * D : ℝ) : WithTop ℝ) := hWm.trans_le (WithTop.coe_le_coe.mpr hmbudget)
  obtain ⟨hinside, L, hL, hLbound, hLstrict⟩ :=
    H.regularizedCost_lt_action_budget_of_weighted_bootstrap first last hl T (3 / a₀) r A k D
      x O q hr hk (fun L hL => (by positivity : 0 < r / 4).trans_le (hmargin L hL)) hbootstrap
  have harg : (riemannianEDistOf (H.stageMetric first (T - k ^ 2)) O q).toReal / r -
      A * (1 - 2 * k ^ 2 / r ^ 2) < 1 / 10 := by
    have hd := ENNReal.toReal_lt_of_lt_ofReal hinside
    apply (sub_lt_iff_lt_add).mpr
    apply (div_lt_iff₀ hr).mpr
    nlinarith only [hd]
  have hmpos : 0 < m := by
    have hp := DifferentialGeometry.Analysis.SingularBarrier.pos harg
    have hfactor : 0 < 2 * k * L + 2 * r * k := by
      have hh := mul_pos (mul_pos (by norm_num : (0 : ℝ) < 2) hk)
        ((by positivity : 0 < r / 4).trans_le (hmargin L hL))
      nlinarith only [hh]
    have heq : DifferentialGeometry.Analysis.SingularBarrier.value
        ((riemannianEDistOf (H.stageMetric first (T - k ^ 2)) O q).toReal / r -
          A * (1 - 2 * k ^ 2 / r ^ 2)) * (2 * k * L + 2 * r * k) = m := by
      apply WithTop.coe_injective
      simpa only [physicalWeightedCost, ite_eq_left hinside, hL, WithTop.map_coe] using hWm
    exact heq ▸ mul_pos hp hfactor
  exact ⟨hseedFirst, q, L, m, (hMstage k ⟨hak.le, le_rfl⟩).trans hm.symm,
    hWm, hqmin, hL, hinside, hmargin L hL, hmpos, hmupper, hmbudget, hLbound, hLstrict⟩

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory
