import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.External.RSupplyLowerC12X
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.NeckBandEstimatesNK

set_option autoImplicit false

/-!
# `hlook` 的树内 no-go（O-C12X-RSUP G2，后缀 `_C12X`）

design：`docs/geometrization/chapter8/out/CH12X-RSUPPLY-design.md` §2。

**Lemma B**（`exists_output_scalar_ge_of_record_C12X`）：带 `GeometricCutoffRecord` 的事件、
任一保留边界 `b`、精度 `δ_b ≤ 1/8646` ⇒ 手术后度量（`H.initialMetric i.succ`）上存在点 `q` 使
`R(q) ≥ nominal⁻²/2`。取点：静态 neck 的保留领口点 `(ω, 1/2)`（原 neck 坐标 `z = ±3/2`），
`old` 节点；它不在任何 cap 里（`core_cap_intersection`：cap 只在 `z = ±1` 的边界球上碰 core），
故 `regularCrossing_or_cap_of_admissible_node` 给 `RegularCrossing`，`RegularCrossing.scalar_eq`
把手术后标量换成 terminal 标量；后者由 `NormalizedNeck.scalar_lower_NK`（`k ≥ 2`、
`δ ≤ 1/8646`）与 `scale = nominal⁻²` 给出。

**tower 形**（`recent_surgery_ratio_C12X`）：块 `j+1` 的末事件在新块内（时间 `> b_j`）且有保留
边界、`j + 2 ≥ 8646` ⇒ `(j+2)²·rad_{j+2}² < 2·rad_{j+1}²`（`rad_{j+2} = ℓ_{j+1}.rNext`）。来源：
`recent_records`（`nominal ≤ rad_{j+1}/(j+2)`）、精度 `δ ≤ d_j ≤ 1/(j+2)`、Lemma B、
restart datum = 块 `j+1` 末 stage（`AffineEventPrefix`），G1 的引理 A
（`restart_scalar_lt_rNext_C12X`）。

**no-go**：`eventually_no_recent_surgery_of_hlook_C12X`（hlook ⇒ 某 `N` 之后每个块 `j+1`
的末事件若在新块内则无保留边界）与 `not_hlook_of_frequently_recent_surgery_C12X`（对无穷多个
`j`，块 `j+1` 的末事件在新块内且有保留边界 ⇒ `¬ hlook`，hlook 与
`nrDoubling_of_lookahead_C11ND` 的前提逐字同形）。
-/

noncomputable section

open Set Filter DifferentialGeometry DifferentialGeometry.Geometry.Curvature
open GC.GeneralFlow
open scoped NNReal

/-! ## Lemma B：手术后度量上的标量下界 -/

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

universe u

/-- **Lemma B**：手术后度量上存在点 `q`，`R(q) ≥ nominal⁻²/2`。 -/
theorem exists_output_scalar_ge_of_record_C12X {H : ObservedHistory.{u}} {i : Fin H.eventCount}
    {p : CutoffParameters} (R : GeometricCutoffRecord H i p)
    (b : (H.event i).RetainedBoundaryIndex) (hδ : R.delta b.1.1 ≤ 1 / 8646) :
    ∃ q : (H.stage i.succ).Carrier,
      ((R.nominalRadius ⟨b.1.1⟩) ^ 2)⁻¹ / 2 ≤ metricScalarAt (H.initialMetric i.succ) q := by
  classical
  obtain ⟨ω⟩ : Nonempty (Sphere 2) := ⟨⟨EuclideanSpace.single 0 1, by simp⟩⟩
  have hSδ : (R.static b).delta < 1 := (R.static b).neck.delta_lt_one
  have hSδpos : 0 < (R.static b).delta := (R.static b).neck.delta_pos
  have hSinv : 1 < (R.static b).delta⁻¹ := (one_lt_inv₀ hSδpos).mpr hSδ
  obtain ⟨x0, hx0def⟩ : ∃ x0 : neckRetainedCollar (R.static b).delta, x0.val = (ω, 1 / 2) :=
    ⟨⟨(ω, 1 / 2), by norm_num, by linarith⟩, rfl⟩
  have hx02 : x0.val.2 = 1 / 2 := by rw [hx0def]
  have hx0 : x0.val ∈ neckBuffer (R.static b).delta := by
    refine ⟨?_, ?_⟩
    · rw [hx02]
      linarith
    · rw [hx02]
      linarith
  have hold := R.old_eq_retained
  let z : (H.event i).old := ⟨((R.static b).retainedPoint x0).1,
    hold.symm ▸ ((R.static b).retainedPoint x0).2⟩
  have hterm : (H.event i).oldTerminal z = (R.static b).neck.chart ⟨x0.val, hx0⟩ := by
    apply Subtype.ext
    rw [(H.event i).oldTerminal_eq]
    exact (R.static b).retained_point_eq x0 hx0
  have hin := R.recenter_in_buffer b ⟨x0.val, hx0⟩
  have hchart := R.recenter_chart b ⟨x0.val, hx0⟩ hin
  have hs2 : (if b.1.2 then (1 : ℝ) else -1) * (1 + x0.val.2) ∈ Icc (-2 : ℝ) 2 := by
    rw [hx02]
    split_ifs <;> constructor <;> norm_num
  let w : TubeDomain := (x0.val.1, ⟨(if b.1.2 then (1 : ℝ) else -1) * (1 + x0.val.2), hs2⟩)
  have htube := R.tube_eq b.1.1 w hin
  rcases MetricCutCapEvent.regularCrossing_or_cap_of_admissible_node (H.event i) hold
      (p := z.val.val) (q := (H.event i).oldOutput z) ⟨z, rfl, rfl⟩ with hcross | ⟨b', z', hz'⟩
  · have hcross' : (H.event i).RegularCrossing ((H.event i).oldTerminal z).val
        ((H.event i).oldOutput z) := by
      rw [(H.event i).oldTerminal_eq z]
      exact hcross
    have heq := MetricCutCapEvent.RegularCrossing.scalar_eq (H.event i) hcross'
    refine ⟨(H.event i).oldOutput z, ?_⟩
    have hδpos := (R.neck b.1.1).delta_pos
    have hδinv : (8646 : ℝ) ≤ (R.delta b.1.1)⁻¹ := by
      have h := inv_anti₀ hδpos hδ
      norm_num at h
      exact h
    have hcl : (⟨_, hin⟩ : neckBuffer (R.delta b.1.1)) ∈ neckClosedTest (R.delta b.1.1) := by
      change -(R.delta b.1.1)⁻¹ ≤ (if b.1.2 then (1 : ℝ) else -1) * (1 + x0.val.2) ∧
        (if b.1.2 then (1 : ℝ) else -1) * (1 + x0.val.2) ≤ (R.delta b.1.1)⁻¹
      rw [hx02]
      split_ifs <;> constructor <;> linarith
    have hord : 2 ≤ R.order b.1.1 := by
      have h := (le_max_left _ _).trans (R.order_lower b.1.1)
      omega
    have hlow := (R.neck b.1.1).scalar_lower_NK hord hδ hcl
    have hchartNK := (R.neck b.1.1).metricScalarAt_chart_NK ⟨_, hin⟩
    have hscale := DifferentialGeometry.Geometry.Curvature.metricScalarAt_scaleMetric
      (R.neck b.1.1).scale (R.neck b.1.1).scale_pos (H.event i).terminal.metric
      ((R.neck b.1.1).chart ⟨_, hin⟩)
    have hN := (R.neck b.1.1).scale_pos
    have hmain : 1 / 2 ≤ (R.neck b.1.1).scale⁻¹ *
        metricScalarAt (H.event i).terminal.metric ((R.neck b.1.1).chart ⟨_, hin⟩) := by
      rw [← hscale, hchartNK]
      exact hlow
    have key : (R.neck b.1.1).scale / 2 ≤
        metricScalarAt (H.event i).terminal.metric ((R.neck b.1.1).chart ⟨_, hin⟩) := by
      have h := mul_le_mul_of_nonneg_left hmain hN.le
      rwa [mul_inv_cancel_left₀ hN.ne', mul_one_div] at h
    rw [R.scale_eq b.1.1] at key
    have hout : metricScalarAt (H.initialMetric i.succ) ((H.event i).oldOutput z) =
        metricScalarAt (H.event i).terminal.metric ((R.neck b.1.1).chart ⟨_, hin⟩) := by
      rw [← H.event_output i, ← heq, hterm, hchart]
    rw [hout]
    exact key
  · exfalso
    have h1 : (H.event i).transition.trace.capping.cap b'.val z' =
        (H.event i).transition.trace.capping.coreInclusion z.1 :=
      (H.event i).transition.trace.presentation.injective
        (hz'.trans ((H.event i).oldOutput_eq z).symm)
    have h3 : (H.event i).transition.trace.capping.coreInclusion z.1 ∈
        Set.range (H.event i).transition.trace.capping.coreInclusion ∩
          Set.range ((H.event i).transition.trace.capping.cap b'.val) :=
      ⟨⟨z.1, rfl⟩, ⟨z', h1⟩⟩
    rw [(H.event i).transition.trace.capping.core_cap_intersection b'.val] at h3
    obtain ⟨y, hy⟩ := h3
    have h4 := (H.event i).transition.trace.capping.coreEmbedding.injective hy
    have h5 : (H.event i).transition.trace.tubes.tube b'.val.1
        (y, TubeSystem.boundaryLevel b'.val.2) =
          (H.event i).transition.trace.tubes.tube b.1.1 w :=
      (congrArg Subtype.val h4).trans (((H.event i).oldTerminal_eq z).symm.trans
        ((congrArg Subtype.val hterm).trans ((congrArg Subtype.val hchart).trans htube.symm)))
    by_cases hα : b'.val.1 = b.1.1
    · rw [hα] at h5
      have h6 := ((H.event i).transition.trace.tubes.embedding b.1.1).injective h5
      have h7 : ((TubeSystem.boundaryLevel b'.val.2 : Icc (-2 : ℝ) 2) : ℝ) =
          (if b.1.2 then (1 : ℝ) else -1) * (1 + x0.val.2) :=
        congrArg (fun v : TubeDomain => (v.2 : ℝ)) h6
      rw [hx02] at h7
      rcases Bool.eq_false_or_eq_true b'.val.2 with hb' | hb' <;>
        rcases Bool.eq_false_or_eq_true b.1.2 with hb | hb <;>
        simp only [hb', hb, TubeSystem.boundaryLevel] at h7 <;> norm_num at h7
    · exact Set.disjoint_left.mp ((H.event i).transition.trace.tubes.disjoint hα)
        ⟨_, rfl⟩ ⟨w, h5.symm⟩

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

/-! ## tower 形与 no-go -/

namespace GC.LongTime.Ch11

open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

universe u

variable {pBase : CutoffParameters} {C : ClosedBirthConstants}
  {P : OrientedThreeStage.{u}} {g : P.Metric}

/-- 纯实数：`0 < n ≤ r/J`、`nominal⁻²/2 < ρ⁻²` ⇒ `J²ρ² < 2r²`。 -/
theorem ratio_of_scalar_bounds_C12X {n r ρ J : ℝ} (hn : 0 < n) (hρ : 0 < ρ) (hJ : 0 < J)
    (hnr : n ≤ 1 / J * r) (hsc : (n ^ 2)⁻¹ / 2 < (ρ ^ 2)⁻¹) : J ^ 2 * ρ ^ 2 < 2 * r ^ 2 := by
  have hn2 : 0 < 2 * n ^ 2 := by positivity
  have hρ2 : 0 < ρ ^ 2 := by positivity
  have h1 : (2 * n ^ 2)⁻¹ < (ρ ^ 2)⁻¹ := by
    rw [mul_inv, mul_comm]
    simpa only [div_eq_mul_inv] using hsc
  have h2 : ρ ^ 2 < 2 * n ^ 2 := (inv_lt_inv₀ hn2 hρ2).mp h1
  have h3 : n * J ≤ r := by
    have := (le_div_iff₀ hJ).mp (by simpa only [one_div, inv_mul_eq_div] using hnr)
    linarith
  have h4 : (n * J) ^ 2 ≤ r ^ 2 := pow_le_pow_left₀ (by positivity) h3 2
  have hJ2 : 0 < J ^ 2 := by positivity
  calc J ^ 2 * ρ ^ 2 < J ^ 2 * (2 * n ^ 2) := mul_lt_mul_of_pos_left h2 hJ2
    _ = 2 * (n * J) ^ 2 := by ring
    _ ≤ 2 * r ^ 2 := by linarith

/-- 纯实数：比值界与 `r ≤ C'ρ` 在 `J > 2C'²`、`J ≥ 1` 时矛盾。 -/
theorem false_of_ratio_and_look_C12X {J ρ r C' : ℝ} (hρ : 0 < ρ) (hr : 0 < r) (hJ1 : 1 ≤ J)
    (hJC : 2 * C' ^ 2 < J) (hratio : J ^ 2 * ρ ^ 2 < 2 * r ^ 2) (hlook : r ≤ C' * ρ) :
    False := by
  have h1 : r ^ 2 ≤ (C' * ρ) ^ 2 := pow_le_pow_left₀ hr.le hlook 2
  have hρ2 : 0 < ρ ^ 2 := by positivity
  have h2 : J ^ 2 * ρ ^ 2 < (2 * C' ^ 2) * ρ ^ 2 := by
    calc J ^ 2 * ρ ^ 2 < 2 * r ^ 2 := hratio
      _ ≤ 2 * (C' * ρ) ^ 2 := by linarith
      _ = (2 * C' ^ 2) * ρ ^ 2 := by ring
  have h3 : J ^ 2 < 2 * C' ^ 2 := lt_of_mul_lt_mul_right h2 hρ2.le
  nlinarith

/-- 末 stage 对齐：`AffineEventPrefix` 到 `Fin.last` 时，两段历史的末 stage 与初始度量一致。 -/
theorem affine_last_stage_C12X {K J : RetainedCoreHistory.{u}} {c : ℝ} {offset : ℕ}
    (A : AffineEventPrefix K J c offset (Fin.last K.eventCount)) :
    J.stage (Fin.last J.eventCount) = K.stage (Fin.last K.eventCount) ∧
      HEq (J.initialMetric (Fin.last J.eventCount)) (K.initialMetric (Fin.last K.eventCount)) := by
  have hcount : J.eventCount = offset + K.eventCount := A.count_eq
  have key : ∀ a : Fin (J.eventCount + 1), a.val = J.eventCount →
      J.stage a = J.stage (Fin.last J.eventCount) ∧
        HEq (J.initialMetric a) (J.initialMetric (Fin.last J.eventCount)) := by
    intro a ha
    obtain rfl : a = Fin.last J.eventCount := Fin.ext ha
    exact ⟨rfl, HEq.rfl⟩
  obtain ⟨h1, h2⟩ := key ⟨offset + K.eventCount, by omega⟩ hcount.symm
  exact ⟨h1.symm.trans (A.stage_eq (Fin.last K.eventCount)),
    h2.symm.trans (A.initialMetric_heq (Fin.last K.eventCount))⟩

/-- 标量下界沿 stage 等式 + 度量 HEq 运输。 -/
theorem exists_scalar_ge_transport_C12X {A B : OrientedThreeStage.{u}} (hAB : A = B)
    {gA : A.Metric} {gB : B.Metric} (hg : HEq gA gB) {c : ℝ}
    (h : ∃ y : A.Carrier, c ≤ metricScalarAt gA y) : ∃ y : B.Carrier, c ≤ metricScalarAt gB y := by
  subst hAB
  obtain rfl := eq_of_heq hg
  exact h

/-- 标量下界沿 stage 下标等式运输。 -/
theorem exists_scalar_ge_index_C12X {H : ObservedHistory.{u}} {a b : Fin (H.eventCount + 1)}
    (hab : a = b) {c : ℝ}
    (h : ∃ y : (H.stage a).Carrier, c ≤ metricScalarAt (H.initialMetric a) y) :
    ∃ y : (H.stage b).Carrier, c ≤ metricScalarAt (H.initialMetric b) y := by
  subst hab
  exact h

/-- **tower 形**：块 `j+1` 的末事件在新块内且有保留边界、`j + 2 ≥ 8646` ⇒
`(j+2)²·rNext_{j+1}² < 2·rad_{j+1}²`（`rNext_{j+1} = rad_{j+2}`）。 -/
theorem recent_surgery_ratio_C12X {Cdist : ℝ≥0} {cMax Dstar εReserve : ℝ}
    (T : BlockTower_C11W pBase C P g Cdist cMax Dstar εReserve) {j : ℕ}
    (hj : (8646 : ℝ) ≤ (j : ℝ) + 2) (i : Fin (T.block (j + 1)).history.eventCount)
    (hlast : i.succ = Fin.last (T.block (j + 1)).history.eventCount)
    (hrecent : preparedSpatialHorizon j < (T.block (j + 1)).history.time i.succ)
    (b : ((T.block (j + 1)).history.toHistory.event i).RetainedBoundaryIndex) :
    ((j : ℝ) + 2) ^ 2 * (T.lookahead (j + 1)).rNext ^ 2 < 2 * (T.block (j + 1)).radius ^ 2 := by
  have hext := T.extension j
  have hsucc := hext.successor
  have hJ : (0 : ℝ) < (j : ℝ) + 2 := by positivity
  have hδ : ((T.block (j + 1)).records i).delta b.1.1 ≤ 1 / 8646 := by
    have h5 : 1 / ((j : ℝ) + 2) ≤ 1 / 8646 := one_div_le_one_div_of_le (by norm_num) hj
    calc ((T.block (j + 1)).records i).delta b.1.1
        ≤ (T.block (j + 1)).parameters.delta ((T.block (j + 1)).history.time i.succ) :=
          ((T.block (j + 1)).records i).delta_le b.1.1
      _ = T.accuracy j := hsucc.delta_after _ hrecent
      _ ≤ (T.request j).accuracyCap := hext.accuracy_le_cap
      _ ≤ 1 / ((j : ℝ) + 2) := (T.ready j).request.cap_le_level
      _ ≤ 1 / 8646 := h5
  have hnom : ((T.block (j + 1)).records i).nominalRadius ⟨b.1.1⟩ ≤
      1 / ((j : ℝ) + 2) * (T.block (j + 1)).radius :=
    hsucc.recent_records i hrecent ⟨b.1.1⟩
  have hnpos : 0 < ((T.block (j + 1)).records i).nominalRadius ⟨b.1.1⟩ :=
    ((T.block (j + 1)).records i).nominal_pos _
  have hB := exists_output_scalar_ge_of_record_C12X ((T.block (j + 1)).records i) b hδ
  have hB' := exists_scalar_ge_index_C12X hlast hB
  obtain ⟨hst, hmet⟩ := affine_last_stage_C12X (T.block (j + 1)).affine
  obtain ⟨y, hy⟩ := exists_scalar_ge_transport_C12X hst hmet hB'
  have hA := restart_scalar_lt_rNext_C12X (T.ready (j + 1)).lookahead y
  exact ratio_of_scalar_bounds_C12X hnpos (T.ready (j + 1)).lookahead.rNext_pos hJ hnom
    (hy.trans_lt hA)

/-- **no-go（全称形）**：hlook ⇒ 存在 `N`，对一切 `j ≥ N`，块 `j+1` 的末事件若在新块内
（时间 `> b_j`），则该事件没有保留边界（不是带 cap 的手术）。 -/
theorem eventually_no_recent_surgery_of_hlook_C12X {Cdist : ℝ≥0} {cMax Dstar εReserve : ℝ}
    (T : BlockTower_C11W pBase C P g Cdist cMax Dstar εReserve)
    (hlook : ∃ C' : ℝ, ∃ k₀ : ℕ, ∀ j : ℕ, k₀ ≤ j →
      (T.block j).radius ≤ C' * (T.lookahead j).rNext) :
    ∃ N : ℕ, ∀ j : ℕ, N ≤ j → ∀ i : Fin (T.block (j + 1)).history.eventCount,
      i.succ = Fin.last (T.block (j + 1)).history.eventCount →
      preparedSpatialHorizon j < (T.block (j + 1)).history.time i.succ →
      IsEmpty ((T.block (j + 1)).history.toHistory.event i).RetainedBoundaryIndex := by
  obtain ⟨C', k₀, hC⟩ := hlook
  refine ⟨k₀ + 8646 + ⌈2 * C' ^ 2⌉₊, fun j hNj i hlast hrec => ⟨fun b => ?_⟩⟩
  have hjR : ((k₀ + 8646 + ⌈2 * C' ^ 2⌉₊ : ℕ) : ℝ) ≤ (j : ℝ) := by exact_mod_cast hNj
  push_cast at hjR
  have hceil : 2 * C' ^ 2 ≤ (⌈2 * C' ^ 2⌉₊ : ℝ) := Nat.le_ceil _
  have hk : (0 : ℝ) ≤ (k₀ : ℝ) := Nat.cast_nonneg k₀
  have hj : (8646 : ℝ) ≤ (j : ℝ) + 2 := by linarith
  have hratio := recent_surgery_ratio_C12X T hj i hlast hrec b
  exact false_of_ratio_and_look_C12X (T.ready (j + 1)).lookahead.rNext_pos
    (T.block (j + 1)).radius_pos (by linarith) (by linarith) hratio (hC (j + 1) (by omega))

/-- **no-go（存在形）**：对无穷多个 `j`，块 `j+1` 的末事件在新块内且有保留边界 ⇒ `¬ hlook`
（hlook 与 `nrDoubling_of_lookahead_C11ND` 的前提逐字同形）。 -/
theorem not_hlook_of_frequently_recent_surgery_C12X {Cdist : ℝ≥0} {cMax Dstar εReserve : ℝ}
    (T : BlockTower_C11W pBase C P g Cdist cMax Dstar εReserve)
    (hfreq : ∀ N : ℕ, ∃ j : ℕ, N ≤ j ∧ ∃ i : Fin (T.block (j + 1)).history.eventCount,
      i.succ = Fin.last (T.block (j + 1)).history.eventCount ∧
      preparedSpatialHorizon j < (T.block (j + 1)).history.time i.succ ∧
      Nonempty ((T.block (j + 1)).history.toHistory.event i).RetainedBoundaryIndex) :
    ¬ ∃ C' : ℝ, ∃ k₀ : ℕ, ∀ j : ℕ, k₀ ≤ j →
      (T.block j).radius ≤ C' * (T.lookahead j).rNext := by
  intro hlook
  obtain ⟨N, hN⟩ := eventually_no_recent_surgery_of_hlook_C12X T hlook
  obtain ⟨j, hNj, i, hlast, hrec, ⟨b⟩⟩ := hfreq N
  exact (hN j hNj i hlast hrec).false b

end GC.LongTime.Ch11
