import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.P6TerminalComparisonP6ST3
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.CrossModelBallCapture
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.HornSeparationSliceTransfer
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.TerminalMetricCompactComparison

/-!
# S-c `hcen`：seed 距离沿 crossing 的左半连续（O-CH11-STAB4 G4，后缀 `_P6ST4`）

HREST2 binder `hcen`：crossing `o⁻ ↦ o⁺`（seed trace）、`p' ↦ y`（坏点）时，`t = v n → s⁻`
eventually `d_{g(t)}(o⁻, p') ≤ d_{g⁺}(o⁺, y) + η`。本文件证明（`eventually_seedDist_le_P6ST4` / 序列版
`seedDist_seq_le_P6ST4`）：在**种子 terminal footprint**
`B̄_ḡ(o⁻, r)` 紧、`val '' B̄_ḡ(o⁻, r) ⊆ interior (val '' old)`、`17(d⁺ + 1) < 16r`
（`d⁺ := d_{g⁺}(o⁺, y)`）之下成立，0 其它 binder。证明：survivor `F : Ω ⇢ Q`（`F*g⁺ = ḡ`，`F o⁻ = o⁺`）+ 树内相对二次界
`exists_compact_relative_quad_bound`（`g(t)|Ω ≤ (1−ε)⁻¹ ḡ` 于 footprint）+ `16/17` 球包含
（`eventually_riemannianBallOf_subset_image_closedBall`，把 `g(t)|Ω` 闭球压进 footprint）+ ball capture
`ball_subset_image_closedBall_of_metric_lower`（`B_{g⁺}(o⁺, R/L) ⊆ F '' B̄_{g(t)|Ω}(o⁻, R)`）+
crossing 左唯一（`F z = y ⇒ z = p'`）+ `restrictOpen` 距离不减。
footprint 本身（种子到坏点之间不碰 cut tube / cap 区）不是本文件的结论：见 DELIVERIES G4 块 repair target。
-/

set_option autoImplicit false

noncomputable section

open Set Filter TopologicalSpace
open DifferentialGeometry DifferentialGeometry.Geometry.Curvature
open scoped Manifold ContDiff Topology

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

universe u

namespace MetricCutCapEvent

variable {P Q : OrientedThreeStage.{u}} {a s : ℝ}

/-- 数值：`ε := min (1/2) (η'/(2(d+1)))` 时 `√((1−ε)⁻¹)·d < d + η'`。 -/
theorem seed_eps_real_P6ST4 {d η' : ℝ} (hd0 : 0 ≤ d) (hη' : 0 < η') :
    Real.sqrt ((1 - min (1 / 2) (η' / (2 * (d + 1))))⁻¹) * d < d + η' := by
  set ε := min (1 / 2) (η' / (2 * (d + 1))) with hεdef
  have hε0 : 0 < ε := lt_min (by norm_num) (by positivity)
  have hε1 : ε ≤ 1 / 2 := min_le_left _ _
  have hε2 : ε ≤ η' / (2 * (d + 1)) := min_le_right _ _
  have hL : Real.sqrt ((1 - ε)⁻¹) ≤ 1 + ε := by
    rw [Real.sqrt_le_left (by linarith), inv_le_iff_one_le_mul₀ (by linarith)]
    have h1 : 0 ≤ 1 - ε - ε ^ 2 := by nlinarith
    nlinarith [mul_nonneg hε0.le h1]
  have hεd : ε * d < η' := by
    have h1 : ε * d ≤ η' / (2 * (d + 1)) * d := mul_le_mul_of_nonneg_right hε2 hd0
    have h2 : η' / (2 * (d + 1)) * d < η' := by
      rw [div_mul_eq_mul_div, div_lt_iff₀ (by positivity)]
      nlinarith
    linarith
  calc Real.sqrt ((1 - ε)⁻¹) * d ≤ (1 + ε) * d := mul_le_mul_of_nonneg_right hL hd0
    _ < d + η' := by nlinarith

/-- **`hcen`（t 层）**：种子 terminal footprint ⇒ `t → s⁻` eventually
`d_{g(t)}(o⁻, p') ≤ d_{g⁺}(o⁺, y) + η`。 -/
theorem eventually_seedDist_le_P6ST4 (E : MetricCutCapEvent P Q a s) {o p' : P.Carrier}
    {o' y : Q.Carrier} (hco : E.RegularCrossing o o') (hcp : E.RegularCrossing p' y) {r d : ℝ}
    (hd0 : 0 ≤ d) (hd : riemannianEDistOf (I := ThreeModel) E.outputMetric o' y = ENNReal.ofReal d)
    (hr : 17 * (d + 1) < 16 * r)
    (hK : IsCompact (riemannianClosedBallOf (I := ThreeModel) E.terminal.metric
      ⟨o, hco.mem_terminalRegularRegion E⟩ r))
    (hKold : Subtype.val '' riemannianClosedBallOf (I := ThreeModel) E.terminal.metric
      ⟨o, hco.mem_terminalRegularRegion E⟩ r ⊆ interior (Subtype.val '' E.old))
    {η : ℝ} (hη : 0 < η) :
    ∀ᶠ t in 𝓝[<] s, riemannianEDistOf (I := ThreeModel) (E.incoming.flow.base.metric t) o p' ≤
      riemannianEDistOf (I := ThreeModel) E.outputMetric o' y + ENNReal.ofReal η := by
  have : SigmaCompactSpace E.incoming.terminalRegularOpen :=
    isSigmaCompact_iff_sigmaCompactSpace.mp
      (DifferentialGeometry.Geometry.isSigmaCompact_of_isOpen ThreeModel
        E.incoming.terminalRegularOpen.isOpen)
  have ho : o ∈ E.incoming.terminalRegularOpen := hco.mem_terminalRegularRegion E
  obtain ⟨F, hFsrc, -, hFo, -, hcrossF, hmetric⟩ :=
    RegularCrossing.exists_survivor_partialDiffeomorph E (p := ⟨o, ho⟩) hco
  set K := riemannianClosedBallOf (I := ThreeModel) E.terminal.metric ⟨o, ho⟩ r with hKdef
  have hKF : K ⊆ F.source := by
    intro z hz
    rw [hFsrc]
    exact hKold ⟨z, hz, rfl⟩
  have hr0 : 0 < r := by linarith
  set η' := min η (1 / 2) with hη'def
  have hη'0 : 0 < η' := lt_min hη (by norm_num)
  set ε := min (1 / 2) (η' / (2 * (d + 1))) with hεdef
  have hε0 : 0 < ε := lt_min (by norm_num) (by positivity)
  have hε1 : ε ≤ 1 / 2 := min_le_left _ _
  set L := Real.sqrt ((1 - ε)⁻¹) with hLdef
  have hL0 : 0 < L := Real.sqrt_pos.mpr (inv_pos.mpr (by linarith))
  have hL2 : L ^ 2 = (1 - ε)⁻¹ := Real.sq_sqrt (inv_nonneg.mpr (by linarith))
  have hLd : L * d < d + η' := seed_eps_real_P6ST4 hd0 hη'0
  obtain ⟨t0, ht0, hq⟩ := E.terminal.exists_compact_relative_quad_bound hK hε0
  filter_upwards [Ioo_mem_nhdsLT ht0.2,
    E.terminal.eventually_riemannianBallOf_subset_image_closedBall ⟨o, ho⟩ hr0 hK] with t ht hsub
  set R2 := d + η' with hR2def
  have hR2 : 0 < R2 := by positivity
  have hR2r : R2 < 16 * r / 17 := by
    have : η' ≤ 1 / 2 := min_le_right _ _
    linarith
  -- `g(t)|Ω` 闭球 ⊆ footprint
  have hballK : riemannianClosedBallOf (I := ThreeModel)
      ((E.incoming.flow.base.metric t).restrictOpen E.incoming.terminalRegularOpen)
      ⟨o, ho⟩ R2 ⊆ K := by
    intro z hz
    have h1 := riemannianEDistOf_le_restrictOpen (E.incoming.flow.base.metric t)
      E.incoming.terminalRegularOpen ⟨o, ho⟩ z
    have hzb : z.val ∈ riemannianBallOf (I := ThreeModel) (E.incoming.flow.base.metric t) o
        (16 * r / 17) := by
      change riemannianEDistOf (I := ThreeModel) (E.incoming.flow.base.metric t) o z.val < _
      exact lt_of_le_of_lt (h1.trans hz) ((ENNReal.ofReal_lt_ofReal_iff (by positivity)).mpr hR2r)
    obtain ⟨w, hw, hwz⟩ := hsub hzb
    have hwz' : w = z := Subtype.ext hwz
    exact hwz' ▸ hw
  have hcpt : IsCompact (riemannianClosedBallOf (I := ThreeModel)
      ((E.incoming.flow.base.metric t).restrictOpen E.incoming.terminalRegularOpen)
      ⟨o, ho⟩ R2) :=
    hK.of_isClosed_subset (Geometry.Metric.isClosed_riemannianClosedBallOf _ _ _) hballK
  have hlower : ∀ z ∈ riemannianClosedBallOf (I := ThreeModel)
      ((E.incoming.flow.base.metric t).restrictOpen E.incoming.terminalRegularOpen) ⟨o, ho⟩ R2,
      ∀ v : TangentSpace ThreeModel z,
        ((E.incoming.flow.base.metric t).restrictOpen E.incoming.terminalRegularOpen).inner z v v ≤
          L ^ 2 * E.outputMetric.inner (F z) (mfderiv ThreeModel ThreeModel (F : _ → _) z v)
            (mfderiv ThreeModel ThreeModel (F : _ → _) z v) := by
    intro z hz v
    have hzK := hballK hz
    rw [hmetric z (hKF hzK) v v, hL2]
    have hb := (abs_le.mp (hq t ht z hzK v)).2
    rw [← div_eq_inv_mul, le_div_iff₀ (by linarith)]
    linarith
  have hcap := DifferentialGeometry.PartialDiffeomorph.ball_subset_image_closedBall_of_metric_lower
    ((E.incoming.flow.base.metric t).restrictOpen E.incoming.terminalRegularOpen)
    E.outputMetric F ⟨o, ho⟩ hR2 hL0 hcpt (hballK.trans hKF) hlower
  have hy : y ∈ riemannianBallOf (I := ThreeModel) E.outputMetric (F ⟨o, ho⟩) (R2 / L) := by
    change riemannianEDistOf (I := ThreeModel) E.outputMetric (F ⟨o, ho⟩) y <
      ENNReal.ofReal (R2 / L)
    rw [hFo, hd, ENNReal.ofReal_lt_ofReal_iff (by positivity), lt_div_iff₀ hL0]
    linarith
  obtain ⟨z, hz, hzy⟩ := hcap hy
  have hzc : E.RegularCrossing z.val y := hzy ▸ hcrossF z (hKF (hballK hz))
  have hzp : z.val = p' := E.regularCrossing_left_unique hzc hcp
  have h1 := riemannianEDistOf_le_restrictOpen (E.incoming.flow.base.metric t)
    E.incoming.terminalRegularOpen ⟨o, ho⟩ z
  rw [hzp] at h1
  refine (h1.trans hz).trans ?_
  rw [hd, ENNReal.ofReal_add hd0 hη'0.le]
  exact add_le_add le_rfl (ENNReal.ofReal_le_ofReal (min_le_left _ _))

/-- **`hcen`（序列形，合同 `v n` 上）**：`v n ∈ (a, s)`、`v n → s` ⇒ eventually in `n`。 -/
theorem seedDist_seq_le_P6ST4 (E : MetricCutCapEvent P Q a s) {o p' : P.Carrier}
    {o' y : Q.Carrier} (hco : E.RegularCrossing o o') (hcp : E.RegularCrossing p' y) {r d : ℝ}
    (hd0 : 0 ≤ d) (hd : riemannianEDistOf (I := ThreeModel) E.outputMetric o' y = ENNReal.ofReal d)
    (hr : 17 * (d + 1) < 16 * r)
    (hK : IsCompact (riemannianClosedBallOf (I := ThreeModel) E.terminal.metric
      ⟨o, hco.mem_terminalRegularRegion E⟩ r))
    (hKold : Subtype.val '' riemannianClosedBallOf (I := ThreeModel) E.terminal.metric
      ⟨o, hco.mem_terminalRegularRegion E⟩ r ⊆ interior (Subtype.val '' E.old))
    {v : ℕ → ℝ} (hv : ∀ n, v n ∈ Ioo a s) (hvt : Tendsto v atTop (𝓝 s)) {η : ℝ} (hη : 0 < η) :
    ∀ᶠ n in atTop, riemannianEDistOf (I := ThreeModel) (E.incoming.flow.base.metric (v n)) o p' ≤
      riemannianEDistOf (I := ThreeModel) E.outputMetric o' y + ENNReal.ofReal η :=
  (tendsto_nhdsLT_of_slab_P6ST3 hv hvt).eventually
    (E.eventually_seedDist_le_P6ST4 hco hcp hd0 hd hr hK hKold hη)

end MetricCutCapEvent

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
