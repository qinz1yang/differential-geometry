import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.NeckWideBandNK2
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.IncomingSliceBandNK
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.CanonicalCapWindows
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.StandardCap.InitialWindowBounds
import DifferentialGeometry.Geometry.Curvature.Metric.Scaling
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.P6NativeSepStaticC11SP

/-!
# O-CH11-NATIVE-SEP G2：`hSEP` chart-reach 的尺度匹配 M3（后缀 `_C11SP`，无 binder）

在 `T(e₁⁺)`（stage `e₁.succ`，度量 = `e₁` 的 output metric）比较同一点
`p₁ = (G₂.backward α).stageChart ⟨e₁+1⟩ w = window(e₁,b) x` 处的标量曲率两侧：

* neck 侧：`metric_on_slab`（`j = e₁+1`，时刻 `T(e₂⁺) + r²v₁ = T(e₁⁺)`，`v₁ ∈ [−1/2, 0)`）+
  `IncomingBackwardNeck.band_cyl_NK`（`R ≥ 3/5`，`δ ≤ 1/40000`）+ `chart_band_estimates_wide_NK2`（转运到
  `range` 上）+ `metricScalarAt_scaleMetric` ⇒ `R_{g₁}(p₁) ≥ (3/5)·r₂⁻²`；
* `e₁` 侧：`hasCanonicalWindow` 的 canonical witness +
  `exists_uniform_window_image_scalar_bound_of_scaled_pullback` ⇒ `|R_{g₁}(window x)| ≤ C·q₁`
  （`C` 绝对常数，`‖x‖ < modelRadius`）。

结论 `exists_scale_match_C11SP`：`3/5 ≤ C·(q₁·r₂²)`，即 `r₂²q₁ ≥ 3/(5C)`——M2（neck band 出口长度
`≥ r₂(δ₂⁻¹ − h₀)/√2`）与 M4（window 内 `x → tip` 长度 `≤ C′(D)/√q₁`）比较时需要的方向。
-/

set_option autoImplicit false

noncomputable section

open Set Manifold DifferentialGeometry.Geometry.Curvature
open scoped Manifold ContDiff Topology

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

universe u

namespace GeometricCutoffRecord

/-- **M3（PROVED）尺度匹配**：`e₂` 的 backward neck（record neck `α`，nominal radius `r₂`）在 stage
`e₁.succ` 的 chart 点 `w`（`|w.1.2| ≤ δ₂⁻¹`）若等于 `e₁` 的 static cap window 点 `x`（`‖x‖ < modelRadius`），且
`0 < T(e₂⁺) − T(e₁⁺) ≤ r₂²/2`、`δ₂ ≤ 1/40000`，则 `3/5 ≤ C·(q₁·r₂²)`（`C` 绝对常数）。 -/
theorem exists_scale_match_C11SP :
    ∃ C : ℝ, 0 < C ∧
    ∀ {H : ObservedHistory.{u}} {parameters : CutoffParameters} {e₁ e₂ : Fin H.eventCount}
      (G₁ : GeometricCutoffRecord H e₁ parameters) (G₂ : GeometricCutoffRecord H e₂ parameters)
      (b : (H.event e₁).RetainedBoundaryIndex) (α : (H.event e₂).transition.trace.tubes.Index),
      (G₁.static b).hasCanonicalWindow → parameters.modelAccuracy ≤ 1 / 2 →
      2 ≤ parameters.modelOrder → G₂.delta α ≤ 1 / 40000 →
      ∀ (hji : e₁.val < e₂.val), H.time e₁.succ < H.time e₂.succ →
        H.time e₂.succ - H.time e₁.succ ≤ (G₂.nominalRadius ⟨α⟩) ^ 2 / 2 →
      ∀ (hn : H.time e₂.succ - (G₂.nominalRadius ⟨α⟩) ^ 2 <
          H.time (⟨e₁.val + 1, by omega⟩ : Fin H.eventCount).succ)
        (w : neckBuffer (G₂.delta α)), |w.1.2| ≤ (G₂.delta α)⁻¹ →
      ∀ x : standardCapWindow parameters.modelRadius, ‖x.val‖ < parameters.modelRadius →
        (G₂.backward α).stageChart ⟨e₁.val + 1, by omega⟩
            (by change e₁.val + 1 ≤ e₂.val; omega) hn w = (G₁.static b).window x →
        3 / 5 ≤ C * ((G₁.static b).neck.scale * (G₂.nominalRadius ⟨α⟩) ^ 2) := by
  obtain ⟨C, hC, hbound⟩ := StandardCap.exists_uniform_window_image_scalar_bound_of_scaled_pullback
  refine ⟨C, hC, ?_⟩
  intro H parameters e₁ e₂ G₁ G₂ b α hcan hε hm hδ hji hlt hT hn w hw x hx hpx
  set r := G₂.nominalRadius ⟨α⟩ with hrdef
  have hr2 : 0 < r ^ 2 := pow_pos (G₂.nominal_pos ⟨α⟩) 2
  set B := G₂.backward α with hBdef
  let nx : Fin H.eventCount := ⟨e₁.val + 1, by omega⟩
  have hnx : nx.val ≤ e₂.val := by
    change e₁.val + 1 ≤ e₂.val
    omega
  set v : ℝ := (H.time e₁.succ - H.time e₂.succ) / r ^ 2 with hvdef
  have hv0 : v < 0 := div_neg_of_neg_of_pos (by linarith) hr2
  have hvhalf : -1 / 2 ≤ v := by
    rw [hvdef, le_div_iff₀ hr2]
    linarith
  have hsv : H.time e₂.succ + r ^ 2 * v = H.time e₁.succ := by
    have : r ^ 2 * v = H.time e₁.succ - H.time e₂.succ := by
      rw [hvdef, mul_div_assoc']
      exact mul_div_cancel_left₀ _ hr2.ne'
    linarith
  have hstart : H.time nx.castSucc ≤ H.time e₂.succ + r ^ 2 * v := by
    rw [hsv]
    exact le_rfl
  have hend : H.time e₂.succ + r ^ 2 * v < H.time nx.succ := by
    rw [hsv]
    exact H.time_strictMono (Fin.castSucc_lt_succ (i := nx))
  have hslab := B.metric_on_slab nx hnx hn v ⟨by linarith, hv0⟩ hstart hend
  let gs := (H.event nx).incoming.flow.base.metric (H.time e₁.succ)
  let gm := scaleMetric (r ^ 2)⁻¹ (inv_pos.mpr hr2) gs
  have hband := chart_band_estimates_wide_NK2 (B.stageChart_smooth nx hnx hn) gm (B.metric v)
    (a := 3 / 5) (C := 2) (T := Icc (-(G₂.delta α)⁻¹) (G₂.delta α)⁻¹) (by
      intro z V W
      change _ = (scaleMetric _ _ _).inner _ _ _
      rw [scaleMetric_inner, hslab z V W, hsv])
    (fun z hz => (B.band_cyl_NK (G₂.two_le_order_NK α) hδ v ⟨hvhalf, hv0.le⟩ z hz).1)
    (fun z hz => (B.band_cyl_NK (G₂.two_le_order_NK α) hδ v ⟨hvhalf, hv0.le⟩ z hz).2)
  have hheight : chartHeight_NK (B.stageChart nx hnx hn) (B.stageChart nx hnx hn w) =
      w.1.2 := chartHeight_chart_NK (B.stageChart_smooth nx hnx hn).isEmbedding.injective w
  have hR := hband.1 _ ⟨w, rfl⟩ (by rw [hheight]; exact abs_le.mp hw)
  rw [DifferentialGeometry.Geometry.Curvature.metricScalarAt_scaleMetric, inv_inv] at hR
  have hgs : gs = (H.event e₁).outputMetric := by
    change (H.event nx).incoming.flow.base.metric (H.time nx.castSucc) = _
    rw [H.event_initial nx, H.event_output e₁]
    rfl
  obtain ⟨x₀, δ₀, k₀, d, wc, -, hmetric, -⟩ := hcan
  have : Fact (Module.finrank ℝ ThreeSpace = 3) := ⟨by simp⟩
  have hwin := hbound wc hε hm (H.event e₁).outputMetric (G₁.static b).window
    (G₁.static b).window_smooth (G₁.static b).neck.scale (G₁.static b).neck.scale_pos hmetric
    x hx
  have hRout : metricScalarAt gs (B.stageChart nx hnx hn w) ≤ C * (G₁.static b).neck.scale := by
    rw [hgs]
    change metricScalarAt (H.event e₁).outputMetric ((G₂.backward α).stageChart ⟨e₁.val + 1, by
      omega⟩ (by change e₁.val + 1 ≤ e₂.val; omega) hn w) ≤ _
    rw [hpx]
    exact (abs_le.mp hwin).2
  nlinarith [mul_le_mul_of_nonneg_left hRout hr2.le]

end GeometricCutoffRecord

/-- **consumer（G1 → G2）**：`hSEP` 语境下 G1 `sep_static_C11SP` 给出的 chart 点 `w`（高度
`≤ 1 + (static δ₂)⁻¹ ≤ δ₂⁻¹`，用 `recenter_delta`、`Rc ≥ 4`、`δ₂ ≤ 1/40000`）喂 M3，得 `3/5 ≤ C·q₁·r₂²`。 -/
example {H : ObservedHistory.{u}} {parameters : CutoffParameters} {e₁ e₂ : Fin H.eventCount}
    (hl : e₁.succ ≤ e₂.castSucc)
    (G₁ : GeometricCutoffRecord H e₁ parameters) (G₂ : GeometricCutoffRecord H e₂ parameters)
    {y : (H.stage e₂.castSucc).Carrier} (A : BackwardPointTrace H e₁.succ e₂.castSucc hl y)
    (b : (H.event e₁).RetainedBoundaryIndex) (x : standardCapWindow parameters.modelRadius)
    (hxD : ‖x.val‖ < parameters.modelRadius)
    (hanchor : A.point e₁.succ le_rfl hl = (G₁.static b).window x)
    (hx0 : (0 : ThreeSpace) ∈ standardCapWindow parameters.modelRadius)
    {y₂ : (H.stage e₂.succ).Carrier} (hcross : (H.event e₂).RegularCrossing y y₂)
    (b₂ : (H.event e₂).RetainedBoundaryIndex) (z₂ : standardCapWindow parameters.modelRadius)
    (heq : (G₂.static b₂).window z₂ = y₂)
    (hcan : (G₁.static b).hasCanonicalWindow) (hε : parameters.modelAccuracy ≤ 1 / 2)
    (hm : 2 ≤ parameters.modelOrder) (hδ : G₂.delta b₂.1.1 ≤ 1 / 40000)
    (hlt : H.time e₁.succ < H.time e₂.succ)
    (hhalf : H.time e₂.succ - H.time e₁.succ ≤ (G₂.nominalRadius ⟨b₂.1.1⟩) ^ 2 / 2) :
    ∃ C : ℝ, 0 < C ∧
      3 / 5 ≤ C * ((G₁.static b).neck.scale * (G₂.nominalRadius ⟨b₂.1.1⟩) ^ 2) := by
  obtain ⟨C, hC, hM3⟩ := GeometricCutoffRecord.exists_scale_match_C11SP.{u}
  have hr : 0 < G₂.nominalRadius ⟨b₂.1.1⟩ := G₂.nominal_pos ⟨b₂.1.1⟩
  have hT : H.time e₂.succ - (G₂.nominalRadius ⟨b₂.1.1⟩) ^ 2 < H.time e₁.succ := by
    nlinarith [pow_pos hr 2]
  obtain ⟨hji, hn, w, hw, hpx, -⟩ :=
    G₁.sep_static_C11SP hl G₂ A b x hanchor hx0 hcross b₂ z₂ heq hT
  have hδpos := G₂.delta_pos b₂.1.1
  have h4 : ((G₂.static b₂).delta)⁻¹ ≤ (4 * G₂.delta b₂.1.1)⁻¹ := by
    rw [G₂.recenter_delta b₂]
    exact inv_anti₀ (by positivity) (by nlinarith [parameters.recenterConstant_ge_four])
  have h4' : (4 * G₂.delta b₂.1.1)⁻¹ = (G₂.delta b₂.1.1)⁻¹ / 4 := by
    rw [mul_inv]
    ring
  have hbig : 40000 ≤ (G₂.delta b₂.1.1)⁻¹ := by
    rw [le_inv_comm₀ (by norm_num) hδpos]
    linarith
  have hw' : |w.1.2| ≤ (G₂.delta b₂.1.1)⁻¹ := by
    linarith
  exact ⟨C, hC, hM3 G₁ G₂ b b₂.1.1 hcan hε hm hδ hji hlt hhalf hn w hw' x hxD hpx⟩

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
