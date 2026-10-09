import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.FirstExitDistanceP6M4
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.SliceDichotomyFinalP6HF

/-!
# GUARDWIRE-FINAL G1：I.8.3(b) 单 slab 距离畸变的 final-slab 孪生（O-CH11-GUARDWIRE-FINAL，后缀 `_P6GWF`）

GUARDWIRE G2b `hseedG` 的 repair target 第 1 项：P6M4 `ObservedHistory.edist_le_add_of_slab_ricci_P6M4`
（event `e` 的 incoming flow，`time e⁻ < s ≤ t < time e⁺`）→ final slab 形：flow 换成
`(K.finalSlab h).restrictIncoming le_rfl h le_rfl`（`IncomingSlab (time last) horizon`，定义域
`Ico (time last) horizon` 与 event incoming slab 同形），`K.time last < s ≤ t < K.horizon`，点在
`K.stage last`。证明体逐字（`edist_le_add_of_endpoint_ricci_solution_C11D` 对 flow 通用，只换 flow / 时间端点）。

* stageMetric 形的同一结论树内已有（S-CH11-HSCALU2 `edist_le_add_of_final_ricci_P6M6`，闭端点）；本文件是
  SEEDCL2 stopped 核所需的 **restrictIncoming 形**（GUARDWIRE G2b 合同 / `hRn` 的 flow 形），两者经
  `RetainedCoreHistory.stageMetric_last_restrict_P6HF` 互转
  （`edist_le_add_of_final_ricci_stage_P6GWF`）。
* 无新数学、无 binder；只 import P6M4 + P6HF stage 桥。
-/

set_option autoImplicit false

noncomputable section

open Set Filter
open DifferentialGeometry.Geometry.Curvature
open scoped Manifold ContDiff Topology ENNReal NNReal

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

universe u

/-- **final slab 内 I.8.3(b)（`_P6GWF`，PROVED）**：P6M4 `edist_le_add_of_slab_ricci_P6M4` 的 final 孪生。
`[s, t] ⊆ (time last, horizon)`、`(s, t)` 上两端 `ℓ`-球 `Ric ≤ (3/ℓ²) g`（restrict final slab 度量）⇒
`d_s(p, q) ≤ d_t(p, q) + (8/ℓ)(t − s)`。证明体逐字（`(H.event e).incoming` → restrict final slab）。 -/
theorem RetainedCoreHistory.edist_le_add_of_final_ricci_P6GWF (K : RetainedCoreHistory.{u})
    (h : K.time (Fin.last K.eventCount) < K.horizon) {s t ℓ : ℝ} (hℓ : 0 < ℓ) (hst : s ≤ t)
    (hs : K.time (Fin.last K.eventCount) < s) (ht : t < K.horizon)
    (p q : (K.stage (Fin.last K.eventCount)).Carrier)
    (hRic : ∀ r ∈ Ioo s t, ∀ z : (K.stage (Fin.last K.eventCount)).Carrier,
      ∀ ξ : TangentSpace ThreeModel z,
      (riemannianEDistOf (((K.finalSlab h).restrictIncoming le_rfl h le_rfl).flow.base.metric r)
          p z < ENNReal.ofReal ℓ ∨
        riemannianEDistOf (((K.finalSlab h).restrictIncoming le_rfl h le_rfl).flow.base.metric r)
          q z < ENNReal.ofReal ℓ) →
      ricciTensor (((K.finalSlab h).restrictIncoming le_rfl h le_rfl).flow.base.metric r) z ξ ξ ≤
        (3 / ℓ ^ 2) *
          (((K.finalSlab h).restrictIncoming le_rfl h le_rfl).flow.base.metric r).inner z ξ ξ) :
    riemannianEDistOf (((K.finalSlab h).restrictIncoming le_rfl h le_rfl).flow.base.metric s) p q ≤
      riemannianEDistOf (((K.finalSlab h).restrictIncoming le_rfl h le_rfl).flow.base.metric t)
          p q +
        ENNReal.ofReal ((8 / ℓ) * (t - s)) :=
  ObservedHistory.edist_le_add_of_endpoint_ricci_solution_C11D
    ((K.finalSlab h).restrictIncoming le_rfl h le_rfl).flow
    ((K.finalSlab h).restrictIncoming le_rfl h le_rfl).equation hst hℓ
    (fun _ hr => ⟨hs.le.trans hr.1, lt_of_le_of_lt hr.2 ht⟩)
    (fun _ hr => ⟨hs.trans hr.1, hr.2.trans ht⟩) p q hRic

/-- **stageMetric 形（`_P6GWF`，PROVED）**：同一结论用 `K.toHistory.stageMetric (Fin.last _)` 写出
（经 `stageMetric_last_restrict_P6HF` 改写到 restrict final slab 形后用上一条）。与 P6M6
`edist_le_add_of_final_ricci_P6M6` 同陈述的开端点版，供 stageMetric 形消费者。 -/
theorem RetainedCoreHistory.edist_le_add_of_final_ricci_stage_P6GWF (K : RetainedCoreHistory.{u})
    (h : K.time (Fin.last K.eventCount) < K.horizon) {s t ℓ : ℝ} (hℓ : 0 < ℓ) (hst : s ≤ t)
    (hs : K.time (Fin.last K.eventCount) < s) (ht : t < K.horizon)
    (p q : (K.stage (Fin.last K.eventCount)).Carrier)
    (hRic : ∀ r ∈ Ioo s t, ∀ z : (K.stage (Fin.last K.eventCount)).Carrier,
      ∀ ξ : TangentSpace ThreeModel z,
      (riemannianEDistOf (K.toHistory.stageMetric (Fin.last K.eventCount) r) p z <
          ENNReal.ofReal ℓ ∨
        riemannianEDistOf (K.toHistory.stageMetric (Fin.last K.eventCount) r) q z <
          ENNReal.ofReal ℓ) →
      ricciTensor (K.toHistory.stageMetric (Fin.last K.eventCount) r) z ξ ξ ≤
        (3 / ℓ ^ 2) * (K.toHistory.stageMetric (Fin.last K.eventCount) r).inner z ξ ξ) :
    riemannianEDistOf (K.toHistory.stageMetric (Fin.last K.eventCount) s) p q ≤
      riemannianEDistOf (K.toHistory.stageMetric (Fin.last K.eventCount) t) p q +
        ENNReal.ofReal ((8 / ℓ) * (t - s)) := by
  simp only [K.stageMetric_last_restrict_P6HF h] at hRic ⊢
  exact K.edist_le_add_of_final_ricci_P6GWF h hℓ hst hs ht p q hRic

/-- consumer（G1，`_P6GWF`）：零长度窗口（`s = t`）的平凡实例——`hRic` 在 `Ioo t t = ∅` 上空真，
结论 `d_t ≤ d_t + 0` 由 G1 直接给出。 -/
example (K : RetainedCoreHistory.{u}) (h : K.time (Fin.last K.eventCount) < K.horizon) {t : ℝ}
    (ht1 : K.time (Fin.last K.eventCount) < t) (ht2 : t < K.horizon)
    (p q : (K.stage (Fin.last K.eventCount)).Carrier) :
    riemannianEDistOf (((K.finalSlab h).restrictIncoming le_rfl h le_rfl).flow.base.metric t) p q ≤
      riemannianEDistOf (((K.finalSlab h).restrictIncoming le_rfl h le_rfl).flow.base.metric t)
          p q +
        ENNReal.ofReal ((8 / (1 : ℝ)) * (t - t)) :=
  K.edist_le_add_of_final_ricci_P6GWF h one_pos le_rfl ht1 ht2 p q
    (fun _ hr => absurd (hr.1.trans hr.2) (lt_irrefl t))

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
