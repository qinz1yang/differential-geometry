import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.Local.FirstExitUSC_P6L4
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.Dist.SmoothDistortionC11D

/-!
# 单 history、单 slab 的首出时刻距离引理（O-CH11-P6ANCH4 G1，后缀 `_P6M4`）

DF-1（`hclosG`）的核心论证，抽象成单 slab 形：event `e` 的 incoming flow（stage `e⁻` 的共同定义域，
`[a, t] ⊆ (time e⁻, time e⁺)`），两点 `p, q`，预算 `X`。
* **条件曲率**（`hRic`）：只在"`d_s(p, q) < X`"的时刻 `s` 要求两端 `ℓ`-球 `Ric ≤ (3/ℓ²) g`（Good 区内的
  曲率，不要求先验的全窗口曲率）；
* **初始余量**（`hmargin`）：`d_t(p, q) + (8/ℓ)(t − a) < X`；
⇒ 首出时刻 `τ⋆ := sInf {s ∈ [a, t] | ∀ s' ∈ [s, t], d_{s'} < X}` 等于 `a`：`(τ⋆, t]` 内 Good ⇒
Perelman I.8.3(b)
（`edist_le_add_of_endpoint_ricci_solution_C11D`）给 `d_{τ⋆} ≤ d_t + 8(t − τ⋆)/ℓ < X`；`τ⋆ > a` 时 USC
（`edist_lt_near_left_P6L4`，紧性给的全局 `|Ric|` 只作有限性）与 inf 矛盾。
结论：`∀ s ∈ [a, t]，d_s(p, q) ≤ d_t(p, q) + (8/ℓ)(t − s)`。
-/

set_option autoImplicit false

noncomputable section

open Set Filter
open DifferentialGeometry.Geometry.Curvature
open scoped Manifold ContDiff Topology ENNReal NNReal

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

universe u

/-- slab 内 I.8.3(b)：`[s, t] ⊆ (time e⁻, time e⁺)`、`(s, t)` 上两端 `ℓ`-球 `Ric ≤ 3/ℓ²`（`_P6M4`）。 -/
theorem ObservedHistory.edist_le_add_of_slab_ricci_P6M4 (H : ObservedHistory.{u})
    (e : Fin H.eventCount) {s t ℓ : ℝ} (hℓ : 0 < ℓ) (hst : s ≤ t) (hs : H.time e.castSucc < s)
    (ht : t < H.time e.succ) (p q : (H.stage e.castSucc).Carrier)
    (hRic : ∀ r ∈ Ioo s t, ∀ z : (H.stage e.castSucc).Carrier, ∀ ξ : TangentSpace ThreeModel z,
      (riemannianEDistOf ((H.event e).incoming.flow.base.metric r) p z < ENNReal.ofReal ℓ ∨
        riemannianEDistOf ((H.event e).incoming.flow.base.metric r) q z < ENNReal.ofReal ℓ) →
      ricciTensor ((H.event e).incoming.flow.base.metric r) z ξ ξ ≤
        (3 / ℓ ^ 2) * ((H.event e).incoming.flow.base.metric r).inner z ξ ξ) :
    riemannianEDistOf ((H.event e).incoming.flow.base.metric s) p q ≤
      riemannianEDistOf ((H.event e).incoming.flow.base.metric t) p q +
        ENNReal.ofReal ((8 / ℓ) * (t - s)) :=
  edist_le_add_of_endpoint_ricci_solution_C11D (H.event e).incoming.flow
    (H.event e).incoming.equation hst hℓ
    (fun _ hr => ⟨hs.le.trans hr.1, lt_of_le_of_lt hr.2 ht⟩)
    (fun _ hr => ⟨hs.trans hr.1, hr.2.trans ht⟩) p q hRic

/-- **首出时刻距离引理（单 slab，`_P6M4`）**：条件曲率 `hRic`（只在 `d_s(p, q) < X` 的时刻）+ 初始余量
`d_t + (8/ℓ)(t − a) < X` ⇒ `[a, t]` 全体时刻 `d_s(p, q) ≤ d_t(p, q) + (8/ℓ)(t − s)`。 -/
theorem ObservedHistory.firstExit_distance_P6M4 (H : ObservedHistory.{u}) (e : Fin H.eventCount)
    {a t ℓ : ℝ} (hℓ : 0 < ℓ) (hat : a ≤ t) (ha : H.time e.castSucc < a)
    (ht : t < H.time e.succ) (p q : (H.stage e.castSucc).Carrier) {X : ℝ≥0∞}
    (hmargin : riemannianEDistOf ((H.event e).incoming.flow.base.metric t) p q +
      ENNReal.ofReal ((8 / ℓ) * (t - a)) < X)
    (hRic : ∀ s ∈ Ioo a t,
      riemannianEDistOf ((H.event e).incoming.flow.base.metric s) p q < X →
      ∀ z : (H.stage e.castSucc).Carrier, ∀ ξ : TangentSpace ThreeModel z,
      (riemannianEDistOf ((H.event e).incoming.flow.base.metric s) p z < ENNReal.ofReal ℓ ∨
        riemannianEDistOf ((H.event e).incoming.flow.base.metric s) q z < ENNReal.ofReal ℓ) →
      ricciTensor ((H.event e).incoming.flow.base.metric s) z ξ ξ ≤
        (3 / ℓ ^ 2) * ((H.event e).incoming.flow.base.metric s).inner z ξ ξ) :
    ∀ s ∈ Icc a t, riemannianEDistOf ((H.event e).incoming.flow.base.metric s) p q ≤
      riemannianEDistOf ((H.event e).incoming.flow.base.metric t) p q +
        ENNReal.ofReal ((8 / ℓ) * (t - s)) := by
  -- 区间 `[s, t]`（`a ≤ s`）上 Good ⇒ I.8.3(b)
  have hdist : ∀ s, a ≤ s → s ≤ t →
      (∀ s' ∈ Ioo s t, riemannianEDistOf ((H.event e).incoming.flow.base.metric s') p q < X) →
      riemannianEDistOf ((H.event e).incoming.flow.base.metric s) p q ≤
        riemannianEDistOf ((H.event e).incoming.flow.base.metric t) p q +
          ENNReal.ofReal ((8 / ℓ) * (t - s)) := by
    intro s has hst hgood
    exact H.edist_le_add_of_slab_ricci_P6M4 e hℓ hst (ha.trans_le has) ht p q
      (fun r hr z ξ hz => hRic r ⟨has.trans_lt hr.1, hr.2⟩ (hgood r hr) z ξ hz)
  -- Good 集合与首出时刻
  let S : Set ℝ := {s | a ≤ s ∧ s ≤ t ∧
    ∀ s' ∈ Icc s t, riemannianEDistOf ((H.event e).incoming.flow.base.metric s') p q < X}
  have htS : t ∈ S := by
    refine ⟨hat, le_rfl, fun s' hs' => ?_⟩
    have h : s' = t := le_antisymm hs'.2 hs'.1
    rw [h]
    exact lt_of_le_of_lt le_self_add hmargin
  have hne : S.Nonempty := ⟨t, htS⟩
  have hbdd : BddBelow S := ⟨a, fun s hs => hs.1⟩
  have hastar : a ≤ sInf S := le_csInf hne fun s hs => hs.1
  have hstart : sInf S ≤ t := csInf_le hbdd htS
  have hup : ∀ s' ∈ Ioc (sInf S) t,
      riemannianEDistOf ((H.event e).incoming.flow.base.metric s') p q < X := by
    intro s' hs'
    obtain ⟨s, hsS, hss'⟩ := exists_lt_of_csInf_lt hne hs'.1
    exact hsS.2.2 s' ⟨hss'.le, hs'.2⟩
  have hℓ8 : (8 / ℓ) * (t - sInf S) ≤ (8 / ℓ) * (t - a) :=
    mul_le_mul_of_nonneg_left (by linarith) (div_pos (by norm_num) hℓ).le
  have hstar_lt : riemannianEDistOf ((H.event e).incoming.flow.base.metric (sInf S)) p q < X :=
    lt_of_le_of_lt ((hdist (sInf S) hastar hstart fun s' hs' => hup s' ⟨hs'.1, hs'.2.le⟩).trans
      (add_le_add le_rfl (ENNReal.ofReal_le_ofReal hℓ8))) hmargin
  have hstarS : sInf S ∈ S := by
    refine ⟨hastar, hstart, fun s' hs' => ?_⟩
    rcases eq_or_lt_of_le hs'.1 with h | h
    · rw [← h]
      exact hstar_lt
    · exact hup s' ⟨h, hs'.2⟩
  -- 首出时刻 = `a`（USC 左延拓）
  have hstar_eq : sInf S = a := by
    by_contra hne'
    have hlt : a < sInf S := lt_of_le_of_ne hastar (Ne.symm hne')
    obtain ⟨s₁, has₁, hs₁, hnear⟩ := edist_lt_near_left_P6L4 (H.event e).incoming.flow
      (H.event e).incoming.equation hlt
      (fun r hr => ⟨ha.trans_le hr.1, lt_of_le_of_lt (hr.2.trans hstart) ht⟩) p q hstar_lt
    have hs₁S : s₁ ∈ S := by
      refine ⟨has₁, hs₁.le.trans hstart, fun s' hs' => ?_⟩
      rcases le_or_gt s' (sInf S) with h | h
      · exact hnear s' ⟨hs'.1, h⟩
      · exact hup s' ⟨h, hs'.2⟩
    have := csInf_le hbdd hs₁S
    linarith
  intro s hs
  refine hdist s hs.1 hs.2 fun s' hs' => hstarS.2.2 s' ⟨?_, hs'.2.le⟩
  rw [hstar_eq]
  exact hs.1.trans hs'.1.le

/-- **consumer（G1）**：首出时刻引理于 `s = a` ⇒ 整窗不出预算：`d_a(p, q) < X`（`hmargin` 的严格余量）。 -/
example (H : ObservedHistory.{u}) (e : Fin H.eventCount)
    {a t ℓ : ℝ} (hℓ : 0 < ℓ) (hat : a ≤ t) (ha : H.time e.castSucc < a)
    (ht : t < H.time e.succ) (p q : (H.stage e.castSucc).Carrier) {X : ℝ≥0∞}
    (hmargin : riemannianEDistOf ((H.event e).incoming.flow.base.metric t) p q +
      ENNReal.ofReal ((8 / ℓ) * (t - a)) < X)
    (hRic : ∀ s ∈ Ioo a t,
      riemannianEDistOf ((H.event e).incoming.flow.base.metric s) p q < X →
      ∀ z : (H.stage e.castSucc).Carrier, ∀ ξ : TangentSpace ThreeModel z,
      (riemannianEDistOf ((H.event e).incoming.flow.base.metric s) p z < ENNReal.ofReal ℓ ∨
        riemannianEDistOf ((H.event e).incoming.flow.base.metric s) q z < ENNReal.ofReal ℓ) →
      ricciTensor ((H.event e).incoming.flow.base.metric s) z ξ ξ ≤
        (3 / ℓ ^ 2) * ((H.event e).incoming.flow.base.metric s).inner z ξ ξ) :
    riemannianEDistOf ((H.event e).incoming.flow.base.metric a) p q < X :=
  lt_of_le_of_lt (H.firstExit_distance_P6M4 e hℓ hat ha ht p q hmargin hRic a ⟨le_rfl, hat⟩)
    hmargin

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
