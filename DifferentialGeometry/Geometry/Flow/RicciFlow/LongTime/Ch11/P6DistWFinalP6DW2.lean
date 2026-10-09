import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.P6HscalUFinalP6M6

/-!
# (TR₀) `hdistW` 的 final slab 孪生：基点 `σ` 落在 final slab（S-CH11-HDISTW2 G1，后缀 `_P6DW2`）

`Ch11/P6DistWFirstExitP6DW`（event 版 `hdistW_of_firstExit_P6DW`，`σ` 在 event slab
`activeStage σ = e⁻`）与 `Local/SeedWindowFirstExit_P6DW` 三件套的 **final slab 孪生**，消费 S-CH11-HSCALU2 的
`hscalW_final_P6M6`（Anchor₀ 的 final 版，PROVISIONAL 合同 Prop）与 `P6FirstExitFinalP6M6` 的 final 首出核
（`edist_le_add_of_final_ricci_P6M6`、`ricci_seed_or_scal_final_P6M6`）。**槽形冻结**：结论 =
`P6ClosedConditionalP6CD:122–137` 的 `hdistW` binder 逐字（stage 泛型，`activeStage` 参数化），不改。

* `firstExit_distance_closed_final_P6DW2`：`firstExit_distance_final_P6M6` 的闭左端版（`time last ≤ a`）；
  USC 一步在 `[(a + τ⋆)/2, τ⋆]` 上做（`firstExit_distance_closed_P6DW` 的 final 版，`(finalSlab hlt).flow`）。
* `seed_window_firstExit_final_P6DW2`：`seed_window_firstExit_P6DW` 的 final 版
  （stage `Fin.last`，窗顶 `σ < horizon`）。
* `distW_transport_final_P6DW2`：stage 指标形（`kv = kσ = Fin.last`，`tr` 单点）⇒ final 层，
  供序列形逐字对接。
* **`hdistW_of_firstExit_final_P6DW2`**：结论 = `hdistW` 槽逐字；前提 = event 版同源数据（K0 `hsmall/hclock`、
  `R r² → ∞`、HI `hpin`、`hwin`、`hL`）+ `hσfin`（`activeStage σ = Fin.last`）+ `hσlt`（`σ < horizon`）+
  **唯一残余 `hscalW_final_P6M6`**（Anchor₀ 的 final 版，HSCALU2 登记的合同 Prop，本文件不证它）。
  `σ < horizon` 是 final 支已有数据（HCLOSEF `htK : t < horizon`，`σ = t`）；它替代 event 版里由
  `hσev` 给出的 `σ < time e⁺`（USC 左延拓需要 `σ` 在 `regular` 内，`σ = horizon` 时不可用）。
* `hfinalBranch_slab_P6DW2`：HCLOSEF `hcloseF_plus_P6HF` / RERUN8 final 支的数据形（`htl`、`htK`、`hKh`、
  `hσ : σ n = t n`）⇒ `hσfin ∧ hσlt`。consumer `example` 把它与主定理接成 final 支可直接消费的 `hdistW`。
-/

set_option autoImplicit false

noncomputable section

open Set Function Filter
open DifferentialGeometry.Geometry.Curvature DifferentialGeometry.Tensor0SBundle
open scoped Manifold NNReal Topology ContDiff ENNReal

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

universe u

/-- **首出时刻距离引理，final slab 闭左端版（`_P6DW2`）**：`firstExit_distance_final_P6M6` 把
`time last < a` 放宽为 `time last ≤ a`；结论同：`∀ s ∈ [a, t]，d_s(p, q) ≤ d_t(p, q) + (8/ℓ)(t − s)`。
Perelman I.8.3(b) 只要 `time last ≤ s`（`edist_le_add_of_final_ricci_P6M6`）；USC 一步在
`[(a + τ⋆)/2, τ⋆]` 上做，避开左端点。 -/
theorem ObservedHistory.firstExit_distance_closed_final_P6DW2 (H : ObservedHistory.{u})
    {a t ℓ : ℝ} (hℓ : 0 < ℓ) (hat : a ≤ t) (ha : H.time (Fin.last H.eventCount) ≤ a)
    (ht : t < H.horizon) (p q : (H.stage (Fin.last H.eventCount)).Carrier) {X : ℝ≥0∞}
    (hmargin : riemannianEDistOf (H.stageMetric (Fin.last H.eventCount) t) p q +
      ENNReal.ofReal ((8 / ℓ) * (t - a)) < X)
    (hRic : ∀ s ∈ Ioo a t,
      riemannianEDistOf (H.stageMetric (Fin.last H.eventCount) s) p q < X →
      ∀ z : (H.stage (Fin.last H.eventCount)).Carrier, ∀ ξ : TangentSpace ThreeModel z,
      (riemannianEDistOf (H.stageMetric (Fin.last H.eventCount) s) p z < ENNReal.ofReal ℓ ∨
        riemannianEDistOf (H.stageMetric (Fin.last H.eventCount) s) q z < ENNReal.ofReal ℓ) →
      ricciTensor (H.stageMetric (Fin.last H.eventCount) s) z ξ ξ ≤
        (3 / ℓ ^ 2) * (H.stageMetric (Fin.last H.eventCount) s).inner z ξ ξ) :
    ∀ s ∈ Icc a t, riemannianEDistOf (H.stageMetric (Fin.last H.eventCount) s) p q ≤
      riemannianEDistOf (H.stageMetric (Fin.last H.eventCount) t) p q +
        ENNReal.ofReal ((8 / ℓ) * (t - s)) := by
  have hlt : H.time (Fin.last H.eventCount) < H.horizon := lt_of_le_of_lt ha (hat.trans_lt ht)
  -- 区间 `[s, t]`（`a ≤ s`）上 Good ⇒ I.8.3(b) final 形
  have hdist : ∀ s, a ≤ s → s ≤ t →
      (∀ s' ∈ Ioo s t, riemannianEDistOf (H.stageMetric (Fin.last H.eventCount) s') p q < X) →
      riemannianEDistOf (H.stageMetric (Fin.last H.eventCount) s) p q ≤
        riemannianEDistOf (H.stageMetric (Fin.last H.eventCount) t) p q +
          ENNReal.ofReal ((8 / ℓ) * (t - s)) := by
    intro s has hst hgood
    exact H.edist_le_add_of_final_ricci_P6M6 hℓ hst (ha.trans has) ht.le p q
      (fun r hr z ξ hz => hRic r ⟨has.trans_lt hr.1, hr.2⟩ (hgood r hr) z ξ hz)
  -- Good 集合与首出时刻
  let S : Set ℝ := {s | a ≤ s ∧ s ≤ t ∧
    ∀ s' ∈ Icc s t, riemannianEDistOf (H.stageMetric (Fin.last H.eventCount) s') p q < X}
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
      riemannianEDistOf (H.stageMetric (Fin.last H.eventCount) s') p q < X := by
    intro s' hs'
    obtain ⟨s, hsS, hss'⟩ := exists_lt_of_csInf_lt hne hs'.1
    exact hsS.2.2 s' ⟨hss'.le, hs'.2⟩
  have hℓ8 : (8 / ℓ) * (t - sInf S) ≤ (8 / ℓ) * (t - a) :=
    mul_le_mul_of_nonneg_left (by linarith) (div_pos (by norm_num) hℓ).le
  have hstar_lt : riemannianEDistOf (H.stageMetric (Fin.last H.eventCount) (sInf S)) p q < X :=
    lt_of_le_of_lt ((hdist (sInf S) hastar hstart fun s' hs' => hup s' ⟨hs'.1, hs'.2.le⟩).trans
      (add_le_add le_rfl (ENNReal.ofReal_le_ofReal hℓ8))) hmargin
  have hstarS : sInf S ∈ S := by
    refine ⟨hastar, hstart, fun s' hs' => ?_⟩
    rcases eq_or_lt_of_le hs'.1 with h | h
    · rw [← h]
      exact hstar_lt
    · exact hup s' ⟨h, hs'.2⟩
  -- 首出时刻 = `a`（USC 左延拓，在 `[(a + τ⋆)/2, τ⋆]` 上，避开左端点；用 `(finalSlab hlt).flow`）
  have hstar_eq : sInf S = a := by
    by_contra hne'
    have hlt' : a < sInf S := lt_of_le_of_ne hastar (Ne.symm hne')
    have hmid : (a + sInf S) / 2 < sInf S := by linarith
    have hmid' : a < (a + sInf S) / 2 := by linarith
    have hstar_lt' : riemannianEDistOf ((H.finalSlab hlt).flow.base.metric (sInf S)) p q < X := by
      rw [← ObservedHistory.stageMetric_last_of_lt (H := H) (h := hlt)]
      exact hstar_lt
    obtain ⟨s₁, has₁, hs₁, hnear⟩ := edist_lt_near_left_P6L4 (H.finalSlab hlt).flow
      (H.finalSlab hlt).equation hmid
      (fun r hr => ⟨(ha.trans_lt hmid').trans_le hr.1, lt_of_le_of_lt (hr.2.trans hstart) ht⟩)
      p q hstar_lt'
    have hs₁S : s₁ ∈ S := by
      refine ⟨hmid'.le.trans has₁, hs₁.le.trans hstart, fun s' hs' => ?_⟩
      rcases le_or_gt s' (sInf S) with h | h
      · rw [ObservedHistory.stageMetric_last_of_lt (H := H) (h := hlt)]
        exact hnear s' ⟨hs'.1, h⟩
      · exact hup s' ⟨h, hs'.2⟩
    have := csInf_le hbdd hs₁S
    linarith
  intro s hs
  refine hdist s hs.1 hs.2 fun s' hs' => hstarS.2.2 s' ⟨?_, hs'.2.le⟩
  rw [hstar_eq]
  exact hs.1.trans hs'.1.le

/-- **基点窗口 seed 距离（final slab 层，`_P6DW2`）**：`seed_window_firstExit_P6DW` 的 final 孪生。
slab = `last`、窗顶 `σ < horizon`，`y, x` 于 `g_last(σ)` 满足 `d_σ(y, x) < D/√R`、`d_σ(O, y) ≤ dσ = A`；
窗 `τ ∈ [σ − T/R, σ]`（`time last ≤ τ`）；K0 种子 + pinching + **条件** U 端标量界 `hscal`（开窗
`s ∈ (σ − T/R, σ)`、`time last < s`、`d_s(O, x) ≤ dσ + L/√R` 时，`B_s(x, 1/√(CR))` 上 `R ≤ CR`）+
`L ≥ D⁺ + 8√K T⁺`、`2500 K ≤ R r²`（`K := max 1 (2√3(C/2 + max C (2e⁴)))`）
⇒ `d_τ(O, x) ≤ dσ + L/√R`。 -/
theorem ObservedHistory.seed_window_firstExit_final_P6DW2 (H : ObservedHistory.{u})
    {Tn aSeed : Icc (0 : ℝ) H.horizon} (haT : aSeed ≤ Tn) {pT : (H.stageAt Tn).Carrier} {r : ℝ}
    (hsmall : GC.LongTime.hasSmallParabolicCurvature H Tn pT r)
    (hclock : (aSeed : ℝ) = (Tn : ℝ) - r ^ 2)
    (seedTrace : BackwardPointTrace H (H.activeStage aSeed) (H.activeStage Tn)
      (H.activeStage_mono haT) pT)
    {a₀ : ℝ} (ha₀ : 0 ≤ a₀)
    (hpin : ∀ (t : Icc (0 : ℝ) H.horizon) (x : (H.stageAt t).Carrier),
      InFixedHamiltonIveyRegion (H.stageMetric (H.activeStage t) t) (a₀ + t) x)
    (h1 : H.activeStage aSeed ≤ Fin.last H.eventCount)
    (h2 : Fin.last H.eventCount ≤ H.activeStage Tn)
    (y x : (H.stage (Fin.last H.eventCount)).Carrier)
    {dσ : ℝ≥0∞} {A R L C D T τ σ : ℝ} (hdσ : dσ = ENNReal.ofReal A) (hA : 0 ≤ A)
    (hR : 0 < R) (hC1 : 1 ≤ C)
    (hRr : 2500 * max 1 (2 * Real.sqrt 3 * (C / 2 + max C (2 * Real.exp 4))) ≤ R * r ^ 2)
    (hL : max D 0 +
      8 * Real.sqrt (max 1 (2 * Real.sqrt 3 * (C / 2 + max C (2 * Real.exp 4)))) * max T 0 ≤ L)
    (hyO : riemannianEDistOf (H.stageMetric (Fin.last H.eventCount) σ)
      (seedTrace.point (Fin.last H.eventCount) h1 h2) y ≤ dσ)
    (hxy : x ∈ riemannianBallOf (H.stageMetric (Fin.last H.eventCount) σ) y (D / Real.sqrt R))
    (hτT : σ - T / R ≤ τ) (hτσ : τ ≤ σ) (hτ1 : H.time (Fin.last H.eventCount) ≤ τ)
    (hσ2 : σ < H.horizon) (haτ : (aSeed : ℝ) ≤ τ) (hσT : σ ≤ Tn) (hRτ : 1 ≤ R * τ)
    (hscal : ∀ s : ℝ, σ - T / R < s → s < σ → H.time (Fin.last H.eventCount) < s →
      riemannianEDistOf (H.stageMetric (Fin.last H.eventCount) s)
          (seedTrace.point (Fin.last H.eventCount) h1 h2) x ≤
        dσ + ENNReal.ofReal (L / Real.sqrt R) →
      ∀ z : (H.stage (Fin.last H.eventCount)).Carrier,
        riemannianEDistOf (H.stageMetric (Fin.last H.eventCount) s) x z <
          ENNReal.ofReal (1 / Real.sqrt (C * R)) →
        metricScalarAt (H.stageMetric (Fin.last H.eventCount) s) z ≤ C * R) :
    riemannianEDistOf (H.stageMetric (Fin.last H.eventCount) τ)
        (seedTrace.point (Fin.last H.eventCount) h1 h2) x ≤
      dσ + ENNReal.ofReal (L / Real.sqrt R) := by
  set K := max 1 (2 * Real.sqrt 3 * (C / 2 + max C (2 * Real.exp 4))) with hKdef
  have hK1 : 1 ≤ K := le_max_left _ _
  have hC : 0 ≤ C := by linarith
  have h3 : 1 ≤ Real.sqrt 3 := by
    rw [show (1 : ℝ) = Real.sqrt 1 by simp]
    exact Real.sqrt_le_sqrt (by norm_num)
  have hCK : C ≤ K := by
    refine le_trans ?_ (le_max_right _ _)
    have hm : C ≤ max C (2 * Real.exp 4) := le_max_left _ _
    nlinarith
  have hr : 0 < r := hsmall.1
  obtain ⟨hℓr, hKr, hKℓ, -⟩ := seq_scale_bounds_C11G hK1 hR hr hRr
  have hsK : 0 < Real.sqrt K := Real.sqrt_pos.2 (by linarith)
  have hsR : 0 < Real.sqrt R := Real.sqrt_pos.2 hR
  have hℓ : 0 < 1 / Real.sqrt K / Real.sqrt R := by positivity
  have hℓCR : 1 / Real.sqrt K / Real.sqrt R ≤ 1 / Real.sqrt (C * R) := by
    have hCR : Real.sqrt (C * R) ≤ Real.sqrt K * Real.sqrt R := by
      rw [← Real.sqrt_mul (by linarith)]
      exact Real.sqrt_le_sqrt (mul_le_mul_of_nonneg_right hCK hR.le)
    rw [div_div]
    exact one_div_le_one_div_of_le (Real.sqrt_pos.2 (by positivity)) hCR
  have hKC : 2 * Real.sqrt 3 * (C / 2 + max C (2 * Real.exp 4)) * R ≤ K * R :=
    mul_le_mul_of_nonneg_right (le_max_right _ _) hR.le
  have hD0 : 0 ≤ max D 0 := le_max_right _ _
  have hT0 : 0 ≤ max T 0 := le_max_right _ _
  have hL0 : 0 ≤ L := by
    have : 0 ≤ 8 * Real.sqrt K * max T 0 := by positivity
    linarith
  -- 漂移与初始余量（σ 时刻三角）
  have hdrift := drift_le_P6L4 (by linarith : (0 : ℝ) < K) hR le_rfl hτT
  have hdr0 : 0 ≤ 8 / (1 / Real.sqrt K / Real.sqrt R) * (σ - τ) :=
    mul_nonneg (by positivity) (by linarith)
  have hyx : riemannianEDistOf (H.stageMetric (Fin.last H.eventCount) σ) y x <
      ENNReal.ofReal (max D 0 / Real.sqrt R) :=
    lt_of_lt_of_le hxy (ENNReal.ofReal_le_ofReal
      (div_le_div_of_nonneg_right (le_max_left _ _) hsR.le))
  have hyO' : riemannianEDistOf (H.stageMetric (Fin.last H.eventCount) σ)
      (seedTrace.point (Fin.last H.eventCount) h1 h2) y ≤ ENNReal.ofReal A := hdσ ▸ hyO
  have hd2 : riemannianEDistOf (H.stageMetric (Fin.last H.eventCount) σ)
        (seedTrace.point (Fin.last H.eventCount) h1 h2) y +
      riemannianEDistOf (H.stageMetric (Fin.last H.eventCount) σ) y x <
      ENNReal.ofReal A + ENNReal.ofReal (max D 0 / Real.sqrt R) :=
    ENNReal.add_lt_add_of_le_of_lt (ne_top_of_le_ne_top ENNReal.ofReal_ne_top hyO') hyO' hyx
  have hd3 : ENNReal.ofReal A + ENNReal.ofReal (max D 0 / Real.sqrt R) +
        ENNReal.ofReal (8 / (1 / Real.sqrt K / Real.sqrt R) * (σ - τ)) ≤
      dσ + ENNReal.ofReal (L / Real.sqrt R) := by
    rw [← ENNReal.ofReal_add hA (by positivity), ← ENNReal.ofReal_add (by positivity) hdr0, hdσ,
      ← ENNReal.ofReal_add hA (by positivity)]
    apply ENNReal.ofReal_le_ofReal
    have hsum : max D 0 / Real.sqrt R + 8 * Real.sqrt K * max T 0 / Real.sqrt R =
        (max D 0 + 8 * Real.sqrt K * max T 0) / Real.sqrt R := by ring
    have hle : (max D 0 + 8 * Real.sqrt K * max T 0) / Real.sqrt R ≤ L / Real.sqrt R :=
      div_le_div_of_nonneg_right hL hsR.le
    linarith
  have hmargin : riemannianEDistOf (H.stageMetric (Fin.last H.eventCount) σ)
        (seedTrace.point (Fin.last H.eventCount) h1 h2) x +
      ENNReal.ofReal (8 / (1 / Real.sqrt K / Real.sqrt R) * (σ - τ)) <
      dσ + ENNReal.ofReal (L / Real.sqrt R) :=
    calc riemannianEDistOf (H.stageMetric (Fin.last H.eventCount) σ)
          (seedTrace.point (Fin.last H.eventCount) h1 h2) x +
          ENNReal.ofReal (8 / (1 / Real.sqrt K / Real.sqrt R) * (σ - τ)) ≤
        (riemannianEDistOf (H.stageMetric (Fin.last H.eventCount) σ)
            (seedTrace.point (Fin.last H.eventCount) h1 h2) y +
          riemannianEDistOf (H.stageMetric (Fin.last H.eventCount) σ) y x) +
          ENNReal.ofReal (8 / (1 / Real.sqrt K / Real.sqrt R) * (σ - τ)) :=
          add_le_add (riemannianEDistOf_triangle _ _ _ _) le_rfl
      _ < ENNReal.ofReal A + ENNReal.ofReal (max D 0 / Real.sqrt R) +
          ENNReal.ofReal (8 / (1 / Real.sqrt K / Real.sqrt R) * (σ - τ)) :=
          ENNReal.add_lt_add_right ENNReal.ofReal_ne_top hd2
      _ ≤ dσ + ENNReal.ofReal (L / Real.sqrt R) := hd3
  -- 首出时刻（闭左端）
  have hfe := H.firstExit_distance_closed_final_P6DW2 hℓ hτσ hτ1 hσ2
    (seedTrace.point (Fin.last H.eventCount) h1 h2) x hmargin
    (fun s hs hgood => H.ricci_seed_or_scal_final_P6M6 haT hsmall hclock seedTrace ha₀ hpin h1 h2 x
      hR hℓ hKℓ hℓr hKr hC hKC (hτ1.trans_lt hs.1) (haτ.trans hs.1.le)
      (hs.2.le.trans hσT) (hRτ.trans (mul_le_mul_of_nonneg_left hs.1.le hR.le))
      (fun z hz => hscal s (lt_of_le_of_lt hτT hs.1) hs.2 (hτ1.trans_lt hs.1) hgood.le z
        (hz.trans_le (ENNReal.ofReal_le_ofReal hℓCR)))) τ ⟨le_rfl, hτσ⟩
  exact (lt_of_le_of_lt hfe hmargin).le

/-- **stage 指标形 ⇒ final 层（`_P6DW2`）**：`kv = kσ = Fin.last`（同 slab）、`tr` 单点 trace
（`tr.point kv = x`）；`stageMetric last ·` 就是 final 首出核的度量；把 `seed_window_firstExit_final_P6DW2`
搬到 hdistW 的 stage 形（`distW_transport_P6DW` 的 final 版，不需要 `stageMetric_castSucc_apply`）。 -/
theorem ObservedHistory.distW_transport_final_P6DW2 (H : ObservedHistory.{u})
    {Tn aSeed : Icc (0 : ℝ) H.horizon} (haT : aSeed ≤ Tn) {pT : (H.stageAt Tn).Carrier} {r : ℝ}
    (hsmall : GC.LongTime.hasSmallParabolicCurvature H Tn pT r)
    (hclock : (aSeed : ℝ) = (Tn : ℝ) - r ^ 2)
    (seedTrace : BackwardPointTrace H (H.activeStage aSeed) (H.activeStage Tn)
      (H.activeStage_mono haT) pT)
    {a₀ : ℝ} (ha₀ : 0 ≤ a₀)
    (hpin : ∀ (t : Icc (0 : ℝ) H.horizon) (x : (H.stageAt t).Carrier),
      InFixedHamiltonIveyRegion (H.stageMetric (H.activeStage t) t) (a₀ + t) x)
    {kv kσ : Fin (H.eventCount + 1)} (hkk : kv = kσ) (he : kσ = Fin.last H.eventCount)
    (h1v : H.activeStage aSeed ≤ kv) (h2v : kv ≤ H.activeStage Tn)
    (h1σ : H.activeStage aSeed ≤ kσ) (h2σ : kσ ≤ H.activeStage Tn) (hle : kv ≤ kσ)
    (y x : (H.stage kσ).Carrier) (tr : BackwardPointTrace H kv kσ hle x)
    {A R L C D T v σ : ℝ}
    (hdσ : riemannianEDistOf (H.stageMetric kσ σ) (seedTrace.point kσ h1σ h2σ) y =
      ENNReal.ofReal A) (hA : 0 ≤ A) (hR : 0 < R) (hC1 : 1 ≤ C)
    (hRr : 2500 * max 1 (2 * Real.sqrt 3 * (C / 2 + max C (2 * Real.exp 4))) ≤ R * r ^ 2)
    (hL : max D 0 +
      8 * Real.sqrt (max 1 (2 * Real.sqrt 3 * (C / 2 + max C (2 * Real.exp 4)))) * max T 0 ≤ L)
    (hxy : x ∈ riemannianBallOf (H.stageMetric kσ σ) y (D / Real.sqrt R))
    (hvT : σ - T / R ≤ v) (hvσ : v ≤ σ) (hv1 : H.time kσ ≤ v) (hσ2 : σ < H.horizon)
    (hav : (aSeed : ℝ) ≤ v) (hσT : σ ≤ Tn) (hRv : 1 ≤ R * v)
    (hscal : ∀ s : ℝ, σ - T / R < s → s < σ → H.time kσ < s →
      riemannianEDistOf (H.stageMetric kσ s) (seedTrace.point kσ h1σ h2σ) x ≤
        riemannianEDistOf (H.stageMetric kσ σ) (seedTrace.point kσ h1σ h2σ) y +
          ENNReal.ofReal (L / Real.sqrt R) →
      ∀ z : (H.stage kσ).Carrier,
        riemannianEDistOf (H.stageMetric kσ s) x z < ENNReal.ofReal (1 / Real.sqrt (C * R)) →
        metricScalarAt (H.stageMetric kσ s) z ≤ C * R) :
    riemannianEDistOf (H.stageMetric kv v) (seedTrace.point kv h1v h2v) (tr.point kv le_rfl hle) ≤
      riemannianEDistOf (H.stageMetric kσ σ) (seedTrace.point kσ h1σ h2σ) y +
        ENNReal.ofReal (L / Real.sqrt R) := by
  subst hkk
  subst he
  have hpt : tr.point (Fin.last H.eventCount) le_rfl hle = x := tr.endpoint_eq
  rw [hpt]
  exact H.seed_window_firstExit_final_P6DW2 haT hsmall hclock seedTrace ha₀ hpin h1σ h2σ y x hdσ
    hA hR hC1 hRr hL le_rfl hxy hvT hvσ hv1 hσ2 hav hσT hRv
    (fun s hs1 hs2 hs3 hs4 z hz => hscal s hs1 hs2 hs3 hs4 z hz)

/-- **(TR₀) `hdistW` ⇐ final slab 首出时刻 σ₂ = 0 基点版（`_P6DW2`）**：结论逐字 = `hdistW` 槽
（`P6ClosedConditionalP6CD:122–137`、`hdistW_of_firstExit_P6DW` 的结论）；`σ` 在 final slab
（`hσfin`），`σ < horizon`（`hσlt`）；唯一残余 `hscalW_final_P6M6`（Anchor₀ 的 final 版，开窗、
单时刻 ExitGuard，`C` 在 `n` 之前）。`hlate` 由 `hwin (T + 1)` + `aSeed ≥ 0` 推出，不另设。 -/
theorem ObservedHistory.hdistW_of_firstExit_final_P6DW2 (Kh : ℕ → ObservedHistory.{u})
    (Tn aSeed σ : ∀ n, Icc (0 : ℝ) (Kh n).horizon)
    (haT : ∀ n, aSeed n ≤ Tn n) (hsT : ∀ n, σ n ≤ Tn n) (has : ∀ n, aSeed n ≤ σ n)
    (pT : ∀ n, ((Kh n).stageAt (Tn n)).Carrier)
    (seedTrace : ∀ n, BackwardPointTrace (Kh n) ((Kh n).activeStage (aSeed n))
      ((Kh n).activeStage (Tn n)) ((Kh n).activeStage_mono (haT n)) (pT n))
    (y : ∀ n, ((Kh n).stageAt (σ n)).Carrier) (R L : ℕ → ℝ) (hR : ∀ n, 0 < R n)
    (r : ℕ → ℝ) (hL : Tendsto L atTop atTop)
    (hsmall : ∀ n, GC.LongTime.hasSmallParabolicCurvature (Kh n) (Tn n) (pT n) (r n))
    (hclock : ∀ n, (aSeed n : ℝ) = (Tn n : ℝ) - r n ^ 2)
    (hRr : Tendsto (fun n => R n * r n ^ 2) atTop atTop)
    (hwin : ∀ T : ℝ, 0 < T → ∀ᶠ n in atTop, (aSeed n : ℝ) ≤ σ n - T / R n)
    {a₀ : ℝ} (ha₀ : 0 ≤ a₀)
    (hpin : ∀ n (τ' : Icc (0 : ℝ) (Kh n).horizon) (x : ((Kh n).stageAt τ').Carrier),
      InFixedHamiltonIveyRegion ((Kh n).stageMetric ((Kh n).activeStage τ') τ') (a₀ + τ') x)
    (hσfin : ∀ n, (Kh n).activeStage (σ n) = Fin.last (Kh n).eventCount)
    (hσlt : ∀ n, (σ n : ℝ) < (Kh n).horizon)
    (hscalW : ObservedHistory.hscalW_final_P6M6 Kh Tn aSeed σ haT hsT has pT seedTrace y R L) :
    ∀ D T : ℝ, 0 < D → 0 < T → ∀ᶠ n in atTop,
      ∀ x ∈ riemannianBallOf ((Kh n).stageMetric ((Kh n).activeStage (σ n)) (σ n)) (y n)
          (D / Real.sqrt (R n)),
      ∀ (v : Icc (0 : ℝ) (Kh n).horizon) (hav : aSeed n ≤ v) (hvs : v ≤ σ n),
        (σ n : ℝ) - T / R n ≤ v →
        (Kh n).activeStage v = (Kh n).activeStage (σ n) →
      ∀ tr : BackwardPointTrace (Kh n) ((Kh n).activeStage v) ((Kh n).activeStage (σ n))
          ((Kh n).activeStage_mono hvs) x,
        riemannianEDistOf ((Kh n).stageMetric ((Kh n).activeStage v) v)
            ((seedTrace n).point ((Kh n).activeStage v) ((Kh n).activeStage_mono hav)
              ((Kh n).activeStage_mono (hvs.trans (hsT n))))
            (tr.point ((Kh n).activeStage v) le_rfl ((Kh n).activeStage_mono hvs)) ≤
          riemannianEDistOf ((Kh n).stageMetric ((Kh n).activeStage (σ n)) (σ n))
              ((seedTrace n).point ((Kh n).activeStage (σ n)) ((Kh n).activeStage_mono (has n))
                ((Kh n).activeStage_mono (hsT n))) (y n) +
            ENNReal.ofReal (L n / Real.sqrt (R n)) := by
  intro D T hD hT
  obtain ⟨C, hC, hev⟩ := ObservedHistory.hscalW_of_hscalW_final_P6M6 Kh Tn aSeed σ haT hsT has pT
    seedTrace y R L hσfin hscalW D T hD hT
  filter_upwards [hev, hwin (T + 1) (by linarith),
    hL.eventually_ge_atTop (max D 0 +
      8 * Real.sqrt (max 1 (2 * Real.sqrt 3 * (C / 2 + max C (2 * Real.exp 4)))) * max T 0),
    hRr.eventually_ge_atTop
      (2500 * max 1 (2 * Real.sqrt 3 * (C / 2 + max C (2 * Real.exp 4))))]
    with n hn hwn hLn hrn
  intro x hx v hav hvs hvT hvσ tr
  have hRn := hR n
  by_cases htop : riemannianEDistOf ((Kh n).stageMetric ((Kh n).activeStage (σ n)) (σ n))
      ((seedTrace n).point ((Kh n).activeStage (σ n)) ((Kh n).activeStage_mono (has n))
        ((Kh n).activeStage_mono (hsT n))) (y n) = ⊤
  · rw [htop, top_add]
    exact le_top
  have hv1 : (Kh n).time ((Kh n).activeStage (σ n)) ≤ v := by
    have h := (Kh n).activeStage_time_le v
    rwa [hvσ] at h
  have hvσ' : (v : ℝ) ≤ σ n := hvs
  have hav' : (aSeed n : ℝ) ≤ v := hav
  have hRv : 1 ≤ R n * v := by
    have h0 : (0 : ℝ) ≤ aSeed n := (aSeed n).2.1
    have e1 : R n * ((T + 1) / R n) = T + 1 := by field_simp
    have e2 : R n * (T / R n) = T := by field_simp
    have h3 : 0 ≤ R n * σ n - R n * ((T + 1) / R n) := by
      rw [← mul_sub]
      exact mul_nonneg hRn.le (by linarith)
    have h4 : R n * σ n - R n * (T / R n) ≤ R n * v := by
      rw [← mul_sub]
      exact mul_le_mul_of_nonneg_left hvT hRn.le
    rw [e1] at h3
    rw [e2] at h4
    linarith
  exact (Kh n).distW_transport_final_P6DW2 (haT n) (hsmall n) (hclock n) (seedTrace n) ha₀ (hpin n)
    hvσ (hσfin n) ((Kh n).activeStage_mono hav) ((Kh n).activeStage_mono (hvs.trans (hsT n)))
    ((Kh n).activeStage_mono (has n)) ((Kh n).activeStage_mono (hsT n))
    ((Kh n).activeStage_mono hvs) (y n) x tr (ENNReal.ofReal_toReal htop).symm
    ENNReal.toReal_nonneg hRn hC hrn hLn hx hvT hvσ' hv1 (hσlt n) hav' (hsT n) hRv (hn x hx)

/-- **final 支数据形 ⇒ `hσfin ∧ hσlt`（`_P6DW2`）**：HCLOSEF `hcloseF_plus_P6HF` / RERUN8 final 支的
数据（`htl : time last < t`、`htK : t < horizon`、`Kh = (K ·).toHistory`、`σ = t`）给出
`activeStage σ = Fin.last` 与 `σ < horizon`，即 `hdistW_of_firstExit_final_P6DW2` 的两条 slab 前提。 -/
theorem hfinalBranch_slab_P6DW2 {K : ℕ → RetainedCoreHistory.{u}} {t : ℕ → ℝ}
    (htl : ∀ n, (K n).time (Fin.last (K n).eventCount) < t n) (htK : ∀ n, t n < (K n).horizon)
    (Kh : ℕ → ObservedHistory.{u}) (hKh : Kh = fun n => (K n).toHistory)
    (σ : ∀ n, Icc (0 : ℝ) (Kh n).horizon) (hσ : ∀ n, (σ n : ℝ) = t n) :
    (∀ n, (Kh n).activeStage (σ n) = Fin.last (Kh n).eventCount) ∧
      ∀ n, (σ n : ℝ) < (Kh n).horizon := by
  subst hKh
  refine ⟨fun n => ?_, fun n => ?_⟩
  · exact (K n).toHistory.activeStage_eq_last_of_time_last_le (σ n)
      (by rw [hσ n]; exact (htl n).le)
  · rw [hσ n]
    exact htK n

/-- **consumer（`_P6DW2`）**：HCLOSEF / RERUN8 final 支的数据形（`htl`、`htK`、`hKh`、`hσ : σ = t`）+
`hscalW_final_P6M6` ⇒ `hdistW` 槽（结论逐字）。`hσfin` / `hσlt` 由 `hfinalBranch_slab_P6DW2` 给。 -/
example {K : ℕ → RetainedCoreHistory.{u}} {t : ℕ → ℝ}
    (htl : ∀ n, (K n).time (Fin.last (K n).eventCount) < t n) (htK : ∀ n, t n < (K n).horizon)
    (Kh : ℕ → ObservedHistory.{u}) (hKh : Kh = fun n => (K n).toHistory)
    (σ : ∀ n, Icc (0 : ℝ) (Kh n).horizon) (hσ : ∀ n, (σ n : ℝ) = t n)
    (Tn aSeed : ∀ n, Icc (0 : ℝ) (Kh n).horizon)
    (haT : ∀ n, aSeed n ≤ Tn n) (hsT : ∀ n, σ n ≤ Tn n) (has : ∀ n, aSeed n ≤ σ n)
    (pT : ∀ n, ((Kh n).stageAt (Tn n)).Carrier)
    (seedTrace : ∀ n, BackwardPointTrace (Kh n) ((Kh n).activeStage (aSeed n))
      ((Kh n).activeStage (Tn n)) ((Kh n).activeStage_mono (haT n)) (pT n))
    (y : ∀ n, ((Kh n).stageAt (σ n)).Carrier) (R L : ℕ → ℝ) (hR : ∀ n, 0 < R n)
    (r : ℕ → ℝ) (hL : Tendsto L atTop atTop)
    (hsmall : ∀ n, GC.LongTime.hasSmallParabolicCurvature (Kh n) (Tn n) (pT n) (r n))
    (hclock : ∀ n, (aSeed n : ℝ) = (Tn n : ℝ) - r n ^ 2)
    (hRr : Tendsto (fun n => R n * r n ^ 2) atTop atTop)
    (hwin : ∀ T : ℝ, 0 < T → ∀ᶠ n in atTop, (aSeed n : ℝ) ≤ σ n - T / R n)
    {a₀ : ℝ} (ha₀ : 0 ≤ a₀)
    (hpin : ∀ n (τ' : Icc (0 : ℝ) (Kh n).horizon) (x : ((Kh n).stageAt τ').Carrier),
      InFixedHamiltonIveyRegion ((Kh n).stageMetric ((Kh n).activeStage τ') τ') (a₀ + τ') x)
    (hscalW : ObservedHistory.hscalW_final_P6M6 Kh Tn aSeed σ haT hsT has pT seedTrace y R L) :
    ∀ D T : ℝ, 0 < D → 0 < T → ∀ᶠ n in atTop,
      ∀ x ∈ riemannianBallOf ((Kh n).stageMetric ((Kh n).activeStage (σ n)) (σ n)) (y n)
          (D / Real.sqrt (R n)),
      ∀ (v : Icc (0 : ℝ) (Kh n).horizon) (hav : aSeed n ≤ v) (hvs : v ≤ σ n),
        (σ n : ℝ) - T / R n ≤ v →
        (Kh n).activeStage v = (Kh n).activeStage (σ n) →
      ∀ tr : BackwardPointTrace (Kh n) ((Kh n).activeStage v) ((Kh n).activeStage (σ n))
          ((Kh n).activeStage_mono hvs) x,
        riemannianEDistOf ((Kh n).stageMetric ((Kh n).activeStage v) v)
            ((seedTrace n).point ((Kh n).activeStage v) ((Kh n).activeStage_mono hav)
              ((Kh n).activeStage_mono (hvs.trans (hsT n))))
            (tr.point ((Kh n).activeStage v) le_rfl ((Kh n).activeStage_mono hvs)) ≤
          riemannianEDistOf ((Kh n).stageMetric ((Kh n).activeStage (σ n)) (σ n))
              ((seedTrace n).point ((Kh n).activeStage (σ n)) ((Kh n).activeStage_mono (has n))
                ((Kh n).activeStage_mono (hsT n))) (y n) +
            ENNReal.ofReal (L n / Real.sqrt (R n)) :=
  ObservedHistory.hdistW_of_firstExit_final_P6DW2 Kh Tn aSeed σ haT hsT has pT seedTrace y R L hR r
    hL hsmall hclock hRr hwin ha₀ hpin (hfinalBranch_slab_P6DW2 htl htK Kh hKh σ hσ).1
    (hfinalBranch_slab_P6DW2 htl htK Kh hKh σ hσ).2 hscalW

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
