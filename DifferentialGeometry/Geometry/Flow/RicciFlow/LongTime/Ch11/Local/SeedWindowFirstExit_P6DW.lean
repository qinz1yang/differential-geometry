import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.Local.HclosFirstExit_P6L4

/-!
# 基点窗口 seed 距离的首出时刻生产（O-CH11-HDISTW G1，后缀 `_P6DW`）

(TR₀) `hdistW`（`P6ClosedConditionalP6CD:122–137`）= P6ANCH4 seed closure 的 **σ₂ = 0 基点版**：窗顶取基点时刻
`σ`、`w := y`、`Q := R = R(σ, y)`。与 `seed_closure_firstExit_P6L4` 的两处差别：
* 窗底 `τ` 可等于 slab 左端 `time e⁻`（hdistW 的前件 `activeStage v = activeStage σ` 只给 `time e⁻ ≤ v`）⇒
  `firstExit_distance_closed_P6DW`：`firstExit_distance_P6M4` 的闭左端版（Perelman I.8.3(b)
  `edist_le_add_of_endpoint_ricci_solution_C11D` 只要 `Icc ⊆ carrier`、`Ioo ⊆ regular`；USC 一步在
  `[(a + τ⋆)/2, τ⋆]` 上做）；
* 初始余量在 σ 时刻是平凡三角：`d_σ(O, x) ≤ d_σ(O, y) + d_σ(y, x) < d_σ + D/√R`（不需要 hscalU 的
  `hwseed` / `R ≤ R(v, w)`）；U 端条件标量界 `hscal` 只在**开窗** `s ∈ (σ − T/R, σ)` 用。
* `distW_transport_P6DW`：stage 指标形（`kv = kσ = e⁻`，`tr` 单点）⇒ event 层，供序列形
  `hdistW_of_firstExit_P6DW` 逐字对接。
-/

set_option autoImplicit false

noncomputable section

open Set Filter
open DifferentialGeometry.Geometry.Curvature DifferentialGeometry.Tensor0SBundle
open scoped Manifold ContDiff Topology ENNReal NNReal

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

universe u

/-- **首出时刻距离引理，闭左端版（`_P6DW`）**：`firstExit_distance_P6M4` 把 `time e⁻ < a` 放宽为
`time e⁻ ≤ a`；结论同：`∀ s ∈ [a, t]，d_s(p, q) ≤ d_t(p, q) + (8/ℓ)(t − s)`。 -/
theorem ObservedHistory.firstExit_distance_closed_P6DW (H : ObservedHistory.{u})
    (e : Fin H.eventCount) {a t ℓ : ℝ} (hℓ : 0 < ℓ) (hat : a ≤ t) (ha : H.time e.castSucc ≤ a)
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
  -- 区间 `[s, t]`（`a ≤ s`）上 Good ⇒ I.8.3(b)（闭左端）
  have hdist : ∀ s, a ≤ s → s ≤ t →
      (∀ s' ∈ Ioo s t, riemannianEDistOf ((H.event e).incoming.flow.base.metric s') p q < X) →
      riemannianEDistOf ((H.event e).incoming.flow.base.metric s) p q ≤
        riemannianEDistOf ((H.event e).incoming.flow.base.metric t) p q +
          ENNReal.ofReal ((8 / ℓ) * (t - s)) := by
    intro s has hst hgood
    exact edist_le_add_of_endpoint_ricci_solution_C11D (H.event e).incoming.flow
      (H.event e).incoming.equation hst hℓ
      (fun _ hr => ⟨(ha.trans has).trans hr.1, lt_of_le_of_lt hr.2 ht⟩)
      (fun _ hr => ⟨(ha.trans has).trans_lt hr.1, hr.2.trans ht⟩) p q
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
  -- 首出时刻 = `a`（USC 左延拓，在 `[(a + τ⋆)/2, τ⋆]` 上，避开左端点）
  have hstar_eq : sInf S = a := by
    by_contra hne'
    have hlt : a < sInf S := lt_of_le_of_ne hastar (Ne.symm hne')
    have hmid : (a + sInf S) / 2 < sInf S := by linarith
    have hmid' : a < (a + sInf S) / 2 := by linarith
    obtain ⟨s₁, has₁, hs₁, hnear⟩ := edist_lt_near_left_P6L4 (H.event e).incoming.flow
      (H.event e).incoming.equation hmid
      (fun r hr => ⟨(ha.trans_lt hmid').trans_le hr.1, lt_of_le_of_lt (hr.2.trans hstart) ht⟩)
      p q hstar_lt
    have hs₁S : s₁ ∈ S := by
      refine ⟨hmid'.le.trans has₁, hs₁.le.trans hstart, fun s' hs' => ?_⟩
      rcases le_or_gt s' (sInf S) with h | h
      · exact hnear s' ⟨hs'.1, h⟩
      · exact hup s' ⟨h, hs'.2⟩
    have := csInf_le hbdd hs₁S
    linarith
  intro s hs
  refine hdist s hs.1 hs.2 fun s' hs' => hstarS.2.2 s' ⟨?_, hs'.2.le⟩
  rw [hstar_eq]
  exact hs.1.trans hs'.1.le

/-- **基点窗口 seed 距离（event 层，`_P6DW`）**：slab `e`、窗顶 `σ < time e⁺`、`y, x` 于 `g(σ)` 满足
`d_σ(y, x) < D/√R`、`d_σ(O, y) ≤ dσ = A`；窗 `τ ∈ [σ − T/R, σ]`（`time e⁻ ≤ τ`）；K0 种子 + pinching +
**条件** U 端标量界 `hscal`（开窗 `s ∈ (σ − T/R, σ)`、`d_s(O, x) ≤ dσ + L/√R` 时，`B_s(x, 1/√(CR))` 上
`R ≤ CR`）+ `L ≥ D⁺ + 8√K T⁺`、`2500 K ≤ R r²`（`K := max 1 (2√3(C/2 + max C (2e⁴)))`）
⇒ `d_τ(O, x) ≤ dσ + L/√R`。 -/
theorem ObservedHistory.seed_window_firstExit_P6DW (H : ObservedHistory.{u})
    {Tn aSeed : Icc (0 : ℝ) H.horizon} (haT : aSeed ≤ Tn) {pT : (H.stageAt Tn).Carrier} {r : ℝ}
    (hsmall : GC.LongTime.hasSmallParabolicCurvature H Tn pT r)
    (hclock : (aSeed : ℝ) = (Tn : ℝ) - r ^ 2)
    (seedTrace : BackwardPointTrace H (H.activeStage aSeed) (H.activeStage Tn)
      (H.activeStage_mono haT) pT)
    {a₀ : ℝ} (ha₀ : 0 ≤ a₀)
    (hpin : ∀ (t : Icc (0 : ℝ) H.horizon) (x : (H.stageAt t).Carrier),
      InFixedHamiltonIveyRegion (H.stageMetric (H.activeStage t) t) (a₀ + t) x)
    (e : Fin H.eventCount) (h1 : H.activeStage aSeed ≤ e.castSucc)
    (h2 : e.castSucc ≤ H.activeStage Tn) (y x : (H.stage e.castSucc).Carrier)
    {dσ : ℝ≥0∞} {A R L C D T τ σ : ℝ} (hdσ : dσ = ENNReal.ofReal A) (hA : 0 ≤ A)
    (hR : 0 < R) (hC1 : 1 ≤ C)
    (hRr : 2500 * max 1 (2 * Real.sqrt 3 * (C / 2 + max C (2 * Real.exp 4))) ≤ R * r ^ 2)
    (hL : max D 0 +
      8 * Real.sqrt (max 1 (2 * Real.sqrt 3 * (C / 2 + max C (2 * Real.exp 4)))) * max T 0 ≤ L)
    (hyO : riemannianEDistOf ((H.event e).incoming.flow.base.metric σ)
      (seedTrace.point e.castSucc h1 h2) y ≤ dσ)
    (hxy : x ∈ riemannianBallOf ((H.event e).incoming.flow.base.metric σ) y (D / Real.sqrt R))
    (hτT : σ - T / R ≤ τ) (hτσ : τ ≤ σ) (hτ1 : H.time e.castSucc ≤ τ)
    (hσ2 : σ < H.time e.succ) (haτ : (aSeed : ℝ) ≤ τ) (hσT : σ ≤ Tn) (hRτ : 1 ≤ R * τ)
    (hscal : ∀ s : ℝ, σ - T / R < s → s < σ → H.time e.castSucc < s →
      riemannianEDistOf ((H.event e).incoming.flow.base.metric s)
          (seedTrace.point e.castSucc h1 h2) x ≤ dσ + ENNReal.ofReal (L / Real.sqrt R) →
      ∀ z : (H.stage e.castSucc).Carrier,
        riemannianEDistOf ((H.event e).incoming.flow.base.metric s) x z <
          ENNReal.ofReal (1 / Real.sqrt (C * R)) →
        (H.event e).incoming.flow.scalar s z ≤ C * R) :
    riemannianEDistOf ((H.event e).incoming.flow.base.metric τ)
        (seedTrace.point e.castSucc h1 h2) x ≤ dσ + ENNReal.ofReal (L / Real.sqrt R) := by
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
  have hyx : riemannianEDistOf ((H.event e).incoming.flow.base.metric σ) y x <
      ENNReal.ofReal (max D 0 / Real.sqrt R) :=
    lt_of_lt_of_le hxy (ENNReal.ofReal_le_ofReal
      (div_le_div_of_nonneg_right (le_max_left _ _) hsR.le))
  have hyO' : riemannianEDistOf ((H.event e).incoming.flow.base.metric σ)
      (seedTrace.point e.castSucc h1 h2) y ≤ ENNReal.ofReal A := hdσ ▸ hyO
  have hd2 : riemannianEDistOf ((H.event e).incoming.flow.base.metric σ)
        (seedTrace.point e.castSucc h1 h2) y +
      riemannianEDistOf ((H.event e).incoming.flow.base.metric σ) y x <
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
  have hmargin : riemannianEDistOf ((H.event e).incoming.flow.base.metric σ)
        (seedTrace.point e.castSucc h1 h2) x +
      ENNReal.ofReal (8 / (1 / Real.sqrt K / Real.sqrt R) * (σ - τ)) <
      dσ + ENNReal.ofReal (L / Real.sqrt R) :=
    calc riemannianEDistOf ((H.event e).incoming.flow.base.metric σ)
          (seedTrace.point e.castSucc h1 h2) x +
          ENNReal.ofReal (8 / (1 / Real.sqrt K / Real.sqrt R) * (σ - τ)) ≤
        (riemannianEDistOf ((H.event e).incoming.flow.base.metric σ)
            (seedTrace.point e.castSucc h1 h2) y +
          riemannianEDistOf ((H.event e).incoming.flow.base.metric σ) y x) +
          ENNReal.ofReal (8 / (1 / Real.sqrt K / Real.sqrt R) * (σ - τ)) :=
          add_le_add (riemannianEDistOf_triangle _ _ _ _) le_rfl
      _ < ENNReal.ofReal A + ENNReal.ofReal (max D 0 / Real.sqrt R) +
          ENNReal.ofReal (8 / (1 / Real.sqrt K / Real.sqrt R) * (σ - τ)) :=
          ENNReal.add_lt_add_right ENNReal.ofReal_ne_top hd2
      _ ≤ dσ + ENNReal.ofReal (L / Real.sqrt R) := hd3
  -- 首出时刻（闭左端）
  have hfe := H.firstExit_distance_closed_P6DW e hℓ hτσ hτ1 hσ2
    (seedTrace.point e.castSucc h1 h2) x hmargin
    (fun s hs hgood => H.ricci_seed_or_scal_P6L4 haT hsmall hclock seedTrace ha₀ hpin e h1 h2 x
      hR hℓ hKℓ hℓr hKr hC hKC (hτ1.trans_lt hs.1) (hs.2.trans hσ2) (haτ.trans hs.1.le)
      (hs.2.le.trans hσT) (hRτ.trans (mul_le_mul_of_nonneg_left hs.1.le hR.le))
      (fun z hz => hscal s (lt_of_le_of_lt hτT hs.1) hs.2 (hτ1.trans_lt hs.1) hgood.le z
        (hz.trans_le (ENNReal.ofReal_le_ofReal hℓCR)))) τ ⟨le_rfl, hτσ⟩
  exact (lt_of_le_of_lt hfe hmargin).le

/-- **stage 指标形 ⇒ event 层（`_P6DW`）**：`kv = kσ = e⁻`（同 slab）、`tr` 单点 trace（`tr.point kv = x`）；
度量 `stageMetric kσ ·` = incoming flow 度量；把 `seed_window_firstExit_P6DW` 搬到 hdistW 的 stage 形。 -/
theorem ObservedHistory.distW_transport_P6DW (H : ObservedHistory.{u})
    {Tn aSeed : Icc (0 : ℝ) H.horizon} (haT : aSeed ≤ Tn) {pT : (H.stageAt Tn).Carrier} {r : ℝ}
    (hsmall : GC.LongTime.hasSmallParabolicCurvature H Tn pT r)
    (hclock : (aSeed : ℝ) = (Tn : ℝ) - r ^ 2)
    (seedTrace : BackwardPointTrace H (H.activeStage aSeed) (H.activeStage Tn)
      (H.activeStage_mono haT) pT)
    {a₀ : ℝ} (ha₀ : 0 ≤ a₀)
    (hpin : ∀ (t : Icc (0 : ℝ) H.horizon) (x : (H.stageAt t).Carrier),
      InFixedHamiltonIveyRegion (H.stageMetric (H.activeStage t) t) (a₀ + t) x)
    {kv kσ : Fin (H.eventCount + 1)} (hkk : kv = kσ) (e : Fin H.eventCount)
    (he : kσ = e.castSucc) (h1v : H.activeStage aSeed ≤ kv) (h2v : kv ≤ H.activeStage Tn)
    (h1σ : H.activeStage aSeed ≤ kσ) (h2σ : kσ ≤ H.activeStage Tn) (hle : kv ≤ kσ)
    (y x : (H.stage kσ).Carrier) (tr : BackwardPointTrace H kv kσ hle x)
    {A R L C D T v σ : ℝ}
    (hdσ : riemannianEDistOf (H.stageMetric kσ σ) (seedTrace.point kσ h1σ h2σ) y =
      ENNReal.ofReal A) (hA : 0 ≤ A) (hR : 0 < R) (hC1 : 1 ≤ C)
    (hRr : 2500 * max 1 (2 * Real.sqrt 3 * (C / 2 + max C (2 * Real.exp 4))) ≤ R * r ^ 2)
    (hL : max D 0 +
      8 * Real.sqrt (max 1 (2 * Real.sqrt 3 * (C / 2 + max C (2 * Real.exp 4)))) * max T 0 ≤ L)
    (hxy : x ∈ riemannianBallOf (H.stageMetric kσ σ) y (D / Real.sqrt R))
    (hvT : σ - T / R ≤ v) (hvσ : v ≤ σ) (hv1 : H.time kσ ≤ v) (hσ2 : σ < H.time e.succ)
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
  have hpt : tr.point e.castSucc le_rfl hle = x := tr.endpoint_eq
  rw [hpt]
  simp only [ObservedHistory.stageMetric_castSucc_apply] at hdσ hxy hscal ⊢
  exact H.seed_window_firstExit_P6DW haT hsmall hclock seedTrace ha₀ hpin e h1σ h2σ y x hdσ hA
    hR hC1 hRr hL le_rfl hxy hvT hvσ hv1 hσ2 hav hσT hRv
    (fun s hs1 hs2 hs3 hs4 z hz => hscal s hs1 hs2 hs3 hs4 z hz)

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
