import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.Local.HclosFirstExit_P6L4

/-!
# final slab 的首出时刻核（S-CH11-HSCALU2 G1a，后缀 `_P6M6`）

`firstExit_distance_P6M4` / `ricci_seed_or_scal_P6L4` / `seed_closure_firstExit_P6L4` 的
**final slab 孪生**
（stage `Fin.last`，度量 `H.stageMetric (Fin.last _) s`，窗口 `time last < τ ≤ v < horizon`）。
`hclosGF`（HCLOSEF `hcloseF⁺` 的 final seed closure binder）的生产核；U 端条件标量界仍是显式前提
（`HU_final_P6M6` 在 `P6HscalUFinalP6M6` 登记）。

* `edist_le_add_of_final_ricci_P6M6`：Perelman I.8.3(b) 的 final slab 形
  （`smooth_distance_distortion_C11D` 的 `k = Fin.last` 实例；`hnext` 空真）。
* `firstExit_distance_final_P6M6`：`firstExit_distance_P6M4` 逐步孪生（USC 一步用 `(finalSlab hlt).flow`，
  `time last < a`，`t < horizon`）。
* `ricci_seed_or_scal_final_P6M6`：Good 时刻端点 Ricci 界（K0 种子端 `seed_rmNorm_le_of_smallParabolic_C11G`
  与 pinching `inFixedHI_stage_C11G` 本来就对 stage `k` 泛型，`k := Fin.last`）。
* `seed_closure_firstExit_final_P6M6`：`seed_closure_firstExit_P6L4` 的 final 孪生。
-/

set_option autoImplicit false

noncomputable section

open Set Filter
open DifferentialGeometry.Geometry.Curvature DifferentialGeometry.Tensor0SBundle
open scoped Manifold ContDiff Topology ENNReal NNReal

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

universe u

/-- **I.8.3(b) final slab 形（`_P6M6`）**：`time last ≤ s ≤ t ≤ horizon`，`(s, t)` 上两端 `ℓ`-球
`Ric ≤ (3/ℓ²) g` ⇒ `d_s(p, q) ≤ d_t(p, q) + (8/ℓ)(t − s)`（stage `Fin.last`）。 -/
theorem ObservedHistory.edist_le_add_of_final_ricci_P6M6 (H : ObservedHistory.{u})
    {s t ℓ : ℝ} (hℓ : 0 < ℓ) (hst : s ≤ t) (hs : H.time (Fin.last H.eventCount) ≤ s)
    (ht : t ≤ H.horizon) (p q : (H.stage (Fin.last H.eventCount)).Carrier)
    (hRic : ∀ r ∈ Ioo s t, ∀ z : (H.stage (Fin.last H.eventCount)).Carrier,
      ∀ ξ : TangentSpace ThreeModel z,
      (riemannianEDistOf (H.stageMetric (Fin.last H.eventCount) r) p z < ENNReal.ofReal ℓ ∨
        riemannianEDistOf (H.stageMetric (Fin.last H.eventCount) r) q z < ENNReal.ofReal ℓ) →
      ricciTensor (H.stageMetric (Fin.last H.eventCount) r) z ξ ξ ≤
        (3 / ℓ ^ 2) * (H.stageMetric (Fin.last H.eventCount) r).inner z ξ ξ) :
    riemannianEDistOf (H.stageMetric (Fin.last H.eventCount) s) p q ≤
      riemannianEDistOf (H.stageMetric (Fin.last H.eventCount) t) p q +
        ENNReal.ofReal ((8 / ℓ) * (t - s)) :=
  H.smooth_distance_distortion_C11D (Fin.last H.eventCount) hℓ hst hs
    (fun e he => absurd he (Fin.castSucc_lt_last e).ne') ht p q hRic

/-- **首出时刻距离引理（final slab，`_P6M6`）**：`firstExit_distance_P6M4` 的 final 孪生。条件曲率 `hRic`
（只在 `d_s(p, q) < X` 的时刻）+ 初始余量 `d_t + (8/ℓ)(t − a) < X` ⇒ `[a, t]` 全体时刻
`d_s(p, q) ≤ d_t(p, q) + (8/ℓ)(t − s)`（`time last < a ≤ t < horizon`）。 -/
theorem ObservedHistory.firstExit_distance_final_P6M6 (H : ObservedHistory.{u})
    {a t ℓ : ℝ} (hℓ : 0 < ℓ) (hat : a ≤ t) (ha : H.time (Fin.last H.eventCount) < a)
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
  have hlt : H.time (Fin.last H.eventCount) < H.horizon := lt_of_lt_of_le ha (hat.trans ht.le)
  -- 区间 `[s, t]`（`a ≤ s`）上 Good ⇒ I.8.3(b)
  have hdist : ∀ s, a ≤ s → s ≤ t →
      (∀ s' ∈ Ioo s t, riemannianEDistOf (H.stageMetric (Fin.last H.eventCount) s') p q < X) →
      riemannianEDistOf (H.stageMetric (Fin.last H.eventCount) s) p q ≤
        riemannianEDistOf (H.stageMetric (Fin.last H.eventCount) t) p q +
          ENNReal.ofReal ((8 / ℓ) * (t - s)) := by
    intro s has hst hgood
    exact H.edist_le_add_of_final_ricci_P6M6 hℓ hst (ha.le.trans has) ht.le p q
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
  -- 首出时刻 = `a`（USC 左延拓，用 `(finalSlab hlt).flow`）
  have hstar_eq : sInf S = a := by
    by_contra hne'
    have hlt' : a < sInf S := lt_of_le_of_ne hastar (Ne.symm hne')
    have hstar_lt' : riemannianEDistOf ((H.finalSlab hlt).flow.base.metric (sInf S)) p q < X := by
      rw [← ObservedHistory.stageMetric_last_of_lt (H := H) (h := hlt)]
      exact hstar_lt
    obtain ⟨s₁, has₁, hs₁, hnear⟩ := edist_lt_near_left_P6L4 (H.finalSlab hlt).flow
      (H.finalSlab hlt).equation hlt'
      (fun r hr => ⟨ha.trans_le hr.1, lt_of_le_of_lt (hr.2.trans hstart) ht⟩) p q hstar_lt'
    have hs₁S : s₁ ∈ S := by
      refine ⟨has₁, hs₁.le.trans hstart, fun s' hs' => ?_⟩
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

/-- **Good 时刻的端点 Ricci 界（final slab，`_P6M6`）**：`ricci_seed_or_scal_P6L4` 的 final 孪生
（stage `Fin.last`；`time last < s`，`activeStage s = last`）。 -/
theorem ObservedHistory.ricci_seed_or_scal_final_P6M6 (H : ObservedHistory.{u})
    {Tn aSeed : Icc (0 : ℝ) H.horizon} (haT : aSeed ≤ Tn) {pT : (H.stageAt Tn).Carrier} {r : ℝ}
    (hsmall : GC.LongTime.hasSmallParabolicCurvature H Tn pT r)
    (hclock : (aSeed : ℝ) = (Tn : ℝ) - r ^ 2)
    (seedTrace : BackwardPointTrace H (H.activeStage aSeed) (H.activeStage Tn)
      (H.activeStage_mono haT) pT)
    {a₀ : ℝ} (ha₀ : 0 ≤ a₀)
    (hpin : ∀ (t : Icc (0 : ℝ) H.horizon) (x : (H.stageAt t).Carrier),
      InFixedHamiltonIveyRegion (H.stageMetric (H.activeStage t) t) (a₀ + t) x)
    (h1 : H.activeStage aSeed ≤ Fin.last H.eventCount)
    (h2 : Fin.last H.eventCount ≤ H.activeStage Tn) (x : (H.stage (Fin.last H.eventCount)).Carrier)
    {Q K C ℓ s : ℝ} (hQ : 0 < Q) (hℓ : 0 < ℓ) (hKℓ : K * ℓ ^ 2 ≤ 1) (hℓr : ℓ ≤ r / 50)
    (hKr : 1 / r ^ 2 ≤ K) (hC : 0 ≤ C)
    (hKC : 2 * Real.sqrt 3 * (C / 2 + max C (2 * Real.exp 4)) * Q ≤ K)
    (hs1 : H.time (Fin.last H.eventCount) < s) (has : (aSeed : ℝ) ≤ s)
    (hsT : s ≤ Tn) (hQs : 1 ≤ Q * s)
    (hscal : ∀ z : (H.stage (Fin.last H.eventCount)).Carrier,
      riemannianEDistOf (H.stageMetric (Fin.last H.eventCount) s) x z < ENNReal.ofReal ℓ →
      metricScalarAt (H.stageMetric (Fin.last H.eventCount) s) z ≤ C * Q) :
    ∀ z : (H.stage (Fin.last H.eventCount)).Carrier, ∀ ξ : TangentSpace ThreeModel z,
      (riemannianEDistOf (H.stageMetric (Fin.last H.eventCount) s)
          (seedTrace.point (Fin.last H.eventCount) h1 h2) z < ENNReal.ofReal ℓ ∨
        riemannianEDistOf (H.stageMetric (Fin.last H.eventCount) s) x z < ENNReal.ofReal ℓ) →
      ricciTensor (H.stageMetric (Fin.last H.eventCount) s) z ξ ξ ≤
        (3 / ℓ ^ 2) * (H.stageMetric (Fin.last H.eventCount) s).inner z ξ ξ := by
  intro z ξ hz
  have hs0 : 0 < s := by
    by_contra hneg
    have hle := not_lt.mp hneg
    nlinarith
  let τI : Icc (0 : ℝ) H.horizon := ⟨s, hs0.le, hsT.trans Tn.2.2⟩
  have hk : H.activeStage τI = Fin.last H.eventCount :=
    H.activeStage_eq_last_of_time_last_le τI hs1.le
  have hK : Real.sqrt (normSq0S (H.stageMetric (Fin.last H.eventCount) s) z 4
      (metricRm04At (H.stageMetric (Fin.last H.eventCount) s) z)) ≤ K := by
    rcases hz with hz | hz
    · have hzr : riemannianEDistOf (H.stageMetric (Fin.last H.eventCount) τI)
          (seedTrace.point (Fin.last H.eventCount) h1 h2) z < ENNReal.ofReal (r / 50) :=
        hz.trans_le (ENNReal.ofReal_le_ofReal hℓr)
      have h := H.seed_rmNorm_le_of_smallParabolic_C11G haT hsmall hclock seedTrace τI has hsT
        (Fin.last H.eventCount) hk h1 h2 z hzr
      exact h.trans hKr
    · have hfix := H.inFixedHI_stage_C11G hpin τI (Fin.last H.eventCount) hk z
      have hsc : metricScalarAt (H.stageMetric (Fin.last H.eventCount) s) z ≤ C * Q :=
        hscal z hz
      exact (sqrt_rmNormSq_le_of_HI_scalar_C11G _ z ha₀ hs0 hQ hQs hC hfix hsc).trans hKC
  have hg : 0 ≤ (H.stageMetric (Fin.last H.eventCount) s).inner z ξ ξ :=
    metric_inner_self_nonneg _ z ξ
  have hK' : K ≤ 1 / ℓ ^ 2 := by
    rw [le_div_iff₀ (pow_pos hℓ 2)]
    exact hKℓ
  calc ricciTensor (H.stageMetric (Fin.last H.eventCount) s) z ξ ξ ≤
        3 * K * (H.stageMetric (Fin.last H.eventCount) s).inner z ξ ξ :=
        ricciTensor_le_of_sqrt_rmNormSq_le_C11D _ z hK ξ
    _ ≤ (3 / ℓ ^ 2) * (H.stageMetric (Fin.last H.eventCount) s).inner z ξ ξ := by
      apply mul_le_mul_of_nonneg_right _ hg
      calc 3 * K ≤ 3 * (1 / ℓ ^ 2) := by linarith
        _ = 3 / ℓ ^ 2 := by ring

/-- **单 history seed closure（首出时刻，final slab，`_P6M6`）**：`seed_closure_firstExit_P6L4` 的 final 孪生。
final slab 内 `Q := R(v, w) ≥ R`、`x ∈ B_v(w, Rad/√Q)`、`d_v(O, w) ≤ d_σ + L/(2√R)`、
窗 `τ ∈ [v − B/Q, v]`（`time last < τ`，`v < horizon`）；K0 种子 + pinching + **条件** U 端标量界 `hscal`（只在
`d_s(O, x) ≤ d_σ + L/√R` 的时刻）⇒ `d_τ(O, x) ≤ d_σ + L/√R`。 -/
theorem ObservedHistory.seed_closure_firstExit_final_P6M6 (H : ObservedHistory.{u})
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
    (w x : (H.stage (Fin.last H.eventCount)).Carrier)
    {dσ : ℝ≥0∞} {A R Q L C Rad B τ v : ℝ} (hdσ : dσ = ENNReal.ofReal A) (hA : 0 ≤ A)
    (hR : 0 < R) (hRQ : R ≤ Q) (hC1 : 1 ≤ C)
    (hRr : 2500 * max 1 (2 * Real.sqrt 3 * (C / 2 + max C (2 * Real.exp 4))) ≤ R * r ^ 2)
    (hL : 2 * max Rad 0 +
      16 * Real.sqrt (max 1 (2 * Real.sqrt 3 * (C / 2 + max C (2 * Real.exp 4)))) * max B 0 ≤ L)
    (hwv : riemannianEDistOf (H.stageMetric (Fin.last H.eventCount) v)
      (seedTrace.point (Fin.last H.eventCount) h1 h2) w ≤
        dσ + ENNReal.ofReal (L / 2 / Real.sqrt R))
    (hxw : x ∈ riemannianBallOf (H.stageMetric (Fin.last H.eventCount) v) w
      (Rad / Real.sqrt Q))
    (hτB : v - B / Q ≤ τ) (hτv : τ ≤ v) (hτ1 : H.time (Fin.last H.eventCount) < τ)
    (hv2 : v < H.horizon) (haτ : (aSeed : ℝ) ≤ τ) (hvT : v ≤ Tn) (hQτ : 1 ≤ Q * τ)
    (hscal : ∀ s : ℝ, v - B / Q ≤ s → s ≤ v → H.time (Fin.last H.eventCount) < s →
      riemannianEDistOf (H.stageMetric (Fin.last H.eventCount) s)
          (seedTrace.point (Fin.last H.eventCount) h1 h2) x ≤
        dσ + ENNReal.ofReal (L / Real.sqrt R) →
      ∀ z : (H.stage (Fin.last H.eventCount)).Carrier,
        riemannianEDistOf (H.stageMetric (Fin.last H.eventCount) s) x z <
          ENNReal.ofReal (1 / Real.sqrt (C * Q)) →
        metricScalarAt (H.stageMetric (Fin.last H.eventCount) s) z ≤ C * Q) :
    riemannianEDistOf (H.stageMetric (Fin.last H.eventCount) τ)
        (seedTrace.point (Fin.last H.eventCount) h1 h2) x ≤
      dσ + ENNReal.ofReal (L / Real.sqrt R) := by
  set K := max 1 (2 * Real.sqrt 3 * (C / 2 + max C (2 * Real.exp 4))) with hKdef
  have hK1 : 1 ≤ K := le_max_left _ _
  have hQ : 0 < Q := hR.trans_le hRQ
  have hC : 0 ≤ C := by linarith
  have h3 : 1 ≤ Real.sqrt 3 := by
    rw [show (1 : ℝ) = Real.sqrt 1 by simp]
    exact Real.sqrt_le_sqrt (by norm_num)
  have hCK : C ≤ K := by
    refine le_trans ?_ (le_max_right _ _)
    have hm : C ≤ max C (2 * Real.exp 4) := le_max_left _ _
    nlinarith
  have hr : 0 < r := hsmall.1
  have hQr : 2500 * K ≤ Q * r ^ 2 := hRr.trans (mul_le_mul_of_nonneg_right hRQ (sq_nonneg r))
  obtain ⟨hℓr, hKr, hKℓ, -⟩ := seq_scale_bounds_C11G hK1 hQ hr hQr
  have hsK : 0 < Real.sqrt K := Real.sqrt_pos.2 (by linarith)
  have hsQ : 0 < Real.sqrt Q := Real.sqrt_pos.2 hQ
  have hsR : 0 < Real.sqrt R := Real.sqrt_pos.2 hR
  have hℓ : 0 < 1 / Real.sqrt K / Real.sqrt Q := by positivity
  have hℓCQ : 1 / Real.sqrt K / Real.sqrt Q ≤ 1 / Real.sqrt (C * Q) := by
    have hCQ : Real.sqrt (C * Q) ≤ Real.sqrt K * Real.sqrt Q := by
      rw [← Real.sqrt_mul (by linarith)]
      exact Real.sqrt_le_sqrt (mul_le_mul_of_nonneg_right hCK hQ.le)
    rw [div_div]
    exact one_div_le_one_div_of_le (Real.sqrt_pos.2 (by positivity)) hCQ
  have hKC : 2 * Real.sqrt 3 * (C / 2 + max C (2 * Real.exp 4)) * Q ≤ K * Q :=
    mul_le_mul_of_nonneg_right (le_max_right _ _) hQ.le
  have hRad0 : 0 ≤ max Rad 0 := le_max_right _ _
  have hB0 : 0 ≤ max B 0 := le_max_right _ _
  have hL0 : 0 ≤ L := by
    have : 0 ≤ 16 * Real.sqrt K * max B 0 := by positivity
    linarith
  -- 漂移与初始余量
  have hdrift := drift_le_P6L4 (by linarith : (0 : ℝ) < K) hR hRQ hτB
  have hdr0 : 0 ≤ 8 / (1 / Real.sqrt K / Real.sqrt Q) * (v - τ) :=
    mul_nonneg (by positivity) (by linarith)
  have hrad' : Rad / Real.sqrt Q ≤ max Rad 0 / Real.sqrt R :=
    (div_le_div_of_nonneg_right (le_max_left _ _) hsQ.le).trans
      (div_le_div_of_nonneg_left hRad0 hsR (Real.sqrt_le_sqrt hRQ))
  have hwx : riemannianEDistOf (H.stageMetric (Fin.last H.eventCount) v) w x <
      ENNReal.ofReal (max Rad 0 / Real.sqrt R) :=
    lt_of_lt_of_le hxw (ENNReal.ofReal_le_ofReal hrad')
  have hwv' : riemannianEDistOf (H.stageMetric (Fin.last H.eventCount) v)
      (seedTrace.point (Fin.last H.eventCount) h1 h2) w ≤
        ENNReal.ofReal (A + L / 2 / Real.sqrt R) := by
    rw [ENNReal.ofReal_add hA (by positivity), ← hdσ]
    exact hwv
  have hd2 : riemannianEDistOf (H.stageMetric (Fin.last H.eventCount) v)
        (seedTrace.point (Fin.last H.eventCount) h1 h2) w +
      riemannianEDistOf (H.stageMetric (Fin.last H.eventCount) v) w x <
      ENNReal.ofReal (A + L / 2 / Real.sqrt R) + ENNReal.ofReal (max Rad 0 / Real.sqrt R) :=
    ENNReal.add_lt_add_of_le_of_lt (ne_top_of_le_ne_top ENNReal.ofReal_ne_top hwv') hwv' hwx
  have hd3 : ENNReal.ofReal (A + L / 2 / Real.sqrt R) +
        ENNReal.ofReal (max Rad 0 / Real.sqrt R) +
        ENNReal.ofReal (8 / (1 / Real.sqrt K / Real.sqrt Q) * (v - τ)) ≤
      dσ + ENNReal.ofReal (L / Real.sqrt R) := by
    rw [← ENNReal.ofReal_add (by positivity) (by positivity),
      ← ENNReal.ofReal_add (by positivity) hdr0, hdσ, ← ENNReal.ofReal_add hA (by positivity)]
    apply ENNReal.ofReal_le_ofReal
    have hsum : L / 2 / Real.sqrt R + max Rad 0 / Real.sqrt R +
        8 * Real.sqrt K * max B 0 / Real.sqrt R =
        (L / 2 + max Rad 0 + 8 * Real.sqrt K * max B 0) / Real.sqrt R := by ring
    have hle : (L / 2 + max Rad 0 + 8 * Real.sqrt K * max B 0) / Real.sqrt R ≤
        L / Real.sqrt R := div_le_div_of_nonneg_right (by linarith) hsR.le
    linarith
  have hmargin : riemannianEDistOf (H.stageMetric (Fin.last H.eventCount) v)
        (seedTrace.point (Fin.last H.eventCount) h1 h2) x +
      ENNReal.ofReal (8 / (1 / Real.sqrt K / Real.sqrt Q) * (v - τ)) <
      dσ + ENNReal.ofReal (L / Real.sqrt R) :=
    calc riemannianEDistOf (H.stageMetric (Fin.last H.eventCount) v)
          (seedTrace.point (Fin.last H.eventCount) h1 h2) x +
          ENNReal.ofReal (8 / (1 / Real.sqrt K / Real.sqrt Q) * (v - τ)) ≤
        (riemannianEDistOf (H.stageMetric (Fin.last H.eventCount) v)
            (seedTrace.point (Fin.last H.eventCount) h1 h2) w +
          riemannianEDistOf (H.stageMetric (Fin.last H.eventCount) v) w x) +
          ENNReal.ofReal (8 / (1 / Real.sqrt K / Real.sqrt Q) * (v - τ)) :=
          add_le_add (riemannianEDistOf_triangle _ _ _ _) le_rfl
      _ < ENNReal.ofReal (A + L / 2 / Real.sqrt R) +
            ENNReal.ofReal (max Rad 0 / Real.sqrt R) +
          ENNReal.ofReal (8 / (1 / Real.sqrt K / Real.sqrt Q) * (v - τ)) :=
          ENNReal.add_lt_add_right ENNReal.ofReal_ne_top hd2
      _ ≤ dσ + ENNReal.ofReal (L / Real.sqrt R) := hd3
  -- 首出时刻
  have hfe := H.firstExit_distance_final_P6M6 hℓ hτv hτ1 hv2
    (seedTrace.point (Fin.last H.eventCount) h1 h2) x
    hmargin (fun s hs hgood => H.ricci_seed_or_scal_final_P6M6 haT hsmall hclock seedTrace ha₀
      hpin h1 h2 x hQ hℓ hKℓ hℓr hKr hC hKC (hτ1.trans hs.1)
      (haτ.trans hs.1.le) (hs.2.le.trans hvT)
      (hQτ.trans (mul_le_mul_of_nonneg_left hs.1.le hQ.le))
      (fun z hz => hscal s (hτB.trans hs.1.le) hs.2.le (hτ1.trans hs.1) hgood.le z
        (hz.trans_le (ENNReal.ofReal_le_ofReal hℓCQ)))) τ ⟨le_rfl, hτv⟩
  exact (lt_of_le_of_lt hfe hmargin).le

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
