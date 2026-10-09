import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.P6PickedBallSeedClosureLocalC11SC2
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.P6HUVFinalP6HF

/-!
# GUARDWIRE-FINAL G3：U 端窗口标量界（局域导数版）的 final-slab 孪生（`_P6GWF`）

GUARDWIRE G2b `hseedG` 的 repair target 第 3 项：SEEDCL2
`windowScal_of_pickedTop_local_C11SC2`（+ `deriv_of_hgood_slab_Cg_C11SC2`、
`ObservedHistory.scalar_le_two_mul_of_localDeriv_C11SC2`）→ final slab 形
（flow = `(K.finalSlab h).restrictIncoming le_rfl h le_rfl`，`time last < s ≤ v < horizon`，点在
`K.stage last`）。hgood 的 stage 桥由 `stageMetric_castSucc_apply` + `activeStage_eq_castSucc` 换成
`activeStage_eq_last_of_time_last_le` + `stageMetric_last_restrict_P6HF`
（= `stageMetric_last_of_lt` + 定义等；ANCHOR5 final 文件已用的两条），点对齐用 P6HF 的
`edist_stage_eq_last_P6HF` / `scalar_stage_eq_last_P6HF`。

* `scalar_le_two_mul_of_localDeriv_final_P6GWF`：worldline ceiling ODE，
  `(H.event j).incoming.equation` → restrict final slab `equation`（定义域 `Ico (time last) horizon`），
  证明体逐字。
* `deriv_of_stage_last_P6GWF` / `deriv_of_hgood_final_P6GWF`：hgood 时间分量
  （`HasSpatialCanonicalTimeControl.2`）的 final 形；`τ < horizon` 直接是 final slab 的上端。
* `windowScal_of_pickedTop_local_final_P6GWF`（主定理）：证明体逐字；梯度核 =
  `RetainedCoreHistory.gradient_of_hgood_final_P6HF`（树内已有），局部传播
  `scalar_le_on_ball_of_gradient_bound_P6L` 对 flow 通用。

无额外前提；无 `DerivativeBoundBefore` / `qcan` / hstop / Hamilton–Ivey（与 SEEDCL2 同一防循环证书）。
-/

set_option autoImplicit false

noncomputable section

open Set Filter Function
open DifferentialGeometry.Geometry.Curvature DifferentialGeometry.Tensor0SBundle
open DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood
open scoped Manifold NNReal Topology ContDiff ENNReal

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

universe u

namespace RetainedCoreHistory

/-- **worldline ceiling ODE（final slab，`_P6GWF`，PROVED）**：SEEDCL2
`scalar_le_two_mul_of_localDeriv_C11SC2` 的 final 孪生。`[s, v] ⊆ [time last, horizon)`、点 `y` 不动；
导数只在 `M < R(r, y)` 处要；`R(v, y) ≤ M`、`Ctime · M · (v − s) ≤ 1/2` ⇒ `[s, v]` 上 `R(·, y) ≤ 2M`。
证明体逐字。 -/
theorem scalar_le_two_mul_of_localDeriv_final_P6GWF (K : RetainedCoreHistory.{u})
    (h : K.time (Fin.last K.eventCount) < K.horizon) {Ctime : ℝ≥0} {s v M : ℝ} (hM : 0 < M)
    (hs0 : K.time (Fin.last K.eventCount) ≤ s) (hsv : s ≤ v) (hv2 : v < K.horizon)
    (y : (K.stage (Fin.last K.eventCount)).Carrier)
    (hloc : ∀ r ∈ Ioo s v, M < ((K.finalSlab h).restrictIncoming le_rfl h le_rfl).flow.scalar r y →
      |derivWithin (fun w => ((K.finalSlab h).restrictIncoming le_rfl h le_rfl).flow.scalar w y)
          (Iic r) r| ≤
        Ctime * ((K.finalSlab h).restrictIncoming le_rfl h le_rfl).flow.scalar r y ^ 2)
    (hy : ((K.finalSlab h).restrictIncoming le_rfl h le_rfl).flow.scalar v y ≤ M)
    (hbud : (Ctime : ℝ) * M * (v - s) ≤ 1 / 2) :
    ∀ r ∈ Icc s v, ((K.finalSlab h).restrictIncoming le_rfl h le_rfl).flow.scalar r y ≤ 2 * M := by
  have hL := lipschitzOnWith_inv_max_scalar_Icc_C11SC2
    ((K.finalSlab h).restrictIncoming le_rfl h le_rfl).equation hM
    (fun r hr => ⟨hs0.trans hr.1, hr.2.trans_lt hv2⟩) y hloc
  intro r hr
  have hd := hL.dist_le_mul r hr v ⟨hsv, le_rfl⟩
  have hrv : |r - v| = v - r := by
    rw [abs_sub_comm]
    exact abs_of_nonneg (by linarith [hr.2])
  rw [Real.dist_eq, Real.dist_eq, hrv] at hd
  refine le_two_mul_of_abs_inv_max_sub_le_C11SC hM hy hd ?_
  have hCM : (0 : ℝ) ≤ Ctime * M := mul_nonneg Ctime.coe_nonneg hM.le
  calc (Ctime : ℝ) * M * (v - r) ≤ Ctime * M * (v - s) :=
        mul_le_mul_of_nonneg_left (by linarith [hr.1]) hCM
    _ ≤ 1 / 2 := hbud

/-- 时间导数 `stageMetric m` → restrict final slab（`m = last`；`_P6GWF`，SEEDCL2 `deriv_of_stage_C11SC2` 的
final 孪生）。 -/
theorem deriv_of_stage_last_P6GWF (K : RetainedCoreHistory.{u})
    (h : K.time (Fin.last K.eventCount) < K.horizon) {m : Fin (K.eventCount + 1)}
    (hm : m = Fin.last K.eventCount) (v : ℝ) (Ctime : ℝ≥0)
    (x : (K.stage (Fin.last K.eventCount)).Carrier) (z : (K.stage m).Carrier) (hz : HEq z x)
    (hd : |derivWithin (fun t => metricScalarAt (K.toHistory.stageMetric m t) z) (Iic v) v| ≤
      Ctime * metricScalarAt (K.toHistory.stageMetric m v) z ^ 2) :
    |derivWithin (fun w => ((K.finalSlab h).restrictIncoming le_rfl h le_rfl).flow.scalar w x)
        (Iic v) v| ≤
      Ctime * ((K.finalSlab h).restrictIncoming le_rfl h le_rfl).flow.scalar v x ^ 2 := by
  subst hm
  obtain rfl := eq_of_heq hz
  simp only [K.stageMetric_last_restrict_P6HF h] at hd
  exact hd

/-- **selection `hgood` ⇒ final slab 内时间导数界（`_P6GWF`，阈值 `Cg·R`，PROVED）**：SEEDCL2
`deriv_of_hgood_slab_Cg_C11SC2` 的 final 孪生（`activeStage τ = last` ⇐ `time last < τ`；P6HF
`witness_of_hgood_final_P6HF` 的同一桥，取 `HasSpatialCanonicalTimeControl` 的时间分量）。 -/
theorem deriv_of_hgood_final_P6GWF {eps C1' C2' : ℝ} {Ctime' : ℝ≥0} {Cg : ℝ}
    (K : RetainedCoreHistory.{u}) (h : K.time (Fin.last K.eventCount) < K.horizon)
    {Tn aSeed σ : Icc (0 : ℝ) K.toHistory.horizon} (haT : aSeed ≤ Tn)
    (hsT : σ ≤ Tn) (has : aSeed ≤ σ) {pT : (K.toHistory.stageAt Tn).Carrier}
    (seedTrace : BackwardPointTrace K.toHistory (K.toHistory.activeStage aSeed)
      (K.toHistory.activeStage Tn) (K.toHistory.activeStage_mono haT) pT)
    (y : (K.toHistory.stageAt σ).Carrier) (R L : ℝ)
    (hgood : ∀ (v : Icc (0 : ℝ) K.toHistory.horizon) (hav : aSeed ≤ v) (hvs : v ≤ σ),
      (σ : ℝ) - L ^ 2 / R ≤ (v : ℝ) →
      ∀ z : (K.toHistory.stageAt v).Carrier,
        riemannianEDistOf (K.toHistory.stageMetric (K.toHistory.activeStage v) v)
            (seedTrace.point (K.toHistory.activeStage v) (K.toHistory.activeStage_mono hav)
              (K.toHistory.activeStage_mono (hvs.trans hsT))) z ≤
          riemannianEDistOf (K.toHistory.stageMetric (K.toHistory.activeStage σ) σ)
              (seedTrace.point (K.toHistory.activeStage σ) (K.toHistory.activeStage_mono has)
                (K.toHistory.activeStage_mono hsT)) y +
            ENNReal.ofReal (L / Real.sqrt R) →
        Cg * R ≤ metricScalarAt (K.toHistory.stageMetric (K.toHistory.activeStage v) v) z →
        K.toHistory.HasSpatialCanonicalTimeControl eps C1' C2' Ctime' v z)
    (τ : ℝ) (hτ1 : K.time (Fin.last K.eventCount) < τ) (hτ2 : τ < K.horizon)
    (haτ : (aSeed : ℝ) ≤ τ) (hτσ : τ ≤ σ) (hLτ : (σ : ℝ) - L ^ 2 / R ≤ τ)
    (h1 : K.toHistory.activeStage aSeed ≤ Fin.last K.eventCount)
    (h2 : Fin.last K.eventCount ≤ K.toHistory.activeStage Tn)
    (x : (K.stage (Fin.last K.eventCount)).Carrier)
    (hd : riemannianEDistOf (((K.finalSlab h).restrictIncoming le_rfl h le_rfl).flow.base.metric τ)
        (seedTrace.point (Fin.last K.eventCount) h1 h2) x ≤
      riemannianEDistOf (K.toHistory.stageMetric (K.toHistory.activeStage σ) σ)
          (seedTrace.point (K.toHistory.activeStage σ) (K.toHistory.activeStage_mono has)
            (K.toHistory.activeStage_mono hsT)) y +
        ENNReal.ofReal (L / Real.sqrt R))
    (hR : Cg * R ≤ ((K.finalSlab h).restrictIncoming le_rfl h le_rfl).flow.scalar τ x) :
    |derivWithin (fun w => ((K.finalSlab h).restrictIncoming le_rfl h le_rfl).flow.scalar w x)
        (Iic τ) τ| ≤
      Ctime' * ((K.finalSlab h).restrictIncoming le_rfl h le_rfl).flow.scalar τ x ^ 2 := by
  have h0 : (0 : ℝ) ≤ τ := (K.toHistory.time_nonneg _).trans hτ1.le
  let τI : Icc (0 : ℝ) K.toHistory.horizon := ⟨τ, h0, hτσ.trans σ.2.2⟩
  have hact : K.toHistory.activeStage τI = Fin.last K.eventCount :=
    K.toHistory.activeStage_eq_last_of_time_last_le τI hτ1.le
  have hav : aSeed ≤ τI := haτ
  have hvs : τI ≤ σ := hτσ
  let xm : (K.stage (K.toHistory.activeStage τI)).Carrier :=
    cast (congrArg (fun m => (K.stage m).Carrier) hact.symm) x
  have hxm : HEq xm x := cast_heq _ _
  have hs := point_heq_of_eq_P6M2 seedTrace hact (K.toHistory.activeStage_mono hav)
    (K.toHistory.activeStage_mono (hvs.trans hsT)) h1 h2
  have hdm : riemannianEDistOf (K.toHistory.stageMetric (K.toHistory.activeStage τI) τI)
      (seedTrace.point (K.toHistory.activeStage τI) (K.toHistory.activeStage_mono hav)
        (K.toHistory.activeStage_mono (hvs.trans hsT))) xm ≤
      riemannianEDistOf (K.toHistory.stageMetric (K.toHistory.activeStage σ) σ)
          (seedTrace.point (K.toHistory.activeStage σ) (K.toHistory.activeStage_mono has)
            (K.toHistory.activeStage_mono hsT)) y +
        ENNReal.ofReal (L / Real.sqrt R) :=
    (K.edist_stage_eq_last_P6HF h hact τ _ xm _ x hs hxm).trans_le hd
  have hRm : Cg * R ≤
      metricScalarAt (K.toHistory.stageMetric (K.toHistory.activeStage τI) τI) xm :=
    hR.trans_eq (K.scalar_stage_eq_last_P6HF h hact τ xm x hxm).symm
  have hctl := (hgood τI hav hvs hLτ xm hdm hRm).2 (by rw [hact]; exact hτ1) hτ2
  exact K.deriv_of_stage_last_P6GWF h hact τ Ctime' x xm hxm hctl

end RetainedCoreHistory

section WindowScalLocalFinal

/-- **U 端窗口标量界的局域导数版（final slab，`_P6GWF`，PROVED）**：SEEDCL2
`windowScal_of_pickedTop_local_C11SC2` 的 final 孪生，结论逐字（`B_s(x, 1/√(Cq))` 上 `R(s, ·) ≤ Cq`，
restrict final slab flow）。前提逐字：hgood（区域 `L/√R`、阈值 `Cg·R`）、`Cg·R ≤ Λq`、`Ctime′ Λ β ≤ 1/2`、
`6Λ ≤ C`、`2Λ ≤ ρ² C`、`Lc + 2ρ/√(2Λ) ≤ L`、`R ≤ q`、`x` 处 anchor `R(v, x) ≤ Λq`、时间域
（`time last < s ≤ v < horizon`）、first-exit 停止 `hGx`（`[s, v]` 上 `d_r(O, x) ≤ d_σ + Lc/√R`）。
证明体逐字（导数核 / 梯度核换 final 孪生）。 -/
theorem windowScal_of_pickedTop_local_final_P6GWF {eps C1' C2' : ℝ} {Ctime' : ℝ≥0} {Cg : ℝ}
    (hC2 : 0 ≤ C2') (K : RetainedCoreHistory.{u})
    (h : K.time (Fin.last K.eventCount) < K.horizon)
    {Tn aSeed σ : Icc (0 : ℝ) K.toHistory.horizon}
    (haT : aSeed ≤ Tn) (hsT : σ ≤ Tn) (has : aSeed ≤ σ) {pT : (K.toHistory.stageAt Tn).Carrier}
    (seedTrace : BackwardPointTrace K.toHistory (K.toHistory.activeStage aSeed)
      (K.toHistory.activeStage Tn) (K.toHistory.activeStage_mono haT) pT)
    (y : (K.toHistory.stageAt σ).Carrier) {R L Lc : ℝ} (hR : 0 < R)
    (hgood : ∀ (v : Icc (0 : ℝ) K.toHistory.horizon) (hav : aSeed ≤ v) (hvs : v ≤ σ),
      (σ : ℝ) - L ^ 2 / R ≤ (v : ℝ) →
      ∀ z : (K.toHistory.stageAt v).Carrier,
        riemannianEDistOf (K.toHistory.stageMetric (K.toHistory.activeStage v) v)
            (seedTrace.point (K.toHistory.activeStage v) (K.toHistory.activeStage_mono hav)
              (K.toHistory.activeStage_mono (hvs.trans hsT))) z ≤
          riemannianEDistOf (K.toHistory.stageMetric (K.toHistory.activeStage σ) σ)
              (seedTrace.point (K.toHistory.activeStage σ) (K.toHistory.activeStage_mono has)
                (K.toHistory.activeStage_mono hsT)) y +
            ENNReal.ofReal (L / Real.sqrt R) →
        Cg * R ≤ metricScalarAt (K.toHistory.stageMetric (K.toHistory.activeStage v) v) z →
        K.toHistory.HasSpatialCanonicalTimeControl eps C1' C2' Ctime' v z)
    (h1 : K.toHistory.activeStage aSeed ≤ Fin.last K.eventCount)
    (h2 : Fin.last K.eventCount ≤ K.toHistory.activeStage Tn)
    {v q Λ β C : ℝ} (hv2 : v < K.horizon) (hq : 0 < q) (hRq : R ≤ q) (hΛ : 0 < Λ)
    (hCgΛ : Cg * R ≤ Λ * q) (hbud : (Ctime' : ℝ) * Λ * β ≤ 1 / 2) (hΛC : 6 * Λ ≤ C)
    (hρC : 2 * Λ ≤ localPropagationRadius C2' ^ 2 * C)
    (hρL : Lc + 2 * (localPropagationRadius C2' / Real.sqrt (2 * Λ)) ≤ L) (hLc0 : 0 ≤ Lc)
    (hvσ : v ≤ σ) (x : (K.stage (Fin.last K.eventCount)).Carrier)
    (hxv : ((K.finalSlab h).restrictIncoming le_rfl h le_rfl).flow.scalar v x ≤ Λ * q)
    (s : ℝ) (hs1 : v - β / q ≤ s) (hsv : s ≤ v) (hs0 : K.time (Fin.last K.eventCount) < s)
    (haS : (aSeed : ℝ) ≤ s) (hσL : (σ : ℝ) - L ^ 2 / R ≤ s)
    (hGx : ∀ r ∈ Icc s v,
      riemannianEDistOf (((K.finalSlab h).restrictIncoming le_rfl h le_rfl).flow.base.metric r)
          (seedTrace.point (Fin.last K.eventCount) h1 h2) x ≤
        riemannianEDistOf (K.toHistory.stageMetric (K.toHistory.activeStage σ) σ)
            (seedTrace.point (K.toHistory.activeStage σ) (K.toHistory.activeStage_mono has)
              (K.toHistory.activeStage_mono hsT)) y + ENNReal.ofReal (Lc / Real.sqrt R))
    (z : (K.stage (Fin.last K.eventCount)).Carrier)
    (hz : riemannianEDistOf (((K.finalSlab h).restrictIncoming le_rfl h le_rfl).flow.base.metric s)
        x z < ENNReal.ofReal (1 / Real.sqrt (C * q))) :
    ((K.finalSlab h).restrictIncoming le_rfl h le_rfl).flow.scalar s z ≤ C * q := by
  set dσ := riemannianEDistOf (K.toHistory.stageMetric (K.toHistory.activeStage σ) σ)
    (seedTrace.point (K.toHistory.activeStage σ) (K.toHistory.activeStage_mono has)
      (K.toHistory.activeStage_mono hsT)) y
    with hdσ
  set ρ := localPropagationRadius C2' with hρdef
  have hρ0 : 0 < ρ := localPropagationRadius_pos hC2
  have hsR : 0 < Real.sqrt R := Real.sqrt_pos.2 hR
  have hΛq : 0 < Λ * q := mul_pos hΛ hq
  have hQ0 : 0 < 2 * (Λ * q) := by linarith
  have hs2Λ : 0 < Real.sqrt (2 * Λ) := Real.sqrt_pos.2 (by linarith)
  -- 半径：`2ρ/√(2Λq) ≤ 2ρ/(√(2Λ)√R)`
  have hsplit : Real.sqrt (2 * (Λ * q)) = Real.sqrt (2 * Λ) * Real.sqrt q := by
    rw [← mul_assoc, Real.sqrt_mul (by linarith : (0 : ℝ) ≤ 2 * Λ)]
  have hradR : 2 * (ρ / Real.sqrt (2 * (Λ * q))) ≤
      2 * (ρ / Real.sqrt (2 * Λ)) / Real.sqrt R := by
    rw [hsplit]
    have h' := div_le_div_of_nonneg_left hρ0.le (mul_pos hs2Λ hsR)
      (mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt hRq) hs2Λ.le)
    have he : 2 * (ρ / (Real.sqrt (2 * Λ) * Real.sqrt R)) =
        2 * (ρ / Real.sqrt (2 * Λ)) / Real.sqrt R := by
      field_simp
    linarith
  have hLcL' : Lc / Real.sqrt R + 2 * (ρ / Real.sqrt (2 * (Λ * q))) ≤ L / Real.sqrt R := by
    have h' := div_le_div_of_nonneg_right hρL hsR.le
    rw [add_div] at h'
    linarith
  have hLcL : Lc / Real.sqrt R ≤ L / Real.sqrt R := by
    have : 0 ≤ 2 * (ρ / Real.sqrt (2 * (Λ * q))) := by positivity
    linarith
  -- (1) worldline ceiling：`[s, v]` 上 `R(·, x) ≤ 2Λq`
  have hqvs : q * (v - s) ≤ β := by
    have hvs : v - s ≤ β / q := by linarith
    have h' := mul_le_mul_of_nonneg_left hvs hq.le
    rwa [mul_div_cancel₀ _ hq.ne'] at h'
  have hwl : ∀ r ∈ Icc s v,
      ((K.finalSlab h).restrictIncoming le_rfl h le_rfl).flow.scalar r x ≤ 2 * (Λ * q) :=
    K.scalar_le_two_mul_of_localDeriv_final_P6GWF h hΛq hs0.le hsv hv2 x (fun r hr hMr =>
      K.deriv_of_hgood_final_P6GWF h haT hsT has seedTrace y R L hgood r
        (hs0.trans hr.1) (hr.2.trans hv2) (haS.trans hr.1.le) (hr.2.le.trans hvσ)
        (hσL.trans hr.1.le) h1 h2 x
        ((hGx r ⟨hr.1.le, hr.2.le⟩).trans (add_le_add le_rfl (ENNReal.ofReal_le_ofReal hLcL)))
        (hCgΛ.trans hMr.le)) hxv (by
      calc (Ctime' : ℝ) * (Λ * q) * (v - s) = Ctime' * Λ * (q * (v - s)) := by ring
        _ ≤ Ctime' * Λ * β := mul_le_mul_of_nonneg_left hqvs (by positivity)
        _ ≤ 1 / 2 := hbud)
  have hxs : ((K.finalSlab h).restrictIncoming le_rfl h le_rfl).flow.scalar s x ≤ 2 * (Λ * q) :=
    hwl s ⟨le_rfl, hsv⟩
  -- (2) 时刻 `s` 的局部传播（hgood 空间分量）
  let U : Set (K.stage (Fin.last K.eventCount)).Carrier := {w | riemannianEDistOf
    (((K.finalSlab h).restrictIncoming le_rfl h le_rfl).flow.base.metric s)
      (seedTrace.point (Fin.last K.eventCount) h1 h2) w ≤
      dσ + ENNReal.ofReal (L / Real.sqrt R)}
  have hU : riemannianBallOf
      (((K.finalSlab h).restrictIncoming le_rfl h le_rfl).flow.base.metric s) x
      (2 * (ρ / Real.sqrt (2 * (Λ * q)))) ⊆ U := by
    intro w hwb
    change riemannianEDistOf _ _ w ≤ _
    calc _ ≤ riemannianEDistOf
          (((K.finalSlab h).restrictIncoming le_rfl h le_rfl).flow.base.metric s)
          (seedTrace.point (Fin.last K.eventCount) h1 h2) x +
          riemannianEDistOf
            (((K.finalSlab h).restrictIncoming le_rfl h le_rfl).flow.base.metric s) x w :=
          riemannianEDistOf_triangle _ _ _ _
      _ ≤ (dσ + ENNReal.ofReal (Lc / Real.sqrt R)) +
          ENNReal.ofReal (2 * (ρ / Real.sqrt (2 * (Λ * q)))) :=
          add_le_add (hGx s ⟨le_rfl, hsv⟩) hwb.le
      _ = dσ + ENNReal.ofReal (Lc / Real.sqrt R + 2 * (ρ / Real.sqrt (2 * (Λ * q)))) := by
          rw [add_assoc, ← ENNReal.ofReal_add (by positivity) (by positivity)]
      _ ≤ dσ + ENNReal.ofReal (L / Real.sqrt R) :=
          add_le_add le_rfl (ENNReal.ofReal_le_ofReal hLcL')
  have hball : ∀ w : (K.stage (Fin.last K.eventCount)).Carrier, w ∈ riemannianClosedBallOf
      (((K.finalSlab h).restrictIncoming le_rfl h le_rfl).flow.base.metric s) x
        (ρ / Real.sqrt (2 * (Λ * q))) →
      ((K.finalSlab h).restrictIncoming le_rfl h le_rfl).flow.scalar s w ≤ 3 * (2 * (Λ * q)) :=
    fun w0 hw0 =>
    scalar_le_on_ball_of_gradient_bound_P6L
      ((K.finalSlab h).restrictIncoming le_rfl h le_rfl).flow hC2 hQ0 U hU
    (fun w hwU hw ξ => by
      have hRw : Cg * R ≤ ((K.finalSlab h).restrictIncoming le_rfl h le_rfl).flow.scalar s w := by
        linarith
      have hg := RetainedCoreHistory.gradient_of_hgood_final_P6HF (Ctime' := Ctime') hC2 K h haT
        hsT has seedTrace y R L hgood s hs0 haS (hsv.trans hvσ) hσL h1 h2 w hwU hRw ξ
      rw [Real.coe_toNNReal _ hC2] at hg
      have hpos : 0 ≤ ((K.finalSlab h).restrictIncoming le_rfl h le_rfl).flow.scalar s w := by
        linarith
      have hterm : 0 ≤ C2' * ((K.finalSlab h).restrictIncoming le_rfl h le_rfl).flow.scalar s w *
          Real.sqrt (((K.finalSlab h).restrictIncoming le_rfl h le_rfl).flow.scalar s w) *
          Real.sqrt ((((K.finalSlab h).restrictIncoming le_rfl h le_rfl).flow.base.metric
            s).inner w ξ ξ) := by positivity
      have hring : 2 * C2' *
          (((K.finalSlab h).restrictIncoming le_rfl h le_rfl).flow.scalar s w *
          Real.sqrt (((K.finalSlab h).restrictIncoming le_rfl h le_rfl).flow.scalar s w)) *
          Real.sqrt ((((K.finalSlab h).restrictIncoming le_rfl h le_rfl).flow.base.metric
            s).inner w ξ ξ) =
          2 * (C2' * ((K.finalSlab h).restrictIncoming le_rfl h le_rfl).flow.scalar s w *
          Real.sqrt (((K.finalSlab h).restrictIncoming le_rfl h le_rfl).flow.scalar s w) *
          Real.sqrt ((((K.finalSlab h).restrictIncoming le_rfl h le_rfl).flow.base.metric
            s).inner w ξ ξ)) := by ring
      rw [hring]
      linarith) hxs hw0
  -- (3) `1/√(Cq) ≤ ρ/√(2Λq)` 且 `6Λq ≤ Cq`
  have hC0 : 0 < C := by linarith
  have hCq : 0 < C * q := mul_pos hC0 hq
  have hℓ : 1 / Real.sqrt (C * q) ≤ ρ / Real.sqrt (2 * (Λ * q)) := by
    have hkey : Real.sqrt (2 * (Λ * q)) ≤ Real.sqrt (C * q) * ρ := by
      have hle : 2 * (Λ * q) ≤ ρ ^ 2 * (C * q) := by
        have h' := mul_le_mul_of_nonneg_right hρC hq.le
        calc 2 * (Λ * q) = 2 * Λ * q := by ring
          _ ≤ ρ ^ 2 * C * q := h'
          _ = ρ ^ 2 * (C * q) := by ring
      have h1' : Real.sqrt (2 * (Λ * q)) ≤ Real.sqrt (ρ ^ 2 * (C * q)) := Real.sqrt_le_sqrt hle
      rw [Real.sqrt_mul (sq_nonneg ρ), Real.sqrt_sq hρ0.le] at h1'
      linarith
    have h2' : Real.sqrt (2 * (Λ * q)) / ρ ≤ Real.sqrt (C * q) := (div_le_iff₀ hρ0).2 hkey
    have h3 := one_div_le_one_div_of_le (div_pos (Real.sqrt_pos.2 hQ0) hρ0) h2'
    rwa [one_div_div] at h3
  have hzb := hball z (hz.le.trans (ENNReal.ofReal_le_ofReal hℓ))
  have h6 := mul_le_mul_of_nonneg_right hΛC hq.le
  linarith

end WindowScalLocalFinal

/-- consumer（G3，`_P6GWF`）：final worldline ceiling 在零长度窗口（`s = v`）的实例——`hloc` 空真，
`R(v, y) ≤ M` ⇒ `R(v, y) ≤ 2M`。 -/
example (K : RetainedCoreHistory.{u}) (h : K.time (Fin.last K.eventCount) < K.horizon) {v M : ℝ}
    (hM : 0 < M) (hv1 : K.time (Fin.last K.eventCount) ≤ v) (hv2 : v < K.horizon)
    (y : (K.stage (Fin.last K.eventCount)).Carrier)
    (hy : ((K.finalSlab h).restrictIncoming le_rfl h le_rfl).flow.scalar v y ≤ M) :
    ((K.finalSlab h).restrictIncoming le_rfl h le_rfl).flow.scalar v y ≤ 2 * M :=
  K.scalar_le_two_mul_of_localDeriv_final_P6GWF h (Ctime := 0) hM hv1 le_rfl hv2 y
    (fun _ hr => absurd (hr.1.trans hr.2) (lt_irrefl v)) hy (by simp) v ⟨le_rfl, le_rfl⟩

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
