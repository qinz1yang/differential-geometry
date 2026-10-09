import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.P6HUVCoverP6M3
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.P6HclosGFirstExitP6M4

/-!
# hclosC / hclosG 的 cover 归约：缺口见证（O-CH11-HCLOSC，后缀 `_P6HC`；B2 分析叶）

**状态：BLOCKED[一致 K = 新上游义务]**。本文件只是缺口见证，不进主链。
* `hclosG_of_cover_uniformK_P6HC`：driver 外（期 5 body 用）`hclosG` ⇐ 条件形 `hdistC` + 半径一致的
  traced 曲率（内联假设 `huni`，不 def）。路线 = `hclosC_of_cover_P6M3`（cover 不等式 DF-1 由一致 `K` 解出）
  + 深度 `−σ₁ + 1` 取值。
* 文件末 example：重索引族 `· ∘ ψ` 上的类型对齐。
driver **内**的条件形 `hclosC` / `hclosCF`（hbcadC → hUVC 所需）另为 BLOCKED：U 侧窗
`[v − Bw/Q, v]` 比已建立的 traced 深度多 `Bw`（P6L2 window anchor 在 `s ∈ [−c k, 0)`、traced 深度 `τ k`
处取 hbcadC，余量 `τ k − c k → 0`），而越深度的唯一路线（first-exit + `hscalU`）只有两侧 Dt
`|∂ₜR| ≤ C R²`，撞饱和反例。repair：(α) seed-good canonical 区上的渐近单侧 Harnack
`∀ η > 0, ∀ᶠ n, ∂ₜR ≥ −η R²`（ch12 候选 C12-8）；(β) 切片二分 U 侧的 Λ-cut 改形。详见
state-O-CH11-HCLOSC.md。不写"端点已闭"。生成器 `build-logs/scratch/O-CH11-HCLOSC/gen/gen.py`。
-/

set_option autoImplicit false

noncomputable section

open Set Function Filter
open DifferentialGeometry.Geometry.Curvature DifferentialGeometry.Integral.Measure
open DifferentialGeometry.CheegerGromovCompactness
open DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood
open scoped Manifold NNReal Topology ContDiff ENNReal

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

universe u

/-- **缺口见证（BLOCKED[一致 K = 新上游义务]，`_P6HC`）**：driver 外（期 5 body 用）的 `hclosG` 经 cover
路线的归约。条件形 `hdistC`（NotKBody:132，余量 `L/4`）+ **半径一致的 traced 曲率** `huni`（内联假设：
对每个深度 `θ` 有一个与半径 `A` 无关的 `K`）⇒ NotKBody:196 `hclosG` 体逐字。取
`θb := max B 0 − σ₁ + 1`、`ρb := Dw + e^{9Kθb}(Dd + max Rad 0)`，满足 `hclosC_of_cover_P6M3` 的 cover
不等式（DF-1）；再在 `φ := id`、深度 `−σ₁ + 1` 处取 hclosC。`huni` **不是**树内已登记 binder：
DepthExtendable 的 `K` 依赖半径（`∀ A ∃ K`），一致 `K` 是新的上游义务（候选来源：P6L2 window-anchor 的
`M` 与 `A`、`T′` 无关，但只在 driver Tstar 分支内，driver 不导出）。本定理不进主链。 -/
theorem ObservedHistory.hclosG_of_cover_uniformK_P6HC (Kh : ℕ → ObservedHistory.{u})
    (Tn aSeed σ : ∀ n, Icc (0 : ℝ) (Kh n).horizon)
    (haT : ∀ n, aSeed n ≤ Tn n) (hsT : ∀ n, σ n ≤ Tn n) (has : ∀ n, aSeed n ≤ σ n)
    (pT : ∀ n, ((Kh n).stageAt (Tn n)).Carrier)
    (seedTrace : ∀ n, BackwardPointTrace (Kh n) ((Kh n).activeStage (aSeed n))
      ((Kh n).activeStage (Tn n)) ((Kh n).activeStage_mono (haT n)) (pT n))
    (y : ∀ n, ((Kh n).stageAt (σ n)).Carrier) (R L : ℕ → ℝ)
    (hR : ∀ n, 0 < R n) (hL : Tendsto L atTop atTop)
    (hwin : ∀ T : ℝ, 0 < T → ∀ᶠ n in atTop, (aSeed n : ℝ) ≤ σ n - T / R n)
    (hdistC : ∀ φ : ℕ → ℕ, StrictMono φ → ∀ D T Kc : ℝ, 0 < D → 0 < T → 0 ≤ Kc →
      (∀ᶠ n in map φ atTop, (Kh n).isTracedRegion (σ n) (y n) (2 * D / Real.sqrt (R n))
        (T / R n) (Kc * R n)) → ∀ᶠ n in map φ atTop,
      ∀ x ∈ riemannianBallOf ((Kh n).stageMetric ((Kh n).activeStage (σ n)) (σ n)) (y n)
          (D / Real.sqrt (R n)),
      ∀ (v : Icc (0 : ℝ) (Kh n).horizon) (hav : aSeed n ≤ v) (hvs : v ≤ σ n),
        (σ n : ℝ) - T / R n ≤ v →
      ∀ tr : BackwardPointTrace (Kh n) ((Kh n).activeStage v) ((Kh n).activeStage (σ n))
          ((Kh n).activeStage_mono hvs) x,
        riemannianEDistOf ((Kh n).stageMetric ((Kh n).activeStage v) v)
            ((seedTrace n).point ((Kh n).activeStage v) ((Kh n).activeStage_mono hav)
              ((Kh n).activeStage_mono (hvs.trans (hsT n))))
            (tr.point ((Kh n).activeStage v) le_rfl ((Kh n).activeStage_mono hvs)) ≤
          riemannianEDistOf ((Kh n).stageMetric ((Kh n).activeStage (σ n)) (σ n))
              ((seedTrace n).point ((Kh n).activeStage (σ n)) ((Kh n).activeStage_mono (has n))
                ((Kh n).activeStage_mono (hsT n))) (y n) +
            ENNReal.ofReal (L n / 4 / Real.sqrt (R n)))
    (huni : ∀ θ : ℝ, 0 < θ → ∃ K : ℝ, 0 ≤ K ∧ ∀ A : ℝ, 0 < A → ∀ᶠ n in atTop,
      (Kh n).isTracedRegion (σ n) (y n) (A / Real.sqrt (R n)) (θ / R n) (K * R n)) :
    ∀ Rad B σ₁ σ₂ : ℝ, σ₁ ≤ σ₂ → σ₂ < 0 → ∀ Dw Dd : ℝ, 0 < Dw → 0 < Dd →
      ∀ᶠ n in atTop,
      ∀ (j' : Fin (Kh n).eventCount) (v : ℝ), (Kh n).time j'.castSucc < v →
        v < (Kh n).time j'.succ → (σ n : ℝ) + σ₁ / R n ≤ v → v ≤ σ n + σ₂ / R n →
      ∀ x₁ ∈ riemannianBallOf ((Kh n).stageMetric ((Kh n).activeStage (σ n)) (σ n)) (y n)
          (Dw / Real.sqrt (R n)),
      ∀ (hjσ : j'.castSucc ≤ (Kh n).activeStage (σ n))
        (tr : BackwardPointTrace (Kh n) j'.castSucc ((Kh n).activeStage (σ n)) hjσ x₁),
      ∀ (h1 : (Kh n).activeStage (aSeed n) ≤ j'.castSucc)
        (h2 : j'.castSucc ≤ (Kh n).activeStage (Tn n)) (w : ((Kh n).stage j'.castSucc).Carrier),
        riemannianEDistOf (((Kh n).event j').incoming.flow.base.metric v)
            ((seedTrace n).point j'.castSucc h1 h2) w ≤
          riemannianEDistOf ((Kh n).stageMetric ((Kh n).activeStage (σ n)) (σ n))
              ((seedTrace n).point ((Kh n).activeStage (σ n)) ((Kh n).activeStage_mono (has n))
                ((Kh n).activeStage_mono (hsT n))) (y n) +
            ENNReal.ofReal (L n / 2 / Real.sqrt (R n)) →
        riemannianEDistOf (((Kh n).event j').incoming.flow.base.metric v)
            (tr.point j'.castSucc le_rfl hjσ) w < ENNReal.ofReal (Dd / Real.sqrt (R n)) →
        R n ≤ ((Kh n).event j').incoming.flow.scalar v w →
        ∀ x ∈ riemannianBallOf (((Kh n).event j').incoming.flow.base.metric v) w
            (Rad / Real.sqrt (((Kh n).event j').incoming.flow.scalar v w)),
        ∀ τ : ℝ, v - B / ((Kh n).event j').incoming.flow.scalar v w ≤ τ → τ ≤ v →
          (Kh n).time j'.castSucc < τ →
          riemannianEDistOf (((Kh n).event j').incoming.flow.base.metric τ)
              ((seedTrace n).point j'.castSucc h1 h2) x ≤
            riemannianEDistOf ((Kh n).stageMetric ((Kh n).activeStage (σ n)) (σ n))
                ((seedTrace n).point ((Kh n).activeStage (σ n)) ((Kh n).activeStage_mono (has n))
                  ((Kh n).activeStage_mono (hsT n))) (y n) +
              ENNReal.ofReal (L n / Real.sqrt (R n)) := by
  have hC := ObservedHistory.hclosC_of_cover_P6M3 Kh Tn aSeed σ haT hsT has pT seedTrace y R L hR
    hwin (fun φ hφ D T K hD hT hK htr => by
      filter_upwards [hdistC φ hφ D T K hD hT hK htr,
        (hL.eventually_ge_atTop 0).filter_mono hφ.tendsto_atTop] with n hn hL0
      intro x hx v hav hvs hvT tr
      refine (hn x hx v hav hvs hvT tr).trans (add_le_add le_rfl (ENNReal.ofReal_le_ofReal ?_))
      exact div_le_div_of_nonneg_right (by linarith) (Real.sqrt_nonneg _))
    (fun Rad B σ₁ σ₂ h12 hσ₂ φ hφ Dw Dd T Kc hDw hDd _hT _hKc _htr => by
      have hM : 0 ≤ max Rad 0 := le_max_right _ _
      have hB0 : 0 ≤ max B 0 := le_max_right _ _
      have hθ : 0 < max B 0 - σ₁ + 1 := by linarith
      obtain ⟨K, hK, hev⟩ := huni (max B 0 - σ₁ + 1) hθ
      have hρ : 0 < Dw + Real.exp (9 * K * (max B 0 - σ₁ + 1)) * (Dd + max Rad 0) :=
        add_pos hDw (mul_pos (Real.exp_pos _) (by linarith))
      exact ⟨Dw + Real.exp (9 * K * (max B 0 - σ₁ + 1)) * (Dd + max Rad 0),
        max B 0 - σ₁ + 1, K, hρ, hθ, hK, by linarith, le_rfl,
        (hev _ (by positivity)).filter_mono hφ.tendsto_atTop⟩)
  intro Rad B σ₁ σ₂ h12 hσ₂ Dw Dd hDw hDd
  obtain ⟨K, hK, hev⟩ := huni (-σ₁ + 1) (by linarith)
  exact hC Rad B σ₁ σ₂ h12 hσ₂ id strictMono_id Dw Dd (-σ₁ + 1) K hDw hDd (by linarith) hK
    (hev (2 * Dw) (by positivity))

/-- **类型对齐（只证类型）**：driver 子列 `ψ` 上的一致 `K`（内联）+ 原族的条件形 `hdistC` / `hwin` / `hL`
⇒ NotKBody `hclosG` 槽（体逐字，写成对族数据的 λ）在重索引族 `· ∘ ψ` 上成立。 -/
example (Kh : ℕ → ObservedHistory.{u})
    (Tn aSeed σ : ∀ n, Icc (0 : ℝ) (Kh n).horizon)
    (haT : ∀ n, aSeed n ≤ Tn n) (hsT : ∀ n, σ n ≤ Tn n) (has : ∀ n, aSeed n ≤ σ n)
    (pT : ∀ n, ((Kh n).stageAt (Tn n)).Carrier)
    (seedTrace : ∀ n, BackwardPointTrace (Kh n) ((Kh n).activeStage (aSeed n))
      ((Kh n).activeStage (Tn n)) ((Kh n).activeStage_mono (haT n)) (pT n))
    (y : ∀ n, ((Kh n).stageAt (σ n)).Carrier) (R L : ℕ → ℝ)
    (hR : ∀ n, 0 < R n) (hL : Tendsto L atTop atTop)
    (hwin : ∀ T : ℝ, 0 < T → ∀ᶠ n in atTop, (aSeed n : ℝ) ≤ σ n - T / R n)
    (hdistC : ∀ φ : ℕ → ℕ, StrictMono φ → ∀ D T Kc : ℝ, 0 < D → 0 < T → 0 ≤ Kc →
      (∀ᶠ n in map φ atTop, (Kh n).isTracedRegion (σ n) (y n) (2 * D / Real.sqrt (R n))
        (T / R n) (Kc * R n)) → ∀ᶠ n in map φ atTop,
      ∀ x ∈ riemannianBallOf ((Kh n).stageMetric ((Kh n).activeStage (σ n)) (σ n)) (y n)
          (D / Real.sqrt (R n)),
      ∀ (v : Icc (0 : ℝ) (Kh n).horizon) (hav : aSeed n ≤ v) (hvs : v ≤ σ n),
        (σ n : ℝ) - T / R n ≤ v →
      ∀ tr : BackwardPointTrace (Kh n) ((Kh n).activeStage v) ((Kh n).activeStage (σ n))
          ((Kh n).activeStage_mono hvs) x,
        riemannianEDistOf ((Kh n).stageMetric ((Kh n).activeStage v) v)
            ((seedTrace n).point ((Kh n).activeStage v) ((Kh n).activeStage_mono hav)
              ((Kh n).activeStage_mono (hvs.trans (hsT n))))
            (tr.point ((Kh n).activeStage v) le_rfl ((Kh n).activeStage_mono hvs)) ≤
          riemannianEDistOf ((Kh n).stageMetric ((Kh n).activeStage (σ n)) (σ n))
              ((seedTrace n).point ((Kh n).activeStage (σ n)) ((Kh n).activeStage_mono (has n))
                ((Kh n).activeStage_mono (hsT n))) (y n) +
            ENNReal.ofReal (L n / 4 / Real.sqrt (R n)))
    (ψ : ℕ → ℕ) (hψ : StrictMono ψ)
    (huni : ∀ θ : ℝ, 0 < θ → ∃ K : ℝ, 0 ≤ K ∧ ∀ A : ℝ, 0 < A → ∀ᶠ i in atTop,
      (Kh (ψ i)).isTracedRegion (σ (ψ i)) (y (ψ i)) (A / Real.sqrt (R (ψ i))) (θ / R (ψ i))
        (K * R (ψ i))) :
    (fun (Kh : ℕ → ObservedHistory.{u}) (Tn aSeed σ : ∀ n, Icc (0 : ℝ) (Kh n).horizon)
        (haT : ∀ n, aSeed n ≤ Tn n) (hsT : ∀ n, σ n ≤ Tn n) (has : ∀ n, aSeed n ≤ σ n)
        (pT : ∀ n, ((Kh n).stageAt (Tn n)).Carrier)
        (seedTrace : ∀ n, BackwardPointTrace (Kh n) ((Kh n).activeStage (aSeed n))
          ((Kh n).activeStage (Tn n)) ((Kh n).activeStage_mono (haT n)) (pT n))
        (y : ∀ n, ((Kh n).stageAt (σ n)).Carrier) (R L : ℕ → ℝ) =>
      ∀ Rad B σ₁ σ₂ : ℝ, σ₁ ≤ σ₂ → σ₂ < 0 → ∀ Dw Dd : ℝ, 0 < Dw → 0 < Dd →
      ∀ᶠ n in atTop,
      ∀ (j' : Fin (Kh n).eventCount) (v : ℝ), (Kh n).time j'.castSucc < v →
        v < (Kh n).time j'.succ → (σ n : ℝ) + σ₁ / R n ≤ v → v ≤ σ n + σ₂ / R n →
      ∀ x₁ ∈ riemannianBallOf ((Kh n).stageMetric ((Kh n).activeStage (σ n)) (σ n)) (y n)
          (Dw / Real.sqrt (R n)),
      ∀ (hjσ : j'.castSucc ≤ (Kh n).activeStage (σ n))
        (tr : BackwardPointTrace (Kh n) j'.castSucc ((Kh n).activeStage (σ n)) hjσ x₁),
      ∀ (h1 : (Kh n).activeStage (aSeed n) ≤ j'.castSucc)
        (h2 : j'.castSucc ≤ (Kh n).activeStage (Tn n)) (w : ((Kh n).stage j'.castSucc).Carrier),
        riemannianEDistOf (((Kh n).event j').incoming.flow.base.metric v)
            ((seedTrace n).point j'.castSucc h1 h2) w ≤
          riemannianEDistOf ((Kh n).stageMetric ((Kh n).activeStage (σ n)) (σ n))
              ((seedTrace n).point ((Kh n).activeStage (σ n)) ((Kh n).activeStage_mono (has n))
                ((Kh n).activeStage_mono (hsT n))) (y n) +
            ENNReal.ofReal (L n / 2 / Real.sqrt (R n)) →
        riemannianEDistOf (((Kh n).event j').incoming.flow.base.metric v)
            (tr.point j'.castSucc le_rfl hjσ) w < ENNReal.ofReal (Dd / Real.sqrt (R n)) →
        R n ≤ ((Kh n).event j').incoming.flow.scalar v w →
        ∀ x ∈ riemannianBallOf (((Kh n).event j').incoming.flow.base.metric v) w
            (Rad / Real.sqrt (((Kh n).event j').incoming.flow.scalar v w)),
        ∀ τ : ℝ, v - B / ((Kh n).event j').incoming.flow.scalar v w ≤ τ → τ ≤ v →
          (Kh n).time j'.castSucc < τ →
          riemannianEDistOf (((Kh n).event j').incoming.flow.base.metric τ)
              ((seedTrace n).point j'.castSucc h1 h2) x ≤
            riemannianEDistOf ((Kh n).stageMetric ((Kh n).activeStage (σ n)) (σ n))
                ((seedTrace n).point ((Kh n).activeStage (σ n)) ((Kh n).activeStage_mono (has n))
                  ((Kh n).activeStage_mono (hsT n))) (y n) +
              ENNReal.ofReal (L n / Real.sqrt (R n)))
      (fun i => Kh (ψ i)) (fun i => Tn (ψ i)) (fun i => aSeed (ψ i)) (fun i => σ (ψ i))
      (fun i => haT (ψ i)) (fun i => hsT (ψ i)) (fun i => has (ψ i)) (fun i => pT (ψ i))
      (fun i => seedTrace (ψ i)) (fun i => y (ψ i)) (fun i => R (ψ i)) (fun i => L (ψ i)) := by
  beta_reduce
  exact ObservedHistory.hclosG_of_cover_uniformK_P6HC (fun i => Kh (ψ i)) (fun i => Tn (ψ i))
    (fun i => aSeed (ψ i)) (fun i => σ (ψ i)) (fun i => haT (ψ i)) (fun i => hsT (ψ i))
    (fun i => has (ψ i)) (fun i => pT (ψ i)) (fun i => seedTrace (ψ i)) (fun i => y (ψ i))
    (fun i => R (ψ i)) (fun i => L (ψ i)) (fun i => hR (ψ i)) (hL.comp hψ.tendsto_atTop)
    (fun T hT => hψ.tendsto_atTop.eventually (hwin T hT))
    (fun φ hφ D T Kc hD hT hKc htr => hdistC (ψ ∘ φ) (hψ.comp hφ) D T Kc hD hT hKc htr) huni

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
