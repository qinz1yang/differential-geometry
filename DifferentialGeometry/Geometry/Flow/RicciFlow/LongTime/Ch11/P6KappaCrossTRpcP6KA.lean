import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.P6StayTRpcP6KA
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.P6KappaFreshP6F4
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.P6FreshRescaleP6JA

/-!
# R1′ (i)：跨更早 surgery 的 trace 上的逐中心 κ（driver `hkappaC` 形；O-CH11-KAPPA-ADAPT，`_P6KA`）

C 文件（`P6KappaTRpcP6KA`）的逐中心 κ 继承 FOOT4 形，只覆盖当前 slab（`time i⁻ < τ`）。driver `hkappaC`
要 `[ts − T/R, ts]` 上**全部** trace（可能跨更早的 surgery event）。本文件不走 slab 内距离畸变，直接用
**跨 slab 的 stay**：A 文件 `hstopE_deep_tower_pc_P6KA`（= BCDBOOT `hstopE_deep_tower_P6BB` 的逐中心孪生；
其 stay 由 CXJP `hgoodV_scalC_CXJP` / `hprotC_scalC_CXJP` 沿 trace **跨 event** 给出，surgery 处由 records
（`hfamT`：`old = retainedCore`、canonical windows）与 `surgery_no_shortcut` 机制保证不出 seed 邻域）对从
`B_tt(y′, r/√R_k)` 出发、到任意 `v ∈ [tt − T/R_k, tt]` 的 trace 给
`d_v(O_v, tr(v)) ≤ d_σ(O, y) + L_k/√R_k`；top gate `hdσ`（前缀）给 `≤ Aseed + 3 < Aseed + 7`，即 FRESH 的宏观
footprint；FRESH（`fresh_rescale_adapter_P6JA`，κ 对**全部 stage** 成立）在 `v` 处给 κ。
* **`hkappaC_tower_of_fresh_P6KA`**（PROVED ⇐ 原尺度 FRESH + `hfamT` + cap 参数；**无 hTR 合同、无 hmargin /
  hdistL**）：结论体 = driver `hkappaC` 的体逐字形（`Hs n ↦ Kh k`、`ts n ↦ tt`（`tt = t ↑ σ`）、`ys n ↦ y′ ≍ p′`、
  `D ↦ r`、`ρnc ↦ 1/200`），traced-region 前提只在当前中心 `(tt, y′)`、当前 `(T, r)`。
* consumer `example`：traced-region 常数取一个数 `K₀`。
剩余 = R4 中心对齐（state HANDOVER (ii)）。
生成器 build-logs/scratch/O-CH11-KAPPA-ADAPT/gen/r1/gen_r1d.py（FOOT4 前缀 / DISTLA2 hfamT 文本逐字抽取，assert）。
-/

set_option autoImplicit false

noncomputable section

open Set Filter Function
open DifferentialGeometry DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.CheegerGromovCompactness
open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.PDE.RicciFlow
open DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood
open DifferentialGeometry.Geometry.Collapse
open scoped Manifold NNReal Topology ContDiff ENNReal

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

universe u

open Perelman.CanonicalNeighborhood.FiniteHorn

/-- **跨 surgery 的逐中心 κ（driver `hkappaC` 形，`_P6KA`，PROVED ⇐ 原尺度 FRESH + `hfamT` + cap 参数）**：
`∀ T r`，FOOT4 塔前缀（含 gate），`∀ᶠ k`、`∀` crossing `p′`、`∀ᶠ t ↑ σ`：当前中心 `(tt, y′ ≍ p′)`、当前
`(T, r)` 的 traced region ⇒ 从 `B_tt(y′, r/√R_k)` 出发、深度 `≤ T/R_k` 的**任意** trace（可跨更早 surgery）
在 `v` 处的点 κ-noncollapsed（尺度 `≤ 1/200`）。footprint = 跨 slab stay（`hstopE_deep_tower_pc_P6KA`）+ top
gate `hdσ`。 -/
theorem hkappaC_tower_of_fresh_P6KA :
    ∃ ε₀ : ℝ, 0 < ε₀ ∧
    ∀ {P : OrientedThreeStage.{u}} {g : P.Metric} {F : GC.Interface.RawSurgery P g}
      {ε C1 C2 : ℝ} {Ctime : ℝ≥0} {qp : CutoffParameters} {Ktr : ℝ → ℝ → ℝ}
      {Aseed : ℝ} {nr : ℝ → ℝ} {κ Tf : ℝ},
    0 < Aseed → 0 < κ →
    (∀ n, KappaSeedWindowFwd_C11PK nr (Aseed + 7) κ Tf (F.tower.history n).toHistory) →
    0 ≤ C2 → StandardCap.transitionEnd + 10 < qp.modelRadius → qp.modelAccuracy ≤ ε₀ →
    2 ≤ qp.modelOrder → Tendsto qp.delta atTop (𝓝 0) →
    (∀ r T, 0 ≤ Ktr r T) →
    (
      ∀ (ind : ℕ → ℕ) (c : ℕ → ℝ) (hc : ∀ k, 0 < c k),
        let Kh : ℕ → ObservedHistory.{u} := fun k =>
          ((F.tower.history (ind k)).rescale_P6N (c k) (hc k)).toHistory
        ∀ (Tn : ∀ k, Icc (0 : ℝ) (Kh k).horizon) (pT : ∀ k, ((Kh k).stageAt (Tn k)).Carrier),
          (∀ k : ℕ, (k : ℝ) + 1 ≤ c k * (Tn k : ℝ)) →
        ∀ (aSeed : ∀ k, Icc (0 : ℝ) (Kh k).horizon) (haT : ∀ k, aSeed k ≤ Tn k),
          (∀ k, (aSeed k : ℝ) = (Tn k : ℝ) - 1 ^ (2 : ℕ)) → (∀ k, 1 ≤ (aSeed k : ℝ)) →
          (∀ k, GC.LongTime.hasSmallParabolicCurvature (Kh k) (Tn k) (pT k) 1) →
        ∀ (seedTrace : ∀ k, BackwardPointTrace (Kh k) ((Kh k).activeStage (aSeed k))
            ((Kh k).activeStage (Tn k)) ((Kh k).activeStage_mono (haT k)) (pT k))
          (σ : ∀ k, Icc (0 : ℝ) (Kh k).horizon) (y : ∀ k, ((Kh k).stageAt (σ k)).Carrier)
          (R : ℕ → ℝ) (hsT : ∀ k, σ k ≤ Tn k) (has : ∀ k, aSeed k ≤ σ k) (L : ℕ → ℝ),
          (∀ k, R k =
            metricScalarAt ((Kh k).stageMetric ((Kh k).activeStage (σ k)) (σ k)) (y k)) →
          (∀ k, 0 < R k) → (∀ k : ℕ, (k : ℝ) + 1 ≤ R k) →
          Tendsto L atTop atTop →
          (∀ k, ¬ (Kh k).HasSpatialCanonicalTimeControl ε C1 C2 Ctime (σ k) (y k)) →
          (∀ k, ∀ (v : Icc (0 : ℝ) (Kh k).horizon) (hav : aSeed k ≤ v) (hvs : v ≤ σ k),
            (σ k : ℝ) - L k ^ (2 : ℕ) / R k ≤ (v : ℝ) →
            ∀ z : ((Kh k).stageAt v).Carrier,
              riemannianEDistOf ((Kh k).stageMetric ((Kh k).activeStage v) v)
                  ((seedTrace k).point ((Kh k).activeStage v) ((Kh k).activeStage_mono hav)
                    ((Kh k).activeStage_mono (hvs.trans (hsT k)))) z ≤
                riemannianEDistOf ((Kh k).stageMetric ((Kh k).activeStage (σ k)) (σ k))
                    ((seedTrace k).point ((Kh k).activeStage (σ k))
                      ((Kh k).activeStage_mono (has k)) ((Kh k).activeStage_mono (hsT k))) (y k) +
                  ENNReal.ofReal (L k / Real.sqrt (R k)) →
              4 * R k ≤ metricScalarAt ((Kh k).stageMetric ((Kh k).activeStage v) v) z →
              (Kh k).HasSpatialCanonicalTimeControl ε C1 C2 Ctime v z) →
          (∀ T : ℝ, 0 < T → ∀ᶠ k in atTop, (aSeed k : ℝ) ≤ σ k - T / R k) →
          (∀ T : ℝ, 0 < T → ∀ᶠ k in atTop, (Tn k : ℝ) - 1 ^ (2 : ℕ) / 2 ≤ (σ k : ℝ) - T / R k) →
          Tendsto (fun k => R k * ((σ k : ℝ) - ((Tn k : ℝ) - 1 ^ (2 : ℕ) / 2))) atTop atTop →
          Tendsto (fun k => 1 / 200 * Real.sqrt (R k)) atTop atTop →
        ∃ (a₀ T₀ : ℕ → ℝ) (records : ∀ k (e : Fin (Kh k).eventCount),
            T₀ k ≤ (Kh k).time e.succ →
              GeometricCutoffRecord (Kh k) e (qp.rescale_P6N (c k) (hc k))),
          (∀ k, 0 ≤ a₀ k) ∧
          (∀ k (τ : Icc (0 : ℝ) (Kh k).horizon) (x : ((Kh k).stageAt τ).Carrier),
            InFixedHamiltonIveyRegion ((Kh k).stageMetric ((Kh k).activeStage τ) τ)
              (a₀ k + τ) x) ∧
          (∀ k, T₀ k ≤ (aSeed k : ℝ)) ∧
          (∀ k (e : Fin (Kh k).eventCount), T₀ k ≤ (Kh k).time e.succ →
            ((Kh k).event e).old = ((Kh k).event e).transition.trace.retainedCore) ∧
          (∀ k (e : Fin (Kh k).eventCount) (he : T₀ k ≤ (Kh k).time e.succ) b,
            ((records k e he).static b).hasCanonicalWindow) ∧
          (∀ k, riemannianEDistOf ((Kh k).stageMetric ((Kh k).activeStage (σ k)) (σ k))
            ((seedTrace k).point ((Kh k).activeStage (σ k)) ((Kh k).activeStage_mono (has k))
              ((Kh k).activeStage_mono (hsT k))) (y k) ≠ ⊤) ∧
          ∀ᶠ k in atTop, WindowNeckScaleBudget_P6HS (Kh k) (qp.rescale_P6N (c k) (hc k))
            (T₀ k) (aSeed k : ℝ) (R k)
    ) →
      ∀ (T r : ℝ), 0 < T → 0 < r →
      ∀ (ind : ℕ → ℕ) (c : ℕ → ℝ) (hc : ∀ k, 0 < c k),
        let Kh : ℕ → ObservedHistory.{u} := fun k =>
          ((F.tower.history (ind k)).rescale_P6N (c k) (hc k)).toHistory
        ∀ (Tn : ∀ k, Icc (0 : ℝ) (Kh k).horizon) (pT : ∀ k, ((Kh k).stageAt (Tn k)).Carrier),
          (∀ k : ℕ, (k : ℝ) + 1 ≤ c k * (Tn k : ℝ)) →
        ∀ (aSeed : ∀ k, Icc (0 : ℝ) (Kh k).horizon) (haT : ∀ k, aSeed k ≤ Tn k),
          (∀ k, (aSeed k : ℝ) = (Tn k : ℝ) - 1 ^ (2 : ℕ)) → (∀ k, 1 ≤ (aSeed k : ℝ)) →
          (∀ k, GC.LongTime.hasSmallParabolicCurvature (Kh k) (Tn k) (pT k) 1) →
          (∀ k, ENNReal.ofReal (Aseed⁻¹ * 1 ^ 3) ≤
            riemannianVolumeMeasure ThreeModel ((Kh k).stageAt (Tn k)).Carrier
              ((Kh k).stageMetric ((Kh k).activeStage (Tn k)) (Tn k))
              (riemannianBallOf ((Kh k).stageMetric ((Kh k).activeStage (Tn k)) (Tn k))
                (pT k) 1)) →
          (∀ k, 2 < (Tn k : ℝ)) →
          (∀ k (w : ℝ), (Tn k : ℝ) - 1 ^ 2 / 2 ≤ w → w ≤ (Tn k : ℝ) →
            nr (c k * w) / Real.sqrt (c k) ≤ 1) →
        ∀ (seedTrace : ∀ k, BackwardPointTrace (Kh k) ((Kh k).activeStage (aSeed k))
            ((Kh k).activeStage (Tn k)) ((Kh k).activeStage_mono (haT k)) (pT k))
          (σ : ∀ k, Icc (0 : ℝ) (Kh k).horizon) (y : ∀ k, ((Kh k).stageAt (σ k)).Carrier)
          (R : ℕ → ℝ) (hsT : ∀ k, σ k ≤ Tn k) (has : ∀ k, aSeed k ≤ σ k) (L : ℕ → ℝ),
          (∀ k, R k =
            metricScalarAt ((Kh k).stageMetric ((Kh k).activeStage (σ k)) (σ k)) (y k)) →
          (∀ k, 0 < R k) → (∀ k : ℕ, (k : ℝ) + 1 ≤ R k) →
          Tendsto L atTop atTop →
          (∀ k, ¬ (Kh k).HasSpatialCanonicalTimeControl ε C1 C2 Ctime (σ k) (y k)) →
          (∀ k, ∀ (v : Icc (0 : ℝ) (Kh k).horizon) (hav : aSeed k ≤ v) (hvs : v ≤ σ k),
            (σ k : ℝ) - L k ^ (2 : ℕ) / R k ≤ (v : ℝ) →
            ∀ z : ((Kh k).stageAt v).Carrier,
              riemannianEDistOf ((Kh k).stageMetric ((Kh k).activeStage v) v)
                  ((seedTrace k).point ((Kh k).activeStage v) ((Kh k).activeStage_mono hav)
                    ((Kh k).activeStage_mono (hvs.trans (hsT k)))) z ≤
                riemannianEDistOf ((Kh k).stageMetric ((Kh k).activeStage (σ k)) (σ k))
                    ((seedTrace k).point ((Kh k).activeStage (σ k))
                      ((Kh k).activeStage_mono (has k)) ((Kh k).activeStage_mono (hsT k))) (y k) +
                  ENNReal.ofReal (L k / Real.sqrt (R k)) →
              4 * R k ≤ metricScalarAt ((Kh k).stageMetric ((Kh k).activeStage v) v) z →
              (Kh k).HasSpatialCanonicalTimeControl ε C1 C2 Ctime v z) →
          (∀ T : ℝ, 0 < T → ∀ᶠ k in atTop, (aSeed k : ℝ) ≤ σ k - T / R k) →
          (∀ T : ℝ, 0 < T → ∀ᶠ k in atTop, (Tn k : ℝ) - 1 ^ (2 : ℕ) / 2 ≤ (σ k : ℝ) - T / R k) →
          Tendsto (fun k => R k * ((σ k : ℝ) - ((Tn k : ℝ) - 1 ^ (2 : ℕ) / 2))) atTop atTop →
          Tendsto (fun k => 1 / 200 * Real.sqrt (R k)) atTop atTop →
          (∀ᶠ k in atTop,
            riemannianEDistOf ((Kh k).stageMetric ((Kh k).activeStage (σ k)) (σ k))
                ((seedTrace k).point ((Kh k).activeStage (σ k)) ((Kh k).activeStage_mono (has k))
                  ((Kh k).activeStage_mono (hsT k))) (y k) +
              ENNReal.ofReal ((L k + 1) / Real.sqrt (R k)) ≤ ENNReal.ofReal ((Aseed + 3) * 1)) →
        ∀ i : ∀ k, Fin (Kh k).eventCount, (∀ k, (σ k : ℝ) = (Kh k).time (i k).succ) →
        ∃ ρ : ℕ → ℝ, Tendsto (fun k => ρ k * Real.sqrt (R k)) atTop atTop ∧
          ∀ᶠ k in atTop, ∀ (p' : ((Kh k).stage (i k).castSucc).Carrier)
            (q : ((Kh k).stage (i k).succ).Carrier), HEq (y k) q →
            ((Kh k).event (i k)).RegularCrossing p' q →
            ∀ᶠ t in 𝓝[<] (Kh k).time (i k).succ,
              ∀ (tt : Icc (0 : ℝ) (Kh k).horizon), (tt : ℝ) = t →
              ∀ y' : ((Kh k).stageAt tt).Carrier, HEq y' p' →
                (Kh k).isTracedRegion tt y' (r / Real.sqrt (R k)) (T / R k) (Ktr r T * R k) →
              ∀ x ∈ riemannianBallOf ((Kh k).stageMetric ((Kh k).activeStage tt) tt) y'
                  (r / Real.sqrt (R k)),
              ∀ (v : Icc (0 : ℝ) (Kh k).horizon) (hvt : v ≤ tt), (tt : ℝ) - T / R k ≤ v →
              ∀ tr : BackwardPointTrace (Kh k) ((Kh k).activeStage v) ((Kh k).activeStage tt)
                ((Kh k).activeStage_mono hvt) x,
              ∀ b : ℝ, 0 < b → b ≤ ρ k →
                (Kh k).isParabolicallyRmControlledBall v
                  (tr.point ((Kh k).activeStage v) le_rfl ((Kh k).activeStage_mono hvt)) b →
                ENNReal.ofReal (κ * b ^ 3) ≤
                  Geometry.Collapse.ballVolume ((Kh k).stageMetric ((Kh k).activeStage v) v)
                    (tr.point ((Kh k).activeStage v) le_rfl ((Kh k).activeStage_mono hvt)) b := by
  obtain ⟨ε₀, hε₀, hST⟩ := hstopE_deep_tower_pc_P6KA.{u}
  refine ⟨ε₀, hε₀, ?_⟩
  intro P g F ε C1 C2 Ctime qp Ktr Aseed nr κ Tf hAs hκ hsup hC2 hDm hacc hm hδlim hK hfamT
    T r hT hr ind c hc Kh Tn pT hTc aSeed haT hclock hone hsm hvol hTn2 hnrS seedTrace σ y R
    hsT has L hRdef hRpos hRr hL hsel hgood haS hTnS hroom hradii hdσ i hi
  have hb := betaStar_P6BB (Ctime := Ctime) (Cball := fun _ => 0)
    (Cgrid := fun r T => 9 * Ktr r T)
  have hstay := hST (Cball := fun _ => 0) (Cgrid := fun r T => 9 * Ktr r T)
    (β := fun r T => gridStep_P6BB Ctime (fun _ => 0) (fun r T => 9 * Ktr r T) r T)
    hC2 hDm hacc hm hδlim hb.1 hb.2 hK (fun _ _ => le_rfl) hfamT
    T r hT hr ind c hc Tn pT hTc aSeed haT hclock hone hsm seedTrace σ y R hsT has L hRdef hRpos
    hRr hL hsel hgood haS hTnS hroom hradii i hi
  have hsupK := GC.LongTime.Ch11.fresh_rescale_adapter_P6JA hsup
  refine ⟨fun _ => 1 / 200, hradii, ?_⟩
  have hTf : ∀ᶠ k in atTop, Tf ≤ c k * (Tn k : ℝ) := by
    filter_upwards [eventually_ge_atTop ⌈Tf⌉₊] with k hk
    have h1 := hTc k
    have h2 : (⌈Tf⌉₊ : ℝ) ≤ k := by exact_mod_cast hk
    linarith [Nat.le_ceil Tf]
  filter_upwards [hstay, hdσ, hTf, hTnS (2 * T) (by positivity), haS (2 * T) (by positivity)]
    with k hstk hdσk hTfk hwk haSk
  intro p' q hq hcross
  have hRk := hRpos k
  have hTR0 : 0 < T / R k := div_pos hT hRk
  have e2 : 2 * T / R k = T / R k + T / R k := by ring
  have hcs : (Kh k).time (i k).castSucc < (Kh k).time (i k).succ :=
    (Kh k).time_strictMono Fin.castSucc_lt_succ
  have hσs : (σ k : ℝ) = (Kh k).time (i k).succ := hi k
  filter_upwards [hstk p' q hq hcross,
    Ioo_mem_nhdsLT (show max ((Kh k).time (i k).castSucc) ((σ k : ℝ) - T / R k) <
      (Kh k).time (i k).succ from max_lt hcs (by linarith))] with t hst hti
  intro tt htt y' hy' hTR x hx v hvt hvT tr b hb0 hbρ hctrl
  have ht1 : (Kh k).time (i k).castSucc < t := lt_of_le_of_lt (le_max_left _ _) hti.1
  have htσ0 : (σ k : ℝ) - T / R k < t := lt_of_le_of_lt (le_max_right _ _) hti.1
  have he : (Kh k).activeStage tt = (i k).castSucc :=
    (Kh k).activeStage_eq_of_mem_slab_P6F3 (i k) tt (by rw [htt]; exact ht1.le)
      (by rw [htt]; exact hti.2)
  have htσ : tt ≤ σ k := by
    change (tt : ℝ) ≤ σ k
    rw [htt, hσs]
    exact hti.2.le
  have hTRat : ∀ (tt' : Icc (0 : ℝ) (Kh k).horizon), (tt' : ℝ) = t →
      ∀ y'' : ((Kh k).stageAt tt').Carrier, HEq y'' p' →
        (Kh k).isTracedRegion tt' y'' (r / Real.sqrt (R k)) (T / R k) (Ktr r T * R k) := by
    intro tt' htt' y'' hy''
    obtain rfl : tt' = tt := Subtype.ext (htt'.trans htt.symm)
    obtain rfl : y'' = y' := eq_of_heq (hy''.trans hy'.symm)
    exact hTR
  have hvT' : t - T / R k ≤ (v : ℝ) := by rw [← htt]; exact hvT
  have haS' : aSeed k ≤ v := by
    change (aSeed k : ℝ) ≤ v
    linarith
  have hP : ∀ z : ((Kh k).stage (i k).castSucc).Carrier, HEq x z →
      z ∈ riemannianBallOf (((Kh k).event (i k)).incoming.flow.base.metric t) p'
        (r / Real.sqrt (R k)) := by
    intro z hz
    have h1 := (ObservedHistory.ball_transport_P6BB he htt x y' z p' hz hy').mp hx
    rwa [ObservedHistory.stageMetric_castSucc_apply] at h1
  have hd := hst hTRat tt htt htσ v haS' hvt hvT' x hP tr v le_rfl hvt
  have hvTn : v ≤ Tn k := (hvt.trans htσ).trans (hsT k)
  have hτw : (Tn k : ℝ) - 1 ^ 2 / 2 ≤ v := by linarith
  have hTn' : Tf / c k ≤ (Tn k : ℝ) := by
    rw [div_le_iff₀ (hc k)]
    linarith [mul_comm (c k) (Tn k : ℝ)]
  have hvolA : ENNReal.ofReal ((Aseed + 7)⁻¹ * 1 ^ 3) ≤
      ballVolume ((Kh k).stageMetric ((Kh k).activeStage (Tn k)) (Tn k)) (pT k) 1 := by
    refine le_trans (ENNReal.ofReal_le_ofReal ?_) (hvol k)
    have : (Aseed + 7)⁻¹ ≤ Aseed⁻¹ := inv_anti₀ hAs (by linarith)
    simpa using this
  have hL1 : L k / Real.sqrt (R k) ≤ (L k + 1) / Real.sqrt (R k) :=
    div_le_div_of_nonneg_right (by linarith) (Real.sqrt_nonneg _)
  have hmem : riemannianEDistOf ((Kh k).stageMetric ((Kh k).activeStage v) v)
      ((seedTrace k).point ((Kh k).activeStage v) ((Kh k).activeStage_mono haS')
        ((Kh k).activeStage_mono hvTn))
      (tr.point ((Kh k).activeStage v) le_rfl ((Kh k).activeStage_mono hvt)) <
      ENNReal.ofReal ((Aseed + 7) * 1) := by
    refine lt_of_le_of_lt
      (hd.trans ((add_le_add le_rfl (ENNReal.ofReal_le_ofReal hL1)).trans hdσk)) ?_
    exact (ENNReal.ofReal_lt_ofReal_iff (by linarith)).mpr (by linarith)
  exact hsupK ind c hc k (Tn k) (pT k) 1 hTn' (by linarith [hTn2 k]) (hsm k) hvolA (hnrS k)
    (aSeed k) (haT k) (hclock k) (seedTrace k) v haS' hvTn hτw
    (tr.point ((Kh k).activeStage v) le_rfl ((Kh k).activeStage_mono hvt)) hmem b hb0.le
    (by linarith) hctrl

/-- **consumer example（`_P6KA`）**：traced-region 常数取一个数 `K₀`（没有 `∀ T r` 合同）——driver `hkappaC`
的体在塔层由**当前中心、当前深度**的 `isTracedRegion … (K₀·R_k)` 产出，覆盖跨更早 surgery 的 trace。 -/
example :
    ∃ ε₀ : ℝ, 0 < ε₀ ∧
    ∀ {P : OrientedThreeStage.{u}} {g : P.Metric} {F : GC.Interface.RawSurgery P g}
      {ε C1 C2 : ℝ} {Ctime : ℝ≥0} {qp : CutoffParameters}
      {Aseed : ℝ} {nr : ℝ → ℝ} {κ Tf : ℝ} (K₀ : ℝ),
    0 < Aseed → 0 < κ →
    (∀ n, KappaSeedWindowFwd_C11PK nr (Aseed + 7) κ Tf (F.tower.history n).toHistory) →
    0 ≤ C2 → StandardCap.transitionEnd + 10 < qp.modelRadius → qp.modelAccuracy ≤ ε₀ →
    2 ≤ qp.modelOrder → Tendsto qp.delta atTop (𝓝 0) →
    0 ≤ K₀ →
    (
      ∀ (ind : ℕ → ℕ) (c : ℕ → ℝ) (hc : ∀ k, 0 < c k),
        let Kh : ℕ → ObservedHistory.{u} := fun k =>
          ((F.tower.history (ind k)).rescale_P6N (c k) (hc k)).toHistory
        ∀ (Tn : ∀ k, Icc (0 : ℝ) (Kh k).horizon) (pT : ∀ k, ((Kh k).stageAt (Tn k)).Carrier),
          (∀ k : ℕ, (k : ℝ) + 1 ≤ c k * (Tn k : ℝ)) →
        ∀ (aSeed : ∀ k, Icc (0 : ℝ) (Kh k).horizon) (haT : ∀ k, aSeed k ≤ Tn k),
          (∀ k, (aSeed k : ℝ) = (Tn k : ℝ) - 1 ^ (2 : ℕ)) → (∀ k, 1 ≤ (aSeed k : ℝ)) →
          (∀ k, GC.LongTime.hasSmallParabolicCurvature (Kh k) (Tn k) (pT k) 1) →
        ∀ (seedTrace : ∀ k, BackwardPointTrace (Kh k) ((Kh k).activeStage (aSeed k))
            ((Kh k).activeStage (Tn k)) ((Kh k).activeStage_mono (haT k)) (pT k))
          (σ : ∀ k, Icc (0 : ℝ) (Kh k).horizon) (y : ∀ k, ((Kh k).stageAt (σ k)).Carrier)
          (R : ℕ → ℝ) (hsT : ∀ k, σ k ≤ Tn k) (has : ∀ k, aSeed k ≤ σ k) (L : ℕ → ℝ),
          (∀ k, R k =
            metricScalarAt ((Kh k).stageMetric ((Kh k).activeStage (σ k)) (σ k)) (y k)) →
          (∀ k, 0 < R k) → (∀ k : ℕ, (k : ℝ) + 1 ≤ R k) →
          Tendsto L atTop atTop →
          (∀ k, ¬ (Kh k).HasSpatialCanonicalTimeControl ε C1 C2 Ctime (σ k) (y k)) →
          (∀ k, ∀ (v : Icc (0 : ℝ) (Kh k).horizon) (hav : aSeed k ≤ v) (hvs : v ≤ σ k),
            (σ k : ℝ) - L k ^ (2 : ℕ) / R k ≤ (v : ℝ) →
            ∀ z : ((Kh k).stageAt v).Carrier,
              riemannianEDistOf ((Kh k).stageMetric ((Kh k).activeStage v) v)
                  ((seedTrace k).point ((Kh k).activeStage v) ((Kh k).activeStage_mono hav)
                    ((Kh k).activeStage_mono (hvs.trans (hsT k)))) z ≤
                riemannianEDistOf ((Kh k).stageMetric ((Kh k).activeStage (σ k)) (σ k))
                    ((seedTrace k).point ((Kh k).activeStage (σ k))
                      ((Kh k).activeStage_mono (has k)) ((Kh k).activeStage_mono (hsT k))) (y k) +
                  ENNReal.ofReal (L k / Real.sqrt (R k)) →
              4 * R k ≤ metricScalarAt ((Kh k).stageMetric ((Kh k).activeStage v) v) z →
              (Kh k).HasSpatialCanonicalTimeControl ε C1 C2 Ctime v z) →
          (∀ T : ℝ, 0 < T → ∀ᶠ k in atTop, (aSeed k : ℝ) ≤ σ k - T / R k) →
          (∀ T : ℝ, 0 < T → ∀ᶠ k in atTop, (Tn k : ℝ) - 1 ^ (2 : ℕ) / 2 ≤ (σ k : ℝ) - T / R k) →
          Tendsto (fun k => R k * ((σ k : ℝ) - ((Tn k : ℝ) - 1 ^ (2 : ℕ) / 2))) atTop atTop →
          Tendsto (fun k => 1 / 200 * Real.sqrt (R k)) atTop atTop →
        ∃ (a₀ T₀ : ℕ → ℝ) (records : ∀ k (e : Fin (Kh k).eventCount),
            T₀ k ≤ (Kh k).time e.succ →
              GeometricCutoffRecord (Kh k) e (qp.rescale_P6N (c k) (hc k))),
          (∀ k, 0 ≤ a₀ k) ∧
          (∀ k (τ : Icc (0 : ℝ) (Kh k).horizon) (x : ((Kh k).stageAt τ).Carrier),
            InFixedHamiltonIveyRegion ((Kh k).stageMetric ((Kh k).activeStage τ) τ)
              (a₀ k + τ) x) ∧
          (∀ k, T₀ k ≤ (aSeed k : ℝ)) ∧
          (∀ k (e : Fin (Kh k).eventCount), T₀ k ≤ (Kh k).time e.succ →
            ((Kh k).event e).old = ((Kh k).event e).transition.trace.retainedCore) ∧
          (∀ k (e : Fin (Kh k).eventCount) (he : T₀ k ≤ (Kh k).time e.succ) b,
            ((records k e he).static b).hasCanonicalWindow) ∧
          (∀ k, riemannianEDistOf ((Kh k).stageMetric ((Kh k).activeStage (σ k)) (σ k))
            ((seedTrace k).point ((Kh k).activeStage (σ k)) ((Kh k).activeStage_mono (has k))
              ((Kh k).activeStage_mono (hsT k))) (y k) ≠ ⊤) ∧
          ∀ᶠ k in atTop, WindowNeckScaleBudget_P6HS (Kh k) (qp.rescale_P6N (c k) (hc k))
            (T₀ k) (aSeed k : ℝ) (R k)
    ) →
      ∀ (T r : ℝ), 0 < T → 0 < r →
      ∀ (ind : ℕ → ℕ) (c : ℕ → ℝ) (hc : ∀ k, 0 < c k),
        let Kh : ℕ → ObservedHistory.{u} := fun k =>
          ((F.tower.history (ind k)).rescale_P6N (c k) (hc k)).toHistory
        ∀ (Tn : ∀ k, Icc (0 : ℝ) (Kh k).horizon) (pT : ∀ k, ((Kh k).stageAt (Tn k)).Carrier),
          (∀ k : ℕ, (k : ℝ) + 1 ≤ c k * (Tn k : ℝ)) →
        ∀ (aSeed : ∀ k, Icc (0 : ℝ) (Kh k).horizon) (haT : ∀ k, aSeed k ≤ Tn k),
          (∀ k, (aSeed k : ℝ) = (Tn k : ℝ) - 1 ^ (2 : ℕ)) → (∀ k, 1 ≤ (aSeed k : ℝ)) →
          (∀ k, GC.LongTime.hasSmallParabolicCurvature (Kh k) (Tn k) (pT k) 1) →
          (∀ k, ENNReal.ofReal (Aseed⁻¹ * 1 ^ 3) ≤
            riemannianVolumeMeasure ThreeModel ((Kh k).stageAt (Tn k)).Carrier
              ((Kh k).stageMetric ((Kh k).activeStage (Tn k)) (Tn k))
              (riemannianBallOf ((Kh k).stageMetric ((Kh k).activeStage (Tn k)) (Tn k))
                (pT k) 1)) →
          (∀ k, 2 < (Tn k : ℝ)) →
          (∀ k (w : ℝ), (Tn k : ℝ) - 1 ^ 2 / 2 ≤ w → w ≤ (Tn k : ℝ) →
            nr (c k * w) / Real.sqrt (c k) ≤ 1) →
        ∀ (seedTrace : ∀ k, BackwardPointTrace (Kh k) ((Kh k).activeStage (aSeed k))
            ((Kh k).activeStage (Tn k)) ((Kh k).activeStage_mono (haT k)) (pT k))
          (σ : ∀ k, Icc (0 : ℝ) (Kh k).horizon) (y : ∀ k, ((Kh k).stageAt (σ k)).Carrier)
          (R : ℕ → ℝ) (hsT : ∀ k, σ k ≤ Tn k) (has : ∀ k, aSeed k ≤ σ k) (L : ℕ → ℝ),
          (∀ k, R k =
            metricScalarAt ((Kh k).stageMetric ((Kh k).activeStage (σ k)) (σ k)) (y k)) →
          (∀ k, 0 < R k) → (∀ k : ℕ, (k : ℝ) + 1 ≤ R k) →
          Tendsto L atTop atTop →
          (∀ k, ¬ (Kh k).HasSpatialCanonicalTimeControl ε C1 C2 Ctime (σ k) (y k)) →
          (∀ k, ∀ (v : Icc (0 : ℝ) (Kh k).horizon) (hav : aSeed k ≤ v) (hvs : v ≤ σ k),
            (σ k : ℝ) - L k ^ (2 : ℕ) / R k ≤ (v : ℝ) →
            ∀ z : ((Kh k).stageAt v).Carrier,
              riemannianEDistOf ((Kh k).stageMetric ((Kh k).activeStage v) v)
                  ((seedTrace k).point ((Kh k).activeStage v) ((Kh k).activeStage_mono hav)
                    ((Kh k).activeStage_mono (hvs.trans (hsT k)))) z ≤
                riemannianEDistOf ((Kh k).stageMetric ((Kh k).activeStage (σ k)) (σ k))
                    ((seedTrace k).point ((Kh k).activeStage (σ k))
                      ((Kh k).activeStage_mono (has k)) ((Kh k).activeStage_mono (hsT k))) (y k) +
                  ENNReal.ofReal (L k / Real.sqrt (R k)) →
              4 * R k ≤ metricScalarAt ((Kh k).stageMetric ((Kh k).activeStage v) v) z →
              (Kh k).HasSpatialCanonicalTimeControl ε C1 C2 Ctime v z) →
          (∀ T : ℝ, 0 < T → ∀ᶠ k in atTop, (aSeed k : ℝ) ≤ σ k - T / R k) →
          (∀ T : ℝ, 0 < T → ∀ᶠ k in atTop, (Tn k : ℝ) - 1 ^ (2 : ℕ) / 2 ≤ (σ k : ℝ) - T / R k) →
          Tendsto (fun k => R k * ((σ k : ℝ) - ((Tn k : ℝ) - 1 ^ (2 : ℕ) / 2))) atTop atTop →
          Tendsto (fun k => 1 / 200 * Real.sqrt (R k)) atTop atTop →
          (∀ᶠ k in atTop,
            riemannianEDistOf ((Kh k).stageMetric ((Kh k).activeStage (σ k)) (σ k))
                ((seedTrace k).point ((Kh k).activeStage (σ k)) ((Kh k).activeStage_mono (has k))
                  ((Kh k).activeStage_mono (hsT k))) (y k) +
              ENNReal.ofReal ((L k + 1) / Real.sqrt (R k)) ≤ ENNReal.ofReal ((Aseed + 3) * 1)) →
        ∀ i : ∀ k, Fin (Kh k).eventCount, (∀ k, (σ k : ℝ) = (Kh k).time (i k).succ) →
        ∃ ρ : ℕ → ℝ, Tendsto (fun k => ρ k * Real.sqrt (R k)) atTop atTop ∧
          ∀ᶠ k in atTop, ∀ (p' : ((Kh k).stage (i k).castSucc).Carrier)
            (q : ((Kh k).stage (i k).succ).Carrier), HEq (y k) q →
            ((Kh k).event (i k)).RegularCrossing p' q →
            ∀ᶠ t in 𝓝[<] (Kh k).time (i k).succ,
              ∀ (tt : Icc (0 : ℝ) (Kh k).horizon), (tt : ℝ) = t →
              ∀ y' : ((Kh k).stageAt tt).Carrier, HEq y' p' →
                (Kh k).isTracedRegion tt y' (r / Real.sqrt (R k)) (T / R k) (K₀ * R k) →
              ∀ x ∈ riemannianBallOf ((Kh k).stageMetric ((Kh k).activeStage tt) tt) y'
                  (r / Real.sqrt (R k)),
              ∀ (v : Icc (0 : ℝ) (Kh k).horizon) (hvt : v ≤ tt), (tt : ℝ) - T / R k ≤ v →
              ∀ tr : BackwardPointTrace (Kh k) ((Kh k).activeStage v) ((Kh k).activeStage tt)
                ((Kh k).activeStage_mono hvt) x,
              ∀ b : ℝ, 0 < b → b ≤ ρ k →
                (Kh k).isParabolicallyRmControlledBall v
                  (tr.point ((Kh k).activeStage v) le_rfl ((Kh k).activeStage_mono hvt)) b →
                ENNReal.ofReal (κ * b ^ 3) ≤
                  Geometry.Collapse.ballVolume ((Kh k).stageMetric ((Kh k).activeStage v) v)
                    (tr.point ((Kh k).activeStage v) le_rfl ((Kh k).activeStage_mono hvt)) b := by
  obtain ⟨ε₀, hε₀, h⟩ := hkappaC_tower_of_fresh_P6KA.{u}
  refine ⟨ε₀, hε₀, ?_⟩
  intro P g F ε C1 C2 Ctime qp Aseed nr κ Tf K₀ hAs hκ hsup hC2 hDm hacc hm hδlim hK₀ hfamT
  exact h (Ktr := fun _ _ => K₀) hAs hκ hsup hC2 hDm hacc hm hδlim (fun _ _ => hK₀) hfamT

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
