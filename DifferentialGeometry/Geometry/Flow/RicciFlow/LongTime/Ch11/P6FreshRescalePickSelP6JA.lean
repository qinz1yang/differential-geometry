import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.P6FreshRescaleP6JA
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.P6PickedCenterSelP6PS

/-!
# J11 adapter 的 PICKSEL consumer：中心 κ 字段（O-CH11-J11ADAPT G2，后缀 `_P6JA`）

PICKSEL `pickedCenterNeighborhood_of_hgood_fresh_P6PS` 的 κ 槽 `hW` 是 shallow 线 history `K n` 上的
单 history FRESH supply。shallow 线 `K` 是 HP3 / selection 的**重标度** family 时
（PBKAPPA HANDOVER 3、PICKSEL (3)），
`hW` 由 G1 `fresh_rescale_adapter_P6JA`（原尺度 ⇒ 重标度）实付：
`pickedCenterNeighborhood_of_hgood_freshOrig_P6JA`。剩余 binder 表 = PICKSEL 原表去掉 `hW`：`hWS`（WindowSeed，
等 R-C11-18 路线 (i)/(ii)）、`hRic`（中心端点 Ricci，owner DIST）、`hdσ`（top gate，= HP3 joint prefix
`hdistσ` 同式，见 `hκPB_of_fresh_jointPrefix_P6JA` 的单调放大）、seed prefix（hgood 同一 prefix）。
**依赖**：PICKSEL 模块未入 SNAP / 未 tracked（AUDITFIX 补审计块后由 INT 收）；本文件对 PICKSEL sha256
`49cad8ec…7216` 编译。陈述由 build-logs/scratch/O-CH11-J11ADAPT/gen/gen_picksel.py 逐字抽取 + 定点替换生成。
-/

set_option autoImplicit false

noncomputable section

open Set Filter Function
open DifferentialGeometry.Geometry.Curvature DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Geometry.Connection DifferentialGeometry.Geometry.Collapse
open DifferentialGeometry.CheegerGromovCompactness
open DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood
open scoped Manifold NNReal Topology ContDiff ENNReal

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

universe u

open Perelman.CanonicalNeighborhood.FiniteHorn (SpatialCanonicalWitness)

section PerCenter

variable {K : ℕ → RetainedCoreHistory.{u}}
  {Tn aSeed σ : ∀ n, Icc (0 : ℝ) (K n).toHistory.horizon}
  {haT : ∀ n, aSeed n ≤ Tn n} {hsT : ∀ n, σ n ≤ Tn n} {has : ∀ n, aSeed n ≤ σ n}
  {pT : ∀ n, ((K n).toHistory.stageAt (Tn n)).Carrier}
  {seedTrace : ∀ n, BackwardPointTrace (K n).toHistory ((K n).toHistory.activeStage (aSeed n))
    ((K n).toHistory.activeStage (Tn n)) ((K n).toHistory.activeStage_mono (haT n)) (pT n)}
  {y : ∀ n, ((K n).toHistory.stageAt (σ n)).Carrier} {R L : ℕ → ℝ} {eps C1 C2 : ℝ}
  {Ctime : ℝ≥0} {Cg : ℝ}

/-- **PICKSEL κ 字段 consumer（`_P6JA`，PROVISIONAL：binder 同 PICKSEL 去掉 `hW`——`hWS`（WindowSeed，
等 R-C11-18）、`hRic`（端点 Ricci，owner DIST））**：`pickedCenterNeighborhood_of_hgood_fresh_P6PS` 逐字，
κ 槽的单 history supply `hW : KappaSeedWindowFwd_C11PK nr A κ Tκ (K n)` 换成：
shallow 线 family 是重标度 family
（`hK : K k = (F.tower.history (ind k)).rescale_P6N (c k)`）+ **原尺度** FRESH supply `hsup`
（PBKAPPA producer 形，
`∀ m`）+ `Tf/c_n ≤ Tn`；`nr = nr₀(c_n ·)/√c_n`。`hW` 由 J11 adapter `fresh_rescale_adapter_P6JA` 实付。 -/
theorem pickedCenterNeighborhood_of_hgood_freshOrig_P6JA
    (hgood : ObservedHistory.HgoodCg_C11SH Cg (fun n => (K n).toHistory) Tn aSeed σ haT hsT has pT
      seedTrace y R L eps C1 C2 Ctime)
    (n : ℕ) {Dw Dc Tc θ qthr ρ κ ℓ A r : ℝ} {Cgrad : ℝ≥0}
    (hRn : 0 < R n) (hDc : 0 ≤ Dc) (hθ : 0 ≤ θ) (hℓ : 0 < ℓ)
    (hLR : 4 * (Dc + 8 * θ / (ℓ * Real.sqrt (R n))) ≤ 3 * L n)
    (hTL : Tc + θ ≤ L n ^ 2) (haS : (aSeed n : ℝ) ≤ (σ n : ℝ) - (Tc + θ) / R n)
    (hq : Cg * R n ≤ qthr) (hC2 : C2 ≤ (Cgrad : ℝ))
    (hdl : ∀ x ∈ riemannianBallOf ((K n).toHistory.stageMetric ((K n).toHistory.activeStage (σ n))
          (σ n)) (y n) (Dw / Real.sqrt (R n)),
        ∀ (v : Icc (0 : ℝ) (K n).toHistory.horizon) (hav : aSeed n ≤ v) (hvs : v ≤ σ n),
          (σ n : ℝ) - Tc / R n ≤ v →
        ∀ tr : BackwardPointTrace (K n).toHistory ((K n).toHistory.activeStage v)
            ((K n).toHistory.activeStage (σ n)) ((K n).toHistory.activeStage_mono hvs) x,
          riemannianEDistOf ((K n).toHistory.stageMetric ((K n).toHistory.activeStage v) v)
              ((seedTrace n).point ((K n).toHistory.activeStage v)
                  ((K n).toHistory.activeStage_mono hav)
                ((K n).toHistory.activeStage_mono (hvs.trans (hsT n))))
              (tr.point ((K n).toHistory.activeStage v) le_rfl
                  ((K n).toHistory.activeStage_mono hvs)) ≤
            riemannianEDistOf ((K n).toHistory.stageMetric ((K n).toHistory.activeStage (σ n))
                (σ n))
              ((seedTrace n).point ((K n).toHistory.activeStage (σ n))
                ((K n).toHistory.activeStage_mono (has n))
                ((K n).toHistory.activeStage_mono (hsT n))) (y n) +
              ENNReal.ofReal (L n / 4 / Real.sqrt (R n)))
    (O : ∀ j' : Fin (K n).eventCount, ((K n).stage j'.castSucc).Carrier)
    (hO : ∀ (j' : Fin (K n).eventCount)
      (h1 : (K n).toHistory.activeStage (aSeed n) ≤ j'.castSucc)
      (h2 : j'.castSucc ≤ (K n).toHistory.activeStage (Tn n)),
      O j' = (seedTrace n).point j'.castSucc h1 h2)
    (hWS : PickedCenterWindowSeed_C11PT Dw Dc Tc θ (R n) qthr (K n) (σ n) (y n) O
      (riemannianEDistOf ((K n).toHistory.stageMetric ((K n).toHistory.activeStage (σ n))
           (σ n))
         ((seedTrace n).point ((K n).toHistory.activeStage (σ n))
           ((K n).toHistory.activeStage_mono (has n))
           ((K n).toHistory.activeStage_mono (hsT n))) (y n) +
        ENNReal.ofReal (L n / Real.sqrt (R n))))
    {P : OrientedThreeStage.{u}} {g : P.Metric} {F : GC.Interface.RawSurgery P g}
    {ind : ℕ → ℕ} {c : ℕ → ℝ} (hc : ∀ k, 0 < c k)
    (hK : ∀ k, K k = (F.tower.history (ind k)).rescale_P6N (c k) (hc k))
    {nr₀ : ℝ → ℝ} {Tf : ℝ}
    (hsup : ∀ m, KappaSeedWindowFwd_C11PK nr₀ A κ Tf (F.tower.history m).toHistory)
    (hTκ : Tf / c n ≤ (Tn n : ℝ))
    (htime : 2 * r ^ 2 < (Tn n : ℝ))
    (hsmall : GC.LongTime.hasSmallParabolicCurvature (K n).toHistory (Tn n) (pT n) r)
    (hvol : ENNReal.ofReal (A⁻¹ * r ^ 3) ≤ ballVolume ((K n).toHistory.stageMetric
      ((K n).toHistory.activeStage (Tn n)) (Tn n)) (pT n) r)
    (hnr : ∀ w : ℝ, (Tn n : ℝ) - r ^ 2 / 2 ≤ w → w ≤ (Tn n : ℝ) →
      nr₀ (c n * w) / Real.sqrt (c n) ≤ r)
    (hclock : (aSeed n : ℝ) = (Tn n : ℝ) - r ^ 2)
    (hwinF : (Tn n : ℝ) - r ^ 2 / 2 ≤ (σ n : ℝ) - (Tc + θ) / R n)
    (hρ : ρ < r / 100) (hκ : 0 ≤ κ)
    (hdσ : riemannianEDistOf ((K n).toHistory.stageMetric ((K n).toHistory.activeStage (σ n))
          (σ n))
        ((seedTrace n).point ((K n).toHistory.activeStage (σ n))
          ((K n).toHistory.activeStage_mono (has n))
          ((K n).toHistory.activeStage_mono (hsT n))) (y n) +
      ENNReal.ofReal ((L n + 1) / Real.sqrt (R n)) ≤ ENNReal.ofReal (A * r))
    (hRic : ∀ (j' : Fin (K n).eventCount) (v : ℝ), (K n).time j'.castSucc < v →
        v < (K n).time j'.succ → (σ n : ℝ) - Tc / R n ≤ v → v ≤ σ n →
      ∀ x₁ ∈ riemannianBallOf ((K n).toHistory.stageMetric ((K n).toHistory.activeStage (σ n))
          (σ n)) (y n) (Dw / Real.sqrt (R n)),
      ∀ (hjσ : j'.castSucc ≤ (K n).toHistory.activeStage (σ n))
        (tr : BackwardPointTrace (K n).toHistory j'.castSucc
          ((K n).toHistory.activeStage (σ n)) hjσ x₁),
      ∀ x ∈ riemannianBallOf (((K n).toHistory.event j').incoming.flow.base.metric v)
          (tr.point j'.castSucc le_rfl hjσ) (Dc / Real.sqrt (R n)),
      ∀ (h1 : (K n).toHistory.activeStage (aSeed n) ≤ j'.castSucc)
        (h2 : j'.castSucc ≤ (K n).toHistory.activeStage (Tn n)),
      ∀ t : ℝ, v - θ / R n < t → t < v → (K n).time j'.castSucc < t →
      ∀ (yy : ((K n).stage j'.castSucc).Carrier) (ξ : TangentSpace ThreeModel yy),
        (riemannianEDistOf (((K n).toHistory.event j').incoming.flow.base.metric t)
            ((seedTrace n).point j'.castSucc h1 h2) yy < ENNReal.ofReal ℓ ∨
          riemannianEDistOf (((K n).toHistory.event j').incoming.flow.base.metric t) x yy <
            ENNReal.ofReal ℓ) →
        ricciTensor (((K n).toHistory.event j').incoming.flow.base.metric t) yy ξ ξ ≤
          (3 / ℓ ^ 2) * (((K n).toHistory.event j').incoming.flow.base.metric t).inner yy ξ ξ) :
    PickedCenterNeighborhood_C11PT Dw Dc Tc θ (R n) qthr ρ κ eps C1 C2 Cgrad (K n) (σ n)
      (y n) := by
  have hW : KappaSeedWindowFwd_C11PK (fun w => nr₀ (c n * w) / Real.sqrt (c n)) A κ (Tf / c n)
      (K n).toHistory := by
    rw [hK n]
    exact GC.LongTime.Ch11.fresh_rescale_adapter_P6JA hsup ind c hc n
  exact pickedCenterNeighborhood_of_hgood_fresh_P6PS hgood n hRn hDc hθ hℓ hLR hTL haS hq hC2 hdl O
    hO hWS hW hTκ htime hsmall hvol hnr hclock hwinF hρ hκ hdσ hRic

end PerCenter

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
