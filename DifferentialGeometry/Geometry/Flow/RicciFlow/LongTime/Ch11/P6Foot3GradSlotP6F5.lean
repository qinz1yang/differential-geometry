import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.P6Foot3DerivSlotP6F5
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.P6TerminalBCDLocalDerivP6F3
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.P6J10WireStayProdP6JW

/-!
# FOOT3 局域五项之 `hgradL`：HP6B2 v2 槽 ⇐ hgood witness 梯度 + seed localization
# （O-CH11-FOOT5 G2，后缀 `_P6F5`）

**G2 `hgradL_slot_of_hgood_stay_P6F5`**（PROVISIONAL[`hstaySlot`]；选择子约束 `hCg4`）：结论 = HP6B2 v2
`hP6bTwoLevelTime_of_slots_v2_P6HPB2` 的 `hgradL` 槽**逐字**（gen 从 l.1343–1409 切出）。证明：
* 梯度来源 = 前缀里的 `hgood`（`HasSpatialCanonicalTimeControl` 的空间 witness，
  `SpatialCanonicalWitness.gradient` 是 witness 点自身的逐点界 `|dR| ≤ C₂ R^{3/2}|ξ|`；同 PICKBALL G4
  `pickedBallGrad_of_hgood_C11PB` /
  ANCHOR4 `hgradL_of_hgood_witness_P6AN4` 的取法）；`Cgrad := C2.toNNReal`
  （`C2 = C2P6 std Γ`，与 T r 无关）；
* 阈值：槽 `Cg·R_k < R(v′, z)` ⇒ hgood 门槛 `4·R_k ≤ R`，需 **`hCg4 : ∀ Γ Γf, 4 ≤ Cgsel Γ Γf`**
  （与 G1 同一共享选择子约束；显式 binder，不进 env）；
* 时间窗：`v′ ∈ [t − T/R_k, t)`，`t ↑ σ_k` ⇒ `aSeed ≤ v′`（前缀 `hwin (2T)`）、`σ − L²/R ≤ v′`（`L → ∞`），
  与 FOOT3 `hderivL_of_hgood_P6F3` 同一 filter 骨架；
* **seed localization**（hgood 区域成员资格 `d_{v′}(seed, z) ≤ d_σ(seed_σ, y) + L/√R`）=
  binder **`hstaySlot`**：FOOT3 G3 的 `hstayΩ` 正文**逐字**（`P6TerminalBCDLocalDerivP6F3.lean` l.158–211，
  对 HP6b env 全称、常数钉住）；
  当前 slab 合取用 singleton trace（同 FOOT3 证明）。
**family 对齐**：`hstaySlot` 与槽同一族（同 `Kh k = (F.tower.history (ind k)).rescale_P6N (c k)`、
同 `seedTrace`、同 `σ y R L`、同 crossing `p′`、同 `t ↑ σ`），不经 picked-ball 二次选点（PICKBALL 的 `w = yG n`
中心与此处 `p′`
不同族，故 PickedBall 合同不能直接喂；本文件直接用 hgood 单点核）。
**G2b `hderivL_slot_of_hgood_stay_P6F5`**（同一 binder 的 `hderivL` 槽另一路线）：= FOOT3
`hderivL_of_hgood_P6F3`（PROVISIONAL[`hstayΩ`]，`Cg = 4`、`Cder = Ctime`）在 env 上实例化 + 同一阈值单调。
⇒ `hderivL` 与 `hgradL` 两槽可由**同一个** seed-localization binder `hstaySlot` 付（`hderivL` 另有 G1 的
[`hTR`, `hfamT`] 路线）。
**`hstaySlot` 的精确 repair target**（不在本车道证）：
1. 当前 slab、窗口 `≤ β/q`：WSBASE `windowSeed_pointAnchor_C11WB`（PROVED，无 binder）在 `x := z`、
   `v := t` 给 `[t − β/q, t]` 上的 closure，输入 = top 时刻 ExitGuard `d_t(seed, z) ≤ dσ + (Lc/2)/√R`（⇐
   G3 的 `hmargin` 槽
   PROVED + `z ∈ B_t(p′, r/√R)`，取 `δ := 1/√R_k`、`Lc := L_k/2`）与 top anchor `R(t, z) ≤ Λq`
   （⇐ `hTR` 在端点时刻，BCDBOOT `hballT_of_tracedRegion_P6BB`）；预算 `Ctime·Λ·β ≤ 1/2`。
2. 任意深度 `T`（槽对 `∀ T` 全称）与跨 slab trace（`∀ first B m`）：point-anchor 单步窗口 `β/q`
   不够长，迭代需要中间时刻的 anchor = `hTR` 的 traced-region 曲率界；drift 由 8.3(b)（端点 Ricci：seed 端 K0、移动端 `R ≤
   Ktr·R_k`）
   给 `(t − v′)·C√(Ktr R_k) ≤ C·T·√Ktr/√R_k = o(L_k/√R_k)`。即
   **`hstaySlot` ⇐ `hTR` + `hmargin`（PROVED）+ HI + 8.3(b) drift**，与 G1 的 `hTR`
   同一合同（不新增分析义务）；guarded 链（GUARDWIRE）只在 guard 后缀给 closure，
   不能直接付 `∀ T` 槽（WSBASE G2：公共窗 base 有 Bryant-tip 障碍）。
生成：build-logs/scratch/O-CH11-FOOT5/gen/gen_g2.py。
-/

set_option autoImplicit false

noncomputable section

open Set Filter Function
open DifferentialGeometry DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.CheegerGromovCompactness
open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Geometry.Connection
open DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood
open DifferentialGeometry.Geometry.Collapse
open scoped Manifold NNReal Topology ContDiff ENNReal

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

universe u

open Perelman.CanonicalNeighborhood.FiniteHorn
open GC.GeneralFlow (ClosedBirthConstants)
open GC.LongTime.Ch11 (p6CoarseC_C11GT6 p6FineEta_C11GT6 p6FineEta_pos_C11GT6 epsW_CXOU2)
open GC.LongTime.Ch11 (BlockTower_C11W capWindowRadius_C11E FineOf_C11G2 BudgetCertificate_C11GT2
  SameConstructionRetentionSupplyPlus_C11GT6 chainDiagonal_C11A C1P6_C11GT6 C2P6_C11GT6
  p6X1std_C11GT6 p6X2std_C11GT6 p6Ctime_C11G7B p6BadC_C11G2 htransMBad_C11G7B)

namespace ObservedHistory

/-- **G2 `hgradL_slot_of_hgood_stay_P6F5`**（PROVISIONAL[`hstaySlot`]；选择子约束 `hCg4`）：
结论 = HP6B2 v2 `hgradL` 槽逐字；`Cgrad := C2.toNNReal`，梯度 = hgood witness 的 `gradient` 字段，seed
localization =
`hstaySlot`（FOOT3 `hstayΩ` 逐字）。 -/
theorem hgradL_slot_of_hgood_stay_P6F5 (P : OrientedThreeStage.{u}) (g : P.Metric)
    (εP6 : ClosedBirthConstants → ClosedBirthConstants → ℝ)
    (Cgsel : ClosedBirthConstants → ClosedBirthConstants → ℝ)
    (hCg4 : ∀ Γ Γf, 4 ≤ Cgsel Γ Γf)
    (hstaySlot :
      ∀ {pB : CutoffParameters} {Γ Γf : ClosedBirthConstants}, FineOf_C11G2.{u} Γf Γ →
      Γ.epsilon ≤ εStrong_C12X.{u} → Γ.epsilon ≤ epsW_CXOU2.{u} →
      ∀ (Cdist : ℝ≥0) (εReserve : ℝ)
        (T : BlockTower_C11W pB Γf P g Cdist 1 (capWindowRadius_C11E + 1) εReserve),
      (∀ j, BudgetCertificate_C11GT2 pB.recenterConstant Γf.Ctime j
        (T.block j) (T.lookahead j) (T.request j)) →
      SameConstructionRetentionSupplyPlus_C11GT6 T →
      ∀ (F : GC.Interface.RawSurgery P g) (q : CutoffParameters), F.tower = T.toChain.tower →
      (∀ t : ℝ, 0 ≤ t → q.delta t = (chainDiagonal_C11A T.toChain).delta t ∧
        q.neckRadius t = (chainDiagonal_C11A T.toChain).neckRadius t) →
      pB.modelAccuracy ≤ εP6 Γ Γf → capWindowRadius_C11E + 1 ≤ pB.modelRadius →
      2 ≤ pB.modelOrder →
      ∀ {ε C1 C2 : ℝ} {Ctime : ℝ≥0}, ε = Γ.epsilon →
      C1 = C1P6_C11GT6.{u} p6X1std_C11GT6.{u} Γ →
      C2 = C2P6_C11GT6.{u} p6X2std_C11GT6.{u} Γ →
      Ctime = p6Ctime_C11G7B.{u} Γ →
      ∀ (T r : ℝ), 0 < T → 0 < r →
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
        ∀ i : ∀ k, Fin (Kh k).eventCount, (∀ k, (σ k : ℝ) = (Kh k).time (i k).succ) →
        ∀ᶠ k in atTop, ∀ (p' : ((Kh k).stage (i k).castSucc).Carrier)
          (q : ((Kh k).stage (i k).succ).Carrier), HEq (y k) q →
          ((Kh k).event (i k)).RegularCrossing p' q →
          ∀ᶠ t in 𝓝[<] (Kh k).time (i k).succ,
            ∀ (first : Fin ((Kh k).eventCount + 1)) (hfl : first ≤ (i k).castSucc),
            ∀ z ∈ riemannianBallOf (((Kh k).event (i k)).incoming.flow.base.metric t) p'
                (r / Real.sqrt (R k)),
            ∀ (B : BackwardPointTrace (Kh k) first (i k).castSucc hfl z)
              (m : Fin ((Kh k).eventCount + 1)) (hf : first ≤ m) (hm : m ≤ (i k).castSucc)
              (v : Icc (0 : ℝ) (Kh k).horizon) (hav : aSeed k ≤ v) (hvs : v ≤ σ k),
              t - T / R k ≤ (v : ℝ) → (v : ℝ) ≤ t → (Kh k).activeStage v = m →
            ∀ zz : ((Kh k).stageAt v).Carrier, HEq zz (B.point m hf hm) →
              riemannianEDistOf ((Kh k).stageMetric ((Kh k).activeStage v) v)
                  ((seedTrace k).point ((Kh k).activeStage v) ((Kh k).activeStage_mono hav)
                    ((Kh k).activeStage_mono (hvs.trans (hsT k)))) zz ≤
                riemannianEDistOf ((Kh k).stageMetric ((Kh k).activeStage (σ k)) (σ k))
                    ((seedTrace k).point ((Kh k).activeStage (σ k))
                      ((Kh k).activeStage_mono (has k)) ((Kh k).activeStage_mono (hsT k))) (y k) +
                  ENNReal.ofReal (L k / Real.sqrt (R k))
      ) :
      ∀ {pB : CutoffParameters} {Γ Γf : ClosedBirthConstants}, FineOf_C11G2.{u} Γf Γ →
      Γ.epsilon ≤ εStrong_C12X.{u} → Γ.epsilon ≤ epsW_CXOU2.{u} →
      ∀ (Cdist : ℝ≥0) (εReserve : ℝ)
        (T : BlockTower_C11W pB Γf P g Cdist 1 (capWindowRadius_C11E + 1) εReserve),
      (∀ j, BudgetCertificate_C11GT2 pB.recenterConstant Γf.Ctime j
        (T.block j) (T.lookahead j) (T.request j)) →
      SameConstructionRetentionSupplyPlus_C11GT6 T →
      ∀ (F : GC.Interface.RawSurgery P g) (q : CutoffParameters), F.tower = T.toChain.tower →
      (∀ t : ℝ, 0 ≤ t → q.delta t = (chainDiagonal_C11A T.toChain).delta t ∧
        q.neckRadius t = (chainDiagonal_C11A T.toChain).neckRadius t) →
      pB.modelAccuracy ≤ εP6 Γ Γf → capWindowRadius_C11E + 1 ≤ pB.modelRadius →
      2 ≤ pB.modelOrder →
      ∀ {ε C1 C2 : ℝ} {Ctime : ℝ≥0}, ε = Γ.epsilon →
      C1 = C1P6_C11GT6.{u} p6X1std_C11GT6.{u} Γ →
      C2 = C2P6_C11GT6.{u} p6X2std_C11GT6.{u} Γ →
      Ctime = p6Ctime_C11G7B.{u} Γ →
      ∀ {Cg : ℝ}, Cg = Cgsel Γ Γf →
      ∃ Cgrad : ℝ≥0,
        ∀ (T r : ℝ), 0 < T → 0 < r →
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
          ∀ i : ∀ k, Fin (Kh k).eventCount, (∀ k, (σ k : ℝ) = (Kh k).time (i k).succ) →
          ∀ᶠ k in atTop, ∀ (p' : ((Kh k).stage (i k).castSucc).Carrier)
            (q : ((Kh k).stage (i k).succ).Carrier), HEq (y k) q →
            ((Kh k).event (i k)).RegularCrossing p' q →
            ∀ᶠ t in 𝓝[<] (Kh k).time (i k).succ,
              ∀ z ∈ riemannianBallOf (((Kh k).event (i k)).incoming.flow.base.metric t) p'
                  (r / Real.sqrt (R k)),
                ∀ v' ∈ Ioo ((Kh k).time (i k).castSucc) t, t - T / R k ≤ v' →
                  Cg * R k < ((Kh k).event (i k)).incoming.flow.scalar v' z →
                  ∀ ξ : TangentSpace ThreeModel z,
                    |scalarDifferential ((Kh k).event (i k)).incoming.flow v' z ξ| ≤
                      Cgrad * ((Kh k).event (i k)).incoming.flow.scalar v' z *
                        Real.sqrt (((Kh k).event (i k)).incoming.flow.scalar v' z) *
                        Real.sqrt
                          ((((Kh k).event (i k)).incoming.flow.base.metric v').inner z ξ ξ) := by
  intro pB Γ Γf hfine hs hW Cdist εReserve T hcert hS F q hF hq hacc hrad hord ε C1 C2 Ctime
    hε hC1 hC2 hCt Cg hCg
  have hst0 := hstaySlot hfine hs hW Cdist εReserve T hcert hS F q hF hq hacc hrad hord hε hC1 hC2
    hCt
  have h4 : (4 : ℝ) ≤ Cg := hCg ▸ hCg4 Γ Γf
  refine ⟨C2.toNNReal, ?_⟩
  intro Tw r hTw hr ind c hc Kh Tn pT hTc aSeed haT hclock hone hsm seedTrace σ y R hsT has L hRdef
    hRpos hRr hL hsel hgood haS hTnS hroom hradii i hi
  have hst := hst0 Tw r hTw hr ind c hc Tn pT hTc aSeed haT hclock hone hsm seedTrace σ y R hsT has
    L hRdef hRpos hRr hL hsel hgood haS hTnS hroom hradii i hi
  have h2T : (0 : ℝ) < 2 * Tw := by positivity
  filter_upwards [hst, hL.eventually_ge_atTop (2 * Tw + 1), haS (2 * Tw) h2T] with k hsk hLk haSk
  intro p' q' hq' hcross
  have hRk := hRpos k
  have hσs : (σ k : ℝ) = (Kh k).time (i k).succ := hi k
  have hcs : (Kh k).time (i k).castSucc < (Kh k).time (i k).succ :=
    (Kh k).time_strictMono Fin.castSucc_lt_succ
  have hTR : 0 < Tw / R k := div_pos hTw hRk
  have hL2 : 2 * Tw / R k ≤ L k ^ (2 : ℕ) / R k := by
    refine div_le_div_of_nonneg_right ?_ hRk.le
    nlinarith [mul_le_mul hLk hLk (by linarith) (by linarith)]
  have h2TR : 2 * Tw / R k = Tw / R k + Tw / R k := by ring
  filter_upwards [hsk p' q' hq' hcross, Ioo_mem_nhdsLT (show max ((Kh k).time (i k).castSucc)
      ((Kh k).time (i k).succ - Tw / R k) < (Kh k).time (i k).succ from max_lt hcs (by linarith))]
    with t hstt ht
  have ht2 : (Kh k).time (i k).succ - Tw / R k < t := lt_of_le_of_lt (le_max_right _ _) ht.1
  have haA : (aSeed k : ℝ) ≤ t - Tw / R k := by linarith
  have hbσ : t ≤ (σ k : ℝ) := by linarith [ht.2]
  have haL : (σ k : ℝ) - L k ^ (2 : ℕ) / R k ≤ t - Tw / R k := by linarith
  intro z hz v' hv' hwin hRv' ξ
  have hv0 : 0 ≤ v' := ((Kh k).time_nonneg _).trans hv'.1.le
  have hv2 : v' < (Kh k).time (i k).succ := hv'.2.trans ht.2
  have hvH : v' ≤ (Kh k).horizon := hv2.le.trans ((Kh k).time_le_horizon_at _)
  let vv : Icc (0 : ℝ) (Kh k).horizon := ⟨v', hv0, hvH⟩
  have hav : aSeed k ≤ vv := show (aSeed k : ℝ) ≤ v' by linarith
  have hvs : vv ≤ σ k := show v' ≤ (σ k : ℝ) by linarith [hv'.2]
  have hact : (Kh k).activeStage vv = (i k).castSucc :=
    (Kh k).activeStage_eq_of_mem_slab_P6F3 (i k) vv hv'.1.le hv2
  obtain ⟨zz, hzz⟩ := exists_heq_stageAt_P6JW (Kh k) hact z
  have hd := hstt (i k).castSucc le_rfl z hz (BackwardPointTrace.singleton (Kh k) (i k).castSucc z)
    (i k).castSucc le_rfl le_rfl vv hav hvs hwin hv'.2.le hact zz hzz
  have hsc := ObservedHistory.scalar_transport_P6BB hact (rfl : (vv : ℝ) = v') zz z hzz
  have h4R : 4 * R k ≤ metricScalarAt ((Kh k).stageMetric ((Kh k).activeStage vv) vv) zz := by
    rw [hsc, ObservedHistory.stageMetric_castSucc_apply]
    exact (mul_le_mul_of_nonneg_right h4 hRk.le).trans hRv'.le
  have hσL : (σ k : ℝ) - L k ^ (2 : ℕ) / R k ≤ (vv : ℝ) := haL.trans hwin
  have hctl := hgood k vv hav hvs hσL zz hd h4R
  have key : ∀ (m : Fin ((Kh k).eventCount + 1)) (hm : (Kh k).activeStage vv = m)
      (x' : ((Kh k).stage m).Carrier), HEq zz x' →
      ∃ W : SpatialCanonicalWitness ((Kh k).stageMetric m v') ε C1 C2 x',
        W.capTubeHasNeckChart ε := by
    intro m hm x' hx'
    subst hm
    obtain rfl := eq_of_heq hx'
    exact hctl.1
  have hres := key (i k).castSucc hact z hzz
  rw [ObservedHistory.stageMetric_castSucc_apply] at hres
  obtain ⟨W, -⟩ := hres
  have hR0 : 0 ≤ ((Kh k).event (i k)).incoming.flow.scalar v' z := W.Q_pos.le
  exact (W.gradient ξ).trans (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_right (Real.le_coe_toNNReal C2) hR0) (Real.sqrt_nonneg _))
    (Real.sqrt_nonneg _))

/-- **G2b `hderivL_slot_of_hgood_stay_P6F5`**（PROVISIONAL[`hstaySlot`]；选择子约束 `hCg4`）：
结论 = HP6B2 v2 `hderivL` 槽逐字；= FOOT3 `hderivL_of_hgood_P6F3` 在 env 上实例化（`Cder := C_t*(Γ)`，阈值 `4 ≤
Cg`）。 -/
theorem hderivL_slot_of_hgood_stay_P6F5 (P : OrientedThreeStage.{u}) (g : P.Metric)
    (εP6 : ClosedBirthConstants → ClosedBirthConstants → ℝ)
    (Cgsel : ClosedBirthConstants → ClosedBirthConstants → ℝ)
    (hCg4 : ∀ Γ Γf, 4 ≤ Cgsel Γ Γf)
    (hstaySlot :
      ∀ {pB : CutoffParameters} {Γ Γf : ClosedBirthConstants}, FineOf_C11G2.{u} Γf Γ →
      Γ.epsilon ≤ εStrong_C12X.{u} → Γ.epsilon ≤ epsW_CXOU2.{u} →
      ∀ (Cdist : ℝ≥0) (εReserve : ℝ)
        (T : BlockTower_C11W pB Γf P g Cdist 1 (capWindowRadius_C11E + 1) εReserve),
      (∀ j, BudgetCertificate_C11GT2 pB.recenterConstant Γf.Ctime j
        (T.block j) (T.lookahead j) (T.request j)) →
      SameConstructionRetentionSupplyPlus_C11GT6 T →
      ∀ (F : GC.Interface.RawSurgery P g) (q : CutoffParameters), F.tower = T.toChain.tower →
      (∀ t : ℝ, 0 ≤ t → q.delta t = (chainDiagonal_C11A T.toChain).delta t ∧
        q.neckRadius t = (chainDiagonal_C11A T.toChain).neckRadius t) →
      pB.modelAccuracy ≤ εP6 Γ Γf → capWindowRadius_C11E + 1 ≤ pB.modelRadius →
      2 ≤ pB.modelOrder →
      ∀ {ε C1 C2 : ℝ} {Ctime : ℝ≥0}, ε = Γ.epsilon →
      C1 = C1P6_C11GT6.{u} p6X1std_C11GT6.{u} Γ →
      C2 = C2P6_C11GT6.{u} p6X2std_C11GT6.{u} Γ →
      Ctime = p6Ctime_C11G7B.{u} Γ →
      ∀ (T r : ℝ), 0 < T → 0 < r →
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
        ∀ i : ∀ k, Fin (Kh k).eventCount, (∀ k, (σ k : ℝ) = (Kh k).time (i k).succ) →
        ∀ᶠ k in atTop, ∀ (p' : ((Kh k).stage (i k).castSucc).Carrier)
          (q : ((Kh k).stage (i k).succ).Carrier), HEq (y k) q →
          ((Kh k).event (i k)).RegularCrossing p' q →
          ∀ᶠ t in 𝓝[<] (Kh k).time (i k).succ,
            ∀ (first : Fin ((Kh k).eventCount + 1)) (hfl : first ≤ (i k).castSucc),
            ∀ z ∈ riemannianBallOf (((Kh k).event (i k)).incoming.flow.base.metric t) p'
                (r / Real.sqrt (R k)),
            ∀ (B : BackwardPointTrace (Kh k) first (i k).castSucc hfl z)
              (m : Fin ((Kh k).eventCount + 1)) (hf : first ≤ m) (hm : m ≤ (i k).castSucc)
              (v : Icc (0 : ℝ) (Kh k).horizon) (hav : aSeed k ≤ v) (hvs : v ≤ σ k),
              t - T / R k ≤ (v : ℝ) → (v : ℝ) ≤ t → (Kh k).activeStage v = m →
            ∀ zz : ((Kh k).stageAt v).Carrier, HEq zz (B.point m hf hm) →
              riemannianEDistOf ((Kh k).stageMetric ((Kh k).activeStage v) v)
                  ((seedTrace k).point ((Kh k).activeStage v) ((Kh k).activeStage_mono hav)
                    ((Kh k).activeStage_mono (hvs.trans (hsT k)))) zz ≤
                riemannianEDistOf ((Kh k).stageMetric ((Kh k).activeStage (σ k)) (σ k))
                    ((seedTrace k).point ((Kh k).activeStage (σ k))
                      ((Kh k).activeStage_mono (has k)) ((Kh k).activeStage_mono (hsT k))) (y k) +
                  ENNReal.ofReal (L k / Real.sqrt (R k))
      ) :
      ∀ {pB : CutoffParameters} {Γ Γf : ClosedBirthConstants}, FineOf_C11G2.{u} Γf Γ →
      Γ.epsilon ≤ εStrong_C12X.{u} → Γ.epsilon ≤ epsW_CXOU2.{u} →
      ∀ (Cdist : ℝ≥0) (εReserve : ℝ)
        (T : BlockTower_C11W pB Γf P g Cdist 1 (capWindowRadius_C11E + 1) εReserve),
      (∀ j, BudgetCertificate_C11GT2 pB.recenterConstant Γf.Ctime j
        (T.block j) (T.lookahead j) (T.request j)) →
      SameConstructionRetentionSupplyPlus_C11GT6 T →
      ∀ (F : GC.Interface.RawSurgery P g) (q : CutoffParameters), F.tower = T.toChain.tower →
      (∀ t : ℝ, 0 ≤ t → q.delta t = (chainDiagonal_C11A T.toChain).delta t ∧
        q.neckRadius t = (chainDiagonal_C11A T.toChain).neckRadius t) →
      pB.modelAccuracy ≤ εP6 Γ Γf → capWindowRadius_C11E + 1 ≤ pB.modelRadius →
      2 ≤ pB.modelOrder →
      ∀ {ε C1 C2 : ℝ} {Ctime : ℝ≥0}, ε = Γ.epsilon →
      C1 = C1P6_C11GT6.{u} p6X1std_C11GT6.{u} Γ →
      C2 = C2P6_C11GT6.{u} p6X2std_C11GT6.{u} Γ →
      Ctime = p6Ctime_C11G7B.{u} Γ →
      ∀ {Cg : ℝ}, Cg = Cgsel Γ Γf →
      ∃ Cder : ℝ≥0,
        ∀ (T r : ℝ), 0 < T → 0 < r →
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
          ∀ i : ∀ k, Fin (Kh k).eventCount, (∀ k, (σ k : ℝ) = (Kh k).time (i k).succ) →
          ∀ᶠ k in atTop, ∀ (p' : ((Kh k).stage (i k).castSucc).Carrier)
            (q : ((Kh k).stage (i k).succ).Carrier), HEq (y k) q →
            ((Kh k).event (i k)).RegularCrossing p' q →
            ∀ᶠ t in 𝓝[<] (Kh k).time (i k).succ,
              (∀ (first : Fin ((Kh k).eventCount + 1)) (hfl : first ≤ (i k).castSucc),
                ∀ z ∈ riemannianBallOf (((Kh k).event (i k)).incoming.flow.base.metric t) p'
                    (r / Real.sqrt (R k)),
                ∀ (B : BackwardPointTrace (Kh k) first (i k).castSucc hfl z)
                  (i' : Fin (Kh k).eventCount) (hf : first ≤ i'.castSucc)
                  (hij : i'.castSucc < (i k).castSucc),
                ∀ v' ∈ Ioo ((Kh k).time i'.castSucc) ((Kh k).time i'.succ), t - T / R k ≤ v' →
                  Cg * R k < ((Kh k).event i').incoming.flow.scalar v'
                    (B.point i'.castSucc hf hij.le) →
                  |derivWithin (fun w' => ((Kh k).event i').incoming.flow.scalar w'
                      (B.point i'.castSucc hf hij.le)) (Iic v') v'| ≤
                    Cder * ((Kh k).event i').incoming.flow.scalar v'
                      (B.point i'.castSucc hf hij.le) ^ 2) ∧
              ∀ z ∈ riemannianBallOf (((Kh k).event (i k)).incoming.flow.base.metric t) p'
                  (r / Real.sqrt (R k)),
                ∀ v' ∈ Ioo ((Kh k).time (i k).castSucc) t, t - T / R k ≤ v' →
                  Cg * R k < ((Kh k).event (i k)).incoming.flow.scalar v' z →
                  |derivWithin (fun w' => ((Kh k).event (i k)).incoming.flow.scalar w' z)
                      (Iic v') v'| ≤
                    Cder * ((Kh k).event (i k)).incoming.flow.scalar v' z ^ 2 := by
  intro pB Γ Γf hfine hs hW Cdist εReserve T hcert hS F q hF hq hacc hrad hord ε C1 C2 Ctime
    hε hC1 hC2 hCt Cg hCg
  have hst0 := hstaySlot hfine hs hW Cdist εReserve T hcert hS F q hF hq hacc hrad hord hε hC1 hC2
    hCt
  have h4 : (4 : ℝ) ≤ Cg := hCg ▸ hCg4 Γ Γf
  refine ⟨Ctime, ?_⟩
  intro Tw r hTw hr ind c hc Kh Tn pT hTc aSeed haT hclock h1 hsm seedTrace σ y R hsT has L hRdef
    hRpos hRr hL hsel hgood hwin hwin' hroom hradii i hi
  have hmain := hderivL_of_hgood_P6F3 (F := F) (ε := ε) (C1 := C1) (C2 := C2) (Ctime := Ctime)
    hst0 Tw r hTw hr ind c hc Tn pT hTc aSeed haT hclock h1 hsm seedTrace σ y R hsT has L hRdef
    hRpos hRr hL hsel hgood hwin hwin' hroom hradii i hi
  filter_upwards [hmain] with k hk
  intro p' q' hq' hcr
  filter_upwards [hk p' q' hq' hcr] with t ht
  have hlt : ∀ x : ℝ, Cg * R k < x → 4 * R k < x := fun x hx =>
    lt_of_le_of_lt (mul_le_mul_of_nonneg_right h4 (hRpos k).le) hx
  exact ⟨fun first hfl z hz B i' hf hij v' hv' hvt hx =>
      ht.1 first hfl z hz B i' hf hij v' hv' hvt (hlt _ hx),
    fun z hz v' hv' hvt hx => ht.2 z hz v' hv' hvt (hlt _ hx)⟩

/-- consumer（G2 / G2b → HP6B2 v2）：`hderivL`、`hgradL` 两槽由同一 `hstaySlot` 付，喂
`hP6bTwoLevelTime_of_slots_v2_P6HPB2`（其余参数保持 binder）。 -/
example (P : OrientedThreeStage.{u}) (g : P.Metric) : True := by
  have _h := fun εP6 hεP6 Csel T₀sel Qtsel hmono Cgsel hCg4 hgapJ hgapJ8 hgapJF hgapJF8 hmargin
      hrecords hpinch hstaySlot hdistLA hscaleSep hcollar =>
    hP6bTwoLevelTime_of_slots_v2_P6HPB2 P g εP6 hεP6 Csel T₀sel Qtsel hmono Cgsel hgapJ hgapJ8
      hgapJF hgapJF8 hmargin hrecords hpinch
      (hderivL_slot_of_hgood_stay_P6F5 P g εP6 Cgsel hCg4 hstaySlot)
      (hgradL_slot_of_hgood_stay_P6F5 P g εP6 Cgsel hCg4 hstaySlot) hdistLA hscaleSep hcollar
  trivial

end ObservedHistory

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
