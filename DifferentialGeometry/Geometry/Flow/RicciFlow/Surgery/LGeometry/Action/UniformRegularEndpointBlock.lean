import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.LGeometry.Action.ClosedTimeACSplice
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.LGeometry.Action.RecentNodePhysicalSupport
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.LGeometry.Action.C1Attainment
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.History.PreparedSpatialPhysicalPolicy
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.ParabolicSeedVolume
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.HistoryParabolicSeedRicci
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.LGeometry.Action.Estimates.Connector
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Noncollapsing.ReducedVolumeBounds

/-!
# C12X (by S-C12X-URE) port of astra `UniformRegularEndpointBlock`（patched-at-path）

来源：donor `UniformRegularEndpointBlock.lean`（Jui-Hui `chapter11-astra` @ `a73e4bdbfd`）。
donor 文本在本树 elaboration 失败。本文件只有 elaboration 层面修补（no definition / proof idea
altered；不加 `set_option`；声明、证明步骤与 donor 一一对应）：
* `open private … from`：两条都改用 `open private <短名> from <模块>`（`open private` 按后缀匹配；
  短名使调用处保持 donor 的裸名，行宽 ≤ 100）；`ricciTensor_abs_le_dim_mul_sqrt_rmNormSq` 的
  私有声明在 `HistoryParabolicSeedRicciPortC11P`（FIX5 的 port），原路径只是 shim；
* `open scoped` 补 `NNReal`（陈述里的 `ℝ≥0`）；
* `capture_terminal_quarter`：`hSeedA : aSeed ≤ a` 是 `Icc` 子类型的序，用作实数不等式处先
  `have hSeedA' : (aSeed : ℝ) ≤ a := hSeedA`（主定理里同理 `has'`）；`hcapture` 的
  `simpa only [hΦ, localPullMetric_inner] using …` → `have h := …; simp only [..] at h; exact h`；
* 主定理陈述（zeta / 记法等价）：`x ^ 2` / `x ^ 3` 写成 `x ^ (2 : ℕ)` / `x ^ (3 : ℕ)`；4 个
  结论 `let`（`v` / `a` / `Dfull` / `κ₀`）加类型标注；结论里 `y ∈ H.regularMinimizerEndpoints …`
  在本树触发整条声明的 `unknown free variable`（`U = …` 形式不触发）→ 在 `let κ₀ …` 之后加
  `let E : Set (H.stage first).Carrier := H.regularMinimizerEndpoints first last hle t.val
  (3 / a₀) v x`，结论用 `y ∈ E`；证明 `intro` 补 `E`；hdata 里两个未用 binder `hf hl` 改 `_hf _hl`；
* `localPullMetric_subtype_val`：3 处 `simp(a) only [.., localPullMetric_subtype_val, ← h]` 在本树不
  触发 → `rw`；`hyClosed` 的 `hy.le` → `(show … from hy).le`；`hdist` 的 `simpa only
  [riemannianEDistOf_comm]` → `rw … ; exact`；
* `has : aSeed ≤ a`（子类型序）作实数不等式处（`betaV` 的 `Icc_subset_Icc` / `Ioo_subset_Ioo` /
  `hmetricConnector` / `hC1Value` 的时钟区间）→ `has'`；2 条 donor 代码行（101 / 103 字符）仅换行；
* `hcanonical` 被 `obtain ⟨…⟩ := hcanonical` 清除后又被引用 → 先 `have hcanonicalCopy := hcanonical`；
* 2 处 `letI : SigmaCompactSpace _ := …`（目标是命题）→ `let : …`（linter）；`field_simp … <;> ring`
  的 `ring` 无事可做 / 单目标（linter）→ 去掉 `<;>`；
* heartbeat（根因，非拆分）：主定理共用 200000 超限的原因是 7 处 `nlinarith [..]`（`hrealSq`
  `henergy` `htwoLower` `hthreeLower` `hbUpper` `hvLower` 与 `hPastExp`）把整个大局部上下文当假设
  搜索，实测占 ~83% 的 heartbeat（432k 中 ~358k）；全部改 `nlinarith only [..]`（同一组事实）后整条
  主定理 ~99k heartbeat，无需 `set_option`、无需拆分。
-/

set_option autoImplicit false

noncomputable section

open Set Filter Manifold MeasureTheory TopologicalSpace
open DifferentialGeometry DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Riemannian DifferentialGeometry.Tensor0SBundle
open DifferentialGeometry.PDE.RicciFlow DifferentialGeometry.PDE.RicciFlow.Perelman
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
open DifferentialGeometry.Integral.Measure
open scoped Manifold ContDiff ENNReal Topology BigOperators NNReal

open private ricciTensor_abs_le_dim_mul_sqrt_rmNormSq from
  DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.HistoryParabolicSeedRicciPortC11P
open private exists_closed_stage_action_splice_preserving_prefix from
  DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.LGeometry.Action.ClosedTimeACSplice

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory

universe u

private local instance (P : OrientedThreeStage.{u}) : MeasurableSpace P.Carrier :=
  borel P.Carrier

private theorem strong_seed_traced_region
    (H : ObservedHistory.{u}) (t : Icc (0 : ℝ) H.horizon)
    (p : (H.stageAt t).Carrier) (r : ℝ)
    (hseed : GC.LongTime.hasSmallParabolicCurvature H t p r) :
    H.isTracedRegion t p r (r ^ 2) (3 * r ^ 2)⁻¹ := by
  obtain ⟨hr, a, hat, ha, htrace⟩ := hseed
  refine ⟨hr, sq_pos_of_pos hr, a, hat, ha, ?_⟩
  intro x hx
  obtain ⟨trace, hcontrol⟩ := htrace x hx
  have hscaled : 0 < Real.sqrt 3 * r := mul_pos (Real.sqrt_pos.mpr (by norm_num)) hr
  have hnorm := (trace.isRmControlled_iff_isRmBoundedBy hscaled).mp hcontrol
  have hsq : (Real.sqrt 3 * r) ^ 2 = 3 * r ^ 2 := by
    rw [mul_pow, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 3)]
  exact ⟨trace, by simpa only [hsq] using hnorm⟩

private theorem capture_terminal_quarter
    (H : ObservedHistory.{u}) (aSeed t a : Icc (0 : ℝ) H.horizon)
    (hSeedTime : aSeed ≤ t) (hSeedA : aSeed ≤ a) (hat : a ≤ t)
    (p : (H.stageAt t).Carrier) (r : ℝ) (hr : 0 < r)
    (U : Opens (H.stageAt t).Carrier)
    (hU : (U : Set (H.stageAt t).Carrier) =
      riemannianBallOf (H.stageMetric (H.activeStage t) t) p r)
    (S : SolutionOn (I := ThreeModel) (M := U)
      (RealTimeInterval.closed aSeed.val t.val hSeedTime))
    (hS : IsSolutionOn S)
    (hterminal : S.base.metric t = (H.stageMetric (H.activeStage t) t).restrictOpen U)
    (hRm : ∀ s ∈ Icc aSeed.val t.val, ∀ z : U,
      normSq0S (S.base.metric s) z 4 (S.base.rm04 s z) ≤ ((3 * r ^ 2)⁻¹) ^ 2)
    (f : U → (H.stageAt a).Carrier) (hf : IsLocalDiffeomorph ThreeModel ThreeModel ∞ f)
    (hinj : Function.Injective f)
    (hpast : S.base.metric a = localPullMetric (H.stageMetric (H.activeStage a) a) f hf)
    (pU : U) (hpU : pU.val = p) (L core : ℝ) (hL : 0 < L)
    (hExp : Real.exp (2 * (r ^ 2)⁻¹ * (t.val - a.val)) ≤ L ^ 2)
    (hmargin : core < (r / 4) / L) :
    riemannianClosedBallOf (H.stageMetric (H.activeStage a) a) (f pU) core ⊆
      f '' riemannianClosedBallOf (S.base.metric t) pU (r / 4) := by
  classical
  have hSeedA' : (aSeed : ℝ) ≤ a := hSeedA
  let : SigmaCompactSpace U := isSigmaCompact_iff_sigmaCompactSpace.mp
    (Geometry.isSigmaCompact_of_isOpen ThreeModel U.isOpen)
  have hRic (s : ℝ) (hs : s ∈ Icc aSeed.val t.val) (z : U)
      (w : TangentSpace ThreeModel z) :
      |ricciTensor (S.base.metric s) z w w| ≤
        (r ^ 2)⁻¹ * (S.base.metric s).inner z w w := by
    have hnorm : Real.sqrt (normSq0S (S.base.metric s) z 4
        (metricRm04At (S.base.metric s) z)) ≤ (3 * r ^ 2)⁻¹ :=
      (Real.sqrt_le_iff).mpr ⟨by positivity, hRm s hs z⟩
    have hraw := ricciTensor_abs_le_dim_mul_sqrt_rmNormSq (S.base.metric s) z w
    have hdim : Module.finrank ℝ ThreeSpace = 3 := by simp [ThreeSpace]
    rw [hdim, Nat.cast_ofNat] at hraw
    have hcoef : (3 : ℝ) * (3 * r ^ 2)⁻¹ = (r ^ 2)⁻¹ := by
      field_simp [hr.ne']
    exact hraw.trans (by
      rw [← hcoef]
      exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hnorm (by norm_num))
        (metric_inner_self_nonneg _ _ _))
  have hcompare (z : U) (w : TangentSpace ThreeModel z) :
      (S.base.metric t).inner z w w ≤
        L ^ 2 * (localPullMetric (H.stageMetric (H.activeStage a) a) f hf).inner z w w := by
    have hh := metricEquiv_Icc S.base.metric
      (metricPDE_Icc S hS (Icc_subset_Icc hSeedA' le_rfl) (Ioo_subset_Ioo hSeedA' le_rfl))
      (fun s hs z w => hRic s ⟨hSeedA'.trans hs.1, hs.2⟩ z w)
      t ⟨hat, le_rfl⟩ z w
    have hupper := hh.2.trans
      (mul_le_mul_of_nonneg_right hExp (metric_inner_self_nonneg _ _ _))
    rwa [hpast] at hupper
  have hcompact : IsCompact (riemannianClosedBallOf (S.base.metric t) pU (r / 4)) := by
    have hc := Geometry.Metric.isCompact_riemannianClosedBallOf_localPullMetric
      (H.stageMetric (H.activeStage t) t) (Subtype.val : U → (H.stageAt t).Carrier)
      (isLocalDiffeomorph_subtype_val U) Subtype.val_injective pU (r / 4)
      (Geometry.Metric.isClosed_riemannianClosedBallOf _ _ _).isCompact (by
        rw [Subtype.range_coe, hU, hpU]
        intro z hz
        exact hz.trans_lt ((ENNReal.ofReal_lt_ofReal_iff hr).mpr (by linarith)))
    simpa only [localPullMetric_subtype_val, ← hterminal] using hc
  let V := hf.image
  let e : U ≃ₘ⟮ThreeModel, ThreeModel⟯ V :=
    DifferentialGeometry.Topology.Manifold.diffeomorphOntoImage f hf hinj
  let iV := DifferentialGeometry.Manifold.openSubtypePartialDiffeomorph ThreeModel V ⟨e pU⟩
  let Φ : PartialDiffeomorph ThreeModel ThreeModel U (H.stageAt a).Carrier ∞ :=
    e.toPartialDiffeomorph.trans iV
  have hΦ : (Φ : U → (H.stageAt a).Carrier) = f := rfl
  have hsource : Φ.source = univ := by
    ext z
    change (z ∈ (univ : Set U) ∧ e z ∈ (univ : Set V)) ↔ z ∈ (univ : Set U)
    simp only [mem_univ, and_self]
  have hcapture := Perelman.CanonicalNeighborhood.closedBall_subset_image_of_metric_lower
    (S.base.metric t) (H.stageMetric (H.activeStage a) a) Φ pU
    (by positivity : 0 < r / 4) hL hmargin hcompact
    (by rw [hsource]; exact subset_univ _) (fun z _ w => by
      have h := hcompare z w
      simp only [localPullMetric_inner] at h
      exact h)
  simpa only [hΦ] using hcapture

theorem exists_uniform_regular_endpoint_block_of_half_clock_action
    (a₀ c Rbirth : ℝ) (Cderiv : ℝ≥0)
    (ha₀ : 0 < a₀)
    (hRbirth : StandardCap.transitionEnd ≤ Rbirth)
    (request : ℝ → ℝ → ℝ → ℝ → ℝ → ℝ × ℝ × ℕ × ℝ)
    (hWindow :
      ∀ (Aact E rTerm qDeriv ρ : ℝ), 0 ≤ E → 0 < rTerm → 0 < qDeriv → 0 < ρ →
              let req := request Aact E rTerm qDeriv ρ
          ∀ (H : ObservedHistory.{u}) (parameters : CutoffParameters)
            (records : ∀ j : Fin H.eventCount, GeometricCutoffRecord H j parameters),
            (∀ y, InFixedHamiltonIveyRegion (H.initialMetric 0) a₀ y) →
            (∀ y, -3 / a₀ ≤ metricScalarAt (H.initialMetric 0) y) →
          ∀ (t : Icc (0 : ℝ) H.horizon)
            (first : Fin (H.eventCount + 1)) (hle : first ≤ H.activeStage t) (v : ℝ),
            0 ≤ v → v ≤ E → t.val - v ^ (2 : ℕ) ∈ H.stageDomain first →
          ∀ (pole : (H.stageAt t).Carrier), H.isParabolicallyRmControlledBall t pole rTerm →
          ∀ gamma : (j : H.StageInterval first (H.activeStage t)) → ℝ → (H.stage j.val).Carrier,
            (∀ j, ContMDiff 𝓘(ℝ, ℝ) ThreeModel 1 (gamma j)) →
            (∀ j, IntervalIntegrable (H.stageRegularizedLagrangian j.val t.val (gamma j)) volume
              (H.regularizedStageStart t.val 0 j.val) (H.regularizedStageEnd t.val v j.val)) →
            gamma ⟨H.activeStage t, hle, le_rfl⟩ 0 = pole →
            (∀ (j : Fin H.eventCount) (hf : first ≤ j.castSucc) (hl : j.succ ≤ H.activeStage t),
              ∃ z : (H.event j).old,
                z.val.val = gamma ⟨j.castSucc, hf, j.castSucc_le_succ.trans hl⟩
                  (Real.sqrt (t.val - H.time j.succ)) ∧
                (H.event j).oldOutput z = gamma ⟨j.succ, hf.trans j.castSucc_le_succ, hl⟩
                  (Real.sqrt (t.val - H.time j.succ))) →
            (∑ j : H.StageInterval first (H.activeStage t),
              H.stageRegularizedAction j.val t.val (gamma j)
                (H.regularizedStageStart t.val 0 j.val)
                (H.regularizedStageEnd t.val v j.val)) ≤ Aact →
          ∀ (i : Fin H.eventCount) (hf : first ≤ i.succ) (hl : i.succ ≤ H.activeStage t),
            t.val - v ^ (2 : ℕ) ≤ H.time i.succ →
            parameters.recenterConstant ≤ c →
            parameters.delta (H.time i.succ) ≤ req.2.2.2 →
            parameters.neckRadius (H.time i.succ) ≤ ρ →
            (∀ j : Fin H.eventCount, i.succ ≤ j.castSucc → j.succ ≤ H.activeStage t →
              ∀ b, (records j).delta b ≤ req.2.2.2) →
            (∀ j : Fin (H.eventCount + 1), i.succ ≤ j → j ≤ H.activeStage t →
              ∀ y : (H.stage j).Carrier, ∀ s ∈ Ioo (H.time j) (H.stageEndTime j), s ≤ t.val →
                qDeriv < metricScalarAt (H.stageMetric j s) y →
                |derivWithin (fun u => metricScalarAt (H.stageMetric j u) y) (Iic s) s| ≤
                  Cderiv * metricScalarAt (H.stageMetric j s) y ^ (2 : ℕ)) →
            ∀ (b : (H.event i).RetainedBoundaryIndex) (Dbig ζ : ℝ) (m : ℕ)
              (S : (H.event i).PresentedStaticCap parameters.fixed Dbig m ζ b),
              req.2.1 ≤ Dbig → req.2.2.1 ≤ m → ζ ≤ req.1 → S.hasCanonicalWindow →
              S.neck.scale = ((records i).static b).neck.scale →
              gamma ⟨i.succ, hf, hl⟩ (Real.sqrt (t.val - H.time i.succ)) ∉
                S.window '' {z : standardCapWindow Dbig | ‖z.val‖ ≤ Rbirth}
    )
    (H : ObservedHistory.{u}) (parameters : CutoffParameters)
    (records : ∀ i : Fin H.eventCount, GeometricCutoffRecord H i parameters)
    (hpc : parameters.recenterConstant ≤ c)
    (hfixed : ∀ y, InFixedHamiltonIveyRegion (H.initialMetric 0) a₀ y)
    (hscalar : ∀ y, -3 / a₀ ≤ metricScalarAt (H.initialMetric 0) y)
    (t : Icc (0 : ℝ) H.horizon) (p x : (H.stageAt t).Carrier)
    (r A : ℝ) (hA : 1 ≤ A) (hT : 2 * r ^ (2 : ℕ) < t.val)
    (hseed : GC.LongTime.hasSmallParabolicCurvature H t p r)
    (hvolume : ENNReal.ofReal (A⁻¹ * r ^ (3 : ℕ)) ≤
      DifferentialGeometry.Geometry.Collapse.ballVolume
        (H.stageMetric (H.activeStage t) t) p r)
    (aSeed : Icc (0 : ℝ) H.horizon) (hSeedTime : aSeed ≤ t)
    (hSeedClock : (aSeed : ℝ) = t.val - r ^ (2 : ℕ))
    (seedTrace : BackwardPointTrace H (H.activeStage aSeed) (H.activeStage t)
      (H.activeStage_mono hSeedTime) p)
    (aHalf : Icc (0 : ℝ) H.horizon) (hSeedHalf : aSeed ≤ aHalf)
    (hHalfTime : aHalf ≤ t) (hHalfClock : (aHalf : ℝ) = t.val - r ^ (2 : ℕ) / 2)
    (qHalf : (H.stage (H.activeStage aHalf)).Carrier)
    (hNearHalf : riemannianEDistOf (H.stageMetric (H.activeStage aHalf) aHalf)
      (seedTrace.point (H.activeStage aHalf) (H.activeStage_mono hSeedHalf)
        (H.activeStage_mono hHalfTime)) qHalf < ENNReal.ofReal (r / 10))
    (actionHalf : ℝ)
    (hActionHalf : (actionHalf : WithTop ℝ) ∈ H.regularizedActionValues
      (H.activeStage aHalf) (H.activeStage t) (H.activeStage_mono hHalfTime)
      t.val (3 / a₀) 0 (r / Real.sqrt 2) x qHalf)
    (hHalfBudget : actionHalf < GC.GeneralFlow.preparedSpatialPhysicalActionFactor A * r) :
    let v : ℝ := Real.sqrt 3 * r / 2
    let a : Icc (0 : ℝ) H.horizon := projIcc 0 H.horizon H.horizon_nonneg (t.val - v ^ (2 : ℕ))
    ∀ (has : aSeed ≤ a) (hat : a ≤ t),
    let first := H.activeStage a
    let last := H.activeStage t
    let hle := H.activeStage_mono hat
    let O := seedTrace.point first (H.activeStage_mono has) hle
    let Dfull : ℝ := GC.GeneralFlow.preparedSpatialPhysicalActionFactor A + Real.exp (9 / 2) + 4
    let κ₀ : ℝ := A⁻¹ * Real.exp (-57) / (512 * (100 : ℝ) ^ (3 : ℕ))
    let E : Set (H.stage first).Carrier :=
      H.regularMinimizerEndpoints first last hle t.val (3 / a₀) v x
    ∀ (nodeA nodeE nodeR nodeQ nodeRho : Fin H.eventCount → ℝ),
      (∀ (i : Fin H.eventCount) (_hf : first ≤ i.castSucc) (_hl : i.succ ≤ last),
        let req := request (nodeA i) (nodeE i) (nodeR i) (nodeQ i) (nodeRho i)
        0 ≤ nodeE i ∧ 0 < nodeR i ∧ 0 < nodeQ i ∧ 0 < nodeRho i ∧ v ≤ nodeE i ∧
        H.isParabolicallyRmControlledBall t x (nodeR i) ∧
        parameters.delta (H.time i.succ) ≤ req.2.2.2 ∧
        parameters.neckRadius (H.time i.succ) ≤ nodeRho i ∧
        (∀ j : Fin H.eventCount, i.succ ≤ j.castSucc → j.succ ≤ last →
          ∀ b, (records j).delta b ≤ req.2.2.2) ∧
        (∀ j : Fin (H.eventCount + 1), i.succ ≤ j → j ≤ last →
          ∀ y : (H.stage j).Carrier, ∀ s ∈ Ioo (H.time j) (H.stageEndTime j), s ≤ t.val →
            nodeQ i < metricScalarAt (H.stageMetric j s) y →
            |derivWithin (fun u => metricScalarAt (H.stageMetric j u) y) (Iic s) s| ≤
              Cderiv * metricScalarAt (H.stageMetric j s) y ^ (2 : ℕ)) ∧
        (∀ b : (H.event i).RetainedBoundaryIndex,
          ∃ (Dbig ζ : ℝ) (m : ℕ)
            (S : (H.event i).PresentedStaticCap parameters.fixed Dbig m ζ b),
            req.2.1 ≤ Dbig ∧ req.2.2.1 ≤ m ∧ ζ ≤ req.1 ∧ S.hasCanonicalWindow ∧
            S.neck.scale = ((records i).static b).neck.scale)) →
      (∀ (i : Fin H.eventCount), first ≤ i.castSucc → i.succ ≤ last → Dfull * r ≤ nodeA i) →
      ∃ U : Set (H.stage first).Carrier,
        U = riemannianBallOf (H.stageMetric first a) O (r / 100) ∧
        IsOpen U ∧ 0 < κ₀ ∧ 0 < Dfull ∧ 0 < v ∧ v ^ (2 : ℕ) ≤ t.val ∧ r ≤ 2 * v ∧
        ENNReal.ofReal (κ₀ * v ^ (3 : ℕ)) ≤
          riemannianVolumeMeasure ThreeModel (H.stage first).Carrier
            (H.stageMetric first (t.val - v ^ (2 : ℕ))) U ∧
        ∀ y ∈ U,
          y ∈ E ∧
          H.regularizedCost first last hle t.val (3 / a₀) 0 v x y ≤
            ((2 * Dfull * v : ℝ) : WithTop ℝ) := by
  classical
  intro v a has hat first last hle O Dfull κ₀ E nodeA nodeE nodeR nodeQ nodeRho hdata hbudget
  have hr : 0 < r := hseed.1
  have hr2 : 0 < r ^ 2 := sq_pos_of_pos hr
  have htwo : 0 < Real.sqrt (2 : ℝ) := Real.sqrt_pos.mpr (by norm_num)
  have hthree : 0 < Real.sqrt (3 : ℝ) := Real.sqrt_pos.mpr (by norm_num)
  let b : ℝ := r / Real.sqrt 2
  let middle := H.activeStage aHalf
  have hb : 0 < b := div_pos hr htwo
  have hb2 : b ^ 2 = r ^ 2 / 2 := by
    dsimp only [b]
    rw [div_pow, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
  have hv : 0 < v := div_pos (mul_pos hthree hr) (by norm_num)
  have hv2 : v ^ 2 = 3 * r ^ 2 / 4 := by
    dsimp only [v]
    rw [div_pow, mul_pow, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 3)]
    norm_num
  have hvr : v ≤ r := by nlinarith only [hv2, hr2, hr, hv]
  have hbv : b < v := by nlinarith only [hb2, hv2, hb, hv, hr2]
  have hvtime : v ^ 2 ≤ t.val := by nlinarith only [hv2, hT, hr2]
  have hamem : t.val - v ^ 2 ∈ Icc (0 : ℝ) H.horizon :=
    ⟨sub_nonneg.mpr hvtime, (sub_le_self _ (sq_nonneg v)).trans t.property.2⟩
  have ha : a.val = t.val - v ^ 2 := by
    dsimp only [a]
    rw [Set.projIcc_of_mem _ hamem]
  have haHalf : a ≤ aHalf := by
    change a.val ≤ aHalf.val
    rw [ha, hHalfClock]
    nlinarith only [hv2, hr2]
  have hfm : first ≤ middle := H.activeStage_mono haHalf
  have hml : middle ≤ last := H.activeStage_mono hHalfTime
  have hupper : t.val - (0 : ℝ) ^ 2 ∈ H.stageDomain last := by
    simpa only [zero_pow (by decide : 2 ≠ 0), sub_zero] using H.activeStage_mem t
  have hupperIcc : t.val - (0 : ℝ) ^ 2 ∈ Icc (H.time last) (H.stageEndTime last) :=
    ⟨H.time_le_of_mem_stageDomain hupper, H.le_stageEndTime_of_mem_stageDomain hupper⟩
  have hmiddle : t.val - b ^ 2 ∈ H.stageDomain middle := by
    rw [hb2, ← hHalfClock]
    exact H.activeStage_mem aHalf
  have hmiddleIcc : t.val - b ^ 2 ∈ Icc (H.time middle) (H.stageEndTime middle) :=
    ⟨H.time_le_of_mem_stageDomain hmiddle, H.le_stageEndTime_of_mem_stageDomain hmiddle⟩
  have hlower : t.val - v ^ 2 ∈ H.stageDomain first := by
    rw [← ha]
    exact H.activeStage_mem a
  have hpreserve := H.fixedHamiltonIveyRegion_and_scalar_lower records ha₀ hfixed hscalar
  have hfloor : ∀ j (s : ℝ), s ∈ H.stageDomain j →
      ∀ z : (H.stage j).Carrier, -(3 / a₀) ≤ metricScalarAt (H.stageMetric j s) z := by
    intro j s hs z
    have htime := (H.stageDomain_subset j hs).1
    have hratio : 3 / (a₀ + s) ≤ 3 / a₀ :=
      div_le_div_of_nonneg_left (by norm_num : (0 : ℝ) ≤ 3) ha₀
        (le_add_of_nonneg_right htime)
    have hneg : -(3 / a₀) ≤ -3 / (a₀ + s) := by
      simpa only [neg_div] using neg_le_neg hratio
    exact hneg.trans (hpreserve.1 j s hs z).2
  have hscalarClock (j : H.StageInterval first last) (w : ℝ)
      (hw : w ∈ Ioo (H.regularizedStageStart t.val 0 j.val)
        (H.regularizedStageEnd t.val v j.val)) (z : (H.stage j.val).Carrier) :
      -(3 / a₀) ≤ metricScalarAt (H.stageMetric j.val (t.val - w ^ 2)) z :=
    hfloor j.val _ (H.mapsTo_regularizedStage_Ioo t.val 0 v j.val hw) z
  obtain ⟨_, _, _, _, alpha, hAlpha, hAlpha0, hAlphab, hAlphaNodes, hAlphaAction⟩ := hActionHalf
  obtain ⟨a0, ha0t, ha0, V, hV, f, hf, hinj, hcross, hlast, S, hS, hmetric, hRm⟩ :=
    H.exists_common_flow_of_isTracedRegion t p (strong_seed_traced_region H t p r hseed)
  have ha0eq : a0 = aSeed := Subtype.ext (ha0.trans hSeedClock.symm)
  subst a0
  let : SigmaCompactSpace V := isSigmaCompact_iff_sigmaCompactSpace.mp
    (Geometry.isSigmaCompact_of_isOpen ThreeModel V.isOpen)
  have hpV : p ∈ V := by
    change p ∈ (V : Set (H.stageAt t).Carrier)
    rw [hV]
    change riemannianEDistOf _ p p < ENNReal.ofReal r
    rw [riemannianEDistOf_self]
    exact ENNReal.ofReal_pos.mpr hr
  let pV : V := ⟨p, hpV⟩
  let sourceTrace : BackwardPointTrace H (H.activeStage aSeed) last
      (H.activeStage_mono hSeedTime) p :=
    { point := fun j hj hl => f ⟨j, hj, hl⟩ pV
      endpoint_eq := hlast pV
      crossing := fun i hi hl => hcross i hi hl pV }
  have hTraceEq : sourceTrace = seedTrace := Subsingleton.elim _ _
  have hcenter (s : Icc (0 : ℝ) H.horizon) (hss : aSeed ≤ s) (hst : s ≤ t) :
      f ⟨H.activeStage s, H.activeStage_mono hss, H.activeStage_mono hst⟩ pV =
        seedTrace.point (H.activeStage s) (H.activeStage_mono hss) (H.activeStage_mono hst) :=
    congrArg (fun A => A.point (H.activeStage s)
      (H.activeStage_mono hss) (H.activeStage_mono hst)) hTraceEq
  have hterminal : S.base.metric t = (H.stageMetric last t).restrictOpen V := by
    have hh := hmetric ⟨last, H.activeStage_mono hSeedTime, le_rfl⟩ t
      ⟨hSeedTime, le_rfl⟩ (H.activeStage_mem t)
    have he : f ⟨last, H.activeStage_mono hSeedTime, le_rfl⟩ = Subtype.val := funext hlast
    simp only [he] at hh
    rw [hh]
    exact localPullMetric_subtype_val _ _
  have hHalfMetric : S.base.metric aHalf = localPullMetric (H.stageMetric middle aHalf)
      (f ⟨middle, H.activeStage_mono hSeedHalf, hml⟩)
      (hf ⟨middle, H.activeStage_mono hSeedHalf, hml⟩) :=
    hmetric _ aHalf ⟨hSeedHalf, hHalfTime⟩ (H.activeStage_mem aHalf)
  have hHalfExp : Real.exp (2 * (r ^ 2)⁻¹ * (t.val - aHalf.val)) ≤ (2 : ℝ) ^ 2 := by
    have he : 2 * (r ^ 2)⁻¹ * (t.val - aHalf.val) = 1 := by
      rw [hHalfClock]
      field_simp [hr.ne']
      ring
    rw [he]
    have hh := Real.exp_one_lt_three
    norm_num at ⊢
    linarith
  have hcaptureHalf := capture_terminal_quarter H aSeed t aHalf hSeedTime hSeedHalf hHalfTime
    p r hr V hV S hS hterminal hRm
    (f ⟨middle, H.activeStage_mono hSeedHalf, hml⟩)
    (hf ⟨middle, H.activeStage_mono hSeedHalf, hml⟩)
    (hinj ⟨middle, H.activeStage_mono hSeedHalf, hml⟩)
    hHalfMetric pV rfl 2 (r / 10) (by norm_num) hHalfExp (by linarith)
  have hqClosed : qHalf ∈ riemannianClosedBallOf (H.stageMetric middle aHalf)
      (f ⟨middle, H.activeStage_mono hSeedHalf, hml⟩ pV) (r / 10) := by
    rw [hcenter aHalf hSeedHalf hHalfTime]
    exact hNearHalf.le
  obtain ⟨qV, hqV, hqImage⟩ := hcaptureHalf hqClosed
  have hPastMetric : S.base.metric a = localPullMetric (H.stageMetric first a)
      (f ⟨first, H.activeStage_mono has, hle⟩) (hf ⟨first, H.activeStage_mono has, hle⟩) :=
    hmetric _ a ⟨has, hat⟩ (H.activeStage_mem a)
  have hPastExp : Real.exp (2 * (r ^ 2)⁻¹ * (t.val - a.val)) ≤ (3 : ℝ) ^ 2 := by
    have he : 2 * (r ^ 2)⁻¹ * (t.val - a.val) = 3 / 2 := by
      rw [ha, hv2]
      field_simp [hr.ne']
      ring
    rw [he]
    have he2 : Real.exp 2 = (Real.exp 1) ^ 2 := by
      rw [pow_two, ← Real.exp_add]
      norm_num
    have hh : Real.exp (3 / 2) ≤ Real.exp 2 := Real.exp_le_exp.mpr (by norm_num)
    rw [he2] at hh
    nlinarith only [hh, Real.exp_one_lt_three, Real.exp_pos 1]
  have hcapturePast := capture_terminal_quarter H aSeed t a hSeedTime has hat
    p r hr V hV S hS hterminal hRm
    (f ⟨first, H.activeStage_mono has, hle⟩)
    (hf ⟨first, H.activeStage_mono has, hle⟩)
    (hinj ⟨first, H.activeStage_mono has, hle⟩)
    hPastMetric pV rfl 3 (r / 100) (by norm_num) hPastExp (by linarith)
  have hqAmbient : riemannianEDistOf (H.stageMetric last t) p qV.val ≤ ENNReal.ofReal (r / 4) := by
    have hh := Geometry.Metric.edistOf_le_of_quad_of_localDiffeomorph
      (localPullMetric (H.stageMetric last t) (Subtype.val : V → (H.stageAt t).Carrier)
        (isLocalDiffeomorph_subtype_val V))
      (H.stageMetric last t) (Subtype.val : V → (H.stageAt t).Carrier)
      (isLocalDiffeomorph_subtype_val V) (c := 1) zero_lt_one
      (fun z w => by rw [localPullMetric_inner, one_mul]) pV qV
    simp only [Real.sqrt_one, ENNReal.ofReal_one, one_mul] at hh
    rw [localPullMetric_subtype_val, ← hterminal] at hh
    exact hh.trans hqV
  have hcompactConnector : IsCompact (riemannianClosedBallOf (S.base.metric t) qV (5 * r / 8)) := by
    have hc := Geometry.Metric.isCompact_riemannianClosedBallOf_localPullMetric
      (H.stageMetric last t) (Subtype.val : V → (H.stageAt t).Carrier)
      (isLocalDiffeomorph_subtype_val V) Subtype.val_injective qV (5 * r / 8)
      (Geometry.Metric.isClosed_riemannianClosedBallOf _ _ _).isCompact (by
        rw [Subtype.range_coe, hV]
        intro z hz
        have hh := (riemannianEDistOf_triangle (H.stageMetric last t) p qV.val z).trans
          (add_le_add hqAmbient hz)
        rw [← ENNReal.ofReal_add (by positivity) (by positivity)] at hh
        exact hh.trans_lt ((ENNReal.ofReal_lt_ofReal_iff hr).mpr (by linarith)))
    rw [localPullMetric_subtype_val, ← hterminal] at hc
    exact hc
  have hApos : 0 < A := lt_of_lt_of_le zero_lt_one hA
  have hκ : 0 < κ₀ := by dsimp only [κ₀]; positivity
  have hD : 0 < Dfull := by
    dsimp only [Dfull, GC.GeneralFlow.preparedSpatialPhysicalActionFactor]
    positivity
  have hrTwoV : r ≤ 2 * v := by nlinarith only [hv2, hr2, hr, hv]
  let U : Set (H.stage first).Carrier :=
    riemannianBallOf (H.stageMetric first a) O (r / 100)
  have hUopen : IsOpen U :=
    isOpen_lt (continuous_riemannianEDist (H.stageMetric first a) O) continuous_const
  have hvolumeU : ENNReal.ofReal (κ₀ * v ^ 3) ≤
      riemannianVolumeMeasure ThreeModel (H.stage first).Carrier
        (H.stageMetric first (t.val - v ^ 2)) U := by
    have hpInner : p ∈ riemannianBallOf (H.stageMetric last t) p (r / 4) := by
      change riemannianEDistOf _ p p < ENNReal.ofReal (r / 4)
      rw [riemannianEDistOf_self]
      exact ENNReal.ofReal_pos.mpr (by positivity)
    have hfloorTime : t.val - r ^ 2 ≤ a.val := by
      rw [← hSeedClock]
      exact has
    have hh := (hseed.volume_lower_along_nearby_trace hvolume hpInner a hat hfloorTime).2
      (seedTrace.restrictFirst (H.activeStage_mono has) hle)
      (r / 100) (by positivity) (by linarith)
    change ENNReal.ofReal ((A⁻¹ * Real.exp (-57) / 512) * (r / 100) ^ 3) ≤
      Geometry.Collapse.ballVolume (H.stageMetric first a) O (r / 100) at hh
    rw [← ha]
    change ENNReal.ofReal (κ₀ * v ^ 3) ≤
      Geometry.Collapse.ballVolume (H.stageMetric first a) O (r / 100)
    apply (ENNReal.ofReal_le_ofReal ?_).trans hh
    calc
      κ₀ * v ^ 3 ≤ κ₀ * r ^ 3 :=
        mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hv.le hvr 3) hκ.le
      _ = _ := by dsimp only [κ₀]; ring
  refine ⟨U, rfl, hUopen, hκ, hD, hv, hvtime, hrTwoV, hvolumeU, ?_⟩
  intro y hy
  have hyClosed : y ∈ riemannianClosedBallOf (H.stageMetric first a)
      (f ⟨first, H.activeStage_mono has, hle⟩ pV) (r / 100) := by
    rw [hcenter a has hat]
    exact (show riemannianEDistOf (H.stageMetric first a) O y < ENNReal.ofReal (r / 100)
      from hy).le
  obtain ⟨yV, hyV, hyImage⟩ := hcapturePast hyClosed
  have hdist : riemannianEDistOf (S.base.metric t) qV yV ≤ ENNReal.ofReal (r / 2) := by
    calc
      _ ≤ riemannianEDistOf (S.base.metric t) qV pV +
          riemannianEDistOf (S.base.metric t) pV yV := riemannianEDistOf_triangle _ _ _ _
      _ ≤ ENNReal.ofReal (r / 4) + ENNReal.ofReal (r / 4) :=
        add_le_add (by rw [riemannianEDistOf_comm]; exact hqV) hyV
      _ = _ := by
        rw [← ENNReal.ofReal_add (by positivity) (by positivity)]
        congr 1
        ring
  have hdistlt : riemannianEDistOf (S.base.metric t) qV yV < ENNReal.ofReal (5 * r / 8) :=
    hdist.trans_lt ((ENNReal.ofReal_lt_ofReal_iff (by positivity)).mpr (by linarith))
  have hclockConnector (w : ℝ) (hw : w ∈ Icc b v) : t.val - w ^ 2 ∈ Icc a.val t.val := by
    rw [ha]
    have hw0 : 0 ≤ w := hb.le.trans hw.1
    have hwsq : w ^ 2 ≤ v ^ 2 := pow_le_pow_left₀ hw0 hw.2 2
    exact ⟨sub_le_sub_left hwsq _, sub_le_self _ (sq_nonneg w)⟩
  have has' : (aSeed : ℝ) ≤ a := has
  obtain ⟨betaV, hBetaSmooth, hBetaStart, hBetaEnd, hBetaStay, hBetaBound⟩ :=
    exists_lRegularizedAction_le_of_curvature_bound S hS
      (u := a.val) (s := t.val) (K := (3 * r ^ 2)⁻¹) (by positivity) hat
      (Icc_subset_Icc has' le_rfl) (Ioo_subset_Ioo has' le_rfl)
      (fun s hs z => hRm s ⟨has'.trans hs.1, hs.2⟩ z)
      qV yV hbv hdistlt hcompactConnector hclockConnector
  have hdim : Module.finrank ℝ ThreeSpace = 3 := by simp [ThreeSpace]
  rw [hdim, Nat.cast_ofNat] at hBetaBound
  have hExpConnector : 2 * (3 : ℝ) ^ 2 * (3 * r ^ 2)⁻¹ * (t.val - a.val) = 9 / 2 := by
    rw [ha, hv2]
    field_simp [hr.ne']
    ring
  have hScalarConnector : 2 * ((3 : ℝ) ^ 2 * (3 * r ^ 2)⁻¹) / 3 = 2 / r ^ 2 := by
    field_simp [hr.ne']
  rw [hExpConnector, hScalarConnector] at hBetaBound
  have htwoLower : (7 : ℝ) / 5 < Real.sqrt 2 := by
    nlinarith only [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2), Real.sqrt_nonneg (2 : ℝ)]
  have hthreeLower : (12 : ℝ) / 7 < Real.sqrt 3 := by
    nlinarith only [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 3), Real.sqrt_nonneg (3 : ℝ)]
  have hbUpper : b < 5 * r / 7 := by
    apply (div_lt_iff₀ htwo).mpr
    nlinarith only [mul_lt_mul_of_pos_right htwoLower hr]
  have hvLower : 6 * r / 7 < v := by
    dsimp only [v]
    nlinarith only [mul_lt_mul_of_pos_right hthreeLower hr]
  have hgap : r / 8 < v - b := by linarith
  have hreal : (riemannianEDistOf (S.base.metric t) qV yV).toReal ≤ r / 2 :=
    ENNReal.toReal_le_of_le_ofReal (by positivity) hdist
  have hrealSq : (riemannianEDistOf (S.base.metric t) qV yV).toReal ^ 2 ≤ r ^ 2 / 4 := by
    nlinarith only [hreal, hr,
      ENNReal.toReal_nonneg (a := riemannianEDistOf (S.base.metric t) qV yV)]
  have henergy : (riemannianEDistOf (S.base.metric t) qV yV).toReal ^ 2 /
      (2 * (v - b)) ≤ r := by
    apply (div_le_iff₀ (by positivity : 0 < 2 * (v - b))).mpr
    nlinarith only [hrealSq, mul_lt_mul_of_pos_right hgap hr]
  have hcubic : v ^ 3 - b ^ 3 ≤ r ^ 3 :=
    (sub_le_self _ (pow_nonneg hb.le 3)).trans (pow_le_pow_left₀ hv.le hvr 3)
  have hscalarAction : (2 / r ^ 2) * (v ^ 3 - b ^ 3) ≤ 2 * r := by
    calc
      _ ≤ (2 / r ^ 2) * r ^ 3 := mul_le_mul_of_nonneg_left hcubic (by positivity)
      _ = _ := by field_simp [hr.ne']
  have hConnector : lRegularizedAction S t.val betaV b v ≤ (Real.exp (9 / 2) + 2) * r := by
    apply hBetaBound.trans
    have hh := mul_le_mul_of_nonneg_left henergy (Real.exp_pos (9 / 2)).le
    rw [← mul_div_assoc] at hh
    nlinarith only [hh, hscalarAction]
  let fConnector (j : H.StageInterval first middle) : V → (H.stage j.val).Carrier :=
    f ⟨j.val, (H.activeStage_mono has).trans j.property.1, j.property.2.trans hml⟩
  have hfConnector (j : H.StageInterval first middle) :
      IsLocalDiffeomorph ThreeModel ThreeModel ∞ (fConnector j) :=
    hf ⟨j.val, (H.activeStage_mono has).trans j.property.1, j.property.2.trans hml⟩
  have hcrossConnector (i : Fin H.eventCount) (hi : first ≤ i.castSucc) (hl : i.succ ≤ middle)
      (z : V) :
      (H.event i).RegularCrossing
        (fConnector ⟨i.castSucc, hi, i.castSucc_lt_succ.le.trans hl⟩ z)
        (fConnector ⟨i.succ, hi.trans i.castSucc_lt_succ.le, hl⟩ z) :=
    hcross i ((H.activeStage_mono has).trans hi) (hl.trans hml) z
  have hmetricConnector (j : H.StageInterval first middle) (w : ℝ)
      (hw : w ∈ Ioo (H.regularizedStageStart t.val b j.val)
        (H.regularizedStageEnd t.val v j.val)) :
      S.base.metric (t.val - w ^ 2) =
        localPullMetric (H.stageMetric j.val (t.val - w ^ 2)) (fConnector j) (hfConnector j) := by
    have hbounds := H.regularizedStage_bounds hb.le hbv.le hmiddleIcc hlower j
    have hwb : b ≤ w := hbounds.1.trans hw.1.le
    have hwv : w ≤ v := hw.2.le.trans hbounds.2.2
    have hclock := hclockConnector w ⟨hwb, hwv⟩
    exact hmetric _ _ ⟨has'.trans hclock.1, hclock.2⟩
      (H.mapsTo_regularizedStage_Ioo t.val b v j.val hw)
  have hC1Value := H.action_mem_regularizedC1ActionValues_of_common_curve first middle hfm
    fConnector hfConnector hcrossConnector S hS t.val hb.le hbv.le hmiddleIcc hlower
    (fun w hw => ⟨has'.trans (hclockConnector w hw).1, (hclockConnector w hw).2⟩)
    hmetricConnector betaV (hBetaSmooth.of_le (by norm_num))
  have hBetaImageStart : fConnector ⟨middle, hfm, le_rfl⟩ (betaV b) = qHalf := by
    rw [hBetaStart]
    exact hqImage
  have hBetaImageEnd : fConnector ⟨first, le_rfl, hfm⟩ (betaV v) = y := by
    rw [hBetaEnd]
    exact hyImage
  rw [hBetaImageStart, hBetaImageEnd] at hC1Value
  have hACValue := H.coe_mem_regularizedActionValues_of_mem_regularizedC1ActionValues
    first middle hfm (B := 3 / a₀)
    (fun j w hw z => hfloor j.val _ (H.mapsTo_regularizedStage_Ioo t.val b v j.val hw) z)
    qHalf y hC1Value
  obtain ⟨_, _, _, _, beta, hBeta, hBetab, hBetav, hBetaNodes, hBetaAction⟩ := hACValue
  obtain ⟨gamma, hGamma, hGamma0, hGammav, hGammaNodes, hGammaAction,
      hPrefixEq, hConnectorEq⟩ :=
    exists_closed_stage_action_splice_preserving_prefix H first middle last hfm hml
      t.val (3 / a₀) 0 b v actionHalf (lRegularizedAction S t.val betaV b v)
      (le_refl 0) hb.le hbv.le hupperIcc hmiddle hlower hscalarClock
      alpha beta hAlpha hBeta (hAlphab.trans hBetab.symm)
      hAlphaNodes hBetaNodes hAlphaAction hBetaAction
  have hFullValue : ((actionHalf + lRegularizedAction S t.val betaV b v : ℝ) : WithTop ℝ) ∈
      H.regularizedActionValues first last hle t.val (3 / a₀) 0 v x y :=
    ⟨le_refl 0, hv.le, hupperIcc, hlower, gamma, hGamma,
      hGamma0.trans hAlpha0, hGammav.trans hBetav, hGammaNodes, hGammaAction⟩
  have hCostLe := H.regularizedCost_le_of_competitor first last hle t.val (3 / a₀) 0 v x y
    hFullValue
  have hFullBudget : actionHalf + lRegularizedAction S t.val betaV b v < Dfull * r := by
    dsimp only [Dfull]
    nlinarith only [hHalfBudget, hConnector, hr]
  have hCostLt : H.regularizedCost first last hle t.val (3 / a₀) 0 v x y <
      ((Dfull * r : ℝ) : WithTop ℝ) :=
    hCostLe.trans_lt (WithTop.coe_lt_coe.mpr hFullBudget)
  have hfinite : H.regularizedCost first last hle t.val (3 / a₀) 0 v x y ≠ ⊤ :=
    ne_of_lt (hCostLt.trans (WithTop.coe_lt_top _))
  have hcost := H.regularizedCost_eq_regularizedC1Cost first last hle
    t.val (3 / a₀) 0 v hupper hscalarClock x y
  have hfiniteC1 : H.regularizedC1Cost first last hle t.val 0 v x y ≠ ⊤ := by
    rw [← hcost]
    exact hfinite
  obtain ⟨minimizer, hC1, hInt, hx, hyEnd, hNodes, hSumC1⟩ :=
    H.exists_regularizedC1Cost_minimizer_of_ne_top first last hle
      t.val (3 / a₀) 0 v hupper hscalarClock x y hfiniteC1
  have hAC (j : H.StageInterval first last) :
      Manifold.absolutelyContinuousOnInterval ThreeModel (minimizer j)
        (H.regularizedStageStart t.val 0 j.val) (H.regularizedStageEnd t.val v j.val) :=
    Manifold.absolutelyContinuousOnInterval_of_contMDiffOn (hC1 j).contMDiffOn
  have hSumCost : (((∑ j : H.StageInterval first last,
      H.stageRegularizedAction j.val t.val (minimizer j)
        (H.regularizedStageStart t.val 0 j.val)
        (H.regularizedStageEnd t.val v j.val)) : ℝ) : WithTop ℝ) =
      H.regularizedCost first last hle t.val (3 / a₀) 0 v x y :=
    hSumC1.trans hcost.symm
  have hmin : H.regularizedExtendedAction first last t.val (3 / a₀) 0 v minimizer =
      H.regularizedCost first last hle t.val (3 / a₀) 0 v x y := by
    have hext := H.regularizedExtendedAction_eq_sum_action first last
      (le_refl 0) hv.le hupperIcc hlower minimizer hInt (fun j => by
        filter_upwards [ae_restrict_mem measurableSet_Ioo] with w hw
        exact hscalarClock j w hw (minimizer j w))
    exact hext.trans hSumCost
  have hcrossAll (i : Fin H.eventCount) (hfi : first ≤ i.castSucc) (hil : i.succ ≤ last) :
      (H.event i).RegularCrossing
        (minimizer ⟨i.castSucc, hfi, i.castSucc_le_succ.trans hil⟩
          (Real.sqrt (t.val - H.time i.succ)))
        (minimizer ⟨i.succ, hfi.trans i.castSucc_le_succ, hil⟩
          (Real.sqrt (t.val - H.time i.succ))) := by
    obtain ⟨hE, hrTerm, hqDeriv, hρ, hvE, hball, hδnode, hρnode, hlater, hderiv, hraw⟩ :=
      hdata i hfi hil
    have hsmallAction : (∑ j : H.StageInterval first last,
        H.stageRegularizedAction j.val t.val (minimizer j)
          (H.regularizedStageStart t.val 0 j.val)
          (H.regularizedStageEnd t.val v j.val)) < nodeA i := by
      have hh := hCostLt.trans_le (WithTop.coe_le_coe.mpr (hbudget i hfi hil))
      rw [← hSumCost] at hh
      exact WithTop.coe_lt_coe.mp hh
    by_contra hbad
    obtain ⟨bcap, z, hcap⟩ :=
      ((H.event i).regularCrossing_or_cap_of_admissible_node
        (records i).old_eq_retained (hNodes i hfi hil)).resolve_left hbad
    obtain ⟨Dbig, ζ, m, Scap, hRadius, hm, hζ, hcanonical, hscaleEq⟩ := hraw bcap
    have hpoint : minimizer ⟨i.succ, hfi.trans i.castSucc_le_succ, hil⟩
        (Real.sqrt (t.val - H.time i.succ)) = Scap.inclusion (Scap.witness.cap z) :=
      Sum.inl_injective (hcap.symm.trans (Scap.cap_eq z))
    have hstart : t.val - v ^ 2 < H.time i.succ := by
      by_contra hn
      have hi : i.succ ≤ first := H.le_activeStage a i.succ (by
        rw [ha]
        exact not_lt.mp hn)
      exact (not_le_of_gt (hfi.trans_lt i.castSucc_lt_succ)) hi
    have hcanonicalCopy := hcanonical
    obtain ⟨_, _, _, _, _, _, _, hcapWindow⟩ := hcanonicalCopy
    obtain ⟨xPast, hxPast, hwindowPoint⟩ := hcapWindow z
    exact hWindow (nodeA i) (nodeE i) (nodeR i) (nodeQ i) (nodeRho i)
      hE hrTerm hqDeriv hρ H parameters records hfixed hscalar t first hle v hv.le hvE hlower
      x hball minimizer hC1 hInt hx hNodes hsmallAction.le i
      (hfi.trans i.castSucc_le_succ) hil hstart.le hpc hδnode hρnode hlater hderiv
      bcap Dbig ζ m Scap hRadius hm hζ hcanonical hscaleEq
      ⟨xPast, hxPast.trans hRbirth, hwindowPoint.trans hpoint.symm⟩
  refine ⟨⟨minimizer, hAC, hx, hyEnd, hcrossAll, hmin⟩, ?_⟩
  exact hCostLt.le.trans (WithTop.coe_le_coe.mpr (by
    nlinarith only [mul_le_mul_of_nonneg_left hrTwoV hD.le]))

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory

end
