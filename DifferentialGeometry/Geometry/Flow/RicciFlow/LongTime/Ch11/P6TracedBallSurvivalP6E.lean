import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.TracedRegion
import DifferentialGeometry.Geometry.Flow.RicciFlow.Estimates.CurvatureMetricComparison
import DifferentialGeometry.Geometry.Comparison.OpenEmbeddingBallCapture
import DifferentialGeometry.Geometry.Curvature.Naturality.Pullback.LocalNorm
import DifferentialGeometry.Geometry.Metric.Distance.LocalBall

/-!
# (α) 球包含路线，跨 event 部分 G1：traced ball 的前向存活（O-CH11-P6CE，后缀 `_P6E`）

P6ANCH2 设计段 B2 的 G2c（hscal 第二分量）的几何核：trace 点 `tr.point j` 在 stage `j`、时刻 `t'` 的
`ℓ`-球内的点**前向存活**到 `s`（= 落在 backward survivor map 的像内）且像落进 `B_s(y, ρ)`。

**不需要 cap / `hnotK` / hprot**：traced region `(ρ, θ, K)` 于 `(s, y)` 已给 `U = B_s(y, ρ)` 的每个点
一条从 `activeStage (s − θ)` 起、跨过所有 event 的 backward trace（`RegularCrossing`），沿 trace
`|Rm| ≤ K`。被某个 event `e'` 切掉的点不在 `f_j(U)` 内（`f_j(U)` 的点都有 crossing），所以要证的只是
度量包含 `B_{t'}(f_j x, ℓ) ⊆ f_j(U)`：
* 树内 `exists_common_flow_of_isTracedRegion`（`Surgery/Topology/TracedRegion:318`）：`U` 上跨 event
  粘好的 smooth Ricci flow `S`（`[s − θ, s]`），`S(τ) = f_j^* g_j(τ)`、`f_j` 单射 local diffeo、
  `f_last = val`、`|Rm_S|² ≤ K²`；
* 逐点 Grönwall `metric_inner_exp_bounds_of_curvature_bound`：`S(s) ≤ e^{18Kθ} S(t')`；
* ball capture `Geometry.Metric.ball_subset_image_of_metric_lower_on_opens`：
  `B_{t'}(f_j x, ℓ) ⊆ f_j(closedBall_s(x, e^{9Kθ} ℓ))`（`r + e^{9Kθ} ℓ ≤ ρ` ⇒ 闭球 `⊆ U`，紧）；
* `|Rm_{g_j(t')}|(f_j x') = |Rm_{S(t')}|(x') ≤ K`（`normSq0S_metricRm04At_localPullMetric`）。

主定理：
* **`survives_of_traced_ball_P6E`**：上述包含的 trace 形（`∃ x' ∈ B_s(y, ρ)`、`d_s(x, x') ≤ e^{9Kθ} ℓ`、
  `x'` 在 `[j, activeStage s]` 的 trace 过 `z`，且 `|Rm_{g_j(t')}(z)|² ≤ K²`）。
  `j = activeStage s` 时即同 slab（`f = val`），故同时覆盖 hscal 第一分量。
* `survives_backwardSurvivorDomain_of_traced_ball_P6E`：`backwardSurvivorDomain` /
  `backwardSurvivorMap` 形（`z` = survivor map 在 `B_s(y, ρ)` 内某点的值）。
-/

set_option autoImplicit false

noncomputable section

open Set Manifold
open DifferentialGeometry.Geometry.Curvature DifferentialGeometry.Tensor0SBundle
open scoped Manifold ContDiff Topology ENNReal

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

universe u

namespace ObservedHistory

/-- `t' ∈ stageDomain j`、`a ≤ t'` ⇒ `activeStage a ≤ j`（`_P6E`）。 -/
theorem activeStage_le_of_mem_stageDomain_P6E (H : ObservedHistory.{u})
    (a : Icc (0 : ℝ) H.horizon) {j : Fin (H.eventCount + 1)} {t' : ℝ}
    (hdom : t' ∈ H.stageDomain j) (hat : (a : ℝ) ≤ t') : H.activeStage a ≤ j := by
  by_contra hlt
  rw [not_le] at hlt
  induction j using Fin.lastCases with
  | last => exact (not_lt.mpr (Fin.le_last _)) hlt
  | cast i =>
    simp only [ObservedHistory.stageDomain, Fin.lastCases_castSucc, Set.mem_Ico] at hdom
    have hsucc : i.succ ≤ H.activeStage a := by
      rw [Fin.lt_def, Fin.val_castSucc] at hlt
      rw [Fin.le_def, Fin.val_succ]
      omega
    have h1 := H.time_strictMono.monotone hsucc
    have h2 := H.activeStage_time_le a
    linarith [hdom.2]

/-- **traced ball 的前向存活（`_P6E`，G1 主定理）**：traced region `(ρ, θ, K)` 于 `(s, y)`、
`x ∈ B_s(y, r)`、`r + e^{9Kθ} ℓ ≤ ρ`；`tr` 为 `x` 在 `[j, activeStage s]` 的 backward trace，
`t' ∈ [s − θ, s] ∩ stageDomain j`。则 `g_j(t')`-球 `B(tr.point j, ℓ)` 内每点 `z` 前向存活到 `s`：
`∃ x' ∈ B_s(y, ρ)`，`d_s(x, x') ≤ e^{9Kθ} ℓ`，`x'` 的 trace 在 stage `j` 过 `z`，且
`|Rm_{g_j(t')}(z)|² ≤ K²`。 -/
theorem survives_of_traced_ball_P6E (H : ObservedHistory.{u})
    (s : Icc (0 : ℝ) H.horizon) (y : (H.stageAt s).Carrier) {ρ θ K r ℓ : ℝ}
    (htr : H.isTracedRegion s y ρ θ K) (hK : 0 ≤ K) (hℓ : 0 < ℓ)
    (hrad : r + Real.exp (9 * K * θ) * ℓ ≤ ρ)
    (x : (H.stageAt s).Carrier)
    (hx : x ∈ riemannianBallOf (H.stageMetric (H.activeStage s) s) y r)
    (j : Fin (H.eventCount + 1)) (hjs : j ≤ H.activeStage s)
    (tr : BackwardPointTrace H j (H.activeStage s) hjs x)
    (t' : ℝ) (ht'a : (s : ℝ) - θ ≤ t') (ht's : t' ≤ s) (hdom : t' ∈ H.stageDomain j)
    (z : (H.stage j).Carrier)
    (hz : riemannianEDistOf (H.stageMetric j t') (tr.point j le_rfl hjs) z <
      ENNReal.ofReal ℓ) :
    ∃ x' ∈ riemannianBallOf (H.stageMetric (H.activeStage s) s) y ρ,
      riemannianEDistOf (H.stageMetric (H.activeStage s) s) x x' ≤
        ENNReal.ofReal (Real.exp (9 * K * θ) * ℓ) ∧
      ∃ A : BackwardPointTrace H j (H.activeStage s) hjs x', A.point j le_rfl hjs = z ∧
        normSq0S (H.stageMetric j t') z 4 (metricRm04At (H.stageMetric j t') z) ≤ K ^ 2 := by
  classical
  obtain ⟨a, hat, ha, U, hU, f, hf, hinj, hcross, hlast, S, hS, hmetric, hRm⟩ :=
    H.exists_common_flow_of_isTracedRegion s y htr
  have hat' : (a : ℝ) ≤ t' := by rw [ha]; exact ht'a
  have haj : H.activeStage a ≤ j := H.activeStage_le_of_mem_stageDomain_P6E a hdom hat'
  set L : ℝ := Real.exp (9 * K * θ) with hLdef
  have hL : 0 < L := Real.exp_pos _
  have hLℓ : 0 < L * ℓ := mul_pos hL hℓ
  have hx' : riemannianEDistOf (H.stageMetric (H.activeStage s) s) y x < ENNReal.ofReal r := hx
  have hr : 0 < r := ENNReal.ofReal_pos.mp (lt_of_le_of_lt zero_le hx')
  have hxU : x ∈ U := by
    rw [← SetLike.mem_coe, hU]
    change riemannianEDistOf _ y x < ENNReal.ofReal ρ
    exact hx'.trans_le (ENNReal.ofReal_le_ofReal (by linarith))
  let pU : U := ⟨x, hxU⟩
  -- common flow 的 `f` 在每点给出 `[j, activeStage s]` 上的 backward trace
  have htraceU : ∀ q : U, ∃ B : BackwardPointTrace H j (H.activeStage s) hjs q.val,
      ∀ (k : Fin (H.eventCount + 1)) (hk1 : j ≤ k) (hk2 : k ≤ H.activeStage s),
        B.point k hk1 hk2 = f ⟨k, haj.trans hk1, hk2⟩ q := by
    intro q
    exact ⟨{ point := fun k hk1 hk2 => f ⟨k, haj.trans hk1, hk2⟩ q
             endpoint_eq := hlast q
             crossing := fun i hi hl => hcross i (haj.trans hi) hl q }, fun _ _ _ => rfl⟩
  let J : H.StageInterval (H.activeStage a) (H.activeStage s) := ⟨j, haj, hjs⟩
  have hfx : f J pU = tr.point j le_rfl hjs := by
    obtain ⟨B, hB⟩ := htraceU pU
    have hBtr : B = tr := Subsingleton.elim _ _
    rw [← hBtr, hB]
  -- 逐点 Grönwall：`g_last(s) ≤ L² f_j^* g_j(t')` 于 `U`
  let Jl : H.StageInterval (H.activeStage a) (H.activeStage s) :=
    ⟨H.activeStage s, H.activeStage_mono hat, le_rfl⟩
  have hfl : f Jl = Subtype.val := funext hlast
  have hsdom : (s : ℝ) ∈ H.stageDomain (H.activeStage s) := H.activeStage_mem s
  have hcar : Icc (a : ℝ) s ⊆ (RealTimeInterval.closed (a : ℝ) s hat).carrier := fun _ h => h
  have hreg : Ioo (a : ℝ) s ⊆ (RealTimeInterval.closed (a : ℝ) s hat).regular := fun _ h => h
  have hsI : (s : ℝ) ∈ Icc (a : ℝ) s := ⟨hat, le_rfl⟩
  have ht'I : t' ∈ Icc (a : ℝ) s := ⟨hat', ht's⟩
  have hexp : Real.exp (2 * (Module.finrank ℝ ThreeSpace : ℝ) ^ 2 * Real.sqrt (K ^ 2) *
      |(s : ℝ) - t'|) ≤ L ^ 2 := by
    have hfin : (Module.finrank ℝ ThreeSpace : ℝ) = 3 := by simp [ThreeSpace]
    have hst : |(s : ℝ) - t'| ≤ θ := by
      rw [abs_of_nonneg (by linarith)]
      linarith
    rw [hfin, Real.sqrt_sq hK, hLdef, ← Real.exp_nat_mul]
    exact Real.exp_le_exp.2 (by push_cast; nlinarith [mul_le_mul_of_nonneg_left hst hK])
  have hlower : ∀ q : U,
      q.val ∈ riemannianClosedBallOf (H.stageMetric (H.activeStage s) s) pU.val (L * ℓ) →
      ∀ v : TangentSpace ThreeModel q,
        (H.stageMetric (H.activeStage s) s).inner q.val v v ≤
          L ^ 2 * (H.stageMetric j t').inner (f J q)
            (mfderiv ThreeModel ThreeModel (f J) q v)
            (mfderiv ThreeModel ThreeModel (f J) q v) := by
    intro q _ v
    have hb := (metric_inner_exp_bounds_of_curvature_bound S hS hcar hreg q
      (fun r' hr' => hRm r' hr' q) hsI ht'I v).2
    rw [hmetric Jl s hsI hsdom, hmetric J t' ht'I hdom, localPullMetric_inner,
      localPullMetric_inner, hfl, mfderiv_subtype_val_apply] at hb
    exact hb.trans (mul_le_mul_of_nonneg_right hexp (metric_inner_self_nonneg _ _ _))
  -- ball capture
  have hcompact : IsCompact
      (riemannianClosedBallOf (H.stageMetric (H.activeStage s) s) pU.val (L * ℓ)) :=
    (Geometry.Metric.isClosed_riemannianClosedBallOf _ _ _).isCompact
  have hsource : riemannianClosedBallOf (H.stageMetric (H.activeStage s) s) pU.val (L * ℓ) ⊆
      (U : Set (H.stageAt s).Carrier) := by
    intro w hw
    rw [hU]
    have hw' : riemannianEDistOf (H.stageMetric (H.activeStage s) s) x w ≤
        ENNReal.ofReal (L * ℓ) := hw
    change riemannianEDistOf _ y w < ENNReal.ofReal ρ
    calc riemannianEDistOf (H.stageMetric (H.activeStage s) s) y w
        ≤ riemannianEDistOf (H.stageMetric (H.activeStage s) s) y x +
          riemannianEDistOf (H.stageMetric (H.activeStage s) s) x w :=
          riemannianEDistOf_triangle _ _ _ _
      _ < ENNReal.ofReal r + ENNReal.ofReal (L * ℓ) :=
          ENNReal.add_lt_add_of_lt_of_le (ne_top_of_le_ne_top ENNReal.ofReal_ne_top hw') hx' hw'
      _ = ENNReal.ofReal (r + L * ℓ) := (ENNReal.ofReal_add hr.le hLℓ.le).symm
      _ ≤ ENNReal.ofReal ρ := ENNReal.ofReal_le_ofReal hrad
  have hcap := Geometry.Metric.ball_subset_image_of_metric_lower_on_opens
    (H.stageMetric j t') (H.stageMetric (H.activeStage s) s) U (f J) (hf J) (hinj J) pU
    hLℓ hL hcompact hsource hlower
  have hdiv : L * ℓ / L = ℓ := by field_simp
  rw [hdiv, hfx] at hcap
  obtain ⟨q, hq, hqz⟩ := hcap hz
  obtain ⟨B, hB⟩ := htraceU q
  refine ⟨q.val, ?_, hq, B, ?_, ?_⟩
  · have hqU := q.property
    rw [← SetLike.mem_coe, hU] at hqU
    exact hqU
  · rw [hB]
    exact hqz
  · have h1 := hRm t' ht'I q
    have hrm : S.base.rm04 t' q = metricRm04At (S.base.metric t') q := metricRm04_apply _ _
    rw [hrm, hmetric J t' ht'I hdom, normSq0S_metricRm04At_localPullMetric, hqz] at h1
    exact h1

/-- **`backwardSurvivorDomain` 形（`_P6E`）**：`survives_of_traced_ball_P6E` 的前提下，`z` 是
`backwardSurvivorMap j (activeStage s)` 在某个 `q ∈ backwardSurvivorDomain`、`q ∈ B_s(y, ρ)` 的值。 -/
theorem survives_backwardSurvivorDomain_of_traced_ball_P6E (H : ObservedHistory.{u})
    (s : Icc (0 : ℝ) H.horizon) (y : (H.stageAt s).Carrier) {ρ θ K r ℓ : ℝ}
    (htr : H.isTracedRegion s y ρ θ K) (hK : 0 ≤ K) (hℓ : 0 < ℓ)
    (hrad : r + Real.exp (9 * K * θ) * ℓ ≤ ρ)
    (x : (H.stageAt s).Carrier)
    (hx : x ∈ riemannianBallOf (H.stageMetric (H.activeStage s) s) y r)
    (j : Fin (H.eventCount + 1)) (hjs : j ≤ H.activeStage s)
    (tr : BackwardPointTrace H j (H.activeStage s) hjs x)
    (t' : ℝ) (ht'a : (s : ℝ) - θ ≤ t') (ht's : t' ≤ s) (hdom : t' ∈ H.stageDomain j)
    (z : (H.stage j).Carrier)
    (hz : riemannianEDistOf (H.stageMetric j t') (tr.point j le_rfl hjs) z <
      ENNReal.ofReal ℓ) :
    ∃ q : H.backwardSurvivorDomain j (H.activeStage s) hjs,
      q.val ∈ riemannianBallOf (H.stageMetric (H.activeStage s) s) y ρ ∧
      H.backwardSurvivorMap j (H.activeStage s) hjs j le_rfl hjs q = z := by
  obtain ⟨x', hx', -, A, hA, -⟩ :=
    H.survives_of_traced_ball_P6E s y htr hK hℓ hrad x hx j hjs tr t' ht'a ht's hdom z hz
  exact ⟨⟨x', ⟨A⟩⟩, hx', (H.backwardSurvivorMap_eq_point j (H.activeStage s) hjs j le_rfl hjs
    ⟨x', ⟨A⟩⟩ A).trans hA⟩

end ObservedHistory

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
