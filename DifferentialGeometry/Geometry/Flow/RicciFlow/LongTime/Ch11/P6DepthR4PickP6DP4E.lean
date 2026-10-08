import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.P6DepthDriverR4P6DP4D
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.P6FirstFailureP6FF
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.Dist.EndpointProtectionC11G

/-!
# 深度归纳期 4 / R4 前半（DEPTH4E-1，后缀 `_P6DP4E`）：activeStage 桥、保护条件、对角取点

DEPTH4D state 的 T3 剩余与 T4 步 1：
* **(③) activeStage 桥**：`activeStage_time_succ_P6DP4E`（`σ = time e⁺ ⇒ activeStage σ = e.succ`）；
  `edist_activeStage_eq_P6DP4E`（stageAt 形的 `d(seed, y)` 经 `activeStage = k` 与 `HEq` 化成
  stage `k` 形；`k = e.castSucc` 用 `activeStage_eq_castSucc_of_mem_P6FF`，`k = e.succ` 用上一条）。
* **(①) 保护条件**：`prot_of_scalar_lt_P6DP4E`：record 精度 `≤ ε₀`、阶 `≥ 2`、canonical windows、
  `transitionEnd + 10 < modelRadius`，点的 output 标量 `< scale_b/2`（每个 `b`）⇒ 不在 cap window 内区
  （`exists_not_ageZeroCapPoint_of_scalar_lt_C11G` ∘ `not_mem_capWindow_inner_of_not_ageZero_C11G`）；
  `scalar_lt_half_scale_of_sep_P6DP4E`：hsepWK 形 `2·max(a, C·R) < scale` + 点标量 `≤ C·R`
  （或 `≤ a`）⇒ `< scale/2`。
* **(取点)** `exists_pick_frequently_eventually_P6DP4E`：逐 `m` 的 `∃ᶠ t ↑ s m` 坏 ∩ `∀ᶠ t ↑ s m` 好
  ⇒ 选 `t m`。
* **(②) records 组装** `hcomp_event_of_records_P6DP4E`：DEPTH4D T3 核 + `S := (records e).static` +
  canonical windows + (①) 的保护（由两端 output 标量 `< scale/2` 给）⇒ event 形距离可比；
  `hOld` 取 DIST `hevent_of_records_C11D` 的已登记前提形。
不新增 binder；E2（driver 前提 + 反证收尾）的输入形见 state-O-CH11-DEPTH4E.md。
-/

set_option autoImplicit false

noncomputable section

open Set Filter
open DifferentialGeometry DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn
open scoped NNReal Topology Manifold ContDiff ENNReal

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

universe u

/-! ### (③) activeStage 桥 -/

/-- **event 输出时刻的 activeStage（`_P6DP4E`）**：`σ = time e⁺` ⇒ `activeStage σ = e.succ`。 -/
theorem activeStage_time_succ_P6DP4E (K : RetainedCoreHistory.{u}) (e : Fin K.eventCount)
    (σ : Icc (0 : ℝ) K.toHistory.horizon) (hσ : (σ : ℝ) = K.time e.succ) :
    K.toHistory.activeStage σ = e.succ := by
  refine ObservedHistory.activeStage_eq_of_maximal _ σ e.succ hσ.symm.le fun k' hk' => ?_
  have h : K.time k' ≤ K.time e.succ := hσ ▸ hk'
  exact K.time_strictMono.le_iff_le.mp h

/-- **距离桥（`_P6DP4E`）**：`activeStage t = k` 时，stageAt 形的 `d_t(A.point (activeStage t), y)` 等于
stage `k` 形的 `d_{k,t}(A.point k, y′)`（`HEq y y′`）。依赖型改写一次完成（泛化 `k` 后 `subst`）。 -/
theorem edist_activeStage_eq_P6DP4E (H : ObservedHistory.{u})
    {first last : Fin (H.eventCount + 1)} {hle : first ≤ last} {endpoint : (H.stage last).Carrier}
    (A : BackwardPointTrace H first last hle endpoint) (t : Icc (0 : ℝ) H.horizon)
    (k : Fin (H.eventCount + 1)) (hk : H.activeStage t = k)
    (h1 : first ≤ H.activeStage t) (h2 : H.activeStage t ≤ last) (h1' : first ≤ k) (h2' : k ≤ last)
    (y : (H.stageAt t).Carrier) (y' : (H.stage k).Carrier) (hy : HEq y y') :
    riemannianEDistOf (H.stageMetric (H.activeStage t) t) (A.point (H.activeStage t) h1 h2) y =
      riemannianEDistOf (H.stageMetric k t) (A.point k h1' h2') y' := by
  suffices key : ∀ (j : Fin (H.eventCount + 1)) (hj : j = k) (g1 : first ≤ j) (g2 : j ≤ last)
      (z : (H.stage j).Carrier), HEq z y' →
      riemannianEDistOf (H.stageMetric j t) (A.point j g1 g2) z =
        riemannianEDistOf (H.stageMetric k t) (A.point k h1' h2') y' from
    key (H.activeStage t) hk h1 h2 y hy
  intro j hj g1 g2 z hz
  subst hj
  obtain rfl := eq_of_heq hz
  rfl

/-! ### (①) 保护条件 -/

/-- **保护 ⇐ 标量（`_P6DP4E`）**：record 精度 `≤ ε₀`、阶 `≥ 2`、canonical windows、
`transitionEnd + 10 < modelRadius`；`z` 的 output 标量 `< scale_b/2`（每个 `b`）⇒ `z` 不在任何 cap window
内区。 -/
theorem prot_of_scalar_lt_P6DP4E :
    ∃ ε₀ : ℝ, 0 < ε₀ ∧
      ∀ {H : ObservedHistory.{u}} {e : Fin H.eventCount} {q : CutoffParameters}
        (R : GeometricCutoffRecord H e q), q.modelAccuracy ≤ ε₀ → 2 ≤ q.modelOrder →
        (∀ b, (R.static b).hasCanonicalWindow) →
        StandardCap.transitionEnd + 10 < q.modelRadius →
        ∀ z : (H.stage e.succ).Carrier,
          (∀ b, metricScalarAt (H.event e).outputMetric z < (R.static b).neck.scale / 2) →
          ∀ b, z ∉ (R.static b).window ''
            {x : standardCapWindow q.modelRadius | ‖x.val‖ ≤ StandardCap.transitionEnd + 10} := by
  obtain ⟨ε₀, hε₀, h⟩ := exists_not_ageZeroCapPoint_of_scalar_lt_C11G.{u}
  refine ⟨ε₀, hε₀, ?_⟩
  intro H e q R hacc hm hcan hDm z hz b
  have hD : StandardCap.transitionEnd + 9 < q.modelRadius - 1 := by linarith
  have hD1 : q.modelRadius - 1 + 1 ≤ q.modelRadius := by linarith
  exact not_mem_capWindow_inner_of_not_ageZero_C11G R hD (h R hacc hm hcan hD1 z hz) b

/-- **hsepWK 形 ⇒ 半 scale（`_P6DP4E`）**：`2·max(a, C·R) < scale`，点标量 `≤ C·R` ⇒ `< scale/2`。 -/
theorem scalar_lt_half_scale_of_sep_P6DP4E {a C R scal S : ℝ}
    (hsep : 2 * max a (C * R) < S) (hz : scal ≤ C * R) : scal < S / 2 := by
  have := le_max_right a (C * R)
  linarith

/-- **hsepWK 形 ⇒ 半 scale（seed 端，`_P6DP4E`）**：`2·max(a, C·R) < scale`，点标量 `≤ a` ⇒ `< scale/2`。 -/
theorem scalar_lt_half_scale_of_sep_seed_P6DP4E {a C R scal S : ℝ}
    (hsep : 2 * max a (C * R) < S) (hz : scal ≤ a) : scal < S / 2 := by
  have := le_max_left a (C * R)
  linarith

/-! ### (取点) 对角取点 -/

/-- **逐 `m` 的 `∃ᶠ` 坏 ∩ `∀ᶠ` 好 ⇒ 选点（`_P6DP4E`）**：R4 的 `t_m ∈ {坏} ∩ U_m`（`U_m` = no-shortcut 的
`∀ᶠ t ↑ σ` 集 ∩ 逐中心 κ 的 `∀ᶠ` 集 ∩ `s − t ≤ 1/R` 等）。 -/
theorem exists_pick_frequently_eventually_P6DP4E {s : ℕ → ℝ} {Bad Good : ℕ → ℝ → Prop}
    (hB : ∀ m, ∃ᶠ t in 𝓝[<] s m, Bad m t) (hG : ∀ m, ∀ᶠ t in 𝓝[<] s m, Good m t) :
    ∃ t : ℕ → ℝ, ∀ m, Bad m (t m) ∧ Good m (t m) := by
  choose t ht using fun m => ((hB m).and_eventually (hG m)).exists
  exact ⟨t, ht⟩

/-- **`s − t ≤ 1/R` 是 `∀ᶠ t ↑ s`（`_P6DP4E`）**：供取点的好集合之一（T2 的 `hclose`）。 -/
theorem eventually_close_P6DP4E {s R : ℝ} (hR : 0 < R) :
    ∀ᶠ t in 𝓝[<] s, s - t ≤ 1 / R ∧ t < s := by
  have hpos : 0 < 1 / R := by positivity
  filter_upwards [Ioo_mem_nhdsLT (show s - 1 / R < s by linarith)] with t ht
  exact ⟨by linarith [ht.1], ht.2⟩

/-! ### (②) records 组装 -/

/-- **(②) event 形距离可比 ⇐ records（`_P6DP4E`）**：record `R`（精度 `≤ ε₀`、阶 `≥ 2`、canonical windows、
`transitionEnd + 10 < modelRadius`）、`hOld`（DIST `hevent_of_records_C11D` 已登记前提形）、seed trace `A`、
新中心 crossing `ym ↦ yp`、两端 output 标量 `< scale_b/2`（hsepWK 形经 `scalar_lt_half_scale_of_sep*` 给）
⇒ `∀ δ > 0, ∀ᶠ t ↑ time e⁺`，`d_{e⁻,t}(seed, ym) ≤ d_{e⁺,τ}(seed, yp) + δ`。 -/
theorem hcomp_event_of_records_P6DP4E :
    ∃ ε₀ : ℝ, 0 < ε₀ ∧
    ∀ (H : ObservedHistory.{u}) (e : Fin H.eventCount) {q : CutoffParameters}
      (R : GeometricCutoffRecord H e q)
      {first last : Fin (H.eventCount + 1)} {hle : first ≤ last}
      {endpoint : (H.stage last).Carrier}
      (A : BackwardPointTrace H first last hle endpoint)
      (hf : first ≤ e.castSucc) (hl : e.succ ≤ last),
      (H.event e).old = (H.event e).transition.trace.retainedCore →
      (∀ b, (R.static b).hasCanonicalWindow) →
      q.modelAccuracy ≤ ε₀ → 2 ≤ q.modelOrder → StandardCap.transitionEnd + 10 < q.modelRadius →
      ∀ {ym : (H.stage e.castSucc).Carrier} {yp : (H.stage e.succ).Carrier},
      (H.event e).RegularCrossing ym yp →
      (∀ b, metricScalarAt (H.event e).outputMetric
          (A.point e.succ (hf.trans (Fin.castSucc_lt_succ (i := e)).le) hl) <
        (R.static b).neck.scale / 2) →
      (∀ b, metricScalarAt (H.event e).outputMetric yp < (R.static b).neck.scale / 2) →
      ∀ {δ : ℝ}, 0 < δ →
      ∀ᶠ t in 𝓝[<] H.time e.succ,
        riemannianEDistOf (H.stageMetric e.castSucc t)
            (A.point e.castSucc hf ((Fin.castSucc_lt_succ (i := e)).le.trans hl)) ym ≤
          riemannianEDistOf (H.stageMetric e.succ (H.time e.succ))
              (A.point e.succ (hf.trans (Fin.castSucc_lt_succ (i := e)).le) hl) yp +
            ENNReal.ofReal δ := by
  obtain ⟨ε₁, hε₁, hprot⟩ := prot_of_scalar_lt_P6DP4E.{u}
  refine ⟨min ε₁ (1 / 2), lt_min hε₁ (by norm_num), ?_⟩
  intro H e q R first last hle endpoint A hf hl hOld hcan hacc hm hDm ym yp hy hseed hyp δ hδ
  have hacc₁ : q.modelAccuracy ≤ ε₁ := hacc.trans (min_le_left _ _)
  have hacc₂ : q.modelAccuracy ≤ 1 / 2 := hacc.trans (min_le_right _ _)
  exact ObservedHistory.hcomp_event_of_noShortcut_P6DP4D H e A hf hl R.static hOld hcan hacc₂ hDm hy
    (hprot R hacc₁ hm hcan hDm _ hseed) (hprot R hacc₁ hm hcan hDm _ hyp) hδ

/-! ### (③) 化成 T1 的 `hcomp` 形 -/

/-- **event 形 ⇒ T1 `hcomp` 形（`_P6DP4E`）**：`s = time e⁺`（R4 塔中心在 output 端）、`t ∈ (time e⁻, time e⁺)`；
event 形距离可比（`stageMetric e.castSucc t` / `stageMetric e.succ (time e⁺)`，`HEq` 对齐两端点）⇒
DEPTH4D `hgood_center_transport_P6DP4D` 的 `hcomp`（activeStage 形）。 -/
theorem hcomp_activeStage_of_event_P6DP4E (K : RetainedCoreHistory.{u}) (e : Fin K.eventCount)
    {Tn aSeed : Icc (0 : ℝ) K.toHistory.horizon} (haT : aSeed ≤ Tn)
    {p : (K.toHistory.stageAt Tn).Carrier}
    (seedTrace : BackwardPointTrace K.toHistory (K.toHistory.activeStage aSeed)
      (K.toHistory.activeStage Tn) (K.toHistory.activeStage_mono haT) p)
    (s t : Icc (0 : ℝ) K.toHistory.horizon) (hs : (s : ℝ) = K.time e.succ)
    (ht : (t : ℝ) ∈ Ioo (K.time e.castSucc) (K.time e.succ))
    (hat : aSeed ≤ t) (hts : t ≤ s) (hsT : s ≤ Tn) (has : aSeed ≤ s)
    (hf : K.toHistory.activeStage aSeed ≤ e.castSucc) (hl : e.succ ≤ K.toHistory.activeStage Tn)
    (w : (K.toHistory.stageAt s).Carrier) (y : (K.toHistory.stageAt t).Carrier)
    (wp : (K.toHistory.stage e.succ).Carrier) (ym : (K.toHistory.stage e.castSucc).Carrier)
    (hw : HEq w wp) (hy : HEq y ym) {d : ENNReal}
    (hev : riemannianEDistOf (K.toHistory.stageMetric e.castSucc t)
        (seedTrace.point e.castSucc hf ((Fin.castSucc_lt_succ (i := e)).le.trans hl)) ym ≤
      riemannianEDistOf (K.toHistory.stageMetric e.succ (K.time e.succ))
          (seedTrace.point e.succ (hf.trans (Fin.castSucc_lt_succ (i := e)).le) hl) wp + d) :
    riemannianEDistOf (K.toHistory.stageMetric (K.toHistory.activeStage t) t)
        (seedTrace.point (K.toHistory.activeStage t) (K.toHistory.activeStage_mono hat)
          (K.toHistory.activeStage_mono (hts.trans hsT))) y ≤
      riemannianEDistOf (K.toHistory.stageMetric (K.toHistory.activeStage s) s)
          (seedTrace.point (K.toHistory.activeStage s) (K.toHistory.activeStage_mono has)
            (K.toHistory.activeStage_mono hsT)) w + d := by
  rw [edist_activeStage_eq_P6DP4E K.toHistory seedTrace t e.castSucc
      (RetainedCoreHistory.activeStage_eq_castSucc_of_mem_P6FF (H := K) e t ht) _ _ hf
      ((Fin.castSucc_lt_succ (i := e)).le.trans hl) y ym hy,
    edist_activeStage_eq_P6DP4E K.toHistory seedTrace s e.succ
      (activeStage_time_succ_P6DP4E K e s hs) _ _ (hf.trans (Fin.castSucc_lt_succ (i := e)).le) hl
      w wp hw, hs]
  exact hev

/-! ### ② + ③：R4 中心的 `hcomp`（eventually 形） -/

/-- **R4 中心的 `hcomp`（`_P6DP4E`，PROVED 相对 records / hOld / 两端标量条件）**：R4 塔中心 `s = time e⁺`、
`w ≍ wp`；新中心点 `ym`（`ym ↦ wp` crossing）。则 `∀ᶠ t′ ↑ time e⁺`，对每个落在 `t′` 的 Icc 点 `t` 与
`y ≍ ym`，DEPTH4D T1 的 `hcomp`（activeStage 形，`δ` 任意）成立。取点时把它并入好集合即可（取 `δ := 1/√R`）。 -/
theorem hcomp_R4_eventually_P6DP4E :
    ∃ ε₀ : ℝ, 0 < ε₀ ∧
    ∀ (K : RetainedCoreHistory.{u}) (e : Fin K.eventCount) {q : CutoffParameters}
      (R : GeometricCutoffRecord K.toHistory e q)
      {Tn aSeed : Icc (0 : ℝ) K.toHistory.horizon} (haT : aSeed ≤ Tn)
      {p : (K.toHistory.stageAt Tn).Carrier}
      (seedTrace : BackwardPointTrace K.toHistory (K.toHistory.activeStage aSeed)
        (K.toHistory.activeStage Tn) (K.toHistory.activeStage_mono haT) p)
      (hf : K.toHistory.activeStage aSeed ≤ e.castSucc)
      (hl : e.succ ≤ K.toHistory.activeStage Tn),
      (K.toHistory.event e).old = (K.toHistory.event e).transition.trace.retainedCore →
      (∀ b, (R.static b).hasCanonicalWindow) →
      q.modelAccuracy ≤ ε₀ → 2 ≤ q.modelOrder → StandardCap.transitionEnd + 10 < q.modelRadius →
      ∀ {ym : (K.toHistory.stage e.castSucc).Carrier} {wp : (K.toHistory.stage e.succ).Carrier},
      (K.toHistory.event e).RegularCrossing ym wp →
      (∀ b, metricScalarAt (K.toHistory.event e).outputMetric
          (seedTrace.point e.succ (hf.trans (Fin.castSucc_lt_succ (i := e)).le) hl) <
        (R.static b).neck.scale / 2) →
      (∀ b, metricScalarAt (K.toHistory.event e).outputMetric wp < (R.static b).neck.scale / 2) →
      ∀ {δ : ℝ}, 0 < δ →
      ∀ (s : Icc (0 : ℝ) K.toHistory.horizon), (s : ℝ) = K.time e.succ → ∀ (hsT : s ≤ Tn)
        (has : aSeed ≤ s) (w : (K.toHistory.stageAt s).Carrier), HEq w wp →
      ∀ᶠ t' in 𝓝[<] K.time e.succ, ∀ (t : Icc (0 : ℝ) K.toHistory.horizon), (t : ℝ) = t' →
        ∀ (hat : aSeed ≤ t) (hts : t ≤ s) (y : (K.toHistory.stageAt t).Carrier), HEq y ym →
        riemannianEDistOf (K.toHistory.stageMetric (K.toHistory.activeStage t) t)
            (seedTrace.point (K.toHistory.activeStage t) (K.toHistory.activeStage_mono hat)
              (K.toHistory.activeStage_mono (hts.trans hsT))) y ≤
          riemannianEDistOf (K.toHistory.stageMetric (K.toHistory.activeStage s) s)
              (seedTrace.point (K.toHistory.activeStage s) (K.toHistory.activeStage_mono has)
                (K.toHistory.activeStage_mono hsT)) w + ENNReal.ofReal δ := by
  obtain ⟨ε₀, hε₀, h2⟩ := hcomp_event_of_records_P6DP4E.{u}
  refine ⟨ε₀, hε₀, ?_⟩
  intro K e q R Tn aSeed haT p seedTrace hf hl hOld hcan hacc hm hDm ym wp hy hseed hwp δ hδ s hs
    hsT has w hw
  have hev := h2 K.toHistory e R seedTrace hf hl hOld hcan hacc hm hDm hy hseed hwp hδ
  filter_upwards [hev, Ioo_mem_nhdsLT (K.time_strictMono (Fin.castSucc_lt_succ (i := e)))]
    with t' ht' hmem t htt hat hts y hyy
  subst htt
  exact hcomp_activeStage_of_event_P6DP4E K e haT seedTrace s t hs hmem hat hts hsT has hf hl w y
    wp ym hw hyy ht'

/-- **consumer（取点）**：好集合 = 任意 `∀ᶠ` 族（如 `hcomp_R4_eventually_P6DP4E` 的输出）∩ `s − t ≤ 1/R`；
坏集合 `∃ᶠ` ⇒ 逐 `m` 选出 `t m`，同时满足坏性、好性与 T2 的 `hclose`。 -/
example (s R : ℕ → ℝ) (hR : ∀ m, 0 < R m) (Bad G : ℕ → ℝ → Prop)
    (hB : ∀ m, ∃ᶠ t in 𝓝[<] s m, Bad m t) (hG : ∀ m, ∀ᶠ t in 𝓝[<] s m, G m t) :
    ∃ t : ℕ → ℝ, ∀ m, Bad m (t m) ∧ (G m (t m) ∧ (s m - t m ≤ 1 / R m ∧ t m < s m)) :=
  exists_pick_frequently_eventually_P6DP4E hB fun m => (hG m).and (eventually_close_P6DP4E (hR m))

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
