import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.Dist.DistanceContractsC11D
import DifferentialGeometry.Geometry.Flow.RicciFlow.Estimates.Distance.FixedEndpoints
import DifferentialGeometry.Geometry.Metric.Completeness
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.SlabPointPicking
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.MasterFlowCompatibility
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.P6SeedTraceP6B

/-!
# P6 距离线 G2：(D3) 光滑段距离畸变（O-CH11-DIST，后缀 `_C11D`）

R-C11-2 D-7 的 (D3)（Perelman I.8.3(b)）在 history stage 上的生产。树内**已有积分形**
`riemannianEDistOf_le_add_of_endpoint_ricci_on_interval`
（`Estimates/Distance/FixedEndpoints.lean:30`）：
两端 `ℓ`-球上 `Ric ≤ (3/ℓ²) g`（只要求端点球，**不需**整条测地线；近距离情形树内已处理）⇒
`d_a(p, x) ≤ d_b(p, x) + (8/ℓ)(b − a)`。这是 D-7 公式 `−2(m−1)(2Ka/3 + 1/a)` 在 `m = 3`、
`K = 3/(2ℓ²)`、`a = ℓ` 的值 `−8/ℓ`。本文件只做 adapter（Hamilton 型整测地线界不需要）：

* `edist_le_add_of_endpoint_ricci_solution_C11D`：stage carrier（紧）上的 solution 版——completeness 由
  紧性给（`RiemannianMetricComplete.of_compact`），`d_b = ⊤`（不同分支）平凡。
* **`smooth_distance_distortion_C11D`（(D3) 合同）**：history 的 stage `k`、`[t₁, t₂]` 在 stage 的 slab 内
  （incoming slab `[time k, time k⁺)` 或 final slab）⇒ 同式。
* 端点 Ricci 上界的生产：`ricciTensor_le_of_sqrt_rmNormSq_le_C11D`（`|Rm| ≤ K ⇒ Ric ≤ 3K g`）；
  `sqrt_rmNormSq_stage_le_of_pinched_C11D`（窗口 pinching ⇒ `|Rm| ≤ C_φ max(R, 1)`，
  stage 形；= `sqrt_rmNormSq_stageMetric_le_of_pinched_window_P6N` 去掉 `activeStage` 包装）。
  种子端 `|Rm|` 界由 K0（`hasSmallParabolicCurvature`）给、另一端由严格内部区域的标量上界 + pinching 给
  （都作显式前提）；标量下界 / 种子控制**不**提供另一端 Ricci 上界（D-7）。
* `smooth_distance_distortion_of_rmNorm_le_C11D`：(D3) 的 `|Rm|` 前提版（`K ℓ² ≤ 1`）。
* **`hsmooth_of_rmNorm_le_C11D`**：G1 `hdist_rel_of_stage_bounds_C11D` 的 `hsmooth` 前提（速率 `Λ = 8/ℓ`）。
-/

set_option autoImplicit false

noncomputable section

open Set Filter Manifold
open DifferentialGeometry DifferentialGeometry.Tensor0SBundle
open DifferentialGeometry.Geometry.Curvature DifferentialGeometry.Geometry.Connection
open scoped Manifold ContDiff Topology ENNReal NNReal BigOperators

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory

universe u

/-! ## (D3) 的 solution / stage adapter -/

/-- **(D3)，solution 版（`_C11D`）**：紧 stage carrier 上的 Ricci flow `S`，`[a, b]` 在 carrier 内、
`(a, b)` regular；两端 `ℓ`-球 `Ric ≤ (3/ℓ²) g` ⇒ `d_a(p, x) ≤ d_b(p, x) + (8/ℓ)(b − a)`。 -/
theorem edist_le_add_of_endpoint_ricci_solution_C11D {P : OrientedThreeStage.{u}}
    {D : RealTimeInterval} (S : SolutionOn (I := ThreeModel) (M := P.Carrier) D)
    (hS : IsSolutionOn S) {a b ℓ : ℝ} (hab : a ≤ b) (hℓ : 0 < ℓ)
    (hcarrier : Icc a b ⊆ D.carrier) (hregular : Ioo a b ⊆ D.regular) (p x : P.Carrier)
    (hRic : ∀ t ∈ Ioo a b, ∀ z : P.Carrier, ∀ ξ : TangentSpace ThreeModel z,
      (riemannianEDistOf (S.base.metric t) p z < ENNReal.ofReal ℓ ∨
        riemannianEDistOf (S.base.metric t) x z < ENNReal.ofReal ℓ) →
      ricciTensor (S.base.metric t) z ξ ξ ≤ (3 / ℓ ^ 2) * (S.base.metric t).inner z ξ ξ) :
    riemannianEDistOf (S.base.metric a) p x ≤
      riemannianEDistOf (S.base.metric b) p x + ENNReal.ofReal ((8 / ℓ) * (b - a)) := by
  by_cases hfin : riemannianEDistOf (S.base.metric b) p x = ⊤
  · rw [hfin, top_add]
    exact le_top
  · exact (DifferentialGeometry.PDE.RicciFlow.riemannianEDistOf_le_add_of_endpoint_ricci_on_interval
      S hS (by simp) hab hℓ hcarrier hregular
      (fun t _ => DifferentialGeometry.RiemannianMetricComplete.of_compact _) p x hfin
      hRic).2

/-- **(D3) 合同（`_C11D`）**：history 的 stage `k`，`time k ≤ t₁ ≤ t₂`，`t₂` 早于 `k` 的下一个 event
（`k = e⁻ ⇒ t₂ < time e⁺`）且 `t₂ ≤ horizon`；两端点 `p, q` 的 `ℓ`-球在 `(t₁, t₂)` 上
`Ric ≤ (3/ℓ²) g` ⇒ `d_{k,t₁}(p, q) ≤ d_{k,t₂}(p, q) + (8/ℓ)(t₂ − t₁)`（Perelman I.8.3(b) 积分形）。 -/
theorem smooth_distance_distortion_C11D (H : ObservedHistory.{u})
    (k : Fin (H.eventCount + 1)) {t₁ t₂ ℓ : ℝ} (hℓ : 0 < ℓ) (h12 : t₁ ≤ t₂)
    (hk : H.time k ≤ t₁) (hnext : ∀ e : Fin H.eventCount, k = e.castSucc → t₂ < H.time e.succ)
    (hhor : t₂ ≤ H.horizon) (p q : (H.stage k).Carrier)
    (hRic : ∀ t ∈ Ioo t₁ t₂, ∀ z : (H.stage k).Carrier, ∀ ξ : TangentSpace ThreeModel z,
      (riemannianEDistOf (H.stageMetric k t) p z < ENNReal.ofReal ℓ ∨
        riemannianEDistOf (H.stageMetric k t) q z < ENNReal.ofReal ℓ) →
      ricciTensor (H.stageMetric k t) z ξ ξ ≤ (3 / ℓ ^ 2) * (H.stageMetric k t).inner z ξ ξ) :
    riemannianEDistOf (H.stageMetric k t₁) p q ≤
      riemannianEDistOf (H.stageMetric k t₂) p q + ENNReal.ofReal ((8 / ℓ) * (t₂ - t₁)) := by
  cases k using Fin.lastCases with
  | last =>
    by_cases hlt : H.time (Fin.last H.eventCount) < H.horizon
    · simp only [stageMetric_last_of_lt (h := hlt)] at hRic ⊢
      exact edist_le_add_of_endpoint_ricci_solution_C11D (H.finalSlab hlt).flow
        (H.finalSlab hlt).equation h12 hℓ (fun t ht => ⟨hk.trans ht.1, ht.2.trans hhor⟩)
        (fun t ht => ⟨lt_of_le_of_lt hk ht.1, lt_of_lt_of_le ht.2 hhor⟩) p q hRic
    · have h1 : t₁ = t₂ := by
        have := H.time_le_horizon
        linarith [not_lt.1 hlt]
      subst h1
      simp
  | cast e =>
    simp only [stageMetric_castSucc_apply] at hRic ⊢
    have hlt := hnext e rfl
    exact edist_le_add_of_endpoint_ricci_solution_C11D (H.event e).incoming.flow
      (H.event e).incoming.equation h12 hℓ (fun t ht => ⟨hk.trans ht.1, lt_of_le_of_lt ht.2 hlt⟩)
      (fun t ht => ⟨lt_of_le_of_lt hk ht.1, ht.2.trans hlt⟩) p q hRic

/-! ## 端点 Ricci 上界的生产 -/

/-- 正交基缩并：`|Ric(w, w)| ≤ n·|Rm|·g(w, w)`（`P6SeedTraceP6B` 私有引理的 `_C11D` 副本）。 -/
private theorem ricciTensor_abs_le_dim_mul_sqrt_rmNormSq_C11D
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
    [T2Space M] [BoundarylessManifold I M]
    (g : SmoothRiemannianMetric I M) (x : M) (w : TangentSpace I x) :
    |ricciTensor g x w w| ≤
      (Module.finrank ℝ E : ℝ) *
        Real.sqrt (normSq0S g x 4 (metricRm04At g x)) * g.inner x w w := by
  classical
  obtain ⟨b, hb⟩ := exists_orthonormal_basis g x
  have hinv := metricInverseInBasis_of_orthonormal g b hb
  let A := ricciEndo g x w w
  have htrace : ricciTensor g x w w = ∑ i, b.repr (A (b i)) i := by
    rw [ricciTensor_apply, LinearMap.trace_eq_matrix_trace ℝ b]
    simp only [Matrix.trace, Matrix.diag, LinearMap.toMatrix_apply]
    rfl
  rw [htrace]
  calc
    _ ≤ ∑ i, |b.repr (A (b i)) i| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _i : Fin (Module.finrank ℝ (TangentSpace I x)),
        Real.sqrt (normSq0S g x 4 (metricRm04At g x)) * g.inner x w w := by
      apply Finset.sum_le_sum
      intro i _
      have hu : g.inner x (b i) (b i) = 1 := by simpa only [ite_true] using hb i i
      have hrepr : b.repr (A (b i)) i = g.inner x (A (b i)) (b i) := by
        rw [basis_repr_eq_sum_inv_inner g x b _ hinv]
        simp [identityInvMetric, diagonalInvMetric]
      have heval : b.repr (A (b i)) i =
          metricRm04At g x (vec4 (b i) w w (b i)) := by
        rw [hrepr]
        change g.inner x (riemannOp (LeviCivita g) x (b i) w w) (b i) = _
        rw [g.symm, ← rm04_eq_inner, metricRm04StandardAt_apply]
      rw [heval]
      have h := abs_apply_le_norm0S g x 4 (metricRm04At g x) (vec4 (b i) w w (b i))
      have hprod : (∏ a : Fin 4,
          Real.sqrt (g.inner x ((vec4 (b i) w w (b i)) a)
            ((vec4 (b i) w w (b i)) a))) = g.inner x w w := by
        simp [vec4, Fin.prod_univ_succ, hu, ← pow_two,
          Real.sq_sqrt (metric_inner_self_nonneg g x w)]
      simpa only [hprod] using h
    _ = _ := by
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      rw [show Module.finrank ℝ (TangentSpace I x) = Module.finrank ℝ E from rfl]
      ring

/-- **`|Rm| ≤ K ⇒ Ric ≤ 3K g`（`_C11D`）**：stage 度量（维数 3）。 -/
theorem ricciTensor_le_of_sqrt_rmNormSq_le_C11D {P : OrientedThreeStage.{u}} (g : P.Metric)
    (x : P.Carrier) {K : ℝ} (hK : Real.sqrt (normSq0S g x 4 (metricRm04At g x)) ≤ K)
    (w : TangentSpace ThreeModel x) :
    ricciTensor g x w w ≤ 3 * K * g.inner x w w := by
  have h := ricciTensor_abs_le_dim_mul_sqrt_rmNormSq_C11D g x w
  have hdim : Module.finrank ℝ ThreeSpace = 3 := by simp
  rw [hdim] at h
  have hg : 0 ≤ g.inner x w w := metric_inner_self_nonneg g x w
  calc ricciTensor g x w w ≤ |ricciTensor g x w w| := le_abs_self _
    _ ≤ ((3 : ℕ) : ℝ) * Real.sqrt (normSq0S g x 4 (metricRm04At g x)) * g.inner x w w := h
    _ ≤ 3 * K * g.inner x w w := by
      push_cast
      exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hK (by norm_num)) hg

/-- **窗口 pinching ⇒ `|Rm| ≤ C_φ max(R, 1)`，stage 形（`_C11D`）**：`time k ≤ t`、`t` 在 stage `k` 的
slab 内、`a ≤ t`；pinching 只在 `[a, ∞)` 上要（`sqrt_rmNormSq_stageMetric_le_of_pinched_window_P6N`
去掉 `activeStage` 包装；证明同）。 -/
theorem sqrt_rmNormSq_stage_le_of_pinched_C11D (H : ObservedHistory.{u}) {phi : ℝ → ℝ} {a : ℝ}
    (hphi : Perelman.AdmissiblePinchingFunction phi)
    (hpinch : ∀ j : Fin H.eventCount, Perelman.PhiAlmostNonnegative
      (H.event j).incoming.flow (Ico (H.time j.castSucc) (H.time j.succ) ∩ Ici a) phi)
    (k : Fin (H.eventCount + 1)) {t : ℝ} (hk : H.time k ≤ t)
    (hnext : ∀ e : Fin H.eventCount, k = e.castSucc → t < H.time e.succ) (hhor : t ≤ H.horizon)
    (hat : a ≤ t)
    (hlast : k = Fin.last H.eventCount →
      ∃ h : H.time (Fin.last H.eventCount) < H.horizon,
        Perelman.PhiAlmostNonnegative (H.finalSlab h).flow
          (Icc (H.time (Fin.last H.eventCount)) H.horizon ∩ Ici a) phi)
    (z : (H.stage k).Carrier) :
    Real.sqrt (normSq0S (H.stageMetric k t) z 4 (metricRm04At (H.stageMetric k t) z)) ≤
      4 * Real.sqrt 3 * (1 + phi 1 + phi 0) * max (metricScalarAt (H.stageMetric k t) z) 1 := by
  have hdim : Module.finrank ℝ ThreeSpace = 3 := by simp
  cases k using Fin.lastCases with
  | last =>
    obtain ⟨h, hfp⟩ := hlast rfl
    have := IsManifold.of_le (I := ThreeModel) (M := (H.stage (Fin.last H.eventCount)).Carrier)
      (n := ∞) (m := 1) (by decide)
    have hb :=
      Perelman.CanonicalNeighborhood.sqrt_rmNormSq_le_mul_max_scalar_one_of_phiAlmostNonnegative
      hphi hfp hdim ⟨⟨hk, hhor⟩, hat⟩ z
    rw [stageMetric_last_of_lt (h := h)]
    exact hb
  | cast e =>
    have := IsManifold.of_le (I := ThreeModel) (M := (H.stage e.castSucc).Carrier)
      (n := ∞) (m := 1) (by decide)
    have hb :=
      Perelman.CanonicalNeighborhood.sqrt_rmNormSq_le_mul_max_scalar_one_of_phiAlmostNonnegative
      hphi (hpinch e) hdim ⟨⟨hk, hnext e rfl⟩, hat⟩ z
    rw [stageMetric_castSucc_apply]
    exact hb

/-- **(D3)，`|Rm|` 前提版（`_C11D`）**：两端 `ℓ`-球上 `|Rm| ≤ K`、`K ℓ² ≤ 1` ⇒ (D3) 积分形
（`Ric ≤ 3K g ≤ (3/ℓ²) g`）。种子端 `K` 由 K0、另一端由标量上界 + pinching
（`sqrt_rmNormSq_stage_le_of_pinched_C11D`）给。 -/
theorem smooth_distance_distortion_of_rmNorm_le_C11D (H : ObservedHistory.{u})
    (k : Fin (H.eventCount + 1)) {t₁ t₂ ℓ K : ℝ} (hℓ : 0 < ℓ) (hKℓ : K * ℓ ^ 2 ≤ 1)
    (h12 : t₁ ≤ t₂) (hk : H.time k ≤ t₁)
    (hnext : ∀ e : Fin H.eventCount, k = e.castSucc → t₂ < H.time e.succ)
    (hhor : t₂ ≤ H.horizon) (p q : (H.stage k).Carrier)
    (hRm : ∀ t ∈ Ioo t₁ t₂, ∀ z : (H.stage k).Carrier,
      (riemannianEDistOf (H.stageMetric k t) p z < ENNReal.ofReal ℓ ∨
        riemannianEDistOf (H.stageMetric k t) q z < ENNReal.ofReal ℓ) →
      Real.sqrt (normSq0S (H.stageMetric k t) z 4 (metricRm04At (H.stageMetric k t) z)) ≤ K) :
    riemannianEDistOf (H.stageMetric k t₁) p q ≤
      riemannianEDistOf (H.stageMetric k t₂) p q + ENNReal.ofReal ((8 / ℓ) * (t₂ - t₁)) := by
  refine H.smooth_distance_distortion_C11D k hℓ h12 hk hnext hhor p q ?_
  intro t ht z ξ hz
  have hK : K ≤ 1 / ℓ ^ 2 := by
    rw [le_div_iff₀ (pow_pos hℓ 2)]
    exact hKℓ
  have hg : 0 ≤ (H.stageMetric k t).inner z ξ ξ := metric_inner_self_nonneg _ z ξ
  calc ricciTensor (H.stageMetric k t) z ξ ξ ≤ 3 * K * (H.stageMetric k t).inner z ξ ξ :=
        ricciTensor_le_of_sqrt_rmNormSq_le_C11D _ z (hRm t ht z hz) ξ
    _ ≤ (3 / ℓ ^ 2) * (H.stageMetric k t).inner z ξ ξ := by
      apply mul_le_mul_of_nonneg_right _ hg
      calc 3 * K ≤ 3 * (1 / ℓ ^ 2) := by linarith
        _ = 3 / ℓ ^ 2 := by ring

/-! ## G1 `hsmooth` 前提的生产 -/

/-- `activeStage s = e⁻ ⇒ s < time e⁺`（ObservedHistory 版）。 -/
theorem lt_time_succ_of_activeStage_eq_C11D (H : ObservedHistory.{u})
    (s : Icc (0 : ℝ) H.horizon) :
    ∀ e : Fin H.eventCount, H.activeStage s = e.castSucc → (s : ℝ) < H.time e.succ := by
  intro e he
  have hlt : (H.activeStage s : ℕ) < H.eventCount := by
    rw [he]
    exact e.isLt
  have h := H.activeStage_before_next s hlt
  have heq : (⟨(H.activeStage s : ℕ) + 1, by omega⟩ : Fin (H.eventCount + 1)) = e.succ := by
    apply Fin.ext
    simp only [he, Fin.val_castSucc, Fin.val_succ]
  rwa [heq] at h

/-- **G1 `hsmooth` 的生产（`_C11D`）**：末 stage `j = activeStage s` 上，窗口 `(s − θ/Q, s)` 内每个时刻
种子点 `O_j` 与每个 `x ∈ B_s(y, Rad/√Q)` 的 `ℓ`-球上 `|Rm| ≤ K`、`K ℓ² ≤ 1` ⇒
`hdist_rel_of_stage_bounds_C11D` 的 `hsmooth`（速率 `Λ = 8/ℓ`；`ℓ = ℓ'/√Q` 时 `Λ = (8/ℓ')√Q`）。 -/
theorem hsmooth_of_rmNorm_le_C11D (H : ObservedHistory.{u})
    {T aSeed s : Icc (0 : ℝ) H.horizon} (haT : aSeed ≤ T) (hsT : s ≤ T) (has : aSeed ≤ s)
    {p : (H.stageAt T).Carrier}
    (seedTrace : BackwardPointTrace H (H.activeStage aSeed) (H.activeStage T)
      (H.activeStage_mono haT) p)
    (y : (H.stageAt s).Carrier) {Q θ Rad ℓ K : ℝ} (hℓ : 0 < ℓ) (hKℓ : K * ℓ ^ 2 ≤ 1)
    (hRm : ∀ x ∈ riemannianBallOf (H.stageMetric (H.activeStage s) s) y (Rad / Real.sqrt Q),
      ∀ t : ℝ, (s : ℝ) - θ / Q < t → H.time (H.activeStage s) < t → t < s →
      ∀ z : (H.stageAt s).Carrier,
        (riemannianEDistOf (H.stageMetric (H.activeStage s) t)
            (seedTrace.point (H.activeStage s) (H.activeStage_mono has)
              (H.activeStage_mono hsT)) z < ENNReal.ofReal ℓ ∨
          riemannianEDistOf (H.stageMetric (H.activeStage s) t) x z < ENNReal.ofReal ℓ) →
        Real.sqrt (normSq0S (H.stageMetric (H.activeStage s) t) z 4
          (metricRm04At (H.stageMetric (H.activeStage s) t) z)) ≤ K) :
    ∀ x ∈ riemannianBallOf (H.stageMetric (H.activeStage s) s) y (Rad / Real.sqrt Q),
      ∀ t : ℝ, (s : ℝ) - θ / Q ≤ t → H.time (H.activeStage s) ≤ t → t ≤ s →
      riemannianEDistOf (H.stageMetric (H.activeStage s) t)
          (seedTrace.point (H.activeStage s) (H.activeStage_mono has) (H.activeStage_mono hsT))
          x ≤
        riemannianEDistOf (H.stageMetric (H.activeStage s) s)
            (seedTrace.point (H.activeStage s) (H.activeStage_mono has) (H.activeStage_mono hsT))
            x +
          ENNReal.ofReal ((8 / ℓ) * ((s : ℝ) - t)) := by
  intro x hx t hθt hjt hts
  exact H.smooth_distance_distortion_of_rmNorm_le_C11D (H.activeStage s) hℓ hKℓ hts hjt
    (fun e he => H.lt_time_succ_of_activeStage_eq_C11D s e he) s.2.2 _ x
    (fun τ hτ z hz => hRm x hx τ (lt_of_le_of_lt hθt hτ.1) (lt_of_le_of_lt hjt hτ.1) hτ.2 z hz)

/-- **consumer（G2）**：G2 生产的 `hsmooth`（`|Rm|` 端点界）喂 G1 主目标
`hdist_rel_of_stage_bounds_C11D`（速率 `Λ = 8/ℓ`；event 跨越 `hevent` 仍显式，G3 生产）。 -/
example (H : ObservedHistory.{u})
    {T aSeed s : Icc (0 : ℝ) H.horizon} (haT : aSeed ≤ T) (hsT : s ≤ T) (has : aSeed ≤ s)
    {p : (H.stageAt T).Carrier}
    (seedTrace : BackwardPointTrace H (H.activeStage aSeed) (H.activeStage T)
      (H.activeStage_mono haT) p)
    (y : (H.stageAt s).Carrier) {Q L θ Rad ℓ K : ℝ} (hℓ : 0 < ℓ) (hKℓ : K * ℓ ^ 2 ≤ 1)
    (hnum : Rad / Real.sqrt Q + 8 / ℓ * (θ / Q) ≤ L / Real.sqrt Q)
    (hRm : ∀ x ∈ riemannianBallOf (H.stageMetric (H.activeStage s) s) y (Rad / Real.sqrt Q),
      ∀ t : ℝ, (s : ℝ) - θ / Q < t → H.time (H.activeStage s) < t → t < s →
      ∀ z : (H.stageAt s).Carrier,
        (riemannianEDistOf (H.stageMetric (H.activeStage s) t)
            (seedTrace.point (H.activeStage s) (H.activeStage_mono has)
              (H.activeStage_mono hsT)) z < ENNReal.ofReal ℓ ∨
          riemannianEDistOf (H.stageMetric (H.activeStage s) t) x z < ENNReal.ofReal ℓ) →
        Real.sqrt (normSq0S (H.stageMetric (H.activeStage s) t) z 4
          (metricRm04At (H.stageMetric (H.activeStage s) t) z)) ≤ K)
    (hevent : ∀ x ∈ riemannianBallOf (H.stageMetric (H.activeStage s) s) y (Rad / Real.sqrt Q),
      ∀ (v : Icc (0 : ℝ) H.horizon) (_hav : aSeed ≤ v) (hvs : v ≤ s), (s : ℝ) - θ / Q ≤ v →
      ∀ tr : BackwardPointTrace H (H.activeStage v) (H.activeStage s) (H.activeStage_mono hvs) x,
      ∀ (e : Fin H.eventCount) (h1 : H.activeStage aSeed ≤ e.castSucc)
        (h2 : e.succ ≤ H.activeStage T) (h3 : H.activeStage v ≤ e.castSucc)
        (h4 : e.succ ≤ H.activeStage s) (t : ℝ),
        (v : ℝ) ≤ t → H.time e.castSucc ≤ t → t < H.time e.succ →
      riemannianEDistOf (H.stageMetric e.castSucc t)
          (seedTrace.point e.castSucc h1 (e.castSucc_lt_succ.le.trans h2))
          (tr.point e.castSucc h3 (e.castSucc_lt_succ.le.trans h4)) ≤
        riemannianEDistOf (H.stageMetric e.succ (H.time e.succ))
            (seedTrace.point e.succ (h1.trans e.castSucc_lt_succ.le) h2)
            (tr.point e.succ (h3.trans e.castSucc_lt_succ.le) h4) +
          ENNReal.ofReal (8 / ℓ * (H.time e.succ - t))) :
    ∀ x ∈ riemannianBallOf (H.stageMetric (H.activeStage s) s) y (Rad / Real.sqrt Q),
      ∀ (v : Icc (0 : ℝ) H.horizon) (hav : aSeed ≤ v) (hvs : v ≤ s), (s : ℝ) - θ / Q ≤ v →
      ∀ tr : BackwardPointTrace H (H.activeStage v) (H.activeStage s) (H.activeStage_mono hvs) x,
        riemannianEDistOf (H.stageMetric (H.activeStage v) v)
            (seedTrace.point (H.activeStage v) (H.activeStage_mono hav)
              (H.activeStage_mono (hvs.trans hsT)))
            (tr.point (H.activeStage v) le_rfl (H.activeStage_mono hvs)) ≤
          riemannianEDistOf (H.stageMetric (H.activeStage s) s)
              (seedTrace.point (H.activeStage s) (H.activeStage_mono has)
                (H.activeStage_mono hsT)) y +
            ENNReal.ofReal (L / Real.sqrt Q) :=
  H.hdist_rel_of_stage_bounds_C11D haT hsT has seedTrace y (div_nonneg (by norm_num) hℓ.le)
    hnum (H.hsmooth_of_rmNorm_le_C11D haT hsT has seedTrace y hℓ hKℓ hRm) hevent

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory
