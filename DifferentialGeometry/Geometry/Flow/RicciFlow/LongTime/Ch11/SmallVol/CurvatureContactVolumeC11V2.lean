import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.HistoryBallVolume
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.FirstCurvatureContactVolumePortC11P
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Noncollapsing.HistoryDegreeBound
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.SmallVol.BGAdapterC11V

/-!
# O-CH11-SMALLVOL2 G1：曲率接触情形的体积装配（V3）+ 接触体积统一定理（后缀 `_C11V2`）

KL Sublemma 79.23 的 history 级 first-contact：`σ := sSup {r ∈ [q₀, R] | P(p, t, r) controlled}`
（树内三分类 `ObservedHistory.csSup_parabolicallyRmControlledBall_eq_or_cap_or_curvature_eq`，
`Surgery/Topology/HistoryBallVolume.lean:712`）。树内已有 (a) cap 接触体积（`:1775`）与时刻 0 接触体积
（`:2010`），只缺 (b) 曲率饱和接触的**装配**（原语 `exists_inward_point_with_earlier_volume_comparison`
在 `:1534`）。本文件：

* **§1 (b) 核心** `terminal_volume_of_curvature_contact_seed_C11V2`：曲率分支的数据（`a < t − σ²` 的
  closed trace buffer、接触点 `w = A.point v`、`σ⁴|Rm(w)|² ≤ 1`）+ 接触切片上 `w` 的 canonical witness
  （只用 `ball_inside` / `radius_lower` / `rm_bound`）+ **native 体积种子**
  `κ_w (σ/100)³ ≤ Vol_v B(w, σ/100)` ⇒ `κ r³ ≤ Vol_t B(p, r)`（`r ≤ σ`），`κ = κ(κ_w, C₂)`。
  路线 = KL (b)：`:1534` 向内取点 `z`
  （`B̄_t(z, θσ/2) ⊆ B_t(p, σ)`，`d_v(π z, w) ≤ e⁹θσ = σ/100`）→ witness domain 内 BG 把种子从 `w` 搬到
  `π z`（`B_v(π z, σ/50) ⊆ domain`，`|Rm| ≤ 9C₂/σ²`）→ `e⁻²⁷` 体积运输回 `t` → history BG 降到 `r`。
* **§2 种子来源**（接触点的 native 体积；`hcan` 是显式前提）：
  - `…_of_degree_C11V2`：witness + `capTubeHasNeckChart` + `StageFiniteDegreeBound … N`（四分支含 round，
    树内 `canonicalBallConsumer_of_stage_degree`）。**P6 profile 不带 `N`**（`LongTime/` grep 0 命中），
    故 `N` 作显式前提；供给者 `uniformHistoryDegree_of_completed_freeFactorBound`。
  - `…_of_nonround_C11V2`：非 round（`requiresVolume`）+ chart，无需 `N`（`exists_ball_volume_of_…`）。
  - `…_of_BGAdapter_C11V2`：非 round + `Ric ≥ −2KQ g`（S-CH11-SMALLVOL G2 `BGAdapterC11V` 非 round 分支）。
* **§3 统一定理**（陈述按 KL 79.23 顺序 (a) surgery cap / (b) 曲率饱和 / (c) 到达上限）：
  `contact_volume_trichotomy_C11V2`（`R² ≤ t`）与加上时刻 0 接触 (d) 的
  `contact_volume_of_initial_or_trichotomy_C11V2`（`R² > t` 时用 `:2010`）。结论是目标半径 `q₀`
  （`P(p, t, q₀)` controlled）处的 `κ q₀³ ≤ Vol`，`κ` 只依赖 `(D, ε, C₁, C₂, N)` 与 (c) 的种子系数。
-/

set_option autoImplicit false
noncomputable section

open Set MeasureTheory
open DifferentialGeometry DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Tensor0SBundle
open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
open scoped Manifold ContDiff ENNReal

namespace GC.LongTime.Ch11

universe u

open private volume_lower_of_scaled_rm_bound from
  DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.FirstCurvatureContactVolumePortC11P
open private ObservedHistory.volume_lower_bound_of_smaller_controlled_radii
  from DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.HistoryBallVolume

/-! ## §1 (b) 曲率饱和接触：核心装配 -/

/-- 接触切片上：`w` 的 witness domain 包含 `B_v(y, σ/50)`（`d_v(y, w) ≤ σ/100`、`√Q σ ≤ 3`），且其上
`√|Rm|² ≤ 9 max(C₂, 1)/σ²`。 -/
theorem witness_ball_control_near_contact_C11V2 {P : OrientedThreeStage.{u}} {g : P.Metric}
    {w y : P.Carrier} {ε C1 C2 σ : ℝ} (V : SpatialCanonicalWitness g ε C1 C2 w) (hσ : 0 < σ)
    (hcurv : σ ^ 4 * normSq0S g w 4 (metricRm04At g w) ≤ 1)
    (hyw : riemannianEDistOf g y w ≤ ENNReal.ofReal (σ / 100)) :
    riemannianBallOf g w (σ / 100) ⊆ riemannianBallOf g y (σ / 50) ∧
    ∀ u ∈ riemannianBallOf g y (σ / 50),
      Real.sqrt (normSq0S g u 4 (metricRm04At g u)) ≤ 9 * max C2 1 / σ ^ 2 := by
  have hs : 0 < σ / 100 := by positivity
  have hwy : riemannianEDistOf g w y ≤ ENNReal.ofReal (σ / 100) := by
    rw [riemannianEDistOf_comm]
    exact hyw
  refine ⟨?_, ?_⟩
  · intro u hu
    change riemannianEDistOf g y u < ENNReal.ofReal (σ / 50)
    calc
      riemannianEDistOf g y u ≤ riemannianEDistOf g y w + riemannianEDistOf g w u :=
        riemannianEDistOf_triangle g y w u
      _ ≤ ENNReal.ofReal (σ / 100) + riemannianEDistOf g w u := add_le_add hyw le_rfl
      _ < ENNReal.ofReal (σ / 100) + ENNReal.ofReal (σ / 100) :=
        ENNReal.add_lt_add_left ENNReal.ofReal_ne_top hu
      _ = ENNReal.ofReal (σ / 50) := by
        rw [← ENNReal.ofReal_add hs.le hs.le]
        congr 1
        ring
  · have hQ := V.Q_pos
    have hsQ : 0 < Real.sqrt (metricScalarAt g w) := Real.sqrt_pos.mpr hQ
    have hthree := sqrt_scalarAt_mul_le_three_of_rm_le g w hcurv
    have hrad : 3 * σ / 100 ≤ V.radius := by
      refine le_trans ?_ V.radius_lower
      rw [inv_eq_one_div]
      apply (le_div_iff₀ hsQ).mpr
      nlinarith
    have hQσ : metricScalarAt g w ≤ 9 / σ ^ 2 := by
      apply (le_div_iff₀ (pow_pos hσ 2)).mpr
      have hh := (sq_le_sq₀ (mul_nonneg (Real.sqrt_nonneg _) hσ.le)
        (by norm_num : (0 : ℝ) ≤ 3)).mpr hthree
      rwa [mul_pow, Real.sq_sqrt hQ.le, show (3 : ℝ) ^ 2 = 9 by norm_num] at hh
    have hC2B : C2 ≤ max C2 1 := le_max_left _ _
    have hB : 0 ≤ max C2 1 := zero_le_one.trans (le_max_right _ _)
    intro u hu
    have hdom : u ∈ V.domain.carrier := by
      apply V.ball_inside
      apply riemannianBallOf_mono g w hrad
      change riemannianEDistOf g w u < ENNReal.ofReal (3 * σ / 100)
      calc
        riemannianEDistOf g w u ≤ riemannianEDistOf g w y + riemannianEDistOf g y u :=
          riemannianEDistOf_triangle g w y u
        _ ≤ ENNReal.ofReal (σ / 100) + riemannianEDistOf g y u := add_le_add hwy le_rfl
        _ < ENNReal.ofReal (σ / 100) + ENNReal.ofReal (σ / 50) :=
          ENNReal.add_lt_add_left ENNReal.ofReal_ne_top hu
        _ = ENNReal.ofReal (3 * σ / 100) := by
          rw [← ENNReal.ofReal_add hs.le (by positivity)]
          congr 1
          ring
    calc
      Real.sqrt (normSq0S g u 4 (metricRm04At g u)) ≤ C2 * metricScalarAt g w :=
        V.rm_bound u hdom
      _ ≤ max C2 1 * metricScalarAt g w := mul_le_mul_of_nonneg_right hC2B hQ.le
      _ ≤ max C2 1 * (9 / σ ^ 2) := mul_le_mul_of_nonneg_left hQσ hB
      _ = 9 * max C2 1 / σ ^ 2 := by ring

/-- 接触切片上的 BG（witness domain 内）：种子 `κ_w (σ/100)³ ≤ Vol_v B(w, σ/100)` ⇒ `π z` 处
`c₂ ρ³ ≤ Vol_v B(y, ρ)`（`ρ ≤ σ/50`），`c₂ = κ_w/100³ · e^{−14√B/50}/(8/50³)`，`B = max(C₂, 1)`。 -/
theorem volume_near_contact_of_witness_seed_C11V2 {P : OrientedThreeStage.{u}} {g : P.Metric}
    {w y : P.Carrier} {ε C1 C2 σ κw ρ : ℝ} (V : SpatialCanonicalWitness g ε C1 C2 w)
    (hσ : 0 < σ) (hcurv : σ ^ 4 * normSq0S g w 4 (metricRm04At g w) ≤ 1)
    (hyw : riemannianEDistOf g y w ≤ ENNReal.ofReal (σ / 100))
    (hseed : ENNReal.ofReal (κw * (σ / 100) ^ 3) ≤
      riemannianVolumeMeasure ThreeModel P.Carrier g (riemannianBallOf g w (σ / 100)))
    (hρ : 0 < ρ) (hρD : ρ ≤ σ / 50) :
    ENNReal.ofReal (κw / 100 ^ 3 * Real.exp (-(2 * (7 * Real.sqrt (max C2 1)) * (1 / 50))) /
        (8 * (1 / 50) ^ 3) * ρ ^ 3) ≤
      riemannianVolumeMeasure ThreeModel P.Carrier g (riemannianBallOf g y ρ) := by
  have hctrl := witness_ball_control_near_contact_C11V2 V hσ hcurv hyw
  have hB : 0 ≤ max C2 1 := zero_le_one.trans (le_max_right _ _)
  have hk : 9 * (9 * max C2 1) ≤ 2 * (7 * Real.sqrt (max C2 1)) ^ 2 := by
    rw [mul_pow, Real.sq_sqrt hB]
    nlinarith
  have hvolD : ENNReal.ofReal (κw / 100 ^ 3 * σ ^ 3) ≤
      riemannianVolumeMeasure ThreeModel P.Carrier g (riemannianBallOf g y (σ / 50)) := by
    have he : κw / 100 ^ 3 * σ ^ 3 = κw * (σ / 100) ^ 3 := by ring
    rw [he]
    exact hseed.trans (measure_mono hctrl.1)
  exact volume_lower_of_scaled_rm_bound g y (c := 7 * Real.sqrt (max C2 1)) (k := 9 * max C2 1)
    (α := 1 / 50) (by positivity) (by norm_num) hσ hρ hρD (le_of_eq (by ring)) hk hctrl.2 hvolD

/-- **(b) 核心装配**（KL 79.23 (b)）：曲率分支数据 + 接触点 `w = A.point v` 的 witness（任意 `ε C₁`，
比较常数 `C₂`）+ native 体积种子 `κ_w (σ/100)³ ≤ Vol_v B(w, σ/100)` ⇒ 所有 `0 < r ≤ σ` 有
`κ r³ ≤ Vol_t B(p, r)`；`κ` 只依赖 `κ_w` 与 `C₂`。前提形与三分类 `:712` 曲率分支的输出逐项对应
（`hcurv` 只需 `≤ 1`：接触等式只用于取 witness）。 -/
theorem terminal_volume_of_curvature_contact_seed_C11V2 (C2 κw : ℝ) (hκw : 0 < κw) :
    ∃ κ : ℝ, 0 < κ ∧
    ∀ (H : ObservedHistory.{u}) (t : Icc (0 : ℝ) H.horizon) (p : (H.stageAt t).Carrier)
      {σ : ℝ}, 0 < σ →
      (∀ q : ℝ, 0 < q → q < σ → H.isParabolicallyRmControlledBall t p q) →
      ∀ (a : Icc (0 : ℝ) H.horizon) (hat : a ≤ t), (a : ℝ) < (t : ℝ) - σ ^ 2 →
      (∀ x ∈ riemannianClosedBallOf (H.stageMetric (H.activeStage t) t) p σ,
        Nonempty (BackwardPointTrace H (H.activeStage a) (H.activeStage t)
          (H.activeStage_mono hat) x)) →
      ∀ x ∈ riemannianClosedBallOf (H.stageMetric (H.activeStage t) t) p σ,
      ∀ (A : BackwardPointTrace H (H.activeStage a) (H.activeStage t)
          (H.activeStage_mono hat) x)
        (v : Icc (0 : ℝ) H.horizon) (hav : a ≤ v) (hvt : v ≤ t), (t : ℝ) - σ ^ 2 ≤ v →
      σ ^ 4 * normSq0S (H.stageMetric (H.activeStage v) v)
          (A.point (H.activeStage v) (H.activeStage_mono hav) (H.activeStage_mono hvt)) 4
          (metricRm04At (H.stageMetric (H.activeStage v) v)
            (A.point (H.activeStage v) (H.activeStage_mono hav) (H.activeStage_mono hvt))) ≤ 1 →
      ∀ {ε C1 : ℝ}, SpatialCanonicalWitness (H.stageMetric (H.activeStage v) v) ε C1 C2
          (A.point (H.activeStage v) (H.activeStage_mono hav) (H.activeStage_mono hvt)) →
      ENNReal.ofReal (κw * (σ / 100) ^ 3) ≤
        riemannianVolumeMeasure ThreeModel (H.stageAt v).Carrier
          (H.stageMetric (H.activeStage v) v)
          (riemannianBallOf (H.stageMetric (H.activeStage v) v)
            (A.point (H.activeStage v) (H.activeStage_mono hav) (H.activeStage_mono hvt))
            (σ / 100)) →
      ∀ r : ℝ, 0 < r → r ≤ σ →
        ENNReal.ofReal κ * ENNReal.ofReal r ^ 3 ≤
          riemannianVolumeMeasure ThreeModel (H.stageAt t).Carrier
            (H.stageMetric (H.activeStage t) t)
            (riemannianBallOf (H.stageMetric (H.activeStage t) t) p r) := by
  set c₂ : ℝ := κw / 100 ^ 3 * Real.exp (-(2 * (7 * Real.sqrt (max C2 1)) * (1 / 50))) /
    (8 * (1 / 50) ^ 3) with hc₂
  set α₁ : ℝ := Real.exp (-9) * (Real.exp (-9) / 100) / 8 with hα₁
  set κ₀ : ℝ := Real.exp (-27) * c₂ * α₁ ^ 3 with hκ₀
  have hc₂pos : 0 < c₂ := by rw [hc₂]; positivity
  have hκ₀pos : 0 < κ₀ := by rw [hκ₀, hα₁]; positivity
  refine ⟨κ₀ / (8 * Real.exp 6), by positivity, ?_⟩
  intro H t p σ hσ hsmall a hat ha htrace x hx A v hav hvt hv hcurv ε C1 V hseed
  set r₀ : ℝ := Real.exp (-9) / 100 * σ with hr₀
  have hr₀pos : 0 < r₀ := by rw [hr₀]; positivity
  have he9 : Real.exp (-9) ≤ 1 := Real.exp_le_one_iff.mpr (by norm_num)
  have hr₀σ : r₀ ≤ σ := by
    rw [hr₀]
    nlinarith [Real.exp_pos (-9)]
  have hinward := H.exists_inward_point_with_earlier_volume_comparison a v t hav hvt p hσ
    hr₀pos hr₀σ ha hv hsmall htrace x hx
    (A.restrictFirst (H.activeStage_mono hav) (H.activeStage_mono hvt))
  obtain ⟨z, hz, hprotect, hdist, -, -, hvolT⟩ := hinward
  generalize hy : H.backwardSurvivorMap (H.activeStage v) (H.activeStage t)
    (H.activeStage_mono hvt) (H.activeStage v) le_rfl (H.activeStage_mono hvt) ⟨z, hz⟩ = y
    at hdist hvolT
  have hstep : Real.exp 9 * r₀ = σ / 100 := by
    rw [hr₀]
    have hh : Real.exp 9 * Real.exp (-9) = 1 := by rw [← Real.exp_add]; norm_num
    calc Real.exp 9 * (Real.exp (-9) / 100 * σ) = (Real.exp 9 * Real.exp (-9)) * σ / 100 := by
          ring
      _ = σ / 100 := by rw [hh]; ring
  have hyw : riemannianEDistOf (H.stageMetric (H.activeStage v) v) y
      (A.point (H.activeStage v) (H.activeStage_mono hav) (H.activeStage_mono hvt)) ≤
        ENNReal.ofReal (σ / 100) := by
    rw [← hstep]
    exact hdist
  have hρ₁ : 0 < Real.exp (-9) * r₀ / 8 := by positivity
  have hρ₁D : Real.exp (-9) * r₀ / 8 ≤ σ / 50 := by
    rw [hr₀]
    have h1 : Real.exp (-9) * (Real.exp (-9) / 100 * σ) ≤ 1 * (1 / 100 * σ) := by
      apply mul_le_mul he9 _ (by positivity) zero_le_one
      nlinarith
    nlinarith
  have hBG : ENNReal.ofReal (c₂ * (Real.exp (-9) * r₀ / 8) ^ 3) ≤
      riemannianVolumeMeasure ThreeModel (H.stageAt v).Carrier
        (H.stageMetric (H.activeStage v) v)
        (riemannianBallOf (H.stageMetric (H.activeStage v) v) y (Real.exp (-9) * r₀ / 8)) :=
    volume_near_contact_of_witness_seed_C11V2 V hσ hcurv hyw hseed hρ₁ hρ₁D
  have hsub : riemannianBallOf (H.stageMetric (H.activeStage t) t) z (r₀ / 2) ⊆
      riemannianBallOf (H.stageMetric (H.activeStage t) t) p σ := by
    intro u hu
    apply hprotect
    change riemannianEDistOf (H.stageMetric (H.activeStage t) t) z u ≤ ENNReal.ofReal (r₀ / 2)
    exact le_of_lt hu
  have hbound := (mul_le_mul' (le_refl (ENNReal.ofReal (Real.exp (-27)))) hBG).trans
    (hvolT.trans (measure_mono hsub))
  have hρα : Real.exp (-9) * r₀ / 8 = α₁ * σ := by rw [hr₀, hα₁]; ring
  have he : ENNReal.ofReal κ₀ * ENNReal.ofReal σ ^ 3 =
      ENNReal.ofReal (Real.exp (-27)) * ENNReal.ofReal (c₂ * (Real.exp (-9) * r₀ / 8) ^ 3) := by
    rw [← ENNReal.ofReal_pow hσ.le, ← ENNReal.ofReal_mul hκ₀pos.le,
      ← ENNReal.ofReal_mul (Real.exp_pos _).le, hρα, hκ₀]
    congr 1
    ring
  have hseedT := he ▸ hbound
  intro r hr hrσ
  exact ObservedHistory.volume_lower_bound_of_smaller_controlled_radii H t p hr hrσ hsmall hseedT

/-! ## §2 接触点 native 体积种子的来源 -/

/-- 种子尺度检查：`σ⁴|Rm(w)|² ≤ 1` ⇒ `(σ/100)⁴|Rm(w)|² ≤ 1`。 -/
theorem curvature_scale_hundredth_C11V2 {P : OrientedThreeStage.{u}} {g : P.Metric}
    {w : P.Carrier} {σ : ℝ} (hσ : 0 < σ)
    (hcurv : σ ^ 4 * normSq0S g w 4 (metricRm04At g w) ≤ 1) :
    (σ / 100) ^ 4 * normSq0S g w 4 (metricRm04At g w) ≤ 1 := by
  have hle : (σ / 100) ^ 4 ≤ σ ^ 4 := pow_le_pow_left₀ (by positivity) (by linarith) 4
  exact (mul_le_mul_of_nonneg_right hle (normSq0S_nonneg _ _ _ _)).trans hcurv

/-- **(b) + 度数界**（四分支含 round）：接触点 witness + `capTubeHasNeckChart` +
`StageFiniteDegreeBound (H.stage (activeStage v)) N`（树内 `canonicalBallConsumer_of_stage_degree`
给 native 种子）⇒ `κ r³ ≤ Vol_t B(p, r)`，`κ = κ(ε, C₁, C₂, N)`。 -/
theorem terminal_volume_of_curvature_contact_of_degree_C11V2 (ε C1 C2 : ℝ) (N : ℕ)
    (hN : 0 < N) :
    ∃ κ : ℝ, 0 < κ ∧
    ∀ (H : ObservedHistory.{u}) (t : Icc (0 : ℝ) H.horizon) (p : (H.stageAt t).Carrier)
      {σ : ℝ}, 0 < σ →
      (∀ q : ℝ, 0 < q → q < σ → H.isParabolicallyRmControlledBall t p q) →
      ∀ (a : Icc (0 : ℝ) H.horizon) (hat : a ≤ t), (a : ℝ) < (t : ℝ) - σ ^ 2 →
      (∀ x ∈ riemannianClosedBallOf (H.stageMetric (H.activeStage t) t) p σ,
        Nonempty (BackwardPointTrace H (H.activeStage a) (H.activeStage t)
          (H.activeStage_mono hat) x)) →
      ∀ x ∈ riemannianClosedBallOf (H.stageMetric (H.activeStage t) t) p σ,
      ∀ (A : BackwardPointTrace H (H.activeStage a) (H.activeStage t)
          (H.activeStage_mono hat) x)
        (v : Icc (0 : ℝ) H.horizon) (hav : a ≤ v) (hvt : v ≤ t), (t : ℝ) - σ ^ 2 ≤ v →
      σ ^ 4 * normSq0S (H.stageMetric (H.activeStage v) v)
          (A.point (H.activeStage v) (H.activeStage_mono hav) (H.activeStage_mono hvt)) 4
          (metricRm04At (H.stageMetric (H.activeStage v) v)
            (A.point (H.activeStage v) (H.activeStage_mono hav) (H.activeStage_mono hvt))) ≤ 1 →
      (∃ V : SpatialCanonicalWitness (H.stageMetric (H.activeStage v) v) ε C1 C2
          (A.point (H.activeStage v) (H.activeStage_mono hav) (H.activeStage_mono hvt)),
        V.capTubeHasNeckChart ε) →
      GC.GeneralFlow.StageFiniteDegreeBound (H.stage (H.activeStage v)) N →
      ∀ r : ℝ, 0 < r → r ≤ σ →
        ENNReal.ofReal κ * ENNReal.ofReal r ^ 3 ≤
          riemannianVolumeMeasure ThreeModel (H.stageAt t).Carrier
            (H.stageMetric (H.activeStage t) t)
            (riemannianBallOf (H.stageMetric (H.activeStage t) t) p r) := by
  obtain ⟨κN, hκN, hconsumer⟩ :=
    GC.GeneralFlow.canonicalBallConsumer_of_stage_degree.{u} ε C1 C2 N hN
  obtain ⟨κ, hκ, hcore⟩ := terminal_volume_of_curvature_contact_seed_C11V2.{u} C2 κN hκN
  refine ⟨κ, hκ, ?_⟩
  intro H t p σ hσ hsmall a hat ha htrace x hx A v hav hvt hv hcurv hcan hdeg
  obtain ⟨V, hV⟩ := hcan
  have hseed := hconsumer V hV hdeg (σ / 100) (by positivity)
    (curvature_scale_hundredth_C11V2 hσ hcurv)
  exact hcore H t p hσ hsmall a hat ha htrace x hx A v hav hvt hv hcurv V hseed

/-- **(b) 非 round**（无需 `N`）：接触点 witness 非 round（`requiresVolume`）+ chart
（树内 `exists_ball_volume_of_spatialCanonicalWitness`）⇒ `κ r³ ≤ Vol_t B(p, r)`。 -/
theorem terminal_volume_of_curvature_contact_of_nonround_C11V2 (ε C1 C2 : ℝ) :
    ∃ κ : ℝ, 0 < κ ∧
    ∀ (H : ObservedHistory.{u}) (t : Icc (0 : ℝ) H.horizon) (p : (H.stageAt t).Carrier)
      {σ : ℝ}, 0 < σ →
      (∀ q : ℝ, 0 < q → q < σ → H.isParabolicallyRmControlledBall t p q) →
      ∀ (a : Icc (0 : ℝ) H.horizon) (hat : a ≤ t), (a : ℝ) < (t : ℝ) - σ ^ 2 →
      (∀ x ∈ riemannianClosedBallOf (H.stageMetric (H.activeStage t) t) p σ,
        Nonempty (BackwardPointTrace H (H.activeStage a) (H.activeStage t)
          (H.activeStage_mono hat) x)) →
      ∀ x ∈ riemannianClosedBallOf (H.stageMetric (H.activeStage t) t) p σ,
      ∀ (A : BackwardPointTrace H (H.activeStage a) (H.activeStage t)
          (H.activeStage_mono hat) x)
        (v : Icc (0 : ℝ) H.horizon) (hav : a ≤ v) (hvt : v ≤ t), (t : ℝ) - σ ^ 2 ≤ v →
      σ ^ 4 * normSq0S (H.stageMetric (H.activeStage v) v)
          (A.point (H.activeStage v) (H.activeStage_mono hav) (H.activeStage_mono hvt)) 4
          (metricRm04At (H.stageMetric (H.activeStage v) v)
            (A.point (H.activeStage v) (H.activeStage_mono hav) (H.activeStage_mono hvt))) ≤ 1 →
      (∃ V : SpatialCanonicalWitness (H.stageMetric (H.activeStage v) v) ε C1 C2
          (A.point (H.activeStage v) (H.activeStage_mono hav) (H.activeStage_mono hvt)),
        V.capTubeHasNeckChart ε ∧ V.alternative.requiresVolume) →
      ∀ r : ℝ, 0 < r → r ≤ σ →
        ENNReal.ofReal κ * ENNReal.ofReal r ^ 3 ≤
          riemannianVolumeMeasure ThreeModel (H.stageAt t).Carrier
            (H.stageMetric (H.activeStage t) t)
            (riemannianBallOf (H.stageMetric (H.activeStage t) t) p r) := by
  obtain ⟨κw, hκw, hwit⟩ := exists_ball_volume_of_spatialCanonicalWitness.{u} ε C1 C2
  obtain ⟨κ, hκ, hcore⟩ := terminal_volume_of_curvature_contact_seed_C11V2.{u} C2 κw hκw
  refine ⟨κ, hκ, ?_⟩
  intro H t p σ hσ hsmall a hat ha htrace x hx A v hav hvt hv hcurv hcan
  obtain ⟨V, hV, hreq⟩ := hcan
  have hseed := hwit V hV hreq (σ / 100) (by positivity)
    (curvature_scale_hundredth_C11V2 hσ hcurv)
  exact hcore H t p hσ hsmall a hat ha htrace x hx A v hav hvt hv hcurv V hseed

/-- **(b) 经 BG 适配合同**（S-CH11-SMALLVOL G2 `vol_ball_ge_of_nonround_witness_C11V` 的非 round
分支）：非 round witness + `Ric ≥ −2KQ g` 于 `B_v(w, 2C₁/√Q)` ⇒ `κ r³ ≤ Vol_t B(p, r)`；
`κ = κ(C₁, C₂, K)`（`1 ≤ C₁`、`1 ≤ C₂` 只用于常数为正）。 -/
theorem terminal_volume_of_curvature_contact_of_BGAdapter_C11V2 (ε C1 C2 K : ℝ)
    (hC1 : 1 ≤ C1) (hC2 : 1 ≤ C2) (hK : 0 ≤ K) :
    ∃ κ : ℝ, 0 < κ ∧
    ∀ (H : ObservedHistory.{u}) (t : Icc (0 : ℝ) H.horizon) (p : (H.stageAt t).Carrier)
      {σ : ℝ}, 0 < σ →
      (∀ q : ℝ, 0 < q → q < σ → H.isParabolicallyRmControlledBall t p q) →
      ∀ (a : Icc (0 : ℝ) H.horizon) (hat : a ≤ t), (a : ℝ) < (t : ℝ) - σ ^ 2 →
      (∀ x ∈ riemannianClosedBallOf (H.stageMetric (H.activeStage t) t) p σ,
        Nonempty (BackwardPointTrace H (H.activeStage a) (H.activeStage t)
          (H.activeStage_mono hat) x)) →
      ∀ x ∈ riemannianClosedBallOf (H.stageMetric (H.activeStage t) t) p σ,
      ∀ (A : BackwardPointTrace H (H.activeStage a) (H.activeStage t)
          (H.activeStage_mono hat) x)
        (v : Icc (0 : ℝ) H.horizon) (hav : a ≤ v) (hvt : v ≤ t), (t : ℝ) - σ ^ 2 ≤ v →
      σ ^ 4 * normSq0S (H.stageMetric (H.activeStage v) v)
          (A.point (H.activeStage v) (H.activeStage_mono hav) (H.activeStage_mono hvt)) 4
          (metricRm04At (H.stageMetric (H.activeStage v) v)
            (A.point (H.activeStage v) (H.activeStage_mono hav) (H.activeStage_mono hvt))) ≤ 1 →
      ∀ V : SpatialCanonicalWitness (H.stageMetric (H.activeStage v) v) ε C1 C2
          (A.point (H.activeStage v) (H.activeStage_mono hav) (H.activeStage_mono hvt)),
      V.alternative.requiresVolume →
      (∀ y ∈ riemannianBallOf (H.stageMetric (H.activeStage v) v)
          (A.point (H.activeStage v) (H.activeStage_mono hav) (H.activeStage_mono hvt))
          (2 * C1 / Real.sqrt (metricScalarAt (H.stageMetric (H.activeStage v) v)
            (A.point (H.activeStage v) (H.activeStage_mono hav) (H.activeStage_mono hvt)))),
        ∀ X : TangentSpace ThreeModel y,
          -(2 * K * metricScalarAt (H.stageMetric (H.activeStage v) v)
            (A.point (H.activeStage v) (H.activeStage_mono hav) (H.activeStage_mono hvt))) *
              (H.stageMetric (H.activeStage v) v).inner y X X ≤
            ricciTensor (I := ThreeModel) (H.stageMetric (H.activeStage v) v) y X X) →
      ∀ r : ℝ, 0 < r → r ≤ σ →
        ENNReal.ofReal κ * ENNReal.ofReal r ^ 3 ≤
          riemannianVolumeMeasure ThreeModel (H.stageAt t).Carrier
            (H.stageMetric (H.activeStage t) t)
            (riemannianBallOf (H.stageMetric (H.activeStage t) t) p r) := by
  have hκw : 0 < Real.exp (-(4 * C1 * Real.sqrt K)) / (64 * C1 ^ 3 * C2) := by
    have : 0 < C1 := by linarith
    have : 0 < C2 := by linarith
    positivity
  obtain ⟨κ, hκ, hcore⟩ := terminal_volume_of_curvature_contact_seed_C11V2.{u} C2 _ hκw
  refine ⟨κ, hκ, ?_⟩
  intro H t p σ hσ hsmall a hat ha htrace x hx A v hav hvt hv hcurv V hnr hRic
  have hsQ : 0 < Real.sqrt (metricScalarAt (H.stageMetric (H.activeStage v) v)
      (A.point (H.activeStage v) (H.activeStage_mono hav) (H.activeStage_mono hvt))) :=
    Real.sqrt_pos.mpr V.Q_pos
  have hthree := sqrt_scalarAt_mul_le_three_of_rm_le _ _ hcurv
  have hρQ : σ / 100 ≤ (Real.sqrt (metricScalarAt (H.stageMetric (H.activeStage v) v)
      (A.point (H.activeStage v) (H.activeStage_mono hav) (H.activeStage_mono hvt))))⁻¹ := by
    rw [inv_eq_one_div]
    apply (le_div_iff₀ hsQ).mpr
    nlinarith
  have hseed := vol_ball_ge_of_nonround_witness_C11V V hnr hK hRic (by positivity) hρQ
  exact hcore H t p hσ hsmall a hat ha htrace x hx A v hav hvt hv hcurv V hseed

/-! ## §3 接触体积统一定理（KL 79.23 顺序：(a) surgery cap / (b) 曲率饱和 / (c) 到达上限） -/

section Unified

open DifferentialGeometry.PDE.RicciFlow

/-- **统一核心**：三分类 `:712` 在 `[q₀, R]`（`q₀ < R`、`R² ≤ t`）上的 first contact `σ`，三种情形各给目标
半径 `q₀` 的体积：
* (a) **surgery cap**（`:1775`）：`t − R² ≤ T_{i+1} ≤ t` 的 event 都带 `η ≤ ε₀`、`m ≥ 2`、有 canonical
  window 的 presented static cap（显式前提 `hcapS`；profile 的 `(records i).static b` 接线待核）；
* (b) **曲率饱和**（§2 `…_of_degree_C11V2`）：`[t − s², t]` 内曲率水平 `s⁻²`（`s < R`）的点有带
  chart 的 canonical witness（显式 `hcan`）+ 各 stage 的 `StageFiniteDegreeBound … N`（显式 `hdeg`）；
* (c) **到达上限**：抽象成 `htop`（`R` 以下全 controlled ⇒ `κ_T q₀³ ≤ Vol`），由下面两个定理分别用
  种子（79.21 + BG）与时刻 0（`:2010`）供给。
结论 `min(κ, κ_T) q₀³ ≤ Vol_t B(p, q₀)`，`κ = κ(D, ε, C₁, C₂, N)`。 -/
theorem contact_volume_of_top_C11V2 (D : ℝ) (hD : 4 * StandardCap.transitionEnd + 6 ≤ D)
    (ε C1 C2 : ℝ) (N : ℕ) (hN : 0 < N) :
    ∃ ε₀ κ : ℝ, 0 < ε₀ ∧ 0 < κ ∧
    ∀ (H : ObservedHistory.{u}) (t : Icc (0 : ℝ) H.horizon) (p : (H.stageAt t).Carrier)
      {q₀ R : ℝ}, H.isParabolicallyRmControlledBall t p q₀ → q₀ < R → R ^ 2 ≤ (t : ℝ) →
      (∀ i : Fin H.eventCount, (t : ℝ) - R ^ 2 < H.time i.succ → H.time i.succ ≤ t →
        (H.event i).old = (H.event i).transition.trace.retainedCore) →
      (∀ (i : Fin H.eventCount) (b : (H.event i).RetainedBoundaryIndex),
        (t : ℝ) - R ^ 2 ≤ H.time i.succ → H.time i.succ ≤ t →
        ∃ (fixed : StaticCapScaffold) (m : ℕ) (η : ℝ)
          (S : (H.event i).PresentedStaticCap fixed D m η b),
          η ≤ ε₀ ∧ 2 ≤ m ∧ S.hasCanonicalWindow) →
      (∀ v : Icc (0 : ℝ) H.horizon, v ≤ t → ∀ (w : (H.stageAt v).Carrier) (s : ℝ),
        0 < s → s < R → (t : ℝ) - s ^ 2 ≤ v →
        s ^ 4 * normSq0S (H.stageMetric (H.activeStage v) v) w 4
          (metricRm04At (H.stageMetric (H.activeStage v) v) w) = 1 →
        ∃ V : SpatialCanonicalWitness (H.stageMetric (H.activeStage v) v) ε C1 C2 w,
          V.capTubeHasNeckChart ε) →
      (∀ j, GC.GeneralFlow.StageFiniteDegreeBound (H.stage j) N) →
      ∀ {κT : ℝ},
      ((∀ q : ℝ, 0 < q → q < R → H.isParabolicallyRmControlledBall t p q) →
        ENNReal.ofReal κT * ENNReal.ofReal q₀ ^ 3 ≤
          riemannianVolumeMeasure ThreeModel (H.stageAt t).Carrier
            (H.stageMetric (H.activeStage t) t)
            (riemannianBallOf (H.stageMetric (H.activeStage t) t) p q₀)) →
      ENNReal.ofReal (min κ κT) * ENNReal.ofReal q₀ ^ 3 ≤
        riemannianVolumeMeasure ThreeModel (H.stageAt t).Carrier
          (H.stageMetric (H.activeStage t) t)
          (riemannianBallOf (H.stageMetric (H.activeStage t) t) p q₀) := by
  obtain ⟨ε₀, κcap, hε₀, -, hκcap, hcapVol⟩ :=
    ObservedHistory.exists_uniform_terminal_ball_volume_lower_of_cap_contact D hD
  obtain ⟨κcurv, hκcurv, hcurvVol⟩ :=
    terminal_volume_of_curvature_contact_of_degree_C11V2.{u} ε C1 C2 N hN
  refine ⟨ε₀, min κcap κcurv, hε₀, lt_min hκcap hκcurv, ?_⟩
  intro H t p q₀ R hq₀ hq₀R hRt hOld hcapS hcan hdeg κT htop
  have hq₀pos : 0 < q₀ := hq₀.1
  have htri := H.csSup_parabolicallyRmControlledBall_eq_or_cap_or_curvature_eq t p hq₀ hq₀R.le
    hRt hOld
  obtain ⟨hσmem, hcases⟩ := htri
  set σ := sSup {r ∈ Icc q₀ R | H.isParabolicallyRmControlledBall t p r} with hσdef
  have hσpos : 0 < σ := hq₀pos.trans_le hσmem.1
  have hsmallσ : ∀ q : ℝ, 0 < q → q < σ → H.isParabolicallyRmControlledBall t p q :=
    fun q hq hqσ => H.isParabolicallyRmControlledBall_of_lt_csSup hq₀ hq₀R.le hq hqσ
  by_cases hσR : σ = R
  · -- (c) 到达上限
    have hall : ∀ q : ℝ, 0 < q → q < R → H.isParabolicallyRmControlledBall t p q := by
      intro q hq hqR
      exact hsmallσ q hq (hσR ▸ hqR)
    exact (mul_le_mul' (ENNReal.ofReal_le_ofReal (min_le_right _ _)) le_rfl).trans (htop hall)
  have hσR' : σ < R := lt_of_le_of_ne hσmem.2 hσR
  rcases hcases with htop' | hcapc | hcurvc
  · exact (hσR htop').elim
  · -- (a) surgery cap
    obtain ⟨x, hx, i, hl, A, b, z, hbirth, hkt, -, hpres, -⟩ := hcapc
    have hσ2 : σ ^ 2 ≤ R ^ 2 := pow_le_pow_left₀ hσpos.le hσmem.2 2
    have hcapData := hcapS i b (by linarith) hkt
    obtain ⟨fixed, m, η, S, hη, hm, hwin⟩ := hcapData
    have hvol := hcapVol H t p hσpos hsmallσ i hl x hx A hbirth hkt hη hm S hwin z hpres q₀
      hq₀pos hσmem.1
    refine (mul_le_mul' (ENNReal.ofReal_le_ofReal ?_) le_rfl).trans hvol
    exact (min_le_left _ _).trans (min_le_left _ _)
  · -- (b) 曲率饱和
    obtain ⟨a, hat, ha, htrace, x, hx, A, v, hav, hvt, hv, hcont⟩ := hcurvc
    have hwit := hcan v hvt _ σ hσpos hσR' hv hcont
    have hvol := hcurvVol H t p hσpos hsmallσ a hat ha htrace x hx A v hav hvt hv hcont.le hwit
      (hdeg _) q₀ hq₀pos hσmem.1
    refine (mul_le_mul' (ENNReal.ofReal_le_ofReal ?_) le_rfl).trans hvol
    exact (min_le_left _ _).trans (min_le_right _ _)

/-- (c) 的种子形：`θR ≤ q < R` 的 controlled 球有 `κ_R q³ ≤ Vol`（KL (79.21)；G2 由 wide window 或
种子球包含供给）⇒ `R` 以下全 controlled 时 `κ_R/(8e⁶) q₀³ ≤ Vol`（`θ < 1`；`θR > q₀` 时用 history BG
从 `θR` 降到 `q₀`）。 -/
theorem top_volume_of_seed_C11V2 (H : ObservedHistory.{u}) (t : Icc (0 : ℝ) H.horizon)
    (p : (H.stageAt t).Carrier) {q₀ R θ κR : ℝ} (hq₀ : 0 < q₀) (hq₀R : q₀ < R) (hθ : θ < 1)
    (hκR : 0 ≤ κR)
    (hseed : ∀ q : ℝ, θ * R ≤ q → q < R → H.isParabolicallyRmControlledBall t p q →
      ENNReal.ofReal κR * ENNReal.ofReal q ^ 3 ≤
        riemannianVolumeMeasure ThreeModel (H.stageAt t).Carrier
          (H.stageMetric (H.activeStage t) t)
          (riemannianBallOf (H.stageMetric (H.activeStage t) t) p q))
    (hall : ∀ q : ℝ, 0 < q → q < R → H.isParabolicallyRmControlledBall t p q) :
    ENNReal.ofReal (κR / (8 * Real.exp 6)) * ENNReal.ofReal q₀ ^ 3 ≤
      riemannianVolumeMeasure ThreeModel (H.stageAt t).Carrier
        (H.stageMetric (H.activeStage t) t)
        (riemannianBallOf (H.stageMetric (H.activeStage t) t) p q₀) := by
  have hR : 0 < R := hq₀.trans hq₀R
  by_cases hθq : θ * R ≤ q₀
  · have h := hseed q₀ hθq hq₀R (hall q₀ hq₀ hq₀R)
    refine (mul_le_mul' (ENNReal.ofReal_le_ofReal ?_) le_rfl).trans h
    have he : 1 ≤ 8 * Real.exp 6 := by
      have := Real.one_le_exp (by norm_num : (0 : ℝ) ≤ 6)
      linarith
    exact div_le_self hκR he
  · have hlt : q₀ < θ * R := lt_of_not_ge hθq
    have hθpos : 0 < θ * R := hq₀.trans hlt
    have hθR : θ * R < R := by nlinarith
    have hs := hseed (θ * R) le_rfl hθR (hall _ hθpos hθR)
    exact ObservedHistory.volume_lower_bound_of_smaller_controlled_radii H t p hq₀ hlt.le
      (fun q hq hqθ => hall q hq (hqθ.trans hθR)) hs

/-- **接触体积统一定理（KL 79.23 (a)(b)(c)）**：`R² ≤ t`，(c) 由种子形 `hseed` 供给。 -/
theorem contact_volume_trichotomy_C11V2 (D : ℝ) (hD : 4 * StandardCap.transitionEnd + 6 ≤ D)
    (ε C1 C2 : ℝ) (N : ℕ) (hN : 0 < N) :
    ∃ ε₀ κ : ℝ, 0 < ε₀ ∧ 0 < κ ∧
    ∀ (H : ObservedHistory.{u}) (t : Icc (0 : ℝ) H.horizon) (p : (H.stageAt t).Carrier)
      {q₀ R : ℝ}, H.isParabolicallyRmControlledBall t p q₀ → q₀ < R → R ^ 2 ≤ (t : ℝ) →
      (∀ i : Fin H.eventCount, (t : ℝ) - R ^ 2 < H.time i.succ → H.time i.succ ≤ t →
        (H.event i).old = (H.event i).transition.trace.retainedCore) →
      (∀ (i : Fin H.eventCount) (b : (H.event i).RetainedBoundaryIndex),
        (t : ℝ) - R ^ 2 ≤ H.time i.succ → H.time i.succ ≤ t →
        ∃ (fixed : StaticCapScaffold) (m : ℕ) (η : ℝ)
          (S : (H.event i).PresentedStaticCap fixed D m η b),
          η ≤ ε₀ ∧ 2 ≤ m ∧ S.hasCanonicalWindow) →
      (∀ v : Icc (0 : ℝ) H.horizon, v ≤ t → ∀ (w : (H.stageAt v).Carrier) (s : ℝ),
        0 < s → s < R → (t : ℝ) - s ^ 2 ≤ v →
        s ^ 4 * normSq0S (H.stageMetric (H.activeStage v) v) w 4
          (metricRm04At (H.stageMetric (H.activeStage v) v) w) = 1 →
        ∃ V : SpatialCanonicalWitness (H.stageMetric (H.activeStage v) v) ε C1 C2 w,
          V.capTubeHasNeckChart ε) →
      (∀ j, GC.GeneralFlow.StageFiniteDegreeBound (H.stage j) N) →
      ∀ {θ κR : ℝ}, θ < 1 → 0 ≤ κR →
      (∀ q : ℝ, θ * R ≤ q → q < R → H.isParabolicallyRmControlledBall t p q →
        ENNReal.ofReal κR * ENNReal.ofReal q ^ 3 ≤
          riemannianVolumeMeasure ThreeModel (H.stageAt t).Carrier
            (H.stageMetric (H.activeStage t) t)
            (riemannianBallOf (H.stageMetric (H.activeStage t) t) p q)) →
      ENNReal.ofReal (min κ (κR / (8 * Real.exp 6))) * ENNReal.ofReal q₀ ^ 3 ≤
        riemannianVolumeMeasure ThreeModel (H.stageAt t).Carrier
          (H.stageMetric (H.activeStage t) t)
          (riemannianBallOf (H.stageMetric (H.activeStage t) t) p q₀) := by
  obtain ⟨ε₀, κ, hε₀, hκ, hcore⟩ := contact_volume_of_top_C11V2.{u} D hD ε C1 C2 N hN
  refine ⟨ε₀, κ, hε₀, hκ, ?_⟩
  intro H t p q₀ R hq₀ hq₀R hRt hOld hcapS hcan hdeg θ κR hθ hκR hseed
  exact hcore H t p hq₀ hq₀R hRt hOld hcapS hcan hdeg
    (top_volume_of_seed_C11V2 H t p hq₀.1 hq₀R hθ hκR hseed)

/-- **加上 (d) 时刻 0 接触**（`:2010`）：去掉 `R² ≤ t`，改要 `InitialIdentification P g H` 与
`R ≤ ρ₀`（`ρ₀` 来自初始度量的一致小球体积）。`R² > t` 时上限 `√t` 处的 first contact 是时刻 0 接触。 -/
theorem contact_volume_of_initial_or_trichotomy_C11V2 (P : OrientedThreeStage.{u}) (g : P.Metric)
    (D : ℝ) (hD : 4 * StandardCap.transitionEnd + 6 ≤ D) (ε C1 C2 : ℝ) (N : ℕ) (hN : 0 < N) :
    ∃ ε₀ ρ₀ κ : ℝ, 0 < ε₀ ∧ 0 < ρ₀ ∧ 0 < κ ∧
    ∀ (H : ObservedHistory.{u}), InitialIdentification P g H →
    ∀ (t : Icc (0 : ℝ) H.horizon) (p : (H.stageAt t).Carrier)
      {q₀ R : ℝ}, H.isParabolicallyRmControlledBall t p q₀ → q₀ < R → R ≤ ρ₀ →
      (∀ i : Fin H.eventCount, (t : ℝ) - R ^ 2 < H.time i.succ → H.time i.succ ≤ t →
        (H.event i).old = (H.event i).transition.trace.retainedCore) →
      (∀ (i : Fin H.eventCount) (b : (H.event i).RetainedBoundaryIndex),
        (t : ℝ) - R ^ 2 ≤ H.time i.succ → H.time i.succ ≤ t →
        ∃ (fixed : StaticCapScaffold) (m : ℕ) (η : ℝ)
          (S : (H.event i).PresentedStaticCap fixed D m η b),
          η ≤ ε₀ ∧ 2 ≤ m ∧ S.hasCanonicalWindow) →
      (∀ v : Icc (0 : ℝ) H.horizon, v ≤ t → ∀ (w : (H.stageAt v).Carrier) (s : ℝ),
        0 < s → s < R → (t : ℝ) - s ^ 2 ≤ v →
        s ^ 4 * normSq0S (H.stageMetric (H.activeStage v) v) w 4
          (metricRm04At (H.stageMetric (H.activeStage v) v) w) = 1 →
        ∃ V : SpatialCanonicalWitness (H.stageMetric (H.activeStage v) v) ε C1 C2 w,
          V.capTubeHasNeckChart ε) →
      (∀ j, GC.GeneralFlow.StageFiniteDegreeBound (H.stage j) N) →
      ∀ {θ κR : ℝ}, θ < 1 → 0 ≤ κR →
      (∀ q : ℝ, θ * R ≤ q → q < R → H.isParabolicallyRmControlledBall t p q →
        ENNReal.ofReal κR * ENNReal.ofReal q ^ 3 ≤
          riemannianVolumeMeasure ThreeModel (H.stageAt t).Carrier
            (H.stageMetric (H.activeStage t) t)
            (riemannianBallOf (H.stageMetric (H.activeStage t) t) p q)) →
      ENNReal.ofReal (min κ (κR / (8 * Real.exp 6))) * ENNReal.ofReal q₀ ^ 3 ≤
        riemannianVolumeMeasure ThreeModel (H.stageAt t).Carrier
          (H.stageMetric (H.activeStage t) t)
          (riemannianBallOf (H.stageMetric (H.activeStage t) t) p q₀) := by
  obtain ⟨ε₀, κ, hε₀, hκ, hcore⟩ := contact_volume_of_top_C11V2.{u} D hD ε C1 C2 N hN
  obtain ⟨ρ₀, κ₀, hρ₀, hκ₀, hinit⟩ :=
    ObservedHistory.exists_uniform_terminal_ball_volume_lower_of_initial_time_contact P g
  refine ⟨ε₀, ρ₀, min κ κ₀, hε₀, hρ₀, lt_min hκ hκ₀, ?_⟩
  intro H hI t p q₀ R hq₀ hq₀R hRρ hOld hcapS hcan hdeg θ κR hθ hκR hseed
  have hq₀pos : 0 < q₀ := hq₀.1
  have hq₀t : q₀ ^ 2 ≤ (t : ℝ) := hq₀.radius_sq_le_time H
  have ht0 : 0 ≤ (t : ℝ) := t.property.1
  have hmono : ENNReal.ofReal (min (min κ κ₀) (κR / (8 * Real.exp 6))) ≤
      ENNReal.ofReal (min κ (κR / (8 * Real.exp 6))) :=
    ENNReal.ofReal_le_ofReal (min_le_min_right _ (min_le_left _ _))
  have hinitial : ∀ {σ : ℝ}, 0 < σ → σ ≤ ρ₀ → (t : ℝ) = σ ^ 2 → q₀ ≤ σ →
      (∀ q : ℝ, 0 < q → q < σ → H.isParabolicallyRmControlledBall t p q) →
      ENNReal.ofReal (min (min κ κ₀) (κR / (8 * Real.exp 6))) * ENNReal.ofReal q₀ ^ 3 ≤
        riemannianVolumeMeasure ThreeModel (H.stageAt t).Carrier
          (H.stageMetric (H.activeStage t) t)
          (riemannianBallOf (H.stageMetric (H.activeStage t) t) p q₀) := by
    intro σ hσ hσρ htime hq₀σ hall
    refine (mul_le_mul' (ENNReal.ofReal_le_ofReal ?_) le_rfl).trans
      (hinit H hI t p hσ hσρ htime hall q₀ hq₀pos hq₀σ)
    exact (min_le_left _ _).trans (min_le_right _ _)
  rcases lt_or_ge (R ^ 2) (t : ℝ) with hRt | hRt
  · exact (mul_le_mul' hmono le_rfl).trans
      (hcore H t p hq₀ hq₀R hRt.le hOld hcapS hcan hdeg
        (top_volume_of_seed_C11V2 H t p hq₀pos hq₀R hθ hκR hseed))
  · -- `R² ≥ t`：上限取 `√t`
    set R' := Real.sqrt (t : ℝ) with hR'
    have hR'sq : R' ^ 2 = (t : ℝ) := Real.sq_sqrt ht0
    have hR'R : R' ≤ R := by
      rw [hR']
      exact Real.sqrt_le_iff.mpr ⟨(hq₀pos.trans hq₀R).le, hRt⟩
    have hq₀R' : q₀ ≤ R' := Real.le_sqrt_of_sq_le hq₀t
    have hR'pos : 0 < R' := hq₀pos.trans_le hq₀R'
    rcases lt_or_eq_of_le hq₀R' with hlt | heq
    · have hsq : R ^ 2 ≥ R' ^ 2 := pow_le_pow_left₀ hR'pos.le hR'R 2
      have htop' : (∀ q : ℝ, 0 < q → q < R' → H.isParabolicallyRmControlledBall t p q) →
          ENNReal.ofReal κ₀ * ENNReal.ofReal q₀ ^ 3 ≤
            riemannianVolumeMeasure ThreeModel (H.stageAt t).Carrier
              (H.stageMetric (H.activeStage t) t)
              (riemannianBallOf (H.stageMetric (H.activeStage t) t) p q₀) := fun hall =>
        hinit H hI t p hR'pos (hR'R.trans hRρ) hR'sq.symm hall q₀ hq₀pos hlt.le
      have hOld' : ∀ i : Fin H.eventCount, (t : ℝ) - R' ^ 2 < H.time i.succ →
          H.time i.succ ≤ t → (H.event i).old = (H.event i).transition.trace.retainedCore :=
        fun i hi hit => hOld i (by linarith) hit
      have h := hcore H t p hq₀ hlt hR'sq.le hOld'
        (fun i b hi hit => hcapS i b (by linarith) hit)
        (fun v hvt w s hs hsR => hcan v hvt w s hs (hsR.trans_le hR'R)) hdeg htop'
      refine (mul_le_mul' (ENNReal.ofReal_le_ofReal ?_) le_rfl).trans h
      exact min_le_left _ _
    · refine (mul_le_mul' (ENNReal.ofReal_le_ofReal ?_) le_rfl).trans
        (hinit H hI t p hq₀pos (hq₀R.le.trans hRρ) (by rw [heq, hR'sq])
          (fun q hq hqq => hq₀.mono_radius H hq hqq.le) q₀ hq₀pos le_rfl)
      exact (min_le_left _ _).trans (min_le_right _ _)


/-- `ENNReal` 形转换：`ofReal κ · ofReal q ³ = ofReal (κ q³)`（`q ≥ 0`，`κ` 不限符号）。 -/
theorem ofReal_mul_ofReal_cube_C11V2 (κ : ℝ) {q : ℝ} (hq : 0 ≤ q) :
    ENNReal.ofReal κ * ENNReal.ofReal q ^ 3 = ENNReal.ofReal (κ * q ^ 3) := by
  rw [ENNReal.ofReal_mul' (pow_nonneg hq 3), ENNReal.ofReal_pow hq]

end Unified

/-- consumer（P6B `ballVolume` 形）：统一定理 + (c) 种子形 ⇒ 目标半径 `q₀` 处
`∃ κ' > 0, κ' q₀³ ≤ ballVolume`；`κ'` 只依赖常数与种子系数（不依赖 `H, t, p, q₀, R`）。 -/
example (D : ℝ) (hD : 4 * DifferentialGeometry.PDE.RicciFlow.StandardCap.transitionEnd + 6 ≤ D)
    (ε C1 C2 : ℝ) (N : ℕ) (hN : 0 < N) (κR : ℝ) (hκR : 0 < κR) :
    ∃ ε₀ κ' : ℝ, 0 < ε₀ ∧ 0 < κ' ∧
    ∀ (H : ObservedHistory.{u}) (t : Icc (0 : ℝ) H.horizon) (p : (H.stageAt t).Carrier)
      {q₀ R : ℝ}, H.isParabolicallyRmControlledBall t p q₀ → q₀ < R → R ^ 2 ≤ (t : ℝ) →
      (∀ i : Fin H.eventCount, (t : ℝ) - R ^ 2 < H.time i.succ → H.time i.succ ≤ t →
        (H.event i).old = (H.event i).transition.trace.retainedCore) →
      (∀ (i : Fin H.eventCount) (b : (H.event i).RetainedBoundaryIndex),
        (t : ℝ) - R ^ 2 ≤ H.time i.succ → H.time i.succ ≤ t →
        ∃ (fixed : StaticCapScaffold) (m : ℕ) (η : ℝ)
          (S : (H.event i).PresentedStaticCap fixed D m η b),
          η ≤ ε₀ ∧ 2 ≤ m ∧ S.hasCanonicalWindow) →
      (∀ v : Icc (0 : ℝ) H.horizon, v ≤ t → ∀ (w : (H.stageAt v).Carrier) (s : ℝ),
        0 < s → s < R → (t : ℝ) - s ^ 2 ≤ v →
        s ^ 4 * normSq0S (H.stageMetric (H.activeStage v) v) w 4
          (metricRm04At (H.stageMetric (H.activeStage v) v) w) = 1 →
        ∃ V : SpatialCanonicalWitness (H.stageMetric (H.activeStage v) v) ε C1 C2 w,
          V.capTubeHasNeckChart ε) →
      (∀ j, GC.GeneralFlow.StageFiniteDegreeBound (H.stage j) N) →
      (∀ q : ℝ, R / 2 ≤ q → q < R → H.isParabolicallyRmControlledBall t p q →
        ENNReal.ofReal (κR * q ^ 3) ≤
          Geometry.Collapse.ballVolume (H.stageMetric (H.activeStage t) t) p q) →
      ENNReal.ofReal (κ' * q₀ ^ 3) ≤
        Geometry.Collapse.ballVolume (H.stageMetric (H.activeStage t) t) p q₀ := by
  obtain ⟨ε₀, κ, hε₀, hκ, hU⟩ := contact_volume_trichotomy_C11V2.{u} D hD ε C1 C2 N hN
  refine ⟨ε₀, min κ (κR / (8 * Real.exp 6)), hε₀, lt_min hκ (by positivity), ?_⟩
  intro H t p q₀ R hq₀ hq₀R hRt hOld hcapS hcan hdeg hseed
  have h := hU H t p hq₀ hq₀R hRt hOld hcapS hcan hdeg (θ := 1 / 2) (by norm_num) hκR.le
    (fun q hq hqR hc => by
      rw [ofReal_mul_ofReal_cube_C11V2 κR hc.1.le]
      exact hseed q (by linarith) hqR hc)
  rw [ofReal_mul_ofReal_cube_C11V2 _ hq₀.1.le] at h
  exact h

end GC.LongTime.Ch11
