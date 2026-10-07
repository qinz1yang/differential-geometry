import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.SmallVol.CurvatureContactVolumeC11V2
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.SmallVol.WindowGlueC11V
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.P6SeedShiftP6B

/-!
# O-CH11-SMALLVOL2 G2：`hsmall` 装配（V4）+ 端到端 consumer（后缀 `_C11V2`）

S-CH11-SMALLVOL G3 的 `localKappaWindow_zero_of_window_and_small_C11V`（`SmallVol/WindowGlueC11V`）把
`tracedKappa_of_window_P6B` 的 `nr := 0` 消费点拆成真实 `nr` 的 window + 显式 `hsmall`
（`ρ' < nr v/100`、`ρ' < r/100` 的 controlled 测试球）。本文件由 G1 的接触体积统一定理
`contact_volume_trichotomy_C11V2` **生产** `hsmall`：在测试点 `(v, x)` 上取 `q₀ := ρ'`、
`R := min(nr v/50, (A+1) r)`：

* (c) 到达上限：`R = nr v/50` 时种子取自 **wide window**（O1 = 放宽，lead 02:3x：KAPPA
  `LocalKappaWideAt_C11Q` 经 seed shift 后 window 上沿 `(A+1) r`，`[nr v/100, (A+1) r]`）；
  `R = (A+1) r < nr v/50` 时 `B_v(x, q) ⊇ B_v(O_v, r/100)`（`q ≥ (A + 1/100) r`），种子取 seed shift
  `earlier_seed_on_half_depth_P6B` 的体积——**不需要 window**，故 `nr v ≥ 100(A+1) r` 也闭合；
* (a) cap 接触 / (b) 曲率饱和：G1（显式 `hcapS`、`hcan`、`hdeg`）。
O1 旧形（window 上沿 `r/100`）下 `r ≤ nr < (A+1)r/c` 无来源；wide window 下不再需要列显式前提。
新增的唯一"尺度"前提是 `nr ≤ M`（neck radius 有界），只用于取 `T` 使 `R² ≤ v`（三分类 `:712` 的
`R² ≤ t`）。

wide window 以**展开形**作前提（与 `LocalKappaWindowAt_P6B` 逐字同形，只把 `ρ' < r/100` 换成
`ρ' ≤ (A+1) r`），不新建具名 Prop；它蕴含 P6B window（`window_of_wide_window_C11V2`），并由 wide late 形
（`LocalKappaLateAt_P6B` 上沿换 `L r`，`L = 100(A+1)`）经 seed shift 得到（`wideWindow_of_wideLate_C11V2`）。
口径（lead 02:5x）：K 链**不**给 `nr = 0`（基点在新鲜手术帽上时作用量无一致下界），`ρ < nr(v)/100` 的
测试球归本文件（first-contact 三分类 + 接触体积）。
`hcan` 的形：`v' ∈ [v − s², v]` 上曲率水平 `s⁻²`（`s < nr v/50`）的点有带 chart 的 witness——
由通常的 CNA（"`|Rm| ≥ (nr v'/50)⁻²` ⇒ canonical"）加 `nr` 单调不增推出（D-12：native canonical，
不挂 P6 canonical 下游）。
-/

set_option autoImplicit false
noncomputable section

open Set MeasureTheory
open DifferentialGeometry DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Tensor0SBundle
open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Geometry.Collapse
open DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn
open DifferentialGeometry.PDE.RicciFlow DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
open scoped Manifold ContDiff ENNReal

namespace GC.LongTime.Ch11

universe u

/-- (c) 的种子比例 `θ = max(1/2, (A + 1/100)/(A + 1)) < 1`。 -/
theorem seedRatio_lt_one_C11V2 {A : ℝ} (hA : 0 < A) :
    max (1 / 2) ((A + 1 / 100) / (A + 1)) < 1 := by
  refine max_lt (by norm_num) ?_
  rw [div_lt_one (by linarith)]
  linarith

/-- (c) 的种子（containment 支）：`x ∈ B_v(O_v, A r)`、`(A + 1/100) r ≤ q ≤ (A+1) r` ⇒
`B_v(O_v, r/100) ⊆ B_v(x, q)`，seed shift 的体积给 `κ_C q³ ≤ Vol B_v(x, q)`，
`κ_C = A⁻¹e⁻⁵⁷/512/(100(A+1))³`。 -/
theorem seed_volume_of_containment_C11V2 {Q : OrientedThreeStage.{u}} {g : Q.Metric}
    {O x : Q.Carrier} {A r q : ℝ} (hA : 0 < A) (hr : 0 < r)
    (hx : x ∈ riemannianBallOf g O (A * r)) (hqlow : (A + 1 / 100) * r ≤ q)
    (hqup : q ≤ (A + 1) * r)
    (hO : ENNReal.ofReal (A⁻¹ * Real.exp (-57) / 512 * (r / 100) ^ 3) ≤
      ballVolume g O (r / 100)) :
    ENNReal.ofReal (A⁻¹ * Real.exp (-57) / 512 / (100 * (A + 1)) ^ 3 * q ^ 3) ≤
      ballVolume g x q := by
  have hq : 0 ≤ q := le_trans (by positivity) hqlow
  have hsub : riemannianBallOf g O (r / 100) ⊆ riemannianBallOf g x q := by
    intro u hu
    change riemannianEDistOf g x u < ENNReal.ofReal q
    have hxO : riemannianEDistOf g x O < ENNReal.ofReal (A * r) := by
      rw [riemannianEDistOf_comm]
      exact hx
    calc
      riemannianEDistOf g x u ≤ riemannianEDistOf g x O + riemannianEDistOf g O u :=
        riemannianEDistOf_triangle g x O u
      _ < ENNReal.ofReal (A * r) + ENNReal.ofReal (r / 100) := ENNReal.add_lt_add hxO hu
      _ = ENNReal.ofReal ((A + 1 / 100) * r) := by
        rw [← ENNReal.ofReal_add (by positivity) (by positivity)]
        congr 1
        ring
      _ ≤ ENNReal.ofReal q := ENNReal.ofReal_le_ofReal hqlow
  have hcoef : A⁻¹ * Real.exp (-57) / 512 / (100 * (A + 1)) ^ 3 * q ^ 3 ≤
      A⁻¹ * Real.exp (-57) / 512 * (r / 100) ^ 3 := by
    have hq' : q / (100 * (A + 1)) ≤ r / 100 := by
      rw [div_le_iff₀ (by positivity)]
      nlinarith
    have hpow := pow_le_pow_left₀ (by positivity) hq' 3
    have he : A⁻¹ * Real.exp (-57) / 512 / (100 * (A + 1)) ^ 3 * q ^ 3 =
        A⁻¹ * Real.exp (-57) / 512 * (q / (100 * (A + 1))) ^ 3 := by
      rw [div_pow]
      ring
    rw [he]
    exact mul_le_mul_of_nonneg_left hpow (by positivity)
  exact (ENNReal.ofReal_le_ofReal hcoef).trans (hO.trans (measure_mono hsub))

/-- wide window（展开形，上沿 `(A+1) r`）⇒ P6B window（上沿 `r/100`）。 -/
theorem window_of_wide_window_C11V2 {P : OrientedThreeStage.{u}} {g : P.Metric}
    {F : GC.Interface.RawSurgery P g} {nr : ℝ → ℝ} {A κ : ℝ} (hA : 0 < A)
    (hW : ∃ T : ℝ, 0 < T ∧
      ∀ n, let H := (F.tower.history n).toHistory;
      ∀ (t : Icc (0 : ℝ) H.horizon) (p : (H.stageAt t).Carrier) (r : ℝ),
        T ≤ (t : ℝ) → 2 * r ^ 2 < (t : ℝ) → hasSmallParabolicCurvature H t p r →
        ENNReal.ofReal (A⁻¹ * r ^ 3) ≤ ballVolume (H.stageMetric (H.activeStage t) t) p r →
        ∀ (aSeed : Icc (0 : ℝ) H.horizon) (haT : aSeed ≤ t), (aSeed : ℝ) = (t : ℝ) - r ^ 2 →
        ∀ seedTrace : BackwardPointTrace H (H.activeStage aSeed) (H.activeStage t)
          (H.activeStage_mono haT) p,
        ∀ (v : Icc (0 : ℝ) H.horizon) (hav : aSeed ≤ v) (hvt : v ≤ t),
          (t : ℝ) - r ^ 2 / 2 ≤ (v : ℝ) →
        ∀ x ∈ riemannianBallOf (H.stageMetric (H.activeStage v) v)
          (seedTrace.point (H.activeStage v) (H.activeStage_mono hav) (H.activeStage_mono hvt))
          (A * r),
        ∀ ρ' : ℝ, nr v / 100 ≤ ρ' → ρ' ≤ (A + 1) * r →
          H.isParabolicallyRmControlledBall v x ρ' →
          ENNReal.ofReal (κ * ρ' ^ 3) ≤ ballVolume (H.stageMetric (H.activeStage v) v) x ρ') :
    LocalKappaWindowAt_P6B F nr A κ := by
  obtain ⟨T, hT, hK⟩ := hW
  refine ⟨T, hT, ?_⟩
  intro n H t p r hTt hr hsm hvol aSeed haT hclock seedTrace v hav hvt hv x hx ρ' hlow hup hball
  have hr0 : 0 < r := hsm.1
  exact hK n t p r hTt hr hsm hvol aSeed haT hclock seedTrace v hav hvt hv x hx ρ' hlow
    (by nlinarith) hball

/-- **seed shift ⇒ wide window**（`localKappaWindow_of_late_P6B` 的 wide 版，lead O1 = 放宽）：
wide late 形（展开；`LocalKappaLateAt_P6B` 只把上沿 `ρ' ≤ r` 换成 `ρ' ≤ L r`）在放大因子
`A' = 51200 e⁵⁷ A`、`L = 100(A+1)` 处 ⇒ 上沿 `(A+1) r` 的 wide window（`T = 4T'/3`）。KAPPA 的
`LocalKappaWideAt_C11Q`（accuracy 形）到此 late 形的一步与 P6B 的 envelope 步同形，留 P6 κ 线。 -/
theorem wideWindow_of_wideLate_C11V2 {P : OrientedThreeStage.{u}} {g : P.Metric}
    {F : GC.Interface.RawSurgery P g} {nr : ℝ → ℝ} {A κ : ℝ} (hA : 0 < A)
    (hL : ∃ T : ℝ, 0 < T ∧
      ∀ n, let H := (F.tower.history n).toHistory;
      ∀ (t : Icc (0 : ℝ) H.horizon) (p : (H.stageAt t).Carrier) (r : ℝ),
        T ≤ (t : ℝ) → 2 * r ^ 2 < (t : ℝ) → hasSmallParabolicCurvature H t p r →
        ENNReal.ofReal ((51200 * Real.exp 57 * A)⁻¹ * r ^ 3) ≤
          ballVolume (H.stageMetric (H.activeStage t) t) p r →
        ∀ x ∈ riemannianBallOf (H.stageMetric (H.activeStage t) t) p (51200 * Real.exp 57 * A * r),
        ∀ ρ' : ℝ, nr t / 100 ≤ ρ' → ρ' ≤ 100 * (A + 1) * r →
          H.isParabolicallyRmControlledBall t x ρ' →
          ENNReal.ofReal (κ * ρ' ^ 3) ≤ ballVolume (H.stageMetric (H.activeStage t) t) x ρ') :
    ∃ T : ℝ, 0 < T ∧
      ∀ n, let H := (F.tower.history n).toHistory;
      ∀ (t : Icc (0 : ℝ) H.horizon) (p : (H.stageAt t).Carrier) (r : ℝ),
        T ≤ (t : ℝ) → 2 * r ^ 2 < (t : ℝ) → hasSmallParabolicCurvature H t p r →
        ENNReal.ofReal (A⁻¹ * r ^ 3) ≤ ballVolume (H.stageMetric (H.activeStage t) t) p r →
        ∀ (aSeed : Icc (0 : ℝ) H.horizon) (haT : aSeed ≤ t), (aSeed : ℝ) = (t : ℝ) - r ^ 2 →
        ∀ seedTrace : BackwardPointTrace H (H.activeStage aSeed) (H.activeStage t)
          (H.activeStage_mono haT) p,
        ∀ (v : Icc (0 : ℝ) H.horizon) (hav : aSeed ≤ v) (hvt : v ≤ t),
          (t : ℝ) - r ^ 2 / 2 ≤ (v : ℝ) →
        ∀ x ∈ riemannianBallOf (H.stageMetric (H.activeStage v) v)
          (seedTrace.point (H.activeStage v) (H.activeStage_mono hav) (H.activeStage_mono hvt))
          (A * r),
        ∀ ρ' : ℝ, nr v / 100 ≤ ρ' → ρ' ≤ (A + 1) * r →
          H.isParabolicallyRmControlledBall v x ρ' →
          ENNReal.ofReal (κ * ρ' ^ 3) ≤ ballVolume (H.stageMetric (H.activeStage v) v) x ρ' := by
  obtain ⟨T', hT', hK⟩ := hL
  refine ⟨4 / 3 * T', by positivity, ?_⟩
  intro n H t p r hTt hr hsmall hvol aSeed haT hclock seedTrace v hav hvt hv x hx ρ' hlow hup
    hball
  have hr0 : 0 < r := hsmall.1
  have hshift := earlier_seed_on_half_depth_P6B haT p r A hr hclock hsmall hvol seedTrace v hav
    hvt hv
  obtain ⟨hseedV, hvolV, htimeV⟩ := hshift
  have hexp : 1 ≤ Real.exp 57 := Real.one_le_exp (by norm_num)
  have hTv : T' ≤ (v : ℝ) := by nlinarith
  have hinv : (51200 * Real.exp 57 * A)⁻¹ ≤ A⁻¹ * Real.exp (-57) / 512 := by
    rw [Real.exp_neg, mul_inv, mul_inv]
    have : (51200 : ℝ)⁻¹ ≤ 1 / 512 := by norm_num
    calc (51200 : ℝ)⁻¹ * (Real.exp 57)⁻¹ * A⁻¹ ≤ 1 / 512 * (Real.exp 57)⁻¹ * A⁻¹ := by
          gcongr
      _ = A⁻¹ * (Real.exp 57)⁻¹ / 512 := by ring
  have hvolA' : ENNReal.ofReal ((51200 * Real.exp 57 * A)⁻¹ * (r / 100) ^ 3) ≤
      ballVolume (H.stageMetric (H.activeStage v) v)
        (seedTrace.point (H.activeStage v) (H.activeStage_mono hav) (H.activeStage_mono hvt))
        (r / 100) :=
    (ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right hinv (by positivity))).trans hvolV
  have hball' : A * r ≤ 51200 * Real.exp 57 * A * (r / 100) := by
    have h1 : 1 ≤ 512 * Real.exp 57 := by nlinarith
    nlinarith [mul_pos hA hr0]
  have hx' := riemannianBallOf_mono _ _ hball' hx
  have hup' : ρ' ≤ 100 * (A + 1) * (r / 100) := by
    have he : 100 * (A + 1) * (r / 100) = (A + 1) * r := by ring
    rw [he]
    exact hup
  exact hK n v _ (r / 100) hTv htimeV hseedV hvolA' x hx' ρ' hlow hup' hball

/-- **G2 主定理（V4）：`hsmall` 装配**。`∃ ε₀ > 0`（G1 cap 接触的静态帽精度），对任意
`F, nr, A > 0, κ > 0, M`：wide window（展开形）+ `nr ≤ M` + (a) `hcapS` + (b) `hcan` + `hdeg` ⇒
WindowGlueC11V 的 `hsmall`（量词与 `LocalKappaWindowAt_P6B` 逐字同形，`0 < ρ' < nr v/100`、
`ρ' < r/100`），`κ' = min(κ_U, min(κ, κ_C)/(8e⁶))` 只依赖 `(D, ε, C₁, C₂, N, A, κ)`，
`T' = max(T, 2(M/50)²)`。 -/
theorem hsmall_of_wide_window_C11V2 (D : ℝ) (hD : 4 * StandardCap.transitionEnd + 6 ≤ D)
    (ε C1 C2 : ℝ) (N : ℕ) (hN : 0 < N) :
    ∃ ε₀ : ℝ, 0 < ε₀ ∧
    ∀ {P : OrientedThreeStage.{u}} {g : P.Metric} {F : GC.Interface.RawSurgery P g}
      {nr : ℝ → ℝ} {A κ M : ℝ}, 0 < A → 0 < κ → (∀ s, nr s ≤ M) →
      (∃ T : ℝ, 0 < T ∧
        ∀ n, let H := (F.tower.history n).toHistory;
        ∀ (t : Icc (0 : ℝ) H.horizon) (p : (H.stageAt t).Carrier) (r : ℝ),
          T ≤ (t : ℝ) → 2 * r ^ 2 < (t : ℝ) → hasSmallParabolicCurvature H t p r →
          ENNReal.ofReal (A⁻¹ * r ^ 3) ≤ ballVolume (H.stageMetric (H.activeStage t) t) p r →
          ∀ (aSeed : Icc (0 : ℝ) H.horizon) (haT : aSeed ≤ t), (aSeed : ℝ) = (t : ℝ) - r ^ 2 →
          ∀ seedTrace : BackwardPointTrace H (H.activeStage aSeed) (H.activeStage t)
            (H.activeStage_mono haT) p,
          ∀ (v : Icc (0 : ℝ) H.horizon) (hav : aSeed ≤ v) (hvt : v ≤ t),
            (t : ℝ) - r ^ 2 / 2 ≤ (v : ℝ) →
          ∀ x ∈ riemannianBallOf (H.stageMetric (H.activeStage v) v)
            (seedTrace.point (H.activeStage v) (H.activeStage_mono hav) (H.activeStage_mono hvt))
            (A * r),
          ∀ ρ' : ℝ, nr v / 100 ≤ ρ' → ρ' ≤ (A + 1) * r →
            H.isParabolicallyRmControlledBall v x ρ' →
            ENNReal.ofReal (κ * ρ' ^ 3) ≤ ballVolume (H.stageMetric (H.activeStage v) v) x ρ') →
      (∀ n, let H := (F.tower.history n).toHistory;
        ∀ (i : Fin H.eventCount) (b : (H.event i).RetainedBoundaryIndex),
          ∃ (fixed : StaticCapScaffold) (m : ℕ) (η : ℝ)
            (S : (H.event i).PresentedStaticCap fixed D m η b),
            η ≤ ε₀ ∧ 2 ≤ m ∧ S.hasCanonicalWindow) →
      (∀ n, let H := (F.tower.history n).toHistory;
        ∀ v v' : Icc (0 : ℝ) H.horizon, v' ≤ v → ∀ (w : (H.stageAt v').Carrier) (s : ℝ),
          0 < s → s < nr v / 50 → (v : ℝ) - s ^ 2 ≤ v' →
          s ^ 4 * normSq0S (H.stageMetric (H.activeStage v') v') w 4
            (metricRm04At (H.stageMetric (H.activeStage v') v') w) = 1 →
          ∃ V : SpatialCanonicalWitness (H.stageMetric (H.activeStage v') v') ε C1 C2 w,
            V.capTubeHasNeckChart ε) →
      (∀ n j, GC.GeneralFlow.StageFiniteDegreeBound ((F.tower.history n).toHistory.stage j) N) →
      ∃ κ' : ℝ, 0 < κ' ∧ ∃ T : ℝ, 0 < T ∧
        ∀ n, let H := (F.tower.history n).toHistory;
        ∀ (t : Icc (0 : ℝ) H.horizon) (p : (H.stageAt t).Carrier) (r : ℝ),
          T ≤ (t : ℝ) →
          2 * r ^ 2 < (t : ℝ) →
          hasSmallParabolicCurvature H t p r →
          ENNReal.ofReal (A⁻¹ * r ^ 3) ≤ ballVolume (H.stageMetric (H.activeStage t) t) p r →
          ∀ (aSeed : Icc (0 : ℝ) H.horizon) (haT : aSeed ≤ t),
            (aSeed : ℝ) = (t : ℝ) - r ^ 2 →
          ∀ seedTrace : BackwardPointTrace H (H.activeStage aSeed) (H.activeStage t)
            (H.activeStage_mono haT) p,
          ∀ (v : Icc (0 : ℝ) H.horizon) (hav : aSeed ≤ v) (hvt : v ≤ t),
            (t : ℝ) - r ^ 2 / 2 ≤ (v : ℝ) →
          ∀ x ∈ riemannianBallOf (H.stageMetric (H.activeStage v) v)
            (seedTrace.point (H.activeStage v) (H.activeStage_mono hav) (H.activeStage_mono hvt))
            (A * r),
          ∀ ρ' : ℝ, 0 < ρ' → ρ' < nr v / 100 → ρ' < r / 100 →
            H.isParabolicallyRmControlledBall v x ρ' →
            ENNReal.ofReal (κ' * ρ' ^ 3) ≤
              ballVolume (H.stageMetric (H.activeStage v) v) x ρ' := by
  obtain ⟨ε₀, κU, hε₀, hκU, hU⟩ := contact_volume_trichotomy_C11V2.{u} D hD ε C1 C2 N hN
  refine ⟨ε₀, hε₀, ?_⟩
  intro P g F nr A κ M hA hκ hnrM hW hcapS hcan hdeg
  obtain ⟨T, hT, hK⟩ := hW
  set κC : ℝ := A⁻¹ * Real.exp (-57) / 512 / (100 * (A + 1)) ^ 3 with hκC
  have hκCpos : 0 < κC := by rw [hκC]; positivity
  set κR : ℝ := min κ κC with hκR
  have hκRpos : 0 < κR := lt_min hκ hκCpos
  refine ⟨min κU (κR / (8 * Real.exp 6)), lt_min hκU (by positivity),
    max T (2 * (M / 50) ^ 2), lt_max_of_lt_left hT, ?_⟩
  intro n H t p r hTt hr hsm hvol aSeed haT hclock seedTrace v hav hvt hv x hx ρ' hρ' hρnr hρr
    hball
  have hr0 : 0 < r := hsm.1
  have hnrpos : 0 < nr v := by linarith
  set R : ℝ := min (nr v / 50) ((A + 1) * r) with hRdef
  have hρR : ρ' < R := lt_min (by linarith) (by nlinarith)
  have hRnr : R ≤ nr v / 50 := min_le_left _ _
  have hRv : R ^ 2 ≤ (v : ℝ) := by
    have hR0 : 0 ≤ R := hρ'.le.trans hρR.le
    have hRM : R ≤ M / 50 := hRnr.trans (by linarith [hnrM v])
    have hsq : R ^ 2 ≤ (M / 50) ^ 2 := pow_le_pow_left₀ hR0 hRM 2
    have hTM : 2 * (M / 50) ^ 2 ≤ (t : ℝ) := (le_max_right _ _).trans hTt
    nlinarith
  have hθ := seedRatio_lt_one_C11V2 hA
  have hseed : ∀ q : ℝ, max (1 / 2) ((A + 1 / 100) / (A + 1)) * R ≤ q → q < R →
      H.isParabolicallyRmControlledBall v x q →
      ENNReal.ofReal κR * ENNReal.ofReal q ^ 3 ≤
        riemannianVolumeMeasure ThreeModel (H.stageAt v).Carrier
          (H.stageMetric (H.activeStage v) v)
          (riemannianBallOf (H.stageMetric (H.activeStage v) v) x q) := by
    intro q hθq hqR hc
    have hq0 : 0 < q := hc.1
    rw [ofReal_mul_ofReal_cube_C11V2 κR hq0.le]
    have hR0 : 0 ≤ R := hρ'.le.trans hρR.le
    by_cases hcase : nr v / 50 ≤ (A + 1) * r
    · have hRe : R = nr v / 50 := min_eq_left hcase
      have hlow : nr v / 100 ≤ q := by
        have h1 : 1 / 2 * R ≤ max (1 / 2) ((A + 1 / 100) / (A + 1)) * R :=
          mul_le_mul_of_nonneg_right (le_max_left _ _) hR0
        rw [hRe] at h1 hθq
        linarith
      have hup : q ≤ (A + 1) * r := hqR.le.trans (min_le_right _ _)
      have h := hK n t p r ((le_max_left _ _).trans hTt) hr hsm hvol aSeed haT hclock seedTrace
        v hav hvt hv x hx q hlow hup hc
      exact (ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right (min_le_left _ _)
        (pow_nonneg hq0.le 3))).trans h
    · have hRe : R = (A + 1) * r := min_eq_right (le_of_lt (lt_of_not_ge hcase))
      have hlow : (A + 1 / 100) * r ≤ q := by
        have h1 : (A + 1 / 100) / (A + 1) * R ≤ max (1 / 2) ((A + 1 / 100) / (A + 1)) * R :=
          mul_le_mul_of_nonneg_right (le_max_right _ _) hR0
        have he : (A + 1 / 100) / (A + 1) * R = (A + 1 / 100) * r := by
          rw [hRe]
          field_simp
        linarith
      have hup : q ≤ (A + 1) * r := hRe ▸ hqR.le
      have hshift := earlier_seed_on_half_depth_P6B haT p r A hr hclock hsm hvol seedTrace v hav
        hvt hv
      have h := seed_volume_of_containment_C11V2 hA hr0 hx hlow hup hshift.2.1
      exact (ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right (min_le_right _ _)
        (pow_nonneg hq0.le 3))).trans h
  have hmain := hU H v x hball hρR hRv (fun i _ _ => rfl)
    (fun i b _ _ => hcapS n i b)
    (fun v' hv'v w s hs hsR hvs hcont => hcan n v v' hv'v w s hs (hsR.trans_le hRnr) hvs hcont)
    (hdeg n) hθ hκRpos.le hseed
  rw [ofReal_mul_ofReal_cube_C11V2 _ hρ'.le] at hmain
  exact hmain

/-- **端到端（window 形）**：同一组前提 ⇒ `∃ κ'' > 0, LocalKappaWindowAt_P6B F (fun _ => 0) A κ''`
（wide window ⇒ P6B window `hW`；G2 主定理 ⇒ `hsmall`；`localKappaWindow_zero_of_window_and_small_C11V`
拼接）。这是 `tracedKappa_of_window_P6B` 的 `hW`。 -/
theorem localKappaWindow_zero_of_wide_window_C11V2 (D : ℝ)
    (hD : 4 * StandardCap.transitionEnd + 6 ≤ D) (ε C1 C2 : ℝ) (N : ℕ) (hN : 0 < N) :
    ∃ ε₀ : ℝ, 0 < ε₀ ∧
    ∀ {P : OrientedThreeStage.{u}} {g : P.Metric} {F : GC.Interface.RawSurgery P g}
      {nr : ℝ → ℝ} {A κ M : ℝ}, 0 < A → 0 < κ → (∀ s, nr s ≤ M) →
      (∃ T : ℝ, 0 < T ∧
        ∀ n, let H := (F.tower.history n).toHistory;
        ∀ (t : Icc (0 : ℝ) H.horizon) (p : (H.stageAt t).Carrier) (r : ℝ),
          T ≤ (t : ℝ) → 2 * r ^ 2 < (t : ℝ) → hasSmallParabolicCurvature H t p r →
          ENNReal.ofReal (A⁻¹ * r ^ 3) ≤ ballVolume (H.stageMetric (H.activeStage t) t) p r →
          ∀ (aSeed : Icc (0 : ℝ) H.horizon) (haT : aSeed ≤ t), (aSeed : ℝ) = (t : ℝ) - r ^ 2 →
          ∀ seedTrace : BackwardPointTrace H (H.activeStage aSeed) (H.activeStage t)
            (H.activeStage_mono haT) p,
          ∀ (v : Icc (0 : ℝ) H.horizon) (hav : aSeed ≤ v) (hvt : v ≤ t),
            (t : ℝ) - r ^ 2 / 2 ≤ (v : ℝ) →
          ∀ x ∈ riemannianBallOf (H.stageMetric (H.activeStage v) v)
            (seedTrace.point (H.activeStage v) (H.activeStage_mono hav) (H.activeStage_mono hvt))
            (A * r),
          ∀ ρ' : ℝ, nr v / 100 ≤ ρ' → ρ' ≤ (A + 1) * r →
            H.isParabolicallyRmControlledBall v x ρ' →
            ENNReal.ofReal (κ * ρ' ^ 3) ≤ ballVolume (H.stageMetric (H.activeStage v) v) x ρ') →
      (∀ n, let H := (F.tower.history n).toHistory;
        ∀ (i : Fin H.eventCount) (b : (H.event i).RetainedBoundaryIndex),
          ∃ (fixed : StaticCapScaffold) (m : ℕ) (η : ℝ)
            (S : (H.event i).PresentedStaticCap fixed D m η b),
            η ≤ ε₀ ∧ 2 ≤ m ∧ S.hasCanonicalWindow) →
      (∀ n, let H := (F.tower.history n).toHistory;
        ∀ v v' : Icc (0 : ℝ) H.horizon, v' ≤ v → ∀ (w : (H.stageAt v').Carrier) (s : ℝ),
          0 < s → s < nr v / 50 → (v : ℝ) - s ^ 2 ≤ v' →
          s ^ 4 * normSq0S (H.stageMetric (H.activeStage v') v') w 4
            (metricRm04At (H.stageMetric (H.activeStage v') v') w) = 1 →
          ∃ V : SpatialCanonicalWitness (H.stageMetric (H.activeStage v') v') ε C1 C2 w,
            V.capTubeHasNeckChart ε) →
      (∀ n j, GC.GeneralFlow.StageFiniteDegreeBound ((F.tower.history n).toHistory.stage j) N) →
      ∃ κ'' : ℝ, 0 < κ'' ∧ LocalKappaWindowAt_P6B F (fun _ => 0) A κ'' := by
  obtain ⟨ε₀, hε₀, hS⟩ := hsmall_of_wide_window_C11V2.{u} D hD ε C1 C2 N hN
  refine ⟨ε₀, hε₀, ?_⟩
  intro P g F nr A κ M hA hκ hnrM hW hcapS hcan hdeg
  obtain ⟨κ', hκ', hsmall⟩ := hS hA hκ hnrM hW hcapS hcan hdeg
  exact ⟨min κ κ', lt_min hκ hκ',
    localKappaWindow_zero_of_window_and_small_C11V (window_of_wide_window_C11V2 hA hW) hsmall⟩

/-- **端到端 consumer**（wide late ⇒ wide window ⇒ `hsmall` ⇒ `nr := 0` window ⇒ M8 bridge）：
wide late 形（展开，`A' = 51200e⁵⁷A`、`L = 100(A+1)`）+ `hcapS` + `hcan` + `hdeg` + `nr ≤ M` 喂
`tracedKappa_of_window_P6B`，坏点序列的 trace-local κ 不再经 `nr := 0` 的隐含假设。 -/
example (D : ℝ) (hD : 4 * StandardCap.transitionEnd + 6 ≤ D) (ε C1 C2 : ℝ) (N : ℕ) (hN : 0 < N) :
    ∃ ε₀ : ℝ, 0 < ε₀ ∧
    ∀ {P : OrientedThreeStage.{u}} {g : P.Metric} {F : GC.Interface.RawSurgery P g}
      {nr : ℝ → ℝ} {A κ M : ℝ}, 0 < A → 0 < κ → (∀ s, nr s ≤ M) →
      (∃ T : ℝ, 0 < T ∧
        ∀ n, let H := (F.tower.history n).toHistory;
        ∀ (t : Icc (0 : ℝ) H.horizon) (p : (H.stageAt t).Carrier) (r : ℝ),
          T ≤ (t : ℝ) → 2 * r ^ 2 < (t : ℝ) → hasSmallParabolicCurvature H t p r →
          ENNReal.ofReal ((51200 * Real.exp 57 * A)⁻¹ * r ^ 3) ≤
            ballVolume (H.stageMetric (H.activeStage t) t) p r →
          ∀ x ∈ riemannianBallOf (H.stageMetric (H.activeStage t) t) p
            (51200 * Real.exp 57 * A * r),
          ∀ ρ' : ℝ, nr t / 100 ≤ ρ' → ρ' ≤ 100 * (A + 1) * r →
            H.isParabolicallyRmControlledBall t x ρ' →
            ENNReal.ofReal (κ * ρ' ^ 3) ≤ ballVolume (H.stageMetric (H.activeStage t) t) x ρ') →
      (∀ n, let H := (F.tower.history n).toHistory;
        ∀ (i : Fin H.eventCount) (b : (H.event i).RetainedBoundaryIndex),
          ∃ (fixed : StaticCapScaffold) (m : ℕ) (η : ℝ)
            (S : (H.event i).PresentedStaticCap fixed D m η b),
            η ≤ ε₀ ∧ 2 ≤ m ∧ S.hasCanonicalWindow) →
      (∀ n, let H := (F.tower.history n).toHistory;
        ∀ v v' : Icc (0 : ℝ) H.horizon, v' ≤ v → ∀ (w : (H.stageAt v').Carrier) (s : ℝ),
          0 < s → s < nr v / 50 → (v : ℝ) - s ^ 2 ≤ v' →
          s ^ 4 * normSq0S (H.stageMetric (H.activeStage v') v') w 4
            (metricRm04At (H.stageMetric (H.activeStage v') v') w) = 1 →
          ∃ V : SpatialCanonicalWitness (H.stageMetric (H.activeStage v') v') ε C1 C2 w,
            V.capTubeHasNeckChart ε) →
      (∀ n j, GC.GeneralFlow.StageFiniteDegreeBound ((F.tower.history n).toHistory.stage j) N) →
      True := by
  obtain ⟨ε₀, hε₀, hE⟩ := localKappaWindow_zero_of_wide_window_C11V2.{u} D hD ε C1 C2 N hN
  refine ⟨ε₀, hε₀, ?_⟩
  intro P g F nr A κ M hA hκ hnrM hL hcapS hcan hdeg
  obtain ⟨κ'', -, hW0⟩ := hE hA hκ hnrM (wideWindow_of_wideLate_C11V2 hA hL) hcapS hcan hdeg
  have := tracedKappa_of_window_P6B hW0
  trivial

end GC.LongTime.Ch11
