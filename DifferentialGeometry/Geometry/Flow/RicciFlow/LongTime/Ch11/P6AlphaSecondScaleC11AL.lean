import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.P6SelectionRetainedP6R2

/-!
# (α) 路线 G1：margin split + 二次重标度集合 ⊂ selection 的 `hgood` 域（O-CH11-ALPHA G1，后缀 `_C11AL`）

设计：`docs/geometrization/chapter8/design-C11-alpha-20261007.md` §1 / §3 S3。canonical 输入**只**是
`selection_of_bad_sequence_retained_P6R2` 输出里的 `hgood`（阈值 `4 R_n`、深度 `L²/R`、seed 余量 `L/√R`）；
不调用 `CanonicalLateCore` / `hspine` / `LargerBallCanonicalLateSupply`。

* `hgood_mono_C11AL`：hgood 关于 `L` 反单调（`0 ≤ L' ≤ L`，`0 ≤ R`）——下游以 `L' := L/2` 运行的依据
  （margin split，§1）。
* `hgood_secondScale_C11AL`（主定理）：对任意固定 `T K η`（`0 < η`），`∀ᶠ n`，对任意二次尺度 `q ≥ max 1 (4/η) · R n`、
  任意 ExitGuard(`L/2`) 点 `(s, x)`（`σ − T/R ≤ s ≤ σ`），二次尺度集合
  `{(v, z) : s − K/q ≤ v ≤ s, d_v(O_v, z) ≤ d_s(O_s, x) + K/√q, η q ≤ R(v, z)}` 上处处
  `HasSpatialCanonicalTimeControl`。即 review Q1(c) 的"阈值 `C_g R_n / q_high → 0`"（`C_g = 4`）在域上成立。
* `hgood_secondScale_of_selection_C11AL`（consumer）：P6R2 前提逐字 ⇒ selection 输出 ∧ 上述二次尺度控制。
-/

set_option autoImplicit false

noncomputable section

open Set Filter Function
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood
open scoped Manifold NNReal Topology ContDiff ENNReal

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

universe u

open Perelman.CanonicalNeighborhood.FiniteHorn (SpatialCanonicalWitness)

namespace ObservedHistory

/-- **hgood 关于 `L` 反单调（`_C11AL`）**：P6R2 的 hgood 合取项（单 history 形）在 `L` 处成立 ⇒ 在任意
`0 ≤ L' ≤ L` 处成立（时间域 `σ − L'²/R ≤ v` 更小、seed 余量 `L'/√R` 更小；需 `0 ≤ R`）。 -/
theorem hgood_mono_C11AL (H : ObservedHistory.{u}) {eps C1 C2 : ℝ} {Ctime : ℝ≥0}
    (aSeed T σ : Icc (0 : ℝ) H.horizon) (haT : aSeed ≤ T) (hsT : σ ≤ T) (has : aSeed ≤ σ)
    {p : (H.stageAt T).Carrier}
    (seedTrace : BackwardPointTrace H (H.activeStage aSeed) (H.activeStage T)
      (H.activeStage_mono haT) p)
    (y : (H.stageAt σ).Carrier) {R L L' : ℝ} (hR : 0 ≤ R) (hL' : 0 ≤ L') (hLL : L' ≤ L)
    (hgood : ∀ (v : Icc (0 : ℝ) H.horizon) (hav : aSeed ≤ v) (hvs : v ≤ σ),
      (σ : ℝ) - L ^ 2 / R ≤ (v : ℝ) →
      ∀ z : (H.stageAt v).Carrier,
        riemannianEDistOf (H.stageMetric (H.activeStage v) v)
            (seedTrace.point (H.activeStage v) (H.activeStage_mono hav)
              (H.activeStage_mono (hvs.trans hsT))) z ≤
          riemannianEDistOf (H.stageMetric (H.activeStage σ) σ)
              (seedTrace.point (H.activeStage σ) (H.activeStage_mono has)
                (H.activeStage_mono hsT)) y +
            ENNReal.ofReal (L / Real.sqrt R) →
        4 * R ≤ metricScalarAt (H.stageMetric (H.activeStage v) v) z →
        H.HasSpatialCanonicalTimeControl eps C1 C2 Ctime v z) :
    ∀ (v : Icc (0 : ℝ) H.horizon) (hav : aSeed ≤ v) (hvs : v ≤ σ),
      (σ : ℝ) - L' ^ 2 / R ≤ (v : ℝ) →
      ∀ z : (H.stageAt v).Carrier,
        riemannianEDistOf (H.stageMetric (H.activeStage v) v)
            (seedTrace.point (H.activeStage v) (H.activeStage_mono hav)
              (H.activeStage_mono (hvs.trans hsT))) z ≤
          riemannianEDistOf (H.stageMetric (H.activeStage σ) σ)
              (seedTrace.point (H.activeStage σ) (H.activeStage_mono has)
                (H.activeStage_mono hsT)) y +
            ENNReal.ofReal (L' / Real.sqrt R) →
        4 * R ≤ metricScalarAt (H.stageMetric (H.activeStage v) v) z →
        H.HasSpatialCanonicalTimeControl eps C1 C2 Ctime v z := by
  intro v hav hvs hv z hz hRz
  have hsq : L' ^ 2 ≤ L ^ 2 := pow_le_pow_left₀ hL' hLL 2
  have htime : (σ : ℝ) - L ^ 2 / R ≤ (v : ℝ) :=
    le_trans (sub_le_sub_left (div_le_div_of_nonneg_right hsq hR) _) hv
  refine hgood v hav hvs htime z (hz.trans ?_) hRz
  exact add_le_add le_rfl
    (ENNReal.ofReal_le_ofReal (div_le_div_of_nonneg_right hLL (Real.sqrt_nonneg R)))

/-- 二次尺度算术（`_C11AL`）：`0 < R ≤ q`、`T + max K 0 ≤ L²` ⇒ `σ − T/R ≤ s`、`s − K/q ≤ v` 推出
`σ − L²/R ≤ v`。 -/
theorem secondScale_time_C11AL {R q L T K σ s v : ℝ} (hR : 0 < R) (hRq : R ≤ q)
    (hTK : T + max K 0 ≤ L ^ 2) (hs : σ - T / R ≤ s) (hv : s - K / q ≤ v) :
    σ - L ^ 2 / R ≤ v := by
  have hq : 0 < q := hR.trans_le hRq
  have hKq : K / q ≤ max K 0 / R :=
    (div_le_div_of_nonneg_right (le_max_left K 0) hq.le).trans
      (div_le_div_of_nonneg_left (le_max_right K 0) hR hRq)
  have hsum : T / R + max K 0 / R ≤ L ^ 2 / R := by
    rw [← add_div]
    exact div_le_div_of_nonneg_right hTK hR.le
  linarith

/-- 二次尺度 seed 余量（`_C11AL`）：`0 < R ≤ q`、`2 max K 0 ≤ L` ⇒
`ofReal((L/2)/√R) + ofReal(K/√q) ≤ ofReal(L/√R)`。 -/
theorem secondScale_margin_C11AL {R q L K : ℝ} (hR : 0 < R) (hRq : R ≤ q)
    (hKL : 2 * max K 0 ≤ L) :
    ENNReal.ofReal (L / 2 / Real.sqrt R) + ENNReal.ofReal (K / Real.sqrt q) ≤
      ENNReal.ofReal (L / Real.sqrt R) := by
  have hsR : 0 < Real.sqrt R := Real.sqrt_pos.mpr hR
  have hsq : Real.sqrt R ≤ Real.sqrt q := Real.sqrt_le_sqrt hRq
  have hK0 : 0 ≤ max K 0 := le_max_right K 0
  have hL0 : 0 ≤ L := le_trans (by positivity) hKL
  have h1 : K / Real.sqrt q ≤ max K 0 / Real.sqrt R :=
    (div_le_div_of_nonneg_right (le_max_left K 0) (Real.sqrt_nonneg q)).trans
      (div_le_div_of_nonneg_left hK0 hsR hsq)
  calc ENNReal.ofReal (L / 2 / Real.sqrt R) + ENNReal.ofReal (K / Real.sqrt q)
      ≤ ENNReal.ofReal (L / 2 / Real.sqrt R) + ENNReal.ofReal (max K 0 / Real.sqrt R) :=
        add_le_add le_rfl (ENNReal.ofReal_le_ofReal h1)
    _ = ENNReal.ofReal (L / 2 / Real.sqrt R + max K 0 / Real.sqrt R) :=
        (ENNReal.ofReal_add (by positivity) (by positivity)).symm
    _ ≤ ENNReal.ofReal (L / Real.sqrt R) := by
        refine ENNReal.ofReal_le_ofReal ?_
        rw [← add_div]
        refine div_le_div_of_nonneg_right ?_ hsR.le
        linarith

/-- 二次尺度阈值（`_C11AL`）：`0 < η`、`0 ≤ R`、`max 1 (4/η) · R ≤ q`、`η q ≤ S` ⇒ `4 R ≤ S`。 -/
theorem secondScale_threshold_C11AL {R q η S : ℝ} (hη : 0 < η) (hR : 0 ≤ R)
    (hq : max 1 (4 / η) * R ≤ q) (hS : η * q ≤ S) : 4 * R ≤ S := by
  have h1 : 4 / η * R ≤ q := (mul_le_mul_of_nonneg_right (le_max_right _ _) hR).trans hq
  have h2 : η * (4 / η * R) ≤ η * q := mul_le_mul_of_nonneg_left h1 hη.le
  have h3 : η * (4 / η * R) = 4 * R := by field_simp
  linarith

/-- **二次重标度集合 ⊂ hgood 域（G1 主定理，`_C11AL`）**：`hgood` = P6R2 输出的 hgood 合取项
（逐字），`L → ∞`、`0 < R n`。对任意固定 `T K η`（`0 < η`），`∀ᶠ n`：对任意 `q ≥ max 1 (4/η) · R n`、
任意 ExitGuard(`L/2`) 点 `(s, x)`（`aSeed ≤ s ≤ σ`，`σ − T/R ≤ s`，
`d_s(O_s, x) ≤ d_σ(O_σ, y) + (L/2)/√R`），二次尺度集合 `s − K/q ≤ v ≤ s`、
`d_v(O_v, z) ≤ d_s(O_s, x) + K/√q`、`η q ≤ R(v, z)` 上处处 `HasSpatialCanonicalTimeControl`。
`n` 的门槛只依赖 `(T, K)`（`L n ≥ max (max 1 (T + max K 0)) (2 max K 0)`），
与 `q, s, x, v, z, η` 无关。 -/
theorem hgood_secondScale_C11AL (Kh : ℕ → ObservedHistory.{u})
    (Tn aSeed σ : ∀ n, Icc (0 : ℝ) (Kh n).horizon)
    (haT : ∀ n, aSeed n ≤ Tn n) (hsT : ∀ n, σ n ≤ Tn n) (has : ∀ n, aSeed n ≤ σ n)
    (pT : ∀ n, ((Kh n).stageAt (Tn n)).Carrier)
    (seedTrace : ∀ n, BackwardPointTrace (Kh n) ((Kh n).activeStage (aSeed n))
      ((Kh n).activeStage (Tn n)) ((Kh n).activeStage_mono (haT n)) (pT n))
    (y : ∀ n, ((Kh n).stageAt (σ n)).Carrier) (R L : ℕ → ℝ) (hR : ∀ n, 0 < R n)
    (hL : Tendsto L atTop atTop) {eps C1 C2 : ℝ} {Ctime : ℝ≥0}
    (hgood : ∀ n, ∀ (v : Icc (0 : ℝ) (Kh n).horizon) (hav : aSeed n ≤ v) (hvs : v ≤ σ n),
      (σ n : ℝ) - L n ^ 2 / R n ≤ (v : ℝ) →
      ∀ z : ((Kh n).stageAt v).Carrier,
        riemannianEDistOf ((Kh n).stageMetric ((Kh n).activeStage v) v)
            ((seedTrace n).point ((Kh n).activeStage v) ((Kh n).activeStage_mono hav)
              ((Kh n).activeStage_mono (hvs.trans (hsT n)))) z ≤
          riemannianEDistOf ((Kh n).stageMetric ((Kh n).activeStage (σ n)) (σ n))
              ((seedTrace n).point ((Kh n).activeStage (σ n)) ((Kh n).activeStage_mono (has n))
                ((Kh n).activeStage_mono (hsT n))) (y n) +
            ENNReal.ofReal (L n / Real.sqrt (R n)) →
        4 * R n ≤ metricScalarAt ((Kh n).stageMetric ((Kh n).activeStage v) v) z →
        (Kh n).HasSpatialCanonicalTimeControl eps C1 C2 Ctime v z) :
    ∀ T K η : ℝ, 0 < η → ∀ᶠ n in atTop,
      ∀ q : ℝ, max 1 (4 / η) * R n ≤ q →
      ∀ (s : Icc (0 : ℝ) (Kh n).horizon) (has' : aSeed n ≤ s) (hsσ : s ≤ σ n)
        (x : ((Kh n).stageAt s).Carrier),
        (σ n : ℝ) - T / R n ≤ (s : ℝ) →
        riemannianEDistOf ((Kh n).stageMetric ((Kh n).activeStage s) s)
            ((seedTrace n).point ((Kh n).activeStage s) ((Kh n).activeStage_mono has')
              ((Kh n).activeStage_mono (hsσ.trans (hsT n)))) x ≤
          riemannianEDistOf ((Kh n).stageMetric ((Kh n).activeStage (σ n)) (σ n))
              ((seedTrace n).point ((Kh n).activeStage (σ n)) ((Kh n).activeStage_mono (has n))
                ((Kh n).activeStage_mono (hsT n))) (y n) +
            ENNReal.ofReal (L n / 2 / Real.sqrt (R n)) →
      ∀ (v : Icc (0 : ℝ) (Kh n).horizon) (hav : aSeed n ≤ v) (hvs : v ≤ s),
        (s : ℝ) - K / q ≤ (v : ℝ) →
      ∀ z : ((Kh n).stageAt v).Carrier,
        riemannianEDistOf ((Kh n).stageMetric ((Kh n).activeStage v) v)
            ((seedTrace n).point ((Kh n).activeStage v) ((Kh n).activeStage_mono hav)
              ((Kh n).activeStage_mono ((hvs.trans hsσ).trans (hsT n)))) z ≤
          riemannianEDistOf ((Kh n).stageMetric ((Kh n).activeStage s) s)
              ((seedTrace n).point ((Kh n).activeStage s) ((Kh n).activeStage_mono has')
                ((Kh n).activeStage_mono (hsσ.trans (hsT n)))) x +
            ENNReal.ofReal (K / Real.sqrt q) →
        η * q ≤ metricScalarAt ((Kh n).stageMetric ((Kh n).activeStage v) v) z →
        (Kh n).HasSpatialCanonicalTimeControl eps C1 C2 Ctime v z := by
  intro T K η hη
  filter_upwards [hL.eventually_ge_atTop (max (max 1 (T + max K 0)) (2 * max K 0))] with n hLn
  intro q hq s has' hsσ x hsT' hx v hav hvs hvK z hz hRz
  have hRn := hR n
  have hRq : R n ≤ q :=
    le_trans (le_mul_of_one_le_left hRn.le (le_max_left _ _)) hq
  have hL1 : 1 ≤ L n := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hLn
  have hTK : T + max K 0 ≤ L n ^ 2 := by
    have h1 : T + max K 0 ≤ L n := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hLn
    nlinarith
  have hKL : 2 * max K 0 ≤ L n := le_trans (le_max_right _ _) hLn
  have htime : (σ n : ℝ) - L n ^ 2 / R n ≤ (v : ℝ) :=
    secondScale_time_C11AL hRn hRq hTK hsT' hvK
  refine hgood n v hav (hvs.trans hsσ) htime z ?_ (secondScale_threshold_C11AL hη hRn.le hq hRz)
  calc riemannianEDistOf ((Kh n).stageMetric ((Kh n).activeStage v) v)
        ((seedTrace n).point ((Kh n).activeStage v) ((Kh n).activeStage_mono hav)
          ((Kh n).activeStage_mono ((hvs.trans hsσ).trans (hsT n)))) z
      ≤ (riemannianEDistOf ((Kh n).stageMetric ((Kh n).activeStage (σ n)) (σ n))
            ((seedTrace n).point ((Kh n).activeStage (σ n)) ((Kh n).activeStage_mono (has n))
              ((Kh n).activeStage_mono (hsT n))) (y n) +
          ENNReal.ofReal (L n / 2 / Real.sqrt (R n))) + ENNReal.ofReal (K / Real.sqrt q) :=
        hz.trans (add_le_add hx le_rfl)
    _ ≤ riemannianEDistOf ((Kh n).stageMetric ((Kh n).activeStage (σ n)) (σ n))
          ((seedTrace n).point ((Kh n).activeStage (σ n)) ((Kh n).activeStage_mono (has n))
            ((Kh n).activeStage_mono (hsT n))) (y n) +
        ENNReal.ofReal (L n / Real.sqrt (R n)) := by
        rw [add_assoc]
        exact add_le_add le_rfl (secondScale_margin_C11AL hRn hRq hKL)

/-- **consumer（`_C11AL`）**：`selection_of_bad_sequence_retained_P6R2` 的前提逐字 ⇒ 存在 selection
`(σ, y, R, L)`：坏点 `¬Control(σ, y)`、`L → ∞`，且二次尺度集合（G1 主定理形）上处处 `HasSpatialCanonicalTimeControl`。
唯一 canonical 输入 = 同一次 selection 的 hgood。 -/
theorem hgood_secondScale_of_selection_C11AL {Kh : ℕ → ObservedHistory.{u}}
    (q : ℕ → CutoffParameters)
    {eps C1 C2 C1' C2' : ℝ} (hC1 : C1 ≤ C1') (hC2 : C2 ≤ C2')
    {Ctime Ctime' : ℝ≥0} (hCtime : Ctime ≤ Ctime')
    (hanti : ∀ n, AntitoneOn (q n).neckRadius (Ici 0))
    (hcanonical : ∀ n (v : Icc (0 : ℝ) (Kh n).horizon) (z : ((Kh n).stageAt v).Carrier),
      ((q n).neckRadius v ^ 2)⁻¹ < metricScalarAt ((Kh n).stageMetric ((Kh n).activeStage v) v) z →
      ∃ W : SpatialCanonicalWitness ((Kh n).stageMetric ((Kh n).activeStage v) v) eps C1 C2 z,
        W.capTubeHasNeckChart eps)
    (hderivative : ∀ n (v : Icc (0 : ℝ) (Kh n).horizon) (z : ((Kh n).stageAt v).Carrier),
      (Kh n).time ((Kh n).activeStage v) < (v : ℝ) → (v : ℝ) < (Kh n).horizon →
      ((q n).neckRadius v ^ 2)⁻¹ < metricScalarAt ((Kh n).stageMetric ((Kh n).activeStage v) v) z →
      |derivWithin (fun t => metricScalarAt ((Kh n).stageMetric ((Kh n).activeStage v) t) z)
        (Iic (v : ℝ)) v| ≤
        Ctime * metricScalarAt ((Kh n).stageMetric ((Kh n).activeStage v) v) z ^ 2)
    (Tn : ∀ n, Icc (0 : ℝ) (Kh n).horizon) (pT : ∀ n, ((Kh n).stageAt (Tn n)).Carrier)
    (r : ℕ → ℝ) (A : ℝ) (hr : ∀ n, 0 < r n) (hA : 0 < A)
    (aSeed : ∀ n, Icc (0 : ℝ) (Kh n).horizon) (haT : ∀ n, aSeed n ≤ Tn n)
    (haSeed : ∀ n, (aSeed n : ℝ) = (Tn n : ℝ) - r n ^ 2)
    (seedTrace : ∀ n, BackwardPointTrace (Kh n) ((Kh n).activeStage (aSeed n))
      ((Kh n).activeStage (Tn n)) ((Kh n).activeStage_mono (haT n)) (pT n))
    (x : ∀ n, ((Kh n).stageAt (Tn n)).Carrier)
    (hx : ∀ n, x n ∈ riemannianBallOf ((Kh n).stageMetric ((Kh n).activeStage (Tn n)) (Tn n))
      (pT n) (A * r n))
    (hR : ∀ n, 0 < metricScalarAt ((Kh n).stageMetric ((Kh n).activeStage (Tn n)) (Tn n)) (x n))
    (hbad : ∀ n, ¬ (Kh n).HasSpatialCanonicalTimeControl eps C1' C2' Ctime' (Tn n) (x n))
    (hdiv : Tendsto (fun n => metricScalarAt ((Kh n).stageMetric ((Kh n).activeStage (Tn n))
      (Tn n)) (x n) * r n ^ 2) atTop atTop) :
    ∃ (σ : ∀ n, Icc (0 : ℝ) (Kh n).horizon) (y : ∀ n, ((Kh n).stageAt (σ n)).Carrier)
      (R : ℕ → ℝ) (hsT : ∀ n, σ n ≤ Tn n) (has : ∀ n, aSeed n ≤ σ n) (L : ℕ → ℝ),
      (∀ n, ¬ (Kh n).HasSpatialCanonicalTimeControl eps C1' C2' Ctime' (σ n) (y n)) ∧
      Tendsto L atTop atTop ∧
      ∀ T K η : ℝ, 0 < η → ∀ᶠ n in atTop,
        ∀ qh : ℝ, max 1 (4 / η) * R n ≤ qh →
        ∀ (s : Icc (0 : ℝ) (Kh n).horizon) (has' : aSeed n ≤ s) (hsσ : s ≤ σ n)
          (xs : ((Kh n).stageAt s).Carrier),
          (σ n : ℝ) - T / R n ≤ (s : ℝ) →
          riemannianEDistOf ((Kh n).stageMetric ((Kh n).activeStage s) s)
              ((seedTrace n).point ((Kh n).activeStage s) ((Kh n).activeStage_mono has')
                ((Kh n).activeStage_mono (hsσ.trans (hsT n)))) xs ≤
            riemannianEDistOf ((Kh n).stageMetric ((Kh n).activeStage (σ n)) (σ n))
                ((seedTrace n).point ((Kh n).activeStage (σ n)) ((Kh n).activeStage_mono (has n))
                  ((Kh n).activeStage_mono (hsT n))) (y n) +
              ENNReal.ofReal (L n / 2 / Real.sqrt (R n)) →
        ∀ (v : Icc (0 : ℝ) (Kh n).horizon) (hav : aSeed n ≤ v) (hvs : v ≤ s),
          (s : ℝ) - K / qh ≤ (v : ℝ) →
        ∀ z : ((Kh n).stageAt v).Carrier,
          riemannianEDistOf ((Kh n).stageMetric ((Kh n).activeStage v) v)
              ((seedTrace n).point ((Kh n).activeStage v) ((Kh n).activeStage_mono hav)
                ((Kh n).activeStage_mono ((hvs.trans hsσ).trans (hsT n)))) z ≤
            riemannianEDistOf ((Kh n).stageMetric ((Kh n).activeStage s) s)
                ((seedTrace n).point ((Kh n).activeStage s) ((Kh n).activeStage_mono has')
                  ((Kh n).activeStage_mono (hsσ.trans (hsT n)))) xs +
              ENNReal.ofReal (K / Real.sqrt qh) →
          η * qh ≤ metricScalarAt ((Kh n).stageMetric ((Kh n).activeStage v) v) z →
          (Kh n).HasSpatialCanonicalTimeControl eps C1' C2' Ctime' v z := by
  obtain ⟨σ, y, R, hsT, has, L, ⟨-, hRpos, -, -, hL, hsel, hgood, -⟩, -⟩ :=
    selection_of_bad_sequence_retained_P6R2 q hC1 hC2 hCtime hanti hcanonical hderivative Tn pT
      r A hr hA aSeed haT haSeed seedTrace x hx hR hbad hdiv
  exact ⟨σ, y, R, hsT, has, L, hsel, hL,
    hgood_secondScale_C11AL Kh Tn aSeed σ haT hsT has pT seedTrace y R L hRpos hL hgood⟩

end ObservedHistory

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
