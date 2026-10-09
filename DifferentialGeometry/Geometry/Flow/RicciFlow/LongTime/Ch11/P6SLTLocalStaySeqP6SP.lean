import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.P6SLTLocalStayCXWireP6SP
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.P6SLTLocalProdP6SP

/-!
# c⋆ 版 `hstayLoc` 的序列层 producer（O-CH11-SLTPROD G3c，后缀 `_P6SP`）

G1 `hslabsLoc_cstar_of_hgood_P6SP` 的 binder `hstayLoc`（固定 `c⋆ := 1/(2·max(Ctime′, 1))` 档）=
WBADAPT `hanchor0_eventSlab_prod_star_P6WA2` 的 `hstayLocStar`。本文件把 G3b 逐点结论包成序列形：
* `cstar_numerics_P6SP`（PROVED，纯实数）：逐点选 `ℓ := κ/√(Qb·R)`、`Kc := Qb·R/κ²`，CXJD 全部数值前提只剩
  与 z 无关的 `L` 门槛；
* `ObservedHistory.hstayLocStar_of_firstExit_P6SP`（PROVED ⇐ CXJD 结构输入族）：结论 = `hstayLoc`（c⋆ 档）逐字。
* consumer `ObservedHistory.hslabsLocStar_of_hgood_firstExit_P6SP`（PROVED ⇐ 同上 + `hwin`）：
  G1 c⋆ 版 producer 的 `hstayLoc` 付清 ⇒ c⋆ 档 `hslabsLoc` 只剩 hgood 时间分量 + CXJD 结构输入族。
剩余 binder（全部是 CXJD 结构输入，无 anchor 球界、无导数阈值槽）：K0 seed、HI、`1 ≤ R`、`1 ≤ R·aSeed`、
records 族（`T₀ ≤ aSeed`）、`hprotC`（⇐ `hprotC_of_ceiling_CXJD`：ceiling + scale 分离）、`hdσ`。
∀ `c` 版仍不可由一次 ODE 得到（见 G3）。**不声称 J10 已去。**
-/

set_option autoImplicit false

noncomputable section

open Set Filter Function
open DifferentialGeometry DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.CheegerGromovCompactness
open DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood
open DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn
open DifferentialGeometry.Integral.Measure
open scoped Manifold NNReal Topology ContDiff ENNReal

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

universe u

/-- **c⋆ 数值（`_P6SP`，PROVED，纯实数）**：`ℓ := κ/√(Qb·R)`、`Kc := Qb·R/κ²`，
`κ := min(min(r/50, ρ/2), min(1, 1/(2√3(9 + 2e⁴))))`；`Qb ≥ 1`、`R ≥ 1`、`2ρ ≤ L/2`、
`Rad + 8c/κ < L/2` ⇒ CXJD / G3 的全部数值前提（`hℓ`、`hKℓ`、`hℓr`、`hKr`、`hKC`、`hℓρ`、`hρL`、
`hnum`，`T := c/Qb`、`D := Rad`）。
与 `z` 无关的门槛只有 `L`（`L → ∞` 时 eventually 成立）。 -/
theorem cstar_numerics_P6SP {r ρ c Qb R Rad L κ : ℝ} (hr : 0 < r) (hρ : 0 < ρ) (hc : 0 ≤ c)
    (hQb : 1 ≤ Qb) (hR : 1 ≤ R)
    (hκdef : κ = min (min (r / 50) (ρ / 2))
      (min 1 (1 / (2 * Real.sqrt 3 * (9 + 2 * Real.exp 4)))))
    (hL1 : 2 * ρ ≤ L / 2) (hL2 : Rad + 8 * c / κ < L / 2) :
    0 < κ / Real.sqrt (Qb * R) ∧ Qb * R / κ ^ 2 * (κ / Real.sqrt (Qb * R)) ^ 2 ≤ 1 ∧
      κ / Real.sqrt (Qb * R) ≤ r / 50 ∧ 1 / r ^ 2 ≤ Qb * R / κ ^ 2 ∧
      2 * Real.sqrt 3 * (6 * Qb / 2 + max (6 * Qb) (2 * Real.exp 4)) * R ≤ Qb * R / κ ^ 2 ∧
      κ / Real.sqrt (Qb * R) ≤ ρ / Real.sqrt (2 * (Qb * R)) ∧
      2 * (ρ / Real.sqrt (2 * (Qb * R))) ≤ L / 2 / Real.sqrt R ∧
      Rad / Real.sqrt R + 8 / (κ / Real.sqrt (Qb * R)) * (c / Qb / R) < L / 2 / Real.sqrt R := by
  set C₁ : ℝ := 2 * Real.sqrt 3 * (9 + 2 * Real.exp 4) with hC₁
  have hs3 : 0 < Real.sqrt 3 := Real.sqrt_pos.mpr (by norm_num)
  have he : 0 < Real.exp 4 := Real.exp_pos 4
  have hC₁1 : 1 ≤ C₁ := by
    have : (1 : ℝ) ≤ Real.sqrt 3 := by
      rw [show (1 : ℝ) = Real.sqrt 1 by simp]
      exact Real.sqrt_le_sqrt (by norm_num)
    rw [hC₁]
    nlinarith
  have hκpos : 0 < κ := by
    rw [hκdef]
    refine lt_min (lt_min (by positivity) (by positivity)) (lt_min one_pos ?_)
    exact one_div_pos.mpr (by linarith)
  have hκr : κ ≤ r / 50 := hκdef ▸ (min_le_left _ _).trans (min_le_left _ _)
  have hκρ : κ ≤ ρ / 2 := hκdef ▸ (min_le_left _ _).trans (min_le_right _ _)
  have hκ1 : κ ≤ 1 := hκdef ▸ (min_le_right _ _).trans (min_le_left _ _)
  have hκC : κ ≤ 1 / C₁ := hκdef ▸ (min_le_right _ _).trans (min_le_right _ _)
  have hQR1 : 1 ≤ Qb * R := by nlinarith
  have hQR0 : 0 < Qb * R := by linarith
  have hsQR : 0 < Real.sqrt (Qb * R) := Real.sqrt_pos.mpr hQR0
  have hsQR1 : 1 ≤ Real.sqrt (Qb * R) := by
    rw [show (1 : ℝ) = Real.sqrt 1 by simp]
    exact Real.sqrt_le_sqrt hQR1
  have hsR : 0 < Real.sqrt R := Real.sqrt_pos.mpr (by linarith)
  have hsq : Real.sqrt (Qb * R) ^ 2 = Qb * R := Real.sq_sqrt hQR0.le
  have hκ2 : κ ^ 2 ≤ 1 / C₁ := by nlinarith
  refine ⟨div_pos hκpos hsQR, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [div_pow, hsq]
    have : Qb * R / κ ^ 2 * (κ ^ 2 / (Qb * R)) = 1 := by field_simp
    rw [this]
  · exact (div_le_self hκpos.le hsQR1).trans hκr
  · have hκr' : κ ^ 2 ≤ r ^ 2 := by
      have : κ ≤ r := hκr.trans (by linarith)
      nlinarith
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    nlinarith
  · have hmax : 6 * Qb / 2 + max (6 * Qb) (2 * Real.exp 4) ≤ (9 + 2 * Real.exp 4) * Qb := by
      have : max (6 * Qb) (2 * Real.exp 4) ≤ 6 * Qb + 2 * Real.exp 4 :=
        max_le (by linarith) (by linarith)
      nlinarith
    have h1 : 2 * Real.sqrt 3 * (6 * Qb / 2 + max (6 * Qb) (2 * Real.exp 4)) * R ≤
        C₁ * (Qb * R) := by
      rw [hC₁]
      have hR0 : 0 ≤ R := by linarith
      have := mul_le_mul_of_nonneg_left hmax (by positivity : (0 : ℝ) ≤ 2 * Real.sqrt 3)
      nlinarith
    have h2 : C₁ ≤ 1 / κ ^ 2 := by
      rw [le_div_iff₀ (by positivity)]
      have := mul_le_mul_of_nonneg_left hκ2 (by linarith : (0 : ℝ) ≤ C₁)
      rw [mul_one_div_cancel (by linarith)] at this
      linarith
    calc _ ≤ C₁ * (Qb * R) := h1
      _ ≤ 1 / κ ^ 2 * (Qb * R) := mul_le_mul_of_nonneg_right h2 hQR0.le
      _ = Qb * R / κ ^ 2 := by ring
  · have hs2 : Real.sqrt (2 * (Qb * R)) = Real.sqrt 2 * Real.sqrt (Qb * R) :=
      Real.sqrt_mul (by norm_num) _
    have hs2le : Real.sqrt 2 ≤ 2 := by
      rw [show (2 : ℝ) = Real.sqrt 4 by
        rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]]
      exact Real.sqrt_le_sqrt (by norm_num)
    have hs20 : 0 < Real.sqrt 2 := Real.sqrt_pos.mpr (by norm_num)
    rw [hs2, ← div_div]
    apply div_le_div_of_nonneg_right _ hsQR.le
    rw [le_div_iff₀ hs20]
    nlinarith
  · have hle : Real.sqrt R ≤ Real.sqrt (2 * (Qb * R)) := Real.sqrt_le_sqrt (by nlinarith)
    have h1 : ρ / Real.sqrt (2 * (Qb * R)) ≤ ρ / Real.sqrt R :=
      div_le_div_of_nonneg_left hρ.le hsR hle
    have h2 : 2 * (ρ / Real.sqrt R) ≤ L / 2 / Real.sqrt R := by
      rw [← mul_div_assoc]
      exact div_le_div_of_nonneg_right hL1 hsR.le
    linarith
  · have hsle : Real.sqrt R ≤ Real.sqrt (Qb * R) := Real.sqrt_le_sqrt (by nlinarith)
    have hterm : 8 / (κ / Real.sqrt (Qb * R)) * (c / Qb / R) =
        8 * c / κ / Real.sqrt (Qb * R) := by
      set s := Real.sqrt (Qb * R) with hs
      rw [div_div c Qb R, ← hsq]
      field_simp
    have hterm2 : 8 * c / κ / Real.sqrt (Qb * R) ≤ 8 * c / κ / Real.sqrt R :=
      div_le_div_of_nonneg_left (by positivity) hsR hsle
    rw [hterm]
    calc Rad / Real.sqrt R + 8 * c / κ / Real.sqrt (Qb * R)
        ≤ Rad / Real.sqrt R + 8 * c / κ / Real.sqrt R := by linarith
      _ = (Rad + 8 * c / κ) / Real.sqrt R := by ring
      _ < L / 2 / Real.sqrt R := div_lt_div_of_pos_right hL2 hsR

/-- **G3c：c⋆ 版 `hstayLoc` 的序列层 producer（`_P6SP`，PROVED ⇐ CXJD 结构输入族）**：结论 = G1
`hslabsLoc_cstar_of_hgood_P6SP` 的 binder `hstayLoc`（c⋆ 档）逐字 = WBADAPT `hstayLocStar`
（`(K n).toHistory` 帧；`Kh := fun n => (K n).toHistory` 时差一步 β）。
逐 `(n, z)`：`Qb := max(R_G(t,z)/R, Cg, 1)`、`T := c⋆/Qb`、`ℓ := κ/√(Qb·R)`、`Kc := Qb·R/κ²`
（`cstar_numerics_P6SP`），喂 G3b `stay_cstar_prefix_of_firstExit_P6SP`。eventual 只用 `L → ∞`
（门槛与 z 无关）；`haL` / `hRa` / `hT₀` 由 c⋆ guard（`t − v' ≤ 1/R`）与 `aSeed ≤ v'` 给。
剩余 binder = CXJD 结构输入族：K0 seed（`hsmall` / `hclock`，固定 `r`）、HI（`hpin`）、`1 ≤ R`、
`hRa`（`1 ≤ R·aSeed`）、records 族（`hT₀ : T₀ ≤ aSeed`、`hOld`、`hcan`、`hacc`、`hDm`）、`hprotC`
（对所有 `v' ≥ aSeed` 与所有自 `activeStage v'` 起的 trace；⇐ `hprotC_of_ceiling_CXJD`）、`hdσ`。
无 anchor 球界、无导数阈值槽。 -/
theorem ObservedHistory.hstayLocStar_of_firstExit_P6SP {eps C1' C2' : ℝ} {Ctime' : ℝ≥0} {Cg : ℝ}
    (hC2 : 0 ≤ C2') (hCg : 1 ≤ Cg) {K : ℕ → RetainedCoreHistory.{u}}
    {j : ∀ n, Fin (K n).eventCount} {t : ℕ → ℝ} (hjt : ∀ n, (K n).time (j n).castSucc < t n)
    (htj : ∀ n, t n < (K n).time (j n).succ) (σ : ∀ n, Icc (0 : ℝ) (K n).toHistory.horizon)
    (hσ : ∀ n, (σ n : ℝ) = t n) (y : ∀ n, ((K n).toHistory.stageAt (σ n)).Carrier)
    (yG : ∀ n, ((K n).stage (j n).castSucc).Carrier) (hyG : ∀ n, HEq (y n) (yG n))
    (R : ℕ → ℝ) (hR : ∀ n, 0 < R n) (hR1 : ∀ n, 1 ≤ R n)
    (hRn : ∀ n, R n = ((K n).toHistory.event (j n)).incoming.flow.scalar (t n) (yG n))
    (Tn aSeed : ∀ n, Icc (0 : ℝ) (K n).toHistory.horizon) (haT : ∀ n, aSeed n ≤ Tn n)
    (hsT : ∀ n, σ n ≤ Tn n) (has : ∀ n, aSeed n ≤ σ n)
    (pT : ∀ n, ((K n).toHistory.stageAt (Tn n)).Carrier)
    (seedTrace : ∀ n, BackwardPointTrace (K n).toHistory ((K n).toHistory.activeStage (aSeed n))
      ((K n).toHistory.activeStage (Tn n)) ((K n).toHistory.activeStage_mono (haT n)) (pT n))
    (L : ℕ → ℝ) (hL : Tendsto L atTop atTop)
    (hgood : ∀ n, ∀ (v : Icc (0 : ℝ) (K n).toHistory.horizon) (hav : aSeed n ≤ v) (hvs : v ≤ σ n),
      (σ n : ℝ) - L n ^ 2 / R n ≤ (v : ℝ) →
      ∀ z : ((K n).toHistory.stageAt v).Carrier,
        riemannianEDistOf ((K n).toHistory.stageMetric ((K n).toHistory.activeStage v) v)
            ((seedTrace n).point ((K n).toHistory.activeStage v)
              ((K n).toHistory.activeStage_mono hav)
              ((K n).toHistory.activeStage_mono (hvs.trans (hsT n)))) z ≤
          riemannianEDistOf ((K n).toHistory.stageMetric ((K n).toHistory.activeStage (σ n))
              (σ n))
              ((seedTrace n).point ((K n).toHistory.activeStage (σ n))
                ((K n).toHistory.activeStage_mono (has n))
                ((K n).toHistory.activeStage_mono (hsT n))) (y n) +
            ENNReal.ofReal (L n / Real.sqrt (R n)) →
        Cg * R n ≤ metricScalarAt ((K n).toHistory.stageMetric ((K n).toHistory.activeStage v) v)
          z →
        (K n).toHistory.HasSpatialCanonicalTimeControl eps C1' C2' Ctime' v z)
    {r : ℝ} (hr : 0 < r)
    (hsmall : ∀ n, GC.LongTime.hasSmallParabolicCurvature (K n).toHistory (Tn n) (pT n) r)
    (hclock : ∀ n, (aSeed n : ℝ) = (Tn n : ℝ) - r ^ 2)
    (a₀ : ℕ → ℝ) (ha₀ : ∀ n, 0 ≤ a₀ n)
    (hpin : ∀ n (s : Icc (0 : ℝ) (K n).toHistory.horizon)
      (x : ((K n).toHistory.stageAt s).Carrier),
      InFixedHamiltonIveyRegion ((K n).toHistory.stageMetric ((K n).toHistory.activeStage s) s)
        (a₀ n + s) x)
    (hRa : ∀ n, 1 ≤ R n * aSeed n)
    (q : ℕ → CutoffParameters) (T₀ : ℕ → ℝ) (hT₀ : ∀ n, T₀ n ≤ aSeed n)
    (records : ∀ n (e : Fin (K n).eventCount), T₀ n ≤ (K n).toHistory.time e.succ →
      GeometricCutoffRecord (K n).toHistory e (q n))
    (hOld : ∀ n (e : Fin (K n).eventCount), T₀ n ≤ (K n).toHistory.time e.succ →
      ((K n).toHistory.event e).old = ((K n).toHistory.event e).transition.trace.retainedCore)
    (hcan : ∀ n (e : Fin (K n).eventCount) (he : T₀ n ≤ (K n).toHistory.time e.succ) b,
      ((records n e he).static b).hasCanonicalWindow)
    (hacc : ∀ n, (q n).modelAccuracy ≤ 1 / 2)
    (hDm : ∀ n, StandardCap.transitionEnd + 10 < (q n).modelRadius)
    (hprotC : ∀ n (v' : Icc (0 : ℝ) (K n).toHistory.horizon) (hav : aSeed n ≤ v')
      (hvs : v' ≤ σ n) (z'' : ((K n).toHistory.stageAt (σ n)).Carrier)
      (A : BackwardPointTrace (K n).toHistory ((K n).toHistory.activeStage v')
          ((K n).toHistory.activeStage (σ n)) ((K n).toHistory.activeStage_mono hvs) z'')
      (e : Fin (K n).eventCount) (h1 : (K n).toHistory.activeStage (aSeed n) ≤ e.castSucc)
      (h2 : e.succ ≤ (K n).toHistory.activeStage (Tn n))
      (h3 : (K n).toHistory.activeStage v' ≤ e.castSucc)
      (h4 : e.succ ≤ (K n).toHistory.activeStage (σ n))
      (he : T₀ n ≤ (K n).toHistory.time e.succ),
      (∀ (w : Icc (0 : ℝ) (K n).toHistory.horizon) (hw : v' ≤ w) (hwσ : w ≤ σ n),
        (K n).toHistory.time e.succ ≤ (w : ℝ) →
        riemannianEDistOf ((K n).toHistory.stageMetric ((K n).toHistory.activeStage w) w)
            ((seedTrace n).point ((K n).toHistory.activeStage w)
              ((K n).toHistory.activeStage_mono (hav.trans hw))
              ((K n).toHistory.activeStage_mono (hwσ.trans (hsT n))))
            (A.point ((K n).toHistory.activeStage w) ((K n).toHistory.activeStage_mono hw)
              ((K n).toHistory.activeStage_mono hwσ)) <
          riemannianEDistOf ((K n).toHistory.stageMetric ((K n).toHistory.activeStage (σ n))
              (σ n))
              ((seedTrace n).point ((K n).toHistory.activeStage (σ n))
                ((K n).toHistory.activeStage_mono (has n))
                ((K n).toHistory.activeStage_mono (hsT n))) (y n) +
            ENNReal.ofReal (L n / 2 / Real.sqrt (R n))) → ∀ b,
      (seedTrace n).point e.succ (h1.trans e.castSucc_lt_succ.le) h2 ∉
          ((records n e he).static b).window ''
            {w : standardCapWindow (q n).modelRadius | ‖w.val‖ ≤ StandardCap.transitionEnd + 10} ∧
        A.point e.succ (h3.trans e.castSucc_lt_succ.le) h4 ∉
          ((records n e he).static b).window ''
            {w : standardCapWindow (q n).modelRadius | ‖w.val‖ ≤ StandardCap.transitionEnd + 10})
    (hdσ : ∀ n, riemannianEDistOf ((K n).toHistory.stageMetric
        ((K n).toHistory.activeStage (σ n)) (σ n))
        ((seedTrace n).point ((K n).toHistory.activeStage (σ n))
          ((K n).toHistory.activeStage_mono (has n))
          ((K n).toHistory.activeStage_mono (hsT n))) (y n) ≠ ⊤) :
    ∀ Rad B : ℝ, ∀ᶠ n in atTop,
      ∀ i : Fin ((K n).prefixAt (j n).castSucc).eventCount,
      ∀ (first : Fin (((K n).prefixAt (j n).castSucc).eventCount + 1)) (hf : first ≤ i.castSucc),
      ∀ z ∈ riemannianBallOf (((K n).toHistory.event (j n)).incoming.flow.base.metric (t n)) (yG n)
          (Rad / Real.sqrt (((K n).toHistory.event (j n)).incoming.flow.scalar (t n) (yG n))),
      ∀ Btr : BackwardPointTrace ((K n).prefixAt (j n).castSucc).toHistory first
        (Fin.last ((K n).prefixAt (j n).castSucc).eventCount) (Fin.le_last first) z,
      ∀ v ∈ Ioo (((K n).prefixAt (j n).castSucc).time i.castSucc)
        (((K n).prefixAt (j n).castSucc).time i.succ),
      t n - B / ((K n).toHistory.event (j n)).incoming.flow.scalar (t n) (yG n) ≤ v →
      (t n - v) * max (Cg * R n) (((K n).toHistory.event (j n)).incoming.flow.scalar (t n) z) ≤
        1 / (2 * max (Ctime' : ℝ) 1) →
      Cg * R n < (((K n).prefixAt (j n).castSucc).toHistory.event i).incoming.flow.scalar v
        (Btr.point i.castSucc hf (Fin.le_last _)) →
      ∀ (v' : Icc (0 : ℝ) (K n).toHistory.horizon) (hav : aSeed n ≤ v') (hvs : v' ≤ σ n),
        (v' : ℝ) = v →
      ∀ x : ((K n).toHistory.stageAt v').Carrier, HEq x (Btr.point i.castSucc hf (Fin.le_last _)) →
        riemannianEDistOf ((K n).toHistory.stageMetric ((K n).toHistory.activeStage v') v')
            ((seedTrace n).point ((K n).toHistory.activeStage v')
              ((K n).toHistory.activeStage_mono hav)
              ((K n).toHistory.activeStage_mono (hvs.trans (hsT n)))) x ≤
          riemannianEDistOf ((K n).toHistory.stageMetric ((K n).toHistory.activeStage (σ n)) (σ n))
              ((seedTrace n).point ((K n).toHistory.activeStage (σ n))
                ((K n).toHistory.activeStage_mono (has n))
                ((K n).toHistory.activeStage_mono (hsT n))) (y n) +
            ENNReal.ofReal (L n / Real.sqrt (R n)) := by
  obtain ⟨κ, hκdef⟩ : ∃ κ : ℝ, κ = min (min (r / 50) (localPropagationRadius C2' / 2))
      (min 1 (1 / (2 * Real.sqrt 3 * (9 + 2 * Real.exp 4)))) := ⟨_, rfl⟩
  have hρ : 0 < localPropagationRadius C2' := localPropagationRadius_pos hC2
  intro Rad B
  filter_upwards [hL.eventually_ge_atTop (max (max (4 * localPropagationRadius C2')
    (2 * (Rad + 8 * (1 / (2 * max (Ctime' : ℝ) 1)) / κ) + 2)) 1)] with n hLn
  intro i first hf z hz Btr v hv hBv hcv hq v' hav hvs hvv x hx
  subst hvv
  have hm1 : (1 : ℝ) ≤ max (Ctime' : ℝ) 1 := le_max_right _ _
  have hc0 : (0 : ℝ) ≤ 1 / (2 * max (Ctime' : ℝ) 1) := by positivity
  have hc1 : 1 / (2 * max (Ctime' : ℝ) 1) ≤ 1 := by
    rw [div_le_one (by linarith)]
    linarith
  have hL4 : 4 * localPropagationRadius C2' ≤ L n :=
    ((le_max_left _ _).trans (le_max_left _ _)).trans hLn
  have hL5 : 2 * (Rad + 8 * (1 / (2 * max (Ctime' : ℝ) 1)) / κ) + 2 ≤ L n :=
    ((le_max_right _ _).trans (le_max_left _ _)).trans hLn
  have hL6 : (1 : ℝ) ≤ L n := (le_max_right _ _).trans hLn
  have hlast : ((K n).prefixAt (j n).castSucc).time i.succ ≤ (K n).time (j n).castSucc :=
    (((K n).prefixAt (j n).castSucc).time_strictMono.monotone (Fin.le_last _)).trans_eq
      ((K n).prefixAt_time_last _)
  have hvt : (v' : ℝ) < t n := hv.2.trans_le (hlast.trans (hjt n).le)
  have htv0 : 0 ≤ t n - v' := by linarith
  have hRle : (t n - v') * R n ≤ 1 := by
    have h3 := mul_le_mul_of_nonneg_left ((show R n ≤ Cg * R n by nlinarith [hR n]).trans
      (le_max_left (Cg * R n) (((K n).toHistory.event (j n)).incoming.flow.scalar (t n) z)))
      htv0
    linarith
  have hTv : t n - v' ≤ 1 / R n := by
    rw [le_div_iff₀ (hR n)]
    exact hRle
  have hLR : 1 / R n ≤ L n ^ 2 / R n :=
    div_le_div_of_nonneg_right (by nlinarith) (hR n).le
  have haL : (σ n : ℝ) - L n ^ 2 / R n ≤ v' := by
    rw [hσ n]
    linarith
  have hav' : (aSeed n : ℝ) ≤ v' := hav
  have hRa' : 1 ≤ R n * v' := by
    have := mul_le_mul_of_nonneg_left hav' (hR n).le
    linarith [hRa n]
  have hT₀' : T₀ n ≤ (v' : ℝ) := (hT₀ n).trans hav'
  rw [← hRn n] at hz
  obtain ⟨hℓ, hKℓ, hℓr, hKr, hKC, hℓρ, hρL, hnum⟩ := cstar_numerics_P6SP
    (Qb := max (max (((K n).toHistory.event (j n)).incoming.flow.scalar (t n) z / R n) Cg) 1)
    (R := R n) (Rad := Rad) (L := L n) hr hρ hc0 (le_max_right _ _) (hR1 n) hκdef (by linarith)
    (by linarith)
  exact ObservedHistory.stay_cstar_prefix_of_firstExit_P6SP hC2 hCg (K n) (j n) (hjt n) (htj n)
    (hσ n) (haT n) (hsmall n) (hclock n) (seedTrace n) (ha₀ n) (hpin n) (hsT n) (has n) (y n)
    (yG n) (hyG n) (L n) (hR n) (hgood n) i first hf z hz Btr v' hv.1 hv.2 hav hvs haL hRa' rfl
    rfl hcv hℓ hKℓ hℓr hKr hKC hℓρ hρL hT₀' (records n) (hOld n) (hcan n) (hacc n) (hDm n)
    (fun z'' _ A => hprotC n v' hav hvs z'' A) (hdσ n) hnum x hx

/-- **consumer（`_P6SP`，PROVED ⇐ CXJD 结构输入族 + hgood + `hwin`）**：G1 c⋆ 版 producer
`hslabsLoc_cstar_of_hgood_P6SP` 的 binder `hstayLoc` 由 `hstayLocStar_of_firstExit_P6SP` 付清 ⇒ c⋆ 档
`hslabsLoc`（前 slab 导数槽）只剩 hgood 时间分量 + CXJD 结构输入族，无 `hstayLoc`。 -/
theorem ObservedHistory.hslabsLocStar_of_hgood_firstExit_P6SP {eps C1' C2' : ℝ}
    {Ctime' : ℝ≥0} {Cg : ℝ}
    (hC2 : 0 ≤ C2') (hCg : 1 ≤ Cg) {K : ℕ → RetainedCoreHistory.{u}}
    {j : ∀ n, Fin (K n).eventCount} {t : ℕ → ℝ} (hjt : ∀ n, (K n).time (j n).castSucc < t n)
    (htj : ∀ n, t n < (K n).time (j n).succ) (σ : ∀ n, Icc (0 : ℝ) (K n).toHistory.horizon)
    (hσ : ∀ n, (σ n : ℝ) = t n) (y : ∀ n, ((K n).toHistory.stageAt (σ n)).Carrier)
    (yG : ∀ n, ((K n).stage (j n).castSucc).Carrier) (hyG : ∀ n, HEq (y n) (yG n))
    (R : ℕ → ℝ) (hR : ∀ n, 0 < R n) (hR1 : ∀ n, 1 ≤ R n)
    (hRn : ∀ n, R n = ((K n).toHistory.event (j n)).incoming.flow.scalar (t n) (yG n))
    (Tn aSeed : ∀ n, Icc (0 : ℝ) (K n).toHistory.horizon) (haT : ∀ n, aSeed n ≤ Tn n)
    (hsT : ∀ n, σ n ≤ Tn n) (has : ∀ n, aSeed n ≤ σ n)
    (pT : ∀ n, ((K n).toHistory.stageAt (Tn n)).Carrier)
    (seedTrace : ∀ n, BackwardPointTrace (K n).toHistory ((K n).toHistory.activeStage (aSeed n))
      ((K n).toHistory.activeStage (Tn n)) ((K n).toHistory.activeStage_mono (haT n)) (pT n))
    (L : ℕ → ℝ) (hL : Tendsto L atTop atTop)
    (hgood : ∀ n, ∀ (v : Icc (0 : ℝ) (K n).toHistory.horizon) (hav : aSeed n ≤ v) (hvs : v ≤ σ n),
      (σ n : ℝ) - L n ^ 2 / R n ≤ (v : ℝ) →
      ∀ z : ((K n).toHistory.stageAt v).Carrier,
        riemannianEDistOf ((K n).toHistory.stageMetric ((K n).toHistory.activeStage v) v)
            ((seedTrace n).point ((K n).toHistory.activeStage v)
              ((K n).toHistory.activeStage_mono hav)
              ((K n).toHistory.activeStage_mono (hvs.trans (hsT n)))) z ≤
          riemannianEDistOf ((K n).toHistory.stageMetric ((K n).toHistory.activeStage (σ n))
              (σ n))
              ((seedTrace n).point ((K n).toHistory.activeStage (σ n))
                ((K n).toHistory.activeStage_mono (has n))
                ((K n).toHistory.activeStage_mono (hsT n))) (y n) +
            ENNReal.ofReal (L n / Real.sqrt (R n)) →
        Cg * R n ≤ metricScalarAt ((K n).toHistory.stageMetric ((K n).toHistory.activeStage v) v)
          z →
        (K n).toHistory.HasSpatialCanonicalTimeControl eps C1' C2' Ctime' v z)
    {r : ℝ} (hr : 0 < r)
    (hsmall : ∀ n, GC.LongTime.hasSmallParabolicCurvature (K n).toHistory (Tn n) (pT n) r)
    (hclock : ∀ n, (aSeed n : ℝ) = (Tn n : ℝ) - r ^ 2)
    (a₀ : ℕ → ℝ) (ha₀ : ∀ n, 0 ≤ a₀ n)
    (hpin : ∀ n (s : Icc (0 : ℝ) (K n).toHistory.horizon)
      (x : ((K n).toHistory.stageAt s).Carrier),
      InFixedHamiltonIveyRegion ((K n).toHistory.stageMetric ((K n).toHistory.activeStage s) s)
        (a₀ n + s) x)
    (hRa : ∀ n, 1 ≤ R n * aSeed n)
    (q : ℕ → CutoffParameters) (T₀ : ℕ → ℝ) (hT₀ : ∀ n, T₀ n ≤ aSeed n)
    (records : ∀ n (e : Fin (K n).eventCount), T₀ n ≤ (K n).toHistory.time e.succ →
      GeometricCutoffRecord (K n).toHistory e (q n))
    (hOld : ∀ n (e : Fin (K n).eventCount), T₀ n ≤ (K n).toHistory.time e.succ →
      ((K n).toHistory.event e).old = ((K n).toHistory.event e).transition.trace.retainedCore)
    (hcan : ∀ n (e : Fin (K n).eventCount) (he : T₀ n ≤ (K n).toHistory.time e.succ) b,
      ((records n e he).static b).hasCanonicalWindow)
    (hacc : ∀ n, (q n).modelAccuracy ≤ 1 / 2)
    (hDm : ∀ n, StandardCap.transitionEnd + 10 < (q n).modelRadius)
    (hprotC : ∀ n (v' : Icc (0 : ℝ) (K n).toHistory.horizon) (hav : aSeed n ≤ v')
      (hvs : v' ≤ σ n) (z'' : ((K n).toHistory.stageAt (σ n)).Carrier)
      (A : BackwardPointTrace (K n).toHistory ((K n).toHistory.activeStage v')
          ((K n).toHistory.activeStage (σ n)) ((K n).toHistory.activeStage_mono hvs) z'')
      (e : Fin (K n).eventCount) (h1 : (K n).toHistory.activeStage (aSeed n) ≤ e.castSucc)
      (h2 : e.succ ≤ (K n).toHistory.activeStage (Tn n))
      (h3 : (K n).toHistory.activeStage v' ≤ e.castSucc)
      (h4 : e.succ ≤ (K n).toHistory.activeStage (σ n))
      (he : T₀ n ≤ (K n).toHistory.time e.succ),
      (∀ (w : Icc (0 : ℝ) (K n).toHistory.horizon) (hw : v' ≤ w) (hwσ : w ≤ σ n),
        (K n).toHistory.time e.succ ≤ (w : ℝ) →
        riemannianEDistOf ((K n).toHistory.stageMetric ((K n).toHistory.activeStage w) w)
            ((seedTrace n).point ((K n).toHistory.activeStage w)
              ((K n).toHistory.activeStage_mono (hav.trans hw))
              ((K n).toHistory.activeStage_mono (hwσ.trans (hsT n))))
            (A.point ((K n).toHistory.activeStage w) ((K n).toHistory.activeStage_mono hw)
              ((K n).toHistory.activeStage_mono hwσ)) <
          riemannianEDistOf ((K n).toHistory.stageMetric ((K n).toHistory.activeStage (σ n))
              (σ n))
              ((seedTrace n).point ((K n).toHistory.activeStage (σ n))
                ((K n).toHistory.activeStage_mono (has n))
                ((K n).toHistory.activeStage_mono (hsT n))) (y n) +
            ENNReal.ofReal (L n / 2 / Real.sqrt (R n))) → ∀ b,
      (seedTrace n).point e.succ (h1.trans e.castSucc_lt_succ.le) h2 ∉
          ((records n e he).static b).window ''
            {w : standardCapWindow (q n).modelRadius | ‖w.val‖ ≤ StandardCap.transitionEnd + 10} ∧
        A.point e.succ (h3.trans e.castSucc_lt_succ.le) h4 ∉
          ((records n e he).static b).window ''
            {w : standardCapWindow (q n).modelRadius | ‖w.val‖ ≤ StandardCap.transitionEnd + 10})
    (hdσ : ∀ n, riemannianEDistOf ((K n).toHistory.stageMetric
        ((K n).toHistory.activeStage (σ n)) (σ n))
        ((seedTrace n).point ((K n).toHistory.activeStage (σ n))
          ((K n).toHistory.activeStage_mono (has n))
          ((K n).toHistory.activeStage_mono (hsT n))) (y n) ≠ ⊤)
    (hwin : ∀ T : ℝ, 0 < T → ∀ᶠ n in atTop, (aSeed n : ℝ) ≤ σ n - T / R n) :
    ∀ Rad B : ℝ, ∀ᶠ n in atTop,
      ∀ i : Fin ((K n).prefixAt (j n).castSucc).eventCount,
      ∀ (first : Fin (((K n).prefixAt (j n).castSucc).eventCount + 1)) (hf : first ≤ i.castSucc),
      ∀ z ∈ riemannianBallOf (((K n).toHistory.event (j n)).incoming.flow.base.metric (t n)) (yG n)
          (Rad / Real.sqrt (((K n).toHistory.event (j n)).incoming.flow.scalar (t n) (yG n))),
      ∀ Btr : BackwardPointTrace ((K n).prefixAt (j n).castSucc).toHistory first
        (Fin.last ((K n).prefixAt (j n).castSucc).eventCount) (Fin.le_last first) z,
      ∀ v ∈ Ioo (((K n).prefixAt (j n).castSucc).time i.castSucc)
        (((K n).prefixAt (j n).castSucc).time i.succ),
      t n - B / ((K n).toHistory.event (j n)).incoming.flow.scalar (t n) (yG n) ≤ v →
      (t n - v) * max (Cg * R n) (((K n).toHistory.event (j n)).incoming.flow.scalar (t n) z) ≤
        1 / (2 * max (Ctime' : ℝ) 1) →
      Cg * R n < (((K n).prefixAt (j n).castSucc).toHistory.event i).incoming.flow.scalar v
        (Btr.point i.castSucc hf (Fin.le_last _)) →
      |derivWithin (fun w =>
          (((K n).prefixAt (j n).castSucc).toHistory.event i).incoming.flow.scalar w
            (Btr.point i.castSucc hf (Fin.le_last _))) (Iic v) v| ≤
        Ctime' * (((K n).prefixAt (j n).castSucc).toHistory.event i).incoming.flow.scalar v
          (Btr.point i.castSucc hf (Fin.le_last _)) ^ 2 :=
  ObservedHistory.hslabsLoc_cstar_of_hgood_P6SP hCg hjt htj σ hσ y yG R hR Tn aSeed haT hsT has pT
    seedTrace L hL hgood hwin
    (ObservedHistory.hstayLocStar_of_firstExit_P6SP hC2 hCg hjt htj σ hσ y yG hyG R hR hR1 hRn Tn
      aSeed haT hsT has pT seedTrace L hL hgood hr hsmall hclock a₀ ha₀ hpin hRa q T₀ hT₀ records
      hOld hcan hacc hDm hprotC hdσ)

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
