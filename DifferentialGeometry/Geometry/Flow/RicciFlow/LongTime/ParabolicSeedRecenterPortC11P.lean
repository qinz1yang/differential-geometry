import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.ParabolicSeedVolume
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.HistoryParabolicSeedRicci

/-!
# S-CH11-FIX9 port of astra `ParabolicSeedRecenter`（`PortC11P`）

来源：donor `ParabolicSeedRecenter.lean`（Jui-Hui `chapter11-astra` @ `a73e4bdbfd`）。
donor 文本在本树 elaboration 失败。本 port 只有 elaboration 层面修补（no statement / definition /
proof idea altered；不加 `set_option`）：
* `open private ObservedHistory.exists_past_seed_core_traces_of_metric_distortion from` 指向
  `HistoryParabolicSeedRicci` 原路径，而原路径已是 FIX5 的 port + shim（private 声明在
  `HistoryParabolicSeedRicciPortC11P`）→ 改指 `…PortC11P`；
* `hdistortion` 的 calc 链 `≤ , < , ≤` 的结论是 `<`，而 `have` 要 `≤`（本树 calc 不自动弱化）→
  先 `refine le_of_lt ?_`；
* 调用处 `exists_past_seed_core_traces_of_metric_distortion …`：`open private` 之后只能用
  `ObservedHistory.` 全名（`open …Topology` 下 `ObservedHistory.xxx` 可解析，裸名不行，报 unknown
  identifier 后连带 `obtain` 的 rcases 报 `?m is not an inductive datatype`）→ 写全名；
* 陈述里未被引用的 binder `hA`（`1 < A` 只在陈述里出现，证明里不用）→ `_hA`（unusedVariables）。

原路径 `ParabolicSeedRecenter` 是只 import 本文件的 re-export shim。
-/

set_option autoImplicit false
noncomputable section

open Set DifferentialGeometry
open DifferentialGeometry.Geometry.Curvature DifferentialGeometry.Tensor0SBundle
open DifferentialGeometry.Geometry.Collapse
open DifferentialGeometry.PDE.RicciFlow DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
open scoped Manifold ContDiff ENNReal

open private ObservedHistory.exists_past_seed_core_traces_of_metric_distortion from
  DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.HistoryParabolicSeedRicciPortC11P

namespace GC.LongTime
universe u

/-- The original strong seed supplies a smaller strong seed around its same
selected trace point at every time in the closed later half of its depth. -/
theorem hasSmallParabolicCurvature.earlier_seed_on_half_depth
    {H : ObservedHistory.{u}} {T aSeed : Icc (0 : ℝ) H.horizon}
    (haT : aSeed ≤ T) (p : (H.stageAt T).Carrier) (r A : ℝ)
    (_hA : 1 < A) (htime : 2 * r ^ 2 < (T : ℝ))
    (hclock : (aSeed : ℝ) = (T : ℝ) - r ^ 2)
    (hseed : hasSmallParabolicCurvature H T p r)
    (hvolume : ENNReal.ofReal (A⁻¹ * r ^ 3) ≤
      DifferentialGeometry.Geometry.Collapse.ballVolume
        (H.stageMetric (H.activeStage T) T) p r)
    (seedTrace : BackwardPointTrace H (H.activeStage aSeed) (H.activeStage T)
      (H.activeStage_mono haT) p)
    (v : Icc (0 : ℝ) H.horizon) (hav : aSeed ≤ v) (hvT : v ≤ T)
    (hv : (T : ℝ) - r ^ 2 / 2 ≤ (v : ℝ)) :
    let O := seedTrace.point (H.activeStage v) (H.activeStage_mono hav)
      (H.activeStage_mono hvT)
    let R := r / 100
    hasSmallParabolicCurvature H v O R ∧
      ENNReal.ofReal ((A⁻¹ * Real.exp (-57) / 512) * R ^ 3) ≤
        DifferentialGeometry.Geometry.Collapse.ballVolume
          (H.stageMetric (H.activeStage v) v) O R ∧
      2 * R ^ 2 < (v : ℝ) := by
  classical
  intro O R
  have hr : 0 < r := hseed.1
  have hR : 0 < R := by dsimp only [R]; positivity
  have hsqrt : 1 ≤ Real.sqrt 3 := by
    nlinarith [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 3), Real.sqrt_nonneg (3 : ℝ)]
  have hrr : r ≤ Real.sqrt 3 * r := le_mul_of_one_le_left hr.le hsqrt
  have hball : H.isParabolicallyRmControlledBall T p r := by
    obtain ⟨_hr, a, hat, ha, htraces⟩ := hseed
    refine ⟨hr, a, hat, ha, ?_⟩
    intro x hx
    obtain ⟨A, hA⟩ := htraces x hx
    have hpow : r ^ 4 ≤ (Real.sqrt 3 * r) ^ 4 := pow_le_pow_left₀ hr.le hrr 4
    refine ⟨A, ?_, ?_⟩
    · intro u hau hut
      exact (mul_le_mul_of_nonneg_right hpow (normSq0S_nonneg _ _ _ _)).trans
        (hA.1 u hau hut)
    · intro i hi hl
      exact (mul_le_mul_of_nonneg_right hpow (normSq0S_nonneg _ _ _ _)).trans
        (hA.2 i hi hl)
  let clock : ℝ := Real.sqrt ((T : ℝ) - v)
  have hclockNonneg : 0 ≤ clock := Real.sqrt_nonneg _
  have hclockSq : clock ^ 2 = (T : ℝ) - v := Real.sq_sqrt (sub_nonneg.mpr hvT)
  have hclockLe : clock ≤ r := (sq_le_sq₀ hclockNonneg hr.le).mp (by
    rw [hclockSq]
    nlinarith [sq_nonneg r])
  have hclockEq : (v : ℝ) = (T : ℝ) - clock ^ 2 := by rw [hclockSq]; ring
  have hratio : clock ^ 2 / r ^ 2 ≤ 1 / 2 := by
    apply (div_le_iff₀ (sq_pos_of_pos hr)).mpr
    rw [hclockSq]
    linarith
  have hdistortion : Real.exp (2 * (3 / r ^ 2) * clock ^ 2) ≤ (10 : ℝ) ^ 2 := by
    have hcoef : 2 * (3 / r ^ 2) * clock ^ 2 ≤ 3 := by
      calc
        _ = 6 * (clock ^ 2 / r ^ 2) := by ring
        _ ≤ 6 * (1 / 2) := mul_le_mul_of_nonneg_left hratio (by norm_num)
        _ = 3 := by norm_num
    have heq : Real.exp 3 = (Real.exp 1) ^ 3 := by
      rw [show (3 : ℝ) = (1 + 1) + 1 by norm_num, Real.exp_add, Real.exp_add]
      ring
    have he2 : (Real.exp 1) ^ 2 < 9 := by
      nlinarith [Real.exp_one_lt_three, Real.exp_pos 1]
    have he3 : (Real.exp 1) ^ 3 < 27 := by
      have hmul := mul_lt_mul_of_pos_right he2 (Real.exp_pos 1)
      have hnine := mul_lt_mul_of_pos_left Real.exp_one_lt_three (by norm_num : (0 : ℝ) < 9)
      nlinarith only [hmul, hnine]
    refine le_of_lt ?_
    calc
      _ ≤ Real.exp 3 := Real.exp_le_exp.mpr hcoef
      _ < 27 := by rwa [heq]
      _ ≤ (10 : ℝ) ^ 2 := by norm_num
  have hmargin : R < (3 * r / 4) / (10 : ℝ) := by dsimp only [R]; linarith
  obtain ⟨b0, hb0v, hb0, htraces⟩ :=
    ObservedHistory.exists_past_seed_core_traces_of_metric_distortion H T v hvT p r clock
      hball hclockNonneg hclockLe hclockEq
      (seedTrace.restrictFirst (H.activeStage_mono hav) (H.activeStage_mono hvT))
      R 10 (by norm_num) hdistortion hmargin
  have hb0a : b0 = aSeed := Subtype.ext (hb0.trans hclock.symm)
  subst b0
  have hstart : (aSeed : ℝ) ≤ (v : ℝ) - R ^ 2 := by
    rw [hclock]
    dsimp only [R]
    nlinarith [sq_nonneg r]
  let b : Icc (0 : ℝ) H.horizon :=
    ⟨(v : ℝ) - R ^ 2, aSeed.property.1.trans hstart,
      (sub_le_self _ (sq_nonneg R)).trans v.property.2⟩
  have hab : aSeed ≤ b := hstart
  have hbv : b ≤ v := sub_le_self _ (sq_nonneg R)
  have hstrongScale : Real.sqrt 3 * R ≤ r := by
    have hsqrtLe : Real.sqrt 3 ≤ 2 := by
      nlinarith [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 3), Real.sqrt_nonneg (3 : ℝ)]
    dsimp only [R]
    nlinarith [mul_le_mul_of_nonneg_right hsqrtLe hr.le]
  have hsmall : hasSmallParabolicCurvature H v O R := by
    refine ⟨hR, b, hbv, rfl, ?_⟩
    intro y hy
    have hO :
        (seedTrace.restrictFirst (H.activeStage_mono hav) (H.activeStage_mono hvT)).point
          (H.activeStage v) le_rfl (H.activeStage_mono hvT) = O := rfl
    have hphysical : riemannianEDistOf
        (H.stageMetric (H.activeStage v) ((T : ℝ) - clock ^ 2))
        ((seedTrace.restrictFirst (H.activeStage_mono hav) (H.activeStage_mono hvT)).point
          (H.activeStage v) le_rfl (H.activeStage_mono hvT)) y < ENNReal.ofReal R := by
      rw [← hclockEq, hO]
      exact hy
    obtain ⟨A, hA⟩ := htraces y hphysical
    exact ⟨A.restrictFirst (H.activeStage_mono hab) (H.activeStage_mono hbv),
      hA.restrictFirst A (by positivity) hstrongScale hab hbv⟩
  refine ⟨hsmall, ?_, ?_⟩
  · have hp : p ∈ riemannianBallOf (H.stageMetric (H.activeStage T) T) p (r / 4) := by
      change riemannianEDistOf _ p p < ENNReal.ofReal (r / 4)
      rw [riemannianEDistOf_self]
      exact ENNReal.ofReal_pos.mpr (by positivity)
    have hvStart : (T : ℝ) - r ^ 2 ≤ (v : ℝ) := by rw [← hclock]; exact hav
    have hvol := (hseed.volume_lower_along_nearby_trace hvolume hp v hvT hvStart).2
      (seedTrace.restrictFirst (H.activeStage_mono hav) (H.activeStage_mono hvT))
      R hR (by dsimp only [R]; linarith)
    exact hvol
  · dsimp only [R]
    nlinarith [sq_nonneg r]

end GC.LongTime
