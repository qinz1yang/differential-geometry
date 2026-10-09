import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.P6SeedTraceP6B
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.AnalyticAdmissibility
import DifferentialGeometry.Geometry.Collapse.CurvatureScale
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.TracedRegionRecenter
import DifferentialGeometry.Geometry.Comparison.Volume.InteriorBallLowerBound
import DifferentialGeometry.Geometry.Flow.RicciFlow.Estimates.Shi.SectionalFromCurvatureBound

/-!
# P6 / L5：seed shift（O-CH11-P6B G1，后缀 `_P6B`）

KL 84.1 的种子 `(p, t, r)`（`hasSmallParabolicCurvature H t p r` + `vol B(p,r) ≥ w r³`）沿种子
trace 搬到更早时刻：对任意 `v ∈ [t − r²/2, t]`，种子 trace 点 `O_v` 周围 `(O_v, v, r/100)` 仍是
种子，体积系数 `w·e⁻⁵⁷/512`（`earlier_seed_on_half_depth_P6B`）。这就是把 KL 84.1(a)（局部
κ(A)，在种子时刻成立）推到 point selection 的 backward 窗 `v ≤ s` 所需的唯一几何步骤。

证明用 `P6SeedTraceP6B` 的覆盖引理（common flow + ball capture）与沿 trace 体积下界；思路参照
astra `LT/ParabolicSeedVolume`、`LT/ParabolicSeedRecenter`（依赖 B1 FAIL 模块，只当 reference）。
-/

set_option autoImplicit false
noncomputable section

open Set DifferentialGeometry
open DifferentialGeometry.Geometry.Curvature DifferentialGeometry.Tensor0SBundle
open DifferentialGeometry.Geometry.Collapse DifferentialGeometry.Geometry.Riemannian
open DifferentialGeometry.PDE.RicciFlow DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
open scoped Manifold ContDiff ENNReal

namespace GC.LongTime.Ch11

universe u

private local instance : NeZero (Module.finrank ℝ ThreeSpace) := ⟨by simp⟩

/-- 种子 ⇒ traced region（半径 `r`、深度 `r²`、`|Rm| ≤ r⁻²`）。 -/
theorem isTracedRegion_of_hasSmallParabolicCurvature_P6B
    {H : ObservedHistory.{u}} {t : Icc (0 : ℝ) H.horizon}
    {p : (H.stageAt t).Carrier} {r : ℝ}
    (h : hasSmallParabolicCurvature H t p r) :
    H.isTracedRegion t p r (r ^ 2) (r ^ 2)⁻¹ := by
  obtain ⟨hr, a, hat, ha, htrace⟩ := h
  have hsqrt : 1 ≤ Real.sqrt 3 := by
    nlinarith [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 3), Real.sqrt_nonneg (3 : ℝ)]
  have hscaled : 0 < Real.sqrt 3 * r :=
    mul_pos (Real.sqrt_pos.mpr (by norm_num)) hr
  have hrr : r ≤ Real.sqrt 3 * r := le_mul_of_one_le_left hr.le hsqrt
  refine ⟨hr, sq_pos_of_pos hr, a, hat, ha, ?_⟩
  intro x hx
  obtain ⟨A, hA⟩ := htrace x hx
  have hbound := (A.isRmControlled_iff_isRmBoundedBy hscaled).mp hA
  refine ⟨A, hbound.mono (by positivity) ?_⟩
  exact (inv_le_inv₀ (sq_pos_of_pos hscaled) (sq_pos_of_pos hr)).mpr
    (pow_le_pow_left₀ hr.le hrr 2)

/-- 种子时刻的近中心体积：`y ∈ B(p, r/4)`、`0 < s ≤ r/2` ⇒ `vol B(y, s) ≥ (w e⁻³/512) s³`
（种子球上 `sec ≥ −r⁻²` + Bishop–Gromov）。 -/
theorem volume_lower_of_nearby_center_P6B
    {H : ObservedHistory.{u}} {t : Icc (0 : ℝ) H.horizon}
    {p : (H.stageAt t).Carrier} {r w : ℝ}
    (hseed : hasSmallParabolicCurvature H t p r)
    (hvolume : ENNReal.ofReal (w * r ^ 3) ≤
      ballVolume (H.stageMetric (H.activeStage t) t) p r)
    {y : (H.stageAt t).Carrier}
    (hy : y ∈ riemannianBallOf (H.stageMetric (H.activeStage t) t) p (r / 4))
    {s : ℝ} (hs : 0 < s) (hsr : s ≤ r / 2) :
    ENNReal.ofReal ((w * Real.exp (-3) / 512) * s ^ 3) ≤
      ballVolume (H.stageMetric (H.activeStage t) t) y s := by
  have hr : 0 < r := hseed.1
  obtain ⟨_, _, a, hat, _, htraces⟩ := isTracedRegion_of_hasSmallParabolicCurvature_P6B hseed
  have hsec : ∀ x ∈ riemannianBallOf (H.stageMetric (H.activeStage t) t) p r,
      SectionalBoundedBelowAt (H.stageMetric (H.activeStage t) t) x (-(r ^ 2)⁻¹) := by
    intro x hx
    obtain ⟨A, hA⟩ := htraces x hx
    have hbound := hA.1 t hat le_rfl
    rw [A.endpoint_eq] at hbound
    have hsectional := sectionalBoundedBelowAt_neg_sqrt_of_normSq0S_le
      (H.stageMetric (H.activeStage t) t) x hbound
    simpa only [Real.sqrt_sq (inv_nonneg.mpr (sq_nonneg r))] using hsectional
  have hdim : Module.finrank ℝ ThreeSpace = 3 := by simp [ThreeSpace]
  have hvolume' := VolumeComparison.riemannianBallOf_volume_lower_of_nearby_center
    (H.stageMetric (H.activeStage t) t) (RiemannianMetricComplete.of_compact _)
    p y hr hs hsr hy hsec (by simpa only [hdim, ballVolume] using hvolume)
  norm_num only [hdim, Nat.reduceSub, Nat.cast_ofNat] at hvolume'
  exact hvolume'

/-- 种子近中心点的更早 trace 存在，且沿每条这样的 trace 有一致体积系数 `w e⁻⁵⁷/512`
（尺度 `≤ r/2`，时刻 `v ≥ t − r²`）。 -/
theorem volume_lower_along_nearby_trace_P6B
    {H : ObservedHistory.{u}} {t : Icc (0 : ℝ) H.horizon}
    {p : (H.stageAt t).Carrier} {r w : ℝ}
    (hseed : hasSmallParabolicCurvature H t p r)
    (hvolume : ENNReal.ofReal (w * r ^ 3) ≤
      ballVolume (H.stageMetric (H.activeStage t) t) p r)
    {y : (H.stageAt t).Carrier}
    (hy : y ∈ riemannianBallOf (H.stageMetric (H.activeStage t) t) p (r / 4))
    (v : Icc (0 : ℝ) H.horizon) (hvt : v ≤ t)
    (hv : (t : ℝ) - r ^ 2 ≤ (v : ℝ)) :
    Nonempty (BackwardPointTrace H (H.activeStage v) (H.activeStage t)
      (H.activeStage_mono hvt) y) ∧
    ∀ A : BackwardPointTrace H (H.activeStage v) (H.activeStage t)
        (H.activeStage_mono hvt) y,
      ∀ s : ℝ, 0 < s → s ≤ r / 2 →
        ENNReal.ofReal ((w * Real.exp (-57) / 512) * s ^ 3) ≤
          ballVolume (H.stageMetric (H.activeStage v) v)
            (A.point (H.activeStage v) le_rfl (H.activeStage_mono hvt)) s := by
  have hr : 0 < r := hseed.1
  have hbuffer : riemannianEDistOf (H.stageMetric (H.activeStage t) t) p y +
      ENNReal.ofReal (r / 2) ≤ ENNReal.ofReal r := by
    calc
      _ ≤ ENNReal.ofReal (r / 4) + ENNReal.ofReal (r / 2) :=
        add_le_add hy.le le_rfl
      _ = ENNReal.ofReal (r / 4 + r / 2) :=
        (ENNReal.ofReal_add (by positivity) (by positivity)).symm
      _ ≤ _ := ENNReal.ofReal_le_ofReal (by linarith)
  have htraced := (isTracedRegion_of_hasSmallParabolicCurvature_P6B hseed).recenter
    (half_pos hr) hbuffer
  have hycenter : y ∈ riemannianBallOf (H.stageMetric (H.activeStage t) t) y (r / 2) := by
    change riemannianEDistOf _ y y < ENNReal.ofReal (r / 2)
    rw [riemannianEDistOf_self]
    exact ENNReal.ofReal_pos.mpr (half_pos hr)
  have htrace : Nonempty (BackwardPointTrace H (H.activeStage v) (H.activeStage t)
      (H.activeStage_mono hvt) y) := by
    obtain ⟨_, _, a, hat, ha, htraces⟩ := htraced
    have hav : a ≤ v := by
      change (a : ℝ) ≤ (v : ℝ)
      rw [ha]
      exact hv
    obtain ⟨A, _⟩ := htraces y hycenter
    exact ⟨A.restrictFirst (H.activeStage_mono hav) (H.activeStage_mono hvt)⟩
  refine ⟨htrace, ?_⟩
  intro A s hs hsr
  let κ : ℝ := w * Real.exp (-3) / 512
  have hterminal : ∀ d : ℝ, 0 < d → d ≤ r / 2 →
      ENNReal.ofReal κ * ENNReal.ofReal d ^ 3 ≤
        ballVolume (H.stageMetric (H.activeStage t) t) y d := by
    intro d hd hdr
    have h := volume_lower_of_nearby_center_P6B hseed hvolume hy hd hdr
    simpa only [κ, ENNReal.ofReal_mul' (pow_nonneg hd.le 3),
      ENNReal.ofReal_pow hd.le] using h
  have hearlier := H.volume_ball_ge_along_trace_of_isTracedRegion_P6B t v hvt y
    (inv_nonneg.mpr (sq_nonneg r)) htraced hv A (le_refl (r / 2)) hterminal hs hsr
  have hcancel : -54 * (r ^ 2)⁻¹ * r ^ 2 = (-54 : ℝ) := by
    field_simp [(sq_pos_of_pos hr).ne']
  rw [hcancel] at hearlier
  have hcoefficient : Real.exp (-54) * κ = w * Real.exp (-57) / 512 := by
    have hexp : Real.exp (-54) * Real.exp (-3) = Real.exp (-57) := by
      rw [← Real.exp_add]
      norm_num
    calc
      Real.exp (-54) * κ = w * (Real.exp (-54) * Real.exp (-3)) / 512 := by
        dsimp only [κ]
        ring
      _ = w * Real.exp (-57) / 512 := by rw [hexp]
  rw [hcoefficient] at hearlier
  simpa only [ballVolume, ENNReal.ofReal_mul' (pow_nonneg hs.le 3),
    ENNReal.ofReal_pow hs.le] using hearlier

/-- **seed shift**（L5 的几何核心）：种子 `(p, t, r)`（`A > 1`）在任意 `v ∈ [t − r²/2, t]` 给出以
种子 trace 点 `O_v` 为中心、半径 `R = r/100` 的种子：`hasSmallParabolicCurvature H v O_v R`、
`vol B(O_v, R) ≥ (A⁻¹ e⁻⁵⁷/512) R³`，且 `2R² < v`。 -/
theorem earlier_seed_on_half_depth_P6B
    {H : ObservedHistory.{u}} {T aSeed : Icc (0 : ℝ) H.horizon}
    (haT : aSeed ≤ T) (p : (H.stageAt T).Carrier) (r A : ℝ)
    (htime : 2 * r ^ 2 < (T : ℝ))
    (hclock : (aSeed : ℝ) = (T : ℝ) - r ^ 2)
    (hseed : hasSmallParabolicCurvature H T p r)
    (hvolume : ENNReal.ofReal (A⁻¹ * r ^ 3) ≤
      ballVolume (H.stageMetric (H.activeStage T) T) p r)
    (seedTrace : BackwardPointTrace H (H.activeStage aSeed) (H.activeStage T)
      (H.activeStage_mono haT) p)
    (v : Icc (0 : ℝ) H.horizon) (hav : aSeed ≤ v) (hvT : v ≤ T)
    (hv : (T : ℝ) - r ^ 2 / 2 ≤ (v : ℝ)) :
    let O := seedTrace.point (H.activeStage v) (H.activeStage_mono hav)
      (H.activeStage_mono hvT)
    let R := r / 100
    hasSmallParabolicCurvature H v O R ∧
      ENNReal.ofReal ((A⁻¹ * Real.exp (-57) / 512) * R ^ 3) ≤
        ballVolume (H.stageMetric (H.activeStage v) v) O R ∧
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
    obtain ⟨B, hB⟩ := htraces x hx
    have hpow : r ^ 4 ≤ (Real.sqrt 3 * r) ^ 4 := pow_le_pow_left₀ hr.le hrr 4
    refine ⟨B, ?_, ?_⟩
    · intro u hau hut
      exact (mul_le_mul_of_nonneg_right hpow (normSq0S_nonneg _ _ _ _)).trans
        (hB.1 u hau hut)
    · intro i hi hl
      exact (mul_le_mul_of_nonneg_right hpow (normSq0S_nonneg _ _ _ _)).trans
        (hB.2 i hi hl)
  let clock : ℝ := Real.sqrt ((T : ℝ) - v)
  have hclockNonneg : 0 ≤ clock := Real.sqrt_nonneg _
  have hclockSq : clock ^ 2 = (T : ℝ) - v :=
    Real.sq_sqrt (sub_nonneg.mpr (show (v : ℝ) ≤ T from hvT))
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
    H.exists_past_seed_core_traces_P6B T v hvT p r clock hball
      hclockNonneg hclockLe hclockEq
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
    obtain ⟨B, hB⟩ := htraces y hphysical
    exact ⟨B.restrictFirst (H.activeStage_mono hab) (H.activeStage_mono hbv),
      hB.restrictFirst B (by positivity) hstrongScale hab hbv⟩
  refine ⟨hsmall, ?_, ?_⟩
  · have hp : p ∈ riemannianBallOf (H.stageMetric (H.activeStage T) T) p (r / 4) := by
      change riemannianEDistOf _ p p < ENNReal.ofReal (r / 4)
      rw [riemannianEDistOf_self]
      exact ENNReal.ofReal_pos.mpr (by positivity)
    have hvStart : (T : ℝ) - r ^ 2 ≤ (v : ℝ) := by rw [← hclock]; exact hav
    have hvol := (volume_lower_along_nearby_trace_P6B hseed hvolume hp v hvT hvStart).2
      (seedTrace.restrictFirst (H.activeStage_mono hav) (H.activeStage_mono hvT))
      R hR (by dsimp only [R]; linarith)
    exact hvol
  · dsimp only [R]
    nlinarith [sq_nonneg r]

end GC.LongTime.Ch11
