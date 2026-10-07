import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.ParabolicCurvature
import DifferentialGeometry.Geometry.Collapse.CurvatureScale
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.TracedRegionRecenter
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.TracedRegionVolume
import DifferentialGeometry.Geometry.Comparison.Volume.InteriorBallLowerBound

/-!
# S-CH11-FIX9 port of astra `ParabolicSeedVolume`（`PortC11P`）

来源：donor `ParabolicSeedVolume.lean`（Jui-Hui `chapter11-astra` @ `a73e4bdbfd`）。
donor 文本在本树 elaboration 失败。本 port 只有 elaboration 层面修补（no statement / definition /
proof idea altered；不加 `set_option`）：
* `hbuffer` 的 calc 首步 `add_le_add_right hy.le _`（本树 Mathlib 把加项放在左边，左右约定相反，
  给出 `c + a ≤ c + b`）→ `add_le_add hy.le le_rfl`（随后 calc 末步 `by linarith` 的 `?m` 一并消掉）。

原路径 `ParabolicSeedVolume` 是只 import 本文件的 re-export shim。
-/

set_option autoImplicit false

noncomputable section

open Set DifferentialGeometry
open DifferentialGeometry.Geometry.Curvature DifferentialGeometry.Tensor0SBundle
open DifferentialGeometry.Geometry.Collapse DifferentialGeometry.Geometry.Riemannian
open DifferentialGeometry.PDE.RicciFlow DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
open scoped Manifold ContDiff ENNReal

namespace GC.LongTime

universe u

private local instance : NeZero (Module.finrank ℝ ThreeSpace) := ⟨by simp⟩

private theorem hasSmallParabolicCurvature.tracedRegion
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

/-- A genuine controlled seed and its volume give one uniform volume coefficient
for smaller balls in the inner quarter of the same terminal metric. -/
theorem hasSmallParabolicCurvature.volume_lower_of_nearby_center
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
  obtain ⟨_, _, a, hat, _, htraces⟩ := hseed.tracedRegion
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

/-- The same seed's nearby terminal centers have actual earlier traces and a
uniform lower volume coefficient along every such trace, including surgery
times. This conclusion remains inside the original controlled seed geometry. -/
theorem hasSmallParabolicCurvature.volume_lower_along_nearby_trace
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
  have htraced := hseed.tracedRegion.recenter (half_pos hr) hbuffer
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
    have h := hseed.volume_lower_of_nearby_center hvolume hy hd hdr
    simpa only [κ, ENNReal.ofReal_mul' (pow_nonneg hd.le 3),
      ENNReal.ofReal_pow hd.le] using h
  have hearlier := H.volume_ball_ge_along_trace_of_isTracedRegion t v hvt y
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

end GC.LongTime
