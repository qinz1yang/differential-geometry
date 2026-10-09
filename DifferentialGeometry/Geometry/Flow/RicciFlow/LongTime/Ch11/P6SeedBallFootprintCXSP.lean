import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.P6PreparedUniformTraceWindowCXSP

set_option autoImplicit false

/-!
# CX-SPINE G28：实际 terminal closed ball 的 seed 距离范围

Q=H0/r² 时，归一化半径 R 对应物理半径 (R/sqrt H0)*r。
真实 seed-to-center 距离与显式 radius 余量经 triangle 控制球内全部点；不制造 κ 域。
-/

noncomputable section

open Set DifferentialGeometry
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
open scoped ENNReal

namespace GC.LongTime.Ch11

universe u

/-- 正比例缩放的 terminal 闭球准确等于原 metric 上半径 R/sqrt Q 的闭球。 -/
theorem scaled_seed_closedBall_eq_CXSP
    {P : OrientedThreeStage.{u}} (g : P.Metric) (y : P.Carrier)
    {Q : ℝ} (hQ : 0 < Q) (R : ℝ) :
    riemannianClosedBallOf (scaleMetric Q hQ g) y R =
      riemannianClosedBallOf g y (R / Real.sqrt Q) := by
  conv_lhs => rw [show R = Real.sqrt Q * (R / Real.sqrt Q) by field_simp]
  exact riemannianClosedBallOf_scaleMetric Q hQ g y _

/-- 同一实际 terminal 闭球中的全部点落在固定 seed 距离范围内。 -/
theorem seed_closedBall_distance_CXSP
    {P : OrientedThreeStage.{u}} (g : P.Metric) {p y : P.Carrier}
    {H0 r R dCenter d0 : ℝ} (hH : 0 < H0) (hr : 0 < r)
    (hR : 0 ≤ R) (hdCenter : 0 ≤ dCenter)
    (hfit : dCenter + R / Real.sqrt H0 ≤ d0)
    (hcenter : riemannianEDistOf g p y ≤ ENNReal.ofReal (dCenter * r)) :
    ∀ z ∈ riemannianClosedBallOf g y (R / Real.sqrt (H0 * (r ^ 2)⁻¹)),
      riemannianEDistOf g p z ≤ ENNReal.ofReal (d0 * r) := by
  intro z hz
  have hroot : 0 < Real.sqrt H0 := Real.sqrt_pos.mpr hH
  have hrad : R / Real.sqrt (H0 * (r ^ 2)⁻¹) = (R / Real.sqrt H0) * r := by
    rw [sqrt_seed_scale_CXSP hH hr]
    field_simp
  have hz' : riemannianEDistOf g y z ≤ ENNReal.ofReal ((R / Real.sqrt H0) * r) := by
    change riemannianEDistOf g y z ≤ _ at hz
    rwa [hrad] at hz
  calc
    riemannianEDistOf g p z ≤ riemannianEDistOf g p y + riemannianEDistOf g y z :=
      riemannianEDistOf_triangle _ _ _ _
    _ ≤ ENNReal.ofReal (dCenter * r) + ENNReal.ofReal ((R / Real.sqrt H0) * r) :=
      add_le_add hcenter hz'
    _ = ENNReal.ofReal ((dCenter + R / Real.sqrt H0) * r) := by
      rw [← ENNReal.ofReal_add (mul_nonneg hdCenter hr.le)
        (mul_nonneg (div_nonneg hR hroot.le) hr.le)]
      congr 1
      ring
    _ ≤ ENNReal.ofReal (d0 * r) :=
      ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right hfit hr.le)

end GC.LongTime.Ch11
