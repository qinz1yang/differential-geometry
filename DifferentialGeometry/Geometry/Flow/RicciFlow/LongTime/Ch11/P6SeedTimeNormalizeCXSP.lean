import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.P6SeedTimeArithmeticCXSP
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.P6NormalizeP6X

set_option autoImplicit false

/-!
# CX-SPINE G4：实际 retained history 的种子时间归一化

令 c=t/2，使用既有 rescale_P6N 搬运整史。实际终端时间为2，activeStage 不变；
新基点曲率为 c*H/r²，两次 metric scaling 恰等于原 Q0 倍 metric。
对 c 坏序列真实生产新基点曲率≥1、Q→∞、Qt→∞、固定正窗口深度H/2与窗口起点≥1。
不把这些标量/metric identities 计作 κ、records、trace footprint 的完整搬运。
-/

noncomputable section

open Set Filter DifferentialGeometry DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
open scoped Manifold ContDiff Topology ENNReal

namespace GC.LongTime.Ch11

universe u

/-- 实际 history slice 归一化到2；两次缩放后的 metric 与原种子曲率尺度完全一致。 -/
theorem seed_history_rescale_at_two_CXSP (K : RetainedCoreHistory.{u})
    (t : Icc (0 : ℝ) K.toHistory.horizon) (ht : 0 < (t : ℝ))
    (x : (K.toHistory.stageAt t).Carrier) {H r : ℝ} (hH : 0 < H) (hr : 0 < r)
    (hR : metricScalarAt (K.toHistory.stageMetric (K.toHistory.activeStage t) t) x =
      H * (r ^ 2)⁻¹) :
    ((K.rescaleTime_P6X (half_pos ht) t :
      Icc (0 : ℝ) (K.rescale_P6N ((t : ℝ) / 2) (half_pos ht)).toHistory.horizon) : ℝ) = 2 ∧
    (K.rescale_P6N ((t : ℝ) / 2) (half_pos ht)).toHistory.activeStage
      (K.rescaleTime_P6X (half_pos ht) t) = K.toHistory.activeStage t ∧
    metricScalarAt
      ((K.rescale_P6N ((t : ℝ) / 2) (half_pos ht)).toHistory.stageMetric
        (K.toHistory.activeStage t) 2) x = ((t : ℝ) / 2) * (H * (r ^ 2)⁻¹) ∧
    scaleMetric (((t : ℝ) / 2) * (H * (r ^ 2)⁻¹))
      (mul_pos (half_pos ht) (mul_pos hH (inv_pos.mpr (pow_pos hr 2))))
      ((K.rescale_P6N ((t : ℝ) / 2) (half_pos ht)).toHistory.stageMetric
        (K.toHistory.activeStage t) 2) =
      scaleMetric (H * (r ^ 2)⁻¹) (mul_pos hH (inv_pos.mpr (pow_pos hr 2)))
        (K.toHistory.stageMetric (K.toHistory.activeStage t) t) := by
  have hclock : (t : ℝ) / 2 * 2 = t := by ring
  refine ⟨?_, K.activeStage_rescaleTime_P6X (half_pos ht) t, ?_, ?_⟩
  · change (t : ℝ) / ((t : ℝ) / 2) = 2
    field_simp
  · rw [K.scalar_rescale_P6X (half_pos ht), hclock, hR]
  · rw [K.rescale_P6N_stageMetric _ (half_pos ht), hclock]
    apply SmoothRiemannianMetric.ext_inner
    intro z v w
    change (((t : ℝ) / 2) * (H * (r ^ 2)⁻¹)) *
        (((t : ℝ) / 2)⁻¹ * (K.toHistory.stageMetric (K.toHistory.activeStage t) t).inner z v w) =
      (H * (r ^ 2)⁻¹) * (K.toHistory.stageMetric (K.toHistory.activeStage t) t).inner z v w
    calc
      _ = (((t : ℝ) / 2) * ((t : ℝ) / 2)⁻¹) *
          ((H * (r ^ 2)⁻¹) * (K.toHistory.stageMetric (K.toHistory.activeStage t) t).inner z v w) :=
        by ring
      _ = _ := by rw [mul_inv_cancel₀ (half_pos ht).ne', one_mul]

/-- 坏种子族经实际整史重标度后给固定深度 scalar 内核所需的曲率增长与时间数据。 -/
theorem seed_history_time_normalized_family_CXSP
    (K : ℕ → RetainedCoreHistory.{u})
    (t : ∀ n, Icc (0 : ℝ) (K n).toHistory.horizon)
    (ht : ∀ n, 0 < (t n : ℝ)) (r : ℕ → ℝ) (hr : ∀ n, 0 < r n)
    (htime : ∀ n, 2 * r n ^ 2 < (t n : ℝ))
    (hsmall : ∀ n, r n ≤ Real.sqrt (t n : ℝ) / ((n : ℝ) + 1))
    (x : ∀ n, ((K n).toHistory.stageAt (t n)).Carrier)
    {H : ℝ} (hH : 2 ≤ H)
    (hR : ∀ n, metricScalarAt
      ((K n).toHistory.stageMetric ((K n).toHistory.activeStage (t n)) (t n)) (x n) =
        H * (r n ^ 2)⁻¹) :
    let Q := fun n => metricScalarAt
      (((K n).rescale_P6N ((t n : ℝ) / 2) (half_pos (ht n))).toHistory.stageMetric
        ((K n).toHistory.activeStage (t n)) 2) (x n)
    ∃ hQ : ∀ n, 1 ≤ Q n,
      Tendsto Q atTop atTop ∧ Tendsto (fun n => Q n * 2) atTop atTop ∧
      (∀ n, 1 < ((t n : ℝ) - r n ^ 2 / 2) / ((t n : ℝ) / 2) ∧
        ((t n : ℝ) - r n ^ 2 / 2) / ((t n : ℝ) / 2) < 2 ∧
        Q n * (2 - ((t n : ℝ) - r n ^ 2 / 2) / ((t n : ℝ) / 2)) = H / 2) ∧
      ∀ n, scaleMetric (Q n) (zero_lt_one.trans_le (hQ n))
          (((K n).rescale_P6N ((t n : ℝ) / 2) (half_pos (ht n))).toHistory.stageMetric
            ((K n).toHistory.activeStage (t n)) 2) =
        scaleMetric (H * (r n ^ 2)⁻¹)
          (mul_pos (by linarith : 0 < H) (inv_pos.mpr (pow_pos (hr n) 2)))
          ((K n).toHistory.stageMetric ((K n).toHistory.activeStage (t n)) (t n)) := by
  intro Q
  have hH0 : 0 < H := by linarith
  have hdata (n : ℕ) :=
    seed_history_rescale_at_two_CXSP (K n) (t n) (ht n) (x n) hH0 (hr n) (hR n)
  have hQeq (n : ℕ) : Q n = ((t n : ℝ) / 2) * (H * (r n ^ 2)⁻¹) :=
    (hdata n).2.2.1
  obtain ⟨hQ0, hlim, htimeLim⟩ := seed_time_scaled_curvature_family_CXSP hH
    (fun n => (t n : ℝ)) r (fun n => (ht n).le) hr hsmall
  have hQ : ∀ n, 1 ≤ Q n := fun n => by rw [hQeq]; exact hQ0 n
  refine ⟨hQ, ?_, ?_, ?_, ?_⟩
  · simpa only [show Q = (fun n => ((t n : ℝ) / 2) * (H * (r n ^ 2)⁻¹)) from
      funext hQeq] using hlim
  · simpa only [hQeq] using htimeLim
  · intro n
    rw [hQeq]
    exact seed_half_window_time_normalization_CXSP (hr n) (htime n) H
  · intro n
    simpa only [hQeq] using (hdata n).2.2.2

end GC.LongTime.Ch11
