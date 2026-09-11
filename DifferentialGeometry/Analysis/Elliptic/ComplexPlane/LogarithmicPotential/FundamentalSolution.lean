import DifferentialGeometry.Analysis.Elliptic.ComplexPlane.Disk.LogKernel
import Mathlib.Analysis.SpecialFunctions.Log.NegMulLog
import Mathlib.MeasureTheory.Integral.CircleIntegral
import Mathlib.Analysis.Calculus.Deriv.Abs
import Mathlib.MeasureTheory.Integral.Bochner.Set



noncomputable section

open Set Filter InnerProductSpace Complex MeasureTheory
open scoped Topology RealInnerProductSpace Interval

namespace DifferentialGeometry.Analysis



theorem hasFDerivAt_log_norm_complex {z : ℂ} (hz : z ≠ 0) :
    HasFDerivAt (fun x : ℂ => Real.log ‖x‖)
      ((‖z‖ ^ 2)⁻¹ • innerSL ℝ z) z := by
  have hsq : ‖z‖ ^ 2 ≠ 0 := pow_ne_zero 2 (norm_ne_zero_iff.mpr hz)
  have hl := ((hasFDerivAt_id z).norm_sq.log hsq).const_mul (1 / 2 : ℝ)
  have heq : (fun x : ℂ => (1 / 2 : ℝ) * Real.log (‖x‖ ^ 2)) =
      (fun x : ℂ => Real.log ‖x‖) := by
    funext x
    rw [Real.log_pow]
    ring
  simp only [id_eq] at hl
  rw [heq] at hl
  convert! hl using 1
  ext v
  simp
  ring



theorem harmonicAt_log_norm_complex {z : ℂ} (hz : z ≠ 0) :
    HarmonicAt (fun x : ℂ => Real.log ‖x‖) z := by
  exact (show AnalyticAt ℂ (fun x : ℂ => x) z by fun_prop).harmonicAt_log_norm hz



theorem laplacian_log_norm_complex {z : ℂ} (hz : z ≠ 0) :
    (Laplacian.laplacian (fun x : ℂ => Real.log ‖x‖)) z = 0 := by
  exact (harmonicAt_log_norm_complex hz).2.self_of_nhds




theorem tendsto_self_mul_log_nhds_zero :
    Tendsto (fun r : ℝ => r * Real.log r) (𝓝 0) (𝓝 0) := by
  simpa using Real.continuous_mul_log.tendsto 0



theorem hasDerivAt_log_norm_circleMap_radius {r θ : ℝ} (hr : 0 < r) :
    HasDerivAt (fun s : ℝ => Real.log ‖circleMap 0 s θ‖) r⁻¹ r := by
  have hlog : HasDerivAt Real.log |r|⁻¹ |r| :=
    Real.hasDerivAt_log (abs_ne_zero.mpr (ne_of_gt hr))
  have hcomp : HasDerivAt (Real.log ∘ abs) r⁻¹ r := by
    simpa only [abs_of_pos hr, mul_one] using hlog.comp r (hasDerivAt_abs_pos hr)
  exact hcomp.congr_of_eventuallyEq (Eventually.of_forall fun s => by
    simp only [Function.comp_apply, norm_circleMap_zero])




theorem disk_log_circle_radial_flux {r : ℝ} (hr : 0 < r) :
    ∫ θ in 0..2 * Real.pi,
      r * deriv (fun s : ℝ => Real.log ‖circleMap 0 s θ‖) r = 2 * Real.pi := by
  have hd (θ : ℝ) : deriv (fun s : ℝ => Real.log ‖circleMap 0 s θ‖) r = r⁻¹ :=
    (hasDerivAt_log_norm_circleMap_radius hr).deriv
  simp_rw [hd]
  rw [mul_inv_cancel₀ (ne_of_gt hr)]
  simp



theorem tendsto_circleMap_intervalIntegral_nhds_zero
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    (f : ℂ → E) (hf : Continuous f) :
    Tendsto (fun r : ℝ => ∫ θ in 0..2 * Real.pi, f (circleMap 0 r θ))
      (nhds 0) (nhds ((2 * Real.pi) • f 0)) := by
  have hjoint : Continuous (fun q : ℝ × ℝ => f (circleMap 0 q.1 q.2)) := by
    apply hf.comp
    unfold circleMap
    fun_prop
  have hc : Continuous (fun r : ℝ =>
      ∫ θ in Set.Icc (0 : ℝ) (2 * Real.pi), f (circleMap 0 r θ)) :=
    continuous_parametric_integral_of_continuous hjoint isCompact_Icc
  have hle : (0 : ℝ) ≤ 2 * Real.pi := Real.two_pi_pos.le
  have heq (r : ℝ) :
      (∫ θ in 0..2 * Real.pi, f (circleMap 0 r θ)) =
        ∫ θ in Set.Icc (0 : ℝ) (2 * Real.pi), f (circleMap 0 r θ) := by
    rw [intervalIntegral.integral_of_le hle]
    exact setIntegral_congr_set (Ioc_ae_eq_Icc (α := ℝ) (μ := volume))
  have hzero : (∫ θ in Set.Icc (0 : ℝ) (2 * Real.pi), f (circleMap 0 0 θ)) =
      (2 * Real.pi) • f 0 := by
    simp [circleMap, hle]
  rw [← hzero]
  exact (hc.tendsto 0).congr' (Eventually.of_forall fun r => (heq r).symm)



theorem tendsto_disk_log_radial_flux_mul_nhdsGT_zero
    (f : ℂ → ℝ) (hf : Continuous f) :
    Tendsto (fun r : ℝ => ∫ θ in 0..2 * Real.pi,
      (r * deriv (fun s : ℝ => Real.log ‖circleMap 0 s θ‖) r) *
        f (circleMap 0 r θ))
      (nhdsWithin 0 (Set.Ioi 0)) (nhds ((2 * Real.pi) * f 0)) := by
  have hbase : Tendsto (fun r : ℝ => ∫ θ in 0..2 * Real.pi, f (circleMap 0 r θ))
      (nhdsWithin 0 (Set.Ioi 0)) (nhds ((2 * Real.pi) * f 0)) := by
    simpa only [smul_eq_mul] using (tendsto_circleMap_intervalIntegral_nhds_zero f hf).mono_left
      (show nhdsWithin (0 : ℝ) (Set.Ioi 0) ≤ nhds 0 from inf_le_left)
  apply hbase.congr'
  filter_upwards [self_mem_nhdsWithin] with r hr
  have hrpos : 0 < r := hr
  have hd (θ : ℝ) : deriv (fun s : ℝ => Real.log ‖circleMap 0 s θ‖) r = r⁻¹ :=
    (hasDerivAt_log_norm_circleMap_radius hrpos).deriv
  apply intervalIntegral.integral_congr
  intro θ _
  change f (circleMap 0 r θ) =
    r * deriv (fun s : ℝ => Real.log ‖circleMap 0 s θ‖) r * f (circleMap 0 r θ)
  rw [hd, mul_inv_cancel₀ (ne_of_gt hrpos), one_mul]

end DifferentialGeometry.Analysis
