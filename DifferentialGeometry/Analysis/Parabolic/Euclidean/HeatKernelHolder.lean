import DifferentialGeometry.Analysis.Parabolic.Euclidean.HeatKernelLpPower
import Mathlib.MeasureTheory.Integral.Bochner.Basic

/-!
# Spatial Hölder bounds for the Euclidean heat potential

The late Koch--Lamm value estimate pairs a spatial heat-kernel slice with an
`L^q` source slice.  This file proves that Banach-valued Hölder step and then
specializes the kernel factor using the exact translated real-power mass from
`HeatKernelLpPower`.

No cylinder cover or time integration is performed here.
-/

noncomputable section

open MeasureTheory Real
open scoped ENNReal RealInnerProductSpace

namespace DifferentialGeometry
namespace Analysis
namespace Parabolic
namespace Euclidean

variable {X F : Type*} [MeasurableSpace X]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]

omit [CompleteSpace F] in
/-- Banach-valued Hölder inequality for a scalar kernel paired with a vector
field. -/
theorem integral_holder {μ : Measure X} {p q : ℝ}
    (hpq : p.HolderConjugate q) (k : X → ℝ) (f : X → F)
    (hk : MemLp k (ENNReal.ofReal p) μ)
    (hf : MemLp f (ENNReal.ofReal q) μ) :
    ‖∫ y, k y • f y ∂μ‖ ≤
      (∫ y, ‖k y‖ ^ p ∂μ) ^ (1 / p) *
        (∫ y, ‖f y‖ ^ q ∂μ) ^ (1 / q) := by
  calc
    ‖∫ y, k y • f y ∂μ‖ ≤ ∫ y, ‖k y • f y‖ ∂μ :=
      norm_integral_le_integral_norm _
    _ = ∫ y, ‖k y‖ * ‖(fun z ↦ ‖f z‖) y‖ ∂μ := by
      apply integral_congr_ae
      filter_upwards with y
      simp only [norm_smul, norm_norm]
    _ ≤ (∫ y, ‖k y‖ ^ p ∂μ) ^ (1 / p) *
        (∫ y, ‖(fun z ↦ ‖f z‖) y‖ ^ q ∂μ) ^ (1 / q) :=
      integral_mul_norm_le_Lp_mul_Lq hpq hk hf.norm
    _ = (∫ y, ‖k y‖ ^ p ∂μ) ^ (1 / p) *
        (∫ y, ‖f y‖ ^ q ∂μ) ^ (1 / q) := by
      simp only [norm_norm]

section HeatKernel

variable {V : Type*}
  [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  [MeasurableSpace V] [BorelSpace V] [Nontrivial V]

/-- A translated-reflected positive-time heat kernel belongs to every
spatial `L^p`, `p > 0`. -/
theorem heatShift_memLp {t p : ℝ} (ht : 0 < t) (hp : 0 < p) (x : V) :
    MemLp (fun y : V ↦ heatKernel t (x - y)) (ENNReal.ofReal p)
      (volume : Measure V) := by
  have hcont : Continuous (fun y : V ↦ heatKernel t (x - y)) := by
    have hkcont : Continuous (heatKernel t : V → ℝ) :=
      continuous_iff_continuousAt.mpr fun z ↦
        (heatKernel_hasFDeriv ht z).continuousAt
    exact hkcont.comp (continuous_const.sub continuous_id)
  apply (integrable_norm_rpow_iff hcont.aestronglyMeasurable
    (ENNReal.ofReal_pos.mpr hp).ne' ENNReal.ofReal_ne_top).mp
  have hpow : Integrable (fun y : V ↦ (heatKernel t (x - y)) ^ p) :=
    (heatKernelPow_mem (V := V) ht hp).comp_sub_left x
  simpa [ENNReal.toReal_ofReal hp.le,
    Real.norm_of_nonneg (heatKernel_nonneg ht _)] using hpow

omit [CompleteSpace F] in
/-- Exact spatial Hölder bound for a positive-time heat convolution.  The
kernel factor is written with its proved parabolic scaling. -/
theorem heatConv_holder {t p q : ℝ} (ht : 0 < t)
    (hpq : p.HolderConjugate q) (x : V) (f : V → F)
    (hf : MemLp f (ENNReal.ofReal q) (volume : Measure V)) :
    ‖∫ y : V, heatKernel t (x - y) • f y‖ ≤
      (t ^ ((Module.finrank ℝ V : ℝ) * (1 - p) / 2) *
          basePowMass V p) ^ (1 / p) *
        (∫ y : V, ‖f y‖ ^ q) ^ (1 / q) := by
  have h := integral_holder hpq (fun y : V ↦ heatKernel t (x - y)) f
    (heatShift_memLp (V := V) ht hpq.pos x) hf
  simp_rw [Real.norm_of_nonneg (heatKernel_nonneg ht _)] at h
  rw [heatPow_shift (V := V) ht hpq.pos x] at h
  exact h

end HeatKernel

end Euclidean
end Parabolic
end Analysis
end DifferentialGeometry

end
