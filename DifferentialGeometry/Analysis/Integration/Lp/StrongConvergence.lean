import DifferentialGeometry.Analysis.Integration.LpNorm
import Mathlib.MeasureTheory.Function.LpSeminorm.TriangleInequality

noncomputable section

open Filter MeasureTheory
open scoped ENNReal Topology

namespace MeasureTheory

variable {P X : Type*} [MeasurableSpace P] [NormedAddCommGroup X]
  {μ ν : Measure P}

private theorem tendsto_eLpNorm_sub_of_tendsto_eLpNorm_sub_of_ae_eq
    (u v : ℕ → P → X) (f g : P → X)
    (huf : Tendsto (fun n => eLpNorm (fun x => u n x - f x) 2 μ) atTop (𝓝 0))
    (hvg : Tendsto (fun n => eLpNorm (fun x => v n x - g x) 2 μ) atTop (𝓝 0))
    (hfg : f =ᵐ[μ] g) :
    Tendsto (fun n => eLpNorm (fun x => u n x - v n x) 2 μ) atTop (𝓝 0) := by
  have hbound (n : ℕ) : eLpNorm (fun x => u n x - v n x) 2 μ ≤
      eLpNorm (fun x => u n x - f x) 2 μ + eLpNorm (fun x => v n x - g x) 2 μ := by
    have heq : (fun x => u n x - v n x) =ᵐ[μ]
        (fun x => (u n x - f x) - (v n x - g x)) := by
      filter_upwards [hfg] with x hx
      rw [hx]
      abel
    rw [eLpNorm_congr_ae heq]
    exact eLpNorm_sub_le (f := fun x => u n x - f x) (g := fun x => v n x - g x)
      (p := 2) (μ := μ) (by norm_num)
  have hsum : Tendsto
      (fun n => eLpNorm (fun x => u n x - f x) 2 μ +
        eLpNorm (fun x => v n x - g x) 2 μ) atTop (𝓝 0) := by
    simpa only [add_zero] using huf.add hvg
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hsum
    (fun _ => zero_le) hbound

private theorem integral_norm_sub_sq_tendsto_zero
    (u v : ℕ → P → X) (f g : P → X)
    (hu : ∀ n, MemLp (u n) 2 μ) (hv : ∀ n, MemLp (v n) 2 μ)
    (huf : Tendsto (fun n => eLpNorm (fun x => u n x - f x) 2 μ) atTop (𝓝 0))
    (hvg : Tendsto (fun n => eLpNorm (fun x => v n x - g x) 2 μ) atTop (𝓝 0))
    (hfg : f =ᵐ[μ] g) :
    Tendsto (fun n => ∫ x, ‖u n x - v n x‖ ^ 2 ∂μ) atTop (𝓝 0) := by
  have h := tendsto_eLpNorm_sub_of_tendsto_eLpNorm_sub_of_ae_eq u v f g
    huf hvg hfg
  have hr := (ENNReal.tendsto_toReal (by simp : (0 : ℝ≥0∞) ≠ ∞)).comp h
  have heq (n : ℕ) : (∫ x, ‖u n x - v n x‖ ^ 2 ∂μ) =
      (eLpNorm (fun x => u n x - v n x) 2 μ).toReal ^ 2 := by
    have hsub : MemLp (fun x => u n x - v n x) 2 μ :=
      (hu n).sub (hv n)
    have hm : MemLp (fun x => ‖u n x - v n x‖) 2 μ := hsub.norm
    rw [DifferentialGeometry.Analysis.Integration.integral_sq_eq_l2 hm]
    rw [eLpNorm_norm _ hsub.aestronglyMeasurable]
  simpa only [heq, Function.comp_def, ENNReal.toReal_zero, zero_pow (by decide : 2 ≠ 0)]
    using hr.pow 2

theorem tendsto_integral_norm_sub_sq_of_tendsto_eLpNorm_sub_of_ae_eq_of_measure_le
    (hν : ν ≤ μ) (u v : ℕ → P → X) (f g : P → X)
    (hu : ∀ n, MemLp (u n) 2 μ) (hv : ∀ n, MemLp (v n) 2 μ)
    (huf : Tendsto (fun n => eLpNorm (fun x => u n x - f x) 2 μ) atTop (𝓝 0))
    (hvg : Tendsto (fun n => eLpNorm (fun x => v n x - g x) 2 μ) atTop (𝓝 0))
    (hfg : f =ᵐ[ν] g) :
    Tendsto (fun n => ∫ x, ‖u n x - v n x‖ ^ 2 ∂ν) atTop (𝓝 0) := by
  apply integral_norm_sub_sq_tendsto_zero u v f g
    (fun n => (hu n).mono_measure hν) (fun n => (hv n).mono_measure hν) _ _ hfg
  · exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds huf
      (fun _ => zero_le) (fun n => eLpNorm_mono_measure _ hν)
  · exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hvg
      (fun _ => zero_le) (fun n => eLpNorm_mono_measure _ hν)

theorem tendsto_integral_norm_sub_sq_of_tendsto_eLpNorm_sub_of_ae_eq
    (u v : ℕ → P → X) (f g : P → X)
    (hu : ∀ n, MemLp (u n) 2 μ) (hv : ∀ n, MemLp (v n) 2 μ)
    (huf : Tendsto (fun n => eLpNorm (fun x => u n x - f x) 2 μ) atTop (𝓝 0))
    (hvg : Tendsto (fun n => eLpNorm (fun x => v n x - g x) 2 μ) atTop (𝓝 0))
    (hfg : f =ᵐ[μ] g) :
    Tendsto (fun n => ∫ x, ‖u n x - v n x‖ ^ 2 ∂μ) atTop (𝓝 0) :=
  tendsto_integral_norm_sub_sq_of_tendsto_eLpNorm_sub_of_ae_eq_of_measure_le
    le_rfl u v f g hu hv huf hvg hfg

theorem tendsto_setIntegral_norm_sub_sq_of_tendsto_eLpNorm_sub_of_ae_eq
    (S : Set P) (u v : ℕ → P → X) (f g : P → X)
    (hu : ∀ n, MemLp (u n) 2 μ) (hv : ∀ n, MemLp (v n) 2 μ)
    (huf : Tendsto (fun n => eLpNorm (fun x => u n x - f x) 2 μ) atTop (𝓝 0))
    (hvg : Tendsto (fun n => eLpNorm (fun x => v n x - g x) 2 μ) atTop (𝓝 0))
    (hfg : f =ᵐ[μ.restrict S] g) :
    Tendsto (fun n => ∫ x in S, ‖u n x - v n x‖ ^ 2 ∂μ) atTop (𝓝 0) :=
  tendsto_integral_norm_sub_sq_of_tendsto_eLpNorm_sub_of_ae_eq_of_measure_le
    Measure.restrict_le_self u v f g hu hv huf hvg hfg

end MeasureTheory

end
