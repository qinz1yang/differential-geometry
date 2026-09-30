import DifferentialGeometry.Analysis.Integration.Lp.OperatorConvergence
import Mathlib.MeasureTheory.Function.LpSeminorm.TriangleInequality
import Mathlib.Analysis.Calculus.FDeriv.Comp
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
import Mathlib.Analysis.Calculus.ContDiff.RCLike
import Mathlib.Analysis.Calculus.ContDiff.Comp

noncomputable section

open MeasureTheory Filter
open scoped ENNReal Topology

namespace MeasureTheory

variable {P X Y : Type*} [MeasurableSpace P] {μ : Measure P}
  [NormedAddCommGroup X] [NormedSpace ℝ X]
  [NormedAddCommGroup Y] [NormedSpace ℝ Y]

theorem tendsto_eLpNorm_clm_apply_of_strong_ae_tendsto
    (A : ℕ → P → X →L[ℝ] Y) (A₀ : P → X →L[ℝ] Y)
    (hA : ∀ n, AEStronglyMeasurable (A n) μ)
    {C : ℝ} (hC : ∀ n, ∀ᵐ t ∂μ, ‖A n t‖ ≤ C)
    (hconv : ∀ᵐ t ∂μ, Tendsto (fun n => A n t) atTop (𝓝 (A₀ t)))
    (v : ℕ → P → X) (v₀ : P → X)
    (hv : ∀ n, MemLp (v n) 2 μ) (hv₀ : MemLp v₀ 2 μ)
    (hlim : Tendsto (fun n => eLpNorm (fun t => v n t - v₀ t) 2 μ) atTop (𝓝 0)) :
    Tendsto (fun n => eLpNorm (fun t => A n t (v n t) - A₀ t (v₀ t)) 2 μ)
      atTop (𝓝 0) := by
  let B (n : ℕ) (t : P) := A n t (v n t - v₀ t)
  let D (n : ℕ) (t : P) := (A n t - A₀ t) (v₀ t)
  have hBm (n : ℕ) : AEStronglyMeasurable (B n) μ :=
    (ContinuousLinearMap.apply ℝ Y).aestronglyMeasurable_comp₂
      ((hv n).sub hv₀).aestronglyMeasurable (hA n)
  have hbound (n : ℕ) : eLpNorm (B n) 2 μ ≤
      ENNReal.ofReal C * eLpNorm (fun t => v n t - v₀ t) 2 μ := by
    apply eLpNorm_le_mul_eLpNorm_of_ae_le_mul (hBm n) _ 2
    filter_upwards [hC n] with t ht
    exact (A n t).le_opNorm (v n t - v₀ t) |>.trans
      (mul_le_mul_of_nonneg_right ht (norm_nonneg _))
  have hBl : Tendsto (fun n => eLpNorm (B n) 2 μ) atTop (𝓝 0) := by
    have ht := ENNReal.Tendsto.const_mul (a := ENNReal.ofReal C) hlim
      (Or.inr ENNReal.ofReal_ne_top)
    simp only [mul_zero] at ht
    exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds ht
      (fun _ => zero_le) hbound
  have hDl : Tendsto (fun n => eLpNorm (D n) 2 μ) atTop (𝓝 0) :=
    tendsto_eLpNorm_clm_apply_sub_of_ae_tendsto (by norm_num) A A₀ hA hC hconv hv₀
  have heq (n : ℕ) : (fun t => A n t (v n t) - A₀ t (v₀ t)) = B n + D n := by
    funext t
    simp only [B, D, Pi.add_apply, map_sub, sub_apply]
    abel
  have ht : Tendsto (fun n => eLpNorm (B n) 2 μ + eLpNorm (D n) 2 μ) atTop (𝓝 0) := by
    simpa only [add_zero] using hBl.add hDl
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds ht (fun _ => zero_le)
  intro n
  change eLpNorm (fun t => A n t (v n t) - A₀ t (v₀ t)) 2 μ ≤ _
  rw [heq n]
  exact eLpNorm_add_le (by norm_num)

end MeasureTheory

end

noncomputable section

open Set MeasureTheory Filter
open scoped Topology ENNReal

namespace MeasureTheory

variable {E F G : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [MeasurableSpace E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  [NormedAddCommGroup G] [NormedSpace ℝ G]
  {μ : Measure E}

theorem tendsto_eLpNorm_fderiv_comp_apply_of_ae_tendsto
    (f : ℕ → E → F) (f₀ : E → F) (r : F → G) (w : E)
    (V : E → F)
    (hf : ∀ n, ∀ᵐ x ∂μ, DifferentiableAt ℝ (f n) x)
    (hr : ∀ n, ∀ᵐ x ∂μ, DifferentiableAt ℝ r (f n x))
    (hA : ∀ n, AEStronglyMeasurable (fun x => fderiv ℝ r (f n x)) μ)
    {C : ℝ} (hC : ∀ n, ∀ᵐ x ∂μ, ‖fderiv ℝ r (f n x)‖ ≤ C)
    (hAr : ∀ᵐ x ∂μ, Tendsto (fun n => fderiv ℝ r (f n x)) atTop
      (𝓝 (fderiv ℝ r (f₀ x))))
    (hdf : ∀ n, MemLp (fun x => fderiv ℝ (f n) x w) 2 μ)
    (hV : MemLp V 2 μ)
    (hlim : Tendsto (fun n => eLpNorm (fun x => fderiv ℝ (f n) x w - V x) 2 μ)
      atTop (𝓝 0)) :
    Tendsto (fun n => eLpNorm (fun x =>
      fderiv ℝ (r ∘ f n) x w - fderiv ℝ r (f₀ x) (V x)) 2 μ) atTop (𝓝 0) := by
  have h := tendsto_eLpNorm_clm_apply_of_strong_ae_tendsto
    (fun n x => fderiv ℝ r (f n x)) (fun x => fderiv ℝ r (f₀ x))
    hA hC hAr (fun n x => fderiv ℝ (f n) x w) V hdf hV hlim
  apply h.congr'
  exact Filter.Eventually.of_forall fun n => eLpNorm_congr_ae (by
    filter_upwards [hf n, hr n] with x hfx hrx
    rw [fderiv_comp x hrx hfx]
    rfl)

end MeasureTheory

end

noncomputable section

open Set MeasureTheory Filter
open scoped Topology ENNReal

namespace MeasureTheory

variable {d : ℕ} {ι : Type*} [Fintype ι]

local notation "E" => EuclideanSpace ℝ (Fin d)
local notation "F" => EuclideanSpace ℝ ι

theorem tendsto_eLpNorm_fderiv_comp_coordinate_of_ae_tendsto
    {Ω : Set E} (u : ℕ → E → F) (f : E → F) (r : F → F)
    (hu : ∀ n, ContDiff ℝ 1 (u n)) (hr : ContDiff ℝ 1 r)
    (j : Fin d) (G : E → F)
    (hA : ∀ n, AEStronglyMeasurable (fun x => fderiv ℝ r (u n x)) (volume.restrict Ω))
    {C : ℝ} (hC : ∀ n, ∀ᵐ x ∂volume.restrict Ω, ‖fderiv ℝ r (u n x)‖ ≤ C)
    (hAr : ∀ᵐ x ∂volume.restrict Ω, Tendsto (fun n => fderiv ℝ r (u n x)) atTop
      (𝓝 (fderiv ℝ r (f x))))
    (hdu : ∀ n, MemLp (fun x => fderiv ℝ (u n) x (EuclideanSpace.single j 1))
      2 (volume.restrict Ω))
    (hG : MemLp G 2 (volume.restrict Ω))
    (hlim : Tendsto (fun n => eLpNorm (fun x =>
      fderiv ℝ (u n) x (EuclideanSpace.single j 1) - G x) 2 (volume.restrict Ω)) atTop (𝓝 0))
    (i : ι) :
    Tendsto (fun n => eLpNorm (fun x =>
      fderiv ℝ (fun y => r (u n y) i) x (EuclideanSpace.single j 1) -
        (fderiv ℝ r (f x) (G x)) i) 2 (volume.restrict Ω)) atTop (𝓝 0) := by
  have ht := tendsto_eLpNorm_clm_apply_of_strong_ae_tendsto
    (fun n x => fderiv ℝ r (u n x)) (fun x => fderiv ℝ r (f x)) hA hC hAr
    (fun n x => fderiv ℝ (u n) x (EuclideanSpace.single j 1)) G hdu hG hlim
  have hA₀ : AEStronglyMeasurable (fun x => fderiv ℝ r (f x)) (volume.restrict Ω) :=
    aestronglyMeasurable_of_tendsto_ae atTop hA hAr
  have htarget : AEStronglyMeasurable
      (fun x => (fderiv ℝ r (f x) (G x)) i) (volume.restrict Ω) :=
    (EuclideanSpace.proj i).continuous.comp_aestronglyMeasurable
      ((ContinuousLinearMap.apply ℝ F).aestronglyMeasurable_comp₂
        hG.aestronglyMeasurable hA₀)
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds ht (fun _ => zero_le)
  intro n
  have hcoord : ContDiff ℝ 1 (fun y => r (u n y) i) :=
    (EuclideanSpace.proj i : F →L[ℝ] ℝ).contDiff.comp (hr.comp (hu n))
  apply eLpNorm_mono_ae
    (((hcoord.continuous_fderiv (by norm_num)).clm_apply continuous_const).aestronglyMeasurable.sub
      htarget)
  filter_upwards [] with x
  have hru :=
    (hr.differentiable (by simp) (u n x)).comp x ((hu n).differentiable (by simp) x)
  have hd : fderiv ℝ (fun y => r (u n y) i) x =
      (EuclideanSpace.proj i).comp (fderiv ℝ (r ∘ u n) x) :=
    ((EuclideanSpace.proj i : F →L[ℝ] ℝ).hasFDerivAt.comp x hru.hasFDerivAt).fderiv
  simp only [Pi.sub_apply]
  rw [hd, fderiv_comp x (hr.differentiable (by simp) (u n x))
    ((hu n).differentiable (by simp) x)]
  exact PiLp.norm_apply_le
    ((fderiv ℝ r (u n x)) (fderiv ℝ (u n) x (EuclideanSpace.single j 1)) -
      (fderiv ℝ r (f x)) (G x)) i

end MeasureTheory

end

noncomputable section

open MeasureTheory Filter
open scoped ENNReal Topology NNReal

namespace MeasureTheory

variable {X F : Type*} [MeasurableSpace X] {μ : Measure X}
  [NormedAddCommGroup F]

theorem LipschitzWith.tendsto_eLpNorm_comp_sub_of_fixed_ae
    {r : F → F} {C : ℝ≥0} (hr : LipschitzWith C r)
    (u : ℕ → X → F) (f : X → F)
    (hf : AEStronglyMeasurable f μ)
    (hfixed : (fun x => r (f x)) =ᵐ[μ] f)
    (hlim : Tendsto (fun n => eLpNorm (fun x => u n x - f x) 2 μ) atTop (𝓝 0)) :
    Tendsto (fun n => eLpNorm (fun x => r (u n x) - f x) 2 μ) atTop (𝓝 0) := by
  have hm : ∀ᶠ n in atTop, AEStronglyMeasurable (fun x => u n x - f x) μ := by
    filter_upwards [hlim.eventually_lt_const (by simp : (0 : ℝ≥0∞) < ⊤)] with n hn
    exact aestronglyMeasurable_of_eLpNorm_ne_top hn.ne
  have hbound : ∀ᶠ n in atTop, eLpNorm (fun x => r (u n x) - f x) 2 μ ≤
      (C : ℝ≥0∞) * eLpNorm (fun x => u n x - f x) 2 μ := by
    filter_upwards [hm] with n hn
    have hum : AEStronglyMeasurable (u n) μ := by
      exact (hn.add hf).congr
        (Filter.Eventually.of_forall fun x => sub_add_cancel (u n x) (f x))
    rw [← ENNReal.ofReal_coe_nnreal]
    apply eLpNorm_le_mul_eLpNorm_of_ae_le_mul
      ((hr.continuous.comp_aestronglyMeasurable hum).sub hf) _ 2
    filter_upwards [hfixed] with x hx
    calc
      ‖r (u n x) - f x‖ = ‖r (u n x) - r (f x)‖ := by rw [hx]
      _ ≤ (C : ℝ) * ‖u n x - f x‖ := hr.norm_sub_le (u n x) (f x)
  have ht := ENNReal.Tendsto.const_mul (a := (C : ℝ≥0∞)) hlim (Or.inr ENNReal.coe_ne_top)
  simp only [mul_zero] at ht
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds ht
    (Filter.Eventually.of_forall fun _ => zero_le) hbound

end MeasureTheory

end
