import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Function.AEEqOfIntegral
import Mathlib.MeasureTheory.Function.LpSpace.Indicator

open MeasureTheory Filter Set
open scoped ENNReal

namespace MeasureTheory

variable {α : Type*} [MeasurableSpace α] {μ : Measure α}

theorem Lp.integral_add_apply
    {X Y : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    [NormedAddCommGroup Y] [NormedSpace ℝ Y]
    (L₁ L₂ : Lp (X →L[ℝ] Y) 2 μ) (u : Lp X 2 μ) :
    (∫ t, (L₁ + L₂) t (u t) ∂μ) =
      (∫ t, L₁ t (u t) ∂μ) + ∫ t, L₂ t (u t) ∂μ := by
  have hint (L : Lp (X →L[ℝ] Y) 2 μ) : Integrable (fun t => L t (u t)) μ := by
    apply ((Lp.memLp L).norm.integrable_mul (Lp.memLp u).norm).mono'
    · exact (ContinuousLinearMap.apply ℝ Y).aestronglyMeasurable_comp₂
        (Lp.aestronglyMeasurable u) (Lp.aestronglyMeasurable L)
    · exact Eventually.of_forall fun t => (L t).le_opNorm (u t)
  rw [← integral_add (hint L₁) (hint L₂)]
  apply integral_congr_ae
  filter_upwards [Lp.coeFn_add L₁ L₂] with t ht
  exact congrArg (fun L : X →L[ℝ] Y => L (u t)) ht

theorem continuous_integral_weight_mul_lp (c : α → ℝ) (hc : MemLp c ∞ μ)
    (f : Lp ℝ 2 μ) :
    Continuous (fun g : Lp ℝ 2 μ => ∫ z, f z * c z * g z ∂μ) := by
  have hfc : MemLp (fun z => f z * c z) 2 μ := by
    simpa only [mul_comm] using (Lp.memLp f).mul' hc
  let fc : Lp ℝ 2 μ := hfc.toLp (fun z => f z * c z)
  have heq : (fun g : Lp ℝ 2 μ => ∫ z, f z * c z * g z ∂μ) =
      (fun g : Lp ℝ 2 μ => inner ℝ fc g) := by
    funext g
    rw [L2.inner_def]
    refine integral_congr_ae ?_
    filter_upwards [hfc.coeFn_toLp] with z hz
    simp only [Real.inner_apply, fc, hz]
  rw [heq]
  exact continuous_const.inner continuous_id

theorem integrable_weight_mul_lp (c : α → ℝ) (hc : MemLp c ∞ μ)
    (f g : Lp ℝ 2 μ) :
    Integrable (fun z => f z * c z * g z) μ := by
  have hfc : MemLp (fun z => f z * c z) 2 μ := by
    simpa only [mul_comm] using (Lp.memLp f).mul' hc
  exact hfc.integrable_mul (Lp.memLp g)

private theorem integral_indicatorConstLp_mul
    {A : Type*} [MeasurableSpace A] {μ : Measure A} {s : Set A}
    (hs : MeasurableSet s) (hμs : μ s ≠ ∞) (f : A → ℝ) :
    (∫ t, indicatorConstLp 2 hs hμs (1 : ℝ) t * f t ∂μ) = ∫ t in s, f t ∂μ := by
  rw [← integral_indicator hs]
  apply integral_congr_ae
  filter_upwards [indicatorConstLp_coeFn (p := 2) (hs := hs) (hμs := hμs) (c := (1 : ℝ))] with t ht
  rw [ht]
  by_cases hts : t ∈ s <;> simp [hts]

theorem Lp.eq_of_integral_mul_dual_eq
    {A X : Type*} [MeasurableSpace A] {μ : Measure A}
    [NormedAddCommGroup X] [NormedSpace ℝ X]
    (L₁ L₂ : Lp (X →L[ℝ] ℝ) 2 μ)
    (h : ∀ (τ : Lp ℝ 2 μ) (x : X),
      (∫ t, τ t * L₁ t x ∂μ) = ∫ t, τ t * L₂ t x ∂μ) : L₁ = L₂ := by
  have hint (L : Lp (X →L[ℝ] ℝ) 2 μ) (s : Set A) (hs : MeasurableSet s) (hμs : μ s < ∞) :
      IntegrableOn (fun t => L t) s μ := by
    let : IsFiniteMeasure (μ.restrict s) := ⟨by simpa using hμs⟩
    exact ((Lp.memLp L).restrict s).integrable (by norm_num)
  apply Lp.ext
  apply Lp.ae_eq_of_forall_setIntegral_eq L₁ L₂ (by norm_num) (by norm_num)
    (hint L₁) (hint L₂)
  intro s hs hμs
  apply ContinuousLinearMap.ext
  intro x
  rw [ContinuousLinearMap.integral_apply (hint L₁ s hs hμs),
    ContinuousLinearMap.integral_apply (hint L₂ s hs hμs)]
  simpa only [integral_indicatorConstLp_mul hs hμs.ne] using
    h (indicatorConstLp 2 hs hμs.ne (1 : ℝ)) x


end MeasureTheory
