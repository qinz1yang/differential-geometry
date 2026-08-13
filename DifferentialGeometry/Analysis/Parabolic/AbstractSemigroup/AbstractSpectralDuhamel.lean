import DifferentialGeometry.Analysis.Parabolic.AbstractSemigroup.AbstractSpectralSemigroupContinuity
import DifferentialGeometry.Analysis.Parabolic.QuasiLinear.Semigroup.DuhamelMap
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

noncomputable section

open Set Filter Topology MeasureTheory
open scoped RealInnerProductSpace InnerProductSpace BigOperators ENNReal

namespace DifferentialGeometry
namespace Analysis
namespace Parabolic

open DifferentialGeometry.Analysis.Parabolic.QuasiLinear

variable {ι : Type*} {X : Type*} [NormedAddCommGroup X]
  [InnerProductSpace ℝ X] [CompleteSpace X]

def abstractSpectralBoundedC0Semigroup (b : HilbertBasis ι ℝ X)
    {lam : ι → ℝ} (hlam : ∀ i, 0 ≤ lam i) : BoundedC0Semigroup X where
  toFun := abstractSpectralSemigroup b hlam
  apply_zero := abstractSpectralSemigroup_apply_zero b hlam
  apply_add := fun _ _ ht hs => abstractSpectralSemigroup_apply_add b hlam ht hs
  opNorm_le_one := fun t _ => abstractSpectralSemigroup_opNorm_le_one b hlam t
  continuousOn_apply := abstractSpectralSemigroup_continuousOn b hlam

@[simp] theorem abstractSpectralBoundedC0Semigroup_apply
    (b : HilbertBasis ι ℝ X) {lam : ι → ℝ} (hlam : ∀ i, 0 ≤ lam i)
    (t : ℝ) :
    abstractSpectralBoundedC0Semigroup b hlam t =
      abstractSpectralSemigroup b hlam t :=
  rfl

def abstractSpectralDuhamel (b : HilbertBasis ι ℝ X)
    {lam : ι → ℝ} (hlam : ∀ i, 0 ≤ lam i) (u₀ : X) (F : ℝ → X)
    (t : ℝ) : X :=
  duhamel (abstractSpectralBoundedC0Semigroup b hlam) u₀ F t

theorem abstractSpectralDuhamel_repr_apply
    (b : HilbertBasis ι ℝ X) {lam : ι → ℝ} (hlam : ∀ i, 0 ≤ lam i)
    (u₀ : X) {F : ℝ → X} (hF : Continuous F) {t : ℝ} (ht : 0 ≤ t)
    (i : ι) :
    (b.repr (abstractSpectralDuhamel b hlam u₀ F t) : ι → ℝ) i =
      Real.exp (-(lam i) * t) * (b.repr u₀ : ι → ℝ) i +
        ∫ τ in (0 : ℝ)..t,
          Real.exp (-(lam i) * (t - τ)) * (b.repr (F τ) : ι → ℝ) i := by
  unfold abstractSpectralDuhamel duhamel
  rw [map_add]
  change
    (b.repr (abstractSpectralSemigroup b hlam t u₀) : ι → ℝ) i +
        (b.repr (∫ τ in (0 : ℝ)..t,
          abstractSpectralSemigroup b hlam (t - τ) (F τ)) : ι → ℝ) i = _
  rw [abstractSpectralSemigroup_repr_apply b hlam ht]
  rw [heatCoeff_def]
  congr 1
  set ℓ : X →L[ℝ] ℝ := innerSL (𝕜 := ℝ) (E := X) (b i)
  have h_integrable := duhamel_integrable
    (abstractSpectralBoundedC0Semigroup b hlam) hF ht
  have h_integrable' : IntervalIntegrable (fun τ : ℝ =>
      abstractSpectralSemigroup b hlam (t - τ) (F τ))
      MeasureTheory.volume 0 t := by
    simpa only [abstractSpectralBoundedC0Semigroup_apply] using h_integrable
  have h_comm := ℓ.intervalIntegral_comp_comm h_integrable'
  rw [b.repr_apply_apply]
  change ℓ (∫ τ in (0 : ℝ)..t,
      abstractSpectralSemigroup b hlam (t - τ) (F τ)) = _
  rw [← h_comm]
  apply intervalIntegral.integral_congr
  intro τ hτ
  rw [Set.uIcc_of_le ht] at hτ
  have htτ : 0 ≤ t - τ := sub_nonneg.mpr hτ.2
  change ℓ (abstractSpectralSemigroup b hlam (t - τ) (F τ)) = _
  simp only [ℓ, innerSL_apply_apply]
  rw [← b.repr_apply_apply,
    abstractSpectralSemigroup_repr_apply b hlam htτ]
  rfl

private lemma abstractSpectralDuhamel_exp_factor
    (lam t s : ℝ) :
    Real.exp (-lam * (t - s)) = Real.exp (-lam * t) * Real.exp (lam * s) := by
  rw [← Real.exp_add]
  congr 1
  ring

private lemma abstractSpectralDuhamel_integral_factor
    (lam : ℝ) {t : ℝ} (h : ℝ → ℝ)
    (_h_int : IntervalIntegrable (fun s => Real.exp (lam * s) * h s)
      MeasureTheory.volume 0 t) :
    ∫ s in (0 : ℝ)..t, Real.exp (-lam * (t - s)) * h s =
      Real.exp (-lam * t) * ∫ s in (0 : ℝ)..t, Real.exp (lam * s) * h s := by
  have h_eq : (fun s : ℝ => Real.exp (-lam * (t - s)) * h s) =
      (fun s : ℝ => Real.exp (-lam * t) * (Real.exp (lam * s) * h s)) := by
    funext s
    rw [abstractSpectralDuhamel_exp_factor]
    ring
  rw [h_eq, intervalIntegral.integral_const_mul]

theorem abstractSpectralDuhamel_hasDerivAt_repr_apply
    (b : HilbertBasis ι ℝ X) {lam : ι → ℝ} (hlam : ∀ i, 0 ≤ lam i)
    (u₀ : X) {F : ℝ → X} (hF : Continuous F) {t : ℝ} (ht : 0 < t)
    (i : ι) :
    HasDerivAt
      (fun s : ℝ =>
        (b.repr (abstractSpectralDuhamel b hlam u₀ F s) : ι → ℝ) i)
      (-(lam i) *
          (b.repr (abstractSpectralDuhamel b hlam u₀ F t) : ι → ℝ) i +
        (b.repr (F t) : ι → ℝ) i) t := by
  set eigenvalue : ℝ := lam i
  set c₀ : ℝ := (b.repr u₀ : ι → ℝ) i
  set f : ℝ → ℝ := fun s => (b.repr (F s) : ι → ℝ) i
  have hf : Continuous f := by
    have hℓ : Continuous (fun v : X => (b.repr v : ι → ℝ) i) := by
      simpa only [b.repr_apply_apply] using
        (innerSL (𝕜 := ℝ) (E := X) (b i)).continuous
    exact hℓ.comp hF
  set c₁ : ℝ → ℝ := fun s => Real.exp (-eigenvalue * s) * c₀
  set G : ℝ → ℝ := fun s => ∫ r in (0 : ℝ)..s, Real.exp (eigenvalue * r) * f r
  set c₂ : ℝ → ℝ := fun s => Real.exp (-eigenvalue * s) * G s
  have h_split : ∀ s, 0 ≤ s →
      (b.repr (abstractSpectralDuhamel b hlam u₀ F s) : ι → ℝ) i =
        c₁ s + c₂ s := by
    intro s hs
    rw [abstractSpectralDuhamel_repr_apply b hlam u₀ hF hs i]
    have h_int : IntervalIntegrable (fun r => Real.exp (eigenvalue * r) * f r)
        MeasureTheory.volume 0 s :=
      ((Real.continuous_exp.comp
        (continuous_const.mul continuous_id)).mul hf).intervalIntegrable 0 s
    have h_factor := abstractSpectralDuhamel_integral_factor
      (t := s) eigenvalue f h_int
    change Real.exp (-eigenvalue * s) * c₀ +
      ∫ r in (0 : ℝ)..s, Real.exp (-eigenvalue * (s - r)) * f r =
        c₁ s + c₂ s
    rw [h_factor]
  have hc₁ : HasDerivAt c₁ (-eigenvalue * c₁ t) t := by
    have hlin : HasDerivAt (fun s : ℝ => -eigenvalue * s) (-eigenvalue) t := by
      simpa using (hasDerivAt_id (𝕜 := ℝ) t).const_mul (-eigenvalue)
    convert hlin.exp.mul_const c₀ using 1
    all_goals simp only [c₁]
    all_goals ring
  have hG : HasDerivAt G (Real.exp (eigenvalue * t) * f t) t := by
    have hcont : Continuous (fun r : ℝ => Real.exp (eigenvalue * r) * f r) :=
      (Real.continuous_exp.comp
        (continuous_const.mul continuous_id)).mul hf
    exact intervalIntegral.integral_hasDerivAt_right
      (hcont.intervalIntegrable 0 t)
      hcont.aestronglyMeasurable.stronglyMeasurableAtFilter hcont.continuousAt
  have hexp : HasDerivAt (fun s : ℝ => Real.exp (-eigenvalue * s))
      (-eigenvalue * Real.exp (-eigenvalue * t)) t := by
    have hlin : HasDerivAt (fun s : ℝ => -eigenvalue * s) (-eigenvalue) t := by
      simpa using (hasDerivAt_id (𝕜 := ℝ) t).const_mul (-eigenvalue)
    convert hlin.exp using 1
    all_goals ring
  have hc₂raw := hexp.mul hG
  have hc₂ : HasDerivAt c₂ (-eigenvalue * c₂ t + f t) t := by
    convert hc₂raw using 1
    all_goals simp only [c₂]
    have hcancel : Real.exp (-eigenvalue * t) *
        Real.exp (eigenvalue * t) = 1 := by
      calc
        Real.exp (-eigenvalue * t) * Real.exp (eigenvalue * t) =
            Real.exp (-eigenvalue * t + eigenvalue * t) :=
          (Real.exp_add _ _).symm
        _ = Real.exp 0 := by congr 1; ring
        _ = 1 := Real.exp_zero
    rw [show Real.exp (-eigenvalue * t) *
        (Real.exp (eigenvalue * t) * f t) =
        (Real.exp (-eigenvalue * t) * Real.exp (eigenvalue * t)) * f t by ring,
      hcancel, one_mul]
    ring
  have hsum := hc₁.add hc₂
  have hsum' : HasDerivAt (fun s => c₁ s + c₂ s)
      (-eigenvalue * (c₁ t + c₂ t) + f t) t := by
    convert hsum using 1
    all_goals ring
  rw [← h_split t ht.le] at hsum'
  have heq : (fun s : ℝ =>
      (b.repr (abstractSpectralDuhamel b hlam u₀ F s) : ι → ℝ) i) =ᶠ[nhds t]
      (fun s => c₁ s + c₂ s) := by
    filter_upwards [Ioi_mem_nhds ht] with s hs
    exact h_split s hs.le
  exact hsum'.congr_of_eventuallyEq heq

end Parabolic
end Analysis
end DifferentialGeometry

end
