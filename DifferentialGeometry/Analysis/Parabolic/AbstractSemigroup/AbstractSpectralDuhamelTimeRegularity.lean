import DifferentialGeometry.Analysis.Parabolic.AbstractSemigroup.AbstractSpectralDuhamel
import DifferentialGeometry.Analysis.Calculus.HilbertBasisDerivative
import DifferentialGeometry.Analysis.Spectral.Intrinsic.HeatSemigroup.TimeDeriv
import Mathlib.Analysis.Calculus.ContDiff.Deriv

noncomputable section

open Set Filter Topology MeasureTheory
open scoped RealInnerProductSpace InnerProductSpace BigOperators ENNReal

namespace DifferentialGeometry
namespace Analysis
namespace Parabolic

open DifferentialGeometry.Analysis.Parabolic.QuasiLinear

variable {ι : Type*} {X : Type*} [NormedAddCommGroup X]
  [InnerProductSpace ℝ X] [CompleteSpace X]

private theorem spectralDuhamel_integration_by_parts
    (lam t : ℝ) {f f' : ℝ → ℝ}
    (hf : ∀ s, HasDerivAt f (f' s) s) (hf' : Continuous f') :
    -lam * (∫ s in (0 : ℝ)..t, Real.exp (-lam * (t - s)) * f s) + f t =
      Real.exp (-lam * t) * f 0 +
        ∫ s in (0 : ℝ)..t, Real.exp (-lam * (t - s)) * f' s := by
  have hfcont : Continuous f := continuous_iff_continuousAt.mpr fun s => (hf s).continuousAt
  let g : ℝ → ℝ := fun s => Real.exp (-lam * (t - s)) * f s
  let g' : ℝ → ℝ := fun s =>
    lam * Real.exp (-lam * (t - s)) * f s +
      Real.exp (-lam * (t - s)) * f' s
  have hg : ∀ s, HasDerivAt g (g' s) s := by
    intro s
    have hlin : HasDerivAt (fun q : ℝ => -lam * (t - q)) lam s := by
      convert ((hasDerivAt_const s t).sub (hasDerivAt_id s)).const_mul (-lam) using 1
      all_goals ring
    have hexp := hlin.exp
    convert hexp.mul (hf s) using 1
    simp only [g']
    ring
  have hexpcont : Continuous (fun s : ℝ => Real.exp (-lam * (t - s))) := by
    fun_prop
  have hleft : Continuous
      (fun s : ℝ => lam * (Real.exp (-lam * (t - s)) * f s)) :=
    (hexpcont.mul hfcont).const_mul lam
  have hright : Continuous
      (fun s : ℝ => Real.exp (-lam * (t - s)) * f' s) :=
    hexpcont.mul hf'
  have hg' : Continuous g' := by
    simpa only [g', Pi.add_apply, mul_assoc] using hleft.add hright
  have hftc := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun s _ => hg s) (hg'.intervalIntegrable 0 t)
  have hsplit :
      (∫ s in (0 : ℝ)..t, g' s) =
        lam * (∫ s in (0 : ℝ)..t, Real.exp (-lam * (t - s)) * f s) +
          ∫ s in (0 : ℝ)..t, Real.exp (-lam * (t - s)) * f' s := by
    rw [show g' = fun s : ℝ =>
        lam * (Real.exp (-lam * (t - s)) * f s) +
          Real.exp (-lam * (t - s)) * f' s from by
      funext s
      simp only [g']
      ring]
    rw [intervalIntegral.integral_add
      (hleft.intervalIntegrable 0 t) (hright.intervalIntegrable 0 t),
      intervalIntegral.integral_const_mul]
  rw [hsplit] at hftc
  simp only [g] at hftc
  have hg_t : Real.exp (-lam * (t - t)) * f t = f t := by simp
  have hg_zero : Real.exp (-lam * (t - 0)) * f 0 = Real.exp (-lam * t) * f 0 := by
    ring_nf
  rw [hg_t, hg_zero] at hftc
  linarith only [hftc]

def abstractSpectralDuhamelDeriv
    (b : HilbertBasis ι ℝ X) {lam : ι → ℝ} (hlam : ∀ i, 0 ≤ lam i)
    (u₀ : X) (F F' : ℝ → X) (t : ℝ) : X :=
  abstractSpectralSemigroupDeriv b lam t u₀ +
    abstractSpectralSemigroup b hlam t (F 0) +
    abstractSpectralDuhamel b hlam 0 F' t

theorem abstractSpectralDuhamelDeriv_repr_apply
    (b : HilbertBasis ι ℝ X) {lam : ι → ℝ} (hlam : ∀ i, 0 ≤ lam i)
    (u₀ : X) {F F' : ℝ → X} (hF : ∀ s, HasDerivAt F (F' s) s)
    (hF' : Continuous F') {t : ℝ} (ht : 0 < t) (i : ι) :
    (b.repr (abstractSpectralDuhamelDeriv b hlam u₀ F F' t) : ι → ℝ) i =
      -(lam i) *
          (b.repr (abstractSpectralDuhamel b hlam u₀ F t) : ι → ℝ) i +
        (b.repr (F t) : ι → ℝ) i := by
  have hFcont : Continuous F :=
    continuous_iff_continuousAt.mpr fun s => (hF s).continuousAt
  have hfmode : ∀ s, HasDerivAt
      (fun y : ℝ => (b.repr (F y) : ι → ℝ) i)
      ((b.repr (F' s) : ι → ℝ) i) s := by
    intro s
    simpa [b.repr_apply_apply] using
      ((hasDerivAt_const s (b i)).inner ℝ (hF s))
  have hip := spectralDuhamel_integration_by_parts (lam i) t hfmode
    (by
      have hlin : Continuous (fun z : X => (b.repr z : ι → ℝ) i) := by
        simpa only [b.repr_apply_apply] using
          (innerSL (𝕜 := ℝ) (E := X) (b i)).continuous
      exact hlin.comp hF')
  simp only [abstractSpectralDuhamelDeriv]
  rw [map_add, map_add]
  change
    (b.repr (abstractSpectralSemigroupDeriv b lam t u₀) : ι → ℝ) i +
        (b.repr (abstractSpectralSemigroup b hlam t (F 0)) : ι → ℝ) i +
        (b.repr (abstractSpectralDuhamel b hlam 0 F' t) : ι → ℝ) i = _
  rw [abstractSpectralSemigroupDeriv_repr_apply b hlam ht,
    abstractSpectralSemigroup_repr_apply b hlam ht.le,
    abstractSpectralDuhamel_repr_apply b hlam 0 hF' ht.le]
  simp only [heatDerivCoeff_def, heatCoeff_def]
  have hrepr_zero : (b.repr (0 : X) : ι → ℝ) i = 0 := by
    rw [map_zero]
    rfl
  rw [hrepr_zero, mul_zero, zero_add]
  rw [abstractSpectralDuhamel_repr_apply b hlam u₀ hFcont ht.le]
  linarith only [hip]

theorem abstractSpectralDuhamel_hasDerivAt_of_hasDerivAt
    (b : HilbertBasis ι ℝ X) {lam : ι → ℝ} (hlam : ∀ i, 0 ≤ lam i)
    (u₀ : X) {F F' : ℝ → X} (hF : ∀ s, HasDerivAt F (F' s) s)
    (hF' : Continuous F') {t : ℝ} (ht : 0 < t) :
    HasDerivAt (abstractSpectralDuhamel b hlam u₀ F)
      (abstractSpectralDuhamelDeriv b hlam u₀ F F' t) t := by
  have hFcont : Continuous F :=
    continuous_iff_continuousAt.mpr fun s => (hF s).continuousAt
  let v : ℝ → X := fun q =>
    abstractSpectralDuhamelDeriv b hlam u₀ F F' q
  have hv : ContinuousOn v (Set.Ioi 0) := by
    unfold v abstractSpectralDuhamelDeriv
    exact ((abstractSpectralSemigroupDeriv_continuousOn b hlam u₀).add
      ((abstractSpectralSemigroup_continuousOn b hlam (F 0)).mono
        Set.Ioi_subset_Ici_self)).add
      ((duhamel_continuousOn (abstractSpectralBoundedC0Semigroup b hlam) 0 hF').mono
        Set.Ioi_subset_Ici_self)
  change HasDerivAt (abstractSpectralDuhamel b hlam u₀ F) (v t) t
  refine hasDerivAt_of_inner_hilbertBasis b isOpen_Ioi hv ?_ ht
  intro q hq i
  have hmodal := abstractSpectralDuhamel_hasDerivAt_repr_apply b hlam u₀ hFcont hq i
  have hcandidate := abstractSpectralDuhamelDeriv_repr_apply b hlam u₀ hF hF' hq i
  have hcandidate' :
      ⟪b i, v q⟫_ℝ =
        -(lam i) *
            (b.repr (abstractSpectralDuhamel b hlam u₀ F q) : ι → ℝ) i +
          (b.repr (F q) : ι → ℝ) i := by
    simpa only [v, b.repr_apply_apply] using hcandidate
  have hmodal' : HasDerivAt
      (fun s : ℝ => ⟪b i, abstractSpectralDuhamel b hlam u₀ F s⟫_ℝ)
      (-(lam i) *
          (b.repr (abstractSpectralDuhamel b hlam u₀ F q) : ι → ℝ) i +
        (b.repr (F q) : ι → ℝ) i) q := by
    simpa only [b.repr_apply_apply] using hmodal
  exact hcandidate' ▸ hmodal'

theorem abstractSpectralDuhamel_hasDerivAt_of_contDiff
    (b : HilbertBasis ι ℝ X) {lam : ι → ℝ} (hlam : ∀ i, 0 ≤ lam i)
    (u₀ : X) {F : ℝ → X} (hF : ContDiff ℝ 1 F) {t : ℝ} (ht : 0 < t) :
    HasDerivAt (abstractSpectralDuhamel b hlam u₀ F)
      (abstractSpectralDuhamelDeriv b hlam u₀ F (deriv F) t) t := by
  exact abstractSpectralDuhamel_hasDerivAt_of_hasDerivAt b hlam u₀
    (fun q => (hF.differentiable one_ne_zero q).hasDerivAt)
    hF.continuous_deriv_one ht

end Parabolic
end Analysis
end DifferentialGeometry

end
