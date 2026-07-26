import DifferentialGeometry.Analysis.Parabolic.Euclidean.HeatKernelCancel
import DifferentialGeometry.Analysis.Parabolic.Euclidean.KochLammPotential
import Mathlib.Analysis.Calculus.ContDiff.Comp

/-!
# Smooth compactly supported Euclidean heat potentials

This file transfers spatial derivatives of the Euclidean heat kernel onto a
smooth compactly supported source.  These identities remove the nonintegrable
terminal-time singularity of the raw second heat derivative and are the
physical-space input for the zero-initial-data energy proof of the causal
`L^2` Hessian estimate.
-/

noncomputable section

open MeasureTheory Set
open scoped RealInnerProductSpace ContDiff

namespace DifferentialGeometry
namespace Analysis
namespace Parabolic
namespace Euclidean

variable {V : Type*}
  [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  [MeasurableSpace V] [BorelSpace V] [Nontrivial V]

omit [InnerProductSpace ℝ V] [FiniteDimensional ℝ V] [MeasurableSpace V]
  [BorelSpace V] [Nontrivial V] in
/-- A spatial slice of a compactly supported space-time function is compactly
supported. -/
theorem slice_compact (f : ℝ × V → ℝ) (hfc : HasCompactSupport f) (s : ℝ) :
    HasCompactSupport (fun y : V ↦ f (s, y)) := by
  let K : Set V := Prod.snd '' tsupport f
  have hK : IsCompact K := hfc.image continuous_snd
  refine HasCompactSupport.of_support_subset_isCompact hK ?_
  intro y hy
  refine ⟨(s, y), subset_tsupport f ?_, rfl⟩
  exact hy

omit [MeasurableSpace V] [BorelSpace V] [Nontrivial V] in
private theorem heat_sub_fderiv {t : ℝ} (ht : 0 < t) (v x y : V) :
    fderiv ℝ (fun z : V ↦ heatKernel t (x - z)) y v =
      -heatD1 t v (x - y) := by
  have hsub : HasFDerivAt (fun z : V ↦ x - z)
      ((0 : V →L[ℝ] V) - ContinuousLinearMap.id ℝ V) y :=
    (hasFDerivAt_const (x := y) (c := x)).sub (hasFDerivAt_id y)
  have h := (heatKernel_hasFDeriv ht (x - y)).comp y hsub
  have h' : HasFDerivAt (fun z : V ↦ heatKernel t (x - z))
      ((heatD1Map t (x - y)).comp
        ((0 : V →L[ℝ] V) - ContinuousLinearMap.id ℝ V)) y := by
    simpa only [Function.comp_apply] using h
  rw [h'.fderiv]
  simp

omit [MeasurableSpace V] [BorelSpace V] [Nontrivial V] in
private theorem d1_sub_fderiv {t : ℝ} (ht : 0 < t) (v w x y : V) :
    fderiv ℝ (fun z : V ↦ heatD1 t v (x - z)) y w =
      -heatD2 t v w (x - y) := by
  have hsub : HasFDerivAt (fun z : V ↦ x - z)
      ((0 : V →L[ℝ] V) - ContinuousLinearMap.id ℝ V) y :=
    (hasFDerivAt_const (x := y) (c := x)).sub (hasFDerivAt_id y)
  have h := (heatD1_hasFDeriv ht v (x - y)).comp y hsub
  have h' : HasFDerivAt (fun z : V ↦ heatD1 t v (x - z))
      ((heatD2Map t v (x - y)).comp
        ((0 : V →L[ℝ] V) - ContinuousLinearMap.id ℝ V)) y := by
    simpa only [Function.comp_apply] using h
  rw [h'.fderiv]
  simp

omit [Nontrivial V] in
/-- Move one spatial derivative of the heat kernel onto a smooth compactly
supported scalar source. -/
theorem heatD1_ibp {t : ℝ} (ht : 0 < t) (v x : V) (g : V → ℝ)
    (hg : ContDiff ℝ ∞ g) (hgc : HasCompactSupport g) :
    ∫ y : V, heatD1 t v (x - y) * g y =
      ∫ y : V, heatKernel t (x - y) * fderiv ℝ g y v := by
  have hK : Continuous (fun y : V ↦ heatKernel t (x - y)) := by
    unfold heatKernel baseHeat baseHeatMass heatScale
    fun_prop
  have hD1 : Continuous (fun y : V ↦ heatD1 t v (x - y)) := by
    unfold heatD1 baseD1 baseHeat baseHeatMass heatScale
    fun_prop
  have hdg : Continuous (fun y : V ↦ fderiv ℝ g y v) :=
    (hg.continuous_fderiv (by simp)).clm_apply continuous_const
  have hf'g : Integrable
      (fun y : V ↦ fderiv ℝ g y v * heatKernel t (x - y)) :=
    (hdg.mul hK).integrable_of_hasCompactSupport
      ((hgc.fderiv_apply (𝕜 := ℝ) v).mul_right)
  have hraw : Integrable (fun y : V ↦ g y * heatD1 t v (x - y)) :=
    (hg.continuous.mul hD1).integrable_of_hasCompactSupport hgc.mul_right
  have hfg' : Integrable (fun y : V ↦
      g y * fderiv ℝ (fun z : V ↦ heatKernel t (x - z)) y v) := by
    simpa only [heat_sub_fderiv ht v x, mul_neg] using hraw.neg
  have hfg : Integrable (fun y : V ↦ g y * heatKernel t (x - y)) :=
    (hg.continuous.mul hK).integrable_of_hasCompactSupport hgc.mul_right
  have hparts :=
    integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable
      (μ := (volume : Measure V))
      (f := g) (g := fun y : V ↦ heatKernel t (x - y)) (v := v)
      hf'g hfg' hfg
      (fun y _ ↦ hg.differentiable (by simp) y)
      (fun y _ ↦
        ((heatKernel_hasFDeriv ht (x - y)).comp y
          ((hasFDerivAt_const (x := y) (c := x)).sub (hasFDerivAt_id y))).differentiableAt)
  simp only [heat_sub_fderiv ht v x, mul_neg, integral_neg, neg_inj] at hparts
  simpa only [mul_comm] using hparts

omit [Nontrivial V] in
/-- Move the second spatial derivative of the heat kernel onto one derivative
of a smooth compactly supported scalar source. -/
theorem heatD2_ibp {t : ℝ} (ht : 0 < t) (v w x : V) (g : V → ℝ)
    (hg : ContDiff ℝ ∞ g) (hgc : HasCompactSupport g) :
    ∫ y : V, heatD2 t v w (x - y) * g y =
      ∫ y : V, heatD1 t v (x - y) * fderiv ℝ g y w := by
  have hD1 : Continuous (fun y : V ↦ heatD1 t v (x - y)) := by
    unfold heatD1 baseD1 baseHeat baseHeatMass heatScale
    fun_prop
  have hD2 : Continuous (fun y : V ↦ heatD2 t v w (x - y)) := by
    unfold heatD2 baseD2 baseHeat baseHeatMass heatScale
    fun_prop
  have hdg : Continuous (fun y : V ↦ fderiv ℝ g y w) :=
    (hg.continuous_fderiv (by simp)).clm_apply continuous_const
  have hf'g : Integrable
      (fun y : V ↦ fderiv ℝ g y w * heatD1 t v (x - y)) :=
    (hdg.mul hD1).integrable_of_hasCompactSupport
      ((hgc.fderiv_apply (𝕜 := ℝ) w).mul_right)
  have hraw : Integrable (fun y : V ↦ g y * heatD2 t v w (x - y)) :=
    (hg.continuous.mul hD2).integrable_of_hasCompactSupport hgc.mul_right
  have hfg' : Integrable (fun y : V ↦
      g y * fderiv ℝ (fun z : V ↦ heatD1 t v (x - z)) y w) := by
    simpa only [d1_sub_fderiv ht v w x, mul_neg] using hraw.neg
  have hfg : Integrable (fun y : V ↦ g y * heatD1 t v (x - y)) :=
    (hg.continuous.mul hD1).integrable_of_hasCompactSupport hgc.mul_right
  have hparts :=
    integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable
      (μ := (volume : Measure V))
      (f := g) (g := fun y : V ↦ heatD1 t v (x - y)) (v := w)
      hf'g hfg' hfg
      (fun y _ ↦ hg.differentiable (by simp) y)
      (fun y _ ↦
        ((heatD1_hasFDeriv ht v (x - y)).comp y
          ((hasFDerivAt_const (x := y) (c := x)).sub (hasFDerivAt_id y))).differentiableAt)
  simp only [d1_sub_fderiv ht v w x, mul_neg, integral_neg, neg_inj] at hparts
  simpa only [mul_comm] using hparts

omit [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V] [Nontrivial V] in
private theorem dir_smooth (g : V → ℝ) (hg : ContDiff ℝ ∞ g) (v : V) :
    ContDiff ℝ ∞ (fun y : V ↦ fderiv ℝ g y v) := by
  exact (hg.contDiff_fderiv_apply (m := ∞) (by simp)).comp
    (contDiff_id.prodMk contDiff_const)

omit [Nontrivial V] in
/-- Move both spatial derivatives of the heat kernel onto a smooth compactly
supported scalar source. -/
theorem heatD2_ibp2 {t : ℝ} (ht : 0 < t) (v w x : V) (g : V → ℝ)
    (hg : ContDiff ℝ ∞ g) (hgc : HasCompactSupport g) :
    ∫ y : V, heatD2 t v w (x - y) * g y =
      ∫ y : V, heatKernel t (x - y) *
        fderiv ℝ (fun z : V ↦ fderiv ℝ g z w) y v := by
  rw [heatD2_ibp ht v w x g hg hgc]
  exact heatD1_ibp ht v x (fun y : V ↦ fderiv ℝ g y w)
    (dir_smooth g hg w) (hgc.fderiv_apply (𝕜 := ℝ) w)

omit [Nontrivial V] in
/-- Slice form of the one-derivative transfer identity. -/
theorem heatD1_slice_ibp {t : ℝ} (ht : 0 < t) (v x : V) (s : ℝ)
    (f : ℝ × V → ℝ) (hf : ContDiff ℝ ∞ f) (hfc : HasCompactSupport f) :
    ∫ y : V, heatD1 t v (x - y) * f (s, y) =
      ∫ y : V, heatKernel t (x - y) *
        fderiv ℝ (fun z : V ↦ f (s, z)) y v :=
  heatD1_ibp ht v x (fun y : V ↦ f (s, y))
    (hf.comp (contDiff_prodMk_right s)) (slice_compact f hfc s)

omit [Nontrivial V] in
/-- Slice form of the one-step second-derivative transfer identity. -/
theorem heatD2_slice_ibp {t : ℝ} (ht : 0 < t) (v w x : V) (s : ℝ)
    (f : ℝ × V → ℝ) (hf : ContDiff ℝ ∞ f) (hfc : HasCompactSupport f) :
    ∫ y : V, heatD2 t v w (x - y) * f (s, y) =
      ∫ y : V, heatD1 t v (x - y) *
        fderiv ℝ (fun z : V ↦ f (s, z)) y w :=
  heatD2_ibp ht v w x (fun y : V ↦ f (s, y))
    (hf.comp (contDiff_prodMk_right s)) (slice_compact f hfc s)

omit [Nontrivial V] in
/-- Slice form of the two-derivative transfer identity. -/
theorem heatD2_slice2 {t : ℝ} (ht : 0 < t) (v w x : V) (s : ℝ)
    (f : ℝ × V → ℝ) (hf : ContDiff ℝ ∞ f) (hfc : HasCompactSupport f) :
    ∫ y : V, heatD2 t v w (x - y) * f (s, y) =
      ∫ y : V, heatKernel t (x - y) *
        fderiv ℝ (fun z : V ↦
          fderiv ℝ (fun q : V ↦ f (s, q)) z w) y v :=
  heatD2_ibp2 ht v w x (fun y : V ↦ f (s, y))
    (hf.comp (contDiff_prodMk_right s)) (slice_compact f hfc s)

/-- Spatial directional derivative of a scalar space-time source. -/
def spaceDeriv (v : V) (f : ℝ × V → ℝ) (z : ℝ × V) : ℝ :=
  fderiv ℝ (fun y : V ↦ f (z.1, y)) z.2 v

omit [Nontrivial V] in
/-- A divergence heat potential of a smooth compactly supported source is the
ordinary heat potential of its spatial derivative. -/
theorem heatPot1_eq_pot0 {t : ℝ} (ht : 0 < t) (w : V) (f : ℝ × V → ℝ)
    (hf : ContDiff ℝ ∞ f) (hfc : HasCompactSupport f) (x : V) :
    heatPot1 t w f x = heatPot0 t (spaceDeriv w f) x := by
  unfold heatPot1 heatPot0
  refine intervalIntegral.integral_congr_ae ?_
  have hne : ∀ᵐ s ∂(volume : Measure ℝ), s ≠ t := by
    simp [ae_iff, measure_singleton]
  filter_upwards [hne] with s hst
  intro hs
  rw [Set.uIoc_of_le ht.le] at hs
  have hstlt : s < t := lt_of_le_of_ne hs.2 hst
  simpa only [smul_eq_mul, spaceDeriv] using
    heatD1_slice_ibp (sub_pos.mpr hstlt) w x s f hf hfc

omit [Nontrivial V] in
/-- The ordinary heat potential has zero initial value. -/
@[simp] theorem heatPot0_zero (f : ℝ × V → ℝ) (x : V) :
    heatPot0 0 f x = 0 := by
  simp [heatPot0]

omit [Nontrivial V] in
/-- A divergence heat potential has zero initial value. -/
@[simp] theorem heatPot1_zero (w : V) (f : ℝ × V → ℝ) (x : V) :
    heatPot1 0 w f x = 0 := by
  simp [heatPot1]

end Euclidean
end Parabolic
end Analysis
end DifferentialGeometry

end
