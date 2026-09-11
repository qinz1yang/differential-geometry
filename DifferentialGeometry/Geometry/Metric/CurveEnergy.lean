/-
Copyright (c) 2026 Bennett Chow. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bennett Chow, OpenAI
-/
import DifferentialGeometry.Geometry.Metric.Comparison.CurveEnergy

set_option autoImplicit false

noncomputable section

open Bundle Manifold MeasureTheory Set
open scoped ENNReal Manifold ContDiff Topology
open DifferentialGeometry

namespace DifferentialGeometry
namespace Geometry
namespace Riemannian

open DifferentialGeometry.Geometry.Riemannian

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M]

theorem curveEnergy_nonneg (g : SmoothRiemannianMetric I M)
    {γ : ℝ → M} {a b : ℝ} (hab : a ≤ b) :
    0 ≤ curveEnergy (I := I) g γ a b := by
  apply intervalIntegral.integral_nonneg hab
  intro t _ht
  let v := mfderiv 𝓘(ℝ, ℝ) I γ t (1 : ℝ)
  rcases eq_or_ne v 0 with hv | hv
  · simp only [v, hv, map_zero]
    exact le_rfl
  · exact (g.pos (γ t) v hv).le

theorem riemannianEDistOf_toReal_sq_le_curveEnergy
    (g : SmoothRiemannianMetric I M) {γ : ℝ → M} {a b : ℝ}
    (hab : a ≤ b)
    (hγ : ContMDiffOn 𝓘(ℝ, ℝ) I 1 γ (Icc a b))
    (hE : IntegrableOn (fun t =>
      g.inner (γ t)
        (mfderiv 𝓘(ℝ, ℝ) I γ t (1 : ℝ))
        (mfderiv 𝓘(ℝ, ℝ) I γ t (1 : ℝ))) (Icc a b)) :
    (riemannianEDistOf (I := I) g (γ a) (γ b)).toReal ^ 2 ≤
      (b - a) * curveEnergy (I := I) g γ a b := by
  have hENN := edistOf_le_energy (I := I) g hab hγ hE
  have hright : ENNReal.ofReal
      (Real.sqrt (b - a) * Real.sqrt (curveEnergy (I := I) g γ a b)) ≠
        (⊤ : ℝ≥0∞) :=
    ENNReal.ofReal_ne_top
  have hleft : riemannianEDistOf (I := I) g (γ a) (γ b) ≠
      (⊤ : ℝ≥0∞) :=
    ne_top_of_le_ne_top hright hENN
  have hreal := (ENNReal.toReal_le_toReal hleft hright).2 hENN
  have hlen : 0 ≤ b - a := sub_nonneg.mpr hab
  have henergy : 0 ≤ curveEnergy (I := I) g γ a b :=
    curveEnergy_nonneg (I := I) g hab
  rw [ENNReal.toReal_ofReal
    (mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _))] at hreal
  have hsquare :=
    (sq_le_sq₀ ENNReal.toReal_nonneg
      (mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _))).2 hreal
  calc
    (riemannianEDistOf (I := I) g (γ a) (γ b)).toReal ^ 2 ≤
        (Real.sqrt (b - a) *
          Real.sqrt (curveEnergy (I := I) g γ a b)) ^ 2 := hsquare
    _ = (b - a) * curveEnergy (I := I) g γ a b := by
      rw [mul_pow, Real.sq_sqrt hlen, Real.sq_sqrt henergy]


theorem arcLength_nonneg (g : SmoothRiemannianMetric I M) {γ : ℝ → M} {a b : ℝ}
    (hab : a ≤ b) : 0 ≤ Variation.arcLength (I := I) g γ a b :=
  intervalIntegral.integral_nonneg hab (fun _ _ => Real.sqrt_nonneg _)


theorem arcLength_sq_le_curveEnergy (g : SmoothRiemannianMetric I M)
    {γ : ℝ → M} {a b : ℝ} (hab : a ≤ b)
    (hE : IntegrableOn (fun t => g.inner (γ t)
      (mfderiv 𝓘(ℝ, ℝ) I γ t 1) (mfderiv 𝓘(ℝ, ℝ) I γ t 1)) (Icc a b)) :
    Variation.arcLength (I := I) g γ a b ^ 2 ≤ (b - a) * curveEnergy (I := I) g γ a b := by
  have h := arcLength_le_energy g hab hE
  have hs := (sq_le_sq₀ (arcLength_nonneg g hab)
    (mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _))).mpr h
  simpa only [mul_pow, Real.sq_sqrt (sub_nonneg.mpr hab),
    Real.sq_sqrt (curveEnergy_nonneg g hab)] using hs

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
theorem riemannianEDistOf_toReal_le_arcLength (g : SmoothRiemannianMetric I M)
    {γ : ℝ → M} {a b : ℝ} (hab : a ≤ b)
    (hγ : ContMDiffOn 𝓘(ℝ, ℝ) I 1 γ (Icc a b)) :
    (riemannianEDistOf (I := I) g (γ a) (γ b)).toReal ≤ Variation.arcLength (I := I) g γ a b := by
  let : RiemannianBundle (TangentSpace I : M → Type _) := ⟨g.toRiemannianMetric⟩
  have hbound := Geodesic.riemannianEDist_le_arcLength (I := I) g hab hγ
    (fun t _ => tensor0SBundle_enorm_eq_riemannianBundle_enorm (I := I) g (γ t)
      (mfderiv 𝓘(ℝ, ℝ) I γ t 1))
  have hfinite := ne_top_of_le_ne_top ENNReal.ofReal_ne_top hbound
  have hreal := (ENNReal.toReal_le_toReal hfinite ENNReal.ofReal_ne_top).mpr hbound
  simpa only [riemannianEDistOf, ENNReal.toReal_ofReal (arcLength_nonneg g hab)] using hreal

end Riemannian
end Geometry
end DifferentialGeometry
