/-
Copyright (c) 2026 Bennett Chow. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bennett Chow, OpenAI
-/
import DifferentialGeometry.Geometry.Metric.Comparison.CurveEnergy
import DifferentialGeometry.Geometry.Metric.Distance.Ball

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

end

set_option autoImplicit false
noncomputable section
open Set MeasureTheory
open scoped Manifold ContDiff ENNReal

namespace DifferentialGeometry.Geometry.Riemannian

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

theorem riemannianEDistOf_toReal_sq_le_curveEnergy_of_mem_Icc
    (g : SmoothRiemannianMetric I M) {γ : ℝ → M} {a b s t : ℝ}
    (hγ : ContMDiffOn 𝓘(ℝ, ℝ) I 1 γ (Icc a b))
    (hs : s ∈ Icc a b) (ht : t ∈ Icc a b) :
    (riemannianEDistOf g (γ s) (γ t)).toReal ^ 2 ≤ (b - a) * curveEnergy g γ a b := by
  have hE := integrableOn_inner_mfderiv_self_of_contMDiffOn g hγ
  have hordered (u v : ℝ) (hu : u ∈ Icc a b) (hv : v ∈ Icc a b) (huv : u ≤ v) :
      (riemannianEDistOf g (γ u) (γ v)).toReal ^ 2 ≤ (b - a) * curveEnergy g γ a b := by
    have hsub : Icc u v ⊆ Icc a b := Icc_subset_Icc hu.1 hv.2
    have hd := riemannianEDistOf_toReal_sq_le_curveEnergy g huv (hγ.mono hsub) (hE.mono_set hsub)
    have hmono := curveEnergy_mono g hu.1 huv hv.2 hE
    exact hd.trans ((mul_le_mul_of_nonneg_left hmono (sub_nonneg.mpr huv)).trans
      (mul_le_mul_of_nonneg_right (by linarith [hu.1, hv.2]) (curveEnergy_nonneg g (hu.1.trans hu.2))))
  rcases le_total s t with hst | hts
  · exact hordered s t hs ht hst
  · rw [riemannianEDistOf_comm g (γ s) (γ t)]
    exact hordered t s ht hs hts

theorem riemannianEDistOf_ne_top_of_mem_Icc
    (g : SmoothRiemannianMetric I M) {γ : ℝ → M} {a b s t : ℝ}
    (hγ : ContMDiffOn 𝓘(ℝ, ℝ) I 1 γ (Icc a b))
    (hs : s ∈ Icc a b) (ht : t ∈ Icc a b) :
    riemannianEDistOf g (γ s) (γ t) ≠ ⊤ := by
  have hE := integrableOn_inner_mfderiv_self_of_contMDiffOn g hγ
  have hordered (u v : ℝ) (hu : u ∈ Icc a b) (hv : v ∈ Icc a b) (huv : u ≤ v) :
      riemannianEDistOf g (γ u) (γ v) ≠ ⊤ := by
    have hsub : Icc u v ⊆ Icc a b := Icc_subset_Icc hu.1 hv.2
    exact ne_top_of_le_ne_top ENNReal.ofReal_ne_top
      (edistOf_le_energy g huv (hγ.mono hsub) (hE.mono_set hsub))
  rcases le_total s t with hst | hts
  · exact hordered s t hs ht hst
  · rw [riemannianEDistOf_comm g (γ s) (γ t)]
    exact hordered t s ht hs hts

theorem sq_le_curveEnergy_of_not_mapsTo_of_ball_subset
    (g : SmoothRiemannianMetric I M) {γ : ℝ → M} {a b t r : ℝ} {U : Set M}
    (hγ : ContMDiffOn 𝓘(ℝ, ℝ) I 1 γ (Icc a b))
    (ht : t ∈ Icc a b) (hr : 0 ≤ r)
    (hball : riemannianBallOf g (γ t) r ⊆ U)
    (hexit : ¬ MapsTo γ (Icc a b) U) :
    r ^ 2 ≤ (b - a) * curveEnergy g γ a b := by
  obtain ⟨s, hs, hsU⟩ : ∃ s ∈ Icc a b, γ s ∉ U := by
    simpa only [MapsTo, not_forall, exists_prop] using hexit
  have hfar : ENNReal.ofReal r ≤ riemannianEDistOf g (γ t) (γ s) := by
    apply le_of_not_gt
    intro hlt
    exact hsU (hball hlt)
  have hreal : r ≤ (riemannianEDistOf g (γ t) (γ s)).toReal :=
    (ENNReal.ofReal_le_iff_le_toReal (riemannianEDistOf_ne_top_of_mem_Icc g hγ ht hs)).mp hfar
  exact (pow_le_pow_left₀ hr hreal 2).trans
    (riemannianEDistOf_toReal_sq_le_curveEnergy_of_mem_Icc g hγ ht hs)

end DifferentialGeometry.Geometry.Riemannian
