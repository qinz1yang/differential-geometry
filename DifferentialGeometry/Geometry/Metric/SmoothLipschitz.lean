import DifferentialGeometry.Geometry.Metric.CompactDerivative
import DifferentialGeometry.Geometry.Metric.Comparison.DistanceScaling
import Mathlib.MeasureTheory.Integral.IntervalIntegral.ContDiff



noncomputable section

open Bundle Manifold DifferentialGeometry Filter Set MeasureTheory
open scoped Bundle Manifold ContDiff Topology ENNReal NNReal

attribute [local instance] normedAddCommGroupTangentSpaceVectorSpace
  normedSpaceTangentSpaceVectorSpace

namespace DifferentialGeometry.Geometry

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
set_option backward.isDefEq.respectTransparency false in
theorem edist_comp_le_metric_path_length
    (g : SmoothRiemannianMetric I M) {f : M → F} {C : ℝ≥0}
    (hf : ContMDiff I 𝓘(ℝ, F) 1 f)
    (hbound : ∀ (x : M) (v : TangentSpace I x),
      ‖(mfderiv I 𝓘(ℝ, F) f x v : F)‖ ≤ C * Real.sqrt (g.inner x v v))
    {γ : ℝ → M} (hγ : ContMDiffOn 𝓘(ℝ, ℝ) I 1 γ (Icc 0 1)) :
    edist (f (γ 0)) (f (γ 1)) ≤ (C : ℝ≥0∞) *
      ∫⁻ t in Icc (0 : ℝ) 1, ENNReal.ofReal (Real.sqrt (g.inner (γ t)
        (mfderiv 𝓘(ℝ, ℝ) I γ t (1 : ℝ)) (mfderiv 𝓘(ℝ, ℝ) I γ t (1 : ℝ)))) := by
  have hη : ContDiffOn ℝ 1 (f ∘ γ) (Icc 0 1) :=
    contMDiffOn_iff_contDiffOn.mp (hf.comp_contMDiffOn hγ)
  have hh := enorm_sub_le_lintegral_deriv_of_contDiffOn_Icc hη zero_le_one
  rw [← edist_eq_enorm_sub, edist_comm] at hh
  apply hh.trans
  rw [← restrict_Ioo_eq_restrict_Icc, ← lintegral_const_mul' _ _ ENNReal.coe_ne_top]
  apply lintegral_mono_ae
  filter_upwards [ae_restrict_mem measurableSet_Ioo] with t ht
  have hγt := (hγ t ⟨ht.1.le, ht.2.le⟩).contMDiffAt (Icc_mem_nhds ht.1 ht.2)
  have hD := mfderiv_comp t (hf.mdifferentiableAt one_ne_zero)
    (hγt.mdifferentiableAt one_ne_zero)
  have hder : deriv (f ∘ γ) t =
      (mfderiv I 𝓘(ℝ, F) f (γ t)) (mfderiv 𝓘(ℝ, ℝ) I γ t (1 : ℝ)) := by
    rw [← fderiv_apply_one_eq_deriv, ← mfderiv_eq_fderiv, hD]
    rfl
  rw [hder]
  have hb := ENNReal.ofReal_le_ofReal (hbound (γ t) (mfderiv 𝓘(ℝ, ℝ) I γ t (1 : ℝ)))
  simpa only [ENNReal.ofReal_mul C.coe_nonneg, ENNReal.ofReal_coe_nnreal, ofReal_norm] using hb

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
set_option backward.isDefEq.respectTransparency false in
theorem edist_map_le_of_metric_mfderiv_bound
    (g : SmoothRiemannianMetric I M) {f : M → F} {C : ℝ≥0} (hC : 0 < C)
    (hf : ContMDiff I 𝓘(ℝ, F) 1 f)
    (hbound : ∀ (x : M) (v : TangentSpace I x),
      ‖(mfderiv I 𝓘(ℝ, F) f x v : F)‖ ≤ C * Real.sqrt (g.inner x v v)) (x y : M) :
    edist (f x) (f y) ≤ (C : ℝ≥0∞) * riemannianEDistOf g x y := by
  let : RiemannianBundle (TangentSpace I : M → Type _) := ⟨g.toRiemannianMetric⟩
  have hC0 : (C : ℝ≥0∞) ≠ 0 := by exact_mod_cast hC.ne'
  change edist (f x) (f y) ≤ (C : ℝ≥0∞) * Manifold.riemannianEDist I x y
  rw [Manifold.riemannianEDist, ENNReal.mul_iInf_of_ne hC0 ENNReal.coe_ne_top]
  apply le_iInf
  intro γ
  rw [ENNReal.mul_iInf_of_ne hC0 ENNReal.coe_ne_top]
  apply le_iInf
  intro hγ
  rw [lintegral_norm_mfderiv_Icc_eq_pathELength_projIcc, pathELength_eq_lintegral_mfderiv_Icc]
  have hc := edist_comp_le_metric_path_length g hf hbound
    (hγ.comp_contMDiffOn contMDiffOn_projIcc)
  have hn (p : M) (v : TangentSpace I p) :
      ENNReal.ofReal (Real.sqrt (g.inner p v v)) = ‖v‖ₑ := by
    rw [← ofReal_norm, norm_eq_sqrt_real_inner]
    rfl
  simp only [Function.comp_apply, projIcc_left, projIcc_right, hn] at hc
  change edist (f (γ 0)) (f (γ 1)) ≤ _ at hc
  simp only [γ.source, γ.target] at hc
  convert! hc using 1

theorem exists_riemannian_lipschitz_of_contMDiff
    [FiniteDimensional ℝ E] [CompactSpace M] [T2Space M]
    (g : SmoothRiemannianMetric I M) {f : M → F} (hf : ContMDiff I 𝓘(ℝ, F) 1 f) :
    ∃ C : ℝ≥0, 0 < C ∧ ∀ x y, edist (f x) (f y) ≤ (C : ℝ≥0∞) * riemannianEDistOf g x y := by
  obtain ⟨B, hB⟩ := exists_metric_mfderiv_bound g hf
  have hbound : ∀ (x : M) (v : TangentSpace I x),
      ‖(mfderiv I 𝓘(ℝ, F) f x v : F)‖ ≤ (B + 1 : ℝ≥0) * Real.sqrt (g.inner x v v) := by
    intro x v
    exact (hB x v).trans (mul_le_mul_of_nonneg_right (by simp) (Real.sqrt_nonneg _))
  exact ⟨B + 1, by positivity, edist_map_le_of_metric_mfderiv_bound g (by positivity) hf hbound⟩

end DifferentialGeometry.Geometry
