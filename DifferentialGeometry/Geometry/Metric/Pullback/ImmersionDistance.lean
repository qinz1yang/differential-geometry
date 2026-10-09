import DifferentialGeometry.Geometry.Metric.Pullback.Immersion
import DifferentialGeometry.Geometry.Metric.Path.Composition
import DifferentialGeometry.Geometry.Metric.Distance.Basic

set_option autoImplicit false

noncomputable section

open Bundle Manifold MeasureTheory Set
open scoped Manifold ContDiff ENNReal

namespace DifferentialGeometry

variable {E F H G M N : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  [TopologicalSpace H] [TopologicalSpace G]
  {I : ModelWithCorners ℝ E H} {J : ModelWithCorners ℝ F G}
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M]
  [TopologicalSpace N] [ChartedSpace G N] [IsManifold J ∞ N]

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
theorem riemannianEDistOf_le_pullback
    (g : SmoothRiemannianMetric J N) (f : M → N) (hf : ContMDiff I J ∞ f)
    (himm : ∀ x, Function.Injective (mfderiv I J f x)) (x y : M) :
    riemannianEDistOf g (f x) (f y) ≤
      riemannianEDistOf (g.pullback f hf himm) x y := by
  let : RiemannianBundle (TangentSpace J : N → Type _) := ⟨g.toRiemannianMetric⟩
  let : RiemannianBundle (TangentSpace I : M → Type _) :=
    ⟨(g.pullback f hf himm).toRiemannianMetric⟩
  have henorm (z : M) (v : TangentSpace I z) :
      ‖mfderiv I J f z v‖ₑ = ‖v‖ₑ := by
    rw [← ofReal_norm, ← ofReal_norm, norm_eq_sqrt_real_inner, norm_eq_sqrt_real_inner]
    rfl
  change riemannianEDist J (f x) (f y) ≤ riemannianEDist I x y
  by_contra hnot
  obtain ⟨γ, hγ0, hγ1, hγ, hlen⟩ :=
    exists_lt_of_riemannianEDist_lt (lt_of_not_ge hnot)
  have hmap : ContMDiffOn 𝓘(ℝ) J 1 (f ∘ γ) (Icc 0 1) :=
    (hf.of_le (by simp)).comp_contMDiffOn hγ
  have hlength : pathELength J (f ∘ γ) 0 1 = pathELength I γ 0 1 := by
    apply pathELength_comp_eq_of_enorm_mfderiv_eq f
    · filter_upwards [ae_restrict_mem measurableSet_Ioo] with t ht
      exact ((hγ.mdifferentiableOn one_ne_zero) t ⟨ht.1.le, ht.2.le⟩).mdifferentiableAt
        (Icc_mem_nhds ht.1 ht.2)
    · exact Filter.Eventually.of_forall (fun _ => hf.mdifferentiableAt (by decide))
    · exact Filter.Eventually.of_forall (fun t => henorm (γ t) _)
  have hbound := riemannianEDist_le_pathELength (x := f x) (y := f y) hmap
    (by simp only [Function.comp_apply, hγ0])
    (by simp only [Function.comp_apply, hγ1]) zero_le_one
  rw [hlength] at hbound
  exact (not_lt_of_ge hbound) hlen

end DifferentialGeometry
