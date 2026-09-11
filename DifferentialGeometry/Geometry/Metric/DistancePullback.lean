import DifferentialGeometry.Geometry.Metric.Pullback.Local
import DifferentialGeometry.Geometry.Metric.Comparison.DistanceScaling

set_option autoImplicit false
noncomputable section
open Set Function Bundle Manifold DifferentialGeometry
open scoped Manifold ContDiff ENNReal
namespace DifferentialGeometry.Geometry.Metric

variable {E F H H' M N : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  [TopologicalSpace H] [TopologicalSpace H']
  {I : ModelWithCorners ℝ E H} {J : ModelWithCorners ℝ F H'}
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M]
  [TopologicalSpace N] [ChartedSpace H' N] [IsManifold J ∞ N] [T2Space N]

omit [FiniteDimensional ℝ F] [T2Space N] in
attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
private theorem edistOf_localPullMetric_le
    (g : SmoothRiemannianMetric J N) (f : M → N)
    (hf : IsLocalDiffeomorph I J ∞ f) (x y : M) :
    riemannianEDistOf g (f x) (f y) ≤ riemannianEDistOf (localPullMetric g f hf) x y := by
  let : RiemannianBundle (TangentSpace J : N → Type _) := ⟨g.toRiemannianMetric⟩
  let : RiemannianBundle (TangentSpace I : M → Type _) :=
    ⟨(localPullMetric g f hf).toRiemannianMetric⟩
  have henorm : ∀ (p : N) (v : TangentSpace J p),
      ‖v‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner p v v)) := by
    intro p v
    rw [← ofReal_norm, norm_eq_sqrt_real_inner]
    rfl
  change riemannianEDist J (f x) (f y) ≤ riemannianEDist I x y
  by_contra hnot
  obtain ⟨γ, hγ0, hγ1, hγ, hlen⟩ :=
    exists_lt_of_riemannianEDist_lt (lt_of_not_ge hnot)
  have hmap : ContMDiffOn 𝓘(ℝ) J 1 (f ∘ γ) (Icc 0 1) :=
    (hf.contMDiff.of_le (by simp)).comp_contMDiffOn hγ
  have hbound := riemannianEDist_le_pathELength (x := f x) (y := f y) hmap
    (by simp only [Function.comp_apply, hγ0])
    (by simp only [Function.comp_apply, hγ1]) zero_le_one
  rw [localPull_pathLen g henorm f hf hγ] at hbound
  exact (not_lt_of_ge hbound) hlen

omit [FiniteDimensional ℝ F] [T2Space N] in
private theorem localPullMetric_eq_pullbackMetricCross
    (g : SmoothRiemannianMetric J N) (Φ : M ≃ₘ⟮I, J⟯ N) :
    localPullMetric g Φ Φ.isLocalDiffeomorph = Diffeomorph.pullbackMetricCross g Φ := by
  apply SmoothRiemannianMetric.ext_inner
  intro x v w
  rw [localPullMetric_inner, Diffeomorph.pullbackMetricCross_inner]

private theorem localPullMetric_symm_pullbackMetricCross
    (g : SmoothRiemannianMetric J N) (Φ : M ≃ₘ⟮I, J⟯ N) :
    localPullMetric (Diffeomorph.pullbackMetricCross g Φ) Φ.symm
      Φ.symm.isLocalDiffeomorph = g := by
  apply SmoothRiemannianMetric.ext_inner
  intro p v w
  have hd := (Φ.toOpenPartialHomeomorph_mdifferentiable (by decide)).comp_symm_deriv
    (show p ∈ (Φ.toHomeomorph.toOpenPartialHomeomorph).target from mem_univ p)
  have hv : mfderiv I J Φ (Φ.symm p) (mfderiv J I Φ.symm p v) = v :=
    congrArg (fun D => D v) hd
  have hw : mfderiv I J Φ (Φ.symm p) (mfderiv J I Φ.symm p w) = w :=
    congrArg (fun D => D w) hd
  rw [localPullMetric_inner, Diffeomorph.pullbackMetricCross_inner, hv, hw,
    Φ.apply_symm_apply]

theorem edistOf_pullbackMetricCross
    (g : SmoothRiemannianMetric J N) (Φ : M ≃ₘ⟮I, J⟯ N) (x y : M) :
    riemannianEDistOf (Diffeomorph.pullbackMetricCross g Φ) x y =
      riemannianEDistOf g (Φ x) (Φ y) := by
  apply le_antisymm
  · have h := edistOf_localPullMetric_le (Diffeomorph.pullbackMetricCross g Φ)
      Φ.symm Φ.symm.isLocalDiffeomorph (Φ x) (Φ y)
    rw [localPullMetric_symm_pullbackMetricCross, Φ.symm_apply_apply, Φ.symm_apply_apply] at h
    exact h
  · have h := edistOf_localPullMetric_le g Φ Φ.isLocalDiffeomorph x y
    rw [localPullMetric_eq_pullbackMetricCross] at h
    exact h

end DifferentialGeometry.Geometry.Metric
