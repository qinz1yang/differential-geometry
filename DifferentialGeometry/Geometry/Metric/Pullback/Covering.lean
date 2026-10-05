import DifferentialGeometry.Geometry.Metric.Pullback.Local

noncomputable section
open Bundle Manifold
open scoped Manifold ContDiff
open DifferentialGeometry

namespace DifferentialGeometry.Geometry.Riemannian

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M C : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [TopologicalSpace C] [ChartedSpace H C] [IsManifold I ∞ C] [T2Space C]


theorem localPullMetric_deck_isometry (g : SmoothRiemannianMetric I M)
    (proj : C → M) (hproj : IsLocalDiffeomorph I I ∞ proj) (τ : C ≃ₘ⟮I, I⟯ C)
    (hdeck : ∀ z, proj (τ z) = proj z) (z : C) (v w : TangentSpace I z) :
    (localPullMetric g proj hproj).inner (τ z) (mfderiv I I τ z v) (mfderiv I I τ z w) =
      (localPullMetric g proj hproj).inner z v w := by
  have heq : (proj ∘ τ) = proj := funext hdeck
  have hd (u : TangentSpace I z) :
      mfderiv I I proj (τ z) (mfderiv I I τ z u) = mfderiv I I proj z u := by
    have hc := mfderiv_comp_apply (I := I) (I' := I) (I'' := I)
      (g := proj) (f := (τ : C → C)) (x := z)
      (hproj.contMDiff.mdifferentiable (by decide) (τ z))
      (τ.contMDiff.mdifferentiable (by decide) z) u
    rw [heq] at hc
    exact hc.symm
  rw [localPullMetric_inner, localPullMetric_inner, hd v, hd w, hdeck]

end DifferentialGeometry.Geometry.Riemannian
