import DifferentialGeometry.Geometry.Curvature.CurvatureOperator.Derivatives.LocalPullback

set_option autoImplicit false
noncomputable section

namespace DifferentialGeometry.CheegerGromovCompactness

open Set
open scoped _root_.Manifold ContDiff

variable {E H M N : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M]
  [TopologicalSpace N] [ChartedSpace H N] [IsManifold I ∞ N] [T2Space N]

theorem curvDerivNorm_eq_of_partialDiffeomorph_restriction
    (Phi : PartialDiffeomorph I I M N ∞) (U : TopologicalSpace.Opens M)
    (hU : (U : Set M) ⊆ Phi.source)
    (g : SmoothRiemannianMetric I U) (h : SmoothRiemannianMetric I N)
    (hmet : ∀ x : U, ∀ v w : TangentSpace I x,
      g.inner x v w = h.inner (Phi x) (mfderiv I I (Phi : M → N) x v)
        (mfderiv I I (Phi : M → N) x w)) (q : ℕ) (x : U) :
    curvDerivNorm q g x = curvDerivNorm q h (Phi x) := by
  let V : TopologicalSpace.Opens N :=
    ⟨(Phi : M → N) '' (U : Set M), image_opens_isOpen Phi hU⟩
  let e : U ≃ₘ⟮I, I⟯ V := PartialDiffeomorph.toOpensDiffeo Phi hU
  have heq : g = Diffeomorph.pullbackMetricCross (h.restrictOpen V) e := by
    apply SmoothRiemannianMetric.ext_inner
    intro y v w
    rw [Diffeomorph.pullbackMetricCross_inner, SmoothRiemannianMetric.restrictOpen_inner]
    exact (hmet y v w).trans
      (congrArg₂ (fun v' w' => h.inner (Phi (y : M)) v' w')
        (PartialDiffeomorph.mfderiv_toOpensDiffeo Phi hU y v)
        (PartialDiffeomorph.mfderiv_toOpensDiffeo Phi hU y w)).symm
  rw [heq,
    DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.curvDerivNorm_pullbackMetricCross,
    curvDerivNorm_restrictOpen]
  rfl

end DifferentialGeometry.CheegerGromovCompactness

end
