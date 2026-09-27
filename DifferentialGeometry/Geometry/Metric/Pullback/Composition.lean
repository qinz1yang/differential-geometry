import DifferentialGeometry.Geometry.Metric.Pullback.Cross

set_option autoImplicit false
noncomputable section
open Set Function Bundle Manifold
open DifferentialGeometry
open scoped Manifold ContDiff

namespace DifferentialGeometry.Geometry.Metric

variable {E F H G Q N P : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  [TopologicalSpace H] [TopologicalSpace G]
  {I : ModelWithCorners ℝ E H} {J : ModelWithCorners ℝ F G}
  [TopologicalSpace Q] [ChartedSpace H Q] [IsManifold I ∞ Q]
  [TopologicalSpace N] [ChartedSpace H N] [IsManifold I ∞ N] [T2Space N]
  [TopologicalSpace P] [ChartedSpace G P]

theorem pullbackMetricCross_symm_comp_inner (g : SmoothRiemannianMetric I Q)
    (e : Q ≃ₘ⟮I, I⟯ N) (f : P → Q) (hf : ContMDiff J I ∞ f)
    (x : P) (V W : TangentSpace J x) :
    (Diffeomorph.pullbackMetricCross g e.symm).inner (e (f x))
      (mfderiv J I (e ∘ f) x V) (mfderiv J I (e ∘ f) x W) =
        g.inner (f x) (mfderiv J I f x V) (mfderiv J I f x W) := by
  let : T2Space Q := e.toHomeomorph.symm.t2Space
  have he : Diffeomorph.pullbackMetricCross (Diffeomorph.pullbackMetricCross g e.symm) e = g :=
    Diffeomorph.pullbackMetricCross_symm_eq_iff.mpr rfl
  conv_rhs => rw [← he]
  rw [Diffeomorph.pullbackMetricCross_inner,
    mfderiv_comp x (e.contMDiff.mdifferentiableAt (by simp)) (hf.mdifferentiableAt (by simp))]
  rfl

end DifferentialGeometry.Geometry.Metric
