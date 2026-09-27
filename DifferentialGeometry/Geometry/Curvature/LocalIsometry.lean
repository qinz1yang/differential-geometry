import DifferentialGeometry.Geometry.Curvature.Naturality.Pullback.Local

noncomputable section

open Bundle DifferentialGeometry DifferentialGeometry.Geometry.Curvature
open Set TopologicalSpace
open scoped Manifold ContDiff Topology

namespace DifferentialGeometry.Geometry.Riemannian

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [CompleteSpace E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M N : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [TopologicalSpace N] [ChartedSpace H N] [IsManifold I ∞ N]
  [T2Space M] [T2Space N]

theorem metricRm04StdAt_of_pullback_on_opens
    (g : SmoothRiemannianMetric I M) (h : SmoothRiemannianMetric I N)
    (U : Opens M) (V : Opens N) [SigmaCompactSpace U] [SigmaCompactSpace V]
    (Φ : U ≃ₘ⟮I, I⟯ V)
    (heq : ∀ (y : U) (v w : TangentSpace I y),
      g.inner (y : M) v w = h.inner (Φ y : N)
        (mfderiv I I (Φ : U → V) y v) (mfderiv I I (Φ : U → V) y w))
    (x : U) (v w z u : TangentSpace I x) :
    metricRm04StandardAt g (x : M) v w z u =
      metricRm04StandardAt h (Φ x : N)
        (mfderiv I I (Φ : U → V) x v) (mfderiv I I (Φ : U → V) x w)
        (mfderiv I I (Φ : U → V) x z) (mfderiv I I (Φ : U → V) x u) := by
  have hm : g.restrictOpen U = Diffeomorph.pullbackMetric (h.restrictOpen V) Φ := by
    apply SmoothRiemannianMetric.ext_inner
    intro y v w
    rw [SmoothRiemannianMetric.restrictOpen_inner, Diffeomorph.pullbackMetric_inner,
      SmoothRiemannianMetric.restrictOpen_inner]
    exact heq y v w
  have hr := metricRm04StandardAt_restrictOpen g U x v w z u
  rw [hm] at hr
  have hp := metricRm04StandardAt_pullback_localDiffeo h V U Φ x v w z u
  simpa only [mfderiv_subtype_val_apply] using hr.symm.trans hp

end DifferentialGeometry.Geometry.Riemannian
