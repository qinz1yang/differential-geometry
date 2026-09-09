import DifferentialGeometry.Geometry.Metric.ProductIsometry
import DifferentialGeometry.Geometry.Metric.UniversalCover.DeckIsometryGlobal

set_option autoImplicit false

noncomputable section

open scoped Manifold ContDiff

namespace DifferentialGeometry.Geometry.Curvature

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] {H : Type*} [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {N : Type*} [TopologicalSpace N] [ChartedSpace H N]
  [IsManifold I ∞ N] [T2Space N]
  {K : Type*} [TopologicalSpace K]
  {J : ModelWithCorners ℝ E K}
  {U : Type*} [TopologicalSpace U] [ChartedSpace K U]
  [IsManifold J ∞ U] [T2Space U]

theorem exists_affine_product_conjugate_of_isometry
    [ConnectedSpace N]
    (g : SmoothRiemannianMetric I N) (hdim : Module.finrank ℝ E = 2)
    (hscalar : ∀ x, metricScalarAt g x ≠ 0)
    (G : SmoothRiemannianMetric J U)
    (F : Diffeomorph (I.prod 𝓘(ℝ, ℝ)) J (N × ℝ) U ∞)
    (hF : Diffeomorph.pullbackMetricCross G F =
      g.prod (euclideanMetric (E := ℝ)))
    (Φ : Diffeomorph J J U U ∞)
    (hΦ : Diffeomorph.pullbackMetricCross G Φ = G) :
    ∃ (φ : N ≃ₘ⟮I, I⟯ N) (ε c : ℝ),
      (ε = 1 ∨ ε = -1) ∧ Diffeomorph.pullbackMetric g φ = g ∧
        ∀ y r, (F.trans (Φ.trans F.symm)) (y, r) = (φ y, ε * r + c) := by
  have hFsym : Diffeomorph.pullbackMetricCross
      (g.prod (euclideanMetric (E := ℝ))) F.symm = G :=
    (Diffeomorph.pullbackMetricCross_symm_eq_iff.mp hF)
  have hconj : Diffeomorph.pullbackMetricCross
      (g.prod (euclideanMetric (E := ℝ)))
      (F.trans (Φ.trans F.symm)) = g.prod (euclideanMetric (E := ℝ)) := by
    calc
      Diffeomorph.pullbackMetricCross
          (g.prod (euclideanMetric (E := ℝ)))
          (F.trans (Φ.trans F.symm)) =
        Diffeomorph.pullbackMetricCross
          (Diffeomorph.pullbackMetricCross
            (g.prod (euclideanMetric (E := ℝ))) (Φ.trans F.symm)) F := by
          exact (Diffeomorph.pullbackMetricCross_trans
            (g.prod (euclideanMetric (E := ℝ))) F (Φ.trans F.symm)).symm
      _ = Diffeomorph.pullbackMetricCross
          (Diffeomorph.pullbackMetricCross
            (Diffeomorph.pullbackMetricCross
              (g.prod (euclideanMetric (E := ℝ))) F.symm) Φ) F := by
          exact congrArg (fun q => Diffeomorph.pullbackMetricCross q F)
            (Diffeomorph.pullbackMetricCross_trans
              (g.prod (euclideanMetric (E := ℝ))) Φ F.symm).symm
      _ = Diffeomorph.pullbackMetricCross
          (Diffeomorph.pullbackMetricCross G Φ) F := by rw [hFsym]
      _ = Diffeomorph.pullbackMetricCross G F := by rw [hΦ]
      _ = g.prod (euclideanMetric (E := ℝ)) := hF
  exact exists_prod_affine_isometry_of_scalar_ne_zero g hdim hscalar
    (F.trans (Φ.trans F.symm)) hconj

end DifferentialGeometry.Geometry.Curvature
