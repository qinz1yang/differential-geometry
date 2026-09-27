import DifferentialGeometry.Geometry.Metric.ProductIsometry
import DifferentialGeometry.Geometry.Flow.RicciFlow.Uniqueness.Forward.Isometry

noncomputable section
open Bundle Set
open DifferentialGeometry.Geometry.Curvature
open scoped Manifold ContDiff

namespace DifferentialGeometry.PDE.RicciFlow

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [T2Space M] [ConnectedSpace M]

theorem ricci_flow_prod_real_pullback_eq_of_initial_isometry
    (g : ℝ → SmoothRiemannianMetric I M) {a b : ℝ} (hab : a < b)
    (hdim : Module.finrank ℝ E = 2)
    (hscalar : ∀ x, metricScalarAt (g a) x ≠ 0)
    (hjoint : ContMDiffOn (𝓘(ℝ, ℝ).prod I) (I.prod 𝓘(ℝ, E →L[ℝ] E →L[ℝ] ℝ)) ∞
      (fun p : ℝ × M => (⟨p.2, (g p.1).inner p.2⟩ :
        TotalSpace (E →L[ℝ] E →L[ℝ] ℝ)
          (fun x => TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ)))
      (Ico a b ×ˢ (Set.univ : Set M)))
    (hpde : ∀ t ∈ Ico a b, ∀ x : M, ∀ v w : TangentSpace I x,
      HasDerivWithinAt (fun s : ℝ => (g s).inner x v w)
        (-2 * ricciTensor (g t) x v w) (Ici a) t)
    (Φ : (M × ℝ) ≃ₘ⟮I.prod 𝓘(ℝ, ℝ), I.prod 𝓘(ℝ, ℝ)⟯ (M × ℝ))
    (hinit : Diffeomorph.pullbackMetricCross ((g a).prod (euclideanMetric (E := ℝ))) Φ =
      (g a).prod (euclideanMetric (E := ℝ))) :
    ∀ t ∈ Ico a b,
      Diffeomorph.pullbackMetricCross ((g t).prod (euclideanMetric (E := ℝ))) Φ =
        (g t).prod (euclideanMetric (E := ℝ)) := by
  let _ : NeZero (Module.finrank ℝ E) := ⟨by omega⟩
  obtain ⟨φ, ψ, rfl, hφ, hψ⟩ :=
    exists_prod_isometries_of_scalar_ne_zero (g a) hdim hscalar Φ hinit
  intro t ht
  rw [Diffeomorph.pullbackMetricCross_eq_pullbackMetric,
    Diffeomorph.pullbackMetric_prodCongr, hψ,
    ricci_flow_pullback_eq_of_initial_isometry g hab hjoint hpde φ hφ t ht]

end DifferentialGeometry.PDE.RicciFlow
