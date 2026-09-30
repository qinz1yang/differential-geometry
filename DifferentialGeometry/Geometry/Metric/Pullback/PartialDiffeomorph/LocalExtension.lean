import DifferentialGeometry.Geometry.Metric.Construction.LocalExtension
import DifferentialGeometry.Geometry.Metric.Pullback.Cross
import DifferentialGeometry.Topology.Manifold.PartialDiffeomorph.Opens

set_option autoImplicit false
noncomputable section
open TopologicalSpace
open scoped Manifold ContDiff Topology

namespace DifferentialGeometry.Geometry.Riemannian

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
  [FiniteDimensional ℝ F]
  {H : Type*} [TopologicalSpace H] {J : ModelWithCorners ℝ F H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold J ∞ M] [T2Space M]

theorem exists_model_metric_eq_pullback_on_nhds
    (g : SmoothRiemannianMetric J M)
    (Φ : PartialDiffeomorph 𝓘(ℝ, E) J E M ∞) {x : E} (hx : x ∈ Φ.source) :
    ∃ gE : SmoothRiemannianMetric 𝓘(ℝ, E) E,
      ∃ V : Opens E, x ∈ V ∧ (V : Set E) ⊆ Φ.source ∧
        ∀ y ∈ V, ∀ v w : E, gE.inner y v w =
          g.inner (Φ y) (mfderiv 𝓘(ℝ, E) J Φ y v)
            (mfderiv 𝓘(ℝ, E) J Φ y w) := by
  let U : Opens E := ⟨Φ.source, Φ.open_source⟩
  let W : Opens M := ⟨Φ '' (U : Set E), image_opens_isOpen Φ (Set.Subset.refl _)⟩
  let Ψ : Diffeomorph 𝓘(ℝ, E) J U W ∞ :=
    DifferentialGeometry.PartialDiffeomorph.toOpensDiffeo Φ (Set.Subset.refl _)
  let gU := Diffeomorph.pullbackMetricCross (g.restrictOpen W) Ψ
  obtain ⟨gE, V, hVU, hxV, heq⟩ := exists_model_metric_extension U gU ⟨x, hx⟩
  refine ⟨gE, V, hxV, hVU, ?_⟩
  intro y hy v w
  erw [heq ⟨y, hy⟩ v w, Diffeomorph.pullbackMetricCross_inner,
    SmoothRiemannianMetric.restrictOpen_inner]
  have hd (a : E) : mfderiv 𝓘(ℝ, E) J Ψ (Opens.inclusion hVU ⟨y, hy⟩) a =
      mfderiv 𝓘(ℝ, E) J Φ y a :=
    DifferentialGeometry.PartialDiffeomorph.mfderiv_toOpensDiffeo
      Φ (Set.Subset.refl _) (Opens.inclusion hVU ⟨y, hy⟩) a
  erw [hd, hd]
  rfl

end DifferentialGeometry.Geometry.Riemannian
