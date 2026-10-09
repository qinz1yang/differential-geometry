import DifferentialGeometry.Geometry.Geodesic.FiniteMetric.ShortSegment
import DifferentialGeometry.Geometry.Metric.Basic

/-!
# Consumers of the short-segment theorem (CM1.e)

For a smooth metric (`r = ⊤`, a `SmoothRiemannianMetric` regarded as finite-order, definitionally)
and for a `C³` metric (`r = 2`): over a compact set there is one radius `ρ > 0` below which every
unit-speed metric segment is a radial geodesic `t ↦ exp_x (t • u)` with `|u| = 1`. Obtained by
feeding the charts of `exists_uniform_normal_charts` into `eq_expMap_of_short_segment`.
-/

set_option autoImplicit false

noncomputable section

open Bundle Set Metric
open scoped Manifold ContDiff

namespace Bundle.ContMDiffRiemannianMetric

attribute [-instance] DifferentialGeometry.Tensor0SBundle.tangentSpaceNormedAddCommGroup
  DifferentialGeometry.Tensor0SBundle.tangentSpaceNormedSpace

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [I.Boundaryless] [MetricSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace I x)] [IsRiemannianManifold I M]
  [NeZero (Module.finrank ℝ E)]

/-- Smooth metric: short unit-speed segments from points of a compact set are radial geodesics. -/
theorem exists_radius_eq_expMap_of_short_segment_of_smooth
    (g : DifferentialGeometry.SmoothRiemannianMetric I M)
    (hnorm : ∀ (x : M) (w : TangentSpace I x), ‖w‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner x w w)))
    {K : Set M} (hK : IsCompact K) :
    ∃ ρ : ℝ, 0 < ρ ∧ ∀ x ∈ K, ∀ (c : ℝ → M) (ℓ : ℝ), 0 ≤ ℓ → ℓ < ρ → c 0 = x →
      (∀ s ∈ Icc 0 ℓ, ∀ t ∈ Icc 0 ℓ, dist (c s) (c t) = |s - t|) →
      ∃ u : E, g.inner x u u = 1 ∧
        ∀ t ∈ Icc 0 ℓ, c t = g.expMap (⟨x, t • u⟩ : TangentBundle I M) := by
  obtain ⟨ρ, hρ, hch⟩ :=
    exists_uniform_normal_charts (r := ⊤) g (by exact_mod_cast le_top) hnorm hK
  refine ⟨ρ, hρ, fun x hx c ℓ hℓ hℓρ hc0 hseg => ?_⟩
  obtain ⟨e, he⟩ := hch x hx
  exact eq_expMap_of_short_segment (r := ⊤) g (by exact_mod_cast le_top) hnorm e he hℓ hℓρ hc0 hseg

/-- `C³` metric: short unit-speed segments from points of a compact set are radial geodesics. -/
theorem exists_radius_eq_expMap_of_short_segment_of_C3
    (g : ContMDiffRiemannianMetric I 3 E (TangentSpace I : M → Type _))
    (hnorm : ∀ (x : M) (w : TangentSpace I x), ‖w‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner x w w)))
    {K : Set M} (hK : IsCompact K) :
    ∃ ρ : ℝ, 0 < ρ ∧ ∀ x ∈ K, ∀ (c : ℝ → M) (ℓ : ℝ), 0 ≤ ℓ → ℓ < ρ → c 0 = x →
      (∀ s ∈ Icc 0 ℓ, ∀ t ∈ Icc 0 ℓ, dist (c s) (c t) = |s - t|) →
      ∃ u : E, g.inner x u u = 1 ∧
        ∀ t ∈ Icc 0 ℓ, c t = g.expMap (⟨x, t • u⟩ : TangentBundle I M) := by
  obtain ⟨ρ, hρ, hch⟩ := exists_uniform_normal_charts (r := 2) g le_rfl hnorm hK
  refine ⟨ρ, hρ, fun x hx c ℓ hℓ hℓρ hc0 hseg => ?_⟩
  obtain ⟨e, he⟩ := hch x hx
  exact eq_expMap_of_short_segment (r := 2) g le_rfl hnorm e he hℓ hℓρ hc0 hseg

end Bundle.ContMDiffRiemannianMetric
