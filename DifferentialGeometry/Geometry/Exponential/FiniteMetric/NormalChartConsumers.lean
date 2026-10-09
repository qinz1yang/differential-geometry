import DifferentialGeometry.Geometry.Exponential.FiniteMetric.UniformNormalCharts
import DifferentialGeometry.Geometry.Metric.Basic

/-!
# Consumers of the uniform normal charts (CM1.d)

The smooth case (`r = ⊤`, a `SmoothRiemannianMetric` regarded as finite-order, definitionally)
and the lowest covered order (`C³`, `r = 2`).
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

/-- Uniform normal charts for a smooth metric, through the finite-order theory. -/
theorem exists_uniform_normal_charts_of_smooth
    (g : DifferentialGeometry.SmoothRiemannianMetric I M)
    (hnorm : ∀ (x : M) (w : TangentSpace I x), ‖w‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner x w w)))
    {K : Set M} (hK : IsCompact K) :
    ∃ ρ : ℝ, 0 < ρ ∧ ∀ x ∈ K, ∃ e : OpenPartialHomeomorph E M,
      e.source = {v : E | g.inner x v v < ρ ^ 2} ∧ e.target = ball x ρ ∧
      (∀ v ∈ e.source, (⟨x, v⟩ : TangentBundle I M) ∈ g.expDomain ∧
        e v = g.expMap (⟨x, v⟩ : TangentBundle I M)) ∧
      ContMDiffOn 𝓘(ℝ, E) I ∞ e e.source ∧ ContMDiffOn I 𝓘(ℝ, E) ∞ e.symm e.target ∧
      ∀ v ∈ e.source, dist x (e v) = Real.sqrt (g.inner x v v) :=
  exists_uniform_normal_charts (r := ⊤) g (by exact_mod_cast le_top) hnorm hK

/-- Uniform normal charts for a `C³` metric. -/
theorem exists_uniform_normal_charts_of_C3
    (g : ContMDiffRiemannianMetric I 3 E (TangentSpace I : M → Type _))
    (hnorm : ∀ (x : M) (w : TangentSpace I x), ‖w‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner x w w)))
    {K : Set M} (hK : IsCompact K) :
    ∃ ρ : ℝ, 0 < ρ ∧ ∀ x ∈ K, ∃ e : OpenPartialHomeomorph E M,
      e.source = {v : E | g.inner x v v < ρ ^ 2} ∧ e.target = ball x ρ ∧
      (∀ v ∈ e.source, (⟨x, v⟩ : TangentBundle I M) ∈ g.expDomain ∧
        e v = g.expMap (⟨x, v⟩ : TangentBundle I M)) ∧
      ContMDiffOn 𝓘(ℝ, E) I 2 e e.source ∧ ContMDiffOn I 𝓘(ℝ, E) 2 e.symm e.target ∧
      ∀ v ∈ e.source, dist x (e v) = Real.sqrt (g.inner x v v) :=
  exists_uniform_normal_charts (r := 2) g le_rfl hnorm hK

end Bundle.ContMDiffRiemannianMetric
