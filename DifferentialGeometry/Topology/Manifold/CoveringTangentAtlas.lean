import DifferentialGeometry.Topology.Manifold.CoveringAtlas
import Mathlib.Geometry.Manifold.MFDeriv.Atlas



noncomputable section
open Bundle Manifold Set
open scoped Manifold ContDiff

namespace DifferentialGeometry.Topology.Manifold

variable {E M C : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  [TopologicalSpace C] {p : C → M}

theorem covering_tangent_trivialization (hp : IsLocalHomeomorph p) :
    letI := coveringChartedSpace (H := E) hp
    letI := covering_isManifold hp 𝓘(ℝ, E)
    ∀ (x y : C) (hy : y ∈ (chartAt E x).source)
      (hb : p y ∈ (chartAt E (p x)).source) (v : TangentSpace 𝓘(ℝ, E) y),
      (trivializationAt E (TangentSpace 𝓘(ℝ, E)) x).continuousLinearEquivAt ℝ y hy v =
        (trivializationAt E (TangentSpace 𝓘(ℝ, E)) (p x)).continuousLinearEquivAt ℝ (p y) hb
          (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) p y v) := by
  let := coveringChartedSpace (H := E) hp
  let := covering_isManifold hp 𝓘(ℝ, E)
  intro x y hy hb v
  rw [Trivialization.coe_continuousLinearEquivAt_eq (R := ℝ) _ hy,
    Trivialization.coe_continuousLinearEquivAt_eq (R := ℝ) _ hb,
    TangentBundle.continuousLinearMapAt_trivializationAt hy,
    TangentBundle.continuousLinearMapAt_trivializationAt hb]
  have heq : (extChartAt 𝓘(ℝ, E) x : C → E) = (extChartAt 𝓘(ℝ, E) (p x)) ∘ p := by
    funext z
    exact coveringChart_apply (H := E) hp x z
  rw [heq]
  exact mfderiv_comp_apply y (mdifferentiableAt_extChartAt hb)
    ((covering_projection_contMDiff hp 𝓘(ℝ, E)).mdifferentiable (by decide) y) v

end DifferentialGeometry.Topology.Manifold
