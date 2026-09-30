import DifferentialGeometry.Geometry.Neck.OrderReduction
import DifferentialGeometry.Topology.ThreeManifold.Surgery.FiniteCap.SphericalCutCore
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.NormalizedNeckDatum
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.GeometricCutoffRemainingFields

set_option autoImplicit false
noncomputable section
open Set Function Manifold TopologicalSpace
open DifferentialGeometry.Geometry.Neck DifferentialGeometry.Geometry
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Topology.ThreeManifold.Surgery
open scoped Manifold ContDiff

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.NormalizedNeck

universe u v

private local instance : Fact (Module.finrank ℝ ThreeSpace = 3) := ⟨by simp⟩
private local instance : Fact (Module.finrank ℝ ThreeSpace = 2 + 1) := ⟨by simp⟩

variable {M : Type u} [TopologicalSpace M] [ChartedSpace ThreeSpace M]
  [IsManifold ThreeModel ∞ M] [T2Space M]
  (U : Opens M) [SigmaCompactSpace U] {g : SmoothRiemannianMetric ThreeModel U}
  {ι : Type v} {δ₀ : ι → ℝ} {k : ι → ℕ}

omit [SigmaCompactSpace U] in
theorem lowerOrder_oriented_rotatedDatum_family
    (N : ∀ i, NormalizedNeck g (δ₀ i) (k i))
    {δ : ℝ} (hδ : ∀ i, δ₀ i ≤ δ) (hδ1 : δ < 1)
    (e : ι → ThreeSpace ≃ₗᵢ[ℝ] ThreeSpace)
    (he : ∀ i, sphereDiffeo (n := 2) (e i) spherePoint = (N i).sphereMark)
    (side : ι → Bool) {m : ℕ} (hm : ∀ i, m ≤ k i)
    {Q : ℝ} (hQ : ∀ i, (N i).scale = Q) :
    let d := fun i => (((N i).monoDelta (hδ i) hδ1).rotatedDatum (e i) (he i) (side i)).oriented
    let d₀ : ∀ i, normalizedDatum g (N i).center δ m := fun i => (d i).lowerOrder (hm i)
    (∀ i, (d₀ i).map = (d i).map) ∧
    (∀ i, (d₀ i).retainedSide = true) ∧
    (∀ i, metricScalarAt g (N i).center = Q) ∧
    (∀ i (σ : ℝ) (hσ : σ ^ 2 = 1), (d₀ i).offsetPoint hσ = (d i).offsetPoint hσ) ∧
    (∀ i, neckAmbientMap U (d₀ i) = neckAmbientMap U (d i)) ∧
    ∀ i, IsLocalDiffeomorph NeckCylinderModel ThreeModel ∞ (neckAmbientMap U (d₀ i)) := by
  dsimp only
  refine ⟨fun _ => rfl,fun _ => rfl,?_,fun _ _ _ => rfl,fun _ => rfl,?_⟩
  · intro i
    exact (N i).scale_scalar.symm.trans (hQ i)
  · intro i
    exact isLocalDiffeomorph_neckAmbientMap U _

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.NormalizedNeck
