import DifferentialGeometry.Topology.ThreeManifold.StandardFactors

/-!
# Maps out of a spherical space form through the sphere

Lane LFR54-QUOT. A map `f` on `S³` that is constant on the fibres of the projection
`S³ → S³ / G` descends to the orbit space (`orbitLift`); it is smooth at the image of every point
where `f` is smooth (`contMDiffAt_orbitLift`), because the projection is a local diffeomorphism.
This is the manifold-valued form of `GC.Seifert.contMDiffAt_lensDescend`.
-/

set_option autoImplicit false

noncomputable section

open Set Filter Metric
open scoped Manifold ContDiff Topology

namespace DifferentialGeometry.Geometry.Collapse.ZeroModel.SpaceForm

open DifferentialGeometry.Topology

variable (G : SphericalSpaceFormGroup)
  {EN : Type*} [NormedAddCommGroup EN] [NormedSpace ℝ EN] {HN : Type*} [TopologicalSpace HN]
  {J : ModelWithCorners ℝ EN HN} {N : Type*} [TopologicalSpace N] [ChartedSpace HN N]

/-- The map on `S³ / G` induced by a fibrewise constant map on `S³`. -/
def orbitLift (f : sphere (0 : EuclideanSpace ℝ (Fin 4)) 1 → N)
    (hf : ∀ x y, G.projection x = G.projection y → f x = f y) : G.Orbit → N :=
  Quotient.lift f fun a b hab => hf a b (Quotient.sound hab)

omit [TopologicalSpace N] in
theorem orbitLift_projection (f : sphere (0 : EuclideanSpace ℝ (Fin 4)) 1 → N)
    (hf : ∀ x y, G.projection x = G.projection y → f x = f y)
    (x : sphere (0 : EuclideanSpace ℝ (Fin 4)) 1) :
    orbitLift G f hf (G.projection x) = f x := rfl

/-- The descended map is smooth wherever the original one is. -/
theorem contMDiffAt_orbitLift (f : sphere (0 : EuclideanSpace ℝ (Fin 4)) 1 → N)
    (hf : ∀ x y, G.projection x = G.projection y → f x = f y)
    (x : sphere (0 : EuclideanSpace ℝ (Fin 4)) 1) (hx : ContMDiffAt (𝓡 3) J ∞ f x) :
    ContMDiffAt (𝓡 3) J ∞ (orbitLift G f hf) (G.projection x) := by
  have hl := G.projection_isLocalDiffeomorph x
  have hc : ContMDiffAt (𝓡 3) J ∞ f (hl.localInverse (G.projection x)) := by
    rw [hl.localInverse_left_inv hl.localInverse_mem_target]
    exact hx
  have h := hc.comp (G.projection x) hl.contMDiffAt_localInverse
  apply h.congr_of_eventuallyEq
  filter_upwards [hl.localInverse_eventuallyEq_right] with q hq
  change orbitLift G f hf q = orbitLift G f hf (G.projection (hl.localInverse q))
  rw [show G.projection (hl.localInverse q) = q from hq]

end DifferentialGeometry.Geometry.Collapse.ZeroModel.SpaceForm
