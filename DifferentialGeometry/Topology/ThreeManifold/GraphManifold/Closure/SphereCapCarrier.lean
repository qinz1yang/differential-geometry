import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.SphereCapBoundary
import
  DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.SphereCapGlobalOrientation

/-!
The actual oriented compact capping quotient and every original retained torus collar.
-/

set_option autoImplicit false

noncomputable section

open Set Function Manifold
open DifferentialGeometry DifferentialGeometry.Topology GC.Endpoint GC.Seifert
open scoped Manifold ContDiff Topology

universe u

namespace GC.GraphManifold.MixedBoundaryCertificate

variable {C : CompactCarrier.{u}} (B : MixedBoundaryCertificate C)

def sphereCapCarrier : CompactCarrier.{u} := by
  letI := B.sphereCapQuotientChartedSpace
  exact {
    kind := .withBoundary
    Carrier := B.SphereCapQuotient
    smooth := B.sphereCapQuotientIsManifold
    orientation := B.sphereCapQuotientOrientation }

theorem sphereCapCarrier_kind : B.sphereCapCarrier.kind = .withBoundary := rfl

def sphereCapRetained : BoundaryTori B.sphereCapCarrier B.torusCount := by
  letI := B.sphereCapQuotientChartedSpace
  let hA := B.exists_sphereCapQuotientAtlas.choose_spec.2
  exact {
    collar := B.sphereCapRetainedCollar hA
    source_eq := B.sphereCapRetainedCollar_source hA
    boundary_zero := B.sphereCapRetainedCollar_zero_boundary hA
    disjoint := B.sphereCapRetainedCollar_disjoint hA }

theorem sphereCapRetained_collar (i : Fin B.torusCount)
    {p : Torus × EuclideanHalfSpace 1} (hp : p ∈ halfCollarSource) :
    B.sphereCapRetained.collar i p = B.sphereCapCore (B.tori.collar i p) := by
  let := B.sphereCapQuotientChartedSpace
  exact B.sphereCapRetainedCollar_apply B.exists_sphereCapQuotientAtlas.choose_spec.2 i hp

theorem sphereCapRetained_exhausted :
    B.sphereCapCarrier.model.boundary B.sphereCapCarrier.Carrier = B.sphereCapRetained.image := by
  let := B.sphereCapQuotientChartedSpace
  rw [show B.sphereCapRetained.image = B.sphereCapCore '' B.tori.image from ?_]
  · exact B.sphereCapQuotient_boundary B.exists_sphereCapQuotientAtlas.choose_spec.2
  · ext q
    constructor
    · intro hq
      obtain ⟨i, t, ht⟩ := mem_iUnion.mp hq
      refine ⟨B.tori.torusMap i t, mem_iUnion.mpr ⟨i, t, rfl⟩, ?_⟩
      exact (B.sphereCapRetained_collar i (zero_mem_halfCollarSource t)).symm.trans ht
    · rintro ⟨x, hx, rfl⟩
      obtain ⟨i, t, rfl⟩ := mem_iUnion.mp hx
      exact mem_iUnion.mpr ⟨i, t, B.sphereCapRetained_collar i (zero_mem_halfCollarSource t)⟩

end GC.GraphManifold.MixedBoundaryCertificate
