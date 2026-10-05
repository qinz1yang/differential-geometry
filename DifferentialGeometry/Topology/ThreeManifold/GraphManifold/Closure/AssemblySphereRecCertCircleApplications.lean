import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.AssemblySphereRecCertCircle

/-!
# FC42 sphere recursion, packet S4 (group G1): consumers

Lane ASM-SPH2. The certificate's lifted circle region restricted to a capped component has cornered
region the preimage of the transported region.
-/

set_option autoImplicit false

noncomputable section

open Set Function
open DifferentialGeometry DifferentialGeometry.Topology GC.Endpoint GC.GraphManifold Manifold
open scoped Manifold ContDiff Topology

universe u

namespace GC.GraphManifold.Assembly

namespace DecompositionCertificate

variable {W : CompactCarrier.{u}} {n : ℕ} {E : BoundaryTori W n} (D : DecompositionCertificate W E)
  (c : Fin D.sphereSeamCount) (X : SphereCutCapped W (D.sphereSeam c) E) (DQ : X.Q.Components)
  (i : Fin DQ.count)

/-- **Consumer (G1).** The circle region of a capped component: the preimage of the transported
cornered region of `D`. -/
theorem region_toComponent_liftCircleRegion :
    ((D.liftCircleRegion c X).toComponent DQ i).region =
      Subtype.val ⁻¹' (X.transport '' D.circ.region) := by
  rw [CircleRegion.region_toComponent, region_liftCircleRegion]

end DecompositionCertificate

end GC.GraphManifold.Assembly
