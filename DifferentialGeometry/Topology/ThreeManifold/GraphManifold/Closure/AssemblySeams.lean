import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.MixedBoundary

/-!
# Chapter-14 assembly: whole interior seams `TorusSeam` and `SphereSeam`

The two seam structures of the chapter-14 assembly certificate, as frozen in the design
(`docs/geometrization/chapter14/design-fc39-fc42-assembly-20261004.md`, §4 row §1). They are copied
verbatim from the frozen interface file. The bridge statements B2 (`AssemblySeamCollar.lean`)
produce them; the certificate and the B3 producer import this file.
-/

set_option autoImplicit false

noncomputable section

open Set
open DifferentialGeometry DifferentialGeometry.Topology GC.Endpoint
open scoped Manifold ContDiff Topology

universe u

namespace GC.GraphManifold.Assembly

/-- A whole interior torus seam (already a whole torus face) with its two-sided signed collar. -/
structure TorusSeam (W : CompactCarrier.{u}) where
  collar : PartialDiffeomorph signedCollarModel W.model (Torus × ℝ) W.Carrier ∞
  source_eq : collar.source = signedCollarSource
  target_interior : collar.target ⊆ W.interior

/-- A whole interior sphere seam with its two-sided signed collar (`MixedBoundary.lean:35–41`). -/
structure SphereSeam (W : CompactCarrier.{u}) where
  collar : PartialDiffeomorph sphereSignedCollarModel W.model
    (ClosureSphere.{u} × ℝ) W.Carrier ∞
  source_eq : collar.source = sphereSignedCollarSource
  target_interior : collar.target ⊆ W.interior

end GC.GraphManifold.Assembly
