import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.AssemblyFC42Components

/-!
# Consumer of B3: the capped carrier of a sphere cut has a component decomposition

`SphereCutCapped.nonempty_components`: for a connected carrier `W`, the capped carrier `X.Q` of any
`SphereCutCapped W S E` has a `Components` structure — the `DQ` input of the L2 theorems
(`exists_rawGraphPresentation_of_sphereCut_nonseparating` / `_separating`, V2) and of
`SphereCutCapped.components_count`. The capped carrier has a point: `W` has one, the fold is onto,
and the core embedding sends the cut carrier into `X.Q`.
-/

set_option autoImplicit false

noncomputable section

open Set
open DifferentialGeometry DifferentialGeometry.Topology GC.Endpoint
open scoped Manifold ContDiff Topology

universe u

namespace GC.GraphManifold.Assembly

/-- The capped carrier of a sphere cut of a connected carrier has a point. -/
theorem SphereCutCapped.nonempty_Q {W : CompactCarrier.{u}} [ConnectedSpace W.Carrier]
    {S : SphereSeam W} {n : ℕ} {E : BoundaryTori W n} (X : SphereCutCapped W S E) :
    Nonempty X.Q.Carrier := by
  obtain ⟨w⟩ := (inferInstance : Nonempty W.Carrier)
  obtain ⟨c, -⟩ := X.surjective w
  exact ⟨X.capping.core c⟩

/-- **The `DQ` of L2.** The capped carrier of a sphere cut of a connected carrier has a component
decomposition. -/
theorem SphereCutCapped.nonempty_components {W : CompactCarrier.{u}} [ConnectedSpace W.Carrier]
    {S : SphereSeam W} {n : ℕ} {E : BoundaryTori W n} (X : SphereCutCapped W S E) :
    Nonempty X.Q.Components := by
  have := X.nonempty_Q
  exact nonempty_components_of_nonempty X.Q

/-- With the decomposition of B3, a sphere cut of a connected carrier has one or two capped
components (`SphereCutCapped.components_count`, lane ASM-L2). -/
theorem SphereCutCapped.exists_components_count {W : CompactCarrier.{u}} [ConnectedSpace W.Carrier]
    {S : SphereSeam W} {n : ℕ} {E : BoundaryTori W n} (X : SphereCutCapped W S E) :
    ∃ DQ : X.Q.Components, DQ.count = 1 ∨ DQ.count = 2 := by
  obtain ⟨DQ⟩ := X.nonempty_components
  exact ⟨DQ, X.components_count DQ⟩

end GC.GraphManifold.Assembly
