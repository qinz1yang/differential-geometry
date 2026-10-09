import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.FibrePlugCapping
import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.AssemblySphereCutCapped

/-!
Actual nonempty standard-model data for the chapter-fourteen assembly interface.
-/

set_option autoImplicit false

noncomputable section

open Set Function
open DifferentialGeometry DifferentialGeometry.Topology GC.Endpoint GC.Seifert GC.GraphManifold
open scoped Manifold ContDiff Topology

universe u

namespace GC.GraphManifold.Assembly

theorem exists_standardSphereCutCapped :
    ∃ (W : CompactCarrier.{u}) (S : SphereSeam W) (E : BoundaryTori W 2),
      W.kind = .withBoundary ∧ Nonempty (SphereCutCapped W S E) := by
  obtain ⟨W, P, j, h, hlin, d, hW, hc, hp, hE, hs, hI, heq, δ, hδ, hδ1,
    C, B, hn, h2, fold, hk, hsm, hsurj, ho, ht, hf, hrel, hq, ⟨K⟩⟩ :=
    exists_fibrePlugCapping.{u}
  refine ⟨W, ⟨d, hs, hI⟩, ?_⟩
  rw [← hE]
  exact ⟨P.toTorus.external.shrink hδ hδ1, hW,
    ⟨⟨C, B, hn, h2, fold, hk, hsm, hsurj, ho, ht, hf,
      fun {x y} hxy => (hrel x y).mp hxy, B.sphereCapCarrier, K⟩⟩⟩

end GC.GraphManifold.Assembly
