import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.FibrePlugCapping
import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.AssemblySeams

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

theorem exists_standardSphereSeam :
    ∃ W : CompactCarrier.{u}, W.kind = .withBoundary ∧ Nonempty (SphereSeam W) := by
  obtain ⟨W, E, j, h, hlin, d, hW, hc, hn, he, hs, hI, hrest⟩ :=
    exists_fibrePlugCapping.{u}
  exact ⟨W, hW, ⟨⟨d, hs, hI⟩⟩⟩

def standardSphereSeamCarrier : CompactCarrier.{u} := exists_standardSphereSeam.choose

def standardSphereSeam : SphereSeam standardSphereSeamCarrier.{u} :=
  exists_standardSphereSeam.choose_spec.2.some

end GC.GraphManifold.Assembly
