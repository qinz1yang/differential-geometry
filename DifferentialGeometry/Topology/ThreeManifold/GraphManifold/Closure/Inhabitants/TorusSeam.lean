import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Seifert.LensCarrierProductModel
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

def standardTorusSeam : TorusSeam (NoCuts.carrier sphereTwoTimesCircleLift) where
  collar := productCarrierSeam
  source_eq := productCarrierSeam_source
  target_interior := by
    change productCarrierSeam.target ⊆ (𝓡 3).interior _
    rw [ModelWithCorners.interior_eq_univ]
    exact subset_univ _

end GC.GraphManifold.Assembly
