import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.AssemblyL1ModelNormalForm

/-!
The accepted rotational model supplies a genuine two-vertex cycle normal form at scale one eighth
on the same fixed solid torus, with all four actual necks and the complete rounded union.
-/

set_option autoImplicit false

noncomputable section

open DifferentialGeometry GC.Endpoint GC.GraphManifold Manifold

namespace GC.GraphManifold.Assembly

universe u

def standardCycleNormalForm :
    CycleNormalForm (𝓡 3) SphereCarrier.{u} 2 (1 / 8) solidTorusSet.{u} :=
  (modelCycleNormalForm (len := 2) (ε := 1 / 8)
    (by norm_num) (by norm_num) (by norm_num)).toCycleNormalForm

end GC.GraphManifold.Assembly
