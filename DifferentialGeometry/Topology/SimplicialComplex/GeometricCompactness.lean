import Mathlib.Analysis.Convex.Topology
import Mathlib.Analysis.Normed.Module.Basic
import Mathlib.Analysis.Convex.SimplicialComplex.Basic

set_option autoImplicit false
noncomputable section
namespace DifferentialGeometry.Topology.SimplicialComplex
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]


theorem isCompact_geometricSpace (K : Geometry.SimplicialComplex ℝ E) [Finite K.faces] :
    IsCompact K.space :=
  (Set.toFinite K.faces).isCompact_biUnion (fun s _ => s.finite_toSet.isCompact_convexHull ℝ)


instance compactSpace_geometricSpace (K : Geometry.SimplicialComplex ℝ E) [Finite K.faces] :
    CompactSpace K.space := isCompact_iff_compactSpace.mp (isCompact_geometricSpace K)

end DifferentialGeometry.Topology.SimplicialComplex
