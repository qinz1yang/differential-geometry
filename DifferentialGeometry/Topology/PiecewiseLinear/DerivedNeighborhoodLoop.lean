import DifferentialGeometry.Topology.Homotopy.DeformationRetractPath
import DifferentialGeometry.Topology.PiecewiseLinear.DerivedNeighborhoodRetraction

open unitInterval
open DifferentialGeometry.Topology.Homotopy

namespace DifferentialGeometry.Topology.PiecewiseLinear

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {K L : Geometry.SimplicialComplex ℝ E} [Finite K.faces]

open Classical in
noncomputable def derivedNeighborhoodRetractLoop (hL : L.faces ⊆ K.faces)
    {x : derivedNeighborhoodSpace K L} (hx : x ∈ derivedNeighborhoodSubcomplex K L)
    (ℓ : Path x x) : Path x x :=
  (derivedNeighborhoodStrongDeformationRetract hL).retractLoop hx ℓ

open Classical in
theorem homotopic_derivedNeighborhoodRetractLoop (hL : L.faces ⊆ K.faces)
    {x : derivedNeighborhoodSpace K L} (hx : x ∈ derivedNeighborhoodSubcomplex K L)
    (ℓ : Path x x) : ℓ.Homotopic (derivedNeighborhoodRetractLoop hL hx ℓ) :=
  (derivedNeighborhoodStrongDeformationRetract hL).homotopic_retractLoop hx ℓ

open Classical in
theorem derivedNeighborhoodRetractLoop_mem_space (hL : L.faces ⊆ K.faces)
    {x : derivedNeighborhoodSpace K L} (hx : x ∈ derivedNeighborhoodSubcomplex K L)
    (ℓ : Path x x) (s : I) :
    ((derivedNeighborhoodRetractLoop hL hx ℓ s : derivedNeighborhoodSpace K L) : E) ∈ L.space :=
  (derivedNeighborhoodStrongDeformationRetract hL).retractLoop_mem hx ℓ s

open Classical in
theorem derivedNeighborhoodRetractLoop_apply (hL : L.faces ⊆ K.faces)
    {x : derivedNeighborhoodSpace K L} (hx : x ∈ derivedNeighborhoodSubcomplex K L)
    (ℓ : Path x x) (s : I) :
    ((derivedNeighborhoodRetractLoop hL hx ℓ s : derivedNeighborhoodSpace K L) : E) =
      subcomplexBarycentricProjection (barycentricSubdivision K) (barycentricSubdivision L)
        ((ℓ s : derivedNeighborhoodSpace K L) : E) :=
  derivedNeighborhoodStrongDeformationRetract_retraction_apply hL (ℓ s)

end DifferentialGeometry.Topology.PiecewiseLinear
