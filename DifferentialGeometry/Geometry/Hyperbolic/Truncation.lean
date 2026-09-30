import DifferentialGeometry.Geometry.Hyperbolic.FiniteVolumeModel
import DifferentialGeometry.Geometry.Hyperbolic.Cusp
import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Presentation

set_option autoImplicit false
noncomputable section
open DifferentialGeometry DifferentialGeometry.Topology GC.Endpoint GC.GraphManifold
open Manifold Set
open scoped Manifold ContDiff
namespace DifferentialGeometry.Geometry.Hyperbolic
universe u

structure HyperbolicTruncation (H : FiniteVolumeHyperbolicModel.{u}) where
  core : CompactCarrier.{u}
  connected : ConnectedSpace core.Carrier
  inclusion : C(core.Carrier, H.Carrier)
  embedding : IsSmoothEmbedding core.model (𝓡 3) ∞ inclusion
  interior_image : IsOpen (inclusion '' (core.interior : Set core.Carrier))
  count : ℕ
  boundary : BoundaryTori core count
  boundary_exhausted : core.model.boundary core.Carrier = boundary.image
  cusp : Fin count → HyperbolicCusp
  cuspMap : Fin count → CuspHalfSpace → H.Carrier
  cuspEmbedding : ∀ i, IsSmoothEmbedding halfCollarModel (𝓡 3) ∞ (cuspMap i)
  cuspIsometry : ∀ i p (v w : TangentSpace halfCollarModel p),
    H.metric.inner (cuspMap i p)
      (mfderiv halfCollarModel (𝓡 3) (cuspMap i) p v)
      (mfderiv halfCollarModel (𝓡 3) (cuspMap i) p w) = (cusp i).metric.inner p v w
  cusp_zero : ∀ i x, cuspMap i (x, halfZero) = inclusion (boundary.torusMap i x)
  cusp_disjoint : Pairwise (fun i j => Disjoint (range (cuspMap i)) (range (cuspMap j)))
  intersection : ∀ i, range inclusion ∩ range (cuspMap i) = range (fun x : Torus => cuspMap i (x, halfZero))
  exhausts : range inclusion ∪ (⋃ i, range (cuspMap i)) = univ

end DifferentialGeometry.Geometry.Hyperbolic
