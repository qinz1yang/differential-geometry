import Mathlib.Geometry.Manifold.Instances.Real
import Mathlib.Geometry.Manifold.IsManifold.InteriorBoundary
import Mathlib.Geometry.Manifold.SmoothEmbedding
import DifferentialGeometry.Topology.SphereSeparation.StandardSphere

set_option autoImplicit false

open Set
open scoped Manifold ContDiff Topology

namespace Poincare.Topology.SphereSeparation

structure SmoothSideClosure
    {N : Type*} [TopologicalSpace N] [ChartedSpace EuclideanThree N]
    (B S : Set N) where

  chartedSpace : ChartedSpace (EuclideanHalfSpace 3) (closure B)

  isManifold : let _ := chartedSpace
    IsManifold (𝓡∂ 3) ∞ (closure B)


  inclusion_isSmoothEmbedding : let _ := chartedSpace
    Manifold.IsSmoothEmbedding (𝓡∂ 3) (𝓘(ℝ, EuclideanThree)) ∞
      (Subtype.val : closure B → N)

  interior_image : let _ := chartedSpace
    Subtype.val '' (𝓡∂ 3).interior (closure B) = B

  boundary_image : let _ := chartedSpace
    Subtype.val '' (𝓡∂ 3).boundary (closure B) = S

structure SmoothSphereSides
    {N : Type*} [TopologicalSpace N] [ChartedSpace EuclideanThree N]
    (S : Set N) extends SphereSides S where
  compactClosureSmooth : SmoothSideClosure toSphereSides.compactSide S
  endClosureSmooth : SmoothSideClosure toSphereSides.endSide S

namespace SmoothSphereSides

variable {N : Type*} [TopologicalSpace N] [ChartedSpace EuclideanThree N]
  {S : Set N}

def sides (d : SmoothSphereSides S) : SphereSides S := d.toSphereSides

end SmoothSphereSides

end Poincare.Topology.SphereSeparation
