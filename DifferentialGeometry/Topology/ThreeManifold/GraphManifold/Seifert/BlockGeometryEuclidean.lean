import
  DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Seifert.BlockGeometryEuclideanTwisted
import
  DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Seifert.BlockGeometryEuclideanNormal
import
  DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Seifert.BlockGeometryEuclideanSolid
import
  DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Seifert.BlockGeometryEuclideanUnfilled

set_option autoImplicit false

/-!
# Interior geometries of Euclidean small Seifert blocks

The imported chart consumers identify the entire actual interior of every two-cone twisted
block, normal two-port block, and solid-torus shape with its geometric model. Arbitrary odd
cone slopes and arbitrary filling ports are included. Unfilled annulus blocks are Euclidean;
unfilled pants retain their actual hyperbolic-product geometry.
-/
