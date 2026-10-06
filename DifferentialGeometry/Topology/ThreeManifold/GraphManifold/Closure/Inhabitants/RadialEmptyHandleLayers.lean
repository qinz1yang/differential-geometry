import
  DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.Inhabitants.RadialLoopEmbedding

set_option autoImplicit false
noncomputable section
open Set Function Manifold
open GC.Endpoint GC.GraphManifold
open scoped Manifold ContDiff
namespace GC.GraphManifold.Assembly.FC39P0.X135Radial

def radialHandleEnds : HandleEndLayer carrier radialVertices radialEdgeLayer radialFaces where
  handleEnd := fun h => Fin.elim0 h
  handleFace := fun h => Fin.elim0 h
  handleFace_owner := fun h => Fin.elim0 h
  handleFace_kind := fun h => Fin.elim0 h
  handleEnd_face := fun h => Fin.elim0 h
  endDisk_disjoint := fun h => Fin.elim0 h

def radialRimRegions : RimRegionLayer carrier radialVertices radialEdgeLayer
    radialCircleRegion radialHandleEnds radialRims where
  rim_vertex := fun h => Fin.elim0 h
  rim_handle := fun h => Fin.elim0 h
  rim_region := fun h => Fin.elim0 h

end GC.GraphManifold.Assembly.FC39P0.X135Radial
