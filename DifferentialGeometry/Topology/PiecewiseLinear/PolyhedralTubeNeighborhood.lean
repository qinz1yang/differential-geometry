/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.PseudoCell

open Set Topology

namespace DifferentialGeometry.Topology.PiecewiseLinear

section Vocabulary

def edgesAt (K : Geometry.SimplicialComplex ℝ (EuclideanSpace ℝ (Fin 3)))
    (v : EuclideanSpace ℝ (Fin 3)) : Set (Finset (EuclideanSpace ℝ (Fin 3))) :=
  {e | e ∈ K.faces ∧ e.card = 2 ∧ v ∈ e}

structure IsPolyhedralTubeNeighborhood
    (K : Geometry.SimplicialComplex ℝ (EuclideanSpace ℝ (Fin 3)))
    (h : EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 3))
    (N' : Set (EuclideanSpace ℝ (Fin 3)))
    (Ec Eint Ebd : Finset (EuclideanSpace ℝ (Fin 3)) → Set (EuclideanSpace ℝ (Fin 3)))
    (XK : Geometry.SimplicialComplex ℝ (EuclideanSpace ℝ (Fin 3))) : Prop where
  facesFinite : XK.faces.Finite
  isManifold : IsCombinatorialManifoldWithBoundary 3 XK
  isNeighborhood : XK.space ∈ nhdsSet (h '' K.space)
  subsetInterior : XK.space ⊆ interior N'
  rimDisjoint : ∀ e ∈ K.faces, e.card = 2 → Disjoint (Ebd e) XK.space
  crossing : ∀ e ∈ K.faces, e.card = 2 → ∀ x ∈ Ec e ∩ frontier XK.space,
    HasPLCrossingAt (Eint e) (frontier XK.space) x

def HasSinglePolygonTraces (K : Geometry.SimplicialComplex ℝ (EuclideanSpace ℝ (Fin 3)))
    (h : EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 3))
    (Ec : Finset (EuclideanSpace ℝ (Fin 3)) → Set (EuclideanSpace ℝ (Fin 3)))
    (X : Set (EuclideanSpace ℝ (Fin 3))) : Prop :=
  ∀ e ∈ K.faces, e.card = 2 →
    IsPLSphere 1 (Ec e ∩ frontier X) ∧
    ∃ DJint : Set (EuclideanSpace ℝ (Fin 3)),
      IsTopologicalCellWithInterior 2 (Ec e ∩ X) DJint ∧
      (Ec e ∩ X) \ DJint = Ec e ∩ frontier X ∧ h (e.centroid ℝ id) ∈ DJint

open Classical in
def HasConnectedHandlePieces (K : Geometry.SimplicialComplex ℝ (EuclideanSpace ℝ (Fin 3)))
    (Ec : Finset (EuclideanSpace ℝ (Fin 3)) → Set (EuclideanSpace ℝ (Fin 3)))
    (Cpp : EuclideanSpace ℝ (Fin 3) → Set (EuclideanSpace ℝ (Fin 3)))
    (X : Set (EuclideanSpace ℝ (Fin 3)))
    (AK : EuclideanSpace ℝ (Fin 3) → Geometry.SimplicialComplex ℝ (EuclideanSpace ℝ (Fin 3))) :
    Prop :=
  IsConnected X ∧ IsConnected (frontier X) ∧
  ∀ v ∈ K.vertices,
    (AK v).faces.Finite ∧ (AK v).space = Cpp v ∩ frontier X ∧
    IsCombinatorialManifoldWithBoundary 2 (AK v) ∧ IsConnected (AK v).space ∧
    (boundaryComplex 2 (AK v)).space = ⋃ e ∈ edgesAt K v, Ec e ∩ frontier X

end Vocabulary

end DifferentialGeometry.Topology.PiecewiseLinear
