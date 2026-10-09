/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.DualCells
import DifferentialGeometry.Topology.PiecewiseLinear.PolyhedralGraph
import DifferentialGeometry.Topology.PiecewiseLinear.BallDensity

open Set Topology

namespace DifferentialGeometry.Topology.PiecewiseLinear

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

abbrev SourceVertex (K : Geometry.SimplicialComplex ℝ E) :=
  {v : E // ({v} : Finset E) ∈ K.faces}

abbrev SourceEdge (K : Geometry.SimplicialComplex ℝ E) :=
  {e : Finset E // e ∈ K.faces ∧ e.card = 2}

abbrev SourceFace (K : Geometry.SimplicialComplex ℝ E) :=
  {s : Finset E // s ∈ K.faces ∧ s.card = 3}

abbrev SourceTetrahedron (K : Geometry.SimplicialComplex ℝ E) :=
  {t : Finset E // t ∈ K.faces ∧ t.card = 4}

def sourceVertexOnEdge {K : Geometry.SimplicialComplex ℝ E}
    (v : SourceVertex K) (e : SourceEdge K) : Prop :=
  v.1 ∈ e.1

def sourceVertexOnFace {K : Geometry.SimplicialComplex ℝ E}
    (v : SourceVertex K) (s : SourceFace K) : Prop :=
  v.1 ∈ s.1

def sourceVertexOnTetrahedron {K : Geometry.SimplicialComplex ℝ E}
    (v : SourceVertex K) (t : SourceTetrahedron K) : Prop :=
  v.1 ∈ t.1

def sourceEdgeOnFace {K : Geometry.SimplicialComplex ℝ E}
    (e : SourceEdge K) (s : SourceFace K) : Prop :=
  e.1 ⊆ s.1

def sourceFaceOnTetrahedron {K : Geometry.SimplicialComplex ℝ E}
    (s : SourceFace K) (t : SourceTetrahedron K) : Prop :=
  s.1 ⊆ t.1

def sourceSimplexSpace (s : Finset E) : Set E :=
  convexHull ℝ (s : Set E)

noncomputable def sourceNeighborhood
    (K L : Geometry.SimplicialComplex ℝ E) : Set E :=
  (@derivedNeighborhood _ _ _ (Classical.decEq _) K L).space

noncomputable def sourceDualCell
    (K L : Geometry.SimplicialComplex ℝ E) (v : SourceVertex K) : Set E :=
  (graphDualCell K L v.1).space

noncomputable def sourceSplittingDisk
    (K : Geometry.SimplicialComplex ℝ E) (e : SourceEdge K) : Set E :=
  (splittingDisk K e.1 e.2.1).space

def sourceFaceRemainder (N : Set E) (s : Finset E) : Set E :=
  closure (sourceSimplexSpace s \ N)

def sourceTetrahedronRemainder {K : Geometry.SimplicialComplex ℝ E} (N : Set E)
    (t : SourceTetrahedron K) : Set E :=
  sourceFaceRemainder N t.1

def sourcePatch (K L : Geometry.SimplicialComplex ℝ E) (N : Set E)
    (t : SourceTetrahedron K) (v : SourceVertex K) : Set E :=
  sourceTetrahedronRemainder N t ∩ sourceDualCell K L v

def sourceFaceEdgePoint {K : Geometry.SimplicialComplex ℝ E} (N : Set E)
    (s : SourceFace K) (e : SourceEdge K) : Set E :=
  frontier (sourceFaceRemainder N s.1) ∩ frontier (sourceSplittingDisk K e)

def sourceVertexFaceTrace (K L : Geometry.SimplicialComplex ℝ E) (N : Set E)
    (v : SourceVertex K) (s : SourceFace K) : Set E :=
  sourceDualCell K L v ∩ frontier (sourceFaceRemainder N s.1)

def sourceTetrahedronEdgeTrace (K : Geometry.SimplicialComplex ℝ E) (N : Set E)
    (t : SourceTetrahedron K) (e : SourceEdge K) : Set E :=
  sourceTetrahedronRemainder N t ∩ frontier (sourceSplittingDisk K e)

def sourcePatchFrontier (K L : Geometry.SimplicialComplex ℝ E) (N : Set E)
    (t : SourceTetrahedron K) (v : SourceVertex K) : Set E :=
  frontier (sourcePatch K L N t v)

theorem sourceSimplexSpace_subset (s : Finset E) :
    sourceSimplexSpace s ⊆ closure (sourceSimplexSpace s) :=
  subset_closure

theorem sourceFaceRemainder_subset_simplex (N : Set E) (s : Finset E) :
    sourceFaceRemainder N s ⊆ sourceSimplexSpace s := by
  apply closure_minimal sdiff_subset
  exact (s.finite_toSet.isCompact_convexHull ℝ).isClosed

theorem sourceTetrahedronRemainder_subset_simplex (N : Set E)
    {K : Geometry.SimplicialComplex ℝ E} (t : SourceTetrahedron K) :
    sourceTetrahedronRemainder N t ⊆ sourceSimplexSpace t.1 :=
  sourceFaceRemainder_subset_simplex N t.1

open Classical in
theorem sourceNeighborhood_subset (K L : Geometry.SimplicialComplex ℝ E) :
    sourceNeighborhood K L ⊆ K.space :=
  by simpa only [sourceNeighborhood] using
    (@derivedNeighborhood_space_subset E _ _ (Classical.decEq _) K L)

theorem sourceDualCell_subset_neighborhood (K L : Geometry.SimplicialComplex ℝ E)
    (v : SourceVertex K) :
    sourceDualCell K L v ⊆ sourceNeighborhood K L := by
  simpa only [sourceDualCell, sourceNeighborhood] using graphDualCell_space_subset K L v.1

theorem sourcePatch_subset_remainder (K L : Geometry.SimplicialComplex ℝ E) (N : Set E)
    (t : SourceTetrahedron K) (v : SourceVertex K) :
    sourcePatch K L N t v ⊆ sourceTetrahedronRemainder N t :=
  inter_subset_left

theorem sourcePatch_subset_dualCell (K L : Geometry.SimplicialComplex ℝ E) (N : Set E)
    (t : SourceTetrahedron K) (v : SourceVertex K) :
    sourcePatch K L N t v ⊆ sourceDualCell K L v :=
  inter_subset_right

open Classical in
theorem sourceDualCell_inter_sourceDualCell
    (K L : Geometry.SimplicialComplex ℝ E) (hL : L.faces ⊆ K.faces)
    (hcard : ∀ s ∈ L.faces, s.card ≤ 2) {v w : SourceVertex K}
    (hvw : v.1 ≠ w.1) (he : ({v.1, w.1} : Finset E) ∈ L.faces) :
    sourceDualCell K L ⟨v.1, v.2⟩ ∩ sourceDualCell K L ⟨w.1, w.2⟩ =
      sourceSplittingDisk K ⟨{v.1, w.1}, hL he, by simp [hvw]⟩ := by
  simpa only [sourceDualCell, sourceSplittingDisk] using
    graphDualCell_space_inter K L hL hcard hvw he

open Classical in
theorem sourceDualCell_inter_sourceDualCell_eq_empty
    (K L : Geometry.SimplicialComplex ℝ E) (hL : L.faces ⊆ K.faces)
    (hcard : ∀ s ∈ L.faces, s.card ≤ 2) {v w : SourceVertex K}
    (hvw : v.1 ≠ w.1) (hv : ({v.1} : Finset E) ∈ L.faces)
    (hw : ({w.1} : Finset E) ∈ L.faces)
    (he : ({v.1, w.1} : Finset E) ∉ L.faces) :
    sourceDualCell K L ⟨v.1, v.2⟩ ∩ sourceDualCell K L ⟨w.1, w.2⟩ = ∅ := by
  simpa only [sourceDualCell] using
    graphDualCell_space_inter_eq_empty K L hL hcard hv hw hvw he

theorem sourceSplittingDisk_inter_sourceNeighborhood
    (K L : Geometry.SimplicialComplex ℝ E) (hL : L.faces ⊆ K.faces)
    (hcard : ∀ s ∈ L.faces, s.card ≤ 2) (e : SourceEdge K)
    (he : e.1 ∈ L.faces) :
    sourceSplittingDisk K e ∩ L.space = {e.1.centroid ℝ id} := by
  simpa only [sourceSplittingDisk] using
    splittingDisk_space_inter K L hL he (by simpa [e.2.2] using hcard)

end DifferentialGeometry.Topology.PiecewiseLinear
