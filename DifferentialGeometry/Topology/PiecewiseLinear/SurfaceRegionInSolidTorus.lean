/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.SurfaceFilling
import DifferentialGeometry.Topology.PiecewiseLinear.ExistsGeneralPositionSolidTorusRelative
import DifferentialGeometry.Topology.Connected.CompactRegion
import Mathlib.Analysis.Normed.Module.Connected

open Set Topology

namespace DifferentialGeometry.Topology.PiecewiseLinear

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

open Classical in
theorem IsCombinatorialManifold.exists_filling_subset_interior
    (L : Geometry.SimplicialComplex ℝ E) [Finite L.faces]
    (hL : IsCombinatorialManifold 2 L) (hdim : Module.finrank ℝ E = 3)
    (hconn : IsConnected L.space) {S : Set E} (hS : IsCompact S)
    (hSf : IsPreconnected (frontier S)) (hLS : L.space ⊆ interior S) :
    ∃ R : Geometry.SimplicialComplex ℝ E, R.faces.Finite ∧
      IsCombinatorialManifoldWithBoundary 3 R ∧
      (boundaryComplex 3 R).space = L.space ∧ frontier R.space = L.space ∧
      closure (interior R.space) = R.space ∧ IsConnected (interior R.space) ∧
      IsConnected R.spaceᶜ ∧ R.space ⊆ interior S := by
  let _ : Nontrivial E := Module.nontrivial_of_finrank_pos (by omega : 0 < Module.finrank ℝ E)
  obtain ⟨R, hRfin, hR, hRb, hRfr, hRreg, hRi, hRe⟩ :=
    hL.exists_isCombinatorialManifoldWithBoundary_boundaryComplex L hdim hconn
  let _ : Finite R.faces := hRfin.to_subtype
  have hRcompact := (isPolyhedron_space R).isCompact
  have hRclosed := hRcompact.isClosed
  have hfront : frontier R.space ⊆ interior S := hRfr.subset.trans hLS
  have hdis : Disjoint (frontier S) (frontier R.space) := disjoint_left.mpr fun x hxS hxR =>
    disjoint_left.mp disjoint_interior_frontier (hfront hxR) hxS
  have hcover : frontier S ⊆ interior R.space ∪ R.spaceᶜ := by
    rw [← hRclosed.isOpen_compl.interior_eq, ← compl_frontier_eq_union_interior]
    exact disjoint_left.mp hdis
  have hRsub : R.space ⊆ interior S := by
    rcases hSf.subset_or_subset isOpen_interior hRclosed.isOpen_compl
        (disjoint_compl_right.mono_left interior_subset) hcover with hinside | houtside
    · have hSR := Topology.subset_of_isCompact_of_frontier_subset_of_isPreconnected_compl
        hS hRcompact hRe.isPreconnected (hinside.trans interior_subset)
      obtain ⟨x, hxL⟩ := hconn.nonempty
      exact (disjoint_left.mp disjoint_interior_frontier
        (interior_mono hSR (hLS hxL)) (hRfr.symm.subset hxL)).elim
    · have hRS : Disjoint R.space (frontier S) :=
        disjoint_left.mpr fun x hxR hxS => houtside hxS hxR
      have hRc : IsPreconnected R.space := hRreg ▸ hRi.isPreconnected.closure
      apply Topology.subset_interior_of_isPreconnected_of_disjoint_frontier hRc hRS
      obtain ⟨x, hxL⟩ := hconn.nonempty
      exact ⟨x, hRclosed.frontier_subset (hRfr.symm.subset hxL), hLS hxL⟩
  exact ⟨R, hRfin, hR, hRb, hRfr, hRreg, hRi, hRe, hRsub⟩

local notation "E3" => EuclideanSpace ℝ (Fin 3)

open Classical in
theorem IsCombinatorialManifold.exists_filling_interior_solidTorus [d : DecidableEq E3]
    (L : Geometry.SimplicialComplex ℝ E3) [Finite L.faces]
    (hL : IsCombinatorialManifold 2 L) (hconn : IsConnected L.space)
    {S : Set E3} (hS : IsTopologicalSolidTorus S) (hLS : L.space ⊆ interior S) :
    ∃ R : Geometry.SimplicialComplex ℝ E3, R.faces.Finite ∧
      IsCombinatorialManifoldWithBoundary 3 R ∧
      (boundaryComplex 3 R).space = L.space ∧ frontier R.space = L.space ∧
      closure (interior R.space) = R.space ∧ IsConnected (interior R.space) ∧
      IsConnected R.spaceᶜ ∧ R.space ⊆ interior S := by
  have hd : d = fun a b => Classical.propDecidable (a = b) := Subsingleton.elim _ _
  subst d
  let _ : DecidableEq E3 := fun a b => Classical.propDecidable (a = b)
  obtain ⟨e⟩ := hS
  let _ : CompactSpace S := e.symm.compactSpace
  have hSc : IsCompact S := isCompact_iff_compactSpace.mpr inferInstance
  obtain ⟨g⟩ := IsTopologicalSolidTorus.nonempty_homeomorph_frontier
    (show IsTopologicalSolidTorus S from ⟨e⟩) hSc.isClosed
  let _ : ConnectedSpace (Metric.sphere (0 : EuclideanSpace ℝ (Fin 2)) 1) :=
    isConnected_iff_connectedSpace.mp
      (isConnected_sphere (by rw [← Module.finrank_eq_rank]; simp) 0 zero_le_one)
  let _ : ConnectedSpace (frontier S) := g.connectedSpace_iff.mpr inferInstance
  exact hL.exists_filling_subset_interior L (by simp) hconn hSc
    (isConnected_iff_connectedSpace.mpr inferInstance).isPreconnected hLS

end DifferentialGeometry.Topology.PiecewiseLinear
