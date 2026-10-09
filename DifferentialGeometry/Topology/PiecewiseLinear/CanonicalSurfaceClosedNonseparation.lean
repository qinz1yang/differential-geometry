/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.EmptyBoundaryManifold
import DifferentialGeometry.Topology.PiecewiseLinear.CanonicalSurfaceState
import DifferentialGeometry.Topology.PiecewiseLinear.CanonicalTowerCarrierTorus
import DifferentialGeometry.Topology.PiecewiseLinear.SurfaceRelativeExterior
import DifferentialGeometry.Topology.PiecewiseLinear.TubePairInterior

open Set Topology

namespace DifferentialGeometry.Topology.PiecewiseLinear

local notation "E3" => EuclideanSpace ℝ (Fin 3)

variable {K : Geometry.SimplicialComplex ℝ E3} {N N' : Set E3} {C : E3 → Set E3}
  {D Dbd : Finset E3 → Set E3} {h : E3 → E3} {u v : E3} {W : Set E3} {P' : E3}
  {φ : E3 → E3} {Pt : ℤ → E3} {Dp Dpint J A S T S'' T'' : ℤ → Set E3}

open Classical in
theorem IsCanonicalSurface.closed_component_not_separates [d : DecidableEq E3]
    (ht : IsTube K N C D Dbd h N')
    (hu : u ∈ K.vertices) (hv : v ∈ K.vertices) (huv : u ≠ v)
    (he : ({u, v} : Finset E3) ∈ K.faces)
    (htw : IsCanonicalTower φ Pt Dp Dpint J A S T S'' T'' (h '' D {u, v}) (h '' Dbd {u, v}) W
      (interior (h '' C u ∪ h '' C v)) P')
    (havoid : ∀ k : ℤ, Disjoint (φ '' S k) ({h u, h v} : Set E3))
    {X : ℤ → Geometry.SimplicialComplex ℝ E3}
    (hX : IsCanonicalSurface X (fun j => φ '' S j) T''
      (interior (h '' C u ∪ h '' C v)) P' (h u) (h v))
    (i : ℤ) (c : ConnectedComponents (X i).space)
    (hclosed : (boundaryComplex 2 (connectedComponentComplex (X i) c)).space = ∅) :
    ¬ Separates (((↑) : interior (h '' C u ∪ h '' C v) → E3) ⁻¹'
        (connectedComponentComplex (X i) c).space)
      (((↑) : interior (h '' C u ∪ h '' C v) → E3) ⁻¹' {h u})
      (((↑) : interior (h '' C u ∪ h '' C v) → E3) ⁻¹' {h v}) := by
  have hd : d = fun a b => Classical.propDecidable (a = b) := Subsingleton.elim _ _
  subst d
  let _ : DecidableEq E3 := fun a b => Classical.propDecidable (a = b)
  let _ : Finite (X i).faces := (hX.finiteFaces i).to_subtype
  let L := connectedComponentComplex (X i) c
  let _ : Finite L.faces := (connectedComponentComplex_faces_finite (X i) c).to_subtype
  have hL : IsCombinatorialManifold 2 L :=
    IsCombinatorialManifoldWithBoundary.isCombinatorialManifold_of_empty_boundary
      ((hX.manifold i).connectedComponentComplex c) hclosed
  have hLconn : IsConnected L.space := isConnected_connectedComponentComplex_space (X i) c
  have hLX : L.space ⊆ (X i).space :=
    (subset_iUnion (fun d => (connectedComponentComplex (X i) d).space) c).trans
      (iUnion_connectedComponentComplex_space (X i)).subset
  let V := (φ '' S (2 * i) ∪ φ '' S (2 * i + 1)) ∪ φ '' S (2 * (i + 1))
  have hV : IsTopologicalSolidTorus V := by
    simpa only [V, show 2 * (i + 1) = 2 * i + 2 by omega] using
      htw.outer_triple_isTopologicalSolidTorus (2 * i)
  have hVU : V ⊆ interior (h '' C u ∪ h '' C v) :=
    union_subset (union_subset (htw.subsetInterior _) (htw.subsetInterior _)) (htw.subsetInterior _)
  have hLV : L.space ⊆ interior V := hLX.trans (hX.interiorCarrier i)
  have hdis : Disjoint V ({h u, h v} : Set E3) :=
    ((havoid (2 * i)).union_left (havoid (2 * i + 1))).union_left (havoid (2 * (i + 1)))
  have huI : h u ∈ interior (h '' C u ∪ h '' C v) :=
    interior_mono subset_union_left (ht.mem_interior_image_dualCell hu)
  have hvI : h v ∈ interior (h '' C u ∪ h '' C v) :=
    interior_mono subset_union_right (ht.mem_interior_image_dualCell hv)
  exact hL.not_separates_in_open_of_subset_solidTorus L hLconn isOpen_interior
    (ht.isConnected_interior_image_pair hu hv huv (by
      exact (congrArg (fun d : DecidableEq E3 =>
        @insert E3 (Finset E3) (@Finset.instInsert E3 d) u {v} ∈ K.faces)
          (Subsingleton.elim _ _)).mp he)) hV hVU hLV huI hvI
    (fun hx => disjoint_left.mp hdis hx (Or.inl rfl))
    (fun hx => disjoint_left.mp hdis hx (Or.inr rfl))

end DifferentialGeometry.Topology.PiecewiseLinear
