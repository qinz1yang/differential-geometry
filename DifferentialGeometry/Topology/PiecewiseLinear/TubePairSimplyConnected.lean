/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.TubePairInterior
import DifferentialGeometry.Topology.PiecewiseLinear.BallInteriorContractible
import Mathlib.AlgebraicTopology.FundamentalGroupoid.SimplyConnected

open Set Topology

namespace DifferentialGeometry.Topology.PiecewiseLinear

local notation "E3" => EuclideanSpace ℝ (Fin 3)

variable {K : Geometry.SimplicialComplex ℝ E3} {N N' : Set E3} {C : E3 → Set E3}
  {D Dbd : Finset E3 → Set E3} {h : E3 → E3} {u v : E3}

open Classical in
theorem IsTube.contractibleSpace_interior_image_pair (ht : IsTube K N C D Dbd h N')
    (hu : u ∈ K.vertices) (hv : v ∈ K.vertices) (huv : u ≠ v)
    (he : ({u, v} : Finset E3) ∈ K.faces) :
    ContractibleSpace (interior (h '' C u ∪ h '' C v)) := by
  have hball := ht.isPLBall_dualCell_pair hu hv huv he
  have hsub : C u ∪ C v ⊆ N := union_subset (ht.dualCell_subset hu) (ht.dualCell_subset hv)
  let _ : CompactSpace ↥(C u ∪ C v) := isCompact_iff_compactSpace.mp hball.isPolyhedron.isCompact
  let _ : ContractibleSpace (interior (C u ∪ C v)) :=
    hball.contractibleSpace_interior_of_finrank (by simp)
  have hc : Continuous ((C u ∪ C v).domRestrict h) := (ht.continuousOn.mono hsub).domRestrict
  have hi : Function.Injective ((C u ∪ C v).domRestrict h) := fun x y hxy =>
    Subtype.ext (ht.injOn (hsub x.property) (hsub y.property) hxy)
  have hfull : IsEmbedding ((C u ∪ C v).domRestrict h) := (hc.isClosedEmbedding hi).isEmbedding
  have hopen : IsEmbedding ((interior (C u ∪ C v)).domRestrict h) :=
    hfull.comp (Topology.IsEmbedding.inclusion interior_subset)
  have himage : h '' interior (C u ∪ C v) = interior (h '' C u ∪ h '' C v) := by
    rw [← image_union, interior_image_eq_image_interior_of_isCompact hball.isPolyhedron.isCompact
      (ht.continuousOn.mono hsub) (ht.injOn.mono hsub)]
  let e : interior (C u ∪ C v) ≃ₜ interior (h '' C u ∪ h '' C v) :=
    hopen.toHomeomorph.trans (Homeomorph.setCongr ((Set.range_domRestrict h _).trans himage))
  exact e.symm.contractibleSpace

open Classical in
theorem IsTube.simplyConnectedSpace_interior_image_pair (ht : IsTube K N C D Dbd h N')
    (hu : u ∈ K.vertices) (hv : v ∈ K.vertices) (huv : u ≠ v)
    (he : ({u, v} : Finset E3) ∈ K.faces) :
    SimplyConnectedSpace (interior (h '' C u ∪ h '' C v)) := by
  let _ := ht.contractibleSpace_interior_image_pair hu hv huv he
  infer_instance

end DifferentialGeometry.Topology.PiecewiseLinear
