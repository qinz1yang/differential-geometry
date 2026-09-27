/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.FreeFaceArc

open Set Topology

namespace DifferentialGeometry.Topology.PiecewiseLinear

local notation "E3" => EuclideanSpace ℝ (Fin 3)

variable {K : Geometry.SimplicialComplex ℝ E3} {N N' : Set E3} {C : E3 → Set E3}
  {D Dbd : Finset E3 → Set E3} {h : E3 → E3}

open Classical in
theorem IsTube.inter_image_pairs_eq (ht : IsTube K N C D Dbd h N')
    {u w : E3} (hu : u ∈ K.vertices) (hw : w ∈ K.vertices) (huw : u ≠ w)
    (he : ({u, w} : Finset E3) ∈ K.faces) (v : E3) :
    (h '' C u ∪ h '' C v) ∩ (h '' C v ∪ h '' C w) = h '' C v ∪ h '' D {u, w} := by
  have hI : h '' C u ∩ h '' C w = h '' D {u, w} := by
    rw [← ht.injOn.image_inter (ht.dualCell_subset hu) (ht.dualCell_subset hw),
      ht.interEdge hu hw huw he]
  rw [← hI]
  ext x
  simp only [mem_inter_iff, mem_union]
  tauto

theorem IsTube.mem_interior_inter_image_pairs (ht : IsTube K N C D Dbd h N')
    {v : E3} (hv : v ∈ K.vertices) (u w : E3) :
    h v ∈ interior ((h '' C u ∪ h '' C v) ∩ (h '' C v ∪ h '' C w)) := by
  have hint : h v ∈ interior (h '' C v) := by
    rw [interior_image_eq_image_interior_of_isCompact (ht.dualBall v hv).isPolyhedron.isCompact
      (ht.continuousOn.mono (ht.dualCell_subset hv)) (ht.injOn.mono (ht.dualCell_subset hv))]
    exact ⟨v, ht.mem_interior_dualCell hv, rfl⟩
  have hsub : h '' C v ⊆ (h '' C u ∪ h '' C v) ∩ (h '' C v ∪ h '' C w) :=
    fun _ hx => ⟨Or.inr hx, Or.inl hx⟩
  exact interior_mono hsub hint

theorem IsTube.not_isPLBall_inter_image_pairs_of_lt_three
    (ht : IsTube K N C D Dbd h N') {v : E3} (hv : v ∈ K.vertices)
    (u w : E3) {m : ℕ} (hm : m < 3) :
    ¬ IsPLBall m ((h '' C u ∪ h '' C v) ∩ (h '' C v ∪ h '' C w)) := by
  intro hball
  have hempty := hball.interior_eq_empty_of_lt_finrank (by simpa using hm)
  have hvI := ht.mem_interior_inter_image_pairs hv u w
  rw [hempty] at hvI
  exact hvI

end DifferentialGeometry.Topology.PiecewiseLinear
