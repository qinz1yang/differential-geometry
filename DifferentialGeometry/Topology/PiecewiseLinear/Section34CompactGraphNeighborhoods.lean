/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.Section34CompactGraphCarriers

open Set Topology

namespace DifferentialGeometry.Topology.PiecewiseLinear

local notation "E3" => EuclideanSpace ℝ (Fin 3)

open Classical in
theorem exists_compactGraphNeighborhoods
    (M K : Geometry.SimplicialComplex ℝ E3) [Finite M.faces]
    (hKM : K.faces ⊆ M.faces) {h : E3 → E3} (hh : ContinuousOn h M.space)
    (hinj : InjOn h M.space) {ε : ℝ} (hε : 0 < ε)
    (hstar : ∀ v ∈ K.vertices, ∀ x ∈ closedStar M v, dist (h x) (h v) < ε / 100) :
    let L := restrict K (section34CompactGraphSkeleton K)
    ∃ (H : Finset E3 → Set E3) (W : E3 → Set E3),
      Section34CompactCarrierControl K h ε H ∧
      (∀ t ∈ K.faces, ∀ v ∈ t, h '' (graphDualCell M L v).space ⊆ interior (H t)) ∧
      (∀ v, IsOpen (W v)) ∧
      (∀ v ∈ K.vertices, h '' (graphDualCell M L v).space ⊆ W v) ∧
      (∀ v, W v ⊆ Metric.ball (h v) (ε / 50)) ∧
      (∀ v, ∀ t ∈ K.faces, v ∈ t → W v ⊆ interior (H t)) ∧
      (∀ v, ∀ t ∈ K.faces, v ∉ t → Disjoint (W v) (h '' convexHull ℝ (t : Set E3))) := by
  classical
  let : DecidableEq E3 := Classical.decEq E3
  dsimp only
  let L := restrict K (section34CompactGraphSkeleton K)
  let _ : Finite K.faces := ((Set.toFinite M.faces).subset hKM).to_subtype
  obtain ⟨H, hH, hHC⟩ := exists_compactGraphCarriers M K hKM hh hε hstar
  let W (v : E3) := Metric.ball (h v) (ε / 50) ∩
    ⋂ t : K.faces, if v ∈ t.1 then interior (H t.1)
      else (h '' convexHull ℝ (t.1 : Set E3))ᶜ
  have hWopen (v : E3) : IsOpen (W v) := by
    refine Metric.isOpen_ball.inter (isOpen_iInter_of_finite fun t => ?_)
    split_ifs
    · exact isOpen_interior
    · exact ((t.1.finite_toSet.isCompact_convexHull ℝ).image_of_continuousOn
        (hh.mono (M.convexHull_subset_space (hKM t.2)))).isClosed.isOpen_compl
  have hCW (v : E3) (hv : v ∈ K.vertices) : h '' (graphDualCell M L v).space ⊆ W v := by
    rintro y ⟨x, hx, rfl⟩
    have hxM : x ∈ M.space :=
      derivedNeighborhood_space_subset M L (graphDualCell_space_subset M L v hx)
    refine ⟨?_, mem_iInter.mpr fun t => ?_⟩
    · have hxstar := (closedStar_subset_of_isSubdivision
        (barycentricSubdivision_isSubdivision M) v) (graphDualCell_space_subset_closedStar M L v hx)
      exact Metric.mem_ball.mpr ((hstar v hv x hxstar).trans (by linarith))
    · split_ifs with hvt
      · exact hHC t.1 t.2 v hvt (mem_image_of_mem h hx)
      · rintro ⟨z, hz, hzx⟩
        have hzx' : z = x := hinj (M.convexHull_subset_space (hKM t.2) hz) hxM hzx
        have hempty := graphDualCell_space_inter_convexHull_eq_empty L (hKM hv)
          (hKM t.2) hvt
        exact (eq_empty_iff_forall_notMem.mp hempty) x ⟨hx, hzx' ▸ hz⟩
  refine ⟨H, W, hH, hHC, hWopen, hCW, fun _ => inter_subset_left, ?_, ?_⟩
  · intro v t ht hvt x hx
    have htmem := mem_iInter.mp hx.2 ⟨t, ht⟩
    simpa only [ite_eq_left hvt] using htmem
  · intro v t ht hvt
    refine disjoint_left.mpr fun x hx hxt => ?_
    have htmem := mem_iInter.mp hx.2 ⟨t, ht⟩
    simp only [ite_eq_right hvt, mem_compl_iff] at htmem
    exact htmem hxt

end DifferentialGeometry.Topology.PiecewiseLinear
