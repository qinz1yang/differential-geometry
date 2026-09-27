/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.ClosedStarFiber
import DifferentialGeometry.Topology.PiecewiseLinear.HeightSectionDecomposition
import DifferentialGeometry.Topology.PiecewiseLinear.RelativeFreeDiskCell

open Set

namespace DifferentialGeometry.Topology.PiecewiseLinear

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

open Classical in
theorem biUnion_heightSectionCells_subset_closedStar_eq
    (K : Geometry.SimplicialComplex ℝ E) [Finite K.faces]
    (hdim : Module.finrank ℝ E = 3) (hK : closure (interior K.space) = K.space)
    (ℓ : E →ₗ[ℝ] ℝ) (hinj : InjOn ℓ K.vertices) {p : E} (hp : {p} ∈ K.faces)
    (hD : IsPLBall 2 (K.space ∩ {x | ℓ x = ℓ p})) :
    (⋃ C ∈ (heightSectionCells 2 K ℓ (ℓ p)).filter (fun C => C ⊆ closedStar K p), C) =
      closedStar K p ∩ {x | ℓ x = ℓ p} := by
  classical
  let cells := (heightSectionCells 2 K ℓ (ℓ p)).filter (fun C => C ⊆ closedStar K p)
  have hclosed : IsClosed (⋃ C ∈ cells, C) := cells.finite_toSet.isClosed_biUnion
    (fun _ hC => (isPLBall_of_mem_heightSectionCells (Finset.mem_filter.mp
        hC).1).isPolyhedron.isClosed)
  have hverts : K.vertices.Finite :=
    (Set.toFinite K.faces).preimage Finset.singleton_injective.injOn
  have hsub : (closedStar K p ∩ {x | ℓ x = ℓ p}) \ K.vertices ⊆ ⋃ C ∈ cells, C := by
    rintro x ⟨⟨hx, hxr⟩, hxnot⟩
    obtain ⟨s, ⟨hs, hps⟩, hxs⟩ := mem_iUnion₂.mp hx
    obtain ⟨t, ht, hst, hcard⟩ :=
      exists_face_superset_card_eq_finrank_succ K isOpen_interior hK.symm hs
    have hpt : p ∈ t := hst (mem_of_mem_convexHull_of_singleton_mem K hp hs hps)
    have hxt := convexHull_mono (Finset.coe_subset.mpr hst) hxs
    have htverts : (t : Set E) ⊆ K.vertices := fun v hv =>
      K.down_closed ht (Finset.singleton_subset_iff.mpr hv) (Finset.singleton_nonempty v)
    rcases convexHull_inter_fiber_eq_singleton_or_exists_lt_and_gt t (K.indep ht)
      ℓ (hinj.mono htverts) ⟨x, hxt, hxr⟩ with ⟨v, hv, heq⟩ | ⟨hbelow, habove⟩
    · have hxv : x = v := heq.subset ⟨hxt, hxr⟩
      exact (hxnot (hxv.symm ▸ htverts hv)).elim
    · refine mem_iUnion₂.mpr ⟨convexHull ℝ (t : Set E) ∩ {x | ℓ x = ℓ p}, ?_, hxt, hxr⟩
      refine Finset.mem_filter.mpr ⟨mem_heightSectionCells_iff.mpr
        ⟨t, ht, by simpa only [hdim] using hcard, hbelow, habove, rfl⟩, ?_⟩
      intro y hy
      exact mem_iUnion₂.mpr ⟨t, ⟨ht, subset_convexHull ℝ _ hpt⟩, hy.1⟩
  apply Subset.antisymm
  · refine iUnion₂_subset fun C hC => ?_
    obtain ⟨hC, hCstar⟩ := Finset.mem_filter.mp hC
    exact fun x hx => ⟨hCstar hx, (subset_fiber_of_mem_heightSectionCells hC hx).2⟩
  · have h := closure_mono hsub
    have hstar : IsPLBall 2 (closedStar K p ∩ {x | ℓ x = ℓ p}) :=
      isPLBall_closedStar_inter_fiber K hp ℓ hD
    rwa [hstar.closure_sdiff_of_finite hverts, hclosed.closure_eq] at h

theorem exists_free_heightSectionCell_outside_closedStar
    (K : Geometry.SimplicialComplex ℝ E) [Finite K.faces]
    (hdim : Module.finrank ℝ E = 3) (hK : closure (interior K.space) = K.space)
    (ℓ : E →ₗ[ℝ] ℝ) (hinj : InjOn ℓ K.vertices) {p : E} (hp : {p} ∈ K.faces)
    (hD : IsPLBall 2 (K.space ∩ {x | ℓ x = ℓ p}))
    (hne : closedStar K p ∩ {x | ℓ x = ℓ p} ≠ K.space ∩ {x | ℓ x = ℓ p}) :
    ∃ (L : Geometry.SimplicialComplex ℝ E) (C : Set E), L.faces.Finite ∧
      L.space = K.space ∩ {x | ℓ x = ℓ p} ∧
      IsPLDiskDecomposition L (heightSectionCells 2 K ℓ (ℓ p)) ∧
      C ∈ heightSectionCells 2 K ℓ (ℓ p) ∧ ¬C ⊆ closedStar K p ∧ IsFreeDiskCell L C := by
  classical
  obtain ⟨L, hLfin, hLspace, hdec⟩ :=
    exists_isPLDiskDecomposition_heightSectionCells K hdim hK ℓ hinj (ℓ p) hD
  have hcover := biUnion_heightSectionCells_subset_closedStar_eq K hdim hK ℓ hinj hp hD
  obtain ⟨C, hC, hnot, hfree⟩ := hdec.exists_free_disk_cell_not_subset
    (Finset.filter_subset (fun C => C ⊆ closedStar K p) _)
    (isPLBall_closedStar_inter_fiber K hp ℓ hD) hcover.symm
    (fun heq => hne (heq.trans hLspace))
  refine ⟨L, C, hLfin, hLspace, hdec, hC, ?_, hfree⟩
  intro hCstar
  exact hnot (fun x hx => ⟨hCstar hx, (subset_fiber_of_mem_heightSectionCells hC hx).2⟩)

end DifferentialGeometry.Topology.PiecewiseLinear
