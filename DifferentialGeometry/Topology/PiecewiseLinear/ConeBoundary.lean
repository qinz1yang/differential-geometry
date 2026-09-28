/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.PLHomeomorphTopology
import DifferentialGeometry.Topology.PiecewiseLinear.BoundaryInvariance
import DifferentialGeometry.Topology.PiecewiseLinear.BoundaryOfBall
import DifferentialGeometry.Topology.PiecewiseLinear.ConeIntersection
import DifferentialGeometry.Topology.PiecewiseLinear.SimplexFrontier

open Set

namespace DifferentialGeometry.Topology.PiecewiseLinear

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem coneComplex_simplexBoundary_space_eq_biUnion_insert_erase [DecidableEq E]
    (T : Finset E) (hT : AffineIndependent ℝ ((↑) : T → E)) (hcard : 2 ≤ T.card)
    {p : E} (hp : IsConeBase p (simplexBoundary T hT)) :
    (coneComplex hp).space = ⋃ v ∈ T, convexHull ℝ ((insert p (T.erase v) : Finset E) : Set E) := by
  ext x
  constructor
  · intro hx
    rcases (mem_coneComplex_space_iff hp).mp hx with rfl | ⟨z, hz, s, hs, hs', rfl⟩
    · obtain ⟨v, hv⟩ := Finset.card_pos.mp (by omega : 0 < T.card)
      exact mem_iUnion₂.mpr ⟨v, hv, subset_convexHull ℝ _ (Finset.mem_insert_self _ _)⟩
    · rw [simplexBoundary_space T hT hcard] at hz
      obtain ⟨v, hv, hzv⟩ := mem_iUnion₂.mp hz
      exact mem_iUnion₂.mpr ⟨v, hv, mem_convexHull_insert_of_combo hzv hs.le hs'⟩
  · intro hx
    obtain ⟨v, hv, hxv⟩ := mem_iUnion₂.mp hx
    exact (coneComplex hp).convexHull_subset_space
      (Or.inr (Or.inr ⟨T.erase v, erase_mem_simplexBoundary_faces hT hcard hv, rfl⟩)) hxv

theorem frontier_coneComplex [FiniteDimensional ℝ E] [dE : DecidableEq E] {n : ℕ}
    (hn : Module.finrank ℝ E = n + 2) {L : Geometry.SimplicialComplex ℝ E}
    [Finite L.faces] {p : E} (hp : IsConeBase p L) (hL : IsPLBall (n + 1) L.space) :
    frontier (coneComplex hp).space = L.space ∪
      (coneComplex (hp.of_faces_subset (boundaryComplex_faces_subset (n + 1) L))).space := by
  classical
  cases Subsingleton.elim dE (Classical.decEq E)
  obtain ⟨T, hT, hcard, -, -, -⟩ :=
    exists_affineIndependent_openSimplex_subset (n := n + 1) (by omega) (0 : E) Filter.univ_mem
  obtain ⟨a, ha⟩ := Finset.card_pos.mp (by omega : 0 < T.card)
  let F := T.erase a
  have hF : AffineIndependent ℝ ((↑) : F → E) := affineIndependent_of_subset hT (Finset.erase_subset
      a T)
  have hFcard : F.card = n + 2 := by simp only [F, Finset.card_erase_of_mem ha]; omega
  have hFne : F.Nonempty := Finset.card_pos.mp (by omega)
  have haF : a ∉ F := Finset.notMem_erase a T
  have hins : insert a F = T := Finset.insert_erase ha
  have hspan : affineSpan ℝ (T : Set E) = ⊤ := by
    have h := hT.affineSpan_eq_top_iff_card_eq_finrank_add_one.mpr (by
      simpa only [Fintype.card_coe, hn] using hcard)
    have hrange : range ((↑) : T → E) = (T : Set E) := Subtype.range_coe
    exact (congrArg (affineSpan ℝ) hrange).symm.trans h
  let M := simplexComplex F hF
  have hMspace : M.space = convexHull ℝ (F : Set E) := simplexComplex_space F hF hFne
  have : Finite M.faces := (simplexComplex_faces_finite F hF).to_subtype
  have hMball : IsPLBall (n + 1) M.space := by
    rw [hMspace]
    exact isPLBall_convexHull_of_affineIndependent F hF hFcard
  have haM : IsConeBase a M := isConeBase_simplexComplex F hF haF (hins.symm ▸ hT)
  obtain ⟨u, hu⟩ := hL
  obtain ⟨v, hv⟩ := hMball
  have hf := hu.symm.trans hv
  obtain ⟨g, hg, hgbase, hgp, hgrad⟩ := exists_isPLHomeomorphOn_coneComplex hp haM hf
  have htarget : (coneComplex haM).space = convexHull ℝ (T : Set E) := by
    rw [coneComplex_simplexComplex_space F hF hFne, hins]
  have hclosed : IsClosed (coneComplex hp).space :=
    (hp.isPLBall_of_isPLBall ⟨u, hu⟩).isPolyhedron.isCompact.isClosed
  have hmodelclosed : IsClosed (coneComplex haM).space := by
    rw [htarget]
    exact (T.finite_toSet.isCompact_convexHull ℝ).isClosed
  have hgfront := hg.image_frontier rfl hclosed hmodelclosed
  rw [htarget] at hgfront
  let B := boundaryComplex (n + 1) L
  let hpB := hp.of_faces_subset (boundaryComplex_faces_subset (n + 1) L)
  let haB := haM.of_faces_subset (simplexBoundary_faces_subset_simplexComplex F hF)
  have hBimage : (v ∘ Function.invFunOn u (Convexity.StdSimplex.coordinateSet ℝ (Fin (n + 2)))) '' B.space =
      (simplexBoundary F hF).space := by
    have h := boundaryComplex_space_of_isPLHomeomorphOn L M
      (IsPLBall.isCombinatorialManifoldWithBoundary (n := n) (K := L) ⟨u, hu⟩) hf
    rw [show M = simplexComplex F hF from rfl, boundaryComplex_simplexComplex hF hFcard] at h
    exact h.symm
  have hgside : g '' (coneComplex hpB).space = (coneComplex haB).space := by
    apply Subset.antisymm
    · rintro _ ⟨x, hx, rfl⟩
      rcases (mem_coneComplex_space_iff hpB).mp hx with rfl | ⟨z, hz, s, hs, hs', rfl⟩
      · rw [hgp]
        exact apex_mem_coneComplex_space haB
      · rw [hgrad z (boundaryComplex_space_subset (n + 1) L hz) s hs.le hs']
        exact (mem_coneComplex_space_iff haB).mpr
          (Or.inr ⟨_, hBimage ▸ ⟨z, hz, rfl⟩, s, hs, hs', rfl⟩)
    · intro y hy
      rcases (mem_coneComplex_space_iff haB).mp hy with rfl | ⟨z, hz, s, hs, hs', rfl⟩
      · exact ⟨p, apex_mem_coneComplex_space hpB, hgp⟩
      · obtain ⟨w, hw, rfl⟩ := hBimage.symm ▸ hz
        exact ⟨p + s • (w - p),
          (mem_coneComplex_space_iff hpB).mpr (Or.inr ⟨w, hw, s, hs, hs', rfl⟩),
          hgrad w (boundaryComplex_space_subset (n + 1) L hw) s hs.le hs'⟩
  have hmodel : frontier (convexHull ℝ (T : Set E)) =
      convexHull ℝ (F : Set E) ∪ (coneComplex haB).space := by
    rw [coneComplex_simplexBoundary_space_eq_biUnion_insert_erase F hF (by omega),
      frontier_convexHull_eq_biUnion_erase T hT hspan]
    ext x
    constructor
    · intro hx
      obtain ⟨b, hb, hxb⟩ := mem_iUnion₂.mp hx
      by_cases hba : b = a
      · exact Or.inl (by simpa only [hba] using hxb)
      · exact Or.inr (mem_iUnion₂.mpr ⟨b, Finset.mem_erase.mpr ⟨hba, hb⟩, by
          simpa only [← hins, Finset.erase_insert_of_ne (Ne.symm hba)] using hxb⟩)
    · rintro (hx | hx)
      · exact mem_iUnion₂.mpr ⟨a, ha, hx⟩
      · obtain ⟨b, hb, hxb⟩ := mem_iUnion₂.mp hx
        exact mem_iUnion₂.mpr ⟨b, Finset.mem_of_mem_erase hb, by
          simpa only [← hins, Finset.erase_insert_of_ne (Finset.mem_erase.mp hb).1.symm] using hxb⟩
  have hsideSub : (coneComplex hpB).space ⊆ (coneComplex hp).space := by
    intro x hx
    rcases (mem_coneComplex_space_iff hpB).mp hx with rfl | ⟨z, hz, s, hs, hs', rfl⟩
    · exact apex_mem_coneComplex_space hp
    · exact (mem_coneComplex_space_iff hp).mpr
        (Or.inr ⟨z, boundaryComplex_space_subset (n + 1) L hz, s, hs, hs', rfl⟩)
  apply (hg.bijOn.injOn.image_eq_image_iff hclosed.frontier_subset
    (union_subset (space_subset_coneComplex_space hp) hsideSub)).mp
  rw [hgfront, image_union, hgside, hgbase.image_eq, hf.image_eq, hMspace, hmodel]

end DifferentialGeometry.Topology.PiecewiseLinear
