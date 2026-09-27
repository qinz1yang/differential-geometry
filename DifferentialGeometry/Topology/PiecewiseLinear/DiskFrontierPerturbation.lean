/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.FiniteIntersection
import DifferentialGeometry.Topology.PiecewiseLinear.BallFrontier
import DifferentialGeometry.Topology.PiecewiseLinear.PLHomeomorphTopology

open Set

namespace DifferentialGeometry.Topology.PiecewiseLinear

open Classical in
theorem IsPLBall.exists_isPLBall_finite_frontier_inter
    {D C Z T U : Set (EuclideanSpace ℝ (Fin 2))} (hD : IsPLBall 2 D)
    (hC : IsClosed C) (hCD : C ⊆ interior D) (hZ : IsClosed Z) (hDZ : Disjoint D Z)
    (hT : IsPolyhedron T) (hTI : interior T = ∅) (hU : IsOpen U) (hDU : D ⊆ U) :
    ∃ D', IsPLBall 2 D' ∧ C ⊆ interior D' ∧ D' ⊆ U ∧ Disjoint D' Z ∧
      (frontier D' ∩ T).Finite := by
  obtain ⟨K, hKfin, hKspace⟩ := hD.isPLSphere_frontier.isPolyhedron.exists_simplicialComplex
  obtain ⟨L, hLfin, hLspace⟩ := hT.exists_simplicialComplex
  let _ : Finite K.faces := hKfin.to_subtype
  let _ : Finite L.faces := hLfin.to_subtype
  have hK : ∀ s ∈ K.faces, s.card ≤ 1 + 1 := fun s hs =>
    card_le_of_isPLSphere K (hKspace.symm ▸ hD.isPLSphere_frontier) hs
  have hL : ∀ s ∈ L.faces, s.card ≤ 1 + 1 := by
    intro s hs
    have hbound := card_le_finrank_succ_of_mem_faces L hs
    have hbound' : s.card ≤ 3 := by simpa using hbound
    by_contra hnot
    have hcard : s.card = 3 := by omega
    obtain ⟨x, hx⟩ := (isPLBall_convexHull_of_affineIndependent s (L.indep hs)
        hcard).interior_nonempty
    have hxT : x ∈ interior T := interior_mono
      ((L.convexHull_subset_space hs).trans hLspace.subset) hx
    rw [hTI] at hxT
    exact hxT
  let V := U \ (C ∪ Z)
  have hV : IsOpen V := hU.sdiff (hC.union hZ)
  have hKV : K.space ⊆ V := by
    intro x hx
    have hxF : x ∈ frontier D := hKspace ▸ hx
    have hxD : x ∈ D := hD.isPolyhedron.isClosed.frontier_subset hxF
    exact ⟨hDU hxD, fun hxCZ => hxCZ.elim (fun hxC => hxF.2 (hCD hxC))
      (fun hxZ => disjoint_left.mp hDZ hxD hxZ)⟩
  obtain ⟨f, hf, _, hfix, hfinite⟩ :=
    exists_small_homeomorph_finite_inter K L hK hL (by simp) hV hKV
      (by norm_num : (0 : ℝ) < 1)
  have hinj : Function.Injective f := by simpa only [injOn_univ] using hf.bijOn.injOn
  have hfixC : EqOn f id C := hfix.mono fun _ hx => fun h => h.2 (Or.inl hx)
  have hfixZ : EqOn f id Z := hfix.mono fun _ hx => fun h => h.2 (Or.inr hx)
  have hfixU : EqOn f id Uᶜ := hfix.mono fun _ hx => fun h => hx h.1
  have hfD := hf.restrict hD.isPolyhedron (subset_univ D)
  have hD' := hD.of_isPLHomeomorphOn hfD
  refine ⟨f '' D, hD', ?_, ?_, ?_, ?_⟩
  · intro x hx
    rw [← hfD.image_interior rfl]
    exact ⟨x, hCD hx, hfixC hx⟩
  · rintro x ⟨y, hy, rfl⟩
    by_contra hnot
    have heq : f y = y := hinj (hfixU hnot)
    exact hnot (heq.symm ▸ hDU hy)
  · refine disjoint_left.mpr ?_
    rintro x ⟨y, hy, rfl⟩ hxZ
    have heq : f y = y := hinj (hfixZ hxZ)
    exact disjoint_left.mp hDZ hy (heq ▸ hxZ)
  · rw [← hfD.image_frontier rfl hD.isPolyhedron.isClosed hD'.isPolyhedron.isClosed]
    simpa only [hKspace, hLspace] using hfinite

end DifferentialGeometry.Topology.PiecewiseLinear
