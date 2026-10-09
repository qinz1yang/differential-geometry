/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.ConeHalfSpace
import DifferentialGeometry.Analysis.Convex.CompactFrontier

open Set Topology

namespace DifferentialGeometry.Topology.PiecewiseLinear

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem isConeBase_of_space_subset_frontier_convex
    {C : Set E} (hC : Convex ℝ C) (hCc : IsClosed C) {p : E} (hp : p ∈ interior C)
    (L : Geometry.SimplicialComplex ℝ E) (hLC : L.space ⊆ frontier C) : IsConeBase p L := by
  classical
  have hclosure : closure (interior C) = C :=
    (hC.closure_interior_eq_closure_of_nonempty_interior ⟨p, hp⟩).trans hCc.closure_eq
  have hsep : ∀ x ∈ frontier C, ∃ A : E →ᵃ[ℝ] ℝ,
      0 < A p ∧ (∀ y ∈ C, 0 ≤ A y) ∧ A x = 0 := by
    intro x hx
    obtain ⟨f, hf⟩ := geometric_hahn_banach_open_point hC.interior isOpen_interior hx.2
    let A : E →ᵃ[ℝ] ℝ := AffineMap.const ℝ E (f x) - f.toLinearMap.toAffineMap
    have hA (y : E) : A y = f x - f y := rfl
    refine ⟨A, sub_pos.mpr (hf p hp), ?_, sub_self _⟩
    intro y hy
    have hclosed : IsClosed {z | f z ≤ f x} := isClosed_le f.continuous continuous_const
    have hsub : interior C ⊆ {z | f z ≤ f x} := fun z hz => (hf z hz).le
    have hle : f y ≤ f x := (closure_minimal hsub hclosed) (hclosure.symm ▸ hy)
    exact sub_nonneg.mpr hle
  have hcenter (s : L.faces) : (s : Finset E).centroid ℝ id ∈ frontier C :=
    hLC (L.convexHull_subset_space s.property (openSimplex_subset_convexHull _
      (centroid_mem_openSimplex (L.nonempty_of_mem_faces s.property))))
  choose A hpA hnonneg hzero using fun s : L.faces => hsep _ (hcenter s)
  apply isConeBase_of_affine_halfSpaces A L
    (fun x hx s => hnonneg s x (hCc.frontier_subset (hLC hx))) ?_ (Or.inl hpA)
  intro s hs
  refine ⟨⟨s, hs⟩, fun v hv => ?_⟩
  have hcent := centroid_mem_openSimplex (L.nonempty_of_mem_faces hs)
  have hcentC := openSimplex_subset_convexHull s hcent
  have hpos : 0 < weights s (s.centroid ℝ id) v :=
    (mem_openSimplex_self_iff (L.indep hs) hcentC).mp hcent v hv
  have hsum : ∑ w ∈ s, weights s (s.centroid ℝ id) w * A ⟨s, hs⟩ w = 0 := by
    have h := affineMap_apply_sum_smul (A ⟨s, hs⟩) (sum_weights hcentC)
    rw [sum_weights_smul hcentC, hzero ⟨s, hs⟩] at h
    simpa only [smul_eq_mul] using h.symm
  have hn : ∀ w ∈ s, 0 ≤ weights s (s.centroid ℝ id) w * A ⟨s, hs⟩ w := by
    intro w hw
    exact mul_nonneg (weights_nonneg hcentC hw)
      (hnonneg ⟨s, hs⟩ w (hCc.frontier_subset
        (hLC (L.convexHull_subset_space hs (subset_convexHull ℝ _ hw)))))
  have hz := (Finset.sum_eq_zero_iff_of_nonneg hn).mp hsum v hv
  exact (mul_eq_zero.mp hz).resolve_left hpos.ne'

theorem coneComplex_space_subset_convex [DecidableEq E] {C : Set E}
    (hC : Convex ℝ C) {p : E} (hp : p ∈ C)
    {L : Geometry.SimplicialComplex ℝ E} (hpL : IsConeBase p L) (hLC : L.space ⊆ C) :
    (coneComplex hpL).space ⊆ C := by
  intro x hx
  rcases (mem_coneComplex_space_iff hpL).mp hx with rfl | ⟨z, hz, t, ht, ht', rfl⟩
  · exact hp
  · rw [add_smul_sub_eq_combo]
    exact hC hp (hLC hz) (sub_nonneg.mpr ht') ht.le (by ring)

theorem coneComplex_space_inter_frontier [DecidableEq E] {C : Set E}
    (hC : Convex ℝ C) (hCc : IsClosed C) {p : E} (hp : p ∈ interior C)
    {L : Geometry.SimplicialComplex ℝ E} (hpL : IsConeBase p L)
    (hLC : L.space ⊆ frontier C) : (coneComplex hpL).space ∩ frontier C = L.space := by
  apply Subset.antisymm
  · rintro x ⟨hx, hxC⟩
    rcases (mem_coneComplex_space_iff hpL).mp hx with rfl | ⟨z, hz, t, ht, ht', rfl⟩
    · exact False.elim (hxC.2 hp)
    · have ht1 : t = 1 := by
        by_contra hne
        have hti : t < 1 := lt_of_le_of_ne ht' hne
        apply hxC.2
        rw [add_smul_sub_eq_combo]
        exact hC.combo_interior_self_mem_interior hp (hCc.frontier_subset (hLC hz))
          (sub_pos.mpr hti) ht.le (by ring)
      simpa only [ht1, one_smul, add_sub_cancel] using hz
  · intro x hx
    exact ⟨space_subset_coneComplex_space hpL hx, hLC hx⟩

theorem coneComplex_space_eq_of_convex [DecidableEq E] {C : Set E}
    (hC : Convex ℝ C) (hCc : IsCompact C) {p : E} (hp : p ∈ C)
    {L : Geometry.SimplicialComplex ℝ E} (hpL : IsConeBase p L)
    (hL : L.space = frontier C) : (coneComplex hpL).space = C := by
  ext x
  rw [mem_coneComplex_space_iff]
  constructor
  · rintro (rfl | ⟨z, hz, s, hs, hs', rfl⟩)
    · exact hp
    · rw [add_smul_sub_eq_combo]
      exact hC hp (hCc.isClosed.frontier_subset (hL ▸ hz)) (by linarith) hs.le (by ring)
  · intro hx
    by_cases hxp : x = p
    · exact Or.inl hxp
    obtain ⟨r, hr, hz⟩ := DifferentialGeometry.Analysis.IsCompact.exists_mem_frontier_add_smul hCc
        hx hxp
    have hr0 : 0 < r := lt_of_lt_of_le zero_lt_one hr
    refine Or.inr ⟨p + r • (x - p), hL.symm ▸ hz, r⁻¹, inv_pos.mpr hr0,
      (inv_le_one₀ hr0).mpr hr, ?_⟩
    rw [add_sub_cancel_left, smul_smul, inv_mul_cancel₀ hr0.ne', one_smul, add_sub_cancel]

end DifferentialGeometry.Topology.PiecewiseLinear
