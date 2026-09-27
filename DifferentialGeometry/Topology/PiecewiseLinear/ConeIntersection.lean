/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.SimplexAvoiding

open Set

namespace DifferentialGeometry.Topology.PiecewiseLinear

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem IsConeBase.space_inter_convexHull_insert [DecidableEq E]
    {K : Geometry.SimplicialComplex ℝ E} {p : E} (hp : IsConeBase p K)
    {t : Finset E} (ht : t ∈ K.faces) :
    K.space ∩ convexHull ℝ ((insert p t : Finset E) : Set E) = convexHull ℝ (t : Set E) := by
  apply Subset.antisymm
  · rintro x ⟨hxK, hx⟩
    rcases exists_combo_of_mem_convexHull_insert (hp.notMem_face ht) hx with
      rfl | ⟨z, hz, s, hs, -, hxs⟩
    · exact (hp.notMem_space hxK).elim
    · exact hp.radial z (K.convexHull_subset_space ht hz) x hxK s hs hxs ▸ hz
  · intro x hx
    exact ⟨K.convexHull_subset_space ht hx,
      convexHull_mono (Finset.coe_subset.mpr (Finset.subset_insert p t)) hx⟩

theorem coneComplex_space_inter [DecidableEq E] {K L M B : Geometry.SimplicialComplex ℝ E}
    {p : E} (hp : IsConeBase p K) (hL : L.faces ⊆ K.faces) (hM : M.faces ⊆ K.faces)
    (hB : B.faces ⊆ L.faces) (hinter : L.space ∩ M.space = B.space) :
    (coneComplex (hp.of_faces_subset hL)).space ∩ (coneComplex (hp.of_faces_subset hM)).space =
      (coneComplex ((hp.of_faces_subset hL).of_faces_subset hB)).space := by
  have hLK : L.space ⊆ K.space := space_mono_of_faces_subset hL
  have hMK : M.space ⊆ K.space := space_mono_of_faces_subset hM
  apply Subset.antisymm
  · rintro x ⟨hxL, hxM⟩
    rcases (mem_coneComplex_space_iff (hp.of_faces_subset hL)).mp hxL with rfl | ⟨z, hz, s, hs, hs',
        rfl⟩
    · exact apex_mem_coneComplex_space _
    rcases (mem_coneComplex_space_iff (hp.of_faces_subset hM)).mp hxM with hx | ⟨w, hw, t, ht, ht',
        hx⟩
    · rw [hx]
      exact apex_mem_coneComplex_space _
    have hwz : w = p + (s / t) • (z - p) := by
      have heq : s • (z - p) = t • (w - p) := add_left_cancel hx
      have h := congrArg (fun v : E => t⁻¹ • v) heq
      simp only [smul_smul, inv_mul_cancel₀ ht.ne', one_smul] at h
      rw [div_eq_inv_mul, h, add_sub_cancel]
    have hwz' : w = z := hp.radial z (hLK hz) w (hMK hw) (s / t) (div_pos hs ht) hwz
    have hzB : z ∈ B.space := hinter ▸ ⟨hz, hwz' ▸ hw⟩
    exact (mem_coneComplex_space_iff _).mpr (Or.inr ⟨z, hzB, s, hs, hs', rfl⟩)
  · intro x hx
    rcases (mem_coneComplex_space_iff _).mp hx with rfl | ⟨z, hz, s, hs, hs', rfl⟩
    · exact ⟨apex_mem_coneComplex_space _, apex_mem_coneComplex_space _⟩
    have hzLM : z ∈ L.space ∩ M.space := hinter.symm ▸ hz
    exact ⟨(mem_coneComplex_space_iff _).mpr (Or.inr ⟨z, hzLM.1, s, hs, hs', rfl⟩),
      (mem_coneComplex_space_iff _).mpr (Or.inr ⟨z, hzLM.2, s, hs, hs', rfl⟩)⟩

theorem coneComplex_space_inter_base [DecidableEq E] {K L M B : Geometry.SimplicialComplex ℝ E}
    {p : E} (hp : IsConeBase p K) (hL : L.faces ⊆ K.faces) (hM : M.faces ⊆ K.faces)
    (hinter : L.space ∩ M.space = B.space) :
    (coneComplex (hp.of_faces_subset hL)).space ∩ M.space = B.space := by
  have hLK : L.space ⊆ K.space := space_mono_of_faces_subset hL
  have hMK : M.space ⊆ K.space := space_mono_of_faces_subset hM
  apply Subset.antisymm
  · rintro x ⟨hxL, hxM⟩
    rcases (mem_coneComplex_space_iff _).mp hxL with rfl | ⟨z, hz, s, hs, hs', hxs⟩
    · exact (hp.notMem_space (hMK hxM)).elim
    · have hxz : x = z := hp.radial z (hLK hz) x (hMK hxM) s hs hxs
      exact hinter ▸ ⟨hxz ▸ hz, hxM⟩
  · intro x hx
    have hxLM : x ∈ L.space ∩ M.space := hinter.symm ▸ hx
    exact ⟨space_subset_coneComplex_space _ hxLM.1, hxLM.2⟩

theorem coneComplex_simplexComplex_space [DecidableEq E] (T : Finset E)
    (hT : AffineIndependent ℝ ((↑) : T → E)) (hne : T.Nonempty)
    {p : E} (hp : IsConeBase p (simplexComplex T hT)) :
    (coneComplex hp).space = convexHull ℝ ((insert p T : Finset E) : Set E) := by
  have hpT : p ∉ T := hp.notMem_face ⟨hne, subset_rfl⟩
  ext x
  rw [mem_coneComplex_space_iff, simplexComplex_space _ _ hne]
  constructor
  · rintro (rfl | ⟨z, hz, s, hs, hs', rfl⟩)
    · exact subset_convexHull ℝ _ (Finset.mem_insert_self _ T)
    · exact mem_convexHull_insert_of_combo hz hs.le hs'
  · exact exists_combo_of_mem_convexHull_insert hpT

end DifferentialGeometry.Topology.PiecewiseLinear
