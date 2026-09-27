/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.ConeExtension
import DifferentialGeometry.Topology.PiecewiseLinear.ConeIntersection

open Set

namespace DifferentialGeometry.Topology.PiecewiseLinear

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [DecidableEq E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [DecidableEq F]

theorem image_coneComplex_of_radial_eq
    {L M : Geometry.SimplicialComplex ℝ E} {L' M' : Geometry.SimplicialComplex ℝ F}
    {p : E} {q : F} (hp : IsConeBase p L) (hq : IsConeBase q L')
    (hM : M.faces ⊆ L.faces) (hM' : M'.faces ⊆ L'.faces)
    {f g : E → F} (hgp : g p = q)
    (hgrad : ∀ z ∈ L.space, ∀ s : ℝ, 0 ≤ s → s ≤ 1 →
      g (p + s • (z - p)) = q + s • (f z - q))
    (hf : f '' M.space = M'.space) :
    g '' (coneComplex (hp.of_faces_subset hM)).space =
      (coneComplex (hq.of_faces_subset hM')).space := by
  apply Subset.antisymm
  · rintro y ⟨x, hx, rfl⟩
    rcases (mem_coneComplex_space_iff _).mp hx with rfl | ⟨z, hz, s, hs, hs1, rfl⟩
    · rw [hgp]
      exact apex_mem_coneComplex_space _
    · rw [hgrad z (space_mono_of_faces_subset hM hz) s hs.le hs1]
      exact (mem_coneComplex_space_iff _).mpr
        (Or.inr ⟨f z, hf ▸ mem_image_of_mem f hz, s, hs, hs1, rfl⟩)
  · intro y hy
    rcases (mem_coneComplex_space_iff _).mp hy with rfl | ⟨w, hw, s, hs, hs1, rfl⟩
    · exact ⟨p, apex_mem_coneComplex_space _, hgp⟩
    · obtain ⟨z, hz, rfl⟩ := hf.symm ▸ hw
      exact ⟨p + s • (z - p),
        (mem_coneComplex_space_iff _).mpr (Or.inr ⟨z, hz, s, hs, hs1, rfl⟩),
        hgrad z (space_mono_of_faces_subset hM hz) s hs.le hs1⟩

private theorem linearMap_combo_eq_zero_iff {V : Type*} [AddCommGroup V] [Module ℝ V]
    (a : V →ₗ[ℝ] ℝ) {v : V} (hv : a v = 0) (z : V) (s : ℝ) (hs : 0 < s) :
    a (v + s • (z - v)) = 0 ↔ a z = 0 := by
  simp only [map_add, map_smul, map_sub, hv, zero_add, sub_zero, smul_eq_mul,
    mul_eq_zero, hs.ne', false_or]
theorem image_coneComplex_inter_fiber_of_radial_eq
    {L : Geometry.SimplicialComplex ℝ E} {L' : Geometry.SimplicialComplex ℝ F}
    {p : E} {q : F} (hp : IsConeBase p L) (hq : IsConeBase q L')
    (ℓ : E →ₗ[ℝ] ℝ) (ℓ' : F →ₗ[ℝ] ℝ) (hpℓ : ℓ p = 0) (hqℓ : ℓ' q = 0)
    {f g : E → F} (hgp : g p = q)
    (hgrad : ∀ z ∈ L.space, ∀ s : ℝ, 0 ≤ s → s ≤ 1 →
      g (p + s • (z - p)) = q + s • (f z - q))
    (hf : f '' (L.space ∩ {x | ℓ x = 0}) = L'.space ∩ {x | ℓ' x = 0}) :
    g '' ((coneComplex hp).space ∩ {x | ℓ x = 0}) =
      (coneComplex hq).space ∩ {x | ℓ' x = 0} := by
  apply Subset.antisymm
  · rintro y ⟨x, ⟨hx, hxℓ⟩, rfl⟩
    rcases (mem_coneComplex_space_iff hp).mp hx with rfl | ⟨z, hz, s, hs, hs1, rfl⟩
    · rw [hgp]
      exact ⟨apex_mem_coneComplex_space hq, hqℓ⟩
    · have hzℓ := (linearMap_combo_eq_zero_iff ℓ hpℓ z s hs).mp hxℓ
      have hzf := hf.subset (mem_image_of_mem f ⟨hz, hzℓ⟩)
      rw [hgrad z hz s hs.le hs1]
      exact ⟨(mem_coneComplex_space_iff hq).mpr (Or.inr ⟨f z, hzf.1, s, hs, hs1, rfl⟩),
        (linearMap_combo_eq_zero_iff ℓ' hqℓ (f z) s hs).mpr hzf.2⟩
  · rintro y ⟨hy, hyℓ⟩
    rcases (mem_coneComplex_space_iff hq).mp hy with rfl | ⟨w, hw, s, hs, hs1, rfl⟩
    · exact ⟨p, ⟨apex_mem_coneComplex_space hp, hpℓ⟩, hgp⟩
    · have hwℓ := (linearMap_combo_eq_zero_iff ℓ' hqℓ w s hs).mp hyℓ
      obtain ⟨z, ⟨hz, hzℓ⟩, rfl⟩ := hf.symm.subset ⟨hw, hwℓ⟩
      exact ⟨p + s • (z - p),
        ⟨(mem_coneComplex_space_iff hp).mpr (Or.inr ⟨z, hz, s, hs, hs1, rfl⟩),
          (linearMap_combo_eq_zero_iff ℓ hpℓ z s hs).mpr hzℓ⟩, hgrad z hz s hs.le hs1⟩

private theorem geometricLink_faces_subset_of_faces_subset
    {K M : Geometry.SimplicialComplex ℝ E} (hM : M.faces ⊆ K.faces) (p : E) :
    (SimplicialComplex.geometricLink M {p}).faces ⊆ (SimplicialComplex.geometricLink K {p}).faces :=
        by
  intro s hs
  obtain ⟨hne, hp, hs⟩ := (SimplicialComplex.mem_geometricLink_singleton M p s).mp hs
  exact (SimplicialComplex.mem_geometricLink_singleton K p s).mpr ⟨hne, hp, hM hs⟩

theorem exists_isPLHomeomorphOn_closedStar_pair
    [FiniteDimensional ℝ E] [FiniteDimensional ℝ F]
    (K : Geometry.SimplicialComplex ℝ E) [Finite K.faces]
    (K' : Geometry.SimplicialComplex ℝ F) [Finite K'.faces]
    (M : Geometry.SimplicialComplex ℝ E) (M' : Geometry.SimplicialComplex ℝ F)
    (hM : M.faces ⊆ K.faces) (hM' : M'.faces ⊆ K'.faces)
    {p : E} {q : F} (hp : {p} ∈ M.faces) (hq : {q} ∈ M'.faces)
    {f : E → F} (hf : IsPLHomeomorphOn f (SimplicialComplex.geometricLink K {p}).space
      (SimplicialComplex.geometricLink K' {q}).space)
    (hfM : f '' (SimplicialComplex.geometricLink M {p}).space =
      (SimplicialComplex.geometricLink M' {q}).space)
    (ℓ : E →ₗ[ℝ] ℝ) (ℓ' : F →ₗ[ℝ] ℝ) (hpℓ : ℓ p = 0) (hqℓ : ℓ' q = 0)
    (hfzero : f '' ((SimplicialComplex.geometricLink K {p}).space ∩ {x | ℓ x = 0}) =
      (SimplicialComplex.geometricLink K' {q}).space ∩ {x | ℓ' x = 0}) :
    ∃ g : E → F, IsPLHomeomorphOn g (closedStar K p) (closedStar K' q) ∧
      g p = q ∧ g '' closedStar M p = closedStar M' q ∧
      g '' (closedStar K p ∩ {x | ℓ x = 0}) = closedStar K' q ∩ {x | ℓ' x = 0} := by
  let hcone := isConeBase_geometricLink K (p := p)
  let hcone' := isConeBase_geometricLink K' (p := q)
  obtain ⟨g, hg, -, hgp, hgrad⟩ := exists_isPLHomeomorphOn_coneComplex hcone hcone' hf
  have hstar := image_coneComplex_of_radial_eq hcone hcone'
    (geometricLink_faces_subset_of_faces_subset hM p)
    (geometricLink_faces_subset_of_faces_subset hM' q) hgp hgrad hfM
  have hzero := image_coneComplex_inter_fiber_of_radial_eq hcone hcone' ℓ ℓ' hpℓ hqℓ hgp hgrad
      hfzero
  have hstarM : g '' closedStar M p = closedStar M' q := by
    rw [closedStar_eq_coneComplex_space M hp, closedStar_eq_coneComplex_space M' hq]
    exact hstar
  rw [← closedStar_eq_coneComplex_space K (hM hp),
    ← closedStar_eq_coneComplex_space K' (hM' hq)] at hg hzero
  exact ⟨g, hg, hgp, hstarM, hzero⟩

end DifferentialGeometry.Topology.PiecewiseLinear
