/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.AmbientExtension
import DifferentialGeometry.Topology.PiecewiseLinear.PLHomeomorphGluing

open Set

namespace DifferentialGeometry.Topology.PiecewiseLinear

theorem exists_isPLHomeomorphOn_extension_coneComplex_union_radial
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [DecidableEq E] {L B : Geometry.SimplicialComplex ℝ E} [Finite L.faces]
    (hB : B.faces ⊆ L.faces) {p q : E} (hp : IsConeBase p L) (hq : IsConeBase q L)
    (hinter : (coneComplex hp).space ∩ (coneComplex hq).space = L.space)
    (hfrontier : frontier ((coneComplex hp).space ∪ (coneComplex hq).space) ⊆
      (coneComplex (hp.of_faces_subset hB)).space ∪ (coneComplex (hq.of_faces_subset hB)).space)
    {f : E → E} (hf : IsPLHomeomorphOn f L.space L.space) (hfix : EqOn f id B.space) :
    ∃ h : E ≃ₜ E, IsPLHomeomorphOn h univ univ ∧ EqOn h f L.space ∧
      h '' (coneComplex hp).space = (coneComplex hp).space ∧
      h '' (coneComplex hq).space = (coneComplex hq).space ∧
      EqOn h id ((coneComplex hp).space ∪ (coneComplex hq).space)ᶜ ∧
      h p = p ∧ h q = q ∧
      (∀ z ∈ L.space, ∀ s : ℝ, 0 ≤ s → s ≤ 1 →
        h (p + s • (z - p)) = p + s • (f z - p)) ∧
      (∀ z ∈ L.space, ∀ s : ℝ, 0 ≤ s → s ≤ 1 →
        h (q + s • (z - q)) = q + s • (f z - q)) := by
  have : Finite (coneComplex hp).faces := (coneComplex_faces_finite hp (Set.toFinite
      L.faces)).to_subtype
  have : Finite (coneComplex hq).faces := (coneComplex_faces_finite hq (Set.toFinite
      L.faces)).to_subtype
  have hP := isPolyhedron_space (coneComplex hp)
  have hQ := isPolyhedron_space (coneComplex hq)
  have hBL : B.space ⊆ L.space := by
    intro x hx
    obtain ⟨s, hs, hxs⟩ := B.mem_space_iff.mp hx
    exact L.convexHull_subset_space (hB hs) hxs
  have hconeSubset {r : E} (hr : IsConeBase r L) :
      (coneComplex (hr.of_faces_subset hB)).space ⊆ (coneComplex hr).space := by
    intro x hx
    rcases (mem_coneComplex_space_iff (hr.of_faces_subset hB)).mp hx with
      rfl | ⟨z, hz, s, hs, hs', rfl⟩
    · exact apex_mem_coneComplex_space hr
    · exact (mem_coneComplex_space_iff hr).mpr (Or.inr ⟨z, hBL hz, s, hs, hs', rfl⟩)
  have hconeFixed {r : E} (hr : IsConeBase r L) {u : E → E} (hpoint : u r = r)
      (hrad : ∀ z ∈ L.space, ∀ s : ℝ, 0 ≤ s → s ≤ 1 →
        u (r + s • (z - r)) = r + s • (f z - r)) :
      EqOn u id (coneComplex (hr.of_faces_subset hB)).space := by
    intro x hx
    rcases (mem_coneComplex_space_iff (hr.of_faces_subset hB)).mp hx with
      rfl | ⟨z, hz, s, hs, hs', rfl⟩
    · exact hpoint
    · change u (r + s • (z - r)) = r + s • (z - r)
      rw [hrad z (hBL hz) s hs.le hs', hfix hz, id_eq]
  obtain ⟨gP, hgP, hgPf, hgp, hPrad⟩ := exists_isPLHomeomorphOn_coneComplex hp hp hf
  obtain ⟨gQ, hgQ, hgQf, hgq, hQrad⟩ := exists_isPLHomeomorphOn_coneComplex hq hq hf
  have hagree : EqOn gP gQ ((coneComplex hp).space ∩ (coneComplex hq).space) := by
    rw [hinter]
    exact hgPf.trans hgQf.symm
  have hsurj : SurjOn gP ((coneComplex hp).space ∩ (coneComplex hq).space)
      ((coneComplex hp).space ∩ (coneComplex hq).space) := by
    rw [hinter]
    intro y hy
    obtain ⟨x, hx, hxy⟩ := hf.bijOn.surjOn hy
    exact ⟨x, hx, (hgPf hx).trans hxy⟩
  obtain ⟨g, hg, hgP', hgQ'⟩ :=
    exists_isPLHomeomorphOn_union_of_eqOn_inter hP hQ hgP hgQ hagree hsurj
  have hgfix : EqOn g id (frontier ((coneComplex hp).space ∪ (coneComplex hq).space)) := by
    intro x hx
    rcases hfrontier hx with hx | hx
    · exact (hgP' (hconeSubset hp hx)).trans (hconeFixed hp hgp hPrad hx)
    · exact (hgQ' (hconeSubset hq hx)).trans (hconeFixed hq hgq hQrad hx)
  obtain ⟨h, hh, hhg, hhfix⟩ := hg.exists_extension_of_eqOn_frontier (hP.union hQ) hgfix
  have hhP : EqOn h gP (coneComplex hp).space := (hhg.mono subset_union_left).trans hgP'
  have hhQ : EqOn h gQ (coneComplex hq).space := (hhg.mono subset_union_right).trans hgQ'
  exact ⟨h, hh, (hhP.mono (space_subset_coneComplex_space hp)).trans hgPf,
    hhP.image_eq.trans hgP.image_eq, hhQ.image_eq.trans hgQ.image_eq, hhfix,
    (hhP (apex_mem_coneComplex_space hp)).trans hgp,
    (hhQ (apex_mem_coneComplex_space hq)).trans hgq,
    fun z hz s hs hs' => (hhP (by
      by_cases hs0 : s = 0
      · simpa only [hs0, zero_smul, add_zero] using apex_mem_coneComplex_space hp
      · exact (mem_coneComplex_space_iff hp).mpr
          (Or.inr ⟨z, hz, s, lt_of_le_of_ne hs (Ne.symm hs0), hs', rfl⟩))).trans
        (hPrad z hz s hs hs'),
    fun z hz s hs hs' => (hhQ (by
      by_cases hs0 : s = 0
      · simpa only [hs0, zero_smul, add_zero] using apex_mem_coneComplex_space hq
      · exact (mem_coneComplex_space_iff hq).mpr
          (Or.inr ⟨z, hz, s, lt_of_le_of_ne hs (Ne.symm hs0), hs', rfl⟩))).trans
        (hQrad z hz s hs hs')⟩

theorem exists_isPLHomeomorphOn_extension_coneComplex_union
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [DecidableEq E] {L B : Geometry.SimplicialComplex ℝ E} [Finite L.faces]
    (hB : B.faces ⊆ L.faces) {p q : E} (hp : IsConeBase p L) (hq : IsConeBase q L)
    (hinter : (coneComplex hp).space ∩ (coneComplex hq).space = L.space)
    (hfrontier : frontier ((coneComplex hp).space ∪ (coneComplex hq).space) ⊆
      (coneComplex (hp.of_faces_subset hB)).space ∪ (coneComplex (hq.of_faces_subset hB)).space)
    {f : E → E} (hf : IsPLHomeomorphOn f L.space L.space) (hfix : EqOn f id B.space) :
    ∃ h : E ≃ₜ E, IsPLHomeomorphOn h univ univ ∧ EqOn h f L.space ∧
      h '' (coneComplex hp).space = (coneComplex hp).space ∧
      h '' (coneComplex hq).space = (coneComplex hq).space ∧
      EqOn h id ((coneComplex hp).space ∪ (coneComplex hq).space)ᶜ := by
  obtain ⟨h, hh, hhf, hhP, hhQ, hhfix, -⟩ :=
    exists_isPLHomeomorphOn_extension_coneComplex_union_radial hB hp hq hinter hfrontier hf hfix
  exact ⟨h, hh, hhf, hhP, hhQ, hhfix⟩

end DifferentialGeometry.Topology.PiecewiseLinear
