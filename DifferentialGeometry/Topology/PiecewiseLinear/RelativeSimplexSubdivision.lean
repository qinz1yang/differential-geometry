/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.RelativeDerived
import DifferentialGeometry.Topology.SimplicialComplex.MaximalFace

/-!
# Stellar subdivision of a maximal simplex
-/

open Set

namespace DifferentialGeometry.Topology.PiecewiseLinear

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

open Classical in
theorem exists_isSubdivision_stellar_of_facet
    (K : Geometry.SimplicialComplex ℝ E) [Finite K.faces]
    {t : Finset E} (ht : t ∈ K.facets) :
    ∃ R : Geometry.SimplicialComplex ℝ E, IsSubdivision R K ∧ R.faces.Finite ∧
      ∀ s, s ∈ R.faces ↔ (s ∈ K.faces ∧ s ≠ t) ∨
        ∃ u : Finset E, u ⊂ t ∧ s = insert (t.centroid ℝ id) u := by
  classical
  let L := SimplicialComplex.geometricFaceCostar K t
  have hLK : L.faces ⊆ K.faces := fun _ hs => hs.1
  have hL (s : Finset E) : s ∈ L.faces ↔ s ∈ K.faces ∧ s ≠ t := by
    constructor
    · exact fun hs => ⟨hs.1, fun h => hs.2 (h ▸ Finset.Subset.refl t)⟩
    · rintro ⟨hs, hne⟩
      exact ⟨hs, fun hsub => hne (ht.2 hs hsub).symm⟩
  let hc := centroid_mem_openSimplex_of_mem_faces K
  let R := relDerived hLK (IsSubdivision.refl L) hc
  refine ⟨R, relDerived_isSubdivision _ _ _, relDerived_faces_finite _ _ _, ?_⟩
  intro s
  constructor
  · rintro ⟨u, d, h, rfl⟩
    have hd : ∀ v ∈ d, v = t := by
      intro v hv
      by_contra hne
      exact h.notMem v hv ((hL v).mpr ⟨h.flag.mem_faces hv, hne⟩)
    rcases d.eq_empty_or_nonempty with hd0 | hdne
    · simp only [hd0, Finset.image_empty, Finset.union_empty]
      apply Or.inl
      rcases h.base with hu | hu
      · subst u
        exact False.elim (h.nonempty.elim Finset.not_nonempty_empty
          (fun hne => hne.ne_empty hd0))
      · exact (hL _).mp hu
    · have hdeq : d = {t} := by
        apply Finset.eq_singleton_iff_unique_mem.mpr
        obtain ⟨v, hv⟩ := hdne
        exact ⟨hd v hv ▸ hv, hd⟩
      have htmem : t ∈ d := hdeq.symm ▸ Finset.mem_singleton_self t
      have hut : u ⊆ t := by
        rcases h.base with hu | hu
        · simp [hu]
        · intro v hv
          have hvface : {v} ∈ K.faces := K.down_closed (hLK hu)
            (Finset.singleton_subset_iff.mpr hv) (Finset.singleton_nonempty v)
          have hvt := face_subset_of_mem_openSimplex_of_mem_convexHull K hvface ht.1
            (by exact ⟨fun _ => 1, by simp, by simp, by simp⟩)
            (h.subset t htmem hv)
          exact hvt (Finset.mem_singleton_self v)
      have hune : u ≠ t := by
        rcases h.base with hu | hu
        · rw [hu]
          exact (K.nonempty_of_mem_faces ht.1).ne_empty.symm
        · exact ((hL _).mp hu).2
      refine Or.inr ⟨u, Finset.ssubset_iff_subset_ne.mpr ⟨hut, hune⟩, ?_⟩
      simp [hdeq]
  · rintro (⟨hs, hne⟩ | ⟨u, hut, rfl⟩)
    · exact faces_subset_relDerived hLK (IsSubdivision.refl L) hc ((hL _).mpr ⟨hs, hne⟩)
    · refine ⟨u, {t}, ?_, by simp⟩
      refine ⟨?_, ?_, ?_, ?_, Or.inr (Finset.singleton_nonempty _)⟩
      · rcases u.eq_empty_or_nonempty with hu | hu
        · exact Or.inl hu
        · exact Or.inr ((hL _).mpr ⟨K.down_closed ht.1 hut.subset hu, hut.ne⟩)
      · refine ⟨fun v hv => Finset.mem_singleton.mp hv ▸ ht.1, ?_⟩
        intro v hv w hw
        rw [Finset.mem_singleton] at hv hw
        subst v
        subst w
        exact Or.inl (Finset.Subset.refl _)
      · intro v hv hmem
        have hvt := Finset.mem_singleton.mp hv
        exact ((hL _).mp hmem).2 hvt
      · intro v hv x hx
        rw [Finset.mem_singleton.mp hv]
        exact subset_convexHull ℝ _ (hut.subset hx)

end DifferentialGeometry.Topology.PiecewiseLinear
