/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.BoundaryArcSection

open Set

namespace DifferentialGeometry.Topology.PiecewiseLinear

theorem linearMap_level_section_convexHull_pair_subsingleton_of_apply_ne
    {E : Type*} [AddCommGroup E] [Module ℝ E] {a b : E} (hab : a ≠ b)
    (f : E →ₗ[ℝ] ℝ) (r : ℝ) (ha : f a ≠ r) :
    (convexHull ℝ ({a, b} : Set E) ∩ {x | f x = r}).Subsingleton := by
  classical
  by_cases hfab : f a = f b
  · rintro x ⟨hx, hfx⟩
    rw [convexHull_pair, segment_eq_image_lineMap] at hx
    obtain ⟨t, -, rfl⟩ := hx
    change f (t • (b - a) + a) = r at hfx
    apply (ha ?_).elim
    calc
      f a = f (t • (b - a) + a) := by
        simp only [map_add, map_smul, map_sub, smul_eq_mul, hfab, sub_self, mul_zero,
          zero_add]
      _ = r := hfx
  · have hcard : ({a, b} : Finset E).card = 2 := by simp [hab]
    have hfinj : InjOn f ((({a, b} : Finset E) : Set E)) := by
      intro x hx y hy hxy
      simp only [Finset.coe_pair, Set.mem_insert_iff, Set.mem_singleton_iff] at hx hy
      rcases hx with (rfl | rfl) <;> rcases hy with (rfl | rfl)
      · rfl
      · exact (hfab hxy).elim
      · exact (hfab hxy.symm).elim
      · rfl
    have hsegment := injOn_linearMap_convexHull_of_card_eq_two
      ({a, b} : Finset E) hcard f hfinj
    rintro x ⟨hx, hfx⟩ y ⟨hy, hfy⟩
    apply hsegment
    · simpa only [Finset.coe_pair] using hx
    · simpa only [Finset.coe_pair] using hy
    · exact hfx.trans hfy.symm

theorem height_section_encard_le_two_of_boundary_vertices
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [DecidableEq E] (L : Geometry.SimplicialComplex ℝ E) [Finite L.faces]
    (hL : IsCombinatorialManifoldWithBoundary 1 L) {a b : E}
    (ha : {a} ∈ (boundaryComplex 1 L).faces)
    (hb : {b} ∈ (boundaryComplex 1 L).faces)
    (f : E →ₗ[ℝ] ℝ) (r : ℝ) (hfa : f a ≠ r) (hfb : f b ≠ r)
    (hother : ∀ v ∈ L.vertices, v ≠ a → v ≠ b → f v < r) :
    (L.space ∩ {x | f x = r}).encard ≤ 2 := by
  obtain ⟨a', haneighbors⟩ :=
    (hL.mem_boundaryComplex_iff_unique_coface L (s := ({a} : Finset E)) (by simp)).mp ha
  obtain ⟨b', hbneighbors⟩ :=
    (hL.mem_boundaryComplex_iff_unique_coface L (s := ({b} : Finset E)) (by simp)).mp hb
  have ha'N : a' ∈ {w | w ∉ ({a} : Finset E) ∧ insert w {a} ∈ L.faces} := by
    rw [haneighbors]
    exact Set.mem_singleton a'
  have hb'N : b' ∈ {w | w ∉ ({b} : Finset E) ∧ insert w {b} ∈ L.faces} := by
    rw [hbneighbors]
    exact Set.mem_singleton b'
  have haa' : a ≠ a' := (Finset.notMem_singleton.mp ha'N.1).symm
  have hbb' : b ≠ b' := (Finset.notMem_singleton.mp hb'N.1).symm
  let A := convexHull ℝ ((({a, a'} : Finset E) : Set E)) ∩ {x | f x = r}
  let B := convexHull ℝ ((({b, b'} : Finset E) : Set E)) ∩ {x | f x = r}
  have hA : A.Subsingleton := by
    simpa only [A, Finset.coe_pair] using
      linearMap_level_section_convexHull_pair_subsingleton_of_apply_ne haa' f r hfa
  have hB : B.Subsingleton := by
    simpa only [B, Finset.coe_pair] using
      linearMap_level_section_convexHull_pair_subsingleton_of_apply_ne hbb' f r hfb
  have hsub : L.space ∩ {x | f x = r} ⊆ A ∪ B := by
    rintro x ⟨hxL, hfx⟩
    obtain ⟨s, hs, hxs⟩ := L.mem_space_iff.mp hxL
    by_cases has : a ∈ s
    · apply Or.inl
      refine ⟨convexHull_mono (Finset.coe_subset.mpr ?_) hxs, hfx⟩
      intro v hv
      by_cases hva : v = a
      · exact hva ▸ Finset.mem_insert_self a {a'}
      · have hav : ({a, v} : Finset E) ∈ L.faces := by
          apply L.down_closed hs _ (Finset.insert_nonempty a {v})
          intro z hz
          rcases Finset.mem_insert.mp hz with hza | hzv
          · exact hza ▸ has
          · exact Finset.mem_singleton.mp hzv ▸ hv
        have hvN : v ∈ {w | w ∉ ({a} : Finset E) ∧ insert w {a} ∈ L.faces} := by
          refine ⟨Finset.notMem_singleton.mpr hva, ?_⟩
          simpa only [Finset.pair_comm] using hav
        have hva' : v = a' := by
          rw [haneighbors] at hvN
          exact Set.mem_singleton_iff.mp hvN
        subst v
        exact Finset.mem_insert_of_mem (Finset.mem_singleton_self a')
    · by_cases hbs : b ∈ s
      · apply Or.inr
        refine ⟨convexHull_mono (Finset.coe_subset.mpr ?_) hxs, hfx⟩
        intro v hv
        by_cases hvb : v = b
        · exact hvb ▸ Finset.mem_insert_self b {b'}
        · have hbv : ({b, v} : Finset E) ∈ L.faces := by
            apply L.down_closed hs _ (Finset.insert_nonempty b {v})
            intro z hz
            rcases Finset.mem_insert.mp hz with hzb | hzv
            · exact hzb ▸ hbs
            · exact Finset.mem_singleton.mp hzv ▸ hv
          have hvN : v ∈ {w | w ∉ ({b} : Finset E) ∧ insert w {b} ∈ L.faces} := by
            refine ⟨Finset.notMem_singleton.mpr hvb, ?_⟩
            simpa only [Finset.pair_comm] using hbv
          have hvb' : v = b' := by
            rw [hbneighbors] at hvN
            exact Set.mem_singleton_iff.mp hvN
          subst v
          exact Finset.mem_insert_of_mem (Finset.mem_singleton_self b')
      · have hslt : (s : Set E) ⊆ {z | f z < r} := by
          intro v hv
          apply hother v
          · change {v} ∈ L.faces
            exact L.down_closed hs (Finset.singleton_subset_iff.mpr hv)
              (Finset.singleton_nonempty v)
          · intro hva
            exact has (hva ▸ hv)
          · intro hvb
            exact hbs (hvb ▸ hv)
        have hxlt := convexHull_min hslt (convex_halfSpace_lt f.isLinear r) hxs
        exact ((ne_of_lt hxlt) hfx).elim
  calc
    (L.space ∩ {x | f x = r}).encard ≤ (A ∪ B).encard := encard_mono hsub
    _ ≤ A.encard + B.encard := encard_union_le A B
    _ ≤ 1 + 1 := add_le_add
      (encard_le_one_iff_subsingleton.mpr hA)
      (encard_le_one_iff_subsingleton.mpr hB)
    _ = 2 := by norm_num

end DifferentialGeometry.Topology.PiecewiseLinear
