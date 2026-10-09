/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.BoundaryFacets
import DifferentialGeometry.Topology.PiecewiseLinear.TriangleEdgeLink

open Set

namespace DifferentialGeometry.Topology.PiecewiseLinear

theorem height_section_subsingleton_of_unique_high_boundary_vertex
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [DecidableEq E] (L : Geometry.SimplicialComplex ℝ E) [Finite L.faces]
    (hL : IsCombinatorialManifoldWithBoundary 1 L) {a : E}
    (ha : {a} ∈ (boundaryComplex 1 L).faces) (f : E →ₗ[ℝ] ℝ) (r : ℝ)
    (hfa : r < f a) (hother : ∀ v ∈ L.vertices, v ≠ a → f v < r) :
    (L.space ∩ {x | f x = r}).Subsingleton := by
  obtain ⟨b, hneighbors⟩ :=
    (hL.mem_boundaryComplex_iff_unique_coface L (s := ({a} : Finset E)) (by simp)).mp ha
  have hbN : b ∈ {w | w ∉ ({a} : Finset E) ∧ insert w {a} ∈ L.faces} := by
    rw [hneighbors]
    exact Set.mem_singleton b
  have hba : b ≠ a := Finset.notMem_singleton.mp hbN.1
  have hbL : {b} ∈ L.faces :=
    L.down_closed hbN.2 (Finset.singleton_subset_iff.mpr (Finset.mem_insert_self b {a}))
      (Finset.singleton_nonempty b)
  have hfb : f b < r := hother b hbL hba
  have hfab : f a ≠ f b := by linarith
  have hpaircard : ({a, b} : Finset E).card = 2 := by simp [hba.symm]
  have hfinj : InjOn f ((({a, b} : Finset E) : Set E)) := by
    intro x hx y hy hxy
    simp only [Finset.coe_pair, Set.mem_insert_iff, Set.mem_singleton_iff] at hx hy
    rcases hx with (rfl | rfl) <;> rcases hy with (rfl | rfl)
    · rfl
    · exact (hfab hxy).elim
    · exact (hfab hxy.symm).elim
    · rfl
  have hsegment := injOn_linearMap_convexHull_of_card_eq_two
    ({a, b} : Finset E) hpaircard f hfinj
  have hmem (x : E) (hx : x ∈ L.space) (hfx : f x = r) :
      x ∈ convexHull ℝ ((({a, b} : Finset E) : Set E)) := by
    obtain ⟨s, hs, hxs⟩ := L.mem_space_iff.mp hx
    have has : a ∈ s := by
      by_contra has
      have hsub : (s : Set E) ⊆ {z | f z < r} := by
        intro v hv
        apply hother v
        · change {v} ∈ L.faces
          exact L.down_closed hs (Finset.singleton_subset_iff.mpr hv)
            (Finset.singleton_nonempty v)
        · intro hva
          exact has (hva ▸ hv)
      have hxlt := convexHull_min hsub (convex_halfSpace_lt f.isLinear r) hxs
      change f x < r at hxlt
      exact (ne_of_lt hxlt) hfx
    apply convexHull_mono (Finset.coe_subset.mpr ?_) hxs
    intro v hv
    by_cases hva : v = a
    · subst v
      exact Finset.mem_insert_self a {b}
    · have hav : ({a, v} : Finset E) ∈ L.faces := by
        apply L.down_closed hs _ (Finset.insert_nonempty a {v})
        intro z hz
        rcases Finset.mem_insert.mp hz with hza | hzv
        · exact hza ▸ has
        · exact Finset.mem_singleton.mp hzv ▸ hv
      have hvN : v ∈ {w | w ∉ ({a} : Finset E) ∧ insert w {a} ∈ L.faces} := by
        refine ⟨Finset.notMem_singleton.mpr hva, ?_⟩
        simpa only [Finset.pair_comm] using hav
      have hvb : v = b := by
        rw [hneighbors] at hvN
        exact Set.mem_singleton_iff.mp hvN
      rw [hvb]
      exact Finset.mem_insert_of_mem (Finset.mem_singleton_self b)
  rintro x ⟨hx, hfx⟩ y ⟨hy, hfy⟩
  change f x = r at hfx
  change f y = r at hfy
  exact hsegment (hmem x hx hfx) (hmem y hy hfy) (hfx.trans hfy.symm)

theorem height_section_subsingleton_of_unique_low_boundary_vertex
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [DecidableEq E] (L : Geometry.SimplicialComplex ℝ E) [Finite L.faces]
    (hL : IsCombinatorialManifoldWithBoundary 1 L) {a : E}
    (ha : {a} ∈ (boundaryComplex 1 L).faces) (f : E →ₗ[ℝ] ℝ) (r : ℝ)
    (hfa : f a < r) (hother : ∀ v ∈ L.vertices, v ≠ a → r < f v) :
    (L.space ∩ {x | f x = r}).Subsingleton := by
  have h := height_section_subsingleton_of_unique_high_boundary_vertex
    L hL ha (-f) (-r) (by simpa only [LinearMap.neg_apply, neg_lt_neg_iff] using hfa)
    (fun v hv hva => by
      simpa only [LinearMap.neg_apply, neg_lt_neg_iff] using hother v hv hva)
  simpa only [LinearMap.neg_apply, neg_inj] using h

end DifferentialGeometry.Topology.PiecewiseLinear
