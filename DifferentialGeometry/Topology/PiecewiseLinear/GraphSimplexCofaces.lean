/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.Derived

open Set

namespace DifferentialGeometry.Topology.PiecewiseLinear

variable {E : Type*} [AddCommGroup E] [Module ℝ E]

theorem IsSubdivision.exists_two_triangles_over_graph_simplex
    {K K' : Geometry.SimplicialComplex ℝ E} (hsub : IsSubdivision K' K)
    {e t : Finset E} (he : e ∈ K'.faces) (ht : t ∈ K.faces) (htcard : t.card = 4)
    (hgraph : convexHull ℝ (e : Set E) ⊆
      ⋃ q ∈ {q : Finset E | q ∈ K.faces ∧ q.card ≤ 2}, convexHull ℝ (q : Set E))
    (het : convexHull ℝ (e : Set E) ⊆ convexHull ℝ (t : Set E)) :
    ∃ s₁ s₂ : Finset E, s₁ ∈ K.faces ∧ s₂ ∈ K.faces ∧
      s₁.card = 3 ∧ s₂.card = 3 ∧ s₁ ≠ s₂ ∧ s₁ ⊆ t ∧ s₂ ⊆ t ∧
      convexHull ℝ (e : Set E) ⊆ convexHull ℝ (s₁ : Set E) ∧
      convexHull ℝ (e : Set E) ⊆ convexHull ℝ (s₂ : Set E) := by
  classical
  have hx := centroid_mem_openSimplex_of_mem_faces K' e he
  have hxe := openSimplex_subset_convexHull e hx
  obtain ⟨q, ⟨hq, hqcard⟩, hxq⟩ := mem_iUnion₂.mp (hgraph hxe)
  have heq := hsub.convexHull_subset_of_mem_openSimplex hq he hx hxq
  have hcount : 1 < (t \ q).card := by
    have hle := Finset.card_le_card_sdiff_add_card (s := t) (t := q)
    omega
  obtain ⟨a, ha, b, hb, hab⟩ := Finset.one_lt_card.mp hcount
  obtain ⟨hat, haq⟩ := Finset.mem_sdiff.mp ha
  obtain ⟨hbt, hbq⟩ := Finset.mem_sdiff.mp hb
  have hcard (v : E) (hv : v ∈ t) : (t.erase v).card = 3 := by
    rw [Finset.card_erase_of_mem hv, htcard]
  have hface (v : E) (hv : v ∈ t) : t.erase v ∈ K.faces :=
    K.down_closed ht (Finset.erase_subset v t)
      (Finset.card_pos.mp (by rw [hcard v hv]; decide))
  have hcontain (v : E) (hvq : v ∉ q) :
      convexHull ℝ (e : Set E) ⊆ convexHull ℝ ((t.erase v : Finset E) : Set E) := by
    intro x hxe'
    have hxinter := K.inter_subset_convexHull ht hq ⟨het hxe', heq hxe'⟩
    refine convexHull_mono ?_ hxinter
    rintro z ⟨hzt, hzq⟩
    exact Finset.mem_coe.mpr (Finset.mem_erase.mpr
      ⟨fun hzv => hvq (hzv ▸ hzq), hzt⟩)
  refine ⟨t.erase a, t.erase b, hface a hat, hface b hbt, hcard a hat, hcard b hbt,
    ?_, Finset.erase_subset a t, Finset.erase_subset b t, hcontain a haq, hcontain b hbq⟩
  intro heq'
  exact hab ((Finset.erase_inj t hat).mp heq')

end DifferentialGeometry.Topology.PiecewiseLinear
