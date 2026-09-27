/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.GeneralPosition
import DifferentialGeometry.Topology.PiecewiseLinear.ManifoldInvariance
import DifferentialGeometry.Topology.PiecewiseLinear.Section34CompactVocabulary
import DifferentialGeometry.Topology.PiecewiseLinear.SimplexBoundary
import DifferentialGeometry.Topology.PiecewiseLinear.Subcomplex

open Set

namespace DifferentialGeometry.Topology.PiecewiseLinear

local notation "E3" => EuclideanSpace ℝ (Fin 3)

variable {K K' : Geometry.SimplicialComplex ℝ E3}

theorem convexHull_inter_section34CompactGraphSkeleton_subset_rim {t : Finset E3}
    (ht : t ∈ K.faces) (hcard : 3 ≤ t.card) :
    convexHull ℝ (t : Set E3) ∩ section34CompactGraphSkeleton K ⊆
      section34CompactSimplexRim t := by
  rintro x ⟨hxt, hxg⟩
  obtain ⟨u, ⟨hu, hucard⟩, hxu⟩ := mem_iUnion₂.mp hxg
  have hx := K.inter_subset_convexHull ht hu ⟨hxt, hxu⟩
  rw [← Finset.coe_inter] at hx
  refine mem_iUnion₂.mpr ⟨t ∩ u, Finset.ssubset_iff_subset_ne.mpr
    ⟨Finset.inter_subset_left, fun h => ?_⟩, hx⟩
  rw [Finset.inter_eq_left] at h
  have := Finset.card_le_card h
  omega

theorem section34CompactSimplexRim_subset_graphSkeleton {t : Finset E3} (ht : t ∈ K.faces)
    (hcard : t.card ≤ 3) : section34CompactSimplexRim t ⊆ section34CompactGraphSkeleton K := by
  intro x hx
  obtain ⟨u, hu, hxu⟩ := mem_iUnion₂.mp hx
  have hut : u ⊂ t := hu
  by_cases hne : u.Nonempty
  · have huK : u ∈ K.faces := K.down_closed ht (Finset.ssubset_iff_subset_ne.mp hut).1 hne
    have hlt := Finset.card_lt_card hut
    exact mem_iUnion₂.mpr ⟨u, ⟨huK, by omega⟩, hxu⟩
  · rw [Finset.not_nonempty_iff_eq_empty] at hne
    subst hne
    simp at hxu

theorem isPLSphere_one_section34CompactSimplexRim {t : Finset E3} (ht : t ∈ K.faces)
    (hcard : t.card = 3) : IsPLSphere 1 (section34CompactSimplexRim t) := by
  classical
  have heq : section34CompactSimplexRim t =
      ⋃ v ∈ t, convexHull ℝ ((t.erase v : Finset E3) : Set E3) := by
    apply Subset.antisymm
    · intro x hx
      obtain ⟨u, hu, hxu⟩ := mem_iUnion₂.mp hx
      have hut : u ⊂ t := hu
      obtain ⟨v, hvt, hvu⟩ := Finset.exists_of_ssubset hut
      refine mem_iUnion₂.mpr ⟨v, hvt, convexHull_mono (fun y hy => ?_) hxu⟩
      have hyu : y ∈ u := Finset.mem_coe.mp hy
      refine Finset.mem_coe.mpr (Finset.mem_erase.mpr ⟨fun h => hvu ?_,
        (Finset.ssubset_iff_subset_ne.mp hut).1 hyu⟩)
      rw [← h]
      exact hyu
    · intro x hx
      obtain ⟨v, hvt, hxv⟩ := mem_iUnion₂.mp hx
      exact mem_iUnion₂.mpr ⟨t.erase v, Finset.erase_ssubset hvt, hxv⟩
  rw [heq]
  exact isPLSphere_biUnion_erase (n := 1) t (K.indep ht) hcard

theorem exists_section34CompactEdgeIndex_pair_of_incident (hsub : IsSubdivision K' K)
    (hK' : K'.faces.Finite) (s : Section34CompactSimplexIndex K 3)
    (w : Section34CompactVertexIndex K K') (hw : Section34Incident w.1 s.1) :
    ∃ e₁ e₂ : Section34CompactEdgeIndex K K', e₁ ≠ e₂ ∧ Section34Incident e₁.1 s.1 ∧
      Section34Incident e₂.1 s.1 ∧ w.1 ⊆ e₁.1 ∧ w.1 ⊆ e₂.1 ∧
      ∀ e : Section34CompactEdgeIndex K K', Section34Incident e.1 s.1 → w.1 ⊆ e.1 →
        e = e₁ ∨ e = e₂ := by
  classical
  have hRK : (restrict K (section34CompactSimplexRim s.1)).space =
      section34CompactSimplexRim s.1 := by
    apply restrict_space_of_eq_biUnion
    apply Subset.antisymm
    · intro x hx
      obtain ⟨u, hu, hxu⟩ := mem_iUnion₂.mp hx
      have hut : u ⊂ s.1 := hu
      have hne : u.Nonempty := by
        by_contra hne
        rw [Finset.not_nonempty_iff_eq_empty] at hne
        subst hne
        simp at hxu
      have huK : u ∈ K.faces :=
        K.down_closed s.2.1 (Finset.ssubset_iff_subset_ne.mp hut).1 hne
      exact mem_iUnion₂.mpr ⟨u, ⟨huK, fun y hy => mem_iUnion₂.mpr ⟨u, hu, hy⟩⟩, hxu⟩
    · exact iUnion₂_subset fun u hu => hu.2
  have hLsp : (restrict K' (section34CompactSimplexRim s.1)).space =
      section34CompactSimplexRim s.1 := by
    have h := (hsub.restrict (restrict K (section34CompactSimplexRim s.1))
      (restrict_faces_subset K _)).1
    rw [hRK] at h
    exact h
  have _ : Finite K'.faces := hK'.to_subtype
  have _ : Finite (restrict K' (section34CompactSimplexRim s.1)).faces :=
    (restrict_faces_finite K' _).to_subtype
  have hLman : IsCombinatorialManifold 1 (restrict K' (section34CompactSimplexRim s.1)) := by
    refine IsPLSphere.isCombinatorialManifold (n := 0) ?_
    rw [hLsp]
    exact isPLSphere_one_section34CompactSimplexRim s.2.1 s.2.2
  obtain ⟨-, hnbr⟩ := (isCombinatorialManifold_one_iff _).mp hLman
  obtain ⟨v, hv⟩ := Finset.card_eq_one.mp w.2.2.1
  have hvw : v ∈ (w.1 : Set E3) := by
    rw [hv]
    exact Finset.mem_coe.mpr (Finset.mem_singleton_self v)
  have hvR : v ∈ section34CompactSimplexRim s.1 :=
    convexHull_inter_section34CompactGraphSkeleton_subset_rim s.2.1 s.2.2.ge
      ⟨hw hvw, w.2.2.2 (subset_convexHull ℝ _ hvw)⟩
  have hvL : ({v} : Finset E3) ∈ (restrict K' (section34CompactSimplexRim s.1)).faces := by
    refine ⟨hv ▸ w.2.1, ?_⟩
    rw [Finset.coe_singleton, convexHull_singleton]
    exact singleton_subset_iff.mpr hvR
  obtain ⟨a, b, hab, hnb⟩ := hnbr v hvL
  have hmem : ∀ x, x ∈ ({a, b} : Set E3) →
      x ≠ v ∧ ({v, x} : Finset E3) ∈ (restrict K' (section34CompactSimplexRim s.1)).faces := by
    intro x hx
    rw [← hnb] at hx
    exact ⟨hx.1, by convert hx.2⟩
  have hedge : ∀ x, x ≠ v →
      ({v, x} : Finset E3) ∈ (restrict K' (section34CompactSimplexRim s.1)).faces →
      ∃ e : Section34CompactEdgeIndex K K', e.1 = {v, x} ∧ Section34Incident e.1 s.1 := by
    intro x hxv hx
    refine ⟨⟨{v, x}, hx.1, Finset.card_pair (Ne.symm hxv),
      hx.2.trans (section34CompactSimplexRim_subset_graphSkeleton s.2.1 s.2.2.le)⟩, rfl, ?_⟩
    exact (subset_convexHull ℝ _).trans (hx.2.trans (section34CompactSimplexRim_subset s.1))
  obtain ⟨ha, haL⟩ := hmem a (mem_insert a {b})
  obtain ⟨hb, hbL⟩ := hmem b (mem_insert_of_mem a (mem_singleton b))
  obtain ⟨e₁, he₁, hi₁⟩ := hedge a ha haL
  obtain ⟨e₂, he₂, hi₂⟩ := hedge b hb hbL
  have hwe : ∀ x, w.1 ⊆ ({v, x} : Finset E3) := by
    intro x
    rw [hv]
    exact Finset.singleton_subset_iff.mpr (Finset.mem_insert_self v {x})
  refine ⟨e₁, e₂, fun h => hab ?_, hi₁, hi₂, he₁ ▸ hwe a, he₂ ▸ hwe b, fun e he hwe' => ?_⟩
  · have hvab : ({v, a} : Finset E3) = {v, b} := by rw [← he₁, ← he₂, h]
    have ha' : a ∈ ({v, b} : Finset E3) := by
      rw [← hvab]
      exact Finset.mem_insert_of_mem (Finset.mem_singleton_self a)
    rcases Finset.mem_insert.mp ha' with h' | h'
    · exact absurd h' ha
    · exact Finset.mem_singleton.mp h'
  · obtain ⟨x, y, hxy, hexy⟩ := Finset.card_eq_two.mp e.2.2.1
    have hve : v ∈ e.1 := hwe' (by rw [hv]; exact Finset.mem_singleton_self v)
    obtain ⟨z, hzv, hez⟩ : ∃ z, z ≠ v ∧ e.1 = {v, z} := by
      rw [hexy] at hve
      rcases Finset.mem_insert.mp hve with h | h
      · refine ⟨y, fun h' => hxy ?_, ?_⟩
        · rw [← h, ← h']
        · rw [hexy, ← h]
      · have h := Finset.mem_singleton.mp h
        refine ⟨x, fun h' => hxy ?_, ?_⟩
        · rw [h', h]
        · rw [hexy, h, Finset.pair_comm]
    have heR : convexHull ℝ (e.1 : Set E3) ⊆ section34CompactSimplexRim s.1 := by
      intro p hp
      exact convexHull_inter_section34CompactGraphSkeleton_subset_rim s.2.1 s.2.2.ge
        ⟨convexHull_min he (convex_convexHull ℝ _) hp, e.2.2.2 hp⟩
    have hzL : ({v, z} : Finset E3) ∈ (restrict K' (section34CompactSimplexRim s.1)).faces := by
      rw [← hez]
      exact ⟨e.2.1, heR⟩
    have hz : z ∈ ({a, b} : Set E3) := by
      rw [← hnb]
      exact ⟨hzv, by convert hzL⟩
    rcases hz with hz | hz
    · left
      apply Subtype.ext
      rw [hez, he₁, hz]
    · right
      apply Subtype.ext
      rw [hez, he₂, mem_singleton_iff.mp hz]

end DifferentialGeometry.Topology.PiecewiseLinear
