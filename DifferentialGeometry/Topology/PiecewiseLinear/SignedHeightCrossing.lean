/-
Copyright (c) 2026 Bennett Chow. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bennett Chow
-/
import DifferentialGeometry.Topology.PiecewiseLinear.Section34PiercedBallFrontiers

/-! # Signed Height Crossing -/

open Set Topology

namespace DifferentialGeometry.Topology.PiecewiseLinear

theorem graph_mem_frontier_lower_height_region {E : Type*} [TopologicalSpace E]
    {P : Set E} {g : E → ℝ} {a : ℝ} {x : E} (hx : x ∈ P) (hax : a ≤ g x) :
    (x, g x) ∈ frontier {y : E × ℝ | y.1 ∈ P ∧ a ≤ y.2 ∧ y.2 ≤ g y.1} := by
  refine ⟨subset_closure ⟨hx, hax, le_rfl⟩, ?_⟩
  intro hi
  have hv : Continuous (fun t : ℝ => (x, t)) := continuous_const.prodMk continuous_id
  have hn := hv.continuousAt.preimage_mem_nhds (mem_interior_iff_mem_nhds.mp hi)
  have hI : Iic (g x) ∈ 𝓝 (g x) := Filter.mem_of_superset hn fun _ ht => ht.2.2
  have hm := mem_interior_iff_mem_nhds.mpr hI
  simp only [interior_Iic, mem_Iio, lt_self_iff_false] at hm

theorem graph_mem_frontier_upper_height_region {E : Type*} [TopologicalSpace E]
    {P : Set E} {g : E → ℝ} {b : ℝ} {x : E} (hx : x ∈ P) (hxb : g x ≤ b) :
    (x, g x) ∈ frontier {y : E × ℝ | y.1 ∈ P ∧ g y.1 ≤ y.2 ∧ y.2 ≤ b} := by
  refine ⟨subset_closure ⟨hx, le_rfl, hxb⟩, ?_⟩
  intro hi
  have hv : Continuous (fun t : ℝ => (x, t)) := continuous_const.prodMk continuous_id
  have hn := hv.continuousAt.preimage_mem_nhds (mem_interior_iff_mem_nhds.mp hi)
  have hI : Ici (g x) ∈ 𝓝 (g x) := Filter.mem_of_superset hn fun _ ht => ht.2.1
  have hm := mem_interior_iff_mem_nhds.mpr hI
  simp only [interior_Ici, mem_Ioi, lt_self_iff_false] at hm

theorem signed_height_regions_cross_along_zero_set {E : Type*} [TopologicalSpace E]
    {P : Set E} {g : E → ℝ} (hg : Continuous g) (hgb : ∀ x ∈ P, |g x| < 1)
    (hpos : {x | x ∈ P ∧ g x = 0} ⊆ closure (interior P ∩ {x | 0 < g x}))
    (hneg : {x | x ∈ P ∧ g x = 0} ⊆ closure (interior P ∩ {x | g x < 0})) :
    let A : Set (E × ℝ) := {y | y.1 ∈ P ∧ -1 ≤ y.2 ∧ y.2 ≤ g y.1}
    let B : Set (E × ℝ) := {y | y.1 ∈ P ∧ -g y.1 ≤ y.2 ∧ y.2 ≤ 1}
    let C := {x | x ∈ P ∧ g x = 0} ×ˢ {(0 : ℝ)}
    C ⊆ closure (frontier A ∩ interior B) ∧ C ⊆ closure (frontier A \ B) ∧
      C ⊆ closure (frontier B ∩ interior A) ∧ C ⊆ closure (frontier B \ A) := by
  intro A B C
  have hAi : {y : E × ℝ | y.1 ∈ interior P ∧ -1 < y.2 ∧ y.2 < g y.1} ⊆ interior A := by
    apply interior_maximal
    · exact fun _ hy => ⟨interior_subset hy.1, hy.2.1.le, hy.2.2.le⟩
    · exact (isOpen_interior.preimage continuous_fst).inter
        ((isOpen_lt continuous_const continuous_snd).inter
          (isOpen_lt continuous_snd (hg.comp continuous_fst)))
  have hBi : {y : E × ℝ | y.1 ∈ interior P ∧ -g y.1 < y.2 ∧ y.2 < 1} ⊆ interior B := by
    apply interior_maximal
    · exact fun _ hy => ⟨interior_subset hy.1, hy.2.1.le, hy.2.2.le⟩
    · exact (isOpen_interior.preimage continuous_fst).inter
        ((isOpen_lt (hg.neg.comp continuous_fst) continuous_snd).inter
          (isOpen_lt continuous_snd continuous_const))
  have hAgraph (x) (hx : x ∈ interior P) : (x, g x) ∈ frontier A :=
    graph_mem_frontier_lower_height_region (interior_subset hx)
      (abs_lt.mp (hgb x (interior_subset hx))).1.le
  have hBgraph (x) (hx : x ∈ interior P) : (x, -g x) ∈ frontier B :=
    graph_mem_frontier_upper_height_region (g := fun x => -g x) (b := 1) (interior_subset hx)
      (by have hb := (abs_lt.mp (hgb x (interior_subset hx))).1; linarith)
  have htransfer (q : E → ℝ) (hq : Continuous q) (J : Set E) (V : Set (E × ℝ))
      (hCJ : {x | x ∈ P ∧ g x = 0} ⊆ closure J)
      (hqzero : ∀ x, g x = 0 → q x = 0) (hJV : ∀ x ∈ J, (x, q x) ∈ V) : C ⊆ closure V := by
    rintro y ⟨hy, hyzero⟩
    have he : (y.1, q y.1) = y := Prod.ext rfl ((hqzero y.1 hy.2).trans hyzero.symm)
    rw [← he]
    exact (closure_mono (image_subset_iff.mpr hJV))
      (image_closure_subset_closure_image (continuous_id.prodMk hq) ⟨y.1, hCJ hy, rfl⟩)
  refine ⟨htransfer g hg _ _ hpos (fun _ hx => hx) ?_,
    htransfer g hg _ _ hneg (fun _ hx => hx) ?_,
    htransfer (fun x => -g x) hg.neg _ _ hpos (fun _ hx => by rw [hx, neg_zero]) ?_,
    htransfer (fun x => -g x) hg.neg _ _ hneg (fun _ hx => by rw [hx, neg_zero]) ?_⟩
  · rintro x ⟨hx, hgx⟩
    change 0 < g x at hgx
    exact ⟨hAgraph x hx, hBi ⟨hx, by change -g x < g x; linarith,
      (abs_lt.mp (hgb x (interior_subset hx))).2⟩⟩
  · rintro x ⟨hx, hgx⟩
    change g x < 0 at hgx
    refine ⟨hAgraph x hx, fun hb => ?_⟩
    have hh : -g x ≤ g x := hb.2.1
    linarith
  · rintro x ⟨hx, hgx⟩
    change 0 < g x at hgx
    exact ⟨hBgraph x hx, hAi ⟨hx,
      by have hb := (abs_lt.mp (hgb x (interior_subset hx))).2; change -1 < -g x; linarith,
      by change -g x < g x; linarith⟩⟩
  · rintro x ⟨hx, hgx⟩
    change g x < 0 at hgx
    refine ⟨hBgraph x hx, fun ha => ?_⟩
    have hh : -g x ≤ g x := ha.2.2
    linarith

end DifferentialGeometry.Topology.PiecewiseLinear
