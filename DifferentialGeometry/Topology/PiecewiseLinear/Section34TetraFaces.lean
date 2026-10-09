/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.Section34TetraSkeleton

open Set

namespace DifferentialGeometry.Topology.PiecewiseLinear

universe u

variable {Ea : Type} [NormedAddCommGroup Ea] [NormedSpace ℝ Ea]

namespace SimplicialComplex

variable {K : Geometry.SimplicialComplex ℝ Ea}

open Classical in
theorem mem_convexHull_inter_of_mem_segment {s : Finset Ea} (hs : s ∈ K.faces) {u v x : Ea}
    (huv : ({u, v} : Finset Ea) ∈ K.faces) (hx : x ∈ segment ℝ u v)
    (hxs : x ∈ convexHull ℝ (s : Set Ea)) :
    x ∈ convexHull ℝ ((({u, v} : Finset Ea) ∩ s : Finset Ea) : Set Ea) := by
  classical
  have h := K.inter_subset_convexHull huv hs
    ⟨by rw [Finset.coe_pair, convexHull_pair]; exact hx, hxs⟩
  rwa [← Finset.coe_inter] at h

open Classical in
theorem section34Incident_of_subset_segment {e s : Finset Ea} {u v : Ea}
    (he : convexHull ℝ (e : Set Ea) ⊆ segment ℝ u v) (hu : u ∈ s) (hv : v ∈ s) :
    Section34Incident e s := fun _ hz =>
  (convex_convexHull ℝ _).segment_subset (subset_convexHull ℝ _ hu) (subset_convexHull ℝ _ hv)
    (he (subset_convexHull ℝ _ hz))

open Classical in
theorem not_section34Incident_of_notMem_left {e s : Finset Ea} (hs : s ∈ K.faces) {u : Ea}
    (huK : ({u} : Finset Ea) ∈ K.faces) (hue : u ∈ e) (hus : u ∉ s) :
    ¬ Section34Incident e s := by
  classical
  intro h
  have hu : u ∈ convexHull ℝ (s : Set Ea) := h (Finset.mem_coe.mpr hue)
  have h' := K.inter_subset_convexHull huK hs
    ⟨subset_convexHull ℝ _ (Finset.mem_coe.mpr (Finset.mem_singleton_self u)), hu⟩
  rw [← Finset.coe_inter, Finset.singleton_inter_of_notMem hus, Finset.coe_empty,
    convexHull_empty] at h'
  exact h'

open Classical in
theorem not_section34Incident_of_notMem_right {e s : Finset Ea} (hs : s ∈ K.faces)
    {u v x : Ea} (huv : ({u, v} : Finset Ea) ∈ K.faces) (hx : x ∈ e) (hxseg : x ∈ segment ℝ u v)
    (hxu : x ≠ u) (hvs : v ∉ s) : ¬ Section34Incident e s := by
  classical
  intro h
  have hxs : x ∈ convexHull ℝ (s : Set Ea) := h (Finset.mem_coe.mpr hx)
  have h' := mem_convexHull_inter_of_mem_segment hs huv hxseg hxs
  have hsub : (({u, v} : Finset Ea) ∩ s : Finset Ea) ⊆ {u} := by
    intro z hz
    rw [Finset.mem_inter, Finset.mem_insert, Finset.mem_singleton] at hz
    rcases hz with ⟨hz | hz, hzs⟩
    · exact Finset.mem_singleton.mpr hz
    · rw [hz] at hzs
      exact absurd hzs hvs
  have h'' := convexHull_mono (Finset.coe_subset.mpr hsub) h'
  rw [Finset.coe_singleton, convexHull_singleton] at h''
  exact hxu h''

end SimplicialComplex

variable {M : Type u} [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
  {U : Set M} {𝒦 : LocallyFinitePLPieceIn Ea 3 M U}

open Classical in
theorem section34SimplexIndex_eq_of_incident {t : Finset Ea} (ht : t ∈ 𝒦.complex.faces)
    {a b c d : Ea} (htabcd : t = {a, b, c, d}) (hab : a ≠ b) (hac : a ≠ c) (had : a ≠ d)
    (hbc : b ≠ c) (hbd : b ≠ d) (hcd : c ≠ d) (s : Section34SimplexIndex 𝒦 3)
    (hs : Section34Incident s.1 t) :
    s.1 = {a, c, d} ∨ s.1 = {a, b, c} ∨ s.1 = {b, c, d} ∨ s.1 = {a, b, d} := by
  classical
  have hsub : s.1 ⊆ t := by
    intro x hx
    have hxK : ({x} : Finset Ea) ∈ 𝒦.complex.faces :=
      𝒦.complex.down_closed s.2.1 (Finset.singleton_subset_iff.mpr hx) (Finset.singleton_nonempty x)
    have h := 𝒦.complex.inter_subset_convexHull hxK ht
      ⟨subset_convexHull ℝ _ (Finset.mem_coe.mpr (Finset.mem_singleton_self x)),
        hs (Finset.mem_coe.mpr hx)⟩
    rw [← Finset.coe_inter] at h
    by_contra hxt
    rw [Finset.singleton_inter_of_notMem hxt, Finset.coe_empty, convexHull_empty] at h
    exact h
  rw [htabcd] at hsub
  have hcard3 : ∀ {x y z : Ea}, x ≠ y → x ≠ z → y ≠ z → ({x, y, z} : Finset Ea).card = 3 :=
    fun hxy hxz hyz => Finset.card_eq_three.mpr ⟨_, _, _, hxy, hxz, hyz, rfl⟩
  have hsub3 : ∀ {x y z : Ea}, s.1 ⊆ {x, y, z} → x ≠ y → x ≠ z → y ≠ z → s.1 = {x, y, z} :=
    fun h hxy hxz hyz => Finset.eq_of_subset_of_card_le h (by rw [hcard3 hxy hxz hyz, s.2.2])
  have hmiss : ∀ x ∈ s.1, x = a ∨ x = b ∨ x = c ∨ x = d := fun x hx => by
    simpa only [Finset.mem_insert, Finset.mem_singleton] using hsub hx
  by_cases hbs : b ∈ s.1
  · by_cases has : a ∈ s.1
    · by_cases hcs : c ∈ s.1
      · refine Or.inr (Or.inl (Finset.eq_of_subset_of_card_le ?_ ?_).symm)
        · intro x hx
          simp only [Finset.mem_insert, Finset.mem_singleton] at hx
          rcases hx with rfl | rfl | rfl
          · exact has
          · exact hbs
          · exact hcs
        · rw [s.2.2, hcard3 hab hac hbc]
      · refine Or.inr (Or.inr (Or.inr (hsub3 (fun x hx => ?_) hab had hbd)))
        rcases hmiss x hx with rfl | rfl | rfl | rfl
        · simp
        · simp
        · exact absurd hx hcs
        · simp
    · refine Or.inr (Or.inr (Or.inl (hsub3 (fun x hx => ?_) hbc hbd hcd)))
      rcases hmiss x hx with rfl | rfl | rfl | rfl
      · exact absurd hx has
      · simp
      · simp
      · simp
  · refine Or.inl (hsub3 (fun x hx => ?_) hac had hcd)
    rcases hmiss x hx with rfl | rfl | rfl | rfl
    · simp
    · exact absurd hx hbs
    · simp
    · simp

end DifferentialGeometry.Topology.PiecewiseLinear
