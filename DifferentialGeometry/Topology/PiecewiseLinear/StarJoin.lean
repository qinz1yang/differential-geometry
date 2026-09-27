/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.BallSphereLink
import DifferentialGeometry.Topology.PiecewiseLinear.JoinInternal
import DifferentialGeometry.Topology.PiecewiseLinear.JoinInvariance
import DifferentialGeometry.Topology.PiecewiseLinear.StarAvoiding

open Set

namespace DifferentialGeometry.Topology.PiecewiseLinear

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem eq_of_mem_openSimplex_singleton {x v : E} (hx : x ∈ openSimplex {v}) : x = v := by
  obtain ⟨w, -, hw1, hwx⟩ := hx
  rw [Finset.sum_singleton] at hw1 hwx
  rw [← hwx, hw1, one_smul]

variable [DecidableEq E] (K : Geometry.SimplicialComplex ℝ E) {t : Finset E} (ht : t ∈ K.faces)

include ht

omit [DecidableEq E] in
theorem simplexBoundary_faces_subset_of_mem_faces :
    (simplexBoundary t (K.indep ht)).faces ⊆ K.faces := fun _ hs =>
  K.down_closed ht hs.1 hs.2.1

theorem union_mem_of_mem_simplexBoundary_of_mem_geometricLink :
    ∀ s ∈ (simplexBoundary t (K.indep ht)).faces,
      ∀ u ∈ (SimplicialComplex.geometricLink K t).faces, s ∪ u ∈ K.faces := by
  intro s hs u hu
  exact K.down_closed hu.2.2 (Finset.union_subset_union hs.1 subset_rfl)
    (hs.2.1.mono Finset.subset_union_left)

omit ht in
theorem disjoint_of_mem_simplexBoundary_of_mem_geometricLink
    {hT : AffineIndependent ℝ ((↑) : t → E)} :
    ∀ s ∈ (simplexBoundary t hT).faces, ∀ u ∈ (SimplicialComplex.geometricLink K t).faces,
      Disjoint s u :=
  fun _ hs _ hu => hu.2.1.mono_left hs.1

theorem starAvoiding_eq_internalJoin :
    starAvoiding K t = internalJoin K (simplexBoundary t (K.indep ht))
      (SimplicialComplex.geometricLink K t) (simplexBoundary_faces_subset_of_mem_faces K ht)
      (geometricLink_faces_subset K t)
      (union_mem_of_mem_simplexBoundary_of_mem_geometricLink K ht) := by
  ext u
  rw [mem_starAvoiding_faces_iff, mem_internalJoin_faces_iff]
  constructor
  · rintro ⟨hu, hut, htu⟩
    refine ⟨u ∩ t, u \ t, ?_, ?_, ?_, ?_⟩
    · rcases (u ∩ t).eq_empty_or_nonempty with h | h
      · exact Or.inl h
      · refine Or.inr ⟨Finset.inter_subset_right, h, fun heq => htu ?_⟩
        rw [← heq]
        exact Finset.inter_subset_left
    · rcases (u \ t).eq_empty_or_nonempty with h | h
      · exact Or.inl h
      · refine Or.inr ⟨h, Finset.disjoint_sdiff, ?_⟩
        rw [Finset.union_sdiff_self_eq_union, Finset.union_comm]
        exact hut
    · obtain ⟨w, hw⟩ := K.nonempty_of_mem_faces hu
      by_cases hwt : w ∈ t
      · exact Or.inl ⟨w, Finset.mem_inter.mpr ⟨hw, hwt⟩⟩
      · exact Or.inr ⟨w, Finset.mem_sdiff.mpr ⟨hw, hwt⟩⟩
    · rw [Finset.union_comm, Finset.sdiff_union_inter]
  · rintro ⟨s, r, hs, hr, hne, rfl⟩
    have hst : s ⊆ t := by
      rcases hs with rfl | hs
      · exact Finset.empty_subset t
      · exact hs.1
    have htr : t ∪ r ∈ K.faces := by
      rcases hr with rfl | hr
      · rwa [Finset.union_empty]
      · exact hr.2.2
    have hsub : s ∪ r ⊆ t ∪ r := Finset.union_subset_union hst subset_rfl
    refine ⟨K.down_closed htr hsub ?_, ?_, ?_⟩
    · rcases hne with h | h
      · exact h.mono Finset.subset_union_left
      · exact h.mono Finset.subset_union_right
    · have heq : s ∪ r ∪ t = t ∪ r := by
        ext w
        simp only [Finset.mem_union]
        constructor
        · rintro ((h | h) | h)
          · exact Or.inl (hst h)
          · exact Or.inr h
          · exact Or.inl h
        · rintro (h | h)
          · exact Or.inr h
          · exact Or.inl (Or.inr h)
      rwa [heq]
    · intro htsr
      have hts : t ⊆ s := by
        intro w hw
        rcases Finset.mem_union.mp (htsr hw) with h | h
        · exact h
        · exfalso
          rcases hr with rfl | hr
          · exact Finset.notMem_empty w h
          · exact Finset.disjoint_left.mp hr.2.1 hw h
      rcases hs with rfl | hs
      · exact (K.nonempty_of_mem_faces ht).ne_empty (Finset.subset_empty.mp hts)
      · exact hs.2.2 (Finset.Subset.antisymm hs.1 hts)

omit ht in
theorem starAvoiding_singleton (v : E) :
    starAvoiding K {v} = SimplicialComplex.geometricLink K {v} := by
  ext s
  rw [mem_starAvoiding_faces_iff, SimplicialComplex.mem_geometricLink_singleton,
    Finset.singleton_subset_iff]
  constructor
  · rintro ⟨hs, hsv, hvs⟩
    exact ⟨K.nonempty_of_mem_faces hs, hvs, by rwa [Finset.insert_eq, Finset.union_comm]⟩
  · rintro ⟨hne, hvs, hins⟩
    refine ⟨K.down_closed hins (Finset.subset_insert v s) hne, ?_, hvs⟩
    rwa [Finset.insert_eq, Finset.union_comm] at hins

theorem exists_isPLHomeomorphOn_starAvoiding [FiniteDimensional ℝ E] [Finite K.faces] :
    ∃ f : E → E × E × ℝ, IsPLHomeomorphOn f (starAvoiding K t).space
      (joinComplex (simplexBoundary t (K.indep ht))
        (SimplicialComplex.geometricLink K t)).space := by
  have hfinA := (simplexBoundary_faces_finite t (K.indep ht)).to_subtype
  have hfin := (internalJoin_faces_finite K _ _ (simplexBoundary_faces_subset_of_mem_faces K ht)
    (geometricLink_faces_subset K t)
    (union_mem_of_mem_simplexBoundary_of_mem_geometricLink K ht)).to_subtype
  have hfinJ := (joinComplex_faces_finite (simplexBoundary t (K.indep ht))
    (SimplicialComplex.geometricLink K t)).to_subtype
  rw [starAvoiding_eq_internalJoin K ht]
  exact ⟨_, (isGlueIso_internalJoin K _ _ _ _ _
    (disjoint_of_mem_simplexBoundary_of_mem_geometricLink K)).isPLHomeomorphOn⟩

theorem isPLBall_geometricLink_of_isPLBall_geometricLink [FiniteDimensional ℝ E] [Finite K.faces]
    {x : E} (hx : x ∈ openSimplex t) {K' : Geometry.SimplicialComplex ℝ E} [Finite K'.faces]
    (hK' : IsSubdivision K' K) (hx' : {x} ∈ K'.faces) {k b : ℕ} (hcard : t.card = k + 1)
    (hball : IsPLBall b (SimplicialComplex.geometricLink K t).space) :
    IsPLBall (k + b) (SimplicialComplex.geometricLink K' {x}).space := by
  cases k with
  | zero =>
    obtain ⟨v, rfl⟩ := Finset.card_eq_one.mp hcard
    obtain rfl := eq_of_mem_openSimplex_singleton hx
    rw [isPLBall_geometricLink_iff_of_isSubdivision hK' ht, Nat.zero_add]
    exact hball
  | succ k =>
    obtain ⟨f, hf⟩ := exists_isPLHomeomorphOn_geometricLink_starAvoiding K ht hx hK' hx'
    obtain ⟨g, hg⟩ := exists_isPLHomeomorphOn_starAvoiding K ht
    have hfinA := (simplexBoundary_faces_finite t (K.indep ht)).to_subtype
    have hsph : IsPLSphere k (simplexBoundary t (K.indep ht)).space := by
      rw [simplexBoundary_space t (K.indep ht) (by omega)]
      exact isPLSphere_biUnion_erase t (K.indep ht) hcard
    have h := (isPLBall_joinComplex_of_isPLSphere_of_isPLBall hsph hball).of_isPLHomeomorphOn
      (hf.trans hg).symm
    rwa [show k + b + 1 = k + 1 + b by omega] at h

theorem isPLSphere_geometricLink_of_isPLSphere_geometricLink [FiniteDimensional ℝ E]
    [Finite K.faces] {x : E} (hx : x ∈ openSimplex t) {K' : Geometry.SimplicialComplex ℝ E}
    [Finite K'.faces] (hK' : IsSubdivision K' K) (hx' : {x} ∈ K'.faces) {k b : ℕ}
    (hcard : t.card = k + 1) (hsph : IsPLSphere b (SimplicialComplex.geometricLink K t).space) :
    IsPLSphere (k + b) (SimplicialComplex.geometricLink K' {x}).space := by
  cases k with
  | zero =>
    obtain ⟨v, rfl⟩ := Finset.card_eq_one.mp hcard
    obtain rfl := eq_of_mem_openSimplex_singleton hx
    rw [isPLSphere_geometricLink_iff_of_isSubdivision hK' ht, Nat.zero_add]
    exact hsph
  | succ k =>
    obtain ⟨f, hf⟩ := exists_isPLHomeomorphOn_geometricLink_starAvoiding K ht hx hK' hx'
    obtain ⟨g, hg⟩ := exists_isPLHomeomorphOn_starAvoiding K ht
    have hfinA := (simplexBoundary_faces_finite t (K.indep ht)).to_subtype
    have hsph' : IsPLSphere k (simplexBoundary t (K.indep ht)).space := by
      rw [simplexBoundary_space t (K.indep ht) (by omega)]
      exact isPLSphere_biUnion_erase t (K.indep ht) hcard
    have h := (isPLSphere_joinComplex_of_isPLSphere hsph' hsph).of_isPLHomeomorphOn
      (hf.trans hg).symm
    rwa [show k + b + 1 = k + 1 + b by omega] at h

end DifferentialGeometry.Topology.PiecewiseLinear
