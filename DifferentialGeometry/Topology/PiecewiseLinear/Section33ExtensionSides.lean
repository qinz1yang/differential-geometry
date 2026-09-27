/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.Section33ExtensionRegions
import DifferentialGeometry.Topology.PiecewiseLinear.SurfaceSideChaining

open Set Topology

namespace DifferentialGeometry.Topology.PiecewiseLinear

local notation "E3" => EuclideanSpace ℝ (Fin 3)

theorem IsPLSphere.exists_connected_neighborhood_pair_sdiff_of_two {S : Set E3}
    (hS : IsPLSphere 2 S) {p : E3} (hp : p ∈ S) {U : Set E3} (hU : U ∈ 𝓝 p) :
    ∃ C ∈ 𝓝 p, C ⊆ U ∧
      ∃ A B : Set E3, IsConnected A ∧ IsConnected B ∧ A ∪ B = C \ S ∧
        C ∩ S ⊆ closure A ∧ C ∩ S ⊆ closure B := by
  classical
  obtain ⟨L, hLfin, hLS⟩ := hS.isPolyhedron.exists_simplicialComplex
  let _ : Finite L.faces := hLfin.to_subtype
  have hL : IsCombinatorialManifold 2 L := IsPLSphere.isCombinatorialManifold (n := 1) (hLS ▸ hS)
  rw [← hLS] at hp ⊢
  exact hL.exists_connected_neighborhood_pair_sdiff L finrank_euclideanSpace_fin hp hU

theorem exists_connected_neighborhood_pair_sdiff_frontier_space
    {XK : Geometry.SimplicialComplex ℝ E3} (hfin : XK.faces.Finite)
    (hX : IsCombinatorialManifoldWithBoundary 3 XK) {p : E3} (hp : p ∈ frontier XK.space)
    {U : Set E3} (hU : U ∈ 𝓝 p) :
    ∃ C ∈ 𝓝 p, C ⊆ U ∧
      ∃ A B : Set E3, IsConnected A ∧ IsConnected B ∧ A ∪ B = C \ frontier XK.space ∧
        C ∩ frontier XK.space ⊆ closure A ∧ C ∩ frontier XK.space ⊆ closure B := by
  classical
  let _ : Finite XK.faces := hfin.to_subtype
  let BX := @boundaryComplex _ _ _ (Classical.decEq _) (2 + 1) XK
  have hFr : frontier XK.space = BX.space := frontier_space_eq_boundaryComplex_space hX
  let _ : Finite BX.faces := ((Set.toFinite XK.faces).subset fun _ hs => hs.1).to_subtype
  have hBman : IsCombinatorialManifold 2 BX := isCombinatorialManifold_boundaryComplex XK hX
  rw [hFr] at hp ⊢
  exact hBman.exists_connected_neighborhood_pair_sdiff BX finrank_euclideanSpace_fin hp hU

theorem isConnected_sdiff_closedBall_of_ball_subset {V : Set E3} (hV : IsConnected V)
    {p : E3} {r : ℝ} (hr : 0 < r) (hball : Metric.ball p (2 * r) ⊆ V) :
    IsConnected (V \ Metric.closedBall p r) := by
  have hrank : 1 < Module.rank ℝ E3 := by
    rw [← Module.finrank_eq_rank]
    simp
  have hA : IsPreconnected (Metric.ball p (2 * r) \ Metric.closedBall p r) :=
    isPreconnected_ball_sdiff_closedBall hrank p hr.le
  have hAW : Metric.ball p (2 * r) \ Metric.closedBall p r ⊆ V \ Metric.closedBall p r :=
    fun z hz => ⟨hball hz.1, hz.2⟩
  obtain ⟨u, hu⟩ := exists_norm_eq E3 zero_le_one
  have hz₀ : p + ((3 / 2) * r) • u ∈ Metric.ball p (2 * r) \ Metric.closedBall p r := by
    have hd : dist (p + ((3 / 2) * r) • u) p = (3 / 2) * r := by
      rw [dist_eq_norm, add_sub_cancel_left, norm_smul, hu, mul_one,
        Real.norm_of_nonneg (by positivity)]
    refine ⟨?_, ?_⟩
    · rw [Metric.mem_ball, hd]
      linarith
    · rw [Metric.mem_closedBall, hd, not_le]
      linarith
  refine ⟨⟨_, hAW hz₀⟩, ?_⟩
  have key : ∀ a b : Set E3, IsOpen a → IsOpen b → V \ Metric.closedBall p r ⊆ a ∪ b →
      (V \ Metric.closedBall p r) ∩ (a ∩ b) = ∅ →
      Metric.ball p (2 * r) \ Metric.closedBall p r ⊆ a → V \ Metric.closedBall p r ⊆ a := by
    intro a b ha hb hab hdis hAa
    have hV' : V ⊆ (a ∪ Metric.ball p (2 * r)) ∪ (b ∩ (Metric.closedBall p r)ᶜ) := by
      intro z hz
      by_cases hzc : z ∈ Metric.closedBall p r
      · left
        right
        rw [Metric.mem_ball]
        have := Metric.mem_closedBall.mp hzc
        linarith
      · rcases hab ⟨hz, hzc⟩ with h | h
        · exact Or.inl (Or.inl h)
        · exact Or.inr ⟨h, hzc⟩
    have hdis' : V ∩ ((a ∪ Metric.ball p (2 * r)) ∩ (b ∩ (Metric.closedBall p r)ᶜ)) = ∅ := by
      apply eq_empty_of_forall_notMem
      rintro z ⟨hzV, hza, hzb, hzc⟩
      have hzW : z ∈ V \ Metric.closedBall p r := ⟨hzV, hzc⟩
      have hzA : z ∈ a := by
        rcases hza with h | h
        · exact h
        · exact hAa ⟨h, hzc⟩
      have : z ∈ (V \ Metric.closedBall p r) ∩ (a ∩ b) := ⟨hzW, hzA, hzb⟩
      rw [hdis] at this
      exact this
    rcases isPreconnected_iff_subset_of_disjoint.mp hV.isPreconnected _ _
      (ha.union Metric.isOpen_ball) (hb.inter Metric.isClosed_closedBall.isOpen_compl) hV' hdis'
      with h | h
    · intro z hz
      rcases h hz.1 with h' | h'
      · exact h'
      · exact hAa ⟨h', hz.2⟩
    · exfalso
      have hzV := hball hz₀.1
      have hzb := (h hzV).1
      have : p + ((3 / 2) * r) • u ∈ (V \ Metric.closedBall p r) ∩ (a ∩ b) :=
        ⟨⟨hzV, hz₀.2⟩, hAa hz₀, hzb⟩
      rw [hdis] at this
      exact this
  rw [isPreconnected_iff_subset_of_disjoint]
  intro a b ha hb hab hdis
  have hAab : Metric.ball p (2 * r) \ Metric.closedBall p r ⊆ a ∪ b := hAW.trans hab
  have hAdis : (Metric.ball p (2 * r) \ Metric.closedBall p r) ∩ (a ∩ b) = ∅ :=
    subset_empty_iff.mp (hdis ▸ inter_subset_inter_left _ hAW)
  rcases isPreconnected_iff_subset_of_disjoint.mp hA a b ha hb hAab hAdis with h | h
  · exact Or.inl (key a b ha hb hab hdis h)
  · refine Or.inr (key b a hb ha (by rw [union_comm]; exact hab) ?_ h)
    rw [inter_comm b a]
    exact hdis

theorem isConnected_sdiff_biUnion_closedBall {ι : Type*} {s : Set ι} (hs : s.Finite)
    {V : Set E3} (hV : IsConnected V) (hVo : IsOpen V) (p : ι → E3) {r : ℝ} (hr : 0 < r)
    (hball : ∀ i ∈ s, Metric.ball (p i) (2 * r) ⊆ V)
    (hsep : ∀ i ∈ s, ∀ j ∈ s, i ≠ j → 3 * r ≤ dist (p i) (p j)) :
    IsConnected (V \ ⋃ i ∈ s, Metric.closedBall (p i) r) := by
  classical
  have key : ∀ t : Finset ι, (↑t : Set ι) ⊆ s →
      IsConnected (V \ ⋃ i ∈ t, Metric.closedBall (p i) r) ∧
        IsOpen (V \ ⋃ i ∈ t, Metric.closedBall (p i) r) := by
    intro t
    induction t using Finset.induction_on with
    | empty =>
      intro _
      simp only [Finset.notMem_empty, iUnion_of_empty, iUnion_empty, sdiff_empty]
      exact ⟨hV, hVo⟩
    | insert j t hj ih =>
      intro hts
      have hjs : j ∈ s := hts (Finset.mem_coe.mpr (Finset.mem_insert_self j t))
      have hts' : (↑t : Set ι) ⊆ s := fun i hi =>
        hts (Finset.mem_coe.mpr (Finset.mem_insert_of_mem (Finset.mem_coe.mp hi)))
      obtain ⟨hc, ho⟩ := ih hts'
      have heq : V \ ⋃ i ∈ insert j t, Metric.closedBall (p i) r =
          (V \ ⋃ i ∈ t, Metric.closedBall (p i) r) \ Metric.closedBall (p j) r := by
        rw [Finset.set_biUnion_insert]
        ext z
        simp only [mem_sdiff, mem_union]
        tauto
      have hsub : Metric.ball (p j) (2 * r) ⊆ V \ ⋃ i ∈ t, Metric.closedBall (p i) r := by
        intro z hz
        refine ⟨hball j hjs hz, ?_⟩
        simp only [mem_iUnion, not_exists]
        intro i hi hzi
        have hij : i ≠ j := fun h => hj (h ▸ hi)
        have h3 := hsep i (hts' (Finset.mem_coe.mpr hi)) j hjs hij
        have h1 := Metric.mem_closedBall.mp hzi
        have h2 := Metric.mem_ball.mp hz
        have := dist_triangle (p i) z (p j)
        rw [dist_comm (p i) z] at this
        linarith
      rw [heq]
      exact ⟨isConnected_sdiff_closedBall_of_ball_subset hc hr hsub,
        ho.sdiff Metric.isClosed_closedBall⟩
  have h := (key hs.toFinset (by simp)).1
  simpa only [Set.Finite.mem_toFinset] using h

end DifferentialGeometry.Topology.PiecewiseLinear
