/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.BicollaredComplement
import DifferentialGeometry.Topology.PiecewiseLinear.BoundaryMatchMobius

open Set

namespace DifferentialGeometry.Topology.PiecewiseLinear

local notation "E3" => EuclideanSpace ℝ (Fin 3)

theorem isConnected_interior_space_and_compl {XK : Geometry.SimplicialComplex ℝ E3}
    (hfin : XK.faces.Finite) (hX : IsCombinatorialManifoldWithBoundary 3 XK)
    (hc : IsConnected (frontier XK.space)) (hint : (interior XK.space).Nonempty) :
    IsConnected (interior XK.space) ∧ IsConnected XK.spaceᶜ ∧
      frontier XK.space ⊆ closure (interior XK.space) := by
  classical
  let _ : Finite XK.faces := hfin.to_subtype
  let BX := @boundaryComplex _ _ _ (Classical.decEq _) (2 + 1) XK
  have hFr : frontier XK.space = BX.space := frontier_space_eq_boundaryComplex_space hX
  let _ : Finite BX.faces := ((Set.toFinite XK.faces).subset fun _ hs => hs.1).to_subtype
  have hBman : IsCombinatorialManifold 2 BX := isCombinatorialManifold_boundaryComplex XK hX
  have hconnB : IsConnected BX.space := hFr ▸ hc
  obtain ⟨a, ha, b, hb, hdis, hunion, -, -, hfa, hfb⟩ :=
    hBman.exists_connectedComponentIn_pair_compl BX finrank_euclideanSpace_fin hconnB
  rw [← hFr] at ha hb hdis hunion hfa hfb
  have hXc : IsClosed XK.space := (isPolyhedron_space XK).isClosed
  have hcomp : (frontier XK.space)ᶜ = interior XK.space ∪ XK.spaceᶜ :=
    compl_frontier_eq_interior_union_compl hXc
  have hXcne : XK.spaceᶜ.Nonempty := by
    by_contra hne
    rw [not_nonempty_iff_eq_empty, compl_empty_iff] at hne
    exact NormedSpace.unbounded_univ ℝ E3 (hne ▸ (isPolyhedron_space XK).isCompact.isBounded)
  have hdisj : Disjoint (interior XK.space) XK.spaceᶜ :=
    disjoint_compl_right.mono_left interior_subset
  have hsplit : ∀ c : E3, connectedComponentIn (frontier XK.space)ᶜ c ⊆ interior XK.space ∨
      connectedComponentIn (frontier XK.space)ᶜ c ⊆ XK.spaceᶜ := fun c =>
    isPreconnected_connectedComponentIn.subset_or_subset isOpen_interior hXc.isOpen_compl hdisj
      ((connectedComponentIn_subset _ _).trans hcomp.subset)
  have hkey : ∀ c ∈ (frontier XK.space)ᶜ, ∀ d ∈ (frontier XK.space)ᶜ,
      connectedComponentIn (frontier XK.space)ᶜ c ∪ connectedComponentIn (frontier XK.space)ᶜ d =
        (frontier XK.space)ᶜ →
      frontier (connectedComponentIn (frontier XK.space)ᶜ c) = frontier XK.space →
      connectedComponentIn (frontier XK.space)ᶜ c ⊆ interior XK.space →
      connectedComponentIn (frontier XK.space)ᶜ d ⊆ XK.spaceᶜ →
      IsConnected (interior XK.space) ∧ IsConnected XK.spaceᶜ ∧
        frontier XK.space ⊆ closure (interior XK.space) := by
    intro c hc d hd hcd hfc hcI hdX
    have hI : interior XK.space = connectedComponentIn (frontier XK.space)ᶜ c := by
      refine Subset.antisymm (fun y hy => ?_) hcI
      have hyS : y ∈ (frontier XK.space)ᶜ := by
        rw [hcomp]
        exact Or.inl hy
      rw [← hcd] at hyS
      exact hyS.resolve_right fun h => disjoint_left.mp hdisj hy (hdX h)
    have hXcomp : XK.spaceᶜ = connectedComponentIn (frontier XK.space)ᶜ d := by
      refine Subset.antisymm (fun y hy => ?_) hdX
      have hyS : y ∈ (frontier XK.space)ᶜ := by
        rw [hcomp]
        exact Or.inr hy
      rw [← hcd] at hyS
      exact hyS.resolve_left fun h => disjoint_left.mp hdisj (hcI h) hy
    refine ⟨hI ▸ isConnected_connectedComponentIn_iff.mpr hc,
      hXcomp ▸ isConnected_connectedComponentIn_iff.mpr hd, ?_⟩
    exact hfc.symm.subset.trans (frontier_subset_closure.trans (closure_mono hcI))
  rcases hsplit a with haI | haX <;> rcases hsplit b with hbI | hbX
  · exfalso
    obtain ⟨z, hz⟩ := hXcne
    have hzS : z ∈ (frontier XK.space)ᶜ := by
      rw [hcomp]
      exact Or.inr hz
    rw [← hunion] at hzS
    rcases hzS with h | h
    · exact hz (interior_subset (haI h))
    · exact hz (interior_subset (hbI h))
  · exact hkey a ha b hb hunion hfa haI hbX
  · exact hkey b hb a ha (by rw [union_comm]; exact hunion) hfb hbI haX
  · exfalso
    obtain ⟨z, hz⟩ := hint
    have hzS : z ∈ (frontier XK.space)ᶜ := by
      rw [hcomp]
      exact Or.inl hz
    rw [← hunion] at hzS
    rcases hzS with h | h
    · exact haX h (interior_subset hz)
    · exact hbX h (interior_subset hz)

theorem closure_subset_of_frontier_subset_of_isConnected_compl {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [Nontrivial E] {X D : Set E}
    (hX : Bornology.IsBounded X) (hXc : IsConnected Xᶜ) (hD : Bornology.IsBounded D)
    (hfr : frontier D ⊆ X) : closure D ⊆ X := by
  have hsub : Xᶜ ⊆ interior D ∪ (closure D)ᶜ := by
    intro z hz
    by_cases hzD : z ∈ closure D
    · left
      by_contra hzi
      exact hz (hfr ⟨hzD, hzi⟩)
    · exact Or.inr hzD
  have hdisj : Disjoint (interior D) (closure D)ᶜ :=
    disjoint_compl_right.mono_left (interior_subset.trans subset_closure)
  rcases hXc.isPreconnected.subset_or_subset isOpen_interior isClosed_closure.isOpen_compl hdisj
    hsub with h | h
  · exfalso
    have hcov : (univ : Set E) ⊆ X ∪ D := fun z _ => by
      by_cases hz : z ∈ X
      · exact Or.inl hz
      · exact Or.inr (interior_subset (h hz))
    exact NormedSpace.unbounded_univ ℝ E ((hX.union hD).subset hcov)
  · intro z hz
    by_contra hzX
    exact h hzX hz

theorem IsCompact.exists_mem_frontier_dist_le_dist {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [Nontrivial E] {B : Set E} (hB : IsCompact B) {x : E} (hx : x ∈ B)
    (y : E) : ∃ z ∈ frontier B, dist x y ≤ dist z y := by
  obtain ⟨u, hu, c, hc, hxy⟩ : ∃ u : E, u ≠ 0 ∧ ∃ c : ℝ, 0 ≤ c ∧ x - y = c • u := by
    by_cases h : x = y
    · obtain ⟨u, hu⟩ := exists_ne (0 : E)
      exact ⟨u, hu, 0, le_rfl, by rw [h, sub_self, zero_smul]⟩
    · exact ⟨x - y, sub_ne_zero.mpr h, 1, zero_le_one, (one_smul ℝ _).symm⟩
  have hpos : 0 < ‖u‖ := norm_pos_iff.mpr hu
  obtain ⟨R, hR⟩ := hB.isBounded.exists_norm_le
  have hTsub : {t : ℝ | 0 ≤ t ∧ x + t • u ∈ B} ⊆ Icc 0 ((R + ‖x‖) / ‖u‖) := by
    rintro t ⟨ht0, htB⟩
    refine ⟨ht0, ?_⟩
    rw [le_div_iff₀ hpos]
    have h1 := hR _ htB
    have h2 : ‖t • u‖ ≤ ‖x + t • u‖ + ‖x‖ := by
      calc ‖t • u‖ = ‖(x + t • u) - x‖ := by rw [add_sub_cancel_left]
        _ ≤ ‖x + t • u‖ + ‖x‖ := norm_sub_le _ _
    rw [norm_smul, Real.norm_of_nonneg ht0] at h2
    linarith
  have hTc : IsCompact {t : ℝ | 0 ≤ t ∧ x + t • u ∈ B} := by
    refine isCompact_Icc.of_isClosed_subset ?_ hTsub
    exact isClosed_Ici.inter (hB.isClosed.preimage (by fun_prop))
  obtain ⟨t, ⟨ht0, htB⟩, htmax⟩ := hTc.exists_isGreatest ⟨0, le_rfl, by simpa using hx⟩
  refine ⟨x + t • u, ⟨subset_closure htB, fun hint => ?_⟩, ?_⟩
  · obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp isOpen_interior _ hint
    have hs : 0 < ε / (2 * ‖u‖) := by positivity
    have hdiff : x + (t + ε / (2 * ‖u‖)) • u - (x + t • u) = (ε / (2 * ‖u‖)) • u := by
      rw [add_smul]
      abel
    have hmem : x + (t + ε / (2 * ‖u‖)) • u ∈ B := by
      apply interior_subset
      apply hball
      rw [Metric.mem_ball, dist_eq_norm, hdiff, norm_smul, Real.norm_of_nonneg hs.le,
        div_mul_eq_mul_div, mul_div_mul_right _ _ hpos.ne']
      linarith
    have hle := htmax ⟨by linarith, hmem⟩
    linarith
  · have hzy : x + t • u - y = (c + t) • u := by
      rw [add_smul, ← hxy]
      abel
    rw [dist_eq_norm, dist_eq_norm, hxy, hzy, norm_smul, norm_smul, Real.norm_of_nonneg hc,
      Real.norm_of_nonneg (by linarith)]
    nlinarith [norm_nonneg u]

theorem IsCompact.exists_mem_frontier_pair_dist_le {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [Nontrivial E] {B : Set E} (hB : IsCompact B) {x y : E} (hx : x ∈ B)
    (hy : y ∈ B) : ∃ z ∈ frontier B, ∃ z' ∈ frontier B, dist x y ≤ dist z z' := by
  obtain ⟨z, hz, hxz⟩ := IsCompact.exists_mem_frontier_dist_le_dist hB hx y
  obtain ⟨z', hz', hyz⟩ := IsCompact.exists_mem_frontier_dist_le_dist hB hy z
  exact ⟨z', hz', z, hz, hxz.trans ((dist_comm z y).le.trans hyz)⟩

end DifferentialGeometry.Topology.PiecewiseLinear
