/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.PLSchoenflies
import DifferentialGeometry.Topology.PiecewiseLinear.SurfaceComplement

open Set

namespace DifferentialGeometry.Topology.PiecewiseLinear

open Classical in
theorem IsPLSphere.exists_isPLBall_complement_components
    {B : Set (EuclideanSpace ℝ (Fin 3))} (hB : IsPLSphere 2 B) :
    ∃ D : Set (EuclideanSpace ℝ (Fin 3)),
      IsPLBall 3 D ∧ frontier D = B ∧ Bornology.IsBounded D ∧
      Bᶜ = interior D ∪ Dᶜ ∧ Disjoint (interior D) Dᶜ ∧
      IsConnected (interior D) ∧ IsConnected Dᶜ ∧ ¬ Bornology.IsBounded Dᶜ := by
  classical
  obtain ⟨D, hD, hfront, hbounded⟩ := hB.exists_isPLBall_frontier_eq
  have hDclosed : IsClosed D := hD.isPolyhedron.isCompact.isClosed
  have hunion : Bᶜ = interior D ∪ Dᶜ := by
    rw [← hfront, hDclosed.frontier_eq]
    ext x
    constructor
    · intro hx
      by_cases hxD : x ∈ D
      · exact Or.inl (by by_contra hni; exact hx ⟨hxD, hni⟩)
      · exact Or.inr hxD
    · rintro (hx | hx) h
      · exact h.2 hx
      · exact hx h.1
  have hdisj : Disjoint (interior D) Dᶜ := disjoint_compl_right.mono_left interior_subset
  have hintOpen : IsOpen (interior D) := isOpen_interior
  have hcompOpen : IsOpen Dᶜ := hDclosed.isOpen_compl
  have hintNe : (interior D).Nonempty := hD.interior_nonempty
  have hunb : ¬ Bornology.IsBounded (univ : Set (EuclideanSpace ℝ (Fin 3))) :=
    NormedSpace.unbounded_univ ℝ _
  have hcompNe : (Dᶜ).Nonempty := by
    by_contra h
    rw [not_nonempty_iff_eq_empty, compl_empty_iff] at h
    exact hunb (h ▸ hbounded)
  obtain ⟨L, hfin, hspace⟩ := hB.isPolyhedron.exists_simplicialComplex
  let _ : Finite L.faces := hfin.to_subtype
  have hLsphere : IsPLSphere 2 L.space := by rw [hspace]; exact hB
  have hLman : IsCombinatorialManifold 2 L := IsPLSphere.isCombinatorialManifold (n := 1) hLsphere
  have hconnL : IsConnected L.space := by rw [hspace]; exact hB.isConnected
  have hdim : Module.finrank ℝ (EuclideanSpace ℝ (Fin 3)) = 3 := by simp
  obtain ⟨a, ha, b, hb, hdisjAB, hcoverAB, -, -, -, -⟩ :=
    IsCombinatorialManifold.exists_connectedComponentIn_pair_compl L hLman hdim hconnL
  rw [hspace] at ha hb hdisjAB hcoverAB
  set A := connectedComponentIn Bᶜ a with hA
  set A' := connectedComponentIn Bᶜ b with hA'
  have hAconn : IsConnected A := isConnected_connectedComponentIn_iff.mpr ha
  have hA'conn : IsConnected A' := isConnected_connectedComponentIn_iff.mpr hb
  have hAsub : A ⊆ interior D ∪ Dᶜ := by
    rw [← hunion]; exact hA ▸ connectedComponentIn_subset _ _
  have hA'sub : A' ⊆ interior D ∪ Dᶜ := by
    rw [← hunion]; exact hA' ▸ connectedComponentIn_subset _ _
  have hAcase := hAconn.isPreconnected.subset_or_subset hintOpen hcompOpen hdisj hAsub
  have hA'case := hA'conn.isPreconnected.subset_or_subset hintOpen hcompOpen hdisj hA'sub
  have hmem : ∀ x, x ∈ interior D ∪ Dᶜ ↔ x ∈ A ∪ A' := by
    intro x; rw [← hunion, ← hcoverAB]
  have key : interior D = A ∧ Dᶜ = A' ∨ interior D = A' ∧ Dᶜ = A := by
    rcases hAcase with hA1 | hA1 <;> rcases hA'case with hA2 | hA2
    · obtain ⟨x, hx⟩ := hcompNe
      rcases (hmem x).mp (Or.inr hx) with h | h
      · exact absurd (interior_subset (hA1 h)) hx
      · exact absurd (interior_subset (hA2 h)) hx
    · left
      refine ⟨subset_antisymm (fun x hx => ?_) hA1, subset_antisymm (fun x hx => ?_) hA2⟩
      · rcases (hmem x).mp (Or.inl hx) with h | h
        · exact h
        · exact absurd (interior_subset hx) (hA2 h)
      · rcases (hmem x).mp (Or.inr hx) with h | h
        · exact absurd (interior_subset (hA1 h)) hx
        · exact h
    · right
      refine ⟨subset_antisymm (fun x hx => ?_) hA2, subset_antisymm (fun x hx => ?_) hA1⟩
      · rcases (hmem x).mp (Or.inl hx) with h | h
        · exact absurd (interior_subset hx) (hA1 h)
        · exact h
      · rcases (hmem x).mp (Or.inr hx) with h | h
        · exact h
        · exact absurd (interior_subset (hA2 h)) hx
    · obtain ⟨x, hx⟩ := hintNe
      rcases (hmem x).mp (Or.inl hx) with h | h
      · exact absurd (interior_subset hx) (hA1 h)
      · exact absurd (interior_subset hx) (hA2 h)
  have hcompUnbounded : ¬ Bornology.IsBounded Dᶜ := by
    intro h
    exact hunb (by simpa using hbounded.union h)
  rcases key with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · exact ⟨D, hD, hfront, hbounded, hunion, hdisj, h1 ▸ hAconn, h2 ▸ hA'conn, hcompUnbounded⟩
  · exact ⟨D, hD, hfront, hbounded, hunion, hdisj, h1 ▸ hA'conn, h2 ▸ hAconn, hcompUnbounded⟩

end DifferentialGeometry.Topology.PiecewiseLinear
