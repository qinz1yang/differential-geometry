import DifferentialGeometry.Topology.JordanCurve
import DifferentialGeometry.External.Schoenflies.JordanClosed
import Mathlib.Order.Preorder.Finite

open Set

namespace Schoenflies

private theorem inside_ssubset_of_subset_inside
    {C J : Set Plane} (hC : IsSeparating C) (hJ : IsSeparating J)
    (hJC : J ⊆ inside C) : inside J ⊂ inside C := by
  have hCJ : Disjoint C J := Set.disjoint_left.2 fun _ hzC hzJ =>
    inside_subset_compl (hJC hzJ) hzC
  have hdis : Disjoint (outside C) J := disjoint_inside_outside.symm.mono_right hJC
  obtain ⟨W, V, hWV, hout⟩ := hJ.exists_isRegionPair_subset
    hC.isConnected_outside.isPreconnected hC.isConnected_outside.nonempty hdis
  rcases hWV with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · exact (hC.not_isBounded_outside (hJ.isBounded_inside.subset hout)).elim
  · have hCout : C ⊆ outside J := by
      intro z hz
      exact hC.absorption hJ (Or.inr rfl) (Or.inr rfl) hout
        ⟨hz, Set.disjoint_left.1 hCJ hz⟩
    have hinsub : inside J ⊆ inside C := by
      intro z hz
      have hzC : z ∉ C := fun h =>
        Set.disjoint_left.1 disjoint_inside_outside hz (hCout h)
      have hzcover : z ∈ inside C ∪ outside C := by
        rwa [inside_union_outside]
      exact hzcover.resolve_right fun h =>
        Set.disjoint_left.1 disjoint_inside_outside hz (hout h)
    refine (ssubset_iff_subset_ne).2 ⟨hinsub, ?_⟩
    intro h
    obtain ⟨z, hz⟩ := hJ.isJordanCurve.nonempty
    have hz' : z ∈ inside J := by
      rw [h]
      exact hJC hz
    exact inside_subset_compl hz' hz

theorem exists_innermost_jordan_curve (curves : Finset (Set Plane))
    (hne : curves.Nonempty) (hcurves : ∀ C ∈ curves, IsJordanCurve C)
    (hdisjoint : (curves : Set (Set Plane)).Pairwise Disjoint) :
    ∃ C ∈ curves, ∀ J ∈ curves, Disjoint (inside C) J := by
  classical
  obtain ⟨C, hmin⟩ := curves.exists_minimalFor inside hne
  have hC := jordan_curve_theorem (hcurves C hmin.1)
  refine ⟨C, hmin.1, ?_⟩
  intro J hJmem
  by_cases hJC : J = C
  · subst J
    exact Set.disjoint_left.2 fun _ hx hxc => inside_subset_compl hx hxc
  by_contra hmeet
  have hJ := jordan_curve_theorem (hcurves J hJmem)
  obtain ⟨W, V, hWV, hsub⟩ := hC.exists_isRegionPair_subset
    hJ.isJordanCurve.isConnected.isPreconnected hJ.isJordanCurve.nonempty
    (hdisjoint hJmem hmin.1 hJC)
  rcases hWV with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · have hproper := inside_ssubset_of_subset_inside hC hJ hsub
    exact hproper.not_ge (hmin.2 hJmem hproper.le)
  · exact hmeet (disjoint_inside_outside.mono_right hsub)

theorem IsSeparating.local_side_sign
    {C U : Set Plane} (hC : IsSeparating C) (hU : IsOpen U) {a : Plane}
    (haC : a ∈ C) (haU : a ∈ U) (g : Plane → ℝ)
    (hzero : ∀ p ∈ U, p ∈ C ↔ g p = 0)
    (hpos : IsPreconnected (U ∩ {p | 0 < g p}))
    (hneg : IsPreconnected (U ∩ {p | g p < 0})) :
    (∀ p ∈ U, p ∈ inside C ↔ 0 < g p) ∨
      (∀ p ∈ U, p ∈ inside C ↔ g p < 0) := by
  have hcover : ∀ p ∈ U, g p ≠ 0 → p ∈ inside C ∪ outside C := by
    intro p hp hne
    rw [inside_union_outside]
    exact fun hpC => hne ((hzero p hp).mp hpC)
  have hsplitpos : U ∩ {p | 0 < g p} ⊆ inside C ∨
      U ∩ {p | 0 < g p} ⊆ outside C :=
    hpos.subset_or_subset hC.isOpen_inside hC.isOpen_outside disjoint_inside_outside
      (fun p hp => hcover p hp.1 hp.2.ne')
  have hsplitneg : U ∩ {p | g p < 0} ⊆ inside C ∨
      U ∩ {p | g p < 0} ⊆ outside C :=
    hneg.subset_or_subset hC.isOpen_inside hC.isOpen_outside disjoint_inside_outside
      (fun p hp => hcover p hp.1 hp.2.ne)
  have hi : (U ∩ inside C).Nonempty := by
    have ha : a ∈ closure (inside C) := (IsRegionOf.inside C).subset_closure hC haC
    exact (mem_closure_iff.mp ha U hU haU)
  have ho : (U ∩ outside C).Nonempty := by
    have ha : a ∈ closure (outside C) := (IsRegionOf.outside C).subset_closure hC haC
    exact (mem_closure_iff.mp ha U hU haU)
  have hsign : ∀ p ∈ U, p ∉ C → g p < 0 ∨ 0 < g p := by
    intro p hp hpC
    exact lt_or_gt_of_ne (fun he => hpC ((hzero p hp).mpr he))
  rcases hsplitpos with hpi | hpo <;> rcases hsplitneg with hni | hno
  · obtain ⟨p, hpU, hpO⟩ := ho
    rcases hsign p hpU hpO.1 with hn | hp
    · exact False.elim (Set.disjoint_left.mp disjoint_inside_outside (hni ⟨hpU, hn⟩) hpO)
    · exact False.elim (Set.disjoint_left.mp disjoint_inside_outside (hpi ⟨hpU, hp⟩) hpO)
  · refine Or.inl fun p hpU => ⟨?_, fun hp => hpi ⟨hpU, hp⟩⟩
    intro hpI
    rcases hsign p hpU hpI.1 with hn | hp
    · exact False.elim (Set.disjoint_left.mp disjoint_inside_outside hpI (hno ⟨hpU, hn⟩))
    · exact hp
  · refine Or.inr fun p hpU => ⟨?_, fun hp => hni ⟨hpU, hp⟩⟩
    intro hpI
    rcases hsign p hpU hpI.1 with hn | hp
    · exact hn
    · exact False.elim (Set.disjoint_left.mp disjoint_inside_outside hpI (hpo ⟨hpU, hp⟩))
  · obtain ⟨p, hpU, hpI⟩ := hi
    rcases hsign p hpU hpI.1 with hn | hp
    · exact False.elim (Set.disjoint_left.mp disjoint_inside_outside hpI (hno ⟨hpU, hn⟩))
    · exact False.elim (Set.disjoint_left.mp disjoint_inside_outside hpI (hpo ⟨hpU, hp⟩))

end Schoenflies
