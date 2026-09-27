/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.FourSpokeDisk

open Set

namespace DifferentialGeometry.Topology.PiecewiseLinear

open Schoenflies

theorem isPLBall_closure_inside_arc_union {D P B₁ B₂ : Set Plane} {p q : Plane}
    (hD : IsPLBall 2 D) (hP : IsPLBall 1 P) (hcross : IsCrosscut (frontier D) P p q)
    (hcut : IsCutPair (frontier D) p q B₁ B₂) :
    IsPLBall 2 (closure (inside (B₁ ∪ P))) ∧
      frontier (closure (inside (B₁ ∪ P))) = B₁ ∪ P := by
  have h := isPLSphere_one_union_of_isCrosscut hD.isPLSphere_frontier hP hcross hcut
  exact ⟨isPLBall_closure_inside_of_isPLSphere_one h,
    frontier_closure_inside_of_isPLSphere_one h⟩

theorem closure_inside_arc_union_union_and_inter {D P B₁ B₂ : Set Plane} {p q : Plane}
    (hD : IsPLBall 2 D) (hcross : IsCrosscut (frontier D) P p q)
    (hcut : IsCutPair (frontier D) p q B₁ B₂) :
    closure (inside (B₁ ∪ P)) ∪ closure (inside (B₂ ∪ P)) = D ∧
      closure (inside (B₁ ∪ P)) ∩ closure (inside (B₂ ∪ P)) = P := by
  refine ⟨?_, PlanarJordan.closure_inside_inter_of_isCrosscut hcross hcut⟩
  rw [PlanarJordan.closure_inside_union_of_isCrosscut hcross hcut,
    ← hD.interior_eq_inside_frontier]
  exact hD.closure_interior

theorem exists_isPLHomeomorphOn_sector_of_isCrosscut
    {D P B₁ B₂ D' P' B₁' B₂' : Set Plane} {p q p' q' : Plane}
    (hD : IsPLBall 2 D) (hP : IsPLBall 1 P) (hcross : IsCrosscut (frontier D) P p q)
    (hcut : IsCutPair (frontier D) p q B₁ B₂)
    (hD' : IsPLBall 2 D') (hP' : IsPLBall 1 P') (hcross' : IsCrosscut (frontier D') P' p' q')
    (hcut' : IsCutPair (frontier D') p' q' B₁' B₂')
    {h : Plane → Plane} (hh : IsPLHomeomorphOn h (B₁ ∪ P) (B₁' ∪ P')) :
    ∃ H : Plane → Plane,
      IsPLHomeomorphOn H (closure (inside (B₁ ∪ P))) (closure (inside (B₁' ∪ P'))) ∧
        EqOn H h (B₁ ∪ P) := by
  obtain ⟨hS, hfr⟩ := isPLBall_closure_inside_arc_union hD hP hcross hcut
  obtain ⟨hS', hfr'⟩ := isPLBall_closure_inside_arc_union hD' hP' hcross' hcut'
  obtain ⟨H, hH, hHh⟩ := exists_isPLHomeomorphOn_of_frontier (n := 1) hS hS'
    (by rw [hfr, hfr']; exact hh)
  exact ⟨H, hH, by rwa [hfr] at hHh⟩

theorem exists_isPLBall_sectors_of_fourSpokeDisk
    {D A₁ A₂ : Set Plane} {c : Plane} {T : Fin 4 → Set Plane} {v : Fin 4 → Plane}
    (hD : IsPLBall 2 D) (hT : ∀ i, IsPLBall 1 (T i))
    (harc : ∀ i, IsArcBetween (T i) c (v i)) (hTD : ∀ i, T i ⊆ D)
    (hTf : ∀ i, T i ∩ frontier D = {v i}) (hTT : ∀ i j, i ≠ j → T i ∩ T j = {c})
    (hcut : IsCutPair (frontier D) (v 0) (v 2) A₁ A₂) (hv1 : v 1 ∈ A₁) (hv3 : v 3 ∈ A₂) :
    ∃ S₀ S₁ S₂ S₃ : Set Plane,
      IsPLBall 2 S₀ ∧ IsPLBall 2 S₁ ∧ IsPLBall 2 S₂ ∧ IsPLBall 2 S₃ ∧
      S₀ ∪ S₁ ∪ (S₂ ∪ S₃) = D ∧ S₀ ∩ S₁ = T 1 ∧ S₂ ∩ S₃ = T 3 ∧
      (S₀ ∪ S₁) ∩ (S₂ ∪ S₃) = T 0 ∪ T 2 ∧
      frontier S₀ ∪ frontier S₁ ∪ (frontier S₂ ∪ frontier S₃) ⊆
        frontier D ∪ (T 0 ∪ T 1 ∪ (T 2 ∪ T 3)) := by
  classical
  have hvne : ∀ i j : Fin 4, i ≠ j → v i ≠ v j := by
    intro i j hij h
    have hmem : v i ∈ T i ∩ T j := ⟨(harc i).right_mem, by rw [h]; exact (harc j).right_mem⟩
    rw [hTT i j hij] at hmem
    exact ne_of_isArcBetween (harc i) (mem_singleton_iff.mp hmem).symm
  obtain ⟨hAball, hcrossA⟩ := isCrosscut_union_of_opposite_spokes hD (hT 0) (hT 2)
    (harc 0) (harc 2) (hTD 0) (hTD 2) (hTf 0) (hTf 2) (hTT 0 2 (by decide))
  have hcA : c ∈ T 0 ∪ T 2 := Or.inl (harc 0).left_mem
  have hcross₁ : IsCrosscut (A₁ ∪ (T 0 ∪ T 2)) (T 1) c (v 1) :=
    isCrosscut_spoke_of_isCutPair hD (hT 1) hAball (harc 1) (hTD 1) (hTf 1)
      (hTT 1 0 (by decide)) (hTT 1 2 (by decide)) hcA hcrossA hcut hv1
      (hvne 1 0 (by decide)) (hvne 1 2 (by decide))
  have hcross₃ : IsCrosscut (A₂ ∪ (T 0 ∪ T 2)) (T 3) c (v 3) :=
    isCrosscut_spoke_of_isCutPair hD (hT 3) hAball (harc 3) (hTD 3) (hTf 3)
      (hTT 3 0 (by decide)) (hTT 3 2 (by decide)) hcA hcrossA hcut.symm hv3
      (hvne 3 0 (by decide)) (hvne 3 2 (by decide))
  obtain ⟨hD₁, hfr₁⟩ := isPLBall_closure_inside_arc_union hD hAball hcrossA hcut
  obtain ⟨hD₂, hfr₂⟩ := isPLBall_closure_inside_arc_union hD hAball hcrossA hcut.symm
  obtain ⟨hDun, hDin⟩ := closure_inside_arc_union_union_and_inter hD hcrossA hcut
  have hcross₁D : IsCrosscut (frontier (closure (inside (A₁ ∪ (T 0 ∪ T 2))))) (T 1) c (v 1) := by
    rw [hfr₁]; exact hcross₁
  have hcross₃D : IsCrosscut (frontier (closure (inside (A₂ ∪ (T 0 ∪ T 2))))) (T 3) c (v 3) := by
    rw [hfr₂]; exact hcross₃
  have hcD₁ : c ∈ frontier (closure (inside (A₁ ∪ (T 0 ∪ T 2)))) := by
    rw [hfr₁]; exact Or.inr hcA
  have hv1D₁ : v 1 ∈ frontier (closure (inside (A₁ ∪ (T 0 ∪ T 2)))) := by
    rw [hfr₁]; exact Or.inl hv1
  have hcD₂ : c ∈ frontier (closure (inside (A₂ ∪ (T 0 ∪ T 2)))) := by
    rw [hfr₂]; exact Or.inr hcA
  have hv3D₂ : v 3 ∈ frontier (closure (inside (A₂ ∪ (T 0 ∪ T 2)))) := by
    rw [hfr₂]; exact Or.inl hv3
  obtain ⟨B₀, B₁, hcutB, -, -⟩ := exists_isCutPair_isPLBall_of_isPLSphere_one
    hD₁.isPLSphere_frontier hcD₁ hv1D₁ (ne_of_isArcBetween (harc 1))
  obtain ⟨B₂, B₃, hcutB', -, -⟩ := exists_isCutPair_isPLBall_of_isPLSphere_one
    hD₂.isPLSphere_frontier hcD₂ hv3D₂ (ne_of_isArcBetween (harc 3))
  have hB₀ : B₀ ⊆ A₁ ∪ (T 0 ∪ T 2) := by rw [← hfr₁]; exact hcutB.fst_subset
  have hB₁ : B₁ ⊆ A₁ ∪ (T 0 ∪ T 2) := by rw [← hfr₁]; exact hcutB.snd_subset
  have hB₂ : B₂ ⊆ A₂ ∪ (T 0 ∪ T 2) := by rw [← hfr₂]; exact hcutB'.fst_subset
  have hB₃ : B₃ ⊆ A₂ ∪ (T 0 ∪ T 2) := by rw [← hfr₂]; exact hcutB'.snd_subset
  obtain ⟨hS₀, hfrS₀⟩ := isPLBall_closure_inside_arc_union hD₁ (hT 1) hcross₁D hcutB
  obtain ⟨hS₁, hfrS₁⟩ := isPLBall_closure_inside_arc_union hD₁ (hT 1) hcross₁D hcutB.symm
  obtain ⟨hS₂, hfrS₂⟩ := isPLBall_closure_inside_arc_union hD₂ (hT 3) hcross₃D hcutB'
  obtain ⟨hS₃, hfrS₃⟩ := isPLBall_closure_inside_arc_union hD₂ (hT 3) hcross₃D hcutB'.symm
  obtain ⟨hun₁, hin₁⟩ := closure_inside_arc_union_union_and_inter hD₁ hcross₁D hcutB
  obtain ⟨hun₂, hin₂⟩ := closure_inside_arc_union_union_and_inter hD₂ hcross₃D hcutB'
  refine ⟨_, _, _, _, hS₀, hS₁, hS₂, hS₃, by rw [hun₁, hun₂, hDun], hin₁, hin₂,
    by rw [hun₁, hun₂, hDin], ?_⟩
  have harcs : ∀ B : Set Plane, B ⊆ A₁ ∪ (T 0 ∪ T 2) ∨ B ⊆ A₂ ∪ (T 0 ∪ T 2) →
      ∀ (S : Set Plane), S = B ∪ T 1 ∨ S = B ∪ T 3 →
      S ⊆ frontier D ∪ (T 0 ∪ T 1 ∪ (T 2 ∪ T 3)) := by
    rintro B hB S (rfl | rfl) x (hx | hx)
    · rcases hB with hB | hB
      · rcases hB hx with h | h | h
        · exact Or.inl (hcut.fst_subset h)
        · exact Or.inr (Or.inl (Or.inl h))
        · exact Or.inr (Or.inr (Or.inl h))
      · rcases hB hx with h | h | h
        · exact Or.inl (hcut.snd_subset h)
        · exact Or.inr (Or.inl (Or.inl h))
        · exact Or.inr (Or.inr (Or.inl h))
    · exact Or.inr (Or.inl (Or.inr hx))
    · rcases hB with hB | hB
      · rcases hB hx with h | h | h
        · exact Or.inl (hcut.fst_subset h)
        · exact Or.inr (Or.inl (Or.inl h))
        · exact Or.inr (Or.inr (Or.inl h))
      · rcases hB hx with h | h | h
        · exact Or.inl (hcut.snd_subset h)
        · exact Or.inr (Or.inl (Or.inl h))
        · exact Or.inr (Or.inr (Or.inl h))
    · exact Or.inr (Or.inr (Or.inr hx))
  rw [hfrS₀, hfrS₁, hfrS₂, hfrS₃]
  refine union_subset (union_subset ?_ ?_) (union_subset ?_ ?_)
  · exact harcs B₀ (Or.inl hB₀) _ (Or.inl rfl)
  · exact harcs B₁ (Or.inl hB₁) _ (Or.inl rfl)
  · exact harcs B₂ (Or.inr hB₂) _ (Or.inr rfl)
  · exact harcs B₃ (Or.inr hB₃) _ (Or.inr rfl)

end DifferentialGeometry.Topology.PiecewiseLinear
