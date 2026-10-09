/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.FourSpokeSector

open Set

namespace DifferentialGeometry.Topology.PiecewiseLinear

open Schoenflies

theorem isCutPair_spoke_arc_union {D A T₀ T₂ β₀ β₂ : Set Plane} {c z v₀ v₂ : Plane}
    (harc0 : IsArcBetween T₀ c v₀) (harc2 : IsArcBetween T₂ c v₂)
    (hTf0 : T₀ ∩ frontier D = {v₀}) (hTf2 : T₂ ∩ frontier D = {v₂})
    (hTT : T₀ ∩ T₂ = {c}) (hb0 : IsArcBetween β₀ v₀ z) (hb2 : IsArcBetween β₂ z v₂)
    (hbun : β₀ ∪ β₂ = A) (hbin : β₀ ∩ β₂ = {z}) (hA : A ⊆ frontier D) :
    IsCutPair (A ∪ (T₀ ∪ T₂)) c z (T₀ ∪ β₀) (T₂ ∪ β₂) := by
  have hb0A : β₀ ⊆ A := hbun ▸ subset_union_left
  have hb2A : β₂ ⊆ A := hbun ▸ subset_union_right
  have hzv0 : v₀ ≠ z := ne_of_isArcBetween hb0
  have hzv2 : z ≠ v₂ := ne_of_isArcBetween hb2
  have h0 : ∀ x ∈ T₀, x ∈ β₀ → x = v₀ :=
    fun x hx hx' => hTf0.subset ⟨hx, hA (hb0A hx')⟩
  have h2 : ∀ x ∈ T₂, x ∈ β₂ → x = v₂ :=
    fun x hx hx' => hTf2.subset ⟨hx, hA (hb2A hx')⟩
  have h02 : T₀ ∩ β₂ = ∅ := by
    refine eq_empty_of_subset_empty fun x hx => ?_
    have hxv : x = v₀ := hTf0.subset ⟨hx.1, hA (hb2A hx.2)⟩
    subst hxv
    exact absurd (hbin.subset ⟨hb0.left_mem, hx.2⟩) hzv0
  have h20 : β₀ ∩ T₂ = ∅ := by
    refine eq_empty_of_subset_empty fun x hx => ?_
    have hxv : x = v₂ := hTf2.subset ⟨hx.2, hA (hb0A hx.1)⟩
    subst hxv
    exact absurd (hbin.subset ⟨hx.1, hb2.right_mem⟩) hzv2.symm
  refine ⟨harc0.concatenate hb0 h0, harc2.concatenate hb2.reverse h2, ?_, ?_⟩
  · rw [← hbun]
    ext x
    simp only [mem_union]
    tauto
  · have hexp : (T₀ ∪ β₀) ∩ (T₂ ∪ β₂) =
        T₀ ∩ T₂ ∪ T₀ ∩ β₂ ∪ (β₀ ∩ T₂ ∪ β₀ ∩ β₂) := by
      ext x
      simp only [mem_union, mem_inter_iff]
      tauto
    rw [hexp, hTT, h02, h20, hbin, union_empty, empty_union, Set.singleton_union]

theorem exists_boundary_arcs_of_isCutPair {D A₁ A₂ : Set Plane} {v : Fin 4 → Plane}
    (hcut : IsCutPair (frontier D) (v 0) (v 2) A₁ A₂) (hv1 : v 1 ∈ A₁) (hv3 : v 3 ∈ A₂)
    (hvne : ∀ i j : Fin 4, i ≠ j → v i ≠ v j) :
    ∃ α : Fin 4 → Set Plane, (∀ i, IsArcBetween (α i) (v i) (v (i + 1))) ∧
      α 0 ∪ α 1 = A₁ ∧ α 0 ∩ α 1 = {v 1} ∧ α 2 ∪ α 3 = A₂ ∧ α 2 ∩ α 3 = {v 3} := by
  obtain ⟨a0, a1, ha0, ha1, hau, hai⟩ :=
    hcut.fst.exists_split hv1 (hvne 1 0 (by decide)) (hvne 1 2 (by decide))
  obtain ⟨b0, b1, hb0, hb1, hbu, hbi⟩ :=
    hcut.snd.exists_split hv3 (hvne 3 0 (by decide)) (hvne 3 2 (by decide))
  refine ⟨![a0, a1, b1, b0], ?_, hau, hai, ?_, ?_⟩
  · intro i
    fin_cases i
    exacts [ha0, ha1, hb1.reverse, hb0.reverse]
  · rw [union_comm]
    exact hbu
  · rw [inter_comm]
    exact hbi

def fourSpokeSector (T α : Fin 4 → Set Plane) (i : Fin 4) : Set Plane :=
  closure (inside (T i ∪ α i ∪ T (i + 1)))

theorem fourSpokeSector_spec {D A₁ A₂ : Set Plane} {c : Plane} {T α : Fin 4 → Set Plane}
    {v : Fin 4 → Plane}
    (hD : IsPLBall 2 D) (hT : ∀ i, IsPLBall 1 (T i))
    (harc : ∀ i, IsArcBetween (T i) c (v i)) (hTD : ∀ i, T i ⊆ D)
    (hTf : ∀ i, T i ∩ frontier D = {v i}) (hTT : ∀ i j, i ≠ j → T i ∩ T j = {c})
    (hcut : IsCutPair (frontier D) (v 0) (v 2) A₁ A₂) (hv1 : v 1 ∈ A₁) (hv3 : v 3 ∈ A₂)
    (hα : ∀ i, IsArcBetween (α i) (v i) (v (i + 1)))
    (hαA₁ : α 0 ∪ α 1 = A₁) (hαA₁' : α 0 ∩ α 1 = {v 1})
    (hαA₂ : α 2 ∪ α 3 = A₂) (hαA₂' : α 2 ∩ α 3 = {v 3}) :
    (∀ i, IsPLBall 2 (fourSpokeSector T α i) ∧
        frontier (fourSpokeSector T α i) = T i ∪ α i ∪ T (i + 1)) ∧
      fourSpokeSector T α 0 ∪ fourSpokeSector T α 1 ∪
          (fourSpokeSector T α 2 ∪ fourSpokeSector T α 3) = D ∧
      ∀ i j, i ≠ j → fourSpokeSector T α i ∩ fourSpokeSector T α j ⊆ ⋃ k, T k := by
  classical
  have hα0 : IsArcBetween (α 0) (v 0) (v 1) := hα 0
  have hα1 : IsArcBetween (α 1) (v 1) (v 2) := hα 1
  have hα2 : IsArcBetween (α 2) (v 2) (v 3) := hα 2
  have hα3 : IsArcBetween (α 3) (v 3) (v 0) := hα 3
  have hvne : ∀ i j : Fin 4, i ≠ j → v i ≠ v j := by
    intro i j hij h
    have hmem : v i ∈ T i ∩ T j := ⟨(harc i).right_mem, by rw [h]; exact (harc j).right_mem⟩
    rw [hTT i j hij] at hmem
    exact ne_of_isArcBetween (harc i) (mem_singleton_iff.mp hmem).symm
  have hA₁f : A₁ ⊆ frontier D := hcut.fst_subset
  have hA₂f : A₂ ⊆ frontier D := hcut.snd_subset
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
  have hcutB : IsCutPair (frontier (closure (inside (A₁ ∪ (T 0 ∪ T 2))))) c (v 1)
      (T 0 ∪ α 0) (T 2 ∪ α 1) := by
    rw [hfr₁]
    exact isCutPair_spoke_arc_union (harc 0) (harc 2) (hTf 0) (hTf 2)
      (hTT 0 2 (by decide)) hα0 hα1 hαA₁ hαA₁' hA₁f
  have hcutB' : IsCutPair (frontier (closure (inside (A₂ ∪ (T 0 ∪ T 2))))) c (v 3)
      (T 2 ∪ α 2) (T 0 ∪ α 3) := by
    rw [hfr₂]
    have h := isCutPair_spoke_arc_union (harc 2) (harc 0) (hTf 2) (hTf 0)
      (hTT 2 0 (by decide)) hα2 hα3 hαA₂ hαA₂' hA₂f
    rwa [union_comm (T 2) (T 0)] at h
  have he1 : T 2 ∪ α 1 ∪ T 1 = T 1 ∪ α 1 ∪ T 2 := by
    ext x; simp only [mem_union]; tauto
  have he3 : T 0 ∪ α 3 ∪ T 3 = T 3 ∪ α 3 ∪ T 0 := by
    ext x; simp only [mem_union]; tauto
  obtain ⟨hs0, hf0⟩ := isPLBall_closure_inside_arc_union hD₁ (hT 1) hcross₁D hcutB
  obtain ⟨hs1, hf1⟩ := isPLBall_closure_inside_arc_union hD₁ (hT 1) hcross₁D hcutB.symm
  obtain ⟨hs2, hf2⟩ := isPLBall_closure_inside_arc_union hD₂ (hT 3) hcross₃D hcutB'
  obtain ⟨hs3, hf3⟩ := isPLBall_closure_inside_arc_union hD₂ (hT 3) hcross₃D hcutB'.symm
  obtain ⟨hun₁, hin₁⟩ := closure_inside_arc_union_union_and_inter hD₁ hcross₁D hcutB
  obtain ⟨hun₂, hin₂⟩ := closure_inside_arc_union_union_and_inter hD₂ hcross₃D hcutB'
  rw [he1] at hs1 hf1 hun₁ hin₁
  rw [he3] at hs3 hf3 hun₂ hin₂
  have hsub0 : closure (inside (T 0 ∪ α 0 ∪ T 1)) ⊆ closure (inside (A₁ ∪ (T 0 ∪ T 2))) := by
    rw [← hun₁]; exact subset_union_left
  have hsub1 : closure (inside (T 1 ∪ α 1 ∪ T 2)) ⊆ closure (inside (A₁ ∪ (T 0 ∪ T 2))) := by
    rw [← hun₁]; exact subset_union_right
  have hsub2 : closure (inside (T 2 ∪ α 2 ∪ T 3)) ⊆ closure (inside (A₂ ∪ (T 0 ∪ T 2))) := by
    rw [← hun₂]; exact subset_union_left
  have hsub3 : closure (inside (T 3 ∪ α 3 ∪ T 0)) ⊆ closure (inside (A₂ ∪ (T 0 ∪ T 2))) := by
    rw [← hun₂]; exact subset_union_right
  have hT02 : T 0 ∪ T 2 ⊆ ⋃ k, T k :=
    union_subset (subset_iUnion T 0) (subset_iUnion T 2)
  have hcrossPair : ∀ S S' : Set Plane, S ⊆ closure (inside (A₁ ∪ (T 0 ∪ T 2))) →
      S' ⊆ closure (inside (A₂ ∪ (T 0 ∪ T 2))) → S ∩ S' ⊆ ⋃ k, T k := by
    intro S S' hS hS'
    exact ((inter_subset_inter hS hS').trans hDin.subset).trans hT02
  have hunion : closure (inside (T 0 ∪ α 0 ∪ T 1)) ∪ closure (inside (T 1 ∪ α 1 ∪ T 2)) ∪
      (closure (inside (T 2 ∪ α 2 ∪ T 3)) ∪ closure (inside (T 3 ∪ α 3 ∪ T 0))) = D := by
    rw [hun₁, hun₂, hDun]
  refine ⟨?_, hunion, ?_⟩
  · intro i
    fin_cases i
    exacts [⟨hs0, hf0⟩, ⟨hs1, hf1⟩, ⟨hs2, hf2⟩, ⟨hs3, hf3⟩]
  · intro i j hij
    fin_cases i <;> fin_cases j
    · exact absurd rfl hij
    · exact hin₁.subset.trans (subset_iUnion T 1)
    · exact hcrossPair _ _ hsub0 hsub2
    · exact hcrossPair _ _ hsub0 hsub3
    · rw [inter_comm]; exact hin₁.subset.trans (subset_iUnion T 1)
    · exact absurd rfl hij
    · exact hcrossPair _ _ hsub1 hsub2
    · exact hcrossPair _ _ hsub1 hsub3
    · rw [inter_comm]; exact hcrossPair _ _ hsub0 hsub2
    · rw [inter_comm]; exact hcrossPair _ _ hsub1 hsub2
    · exact absurd rfl hij
    · exact hin₂.subset.trans (subset_iUnion T 3)
    · rw [inter_comm]; exact hcrossPair _ _ hsub0 hsub3
    · rw [inter_comm]; exact hcrossPair _ _ hsub1 hsub3
    · rw [inter_comm]; exact hin₂.subset.trans (subset_iUnion T 3)
    · exact absurd rfl hij

theorem inter_frontier_eq_of_frontier_union_eq {D S T₁ T₂ A : Set Plane} {a b : Plane}
    (hS : IsClosed S) (hSD : S ⊆ D) (hfr : frontier S = T₁ ∪ A ∪ T₂)
    (hT₁ : T₁ ∩ frontier D = {a}) (hT₂ : T₂ ∩ frontier D = {b})
    (ha : a ∈ A) (hb : b ∈ A) (hAD : A ⊆ frontier D) :
    S ∩ frontier D = A := by
  refine Subset.antisymm (fun x hx => ?_) (fun x hx => ?_)
  · have hxfr : x ∈ frontier S := ⟨subset_closure hx.1, fun h => hx.2.2 (interior_mono hSD h)⟩
    rw [hfr] at hxfr
    rcases hxfr with h | h
    · rcases h with h | h
      · have hxa : x = a := hT₁.subset ⟨h, hx.2⟩
        rw [hxa]
        exact ha
      · exact h
    · have hxb : x = b := hT₂.subset ⟨h, hx.2⟩
      rw [hxb]
      exact hb
  · exact ⟨hS.frontier_subset (by rw [hfr]; exact Or.inl (Or.inr hx)), hAD hx⟩

theorem arc_inter_subset_singleton_of_notMem {S T : Set Plane} {c w : Plane}
    (hS : IsClosed S) (harc : IsArcBetween T c w)
    (hfr : Disjoint (T \ {c, w}) (frontier S)) (hw : w ∉ S) : T ∩ S ⊆ {c} := by
  intro x hx
  by_contra hxc
  have hxc' : x ≠ c := fun h => hxc (by simp [h])
  have hxw : x ≠ w := fun h => hw (h ▸ hx.2)
  have hmem : x ∈ T \ {c, w} := ⟨hx.1, by simp [hxc', hxw]⟩
  have hcover : T \ {c, w} ⊆ interior S ∪ Sᶜ := by
    intro y hy
    by_cases hyS : y ∈ S
    · exact Or.inl ((mem_interior_iff_notMem_frontier hyS).mpr
        fun hyfr => Set.disjoint_left.mp hfr hy hyfr)
    · exact Or.inr hyS
  have hdisj : Disjoint (interior S) Sᶜ :=
    Set.disjoint_left.mpr fun y hy hy' => hy' (interior_subset hy)
  have hsub := (IsPreconnected.subset_or_subset isOpen_interior hS.isOpen_compl hdisj hcover
    harc.isPreconnected_diff).resolve_right fun h => h hmem hx.2
  have hwcl : w ∈ closure S := closure_mono (hsub.trans interior_subset)
    harc.right_mem_closure_diff
  rw [hS.closure_eq] at hwcl
  exact hw hwcl

end DifferentialGeometry.Topology.PiecewiseLinear
