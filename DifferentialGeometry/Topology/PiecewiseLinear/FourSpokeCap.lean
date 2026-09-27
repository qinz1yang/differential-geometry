/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.FourSpokeSectorFrontier
import DifferentialGeometry.Topology.PiecewiseLinear.FiniteGluing
import DifferentialGeometry.Topology.PiecewiseLinear.BallComplement
import DifferentialGeometry.Topology.PiecewiseLinear.PolygonalArcBall

open Set

namespace DifferentialGeometry.Topology.PiecewiseLinear

open Schoenflies

structure IsInitialSpokeSegment (T E : Set Plane) (c w v : Plane) : Prop where
  initialArc : IsArcBetween (T ∩ E) c w
  outerArc : IsArcBetween (T \ interior E) w v
  union_eq : (T ∩ E) ∪ (T \ interior E) = T
  inter_eq : (T ∩ E) ∩ (T \ interior E) = {w}

theorem isInitialSpokeSegment_of_isArcBetween
    {T E : Set Plane} {c w v : Plane}
    (hEclosed : IsClosed E)
    (harc : IsArcBetween T c v)
    (hTfE : T ∩ frontier E = {w})
    (hcE : c ∈ interior E)
    (hvE : v ∉ E) :
    IsInitialSpokeSegment T E c w v := by
  have hwpair : w ∈ T ∩ frontier E := hTfE.symm.subset rfl
  have hwT : w ∈ T := hwpair.1
  have hwfr : w ∈ frontier E := hwpair.2
  have hwE : w ∈ E := hEclosed.frontier_subset hwfr
  have hcfr : c ∉ frontier E :=
    (mem_interior_iff_notMem_frontier (interior_subset hcE)).mp hcE
  have hwc : w ≠ c := by
    intro h
    exact hcfr (h ▸ hwfr)
  have hwv : w ≠ v := by
    intro h
    exact hvE (h ▸ hwE)
  obtain ⟨A₁, A₂, hA₁, hA₂, hAunion, hAinter⟩ :=
    harc.exists_split hwT hwc hwv
  have hcover₁ : A₁ \ {c, w} ⊆ interior E ∪ Eᶜ := by
    intro x hx
    by_cases hxE : x ∈ E
    · have hxnotfr : x ∉ frontier E := by
        intro hxfr
        have hxw : x = w := mem_singleton_iff.mp
          (hTfE.subset ⟨hAunion ▸ Or.inl hx.1, hxfr⟩)
        exact hx.2 (by simp [hxw])
      exact Or.inl ((mem_interior_iff_notMem_frontier hxE).mpr hxnotfr)
    · exact Or.inr hxE
  have hcover₂ : A₂ \ {w, v} ⊆ interior E ∪ Eᶜ := by
    intro x hx
    by_cases hxE : x ∈ E
    · have hxnotfr : x ∉ frontier E := by
        intro hxfr
        have hxw : x = w := mem_singleton_iff.mp
          (hTfE.subset ⟨hAunion ▸ Or.inr hx.1, hxfr⟩)
        exact hx.2 (by simp [hxw])
      exact Or.inl ((mem_interior_iff_notMem_frontier hxE).mpr hxnotfr)
    · exact Or.inr hxE
  have hdisj : Disjoint (interior E) Eᶜ :=
    Set.disjoint_left.mpr fun x hxint hxcomp => hxcomp (interior_subset hxint)
  have hA₁side : A₁ \ {c, w} ⊆ interior E := by
    have hsub := IsPreconnected.subset_or_subset isOpen_interior hEclosed.isOpen_compl
      hdisj hcover₁ hA₁.isPreconnected_diff
    apply hsub.resolve_right
    intro hsubc
    have hccl : c ∈ closure Eᶜ :=
      closure_mono hsubc hA₁.left_mem_closure_diff
    exact Set.disjoint_left.mp (hdisj.closure_right isOpen_interior) hcE hccl
  have hA₂side : A₂ \ {w, v} ⊆ Eᶜ := by
    have hsub := IsPreconnected.subset_or_subset isOpen_interior hEclosed.isOpen_compl
      hdisj hcover₂ hA₂.isPreconnected_diff
    apply hsub.resolve_left
    intro hsubi
    have hvcl : v ∈ closure E :=
      closure_mono (hsubi.trans interior_subset) hA₂.right_mem_closure_diff
    exact hvE (hEclosed.closure_eq ▸ hvcl)
  have hA₁E : A₁ ⊆ E := by
    intro x hx
    by_cases hxc : x = c
    · exact hxc ▸ interior_subset hcE
    · by_cases hxw : x = w
      · exact hxw ▸ hwE
      · exact interior_subset (hA₁side ⟨hx, by simp [hxc, hxw]⟩)
  have hA₂notint : A₂ ⊆ (interior E)ᶜ := by
    intro x hx
    by_cases hxw : x = w
    · exact fun hxint => by
        have hwint : w ∈ interior E := hxw ▸ hxint
        exact ((mem_interior_iff_notMem_frontier hwE).mp hwint) hwfr
    · by_cases hxv : x = v
      · exact fun hxint => hvE (hxv ▸ interior_subset hxint)
      · exact fun hxint => (hA₂side ⟨hx, by simp [hxw, hxv]⟩) (interior_subset hxint)
  have hA₁eq : A₁ = T ∩ E := by
    apply Subset.antisymm
    · exact fun x hx => ⟨hAunion ▸ Or.inl hx, hA₁E hx⟩
    · intro x hx
      rcases hAunion ▸ hx.1 with hxA₁ | hxA₂
      · exact hxA₁
      · by_cases hxw : x = w
        · exact hxw ▸ hA₁.right_mem
        · by_cases hxv : x = v
          · exact (hvE (hxv ▸ hx.2)).elim
          · exact (False.elim ((hA₂side ⟨hxA₂, by simp [hxw, hxv]⟩) hx.2))
  have hA₂eq : A₂ = T \ interior E := by
    apply Subset.antisymm
    · exact fun x hx => ⟨hAunion ▸ Or.inr hx, hA₂notint hx⟩
    · intro x hx
      rcases hAunion ▸ hx.1 with hxA₁ | hxA₂
      · by_cases hxc : x = c
        · exact (hx.2 (hxc ▸ hcE)).elim
        · by_cases hxw : x = w
          · exact hxw ▸ hA₂.left_mem
          · exact (False.elim (hx.2 (hA₁side ⟨hxA₁, by simp [hxc, hxw]⟩)))
      · exact hxA₂
  exact ⟨hA₁eq ▸ hA₁, hA₂eq ▸ hA₂, by rw [← hA₁eq, ← hA₂eq]; exact hAunion,
    by rw [← hA₁eq, ← hA₂eq]; exact hAinter⟩

theorem IsInitialSpokeSegment.prefix_mem
    {T E : Set Plane} {c w v : Plane}
    (_h : IsInitialSpokeSegment T E c w v) : c ∈ T ∩ E := _h.initialArc.left_mem

theorem IsInitialSpokeSegment.tail_mem
    {T E : Set Plane} {c w v : Plane}
    (_h : IsInitialSpokeSegment T E c w v) : v ∈ T \ interior E := _h.outerArc.right_mem

theorem IsInitialSpokeSegment.boundary_mem
    {T E : Set Plane} {c w v : Plane}
    (_h : IsInitialSpokeSegment T E c w v) : w ∈ T ∩ E := _h.initialArc.right_mem

theorem IsInitialSpokeSegment.outerArc_isPLBall
    {T E : Set Plane} {c w v : Plane}
    (hT : IsPLBall 1 T) (hE : IsPLBall 2 E)
    (_h : IsInitialSpokeSegment T E c w v) : IsPLBall 1 (T \ interior E) := by
  apply isPLBall_one_of_isArcBetween_of_isPolygonal _h.outerArc
  exact (hT.isPolyhedron.sdiff_interior_of_isPLBall hE).isPolygonal_of_isArcBetween _h.outerArc

theorem subset_inside_sector_of_inner_arc
    {H J A₁ A₂ β : Set Plane} {p q a b : Plane}
    (_hH : IsPLBall 2 H) (hcross : IsCrosscut (frontier H) J p q)
    (hcut : IsCutPair (frontier H) p q A₁ A₂)
    (hβ : IsArcBetween β a b)
    (hβinside : β \ {a, b} ⊆ inside (frontier H))
    (hβavoid : ∀ x ∈ β \ {a, b}, x ∉ J)
    (ha : a ∈ A₁) (hap : a ≠ p) (haq : a ≠ q) :
    β \ {a, b} ⊆ inside (A₁ ∪ J) := by
  apply subset_inside_arc_union_of_isPreconnected hcross hcut hβ.isPreconnected_diff
  · exact hβinside
  · exact hβavoid
  · exact hβ.left_mem_closure_diff
  · exact ha
  · exact hap
  · exact haq

theorem subset_inside_outer_half_of_inner_arc
    {D E A₁ A₂ T₀ T₂ R β : Set Plane} {v₀ v₁ v₂ w₀ w₁ : Plane}
    (hD : IsPLBall 2 D) (hE : IsPLBall 2 E) (hEint : E ⊆ interior D)
    (hcross : IsCrosscut (frontier D) (T₀ ∪ T₂) v₀ v₂)
    (hcut : IsCutPair (frontier D) v₀ v₂ A₁ A₂)
    (hR : IsArcBetween R w₁ v₁) (hβ : IsArcBetween β w₀ w₁)
    (hmeet : ∀ x ∈ β, x ∈ R → x = w₁)
    (hβD : β ⊆ frontier E) (hβcut : Disjoint (β \ {w₀, w₁}) (T₀ ∪ T₂))
    (hRsub : R ⊆ D) (hRf : R ∩ frontier D = {v₁})
    (hRT : Disjoint (R \ {w₁, v₁}) (T₀ ∪ T₂))
    (hw₁A : w₁ ∉ T₀ ∪ T₂)
    (hv₁ : v₁ ∈ A₁) (hv₁fr : v₁ ∈ frontier D)
    (hvne₀ : v₁ ≠ v₀) (hvne₂ : v₁ ≠ v₂) :
    β \ {w₀, w₁} ⊆ inside (A₁ ∪ (T₀ ∪ T₂)) := by
  have hpath : IsArcBetween (β ∪ R) w₀ v₁ := hβ.concatenate hR hmeet
  have hS : IsPreconnected ((β ∪ R) \ {w₀, v₁}) := hpath.isPreconnected_diff
  have hside : (β ∪ R) \ {w₀, v₁} ⊆ inside (A₁ ∪ (T₀ ∪ T₂)) :=
    by
      refine subset_inside_arc_union_of_isPreconnected (w := v₁) hcross hcut hS ?_ ?_ ?_ ?_ ?_ ?_
      · intro x hx
        rw [← hD.interior_eq_inside_frontier]
        rcases hx.1 with hxb | hxr
        · exact hEint (hE.isPolyhedron.isClosed.frontier_subset (hβD hxb))
        · apply (mem_interior_iff_notMem_frontier (hRsub hxr)).mpr
          intro hfr
          apply hx.2
          have hfr' : x ∈ R ∩ frontier D := ⟨hxr, hfr⟩
          rw [hRf] at hfr'
          exact by simp [mem_insert_iff, mem_singleton_iff, mem_singleton_iff.mp hfr']
      · intro x hx hxA
        have hxnot : x ≠ w₀ ∧ x ≠ v₁ := by
          simpa [mem_insert_iff, mem_singleton_iff, not_or] using hx.2
        rcases hx.1 with hxb | hxr
        · by_cases hxw₁ : x = w₁
          · exact hw₁A (hxw₁ ▸ hxA)
          · exact Set.disjoint_left.mp hβcut ⟨hxb, by simp [hxnot.1, hxw₁]⟩ hxA
        · by_cases hxw₁ : x = w₁
          · exact hw₁A (hxw₁ ▸ hxA)
          · exact Set.disjoint_left.mp hRT ⟨hxr, by simp [hxnot.2, hxw₁]⟩ hxA
      · exact hpath.right_mem_closure_diff
      · exact hv₁
      · exact hvne₀
      · exact hvne₂
  have hv₁notE : v₁ ∉ frontier E := by
    intro hvE
    have hv₁int : v₁ ∈ interior D :=
      hEint (hE.isPolyhedron.isClosed.frontier_subset hvE)
    exact (mem_interior_iff_notMem_frontier (hRsub hR.right_mem)).mp hv₁int hv₁fr
  have hv₁notβ : v₁ ∉ β := fun hvβ => hv₁notE (hβD hvβ)
  intro x hx
  have hxv₁ : x ≠ v₁ := fun h => hv₁notβ (h ▸ hx.1)
  have hxw₀ : x ≠ w₀ := by
    intro h
    exact hx.2 (by simp [h])
  exact hside ⟨Or.inl hx.1, by simp [hxv₁, hxw₀]⟩

theorem fourSpokeCap_sector_data_of_arcs
    {D E A₁ A₂ B₁ B₂ : Set Plane} {c : Plane}
    {T : Fin 4 → Set Plane} {v w : Fin 4 → Plane}
    {α β : Fin 4 → Set Plane}
    (hD : IsPLBall 2 D) (hE : IsPLBall 2 E) (hEint : E ⊆ interior D)
    (hcE : c ∈ interior E)
    (hT : ∀ i, IsPLBall 1 (T i)) (harc : ∀ i, IsArcBetween (T i) c (v i))
    (hTD : ∀ i, T i ⊆ D) (hTf : ∀ i, T i ∩ frontier D = {v i})
    (hTT : ∀ i j, i ≠ j → T i ∩ T j = {c})
    (hTfE : ∀ i, T i ∩ frontier E = {w i})
    (hcut : IsCutPair (frontier D) (v 0) (v 2) A₁ A₂)
    (hv1 : v 1 ∈ A₁) (hv3 : v 3 ∈ A₂)
    (hcutE : IsCutPair (frontier E) (w 0) (w 2) B₁ B₂)
    (hα : ∀ i, IsArcBetween (α i) (v i) (v (i + 1)))
    (hα01 : α 0 ∪ α 1 = A₁) (hα01i : α 0 ∩ α 1 = {v 1})
    (hα23 : α 2 ∪ α 3 = A₂) (hα23i : α 2 ∩ α 3 = {v 3})
    (hβ : ∀ i, IsArcBetween (β i) (w i) (w (i + 1)))
    (hβ01 : β 0 ∪ β 1 = B₁) (hβ01i : β 0 ∩ β 1 = {w 1})
    (hβ23 : β 2 ∪ β 3 = B₂) (hβ23i : β 2 ∩ β 3 = {w 3}) :
    (∀ i, IsPLBall 2 (fourSpokeSector T α i) ∧
      frontier (fourSpokeSector T α i) = T i ∪ α i ∪ T (i + 1)) ∧
    (∀ i, IsCrosscut (frontier (fourSpokeSector T α i)) (β i)
      (w i) (w (i + 1))) := by
  classical
  have hvE : ∀ i : Fin 4, v i ∉ E := by
    intro i hvi
    have hviint : v i ∈ interior D := hEint hvi
    have hvif : v i ∈ frontier D := (hTf i).symm.subset rfl |>.2
    exact (mem_interior_iff_notMem_frontier (interior_subset hviint)).mp hviint hvif
  have hinit : ∀ i : Fin 4, IsInitialSpokeSegment (T i) E c (w i) (v i) := by
    intro i
    exact isInitialSpokeSegment_of_isArcBetween hE.isPolyhedron.isClosed (harc i)
      (hTfE i) hcE (hvE i)
  have hvne : ∀ i j : Fin 4, i ≠ j → v i ≠ v j := by
    intro i j hij h
    have hmem : v i ∈ T i ∩ T j := ⟨(harc i).right_mem, by rw [h]; exact (harc j).right_mem⟩
    rw [hTT i j hij] at hmem
    exact ne_of_isArcBetween (harc i) (mem_singleton_iff.mp hmem).symm
  have hwne : ∀ i j : Fin 4, i ≠ j → w i ≠ w j := by
    intro i j hij h
    have hmem : w i ∈ T i ∩ T j :=
      ⟨(hTfE i).symm.subset rfl |>.1, by rw [h]; exact (hTfE j).symm.subset rfl |>.1⟩
    rw [hTT i j hij] at hmem
    have hwc : w i = c := mem_singleton_iff.mp hmem
    have hwfr : w i ∈ frontier E := (hTfE i).symm.subset rfl |>.2
    exact (mem_interior_iff_notMem_frontier (hinit i).prefix_mem.2).mp hcE (hwc ▸ hwfr)
  obtain ⟨hsector, hsectorsCover, hsectorInter⟩ :=
    fourSpokeSector_spec hD hT harc hTD hTf hTT hcut hv1 hv3 hα hα01 hα01i hα23 hα23i
  have hwc : ∀ i : Fin 4, w i ≠ c := by
    intro i h
    have hwi : w i ∈ frontier E := (hTfE i).symm.subset rfl |>.2
    exact (mem_interior_iff_notMem_frontier (hinit i).prefix_mem.2).mp hcE (h ▸ hwi)
  have hwT : ∀ i j : Fin 4, i ≠ j → w i ∉ T j := by
    intro i j hij hwi
    have hmem : w i ∈ T i ∩ T j :=
      ⟨(hTfE i).symm.subset rfl |>.1, hwi⟩
    rw [hTT i j hij] at hmem
    exact hwc i (mem_singleton_iff.mp hmem)
  have hvfr : ∀ i : Fin 4, v i ∈ frontier D := by
    intro i
    exact (hTf i).symm.subset rfl |>.2
  have hwv : ∀ i j : Fin 4, w i ≠ v j := by
    intro i j h
    have hwfr : w i ∈ frontier E := (hTfE i).symm.subset rfl |>.2
    have hwint : w i ∈ interior D :=
      hEint (hE.isPolyhedron.isClosed.frontier_subset hwfr)
    exact (mem_interior_iff_notMem_frontier (x := w i) (interior_subset hwint)).mp hwint
      (h ▸ hvfr j)
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
  have hcross₁D : IsCrosscut (frontier (closure (inside (A₁ ∪ (T 0 ∪ T 2))))) (T 1) c (v 1) := by
    rw [hfr₁]
    exact hcross₁
  have hcross₃D : IsCrosscut (frontier (closure (inside (A₂ ∪ (T 0 ∪ T 2))))) (T 3) c (v 3) := by
    rw [hfr₂]
    exact hcross₃
  have hA₁f : A₁ ⊆ frontier D := hcut.fst_subset
  have hA₂f : A₂ ⊆ frontier D := hcut.snd_subset
  have hcutB : IsCutPair (frontier (closure (inside (A₁ ∪ (T 0 ∪ T 2))))) c (v 1)
      (T 0 ∪ α 0) (T 2 ∪ α 1) := by
    rw [hfr₁]
    exact isCutPair_spoke_arc_union (harc 0) (harc 2) (hTf 0) (hTf 2)
      (hTT 0 2 (by decide)) (hα 0) (hα 1) hα01 hα01i hA₁f
  have hcutB' : IsCutPair (frontier (closure (inside (A₂ ∪ (T 0 ∪ T 2))))) c (v 3)
      (T 2 ∪ α 2) (T 0 ∪ α 3) := by
    rw [hfr₂]
    have h := isCutPair_spoke_arc_union (harc 2) (harc 0) (hTf 2) (hTf 0)
      (hTT 2 0 (by decide)) (hα 2) (hα 3) hα23 hα23i hA₂f
    rwa [union_comm (T 2) (T 0)] at h
  have hβsub : ∀ i : Fin 4, β i ⊆ frontier E := by
    intro i
    fin_cases i
    · intro x hx
      exact hcutE.fst_subset (hβ01 ▸ Or.inl hx)
    · intro x hx
      exact hcutE.fst_subset (hβ01 ▸ Or.inr hx)
    · intro x hx
      exact hcutE.snd_subset (hβ23 ▸ Or.inl hx)
    · intro x hx
      exact hcutE.snd_subset (hβ23 ▸ Or.inr hx)
  have hR1 : IsArcBetween (T 1 \ interior E) (w 1) (v 1) := (hinit 1).outerArc
  have hR3 : IsArcBetween (T 3 \ interior E) (w 3) (v 3) := (hinit 3).outerArc
  have hR1f : (T 1 \ interior E) ∩ frontier D = {v 1} := by
    apply Subset.antisymm
    · intro x hx
      have hx' : x ∈ T 1 ∩ frontier D := ⟨sdiff_subset hx.1, hx.2⟩
      exact (hTf 1).subset hx'
    · intro x hx
      have hx' : x = v 1 := mem_singleton_iff.mp hx
      subst x
      exact ⟨(hinit 1).outerArc.right_mem, hvfr 1⟩
  have hR3f : (T 3 \ interior E) ∩ frontier D = {v 3} := by
    apply Subset.antisymm
    · intro x hx
      have hx' : x ∈ T 3 ∩ frontier D := ⟨sdiff_subset hx.1, hx.2⟩
      exact (hTf 3).subset hx'
    · intro x hx
      have hx' : x = v 3 := mem_singleton_iff.mp hx
      subst x
      exact ⟨(hinit 3).outerArc.right_mem, hvfr 3⟩
  have hR1T : Disjoint ((T 1 \ interior E) \ {w 1, v 1}) (T 0 ∪ T 2) := by
    rw [disjoint_left]
    intro x hx hxT
    rcases hxT with hx0 | hx2
    · have hmem : x ∈ T 1 ∩ T 0 := ⟨sdiff_subset hx.1, hx0⟩
      rw [hTT 1 0 (by decide)] at hmem
      exact (mem_singleton_iff.mp hmem ▸ hx.1).2 hcE
    · have hmem : x ∈ T 1 ∩ T 2 := ⟨sdiff_subset hx.1, hx2⟩
      rw [hTT 1 2 (by decide)] at hmem
      exact (mem_singleton_iff.mp hmem ▸ hx.1).2 hcE
  have hR3T : Disjoint ((T 3 \ interior E) \ {w 3, v 3}) (T 0 ∪ T 2) := by
    rw [disjoint_left]
    intro x hx hxT
    rcases hxT with hx0 | hx2
    · have hmem : x ∈ T 3 ∩ T 0 := ⟨sdiff_subset hx.1, hx0⟩
      rw [hTT 3 0 (by decide)] at hmem
      exact (mem_singleton_iff.mp hmem ▸ hx.1).2 hcE
    · have hmem : x ∈ T 3 ∩ T 2 := ⟨sdiff_subset hx.1, hx2⟩
      rw [hTT 3 2 (by decide)] at hmem
      exact (mem_singleton_iff.mp hmem ▸ hx.1).2 hcE
  have hw2notβ0 : w 2 ∉ β 0 := by
    intro hw
    have hi : w 2 ∈ β 0 ∩ β 1 := ⟨hw, by simpa using (hβ 1).right_mem⟩
    rw [hβ01i] at hi
    exact (hwne 2 1 (by decide)) (mem_singleton_iff.mp hi)
  have hw0notβ1 : w 0 ∉ β 1 := by
    intro hw
    have hi : w 0 ∈ β 0 ∩ β 1 := ⟨(by simpa using (hβ 0).left_mem), hw⟩
    rw [hβ01i] at hi
    exact (hwne 0 1 (by decide)) (mem_singleton_iff.mp hi)
  have hw0notβ2 : w 0 ∉ β 2 := by
    intro hw
    have hi : w 0 ∈ β 2 ∩ β 3 := ⟨hw, by simpa using (hβ 3).right_mem⟩
    rw [hβ23i] at hi
    exact (hwne 0 3 (by decide)) (mem_singleton_iff.mp hi)
  have hw2notβ3 : w 2 ∉ β 3 := by
    intro hw
    have hi : w 2 ∈ β 2 ∩ β 3 := ⟨(by simpa using (hβ 2).left_mem), hw⟩
    rw [hβ23i] at hi
    exact (hwne 2 3 (by decide)) (mem_singleton_iff.mp hi)
  have hβ0cut : Disjoint (β 0 \ {w 0, w 1}) (T 0 ∪ T 2) := by
    rw [disjoint_left]
    intro x hx hxT
    rcases hxT with hx0 | hx2
    · have hxw : x = w 0 := mem_singleton_iff.mp ((hTfE 0).subset ⟨hx0, hβsub 0 hx.1⟩)
      exact hx.2 (by simp [hxw])
    · have hxw : x = w 2 := mem_singleton_iff.mp ((hTfE 2).subset ⟨hx2, hβsub 0 hx.1⟩)
      exact hw2notβ0 (hxw ▸ hx.1)
  have hβ1cut : Disjoint (β 1 \ {w 2, w 1}) (T 0 ∪ T 2) := by
    rw [disjoint_left]
    intro x hx hxT
    rcases hxT with hx0 | hx2
    · have hxw : x = w 0 := mem_singleton_iff.mp ((hTfE 0).subset ⟨hx0, hβsub 1 hx.1⟩)
      exact hw0notβ1 (hxw ▸ hx.1)
    · have hxw : x = w 2 := mem_singleton_iff.mp ((hTfE 2).subset ⟨hx2, hβsub 1 hx.1⟩)
      exact hx.2 (by simp [hxw])
  have hβ2cut : Disjoint (β 2 \ {w 2, w 3}) (T 0 ∪ T 2) := by
    rw [disjoint_left]
    intro x hx hxT
    rcases hxT with hx0 | hx2
    · have hxw : x = w 0 := mem_singleton_iff.mp ((hTfE 0).subset ⟨hx0, hβsub 2 hx.1⟩)
      exact hw0notβ2 (hxw ▸ hx.1)
    · have hxw : x = w 2 := mem_singleton_iff.mp ((hTfE 2).subset ⟨hx2, hβsub 2 hx.1⟩)
      exact hx.2 (by simp [hxw])
  have hβ3cut : Disjoint (β 3 \ {w 0, w 3}) (T 0 ∪ T 2) := by
    rw [disjoint_left]
    intro x hx hxT
    rcases hxT with hx0 | hx2
    · have hxw : x = w 0 := mem_singleton_iff.mp ((hTfE 0).subset ⟨hx0, hβsub 3 hx.1⟩)
      exact hx.2 (by simp [hxw])
    · have hxw : x = w 2 := mem_singleton_iff.mp ((hTfE 2).subset ⟨hx2, hβsub 3 hx.1⟩)
      exact hw2notβ3 (hxw ▸ hx.1)
  have hw1A : w 1 ∉ T 0 ∪ T 2 := by
    rintro (hx0 | hx2)
    · exact hwT 1 0 (by decide) hx0
    · exact hwT 1 2 (by decide) hx2
  have hw3A : w 3 ∉ T 0 ∪ T 2 := by
    rintro (hx0 | hx2)
    · exact hwT 3 0 (by decide) hx0
    · exact hwT 3 2 (by decide) hx2
  have hmeet0 : ∀ x ∈ β 0, x ∈ T 1 \ interior E → x = w 1 := by
    intro x hxb hxr
    have hx : x ∈ T 1 ∩ frontier E := ⟨hxr.1, hβsub 0 hxb⟩
    rw [hTfE 1] at hx
    exact mem_singleton_iff.mp hx
  have hmeet1 : ∀ x ∈ β 1, x ∈ T 1 \ interior E → x = w 1 := by
    intro x hxb hxr
    have hx : x ∈ T 1 ∩ frontier E := ⟨hxr.1, hβsub 1 hxb⟩
    rw [hTfE 1] at hx
    exact mem_singleton_iff.mp hx
  have hmeet2 : ∀ x ∈ β 2, x ∈ T 3 \ interior E → x = w 3 := by
    intro x hxb hxr
    have hx : x ∈ T 3 ∩ frontier E := ⟨hxr.1, hβsub 2 hxb⟩
    rw [hTfE 3] at hx
    exact mem_singleton_iff.mp hx
  have hmeet3 : ∀ x ∈ β 3, x ∈ T 3 \ interior E → x = w 3 := by
    intro x hxb hxr
    have hx : x ∈ T 3 ∩ frontier E := ⟨hxr.1, hβsub 3 hxb⟩
    rw [hTfE 3] at hx
    exact mem_singleton_iff.mp hx
  have hβ0side : β 0 \ {w 0, w 1} ⊆ inside (A₁ ∪ (T 0 ∪ T 2)) :=
    subset_inside_outer_half_of_inner_arc hD hE hEint hcrossA hcut hR1 (hβ 0) hmeet0
      (hβsub 0) hβ0cut (sdiff_subset.trans (hTD 1)) hR1f hR1T hw1A hv1 (hvfr 1)
      (hvne 1 0 (by decide)) (hvne 1 2 (by decide))
  have hβ1side' : β 1 \ {w 2, w 1} ⊆ inside (A₁ ∪ (T 0 ∪ T 2)) :=
    subset_inside_outer_half_of_inner_arc (w₀ := w 2) (w₁ := w 1) hD hE hEint hcrossA hcut hR1
      ((hβ 1).reverse) hmeet1 (hβsub 1) hβ1cut (sdiff_subset.trans (hTD 1)) hR1f hR1T
      hw1A hv1 (hvfr 1) (hvne 1 0 (by decide)) (hvne 1 2 (by decide))
  have hpair1 : ({w 2, w 1} : Set Plane) = {w 1, w 2} := by
    ext x
    simp [or_comm]
  have hβ1side : β 1 \ {w 1, w 2} ⊆ inside (A₁ ∪ (T 0 ∪ T 2)) := by
    rw [← hpair1]
    exact hβ1side'
  have hβ2side : β 2 \ {w 2, w 3} ⊆ inside (A₂ ∪ (T 0 ∪ T 2)) :=
    subset_inside_outer_half_of_inner_arc hD hE hEint hcrossA hcut.symm hR3 (hβ 2) hmeet2
      (hβsub 2) hβ2cut (sdiff_subset.trans (hTD 3)) hR3f hR3T hw3A hv3 (hvfr 3)
      (hvne 3 0 (by decide)) (hvne 3 2 (by decide))
  have hβ3side' : β 3 \ {w 0, w 3} ⊆ inside (A₂ ∪ (T 0 ∪ T 2)) :=
    subset_inside_outer_half_of_inner_arc (w₀ := w 0) (w₁ := w 3) hD hE hEint hcrossA hcut.symm hR3
      ((hβ 3).reverse) hmeet3 (hβsub 3) hβ3cut (sdiff_subset.trans (hTD 3)) hR3f hR3T
      hw3A hv3 (hvfr 3) (hvne 3 0 (by decide)) (hvne 3 2 (by decide))
  have hpair3 : ({w 0, w 3} : Set Plane) = {w 3, w 0} := by
    ext x
    simp [or_comm]
  have hβ3side : β 3 \ {w 3, w 0} ⊆ inside (A₂ ∪ (T 0 ∪ T 2)) := by
    rw [← hpair3]
    exact hβ3side'
  have hβ0inside : β 0 \ {w 0, w 1} ⊆
      inside (frontier (closure (inside (A₁ ∪ (T 0 ∪ T 2))))) := by
    rw [hfr₁]
    exact hβ0side
  have hβ1inside : β 1 \ {w 1, w 2} ⊆
      inside (frontier (closure (inside (A₁ ∪ (T 0 ∪ T 2))))) := by
    rw [hfr₁]
    exact hβ1side
  have hβ1inside' : β 1 \ {w 2, w 1} ⊆
      inside (frontier (closure (inside (A₁ ∪ (T 0 ∪ T 2))))) := by
    rw [hfr₁]
    exact hβ1side'
  have hβ2inside : β 2 \ {w 2, w 3} ⊆
      inside (frontier (closure (inside (A₂ ∪ (T 0 ∪ T 2))))) := by
    rw [hfr₂]
    exact hβ2side
  have hβ3inside : β 3 \ {w 3, w 0} ⊆
      inside (frontier (closure (inside (A₂ ∪ (T 0 ∪ T 2))))) := by
    rw [hfr₂]
    exact hβ3side
  have hβ3inside' : β 3 \ {w 0, w 3} ⊆
      inside (frontier (closure (inside (A₂ ∪ (T 0 ∪ T 2))))) := by
    rw [hfr₂]
    exact hβ3side'
  have hβ0avoid : ∀ x ∈ β 0 \ {w 0, w 1}, x ∉ T 1 := by
    intro x hx hT1
    have hxw : x = w 1 := mem_singleton_iff.mp ((hTfE 1).subset ⟨hT1, hβsub 0 hx.1⟩)
    exact hx.2 (by simp [hxw])
  have hβ1avoid : ∀ x ∈ β 1 \ {w 2, w 1}, x ∉ T 1 := by
    intro x hx hT1
    have hxw : x = w 1 := mem_singleton_iff.mp ((hTfE 1).subset ⟨hT1, hβsub 1 hx.1⟩)
    exact hx.2 (by simp [hxw])
  have hβ2avoid : ∀ x ∈ β 2 \ {w 2, w 3}, x ∉ T 3 := by
    intro x hx hT3
    have hxw : x = w 3 := mem_singleton_iff.mp ((hTfE 3).subset ⟨hT3, hβsub 2 hx.1⟩)
    exact hx.2 (by simp [hxw])
  have hβ3avoid : ∀ x ∈ β 3 \ {w 0, w 3}, x ∉ T 3 := by
    intro x hx hT3
    have hxw : x = w 3 := mem_singleton_iff.mp ((hTfE 3).subset ⟨hT3, hβsub 3 hx.1⟩)
    exact hx.2 (by simp [hxw])
  have hβ0sector : β 0 \ {w 0, w 1} ⊆ inside (T 0 ∪ α 0 ∪ T 1) := by
    have h := subset_inside_sector_of_inner_arc hD₁ hcross₁D hcutB (hβ 0) hβ0inside
      hβ0avoid (Or.inl ((hTfE 0).symm.subset rfl |>.1)) (hwc 0) (hwv 0 1)
    exact h
  have hβ1sector' : β 1 \ {w 2, w 1} ⊆ inside (T 1 ∪ α 1 ∪ T 2) := by
    have h := subset_inside_sector_of_inner_arc hD₁ hcross₁D hcutB.symm ((hβ 1).reverse)
      hβ1inside' hβ1avoid (Or.inl ((hTfE 2).symm.subset rfl |>.1)) (hwc 2) (hwv 2 1)
    simpa [union_assoc, union_left_comm, union_comm] using h
  have hβ1sector : β 1 \ {w 1, w 2} ⊆ inside (T 1 ∪ α 1 ∪ T 2) := by
    rw [← hpair1]
    exact hβ1sector'
  have hβ2sector : β 2 \ {w 2, w 3} ⊆ inside (T 2 ∪ α 2 ∪ T 3) := by
    have h := subset_inside_sector_of_inner_arc hD₂ hcross₃D hcutB' (hβ 2) hβ2inside
      hβ2avoid (Or.inl ((hTfE 2).symm.subset rfl |>.1)) (hwc 2) (hwv 2 3)
    exact h
  have hβ3sector' : β 3 \ {w 0, w 3} ⊆ inside (T 3 ∪ α 3 ∪ T 0) := by
    have h := subset_inside_sector_of_inner_arc hD₂ hcross₃D hcutB'.symm ((hβ 3).reverse)
      hβ3inside' hβ3avoid (Or.inl ((hTfE 0).symm.subset rfl |>.1)) (hwc 0) (hwv 0 3)
    simpa [union_assoc, union_left_comm, union_comm] using h
  have hβ3sector : β 3 \ {w 3, w 0} ⊆ inside (T 3 ∪ α 3 ∪ T 0) := by
    rw [← hpair3]
    exact hβ3sector'
  have hβ0ball : IsPLBall 1 (β 0) :=
    isPLBall_of_isArc_subset_isPLSphere hE.isPLSphere_frontier (hβ 0).isArc (hβsub 0)
  have hβ1ball : IsPLBall 1 (β 1) :=
    isPLBall_of_isArc_subset_isPLSphere hE.isPLSphere_frontier (hβ 1).isArc (hβsub 1)
  have hβ2ball : IsPLBall 1 (β 2) :=
    isPLBall_of_isArc_subset_isPLSphere hE.isPLSphere_frontier (hβ 2).isArc (hβsub 2)
  have hβ3ball : IsPLBall 1 (β 3) :=
    isPLBall_of_isArc_subset_isPLSphere hE.isPLSphere_frontier (hβ 3).isArc (hβsub 3)
  have hβ0cross : IsCrosscut (frontier (fourSpokeSector T α 0)) (β 0) (w 0) (w 1) := by
    refine ⟨isJordanCurve_of_isPLSphere_one (hsector 0).1.isPLSphere_frontier, hβ 0,
      hβ0ball.isPolyhedron.isPolygonal_of_isArcBetween (hβ 0), ?_, ?_, ?_⟩
    · rw [(hsector 0).2]
      exact Or.inl (Or.inl ((hTfE 0).symm.subset rfl |>.1))
    · rw [(hsector 0).2]
      exact Or.inr ((hTfE 1).symm.subset rfl |>.1)
    · rw [(hsector 0).2]
      exact hβ0sector
  have hβ1cross : IsCrosscut (frontier (fourSpokeSector T α 1)) (β 1) (w 1) (w 2) := by
    refine ⟨isJordanCurve_of_isPLSphere_one (hsector 1).1.isPLSphere_frontier, hβ 1,
      hβ1ball.isPolyhedron.isPolygonal_of_isArcBetween (hβ 1), ?_, ?_, ?_⟩
    · rw [(hsector 1).2]
      exact Or.inl (Or.inl ((hTfE 1).symm.subset rfl |>.1))
    · rw [(hsector 1).2]
      exact Or.inr ((hTfE 2).symm.subset rfl |>.1)
    · rw [(hsector 1).2]
      exact hβ1sector
  have hβ2cross : IsCrosscut (frontier (fourSpokeSector T α 2)) (β 2) (w 2) (w 3) := by
    refine ⟨isJordanCurve_of_isPLSphere_one (hsector 2).1.isPLSphere_frontier, hβ 2,
      hβ2ball.isPolyhedron.isPolygonal_of_isArcBetween (hβ 2), ?_, ?_, ?_⟩
    · rw [(hsector 2).2]
      exact Or.inl (Or.inl ((hTfE 2).symm.subset rfl |>.1))
    · rw [(hsector 2).2]
      exact Or.inr ((hTfE 3).symm.subset rfl |>.1)
    · rw [(hsector 2).2]
      exact hβ2sector
  have hβ3cross : IsCrosscut (frontier (fourSpokeSector T α 3)) (β 3) (w 3) (w 0) := by
    refine ⟨isJordanCurve_of_isPLSphere_one (hsector 3).1.isPLSphere_frontier, hβ 3,
      hβ3ball.isPolyhedron.isPolygonal_of_isArcBetween (hβ 3), ?_, ?_, ?_⟩
    · rw [(hsector 3).2]
      exact Or.inl (Or.inl ((hTfE 3).symm.subset rfl |>.1))
    · rw [(hsector 3).2]
      exact Or.inr ((hTfE 0).symm.subset rfl |>.1)
    · rw [(hsector 3).2]
      exact hβ3sector
  have hβcross : ∀ i : Fin 4,
      IsCrosscut (frontier (fourSpokeSector T α i)) (β i) (w i) (w (i + 1)) := by
    intro i
    fin_cases i
    · exact hβ0cross
    · exact hβ1cross
    · exact hβ2cross
    · exact hβ3cross
  exact ⟨hsector, hβcross⟩

theorem exists_fourSpokeCap_sector_data
    {D E A₁ A₂ B₁ B₂ : Set Plane} {c : Plane}
    {T : Fin 4 → Set Plane} {v w : Fin 4 → Plane}
    (hD : IsPLBall 2 D) (hE : IsPLBall 2 E) (hEint : E ⊆ interior D)
    (hcE : c ∈ interior E)
    (hT : ∀ i, IsPLBall 1 (T i)) (harc : ∀ i, IsArcBetween (T i) c (v i))
    (hTD : ∀ i, T i ⊆ D) (hTf : ∀ i, T i ∩ frontier D = {v i})
    (hTT : ∀ i j, i ≠ j → T i ∩ T j = {c})
    (hTfE : ∀ i, T i ∩ frontier E = {w i})
    (hcut : IsCutPair (frontier D) (v 0) (v 2) A₁ A₂)
    (hv1 : v 1 ∈ A₁) (hv3 : v 3 ∈ A₂)
    (hcutE : IsCutPair (frontier E) (w 0) (w 2) B₁ B₂)
    (hw1 : w 1 ∈ B₁) (hw3 : w 3 ∈ B₂) :
    ∃ α β : Fin 4 → Set Plane,
      (∀ i, IsArcBetween (α i) (v i) (v (i + 1))) ∧
        α 0 ∪ α 1 = A₁ ∧ α 0 ∩ α 1 = {v 1} ∧
        α 2 ∪ α 3 = A₂ ∧ α 2 ∩ α 3 = {v 3} ∧
        (∀ i, IsArcBetween (β i) (w i) (w (i + 1))) ∧
        β 0 ∪ β 1 = B₁ ∧ β 0 ∩ β 1 = {w 1} ∧
        β 2 ∪ β 3 = B₂ ∧ β 2 ∩ β 3 = {w 3} ∧
        (∀ i, IsPLBall 2 (fourSpokeSector T α i) ∧
          frontier (fourSpokeSector T α i) = T i ∪ α i ∪ T (i + 1)) ∧
        (∀ i, IsCrosscut (frontier (fourSpokeSector T α i)) (β i)
          (w i) (w (i + 1))) := by
  classical
  have hvE : ∀ i : Fin 4, v i ∉ E := by
    intro i hvi
    have hviint : v i ∈ interior D := hEint hvi
    have hvif : v i ∈ frontier D := (hTf i).symm.subset rfl |>.2
    exact (mem_interior_iff_notMem_frontier (interior_subset hviint)).mp hviint hvif
  have hinit : ∀ i : Fin 4, IsInitialSpokeSegment (T i) E c (w i) (v i) := by
    intro i
    exact isInitialSpokeSegment_of_isArcBetween hE.isPolyhedron.isClosed (harc i)
      (hTfE i) hcE (hvE i)
  have hvne : ∀ i j : Fin 4, i ≠ j → v i ≠ v j := by
    intro i j hij h
    have hmem : v i ∈ T i ∩ T j := ⟨(harc i).right_mem, by rw [h]; exact (harc j).right_mem⟩
    rw [hTT i j hij] at hmem
    exact ne_of_isArcBetween (harc i) (mem_singleton_iff.mp hmem).symm
  have hwne : ∀ i j : Fin 4, i ≠ j → w i ≠ w j := by
    intro i j hij h
    have hmem : w i ∈ T i ∩ T j :=
      ⟨(hTfE i).symm.subset rfl |>.1, by rw [h]; exact (hTfE j).symm.subset rfl |>.1⟩
    rw [hTT i j hij] at hmem
    have hwc : w i = c := mem_singleton_iff.mp hmem
    have hwfr : w i ∈ frontier E := (hTfE i).symm.subset rfl |>.2
    exact (mem_interior_iff_notMem_frontier (hinit i).prefix_mem.2).mp hcE (hwc ▸ hwfr)
  obtain ⟨α, hα, hα01, hα01i, hα23, hα23i⟩ :=
    exists_boundary_arcs_of_isCutPair hcut hv1 hv3 hvne
  obtain ⟨β, hβ, hβ01, hβ01i, hβ23, hβ23i⟩ :=
    exists_boundary_arcs_of_isCutPair hcutE hw1 hw3 hwne
  obtain ⟨hsector, hβcross⟩ := fourSpokeCap_sector_data_of_arcs hD hE hEint hcE hT harc
    hTD hTf hTT hTfE hcut hv1 hv3 hcutE hα hα01 hα01i hα23 hα23i hβ
    hβ01 hβ01i hβ23 hβ23i
  exact ⟨α, β, hα, hα01, hα01i, hα23, hα23i, hβ, hβ01, hβ01i, hβ23, hβ23i,
    hsector, hβcross⟩

theorem isCutPair_cap_sector_boundary
    {D E S α T₀ T₁ P₀ P₁ R₀ R₁ : Set Plane} {c w₀ w₁ v₀ v₁ : Plane}
    (hEint : E ⊆ interior D) (hfront : frontier S = T₀ ∪ α ∪ T₁)
    (hα : IsArcBetween α v₀ v₁) (hαD : α ⊆ frontier D)
    (hP₀ : IsArcBetween P₀ c w₀) (hP₁ : IsArcBetween P₁ c w₁)
    (hR₀ : IsArcBetween R₀ w₀ v₀) (hR₁ : IsArcBetween R₁ w₁ v₁)
    (hP₀sub : P₀ ⊆ T₀) (hP₁sub : P₁ ⊆ T₁)
    (hR₀sub : R₀ ⊆ T₀) (hR₁sub : R₁ ⊆ T₁)
    (hP₀E : P₀ ⊆ E) (hP₁E : P₁ ⊆ E)
    (hT₀ : P₀ ∪ R₀ = T₀) (hT₁ : P₁ ∪ R₁ = T₁)
    (hPR₀ : P₀ ∩ R₀ = {w₀}) (hPR₁ : P₁ ∩ R₁ = {w₁})
    (hTT : T₀ ∩ T₁ = {c}) (hcR₀ : c ∉ R₀) (hcR₁ : c ∉ R₁)
    (hR₀f : R₀ ∩ frontier D = {v₀}) (hR₁f : R₁ ∩ frontier D = {v₁}) :
    IsCutPair (frontier S) w₀ w₁ (R₀ ∪ α ∪ R₁) (P₀ ∪ P₁) := by
  have hR₀α : ∀ x ∈ R₀, x ∈ α → x = v₀ := by
    intro x hx₀ hxα
    exact mem_singleton_iff.mp (hR₀f.subset ⟨hx₀, hαD hxα⟩)
  have hαR₁ : ∀ x ∈ α, x ∈ R₁ → x = v₁ := by
    intro x hxα hx₁
    exact mem_singleton_iff.mp (hR₁f.subset ⟨hx₁, hαD hxα⟩)
  have hR₀R₁ : ∀ x ∈ R₀, x ∈ R₁ → x = c := by
    intro x hx₀ hx₁
    exact mem_singleton_iff.mp (hTT.subset ⟨hR₀sub hx₀, hR₁sub hx₁⟩)
  have hP₀P₁ : ∀ x ∈ P₀, x ∈ P₁ → x = c := by
    intro x hx₀ hx₁
    exact mem_singleton_iff.mp (hTT.subset ⟨hP₀sub hx₀, hP₁sub hx₁⟩)
  have hR₀P₁ : ∀ x ∈ R₀, x ∈ P₁ → x = c := by
    intro x hx₀ hx₁
    exact mem_singleton_iff.mp (hTT.subset ⟨hR₀sub hx₀, hP₁sub hx₁⟩)
  have hP₀R₁ : ∀ x ∈ P₀, x ∈ R₁ → x = c := by
    intro x hx₀ hx₁
    exact mem_singleton_iff.mp (hTT.subset ⟨hP₀sub hx₀, hR₁sub hx₁⟩)
  have houter : IsArcBetween (R₀ ∪ α ∪ R₁) w₀ w₁ := by
    apply (hR₀.concatenate hα hR₀α).concatenate hR₁.reverse
    intro x hxU hx₁
    rcases hxU with hx₀ | hxα
    · have hxc := hR₀R₁ x hx₀ hx₁
      exact (hcR₀ (hxc ▸ hx₀)).elim
    · exact hαR₁ x hxα hx₁
  have hinner : IsArcBetween (P₀ ∪ P₁) w₀ w₁ := by
    exact hP₀.reverse.concatenate hP₁ hP₀P₁
  have hcover : (R₀ ∪ α ∪ R₁) ∪ (P₀ ∪ P₁) = frontier S := by
    rw [hfront, ← hT₀, ← hT₁]
    ext x
    simp only [mem_union]
    tauto
  have hEfront : Disjoint E (frontier D) := by
    rw [disjoint_left]
    intro x hxE hxfr
    exact (mem_interior_iff_notMem_frontier (interior_subset (hEint hxE))).mp
      (hEint hxE) hxfr
  have hmeet : (R₀ ∪ α ∪ R₁) ∩ (P₀ ∪ P₁) = {w₀, w₁} := by
    apply Subset.antisymm
    · rintro x ⟨hxout, hxP⟩
      rcases hxout with hx01 | hx₁
      · rcases hx01 with hx₀ | hxα
        · rcases hxP with hxP₀ | hxP₁
          · have hxw := mem_singleton_iff.mp (hPR₀.subset ⟨hxP₀, hx₀⟩)
            simp [hxw]
          · have hxc := hR₀P₁ x hx₀ hxP₁
            exact (hcR₀ (hxc ▸ hx₀)).elim
        · rcases hxP with hxP₀ | hxP₁
          · exact (Set.disjoint_left.mp hEfront (hP₀E hxP₀) (hαD hxα)).elim
          · exact (Set.disjoint_left.mp hEfront (hP₁E hxP₁) (hαD hxα)).elim
      · rcases hxP with hxP₀ | hxP₁
        · have hxc := hP₀R₁ x hxP₀ hx₁
          exact (hcR₁ (hxc ▸ hx₁)).elim
        · have hxw := mem_singleton_iff.mp (hPR₁.subset ⟨hxP₁, hx₁⟩)
          simp [hxw]
    · exact pair_subset ⟨houter.left_mem, hinner.left_mem⟩ ⟨houter.right_mem, hinner.right_mem⟩
  exact ⟨houter, hinner, hcover, hmeet⟩

theorem isCutPair_cap_sector_of_fourSpokeData
    {D E : Set Plane} {c : Plane}
    {T : Fin 4 → Set Plane} {v w : Fin 4 → Plane} {α : Fin 4 → Set Plane}
    (hE : IsPLBall 2 E) (hEint : E ⊆ interior D)
    (hcE : c ∈ interior E)
    (harc : ∀ i, IsArcBetween (T i) c (v i))
    (hTf : ∀ i, T i ∩ frontier D = {v i})
    (hTT : ∀ i j, i ≠ j → T i ∩ T j = {c})
    (hTfE : ∀ i, T i ∩ frontier E = {w i})
    (hα : ∀ i, IsArcBetween (α i) (v i) (v (i + 1)))
    (hαD : ∀ i, α i ⊆ frontier D)
    (hsector : ∀ i, IsPLBall 2 (fourSpokeSector T α i) ∧
      frontier (fourSpokeSector T α i) = T i ∪ α i ∪ T (i + 1))
    (i : Fin 4) :
    IsCutPair (frontier (fourSpokeSector T α i)) (w i) (w (i + 1))
      ((T i \ interior E) ∪ α i ∪ (T (i + 1) \ interior E))
      ((T i ∩ E) ∪ (T (i + 1) ∩ E)) := by
  have hvE : ∀ j : Fin 4, v j ∉ E := by
    intro j hvj
    have hvjint : v j ∈ interior D := hEint hvj
    have hvjf : v j ∈ frontier D := (hTf j).symm.subset rfl |>.2
    exact (mem_interior_iff_notMem_frontier (interior_subset hvjint)).mp hvjint hvjf
  have hinit : ∀ j : Fin 4, IsInitialSpokeSegment (T j) E c (w j) (v j) := by
    intro j
    exact isInitialSpokeSegment_of_isArcBetween hE.isPolyhedron.isClosed (harc j)
      (hTfE j) hcE (hvE j)
  have hi_ne : i ≠ i + 1 := by
    intro h
    have hv := congrArg Fin.val h
    omega
  have hRf : ∀ j, (T j \ interior E) ∩ frontier D = {v j} := by
    intro j
    apply Subset.antisymm
    · intro x hx
      exact (hTf j).subset ⟨sdiff_subset hx.1, hx.2⟩
    · intro x hx
      have hxi : x = v j := mem_singleton_iff.mp hx
      subst x
      exact ⟨(hinit j).tail_mem, (hTf j).symm.subset rfl |>.2⟩
  apply isCutPair_cap_sector_boundary hEint (hsector i).2 (hα i) (hαD i)
    (hinit i).initialArc (hinit (i + 1)).initialArc
    (hinit i).outerArc (hinit (i + 1)).outerArc
    inter_subset_left inter_subset_left
    sdiff_subset sdiff_subset
    (fun x hx => hx.2)
    (fun x hx => hx.2)
    (hinit i).union_eq (hinit (i + 1)).union_eq
    (hinit i).inter_eq (hinit (i + 1)).inter_eq
    (hTT i (i + 1) hi_ne) (by intro hx; exact hx.2 hcE)
     (by intro hx; exact hx.2 hcE) (hRf i) (hRf (i + 1))

private theorem inner_sector_spec_of_fourSpokeCap
    {E B₁ B₂ : Set Plane} {c : Plane}
    {T : Fin 4 → Set Plane} {w : Fin 4 → Plane} {β : Fin 4 → Set Plane}
    (hE : IsPLBall 2 E) (hcE : c ∈ interior E)
    (hT : ∀ i, IsPLBall 1 (T i))
    (hinitArc : ∀ i, IsArcBetween (T i ∩ E) c (w i))
    (hTfE : ∀ i, T i ∩ frontier E = {w i})
    (hTT : ∀ i j, i ≠ j → T i ∩ T j = {c})
    (hcutE : IsCutPair (frontier E) (w 0) (w 2) B₁ B₂)
    (hw1 : w 1 ∈ B₁) (hw3 : w 3 ∈ B₂)
    (hβ : ∀ i, IsArcBetween (β i) (w i) (w (i + 1)))
    (hβ01 : β 0 ∪ β 1 = B₁) (hβ01i : β 0 ∩ β 1 = {w 1})
    (hβ23 : β 2 ∪ β 3 = B₂) (hβ23i : β 2 ∩ β 3 = {w 3}) :
    (∀ i, IsPLBall 2
        (closure (inside ((T i ∩ E) ∪ β i ∪ (T (i + 1) ∩ E)))) ∧
      frontier (closure (inside ((T i ∩ E) ∪ β i ∪ (T (i + 1) ∩ E)))) =
        (T i ∩ E) ∪ β i ∪ (T (i + 1) ∩ E)) ∧
      closure (inside ((T 0 ∩ E) ∪ β 0 ∪ (T 1 ∩ E))) ∪
          closure (inside ((T 1 ∩ E) ∪ β 1 ∪ (T 2 ∩ E))) ∪
          (closure (inside ((T 2 ∩ E) ∪ β 2 ∪ (T 3 ∩ E))) ∪
            closure (inside ((T 3 ∩ E) ∪ β 3 ∪ (T 0 ∩ E)))) = E ∧
      ∀ i j, i ≠ j →
        closure (inside ((T i ∩ E) ∪ β i ∪ (T (i + 1) ∩ E))) ∩
            closure (inside ((T j ∩ E) ∪ β j ∪ (T (j + 1) ∩ E))) ⊆
          ⋃ k, T k ∩ E := by
  have hP : ∀ i : Fin 4, IsPLBall 1 (T i ∩ E) := by
    intro i
    exact isPLBall_one_of_isArcBetween_of_isPolygonal (hinitArc i)
      (((hT i).isPolyhedron.inter hE.isPolyhedron).isPolygonal_of_isArcBetween
        (hinitArc i))
  have hPc : ∀ i : Fin 4, (T i ∩ E) ⊆ E := fun i => inter_subset_right
  have hPfc : ∀ i : Fin 4, (T i ∩ E) ∩ frontier E = {w i} := by
    intro i
    apply Subset.antisymm
    · intro x hx
      exact (hTfE i).subset ⟨hx.1.1, hx.2⟩
    · intro x hx
      have hxi : x = w i := mem_singleton_iff.mp hx
      subst x
      exact ⟨hinitArc i |>.right_mem, (hTfE i).symm.subset rfl |>.2⟩
  have hPTT : ∀ i j : Fin 4, i ≠ j → (T i ∩ E) ∩ (T j ∩ E) = {c} := by
    intro i j hij
    apply Subset.antisymm
    · intro x hx
      have hxy : x ∈ T i ∩ T j := ⟨hx.1.1, hx.2.1⟩
      rw [hTT i j hij] at hxy
      exact hxy
    · intro x hx
      have hxc : x = c := mem_singleton_iff.mp hx
      subst x
      exact ⟨⟨(hinitArc i).left_mem.1, interior_subset hcE⟩,
        ⟨(hinitArc j).left_mem.1, interior_subset hcE⟩⟩
  have hPrc : ∀ i : Fin 4, IsArcBetween (T i ∩ E) c (w i) := hinitArc
  have h := fourSpokeSector_spec hE hP hPrc hPc hPfc hPTT hcutE hw1 hw3 hβ
    hβ01 hβ01i hβ23 hβ23i
  simpa [fourSpokeSector] using h

private theorem cap_boundary_intersections_of_data
    {D E : Set Plane} {c : Plane}
    {T : Fin 4 → Set Plane} {v w : Fin 4 → Plane}
    {α β : Fin 4 → Set Plane}
    (hE : IsPLBall 2 E) (hEint : E ⊆ interior D)
    (hcE : c ∈ interior E)
    (hinit : ∀ i, IsInitialSpokeSegment (T i) E c (w i) (v i))
    (hTf : ∀ i, T i ∩ frontier D = {v i})
    (hTT : ∀ i j, i ≠ j → T i ∩ T j = {c})
    (hTfE : ∀ i, T i ∩ frontier E = {w i})
    (hα : ∀ i, IsArcBetween (α i) (v i) (v (i + 1)))
    (hαD : ∀ i, α i ⊆ frontier D)
    (hβ : ∀ i, IsArcBetween (β i) (w i) (w (i + 1)))
    (hβsub : ∀ i, β i ⊆ frontier E) :
    ∀ i,
      (T i \ interior E) ∩ α i = {v i} ∧
        ((T i \ interior E) ∪ α i) ∩ (T (i + 1) \ interior E) = {v (i + 1)} ∧
        ((T i \ interior E) ∪ α i ∪ (T (i + 1) \ interior E)) ∩ β i =
          {w i, w (i + 1)} := by
  intro i
  have hine : i ≠ i + 1 := by omega
  have hRi : (T i \ interior E) ∩ frontier D = {v i} := by
    apply Subset.antisymm
    · intro x hx
      exact (hTf i).subset ⟨sdiff_subset hx.1, hx.2⟩
    · intro x hx
      have hxi : x = v i := mem_singleton_iff.mp hx
      subst x
      exact ⟨(hinit i).outerArc.right_mem, (hTf i).symm.subset rfl |>.2⟩
  have hRiA : (T i \ interior E) ∩ α i = {v i} := by
    apply Subset.antisymm
    · intro x hx
      exact (hTf i).subset ⟨hx.1.1, hαD i hx.2⟩
    · intro x hx
      have hxi : x = v i := mem_singleton_iff.mp hx
      subst x
      exact ⟨(hinit i).outerArc.right_mem, (hα i).left_mem⟩
  have hRiRj : ∀ x ∈ T i \ interior E, x ∈ T (i + 1) \ interior E → x = c := by
    intro x hxi hxj
    exact mem_singleton_iff.mp ((hTT i (i + 1) hine).subset ⟨hxi.1, hxj.1⟩)
  have hRj : (T (i + 1) \ interior E) ∩ frontier D = {v (i + 1)} := by
    apply Subset.antisymm
    · intro x hx
      exact (hTf (i + 1)).subset ⟨sdiff_subset hx.1, hx.2⟩
    · intro x hx
      have hxi : x = v (i + 1) := mem_singleton_iff.mp hx
      subst x
      exact ⟨(hinit (i + 1)).outerArc.right_mem,
        (hTf (i + 1)).symm.subset rfl |>.2⟩
  have hRjA : α i ∩ (T (i + 1) \ interior E) = {v (i + 1)} := by
    apply Subset.antisymm
    · intro x hx
      exact (hTf (i + 1)).subset ⟨hx.2.1, hαD i hx.1⟩
    · intro x hx
      have hxi : x = v (i + 1) := mem_singleton_iff.mp hx
      subst x
      exact ⟨(hα i).right_mem, (hinit (i + 1)).outerArc.right_mem⟩
  have hRR : ((T i \ interior E) ∪ α i) ∩ (T (i + 1) \ interior E) =
      {v (i + 1)} := by
    apply Subset.antisymm
    · rintro x ⟨hx, hxj⟩
      rcases hx with hxi | hxa
      · have hxc := hRiRj x hxi hxj
        exact (hxi.2 (hxc ▸ hcE)).elim
      · exact hRjA.subset ⟨hxa, hxj⟩
    · intro x hx
      have hxi : x = v (i + 1) := mem_singleton_iff.mp hx
      subst x
      exact ⟨Or.inr (hα i).right_mem, (hinit (i + 1)).outerArc.right_mem⟩
  have hRiβ : ∀ x ∈ T i \ interior E, x ∈ β i → x = w i := by
    intro x hxr hxb
    exact mem_singleton_iff.mp ((hTfE i).subset ⟨hxr.1, hβsub i hxb⟩)
  have hRjβ : ∀ x ∈ T (i + 1) \ interior E, x ∈ β i → x = w (i + 1) := by
    intro x hxr hxb
    exact mem_singleton_iff.mp ((hTfE (i + 1)).subset ⟨hxr.1, hβsub i hxb⟩)
  have hαβ : Disjoint (α i) (β i) := by
    have hdis : Disjoint (frontier E) (frontier D) := by
      apply disjoint_left.mpr
      intro x hxE hxfr
      have hxE' : x ∈ E := hE.isPolyhedron.isClosed.frontier_subset hxE
      exact (mem_interior_iff_notMem_frontier (interior_subset (hEint hxE'))).mp
        (hEint hxE') hxfr
    apply disjoint_left.mpr
    intro x hxa hxb
    exact Set.disjoint_left.mp hdis (hβsub i hxb) (hαD i hxa)
  have hOβ : ((T i \ interior E) ∪ α i ∪ (T (i + 1) \ interior E)) ∩ β i =
      {w i, w (i + 1)} := by
    apply Subset.antisymm
    · rintro x ⟨hx, hxb⟩
      rcases hx with hx01 | hxj
      · rcases hx01 with hxi | hxa
        · exact by simp [hRiβ x hxi hxb]
        · exact (hαβ.le_bot ⟨hxa, hxb⟩).elim
      · exact by simp [hRjβ x hxj hxb]
    · intro x hx
      simp only [mem_insert_iff, mem_singleton_iff] at hx
      rcases hx with rfl | rfl
      · exact ⟨Or.inl (Or.inl (hinit i).outerArc.left_mem),
          (hβ i).left_mem⟩
      · exact ⟨Or.inr (hinit (i + 1)).outerArc.left_mem,
          (hβ i).right_mem⟩
  exact ⟨hRiA, hRR, hOβ⟩

private theorem outer_cap_meets_bounding_spoke
    {S Ω T₀ T₁ A β R₀ R₁ : Set Plane} {c w₀ w₁ v₀ v₁ : Plane}
    (hΩclosed : IsClosed Ω) (hΩsub : Ω ⊆ S)
    (hΩfront : frontier Ω = R₀ ∪ A ∪ R₁ ∪ β)
    (hT₀front : T₀ ⊆ frontier S) (hT₁front : T₁ ⊆ frontier S)
    (hT₀A : T₀ ∩ A = {v₀}) (hT₁A : A ∩ T₁ = {v₁})
    (hT₀T₁ : T₀ ∩ T₁ = {c}) (hcR₁ : c ∉ R₁) (hcR₀ : c ∉ R₀)
    (hT₀β : T₀ ∩ β = {w₀}) (hT₁β : T₁ ∩ β = {w₁})
    (hw₀R₀ : w₀ ∈ R₀) (hw₁R₁ : w₁ ∈ R₁)
    (hv₀R₀ : v₀ ∈ R₀) (hv₁R₁ : v₁ ∈ R₁)
    (hR₀sub : R₀ ⊆ T₀) (hR₁sub : R₁ ⊆ T₁) :
    Ω ∩ T₀ = R₀ ∧ Ω ∩ T₁ = R₁ := by
  have hT₀Ω : Ω ∩ T₀ ⊆ R₀ := by
    intro x hx
    have hxfr : x ∈ frontier Ω := by
      refine ⟨subset_closure hx.1, ?_⟩
      intro hxint
      have hxintS : x ∈ interior S := interior_mono hΩsub hxint
      exact (hT₀front hx.2).2 hxintS
    rw [hΩfront] at hxfr
    rcases hxfr with hxall | hxβ
    · rcases hxall with hx01 | hxR₁
      · rcases hx01 with hxR₀ | hxA
        · exact hxR₀
        · exact mem_singleton_iff.mp (hT₀A.subset ⟨hx.2, hxA⟩) ▸ hv₀R₀
      · have hxc : x = c := mem_singleton_iff.mp
          (hT₀T₁.subset ⟨hx.2, hR₁sub hxR₁⟩)
        exact (hcR₁ (hxc ▸ hxR₁)).elim
    · have hxw : x = w₀ := mem_singleton_iff.mp
        (hT₀β.subset ⟨hx.2, hxβ⟩)
      exact hxw ▸ hw₀R₀
  have hT₁Ω : Ω ∩ T₁ ⊆ R₁ := by
    intro x hx
    have hxfr : x ∈ frontier Ω := by
      refine ⟨subset_closure hx.1, ?_⟩
      intro hxint
      have hxintS : x ∈ interior S := interior_mono hΩsub hxint
      exact (hT₁front hx.2).2 hxintS
    rw [hΩfront] at hxfr
    rcases hxfr with hxall | hxβ
    · rcases hxall with hx01 | hxR₁
      · rcases hx01 with hxR₀ | hxA
        · have hxc : x = c := mem_singleton_iff.mp
            (hT₀T₁.subset ⟨hR₀sub hxR₀, hx.2⟩)
          exact (hcR₀ (hxc ▸ hxR₀)).elim
        · exact mem_singleton_iff.mp (hT₁A.subset ⟨hxA, hx.2⟩) ▸ hv₁R₁
      · exact hxR₁
    · have hxw : x = w₁ := mem_singleton_iff.mp
        (hT₁β.subset ⟨hx.2, hxβ⟩)
      exact hxw ▸ hw₁R₁
  refine ⟨Subset.antisymm hT₀Ω (fun x hx => hΩclosed.closure_eq ▸
      ⟨frontier_subset_closure (by rw [hΩfront]; exact Or.inl (Or.inl (Or.inl hx))),
        hR₀sub hx⟩),
    Subset.antisymm hT₁Ω (fun x hx => hΩclosed.closure_eq ▸
      ⟨frontier_subset_closure (by rw [hΩfront]; exact Or.inl (Or.inr hx)),
        hR₁sub hx⟩)⟩

private theorem opposite_spoke_inter_sector
    {D S T T₀ T₁ A : Set Plane} {c v : Plane}
    (hS : IsPLBall 2 S) (harc : IsArcBetween T c v)
    (hfront : frontier S = T₀ ∪ A ∪ T₁)
    (hT₀ : T ∩ T₀ = {c}) (hT₁ : T ∩ T₁ = {c})
    (hTf : T ∩ frontier D = {v})
    (hαD : A ⊆ frontier D) (hvα : v ∉ A)
    (hSfrontD : S ∩ frontier D = A) :
    T ∩ S ⊆ {c} := by
  have hdis : Disjoint (T \ {c, v}) (frontier S) := by
    apply disjoint_left.mpr
    intro x hx hxfr
    rw [hfront] at hxfr
    rcases hxfr with hx01 | hx₁
    · rcases hx01 with hx₀ | hxA
      · have hxc : x = c := mem_singleton_iff.mp (hT₀.subset ⟨hx.1, hx₀⟩)
        exact hx.2 (by simp [hxc])
      · have hxv : x = v := mem_singleton_iff.mp
          (hTf.subset ⟨hx.1, hαD hxA⟩)
        exact hx.2 (by simp [hxv])
    · have hxc : x = c := mem_singleton_iff.mp (hT₁.subset ⟨hx.1, hx₁⟩)
      exact hx.2 (by simp [hxc])
  have hvS : v ∉ S := by
    intro hvS
    have hvfr : v ∈ frontier D := (hTf.symm.subset rfl).2
    exact hvα (hSfrontD.subset ⟨hvS, hvfr⟩)
  exact arc_inter_subset_singleton_of_notMem hS.isPolyhedron.isClosed harc hdis hvS

private theorem boundary_arc_avoids_opposite_endpoint
    {D A₁ A₂ : Set Plane} {v : Fin 4 → Plane} {α : Fin 4 → Set Plane}
    (hcut : IsCutPair (frontier D) (v 0) (v 2) A₁ A₂)
    (hv1 : v 1 ∈ A₁) (hv3 : v 3 ∈ A₂)
    (hα : ∀ i, IsArcBetween (α i) (v i) (v (i + 1)))
    (hα01 : α 0 ∪ α 1 = A₁) (hα01i : α 0 ∩ α 1 = {v 1})
    (hα23 : α 2 ∪ α 3 = A₂) (hα23i : α 2 ∩ α 3 = {v 3})
    (hvne : ∀ i j : Fin 4, i ≠ j → v i ≠ v j) :
    ∀ i k, k ≠ i → k ≠ i + 1 → v k ∉ α i := by
  have hα0A₁ : α 0 ⊆ A₁ := by rw [← hα01]; exact subset_union_left
  have hα1A₁ : α 1 ⊆ A₁ := by rw [← hα01]; exact subset_union_right
  have hα2A₂ : α 2 ⊆ A₂ := by rw [← hα23]; exact subset_union_left
  have hα3A₂ : α 3 ⊆ A₂ := by rw [← hα23]; exact subset_union_right
  have hv0α0 : v 0 ∈ α 0 := (hα 0).left_mem
  have hv1α0 : v 1 ∈ α 0 := (hα 0).right_mem
  have hv1α1 : v 1 ∈ α 1 := (hα 1).left_mem
  have hv2α1 : v 2 ∈ α 1 := (hα 1).right_mem
  have hv2α2 : v 2 ∈ α 2 := (hα 2).left_mem
  have hv3α2 : v 3 ∈ α 2 := (hα 2).right_mem
  have hv3α3 : v 3 ∈ α 3 := (hα 3).left_mem
  have hv0α3 : v 0 ∈ α 3 := (hα 3).right_mem
  have hv2notα0 : v 2 ∉ α 0 := by
    intro hx
    have hm : v 2 ∈ α 0 ∩ α 1 := ⟨hx, hv2α1⟩
    rw [hα01i] at hm
    exact hvne 2 1 (by decide) (mem_singleton_iff.mp hm)
  have hv0notα1 : v 0 ∉ α 1 := by
    intro hx
    have hm : v 0 ∈ α 0 ∩ α 1 := ⟨hv0α0, hx⟩
    rw [hα01i] at hm
    exact hvne 0 1 (by decide) (mem_singleton_iff.mp hm)
  have hv0notα2 : v 0 ∉ α 2 := by
    intro hx
    have hm : v 0 ∈ α 2 ∩ α 3 := ⟨hx, hv0α3⟩
    rw [hα23i] at hm
    exact hvne 0 3 (by decide) (mem_singleton_iff.mp hm)
  have hv2notα3 : v 2 ∉ α 3 := by
    intro hx
    have hm : v 2 ∈ α 2 ∩ α 3 := ⟨hv2α2, hx⟩
    rw [hα23i] at hm
    exact hvne 2 3 (by decide) (mem_singleton_iff.mp hm)
  have hv3notA₁ : v 3 ∉ A₁ := by
    intro hx
    have hm : v 3 ∈ A₁ ∩ A₂ := ⟨hx, hv3⟩
    rw [hcut.inter_eq] at hm
    rcases hm with hm | hm
    · exact hvne 3 0 (by decide) hm
    · exact hvne 3 2 (by decide) hm
  have hv1notA₂ : v 1 ∉ A₂ := by
    intro hx
    have hm : v 1 ∈ A₁ ∩ A₂ := ⟨hv1, hx⟩
    rw [hcut.inter_eq] at hm
    rcases hm with hm | hm
    · exact hvne 1 0 (by decide) hm
    · exact hvne 1 2 (by decide) hm
  intro i k hik hik1
  fin_cases i
  · fin_cases k
    · exact (hik rfl).elim
    · exact (hik1 (by decide)).elim
    · exact hv2notα0
    · intro hk
      exact hv3notA₁ (hα0A₁ hk)
  · fin_cases k
    · exact hv0notα1
    · exact (hik rfl).elim
    · exact (hik1 (by decide)).elim
    · intro hk
      exact hv3notA₁ (hα1A₁ hk)
  · fin_cases k
    · exact hv0notα2
    · intro hk
      exact hv1notA₂ (hα2A₂ hk)
    · exact (hik rfl).elim
    · exact (hik1 (by decide)).elim
  · fin_cases k
    · exact (hik1 (by decide)).elim
    · intro hk
      exact hv1notA₂ (hα3A₂ hk)
    · exact hv2notα3
    · exact (hik rfl).elim

theorem exists_isPLHomeomorphOn_cap_boundary
    {R₀ A R₁ β R₀' A' R₁' β' : Set Plane}
    {w₀ w₁ v₀ v₁ w₀' w₁' v₀' v₁' : Plane}
    (hR₀ : IsPolyhedron R₀) (hA : IsPolyhedron A) (hR₁ : IsPolyhedron R₁)
    (hβ : IsPolyhedron β)
    {r₀ r₁ a b : Plane → Plane}
    (hr₀ : IsPLHomeomorphOn r₀ R₀ R₀') (ha : IsPLHomeomorphOn a A A')
    (hr₁ : IsPLHomeomorphOn r₁ R₁ R₁') (hb : IsPLHomeomorphOn b β β')
    (hR₀A : R₀ ∩ A = {v₀}) (hR₀A' : R₀' ∩ A' = {v₀'})
    (hR₀AR₁ : (R₀ ∪ A) ∩ R₁ = {v₁})
    (hR₀AR₁' : (R₀' ∪ A') ∩ R₁' = {v₁'})
    (houterβ : (R₀ ∪ A ∪ R₁) ∩ β = {w₀, w₁})
    (houterβ' : (R₀' ∪ A' ∪ R₁') ∩ β' = {w₀', w₁'})
    (hw₀R₀ : w₀ ∈ R₀) (hw₁R₁ : w₁ ∈ R₁)
    (hw₀β : w₀ ∈ β) (hw₁β : w₁ ∈ β)
    (hw₀'R₀' : w₀' ∈ R₀') (hw₁'R₁' : w₁' ∈ R₁')
    (hw₀'β' : w₀' ∈ β') (hw₁'β' : w₁' ∈ β')
    (hv₁A : v₁ ∈ A)
    (hr₀v : r₀ v₀ = v₀') (hav : a v₀ = v₀')
    (hav₁ : a v₁ = v₁') (hr₁v : r₁ v₁ = v₁')
    (hr₀w : r₀ w₀ = w₀') (hbw₀ : b w₀ = w₀')
    (hr₁w : r₁ w₁ = w₁') (hbw₁ : b w₁ = w₁') :
    ∃ h : Plane → Plane,
      IsPLHomeomorphOn h (R₀ ∪ A ∪ R₁ ∪ β) (R₀' ∪ A' ∪ R₁' ∪ β') ∧
        EqOn h r₀ R₀ ∧ EqOn h a A ∧ EqOn h r₁ R₁ ∧ EqOn h b β := by
  have hEq₀ : EqOn r₀ a (R₀ ∩ A) := by
    rw [hR₀A]
    intro x hx
    simpa [mem_singleton_iff.mp hx] using hr₀v.trans hav.symm
  have hSurj₀ : SurjOn r₀ (R₀ ∩ A) (R₀' ∩ A') := by
    rw [hR₀A, hR₀A']
    intro y hy
    have hy' : y = v₀' := mem_singleton_iff.mp hy
    exact ⟨v₀, by simp, by simpa [hy'] using hr₀v⟩
  obtain ⟨h₀, hh₀, h₀R, h₀A⟩ := exists_isPLHomeomorphOn_union hR₀ hA hr₀ ha hEq₀ hSurj₀
  have hEq₁ : EqOn h₀ r₁ ((R₀ ∪ A) ∩ R₁) := by
    rw [hR₀AR₁]
    intro x hx
    have hxv : x = v₁ := mem_singleton_iff.mp hx
    subst x
    exact (h₀A hv₁A).trans (hav₁.trans hr₁v.symm)
  have hSurj₁ : SurjOn h₀ ((R₀ ∪ A) ∩ R₁) ((R₀' ∪ A') ∩ R₁') := by
    rw [hR₀AR₁, hR₀AR₁']
    intro y hy
    have hy' : y = v₁' := mem_singleton_iff.mp hy
    exact ⟨v₁, by simp, by simpa [hy'] using (h₀A hv₁A).trans hav₁⟩
  obtain ⟨h₁, hh₁, h₁₀, h₁R⟩ := exists_isPLHomeomorphOn_union (hR₀.union hA) hR₁ hh₀ hr₁
    hEq₁ hSurj₁
  have hEq₂ : EqOn h₁ b ((R₀ ∪ A ∪ R₁) ∩ β) := by
    rw [houterβ]
    intro x hx
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rcases hx with rfl | rfl
    · exact ((h₁₀ (Or.inl hw₀R₀)).trans (h₀R hw₀R₀)).trans
        (hr₀w.trans hbw₀.symm)
    · exact ((h₁R hw₁R₁).trans hr₁w).trans hbw₁.symm
  have hSurj₂ : SurjOn h₁ ((R₀ ∪ A ∪ R₁) ∩ β)
      ((R₀' ∪ A' ∪ R₁') ∩ β') := by
    rw [houterβ, houterβ']
    intro y hy
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hy
    rcases hy with rfl | rfl
    · have heq := hEq₂ (show w₀ ∈ (R₀ ∪ A ∪ R₁) ∩ β by
        rw [houterβ]; simp)
      exact ⟨w₀, by simp, heq.trans hbw₀⟩
    · have heq := hEq₂ (show w₁ ∈ (R₀ ∪ A ∪ R₁) ∩ β by
        rw [houterβ]; simp)
      exact ⟨w₁, by simp, heq.trans hbw₁⟩
  obtain ⟨h, hh, hh₁, hβ⟩ := exists_isPLHomeomorphOn_union ((hR₀.union hA).union hR₁)
    hβ hh₁ hb hEq₂ hSurj₂
  refine ⟨h, hh, ?_, ?_, ?_, hβ⟩
  · intro x hx
    exact (hh₁ (Or.inl (Or.inl hx))).trans
      ((h₁₀ (Or.inl hx)).trans (h₀R hx))
  · intro x hx
    exact (hh₁ (Or.inl (Or.inr hx))).trans
      ((h₁₀ (Or.inr hx)).trans (h₀A hx))
  · intro x hx
    exact (hh₁ (Or.inr hx)).trans (h₁R hx)

private theorem exists_isPLHomeomorphOn_iUnion_union
    {ι : Type*} [Finite ι]
    {V W : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
    [NormedAddCommGroup W] [NormedSpace ℝ W] [FiniteDimensional ℝ W]
    {E : Set V} {E' : Set W} {Ω β : ι → Set V} {Ω' β' : ι → Set W}
    {g : V → W} {f : ι → V → W}
    (hΩ : ∀ i, IsPolyhedron (Ω i)) (hE : IsPolyhedron E)
    (hf : ∀ i, IsPLHomeomorphOn (f i) (Ω i) (Ω' i))
    (hg : IsPLHomeomorphOn g E E')
    (hinter : ∀ i, Ω i ∩ E = β i) (hinter' : ∀ i, Ω' i ∩ E' = β' i)
    (hfg : ∀ i, EqOn (f i) g (β i)) (hgβ : ∀ i, g '' β i = β' i)
    (hcompat : ∀ i j, EqOn (f i) (f j) (Ω i ∩ Ω j))
    (hmeet : ∀ i j, f i '' (Ω i ∩ Ω j) = Ω' i ∩ Ω' j) :
    ∃ F : V → W,
      IsPLHomeomorphOn F ((⋃ i, Ω i) ∪ E) ((⋃ i, Ω' i) ∪ E') ∧
        EqOn F g E ∧ ∀ i, EqOn F (f i) (Ω i) := by
  obtain ⟨H, hH, hHf⟩ := exists_isPLHomeomorphOn_iUnion hΩ hf hcompat hmeet
  have hHg : EqOn H g ((⋃ i, Ω i) ∩ E) := by
    intro x hx
    obtain ⟨i, hxi⟩ := mem_iUnion.mp hx.1
    exact (hHf i hxi).trans (hfg i ((hinter i).subset ⟨hxi, hx.2⟩))
  have hsurj : SurjOn H ((⋃ i, Ω i) ∩ E) ((⋃ i, Ω' i) ∩ E') := by
    intro y hy
    obtain ⟨i, hyi⟩ := mem_iUnion.mp hy.1
    have hyβ : y ∈ β' i := (hinter' i).subset ⟨hyi, hy.2⟩
    obtain ⟨x, hxβ, hgxy⟩ := (hgβ i).symm.subset hyβ
    have hx : x ∈ Ω i ∩ E := (hinter i).symm.subset hxβ
    refine ⟨x, ⟨mem_iUnion.mpr ⟨i, hx.1⟩, hx.2⟩, ?_⟩
    exact (hHf i hx.1).trans ((hfg i hxβ).trans hgxy)
  obtain ⟨F, hF, hFH, hFg⟩ :=
    exists_isPLHomeomorphOn_union (IsPolyhedron.iUnion hΩ) hE hH hg hHg hsurj
  refine ⟨F, hF, hFg, ?_⟩
  intro i x hx
  exact (hFH (mem_iUnion.mpr ⟨i, hx⟩)).trans (hHf i hx)


theorem exists_isPLHomeomorphOn_fourSpokeCap
    {D D' E E' A₁ A₂ B₁ B₂ A₁' A₂' B₁' B₂' : Set Plane} {c c' : Plane}
    {T T' : Fin 4 → Set Plane} {v v' w w' : Fin 4 → Plane}
    {α β α' β' : Fin 4 → Set Plane}
    {π : Equiv.Perm (Fin 4)} {g γ : Plane → Plane}
    {r : Fin 4 → Plane → Plane}
    (hD : IsPLBall 2 D) (hD' : IsPLBall 2 D')
    (hE : IsPLBall 2 E) (hE' : IsPLBall 2 E')
    (hEint : E ⊆ interior D) (hEint' : E' ⊆ interior D')
    (hcE : c ∈ interior E) (hcE' : c' ∈ interior E')
    (hT : ∀ i, IsPLBall 1 (T i)) (hT' : ∀ i, IsPLBall 1 (T' i))
    (harc : ∀ i, IsArcBetween (T i) c (v i))
    (harc' : ∀ i, IsArcBetween (T' i) c' (v' i))
    (hTD : ∀ i, T i ⊆ D) (hTD' : ∀ i, T' i ⊆ D')
    (hTf : ∀ i, T i ∩ frontier D = {v i})
    (hTf' : ∀ i, T' i ∩ frontier D' = {v' i})
    (hTT : ∀ i j, i ≠ j → T i ∩ T j = {c})
    (hTT' : ∀ i j, i ≠ j → T' i ∩ T' j = {c'})
    (hTfE : ∀ i, T i ∩ frontier E = {w i})
    (hTfE' : ∀ i, T' i ∩ frontier E' = {w' i})
    (hcut : IsCutPair (frontier D) (v 0) (v 2) A₁ A₂)
    (hv1 : v 1 ∈ A₁) (hv3 : v 3 ∈ A₂)
    (hcutE : IsCutPair (frontier E) (w 0) (w 2) B₁ B₂)
    (hw1 : w 1 ∈ B₁) (hw3 : w 3 ∈ B₂)
    (hα : ∀ i, IsArcBetween (α i) (v i) (v (i + 1)))
    (hα01 : α 0 ∪ α 1 = A₁) (hα01i : α 0 ∩ α 1 = {v 1})
    (hα23 : α 2 ∪ α 3 = A₂) (hα23i : α 2 ∩ α 3 = {v 3})
    (hβ : ∀ i, IsArcBetween (β i) (w i) (w (i + 1)))
    (hβ01 : β 0 ∪ β 1 = B₁) (hβ01i : β 0 ∩ β 1 = {w 1})
    (hβ23 : β 2 ∪ β 3 = B₂) (hβ23i : β 2 ∩ β 3 = {w 3})
    (hcut' : IsCutPair (frontier D') (v' (π 0)) (v' (π 2)) A₁' A₂')
    (hv1' : v' (π 1) ∈ A₁') (hv3' : v' (π 3) ∈ A₂')
    (hcutE' : IsCutPair (frontier E') (w' (π 0)) (w' (π 2)) B₁' B₂')
    (hw1' : w' (π 1) ∈ B₁') (hw3' : w' (π 3) ∈ B₂')
    (hα' : ∀ i, IsArcBetween (α' i) (v' (π i)) (v' (π (i + 1))))
    (hα'01 : α' 0 ∪ α' 1 = A₁') (hα'01i : α' 0 ∩ α' 1 = {v' (π 1)})
    (hα'23 : α' 2 ∪ α' 3 = A₂') (hα'23i : α' 2 ∩ α' 3 = {v' (π 3)})
    (hβ' : ∀ i, IsArcBetween (β' i) (w' (π i)) (w' (π (i + 1))))
    (hβ'01 : β' 0 ∪ β' 1 = B₁') (hβ'01i : β' 0 ∩ β' 1 = {w' (π 1)})
    (hβ'23 : β' 2 ∪ β' 3 = B₂') (hβ'23i : β' 2 ∩ β' 3 = {w' (π 3)})
    (hg : IsPLHomeomorphOn g E E')
    (hgT : ∀ i, g '' (T i ∩ E) = T' (π i) ∩ E')
    (hγ : IsPLHomeomorphOn γ (frontier D) (frontier D'))
    (hγv : ∀ i, γ (v i) = v' (π i))
    (hαmap : ∀ i, γ '' α i = α' i) (hβmap : ∀ i, g '' β i = β' i)
    (hr : ∀ i, IsPLHomeomorphOn (r i) (T i \ interior E)
      (T' (π i) \ interior E'))
    (hrw : ∀ i, r i (w i) = g (w i))
    (hrv : ∀ i, r i (v i) = γ (v i)) :
    ∃ F : Plane → Plane, IsPLHomeomorphOn F D D' ∧ EqOn F g E ∧
      EqOn F γ (frontier D) ∧
        ∀ i, EqOn F (r i) (T i \ interior E) ∧ F '' T i = T' (π i) := by
  classical
  have hvne : ∀ i j : Fin 4, i ≠ j → v i ≠ v j := by
    intro i j hij h
    have hm : v i ∈ T i ∩ T j := ⟨(harc i).right_mem, by rw [h]; exact (harc j).right_mem⟩
    rw [hTT i j hij] at hm
    exact ne_of_isArcBetween (harc i) (mem_singleton_iff.mp hm).symm
  have hvE : ∀ i : Fin 4, v i ∉ E := by
    intro i hvi
    have hviint : v i ∈ interior D := hEint hvi
    have hvif : v i ∈ frontier D := (hTf i).symm.subset rfl |>.2
    exact (mem_interior_iff_notMem_frontier (interior_subset hviint)).mp hviint hvif
  have hinit : ∀ i : Fin 4, IsInitialSpokeSegment (T i) E c (w i) (v i) := by
    intro i
    exact isInitialSpokeSegment_of_isArcBetween hE.isPolyhedron.isClosed (harc i)
      (hTfE i) hcE (hvE i)
  have hTₚ : ∀ i : Fin 4, IsPLBall 1 (T' (π i)) := by
    intro i
    exact hT' (π i)
  have harcₚ : ∀ i : Fin 4, IsArcBetween (T' (π i)) c' (v' (π i)) := by
    intro i
    exact harc' (π i)
  have hTDₚ : ∀ i : Fin 4, T' (π i) ⊆ D' := fun i => hTD' (π i)
  have hTfₚ : ∀ i : Fin 4, T' (π i) ∩ frontier D' = {v' (π i)} :=
    fun i => hTf' (π i)
  have hTTₚ : ∀ i j : Fin 4, i ≠ j → T' (π i) ∩ T' (π j) = {c'} := by
    intro i j hij
    exact hTT' (π i) (π j) (π.injective.ne hij)
  have hTfEₚ : ∀ i : Fin 4, T' (π i) ∩ frontier E' = {w' (π i)} :=
    fun i => hTfE' (π i)
  have hvEₚ : ∀ i : Fin 4, v' (π i) ∉ E' := by
    intro i hvi
    have hviint : v' (π i) ∈ interior D' := hEint' hvi
    have hvif : v' (π i) ∈ frontier D' := (hTfₚ i).symm.subset rfl |>.2
    exact (mem_interior_iff_notMem_frontier (interior_subset hviint)).mp hviint hvif
  have hinitₚ : ∀ i : Fin 4,
      IsInitialSpokeSegment (T' (π i)) E' c' (w' (π i)) (v' (π i)) := by
    intro i
    exact isInitialSpokeSegment_of_isArcBetween hE'.isPolyhedron.isClosed (harcₚ i)
      (hTfEₚ i) hcE' (hvEₚ i)
  obtain ⟨hsector, hβcross⟩ := fourSpokeCap_sector_data_of_arcs hD hE hEint hcE hT harc
    hTD hTf hTT hTfE hcut hv1 hv3 hcutE hα hα01 hα01i hα23 hα23i hβ
    hβ01 hβ01i hβ23 hβ23i
  obtain ⟨hsectorₚ, hβcrossₚ⟩ := fourSpokeCap_sector_data_of_arcs hD' hE' hEint' hcE'
    hTₚ harcₚ hTDₚ hTfₚ hTTₚ hTfEₚ hcut' hv1' hv3' hcutE' hα' hα'01 hα'01i
    hα'23 hα'23i hβ' hβ'01 hβ'01i hβ'23 hβ'23i
  obtain ⟨-, hsectorCover, hsectorInter⟩ := fourSpokeSector_spec hD hT harc
    hTD hTf hTT hcut hv1 hv3 hα hα01 hα01i hα23 hα23i
  obtain ⟨-, hsectorCoverₚ, hsectorInterₚ⟩ := fourSpokeSector_spec hD' hTₚ harcₚ
    hTDₚ hTfₚ hTTₚ hcut' hv1' hv3' hα' hα'01 hα'01i hα'23 hα'23i
  have hαD : ∀ i : Fin 4, α i ⊆ frontier D := by
    intro i
    fin_cases i
    · intro x hx; exact hcut.fst_subset (hα01 ▸ Or.inl hx)
    · intro x hx; exact hcut.fst_subset (hα01 ▸ Or.inr hx)
    · intro x hx; exact hcut.snd_subset (hα23 ▸ Or.inl hx)
    · intro x hx; exact hcut.snd_subset (hα23 ▸ Or.inr hx)
  have hαDₚ : ∀ i : Fin 4, α' i ⊆ frontier D' := by
    intro i
    fin_cases i
    · intro x hx; exact hcut'.fst_subset (hα'01 ▸ Or.inl hx)
    · intro x hx; exact hcut'.fst_subset (hα'01 ▸ Or.inr hx)
    · intro x hx; exact hcut'.snd_subset (hα'23 ▸ Or.inl hx)
    · intro x hx; exact hcut'.snd_subset (hα'23 ▸ Or.inr hx)
  have hβsub : ∀ i : Fin 4, β i ⊆ frontier E := by
    intro i
    fin_cases i
    · intro x hx; exact hcutE.fst_subset (hβ01 ▸ Or.inl hx)
    · intro x hx; exact hcutE.fst_subset (hβ01 ▸ Or.inr hx)
    · intro x hx; exact hcutE.snd_subset (hβ23 ▸ Or.inl hx)
    · intro x hx; exact hcutE.snd_subset (hβ23 ▸ Or.inr hx)
  have hβsubₚ : ∀ i : Fin 4, β' i ⊆ frontier E' := by
    intro i
    fin_cases i
    · intro x hx; exact hcutE'.fst_subset (hβ'01 ▸ Or.inl hx)
    · intro x hx; exact hcutE'.fst_subset (hβ'01 ▸ Or.inr hx)
    · intro x hx; exact hcutE'.snd_subset (hβ'23 ▸ Or.inl hx)
    · intro x hx; exact hcutE'.snd_subset (hβ'23 ▸ Or.inr hx)
  obtain ⟨hinner, hinnerCover, -⟩ := inner_sector_spec_of_fourSpokeCap hE hcE hT
    (fun i => (hinit i).initialArc) hTfE hTT hcutE hw1 hw3 hβ hβ01 hβ01i hβ23 hβ23i
  obtain ⟨hinnerₚ, hinnerCoverₚ, -⟩ := inner_sector_spec_of_fourSpokeCap hE' hcE'
    hTₚ (fun i => (hinitₚ i).initialArc) hTfEₚ hTTₚ hcutE' hw1' hw3' hβ' hβ'01
    hβ'01i hβ'23 hβ'23i
  let R : Fin 4 → Set Plane := fun i => T i \ interior E
  let P : Fin 4 → Set Plane := fun i => T i ∩ E
  let S : Fin 4 → Set Plane := fun i => fourSpokeSector T α i
  let Rₚ : Fin 4 → Set Plane := fun i => T' (π i) \ interior E'
  let Pₚ : Fin 4 → Set Plane := fun i => T' (π i) ∩ E'
  let Sₚ : Fin 4 → Set Plane := fun i => fourSpokeSector (fun j => T' (π j)) α' i
  let O : Fin 4 → Set Plane := fun i => R i ∪ α i ∪ R (i + 1)
  let I : Fin 4 → Set Plane := fun i => P i ∪ P (i + 1)
  let Oₚ : Fin 4 → Set Plane := fun i => Rₚ i ∪ α' i ∪ Rₚ (i + 1)
  let Iₚ : Fin 4 → Set Plane := fun i => Pₚ i ∪ Pₚ (i + 1)
  let Ω : Fin 4 → Set Plane := fun i => closure (inside (O i ∪ β i))
  let K : Fin 4 → Set Plane := fun i => closure (inside (I i ∪ β i))
  let Ωₚ : Fin 4 → Set Plane := fun i => closure (inside (Oₚ i ∪ β' i))
  let Kₚ : Fin 4 → Set Plane := fun i => closure (inside (Iₚ i ∪ β' i))
  have hcap : ∀ i, IsCutPair (frontier (S i)) (w i) (w (i + 1)) (O i) (I i) := by
    intro i
    simpa [S, O, I, R, P] using isCutPair_cap_sector_of_fourSpokeData hE hEint hcE harc
      hTf hTT hTfE hα hαD hsector i
  have hcapₚ : ∀ i, IsCutPair (frontier (Sₚ i)) (w' (π i)) (w' (π (i + 1)))
      (Oₚ i) (Iₚ i) := by
    intro i
    simpa [Sₚ, Oₚ, Iₚ, Rₚ, Pₚ] using
      isCutPair_cap_sector_of_fourSpokeData hE' hEint' hcE' harcₚ hTfₚ hTTₚ hTfEₚ hα'
        hαDₚ hsectorₚ i
  have hβball : ∀ i, IsPLBall 1 (β i) := by
    intro i
    exact isPLBall_of_isArc_subset_isPLSphere hE.isPLSphere_frontier (hβ i).isArc (hβsub i)
  have hβballₚ : ∀ i, IsPLBall 1 (β' i) := by
    intro i
    exact isPLBall_of_isArc_subset_isPLSphere hE'.isPLSphere_frontier (hβ' i).isArc
      (hβsubₚ i)
  have hΩball : ∀ i, IsPLBall 2 (Ω i) := by
    intro i
    simpa [Ω] using (isPLBall_closure_inside_arc_union (hsector i).1 (hβball i)
      (hβcross i) (hcap i)).1
  have hΩfront : ∀ i, frontier (Ω i) = O i ∪ β i := by
    intro i
    simpa [Ω] using (isPLBall_closure_inside_arc_union (hsector i).1 (hβball i)
      (hβcross i) (hcap i)).2
  have hΩballₚ : ∀ i, IsPLBall 2 (Ωₚ i) := by
    intro i
    simpa [Ωₚ] using (isPLBall_closure_inside_arc_union (hsectorₚ i).1 (hβballₚ i)
      (hβcrossₚ i) (hcapₚ i)).1
  have hΩfrontₚ : ∀ i, frontier (Ωₚ i) = Oₚ i ∪ β' i := by
    intro i
    simpa [Ωₚ] using (isPLBall_closure_inside_arc_union (hsectorₚ i).1 (hβballₚ i)
      (hβcrossₚ i) (hcapₚ i)).2
  have hsplit : ∀ i, Ω i ∪ K i = S i ∧ Ω i ∩ K i = β i := by
    intro i
    simpa [Ω, K, O, I] using
      closure_inside_arc_union_union_and_inter (hsector i).1 (hβcross i) (hcap i)
  have hsplitₚ : ∀ i, Ωₚ i ∪ Kₚ i = Sₚ i ∧ Ωₚ i ∩ Kₚ i = β' i := by
    intro i
    simpa [Ωₚ, Kₚ, Oₚ, Iₚ] using
      closure_inside_arc_union_union_and_inter (hsectorₚ i).1 (hβcrossₚ i) (hcapₚ i)
  have hKball : ∀ i, IsPLBall 2 (K i) := by
    intro i
    have hu : (P i ∪ P (i + 1)) ∪ β i = P i ∪ β i ∪ P (i + 1) := by
      ext x
      simp only [mem_union]
      tauto
    dsimp [K, I]
    rw [hu]
    simpa [P] using (hinner i).1
  have hKfront : ∀ i, frontier (K i) = P i ∪ β i ∪ P (i + 1) := by
    intro i
    have hu : (P i ∪ P (i + 1)) ∪ β i = P i ∪ β i ∪ P (i + 1) := by
      ext x
      simp only [mem_union]
      tauto
    dsimp [K, I]
    rw [hu]
    exact (hinner i).2
  have hKballₚ : ∀ i, IsPLBall 2 (Kₚ i) := by
    intro i
    have hu : (Pₚ i ∪ Pₚ (i + 1)) ∪ β' i =
        Pₚ i ∪ β' i ∪ Pₚ (i + 1) := by
      ext x
      simp only [mem_union]
      tauto
    dsimp [Kₚ, Iₚ]
    rw [hu]
    simpa [Pₚ] using (hinnerₚ i).1
  have hKfrontₚ : ∀ i, frontier (Kₚ i) = Pₚ i ∪ β' i ∪ Pₚ (i + 1) := by
    intro i
    have hu : (Pₚ i ∪ Pₚ (i + 1)) ∪ β' i =
        Pₚ i ∪ β' i ∪ Pₚ (i + 1) := by
      ext x
      simp only [mem_union]
      tauto
    dsimp [Kₚ, Iₚ]
    rw [hu]
    exact (hinnerₚ i).2
  have hKcover : K 0 ∪ K 1 ∪ (K 2 ∪ K 3) = E := by
    have hK : ∀ i, K i = closure (inside ((T i ∩ E) ∪ β i ∪ (T (i + 1) ∩ E))) := by
      intro i
      have hu : (P i ∪ P (i + 1)) ∪ β i =
          P i ∪ β i ∪ P (i + 1) := by
        ext x
        simp only [mem_union]
        tauto
      dsimp [K, I]
      rw [hu]
    rw [hK 0, hK 1, hK 2, hK 3]
    exact hinnerCover
  have hKcoverₚ : Kₚ 0 ∪ Kₚ 1 ∪ (Kₚ 2 ∪ Kₚ 3) = E' := by
    have hK : ∀ i, Kₚ i = closure (inside ((T' (π i) ∩ E') ∪ β' i ∪
        (T' (π (i + 1)) ∩ E'))) := by
      intro i
      have hu : (Pₚ i ∪ Pₚ (i + 1)) ∪ β' i =
          Pₚ i ∪ β' i ∪ Pₚ (i + 1) := by
        ext x
        simp only [mem_union]
        tauto
      dsimp [Kₚ, Iₚ]
      rw [hu]
    rw [hK 0, hK 1, hK 2, hK 3]
    exact hinnerCoverₚ
  have hSsub : ∀ i, S i ⊆ D := by
    intro i x hx
    rw [← hsectorCover]
    fin_cases i
    · exact Or.inl (Or.inl (by simpa [S] using hx))
    · exact Or.inl (Or.inr (by simpa [S] using hx))
    · exact Or.inr (Or.inl (by simpa [S] using hx))
    · exact Or.inr (Or.inr (by simpa [S] using hx))
  have hSsubₚ : ∀ i, Sₚ i ⊆ D' := by
    intro i x hx
    rw [← hsectorCoverₚ]
    fin_cases i
    · exact Or.inl (Or.inl (by simpa [Sₚ] using hx))
    · exact Or.inl (Or.inr (by simpa [Sₚ] using hx))
    · exact Or.inr (Or.inl (by simpa [Sₚ] using hx))
    · exact Or.inr (Or.inr (by simpa [Sₚ] using hx))
  have hSfrontD : ∀ i, S i ∩ frontier D = α i := by
    intro i
    exact inter_frontier_eq_of_frontier_union_eq (hsector i).1.isPolyhedron.isClosed
      (hSsub i) (hsector i).2 (hTf i) (hTf (i + 1)) (hα i).left_mem (hα i).right_mem
      (hαD i)
  have hSfrontDₚ : ∀ i, Sₚ i ∩ frontier D' = α' i := by
    intro i
    exact inter_frontier_eq_of_frontier_union_eq (hsectorₚ i).1.isPolyhedron.isClosed
      (hSsubₚ i) (hsectorₚ i).2 (hTfₚ i) (hTfₚ (i + 1)) (hα' i).left_mem
      (hα' i).right_mem (hαDₚ i)
  have hcomp := cap_boundary_intersections_of_data hE hEint hcE hinit hTf hTT hTfE hα hαD
    hβ hβsub
  have hcompR : ∀ i, ((T i \ interior E) ∪ α i) ∩ (T (i + 1) \ interior E) =
      {v (i + 1)} := fun i => (hcomp i).2.1
  have hcompI : ∀ i, ((T i \ interior E) ∪ α i ∪ (T (i + 1) \ interior E)) ∩ β i =
      {w i, w (i + 1)} := fun i => (hcomp i).2.2
  have hcompₚ := cap_boundary_intersections_of_data hE' hEint' hcE' hinitₚ hTfₚ hTTₚ hTfEₚ
    hα' hαDₚ hβ' hβsubₚ
  have hcompRₚ : ∀ i,
      ((T' (π i) \ interior E') ∪ α' i) ∩ (T' (π (i + 1)) \ interior E') =
        {v' (π (i + 1))} := fun i => (hcompₚ i).2.1
  have hcompIₚ : ∀ i,
      ((T' (π i) \ interior E') ∪ α' i ∪ (T' (π (i + 1)) \ interior E')) ∩ β' i =
        {w' (π i), w' (π (i + 1))} := fun i => (hcompₚ i).2.2
  have hRα : ∀ i, R i ∩ α i = {v i} := by
    intro i
    simpa [R] using (hcomp i).1
  have hRR : ∀ i, (R i ∪ α i) ∩ R (i + 1) = {v (i + 1)} := by
    intro i
    simpa [R] using (hcompR i)
  have hOβ : ∀ i, O i ∩ β i = {w i, w (i + 1)} := by
    intro i
    simpa [O, R] using (hcompI i)
  have hRαₚ : ∀ i, Rₚ i ∩ α' i = {v' (π i)} := by
    intro i
    simpa [Rₚ] using (hcompₚ i).1
  have hRRₚ : ∀ i, (Rₚ i ∪ α' i) ∩ Rₚ (i + 1) = {v' (π (i + 1))} := by
    intro i
    simpa [Rₚ] using hcompRₚ i
  have hOβₚ : ∀ i, Oₚ i ∩ β' i = {w' (π i), w' (π (i + 1))} := by
    intro i
    simpa [Oₚ, Rₚ] using hcompIₚ i
  have hTfront : ∀ i, T i ⊆ frontier (S i) := by
    intro i x hx
    rw [hsector i |>.2]
    exact Or.inl (Or.inl hx)
  have hTfrontₚ : ∀ i, T' (π i) ⊆ frontier (Sₚ i) := by
    intro i x hx
    rw [hsectorₚ i |>.2]
    exact Or.inl (Or.inl hx)
  have hTfrontNext : ∀ i, T (i + 1) ⊆ frontier (S i) := by
    intro i x hx
    rw [hsector i |>.2]
    exact Or.inr hx
  have hTfrontNextₚ : ∀ i, T' (π (i + 1)) ⊆ frontier (Sₚ i) := by
    intro i x hx
    rw [hsectorₚ i |>.2]
    exact Or.inr hx
  have hTα : ∀ i, T i ∩ α i = {v i} := by
    intro i
    apply Subset.antisymm
    · intro x hx
      exact (hTf i).subset ⟨hx.1, hαD i hx.2⟩
    · intro x hx
      subst x
      exact ⟨(harc i).right_mem, (hα i).left_mem⟩
  have hαT : ∀ i, α i ∩ T (i + 1) = {v (i + 1)} := by
    intro i
    apply Subset.antisymm
    · intro x hx
      exact (hTf (i + 1)).subset ⟨hx.2, hαD i hx.1⟩
    · intro x hx
      subst x
      exact ⟨(hα i).right_mem, (harc (i + 1)).right_mem⟩
  have hTβ : ∀ i, T i ∩ β i = {w i} := by
    intro i
    apply Subset.antisymm
    · intro x hx
      exact (hTfE i).subset ⟨hx.1, hβsub i hx.2⟩
    · intro x hx
      subst x
      exact ⟨(hTfE i).symm.subset rfl |>.1, (hβ i).left_mem⟩
  have hTnextβ : ∀ i, T (i + 1) ∩ β i = {w (i + 1)} := by
    intro i
    apply Subset.antisymm
    · intro x hx
      exact (hTfE (i + 1)).subset ⟨hx.1, hβsub i hx.2⟩
    · intro x hx
      subst x
      exact ⟨(hTfE (i + 1)).symm.subset rfl |>.1, (hβ i).right_mem⟩
  have hTαₚ : ∀ i, T' (π i) ∩ α' i = {v' (π i)} := by
    intro i
    apply Subset.antisymm
    · intro x hx
      exact (hTfₚ i).subset ⟨hx.1, hαDₚ i hx.2⟩
    · intro x hx
      subst x
      exact ⟨(harcₚ i).right_mem, (hα' i).left_mem⟩
  have hαTₚ : ∀ i, α' i ∩ T' (π (i + 1)) = {v' (π (i + 1))} := by
    intro i
    apply Subset.antisymm
    · intro x hx
      exact (hTfₚ (i + 1)).subset ⟨hx.2, hαDₚ i hx.1⟩
    · intro x hx
      subst x
      exact ⟨(hα' i).right_mem, (harcₚ (i + 1)).right_mem⟩
  have hTβₚ : ∀ i, T' (π i) ∩ β' i = {w' (π i)} := by
    intro i
    apply Subset.antisymm
    · intro x hx
      exact (hTfEₚ i).subset ⟨hx.1, hβsubₚ i hx.2⟩
    · intro x hx
      subst x
      exact ⟨(hTfEₚ i).symm.subset rfl |>.1, (hβ' i).left_mem⟩
  have hTnextβₚ : ∀ i, T' (π (i + 1)) ∩ β' i = {w' (π (i + 1))} := by
    intro i
    apply Subset.antisymm
    · intro x hx
      exact (hTfEₚ (i + 1)).subset ⟨hx.1, hβsubₚ i hx.2⟩
    · intro x hx
      subst x
      exact ⟨(hTfEₚ (i + 1)).symm.subset rfl |>.1, (hβ' i).right_mem⟩
  have hΩsub : ∀ i, Ω i ⊆ S i := by
    intro i
    rw [← (hsplit i).1]
    exact subset_union_left
  have hΩsubₚ : ∀ i, Ωₚ i ⊆ Sₚ i := by
    intro i
    rw [← (hsplitₚ i).1]
    exact subset_union_left
  have hΩbound : ∀ i, Ω i ∩ T i = R i ∧ Ω i ∩ T (i + 1) = R (i + 1) := by
    intro i
    have hcR₀ : c ∉ R i := by
      intro hx
      exact hx.2 hcE
    have hcR₁ : c ∉ R (i + 1) := by
      intro hx
      exact hx.2 hcE
    have h := outer_cap_meets_bounding_spoke (S := S i) (Ω := Ω i) (T₀ := T i)
      (T₁ := T (i + 1)) (A := α i) (β := β i) (R₀ := R i) (R₁ := R (i + 1))
      (hΩball i).isPolyhedron.isClosed (hΩsub i)
      (hΩfront i) (hTfront i) (hTfrontNext i) (hTα i) (hαT i)
      (hTT i (i + 1) (by omega)) hcR₁ hcR₀ (hTβ i) (hTnextβ i)
      (hinit i).outerArc.left_mem (hinit (i + 1)).outerArc.left_mem
      (hinit i).outerArc.right_mem (hinit (i + 1)).outerArc.right_mem sdiff_subset sdiff_subset
    simpa [R] using h
  have hΩboundₚ : ∀ i,
      Ωₚ i ∩ T' (π i) = Rₚ i ∧ Ωₚ i ∩ T' (π (i + 1)) = Rₚ (i + 1) := by
    intro i
    have hcR₀ : c' ∉ Rₚ i := by
      intro hx
      exact hx.2 hcE'
    have hcR₁ : c' ∉ Rₚ (i + 1) := by
      intro hx
      exact hx.2 hcE'
    have h := outer_cap_meets_bounding_spoke (S := Sₚ i) (Ω := Ωₚ i)
      (T₀ := T' (π i)) (T₁ := T' (π (i + 1))) (A := α' i) (β := β' i)
      (R₀ := Rₚ i) (R₁ := Rₚ (i + 1)) (hΩballₚ i).isPolyhedron.isClosed
      (hΩsubₚ i) (hΩfrontₚ i) (hTfrontₚ i) (hTfrontNextₚ i) (hTαₚ i) (hαTₚ i)
      (hTTₚ i (i + 1) (by omega)) hcR₁ hcR₀ (hTβₚ i) (hTnextβₚ i)
      (hinitₚ i).outerArc.left_mem (hinitₚ (i + 1)).outerArc.left_mem
      (hinitₚ i).outerArc.right_mem (hinitₚ (i + 1)).outerArc.right_mem sdiff_subset sdiff_subset
    simpa [Rₚ] using h
  have hvneₚ : ∀ i j : Fin 4, i ≠ j → v' (π i) ≠ v' (π j) := by
    intro i j hij h
    have hm : v' (π i) ∈ T' (π i) ∩ T' (π j) :=
      ⟨(harcₚ i).right_mem, by rw [h]; exact (harcₚ j).right_mem⟩
    rw [hTTₚ i j hij] at hm
    exact ne_of_isArcBetween (harcₚ i) (mem_singleton_iff.mp hm).symm
  have havoid : ∀ i k, k ≠ i → k ≠ i + 1 → v k ∉ α i :=
    boundary_arc_avoids_opposite_endpoint hcut hv1 hv3 hα hα01 hα01i hα23 hα23i hvne
  have havoidₚ : ∀ i k, k ≠ i → k ≠ i + 1 → v' (π k) ∉ α' i :=
    boundary_arc_avoids_opposite_endpoint hcut' hv1' hv3' hα' hα'01 hα'01i hα'23 hα'23i
      hvneₚ
  have hOpp : ∀ i k, k ≠ i → k ≠ i + 1 → S i ∩ T k ⊆ {c} := by
    intro i k hki hkn x hx
    exact opposite_spoke_inter_sector (S := S i) (T := T k) (T₀ := T i)
      (T₁ := T (i + 1)) (A := α i) (hsector i).1 (harc k) (hsector i).2
      (hTT k i hki) (hTT k (i + 1) hkn) (hTf k) (hαD i)
      (havoid i k hki hkn) (hSfrontD i) ⟨hx.2, hx.1⟩
  have hOppₚ : ∀ i k, k ≠ i → k ≠ i + 1 → Sₚ i ∩ T' (π k) ⊆ {c'} := by
    intro i k hki hkn x hx
    exact opposite_spoke_inter_sector (S := Sₚ i) (T := T' (π k))
      (T₀ := T' (π i)) (T₁ := T' (π (i + 1))) (A := α' i) (hsectorₚ i).1
      (harcₚ k) (hsectorₚ i).2 (hTTₚ k i hki) (hTTₚ k (i + 1) hkn)
      (hTfₚ k) (hαDₚ i) (havoidₚ i k hki hkn) (hSfrontDₚ i) ⟨hx.2, hx.1⟩
  have hcK : ∀ i, c ∈ K i := by
    intro i
    rw [← (hKball i).isPolyhedron.isClosed.closure_eq]
    exact frontier_subset_closure ((hKfront i).symm ▸
      Or.inl (Or.inl ⟨(harc i).left_mem, interior_subset hcE⟩))
  have hcKₚ : ∀ i, c' ∈ Kₚ i := by
    intro i
    rw [← (hKballₚ i).isPolyhedron.isClosed.closure_eq]
    exact frontier_subset_closure ((hKfrontₚ i).symm ▸
      Or.inl (Or.inl ⟨(harcₚ i).left_mem, interior_subset hcE'⟩))
  have hcβ : ∀ i, c ∉ β i := by
    intro i hx
    have hfr : c ∈ frontier E := hβsub i hx
    exact (mem_interior_iff_notMem_frontier (interior_subset hcE)).mp hcE hfr
  have hcβₚ : ∀ i, c' ∉ β' i := by
    intro i hx
    have hfr : c' ∈ frontier E' := hβsubₚ i hx
    exact (mem_interior_iff_notMem_frontier (interior_subset hcE')).mp hcE' hfr
  have hcΩ : ∀ i, c ∉ Ω i := by
    intro i hx
    have hmem : c ∈ Ω i ∩ K i := ⟨hx, hcK i⟩
    rw [hsplit i |>.2] at hmem
    exact hcβ i hmem
  have hcΩₚ : ∀ i, c' ∉ Ωₚ i := by
    intro i hx
    have hmem : c' ∈ Ωₚ i ∩ Kₚ i := ⟨hx, hcKₚ i⟩
    rw [hsplitₚ i |>.2] at hmem
    exact hcβₚ i hmem
  have hΩopp : ∀ i k, k ≠ i → k ≠ i + 1 → Ω i ∩ T k ⊆ (∅ : Set Plane) := by
    intro i k hki hkn x hx
    have hxc : x = c := mem_singleton_iff.mp (hOpp i k hki hkn ⟨(hΩsub i hx.1), hx.2⟩)
    exact (hcΩ i (hxc ▸ hx.1)).elim
  have hΩoppₚ : ∀ i k, k ≠ i → k ≠ i + 1 → Ωₚ i ∩ T' (π k) ⊆ (∅ : Set Plane) := by
    intro i k hki hkn x hx
    have hxc : x = c' := mem_singleton_iff.mp
      (hOppₚ i k hki hkn ⟨(hΩsubₚ i hx.1), hx.2⟩)
    exact (hcΩₚ i (hxc ▸ hx.1)).elim
  have hKsubE : ∀ i, K i ⊆ E := by
    intro i x hx
    rw [← hKcover]
    fin_cases i
    · exact Or.inl (Or.inl hx)
    · exact Or.inl (Or.inr hx)
    · exact Or.inr (Or.inl hx)
    · exact Or.inr (Or.inr hx)
  have hKsubEₚ : ∀ i, Kₚ i ⊆ E' := by
    intro i x hx
    rw [← hKcoverₚ]
    fin_cases i
    · exact Or.inl (Or.inl hx)
    · exact Or.inl (Or.inr hx)
    · exact Or.inr (Or.inl hx)
    · exact Or.inr (Or.inr hx)
  have hRE : ∀ i, R i ∩ E = {w i} := by
    intro i
    apply Subset.antisymm
    · intro x hx
      have hfr : x ∈ frontier E := by
        rw [hE.isPolyhedron.isClosed.frontier_eq]
        exact ⟨hx.2, hx.1.2⟩
      exact (hTfE i).subset ⟨hx.1.1, hfr⟩
    · intro x hx
      subst x
      exact ⟨(hinit i).outerArc.left_mem, hE.isPolyhedron.isClosed.frontier_subset
        ((hTfE i).symm.subset rfl |>.2)⟩
  have hREₚ : ∀ i, Rₚ i ∩ E' = {w' (π i)} := by
    intro i
    apply Subset.antisymm
    · intro x hx
      have hfr : x ∈ frontier E' := by
        rw [hE'.isPolyhedron.isClosed.frontier_eq]
        exact ⟨hx.2, hx.1.2⟩
      exact (hTfEₚ i).subset ⟨hx.1.1, hfr⟩
    · intro x hx
      subst x
      exact ⟨(hinitₚ i).outerArc.left_mem, hE'.isPolyhedron.isClosed.frontier_subset
        ((hTfEₚ i).symm.subset rfl |>.2)⟩
  have hΩK : ∀ i j, i ≠ j → Ω i ∩ K j ⊆ β i := by
    intro i j hij x hx
    have hsp := hsectorInter i j hij
      ⟨hΩsub i hx.1, (hsplit j).1.subset (Or.inr hx.2)⟩
    rcases Set.mem_iUnion.mp hsp with ⟨k, hk⟩
    by_cases hki : k = i
    · subst k
      have hxw := mem_singleton_iff.mp ((hRE i).subset
        ⟨(hΩbound i).1.subset ⟨hx.1, hk⟩, hKsubE j hx.2⟩)
      exact hxw.symm ▸ (hβ i).left_mem
    · by_cases hkn : k = i + 1
      · subst k
        have hxw := mem_singleton_iff.mp ((hRE (i + 1)).subset
          ⟨(hΩbound i).2.subset ⟨hx.1, hk⟩, hKsubE j hx.2⟩)
        exact hxw.symm ▸ (hβ i).right_mem
      · exact (hΩopp i k hki hkn ⟨hx.1, hk⟩).elim
  have hΩKₚ : ∀ i j, i ≠ j → Ωₚ i ∩ Kₚ j ⊆ β' i := by
    intro i j hij x hx
    have hsp := hsectorInterₚ i j hij
      ⟨hΩsubₚ i hx.1, (hsplitₚ j).1.subset (Or.inr hx.2)⟩
    rcases Set.mem_iUnion.mp hsp with ⟨k, hk⟩
    by_cases hki : k = i
    · subst k
      have hxw := mem_singleton_iff.mp ((hREₚ i).subset
        ⟨(hΩboundₚ i).1.subset ⟨hx.1, hk⟩, hKsubEₚ j hx.2⟩)
      exact hxw.symm ▸ (hβ' i).left_mem
    · by_cases hkn : k = i + 1
      · subst k
        have hxw := mem_singleton_iff.mp ((hREₚ (i + 1)).subset
          ⟨(hΩboundₚ i).2.subset ⟨hx.1, hk⟩, hKsubEₚ j hx.2⟩)
        exact hxw.symm ▸ (hβ' i).right_mem
      · exact (hΩoppₚ i k hki hkn ⟨hx.1, hk⟩).elim
  have hΩE : ∀ i, Ω i ∩ E = β i := by
    intro i
    apply Subset.antisymm
    · intro x hx
      have hxK : x ∈ K 0 ∪ K 1 ∪ (K 2 ∪ K 3) := hKcover.symm.subset hx.2
      have hxK' : ∃ j, x ∈ K j := by
        rcases hxK with (h0 | h1) | (h2 | h3)
        · exact ⟨0, h0⟩
        · exact ⟨1, h1⟩
        · exact ⟨2, h2⟩
        · exact ⟨3, h3⟩
      obtain ⟨j, hxj⟩ := hxK'
      by_cases hij : i = j
      · subst j
        exact (hsplit i).2.subset ⟨hx.1, hxj⟩
      · exact hΩK i j hij ⟨hx.1, hxj⟩
    · intro x hx
      exact ⟨((hsplit i).2.symm.subset hx).1,
        hE.isPolyhedron.isClosed.frontier_subset (hβsub i hx)⟩
  have hΩEₚ : ∀ i, Ωₚ i ∩ E' = β' i := by
    intro i
    apply Subset.antisymm
    · intro x hx
      have hxK : x ∈ Kₚ 0 ∪ Kₚ 1 ∪ (Kₚ 2 ∪ Kₚ 3) := hKcoverₚ.symm.subset hx.2
      have hxK' : ∃ j, x ∈ Kₚ j := by
        rcases hxK with (h0 | h1) | (h2 | h3)
        · exact ⟨0, h0⟩
        · exact ⟨1, h1⟩
        · exact ⟨2, h2⟩
        · exact ⟨3, h3⟩
      obtain ⟨j, hxj⟩ := hxK'
      by_cases hij : i = j
      · subst j
        exact (hsplitₚ i).2.subset ⟨hx.1, hxj⟩
      · exact hΩKₚ i j hij ⟨hx.1, hxj⟩
    · intro x hx
      exact ⟨((hsplitₚ i).2.symm.subset hx).1,
        hE'.isPolyhedron.isClosed.frontier_subset (hβsubₚ i hx)⟩
  have hgw : ∀ i, g (w i) = w' (π i) := by
    intro i
    have hmT : g (w i) ∈ T' (π i) :=
      ((hgT i).subset ⟨w i, (hinit i).boundary_mem, rfl⟩).1
    have hmβ : g (w i) ∈ β' i := (hβmap i).subset ⟨w i, (hβ i).left_mem, rfl⟩
    exact mem_singleton_iff.mp ((hTfEₚ i).subset ⟨hmT, hβsubₚ i hmβ⟩)
  have hlocal : ∀ i, ∃ f : Plane → Plane,
      IsPLHomeomorphOn f (Ω i) (Ωₚ i) ∧
      EqOn f (r i) (R i) ∧ EqOn f γ (α i) ∧
      EqOn f (r (i + 1)) (R (i + 1)) ∧ EqOn f g (β i) := by
    intro i
    have hRpoly : ∀ j, IsPolyhedron (R j) := fun j =>
      (IsInitialSpokeSegment.outerArc_isPLBall (hT j) hE (hinit j)).isPolyhedron
    have hαpoly : IsPolyhedron (α i) :=
      (isPLBall_of_isArc_subset_isPLSphere hD.isPLSphere_frontier
        (hα i).isArc (hαD i)).isPolyhedron
    have hγi : IsPLHomeomorphOn γ (α i) (α' i) := by
      rw [← hαmap i]
      exact hγ.restrict hαpoly (hαD i)
    have hgi : IsPLHomeomorphOn g (β i) (β' i) := by
      rw [← hβmap i]
      exact hg.restrict (hβball i).isPolyhedron
        ((hβsub i).trans hE.isPolyhedron.isClosed.frontier_subset)
    obtain ⟨b, hb, hbR, hbα, hbRnext, hbβ⟩ := exists_isPLHomeomorphOn_cap_boundary
      (hRpoly i) hαpoly (hRpoly (i + 1)) (hβball i).isPolyhedron
      (hr i) hγi (hr (i + 1)) hgi
      (hRα i) (hRαₚ i) (hRR i) (hRRₚ i) (hOβ i) (hOβₚ i)
      (hinit i).outerArc.left_mem (hinit (i + 1)).outerArc.left_mem
      (hβ i).left_mem (hβ i).right_mem
      (hinitₚ i).outerArc.left_mem (hinitₚ (i + 1)).outerArc.left_mem
      (hβ' i).left_mem (hβ' i).right_mem (hα i).right_mem
      ((hrv i).trans (hγv i)) (hγv i)
      (hγv (i + 1)) ((hrv (i + 1)).trans (hγv (i + 1)))
      ((hrw i).trans (hgw i)) (hgw i)
      ((hrw (i + 1)).trans (hgw (i + 1))) (hgw (i + 1))
    have hbfront : IsPLHomeomorphOn b (frontier (Ω i)) (frontier (Ωₚ i)) := by
      rw [hΩfront i, hΩfrontₚ i]
      exact hb
    obtain ⟨f, hf, hfb⟩ := exists_isPLHomeomorphOn_of_frontier (hΩball i)
      (hΩballₚ i) hbfront
    refine ⟨f, hf, ?_, ?_, ?_, ?_⟩
    · intro x hx
      exact (hfb ((hΩfront i).symm.subset (Or.inl (Or.inl (Or.inl hx))))).trans
        (hbR hx)
    · intro x hx
      exact (hfb ((hΩfront i).symm.subset (Or.inl (Or.inl (Or.inr hx))))).trans
        (hbα hx)
    · intro x hx
      exact (hfb ((hΩfront i).symm.subset (Or.inl (Or.inr hx)))).trans (hbRnext hx)
    · intro x hx
      exact (hfb ((hΩfront i).symm.subset (Or.inr hx))).trans (hbβ hx)
  choose f hf hfR hfα hfRnext hfβ using hlocal
  have hfspoke : ∀ i k, EqOn (f i) (r k) (Ω i ∩ T k) := by
    intro i k x hx
    by_cases hki : k = i
    · subst k
      exact hfR i ((hΩbound i).1.subset hx)
    · by_cases hkn : k = i + 1
      · subst k
        exact hfRnext i ((hΩbound i).2.subset hx)
      · exact (hΩopp i k hki hkn hx).elim
  have hRΩ : ∀ i k, (Ωₚ i ∩ T' (π k)).Nonempty → R k ⊆ Ω i := by
    intro i k hnon
    by_cases hki : k = i
    · subst k
      exact fun x hx => ((hΩbound i).1.symm.subset hx).1
    · by_cases hkn : k = i + 1
      · subst k
        exact fun x hx => ((hΩbound i).2.symm.subset hx).1
      · obtain ⟨x, hx⟩ := hnon
        exact (hΩoppₚ i k hki hkn hx).elim
  have hcompat : ∀ i j, EqOn (f i) (f j) (Ω i ∩ Ω j) := by
    intro i j x hx
    by_cases hij : i = j
    · subst j
      rfl
    · obtain ⟨k, hk⟩ := mem_iUnion.mp
        (hsectorInter i j hij ⟨hΩsub i hx.1, hΩsub j hx.2⟩)
      exact (hfspoke i k ⟨hx.1, hk⟩).trans (hfspoke j k ⟨hx.2, hk⟩).symm
  have hmeet : ∀ i j, f i '' (Ω i ∩ Ω j) = Ωₚ i ∩ Ωₚ j := by
    intro i j
    apply Subset.antisymm
    · rintro _ ⟨x, hx, rfl⟩
      exact ⟨(hf i).bijOn.mapsTo hx.1,
        (hcompat i j hx).symm ▸ (hf j).bijOn.mapsTo hx.2⟩
    · intro y hy
      by_cases hij : i = j
      · subst j
        obtain ⟨x, hx, hxy⟩ := (hf i).bijOn.surjOn hy.1
        exact ⟨x, ⟨hx, hx⟩, hxy⟩
      · obtain ⟨k, hk⟩ := mem_iUnion.mp
          (hsectorInterₚ i j hij ⟨hΩsubₚ i hy.1, hΩsubₚ j hy.2⟩)
        have hyR : y ∈ Rₚ k := by
          by_cases hki : k = i
          · subst k
            exact (hΩboundₚ i).1.subset ⟨hy.1, hk⟩
          · by_cases hkn : k = i + 1
            · subst k
              exact (hΩboundₚ i).2.subset ⟨hy.1, hk⟩
            · exact (hΩoppₚ i k hki hkn ⟨hy.1, hk⟩).elim
        obtain ⟨x, hx, hxy⟩ := (hr k).bijOn.surjOn hyR
        have hxi : x ∈ Ω i := hRΩ i k ⟨y, hy.1, hk⟩ hx
        have hxj : x ∈ Ω j := hRΩ j k ⟨y, hy.2, hk⟩ hx
        exact ⟨x, ⟨hxi, hxj⟩, (hfspoke i k ⟨hxi, hx.1⟩).trans hxy⟩
  obtain ⟨F, hF, hFg, hFf⟩ := exists_isPLHomeomorphOn_iUnion_union
    (fun i => (hΩball i).isPolyhedron) hE.isPolyhedron hf hg hΩE hΩEₚ hfβ hβmap
    hcompat hmeet
  have hDcover : (⋃ i, Ω i) ∪ E = D := by
    apply Subset.antisymm
    · rintro x (hx | hx)
      · obtain ⟨i, hxi⟩ := mem_iUnion.mp hx
        exact hSsub i (hΩsub i hxi)
      · exact interior_subset (hEint hx)
    · intro x hx
      have hxS : ∃ i, x ∈ S i := by
        have hxs := hsectorCover.symm.subset hx
        rcases hxs with (h0 | h1) | (h2 | h3)
        · exact ⟨0, h0⟩
        · exact ⟨1, h1⟩
        · exact ⟨2, h2⟩
        · exact ⟨3, h3⟩
      obtain ⟨i, hxi⟩ := hxS
      rcases (hsplit i).1.symm.subset hxi with hxo | hxk
      · exact Or.inl (mem_iUnion.mpr ⟨i, hxo⟩)
      · exact Or.inr (hKsubE i hxk)
  have hDcoverₚ : (⋃ i, Ωₚ i) ∪ E' = D' := by
    apply Subset.antisymm
    · rintro x (hx | hx)
      · obtain ⟨i, hxi⟩ := mem_iUnion.mp hx
        exact hSsubₚ i (hΩsubₚ i hxi)
      · exact interior_subset (hEint' hx)
    · intro x hx
      have hxS : ∃ i, x ∈ Sₚ i := by
        have hxs := hsectorCoverₚ.symm.subset hx
        rcases hxs with (h0 | h1) | (h2 | h3)
        · exact ⟨0, h0⟩
        · exact ⟨1, h1⟩
        · exact ⟨2, h2⟩
        · exact ⟨3, h3⟩
      obtain ⟨i, hxi⟩ := hxS
      rcases (hsplitₚ i).1.symm.subset hxi with hxo | hxk
      · exact Or.inl (mem_iUnion.mpr ⟨i, hxo⟩)
      · exact Or.inr (hKsubEₚ i hxk)
  have hFγ : EqOn F γ (frontier D) := by
    intro x hx
    have hxα : ∃ i, x ∈ α i := by
      have hxs := hcut.union_eq.symm.subset hx
      rcases hxs with hxA | hxA
      · rcases hα01.symm.subset hxA with h0 | h1
        · exact ⟨0, h0⟩
        · exact ⟨1, h1⟩
      · rcases hα23.symm.subset hxA with h2 | h3
        · exact ⟨2, h2⟩
        · exact ⟨3, h3⟩
    obtain ⟨i, hxi⟩ := hxα
    have hxo : x ∈ Ω i := (hΩball i).isPolyhedron.isClosed.frontier_subset
      ((hΩfront i).symm.subset (Or.inl (Or.inl (Or.inr hxi))))
    exact (hFf i hxo).trans (hfα i hxi)
  have hFr : ∀ i, EqOn F (r i) (T i \ interior E) := by
    intro i x hx
    exact (hFf i (((hΩbound i).1.symm.subset hx).1)).trans (hfR i hx)
  refine ⟨F, ?_, hFg, hFγ, ?_⟩
  · simpa only [hDcover, hDcoverₚ] using hF
  · intro i
    refine ⟨hFr i, ?_⟩
    have hFP : F '' (T i ∩ E) = T' (π i) ∩ E' :=
      (Set.image_congr (fun _ hx => hFg hx.2)).trans (hgT i)
    have hFR : F '' (T i \ interior E) = T' (π i) \ interior E' :=
      (Set.image_congr (fun _ hx => hFr i hx)).trans (hr i).image_eq
    calc
      F '' T i = F '' (T i ∩ E) ∪ F '' (T i \ interior E) := by
        rw [← image_union, (hinit i).union_eq]
      _ = (T' (π i) ∩ E') ∪ (T' (π i) \ interior E') := by rw [hFP, hFR]
      _ = T' (π i) := (hinitₚ i).union_eq

end DifferentialGeometry.Topology.PiecewiseLinear
