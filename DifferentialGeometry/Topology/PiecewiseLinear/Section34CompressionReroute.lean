/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.Homeomorph.SubsetImage
import Mathlib.Analysis.InnerProductSpace.PiL2

open Set Topology

namespace DifferentialGeometry.Topology.PiecewiseLinear

local notation "E3" => EuclideanSpace ℝ (Fin 3)

theorem continuousOn_of_isClosed_cover {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    {f : X → Y} {S A B : Set X} (hA : IsClosed A) (hB : IsClosed B) (hS : S ⊆ A ∪ B)
    (hfA : ContinuousOn f (S ∩ A)) (hfB : ContinuousOn f (S ∩ B)) : ContinuousOn f S := by
  intro x hx
  have hwA : ContinuousWithinAt f (S ∩ A) x := by
    by_cases hxA : x ∈ A
    · exact hfA x ⟨hx, hxA⟩
    · exact continuousWithinAt_of_notMem_closure fun h =>
        hxA (closure_minimal inter_subset_right hA h)
  have hwB : ContinuousWithinAt f (S ∩ B) x := by
    by_cases hxB : x ∈ B
    · exact hfB x ⟨hx, hxB⟩
    · exact continuousWithinAt_of_notMem_closure fun h =>
        hxB (closure_minimal inter_subset_right hB h)
  have hSeq : S = S ∩ A ∪ S ∩ B := by
    ext y
    constructor
    · intro hy
      rcases hS hy with h | h
      · exact Or.inl ⟨hy, h⟩
      · exact Or.inr ⟨hy, h⟩
    · rintro (h | h)
      · exact h.1
      · exact h.1
  rw [hSeq]
  exact hwA.union hwB

variable {M : Type*} [TopologicalSpace M] [T2Space M]

theorem exists_reroute_collapse {c : OpenPartialHomeomorph M E3} {Hs Obs Mk : Set M}
    {Y : Set E3} (hY : IsCompact Y) (hYt : Y ⊆ c.target) (hYfr : c.symm '' frontier Y ⊆ Obs)
    (hYH : Disjoint (c.symm '' Y) (frontier Hs)) (hMk : Disjoint Mk (c.symm '' Y))
    {p : M} (hp : p ∈ frontier Hs) (hHs : IsClosed Hs) (hObsH : Disjoint Obs (frontier Hs)) :
    ∃ r : M → M, ContinuousOn r (Hs \ Obs) ∧ MapsTo r (Hs \ Obs) (Hs \ (Obs ∪ c.symm '' Y)) ∧
      (∀ z ∈ frontier Hs, r z = z) ∧ (∀ y ∈ Mk, r y = y) ∧
      ∀ y ∈ Hs \ Obs, y ∉ c.symm '' Y → r y = y := by
  classical
  set Pk := c.symm '' Y with hPkdef
  have hPkc : IsClosed Pk := (hY.image_of_continuousOn (c.continuousOn_symm.mono hYt)).isClosed
  have hPkfr : frontier Pk ⊆ Obs := by
    rw [hPkdef, ← c.symm.image_frontier_of_isCompact hY hYt]
    exact hYfr
  set r : M → M := fun y => if y ∈ Pk then p else y with hrdef
  have hpPk : p ∉ Pk := fun h => Set.disjoint_left.mp hYH h hp
  have hpObs : p ∉ Obs := fun h => Set.disjoint_left.mp hObsH h hp
  have hpH : p ∈ Hs := hHs.frontier_subset hp
  refine ⟨r, ?_, ?_, fun z hz => ?_, fun y hy => ?_, fun y _ hy => ?_⟩
  · refine continuousOn_of_isClosed_cover hPkc (isOpen_interior (s := Pk)).isClosed_compl
      (fun y hy => ?_) ?_ ?_
    · by_cases hyP : y ∈ interior Pk
      · exact Or.inl (interior_subset hyP)
      · exact Or.inr hyP
    · refine (continuousOn_const (c := p)).congr fun y hy => ?_
      simp only [hrdef, ite_eq_left hy.2]
    · refine continuousOn_id.congr fun y hy => ?_
      have hyP : y ∉ Pk := by
        intro h
        have hyfr : y ∈ frontier Pk := ⟨subset_closure h, hy.2⟩
        exact hy.1.2 (hPkfr hyfr)
      simp only [hrdef, ite_eq_right hyP, id]
  · intro y hy
    by_cases hyP : y ∈ Pk
    · simp only [hrdef, ite_eq_left hyP]
      exact ⟨hpH, fun h => h.elim hpObs hpPk⟩
    · simp only [hrdef, ite_eq_right hyP]
      exact ⟨hy.1, fun h => h.elim hy.2 hyP⟩
  · have hzP : z ∉ Pk := fun h => Set.disjoint_left.mp hYH h hz
    simp only [hrdef, ite_eq_right hzP]
  · have hyP : y ∉ Pk := fun h => Set.disjoint_left.mp hMk hy h
    simp only [hrdef, ite_eq_right hyP]
  · simp only [hrdef, ite_eq_right hy]

theorem exists_reroute_push {c : OpenPartialHomeomorph M E3} {Hs Obs Mk : Set M}
    {R Lr Bh T : Set E3} {g : E3 → E3} (hRo : IsOpen R) (hclR : closure R ⊆ R ∪ Bh ∪ Lr)
    (hclRc : IsCompact (closure R)) (hclRt : closure R ⊆ c.target) (hLrt : Lr ⊆ c.target)
    (hTt : T ⊆ c.target) (hBh : c.symm '' Bh ⊆ Obs)
    (hgc : ContinuousOn g (R ∪ Lr)) (hgLr : ∀ y ∈ Lr, g y = y) (hgR : MapsTo g R R)
    (hgT : ∀ y ∈ R, g y ∉ T) (hTR : T ⊆ R ∪ Bh) (hRH : c.symm '' R ⊆ Hs)
    (hRobs : c.symm '' R ⊆ Obs ∨ Disjoint (c.symm '' R) Obs)
    (hRfr : Disjoint (c.symm '' R) (frontier Hs)) (hMk : Disjoint Mk (c.symm '' R)) :
    ∃ r : M → M, ContinuousOn r (Hs \ Obs) ∧ MapsTo r (Hs \ Obs) (Hs \ (Obs ∪ c.symm '' T)) ∧
      (∀ z ∈ frontier Hs, r z = z) ∧ (∀ y ∈ Mk, r y = y) ∧
      (∀ y ∈ Hs \ Obs, y ∉ c.symm '' R → r y = y) ∧
      ∀ y ∈ Hs \ Obs, y ∈ c.symm '' R → r y ∈ c.symm '' R := by
  classical
  set SR := c.symm '' R with hSRdef
  have hRt : R ⊆ c.target := subset_closure.trans hclRt
  have hSRo : IsOpen SR := c.isOpen_image_symm_of_subset_target hRo hRt
  have hSRc : IsClosed (c.symm '' closure R) :=
    (hclRc.image_of_continuousOn (c.continuousOn_symm.mono hclRt)).isClosed
  set r : M → M := fun y => if y ∈ SR then c.symm (g (c y)) else y with hrdef
  have hRr : ∀ y ∈ SR, c y ∈ R ∧ r y = c.symm (g (c y)) := by
    rintro _ ⟨x, hx, rfl⟩
    refine ⟨by rw [c.right_inv (hRt hx)]; exact hx, ?_⟩
    simp only [hrdef, ite_eq_left (show c.symm x ∈ SR from ⟨x, hx, rfl⟩)]
  have hrin : ∀ y ∈ SR, r y ∈ SR := by
    intro y hy
    obtain ⟨hcy, hry⟩ := hRr y hy
    rw [hry]
    exact ⟨g (c y), hgR hcy, rfl⟩
  have hDomSR : ∀ y ∈ Hs \ Obs, y ∈ SR → Disjoint SR Obs := fun y hy hyR =>
    hRobs.resolve_left fun h => hy.2 (h hyR)
  refine ⟨r, ?_, ?_, fun z hz => ?_, fun y hy => ?_, fun y _ hy => ?_,
    fun y _ hy => hrin y hy⟩
  · refine continuousOn_of_isClosed_cover hSRc hSRo.isClosed_compl (fun y hy => ?_) ?_ ?_
    · by_cases hyR : y ∈ SR
      · exact Or.inl (image_mono subset_closure hyR)
      · exact Or.inr hyR
    · have hsub : (Hs \ Obs) ∩ c.symm '' closure R ⊆ c.symm '' (R ∪ Lr) := by
        rintro _ ⟨hy, x, hx, rfl⟩
        rcases hclR hx with (hxR | hxB) | hxL
        · exact ⟨x, Or.inl hxR, rfl⟩
        · exact absurd (hBh ⟨x, hxB, rfl⟩) hy.2
        · exact ⟨x, Or.inr hxL, rfl⟩
      have hRLt : R ∪ Lr ⊆ c.target := union_subset hRt hLrt
      have hcm : MapsTo c (c.symm '' (R ∪ Lr)) (R ∪ Lr) := by
        rintro _ ⟨x, hx, rfl⟩
        rw [c.right_inv (hRLt hx)]
        exact hx
      have hsrc : c.symm '' (R ∪ Lr) ⊆ c.source := by
        rintro _ ⟨x, hx, rfl⟩
        exact c.map_target (hRLt hx)
      have hgm : MapsTo g (R ∪ Lr) c.target := by
        rintro x (hx | hx)
        · exact hRt (hgR hx)
        · rw [hgLr x hx]
          exact hLrt hx
      have hF : ContinuousOn (fun y => c.symm (g (c y))) (c.symm '' (R ∪ Lr)) :=
        c.continuousOn_symm.comp (hgc.comp (c.continuousOn.mono hsrc) hcm) (hgm.comp hcm)
      refine (hF.mono hsub).congr fun y hy => ?_
      obtain ⟨x, hx, rfl⟩ := hsub hy
      by_cases hxS : c.symm x ∈ SR
      · simp only [hrdef, ite_eq_left hxS]
      · simp only [hrdef, ite_eq_right hxS]
        rcases hx with hxR | hxL
        · exact absurd ⟨x, hxR, rfl⟩ hxS
        · rw [c.right_inv (hLrt hxL), hgLr x hxL]
    · refine continuousOn_id.congr fun y hy => ?_
      simp only [hrdef, ite_eq_right hy.2, id]
  · intro y hy
    by_cases hyR : y ∈ SR
    · obtain ⟨hcy, hry⟩ := hRr y hyR
      have hdis := hDomSR y hy hyR
      have hmem := hrin y hyR
      refine ⟨hRH hmem, ?_⟩
      rintro (h | ⟨t, ht, heq⟩)
      · exact Set.disjoint_left.mp hdis hmem h
      · rw [hry] at heq
        have h2 := c.symm.injOn (hTt ht) (hRt (hgR hcy)) heq
        exact hgT (c y) hcy (h2 ▸ ht)
    · simp only [hrdef, ite_eq_right hyR]
      refine ⟨hy.1, ?_⟩
      rintro (h | ⟨t, ht, rfl⟩)
      · exact hy.2 h
      · rcases hTR ht with htR | htB
        · exact hyR ⟨t, htR, rfl⟩
        · exact hy.2 (hBh ⟨t, htB, rfl⟩)
  · have hzR : z ∉ SR := fun h => Set.disjoint_left.mp hRfr h hz
    simp only [hrdef, ite_eq_right hzR]
  · have hyR : y ∉ SR := fun h => Set.disjoint_left.mp hMk hy h
    simp only [hrdef, ite_eq_right hyR]
  · simp only [hrdef, ite_eq_right hy]

omit [T2Space M] in
theorem exists_reroute_comp {Hs Obs Mk Z₁ Z₂ : Set M} {r₁ r₂ : M → M}
    (hr₁c : ContinuousOn r₁ (Hs \ Obs)) (hr₁m : MapsTo r₁ (Hs \ Obs) (Hs \ (Obs ∪ Z₁)))
    (hr₁fr : ∀ z ∈ frontier Hs, r₁ z = z) (hr₁k : ∀ y ∈ Mk, r₁ y = y)
    (hr₂c : ContinuousOn r₂ (Hs \ Obs)) (hr₂m : MapsTo r₂ (Hs \ Obs) (Hs \ (Obs ∪ Z₂)))
    (hr₂fr : ∀ z ∈ frontier Hs, r₂ z = z) (hr₂k : ∀ y ∈ Mk, r₂ y = y)
    (hr₂Z : ∀ y ∈ Hs \ (Obs ∪ Z₁), r₂ y ∉ Z₁) :
    ∃ r : M → M, ContinuousOn r (Hs \ Obs) ∧ MapsTo r (Hs \ Obs) (Hs \ (Obs ∪ (Z₁ ∪ Z₂))) ∧
      (∀ z ∈ frontier Hs, r z = z) ∧ ∀ y ∈ Mk, r y = y := by
  have hsub : MapsTo r₁ (Hs \ Obs) (Hs \ Obs) := fun y hy =>
    ⟨(hr₁m hy).1, fun h => (hr₁m hy).2 (Or.inl h)⟩
  refine ⟨r₂ ∘ r₁, hr₂c.comp hr₁c hsub, fun y hy => ?_, fun z hz => ?_, fun y hy => ?_⟩
  · have h1 := hr₁m hy
    have h2 := hr₂m (hsub hy)
    refine ⟨h2.1, ?_⟩
    rintro (h | h | h)
    · exact h2.2 (Or.inl h)
    · exact hr₂Z (r₁ y) h1 h
    · exact h2.2 (Or.inr h)
  · simp only [Function.comp, hr₁fr z hz, hr₂fr z hz]
  · simp only [Function.comp, hr₁k y hy, hr₂k y hy]

theorem exists_reroute_pocket_push {c : OpenPartialHomeomorph M E3} {Hs Obs Mk : Set M}
    {Y R Lr Bh T : Set E3} {g : E3 → E3} (hY : IsCompact Y) (hYt : Y ⊆ c.target)
    (hYfr : c.symm '' frontier Y ⊆ Obs) (hYH : Disjoint (c.symm '' Y) (frontier Hs))
    (hMkY : Disjoint Mk (c.symm '' Y)) (hHne : (frontier Hs).Nonempty) (hHs : IsClosed Hs)
    (hObsH : Disjoint Obs (frontier Hs)) (hRo : IsOpen R) (hclR : closure R ⊆ R ∪ Bh ∪ Lr)
    (hclRc : IsCompact (closure R)) (hclRt : closure R ⊆ c.target) (hLrt : Lr ⊆ c.target)
    (hTt : T ⊆ c.target) (hBh : c.symm '' Bh ⊆ Obs) (hgc : ContinuousOn g (R ∪ Lr))
    (hgLr : ∀ y ∈ Lr, g y = y) (hgR : MapsTo g R R) (hgT : ∀ y ∈ R, g y ∉ T)
    (hTR : T ⊆ R ∪ Bh) (hRH : c.symm '' R ⊆ Hs)
    (hRobs : c.symm '' R ⊆ Obs ∨ Disjoint (c.symm '' R) Obs)
    (hRfr : Disjoint (c.symm '' R) (frontier Hs)) (hMkR : Disjoint Mk (c.symm '' R))
    (hRY : Disjoint R Y) :
    ∃ r : M → M, ContinuousOn r (Hs \ Obs) ∧
      MapsTo r (Hs \ Obs) (Hs \ (Obs ∪ c.symm '' (Y ∪ T))) ∧
      (∀ z ∈ frontier Hs, r z = z) ∧ ∀ y ∈ Mk, r y = y := by
  obtain ⟨p, hp⟩ := hHne
  obtain ⟨r₁, hr₁c, hr₁m, hr₁fr, hr₁k, -⟩ :=
    exists_reroute_collapse hY hYt hYfr hYH hMkY hp hHs hObsH
  obtain ⟨r₂, hr₂c, hr₂m, hr₂fr, hr₂k, hr₂id, hr₂in⟩ :=
    exists_reroute_push hRo hclR hclRc hclRt hLrt hTt hBh hgc hgLr hgR hgT hTR hRH hRobs hRfr
      hMkR
  have hRt : R ⊆ c.target := subset_closure.trans hclRt
  have hr₂Z : ∀ y ∈ Hs \ (Obs ∪ c.symm '' Y), r₂ y ∉ c.symm '' Y := by
    intro y hy
    have hyD : y ∈ Hs \ Obs := ⟨hy.1, fun h' => hy.2 (Or.inl h')⟩
    by_cases hyR : y ∈ c.symm '' R
    · obtain ⟨x', hx', hx'e⟩ := hr₂in y hyD hyR
      rintro ⟨x, hx, hxe⟩
      rw [← hxe] at hx'e
      have hxx := c.symm.injOn (hRt hx') (hYt hx) hx'e
      rw [hxx] at hx'
      exact Set.disjoint_left.mp hRY hx' hx
    · rw [hr₂id y hyD hyR]
      exact fun h' => hy.2 (Or.inr h')
  obtain ⟨r, hrc, hrm, hrfr, hrk⟩ :=
    exists_reroute_comp hr₁c hr₁m hr₁fr hr₁k hr₂c hr₂m hr₂fr hr₂k hr₂Z
  refine ⟨r, hrc, fun y hy => ?_, hrfr, hrk⟩
  have h1 := hrm hy
  refine ⟨h1.1, fun h2 => h1.2 ?_⟩
  rw [image_union] at h2
  rcases h2 with h2 | h2 | h2
  · exact Or.inl h2
  · exact Or.inr (Or.inl h2)
  · exact Or.inr (Or.inr h2)

end DifferentialGeometry.Topology.PiecewiseLinear
