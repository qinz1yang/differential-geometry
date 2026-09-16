import DifferentialGeometry.Topology.PlanarJordan.ArcExtension
import DifferentialGeometry.Topology.PlanarJordan.Transport

open Set

namespace DifferentialGeometry.Topology.PlanarJordan

open Schoenflies

theorem arc_inter_curve_eq_pair {C P : Set Plane} {p q : Plane}
    (hP : IsArcBetween P p q) (hp : p ∈ C) (hq : q ∈ C)
    (hPC : P \ {p, q} ⊆ inside C) : P ∩ C = {p, q} := by
  apply Subset.antisymm
  · intro x hx
    by_contra hxends
    exact (hPC ⟨hx.1, hxends⟩).1 hx.2
  · exact pair_subset ⟨hP.left_mem, hp⟩ ⟨hP.right_mem, hq⟩

theorem isJordanCurve_cut_arc_union {C P A₁ A₂ : Set Plane} {p q : Plane}
    (hP : IsArcBetween P p q) (hcut : IsCutPair C p q A₁ A₂)
    (hPC : P \ {p, q} ⊆ inside C) : IsJordanCurve (A₁ ∪ P) := by
  apply Schoenflies.isJordanCurve_union hcut.fst hP
  intro x hxA hxP
  have hx := (arc_inter_curve_eq_pair hP (hcut.fst_subset hcut.fst.left_mem)
    (hcut.fst_subset hcut.fst.right_mem) hPC).subset ⟨hxP, hcut.fst_subset hxA⟩
  simpa only [mem_insert_iff, mem_singleton_iff] using hx

theorem crosscut_regions {C P A₁ A₂ : Set Plane} {p q : Plane}
    (hC : IsJordanCurve C) (hP : IsArcBetween P p q)
    (hcut : IsCutPair C p q A₁ A₂) (hPC : P \ {p, q} ⊆ inside C) :
    inside C \ P = inside (A₁ ∪ P) ∪ inside (A₂ ∪ P) ∧
      Disjoint (inside (A₁ ∪ P)) (inside (A₂ ∪ P)) ∧
      closure (inside (A₁ ∪ P)) ∩ C = A₁ ∧
      closure (inside (A₂ ∪ P)) ∩ C = A₂ := by
  have hp := hcut.fst_subset hcut.fst.left_mem
  have hq := hcut.fst_subset hcut.fst.right_mem
  have hmeet := arc_inter_curve_eq_pair hP hp hq hPC
  obtain ⟨e, heP, _⟩ := exists_homeomorph_image_arc_polygonal hP hcut.fst (by
    intro x hxP hxA
    have hx := hmeet.subset ⟨hxP, hcut.fst_subset hxA⟩
    simpa only [mem_insert_iff, mem_singleton_iff] using hx)
  have hcross : Schoenflies.IsCrosscut (e '' C) (e '' P) (e p) (e q) := by
    refine ⟨isJordanCurve_image e hC, isArcBetween_image e hP, heP,
      mem_image_of_mem e hp, mem_image_of_mem e hq, ?_⟩
    rintro y ⟨⟨x, hxP, rfl⟩, hxends⟩
    rw [← image_inside]
    refine ⟨x, hPC ⟨hxP, ?_⟩, rfl⟩
    intro hx
    rcases hx with rfl | rfl
    · exact hxends (by simp)
    · exact hxends (by simp)
  have hcut' : IsCutPair (e '' C) (e p) (e q) (e '' A₁) (e '' A₂) := by
    refine ⟨isArcBetween_image e hcut.fst, isArcBetween_image e hcut.snd, ?_, ?_⟩
    · rw [← image_union, hcut.union_eq]
    · rw [← image_inter e.injective, hcut.inter_eq]
      simp only [image_insert_eq, image_singleton]
  obtain ⟨hcover, hdis, _, _, _, _, _, _, htrace₁, htrace₂⟩ :=
    Schoenflies.crosscut_theorem hcross hcut'
  refine ⟨?_, ?_, ?_, ?_⟩
  · apply e.injective.image_injective
    simpa only [image_sdiff e.injective, image_union, image_inside] using hcover
  · rw [disjoint_iff_inter_eq_empty]
    apply e.injective.image_injective
    simpa only [image_inter e.injective, image_inside, image_union, image_empty] using
      disjoint_iff_inter_eq_empty.mp hdis
  · apply e.injective.image_injective
    simpa only [image_inter e.injective, e.image_closure, image_inside, image_union] using htrace₁
  · apply e.injective.image_injective
    simpa only [image_inter e.injective, e.image_closure, image_inside, image_union] using htrace₂

theorem closed_crosscut_regions {C P A₁ A₂ : Set Plane} {p q : Plane}
    (hC : IsJordanCurve C) (hP : IsArcBetween P p q)
    (hcut : IsCutPair C p q A₁ A₂) (hPC : P \ {p, q} ⊆ inside C) :
    closure (inside (A₁ ∪ P)) ∪ closure (inside (A₂ ∪ P)) = C ∪ inside C ∧
      closure (inside (A₁ ∪ P)) ∩ closure (inside (A₂ ∪ P)) = P := by
  obtain ⟨hcover, hdis, _, _⟩ := crosscut_regions hC hP hcut hPC
  have hcl₁ := (IsRegionOf.inside (A₁ ∪ P)).closure_eq
    (jordan_curve_theorem (isJordanCurve_cut_arc_union hP hcut hPC))
  have hcl₂ := (IsRegionOf.inside (A₂ ∪ P)).closure_eq
    (jordan_curve_theorem (isJordanCurve_cut_arc_union hP hcut.symm hPC))
  have hside₁ : inside (A₁ ∪ P) ⊆ inside C \ P :=
    fun _ hx => hcover.symm ▸ Or.inl hx
  have hside₂ : inside (A₂ ∪ P) ⊆ inside C \ P :=
    fun _ hx => hcover.symm ▸ Or.inr hx
  have hPsub : P ⊆ C ∪ inside C := by
    intro x hx
    by_cases hends : x ∈ ({p, q} : Set Plane)
    · rcases hends with rfl | rfl
      · exact Or.inl (hcut.fst_subset hcut.fst.left_mem)
      · exact Or.inl (hcut.fst_subset hcut.fst.right_mem)
    · exact Or.inr (hPC ⟨hx, hends⟩)
  rw [hcl₁, hcl₂]
  constructor
  · apply Subset.antisymm
    · apply union_subset
      · exact union_subset (fun _ hx => Or.inr (hside₁ hx).1)
          (union_subset (fun _ hx => Or.inl (hcut.fst_subset hx)) hPsub)
      · exact union_subset (fun _ hx => Or.inr (hside₂ hx).1)
          (union_subset (fun _ hx => Or.inl (hcut.snd_subset hx)) hPsub)
    · intro x hx
      rcases hx with hx | hx
      · rw [← hcut.union_eq] at hx
        exact hx.elim (fun h => Or.inl (Or.inr (Or.inl h)))
          (fun h => Or.inr (Or.inr (Or.inl h)))
      · by_cases hxP : x ∈ P
        · exact Or.inl (Or.inr (Or.inr hxP))
        · have hxside : x ∈ inside (A₁ ∪ P) ∪ inside (A₂ ∪ P) :=
            hcover ▸ ⟨hx, hxP⟩
          exact hxside.elim (fun h => Or.inl (Or.inl h)) (fun h => Or.inr (Or.inl h))
  · apply Subset.antisymm
    · rintro x ⟨hx₁, hx₂⟩
      by_contra hxP
      have h₁ : x ∈ inside (A₁ ∪ P) ∨ x ∈ A₁ := by
        rcases hx₁ with hx | hx | hx
        · exact Or.inl hx
        · exact Or.inr hx
        · exact (hxP hx).elim
      have h₂ : x ∈ inside (A₂ ∪ P) ∨ x ∈ A₂ := by
        rcases hx₂ with hx | hx | hx
        · exact Or.inl hx
        · exact Or.inr hx
        · exact (hxP hx).elim
      rcases h₁ with h₁ | h₁ <;> rcases h₂ with h₂ | h₂
      · exact disjoint_left.mp hdis h₁ h₂
      · exact (hside₁ h₁).1.1 (hcut.snd_subset h₂)
      · exact (hside₂ h₂).1.1 (hcut.fst_subset h₁)
      · have hends := hcut.inter_eq.subset ⟨h₁, h₂⟩
        rcases hends with rfl | rfl
        · exact hxP hP.left_mem
        · exact hxP hP.right_mem
    · exact fun _ hx => ⟨Or.inr (Or.inr hx), Or.inr (Or.inr hx)⟩

theorem subset_crosscut_side_of_mem_closure {C P A₁ A₂ R : Set Plane} {p q r : Plane}
    (hC : IsJordanCurve C) (hP : IsArcBetween P p q)
    (hcut : IsCutPair C p q A₁ A₂) (hPC : P \ {p, q} ⊆ inside C)
    (hR : IsPreconnected R) (hRC : R ⊆ inside C \ P)
    (hr : r ∈ closure R) (hrA : r ∈ A₁ \ {p, q}) : R ⊆ inside (A₁ ∪ P) := by
  obtain ⟨hcover, hdis, _, htrace⟩ := crosscut_regions hC hP hcut hPC
  have hsep₁ := jordan_curve_theorem (isJordanCurve_cut_arc_union hP hcut hPC)
  have hsep₂ := jordan_curve_theorem (isJordanCurve_cut_arc_union hP hcut.symm hPC)
  rcases hR.subset_or_subset hsep₁.isOpen_inside hsep₂.isOpen_inside hdis
      (hRC.trans hcover.subset) with hsub | hsub
  · exact hsub
  · have hrA₂ : r ∈ A₂ := htrace.subset
      ⟨closure_mono hsub hr, hcut.fst_subset hrA.1⟩
    exact (hrA.2 (hcut.inter_eq.subset ⟨hrA.1, hrA₂⟩)).elim

theorem arc_diff_subset_crosscut_side {C P A₁ A₂ R : Set Plane} {p q v r : Plane}
    (hC : IsJordanCurve C) (hP : IsArcBetween P p q)
    (hcut : IsCutPair C p q A₁ A₂) (hPC : P \ {p, q} ⊆ inside C)
    (hR : IsArcBetween R v r) (hRC : R \ {v, r} ⊆ inside C \ P)
    (hrA : r ∈ A₁ \ {p, q}) : R \ {v, r} ⊆ inside (A₁ ∪ P) :=
  subset_crosscut_side_of_mem_closure hC hP hcut hPC hR.isPreconnected_diff hRC
    hR.right_mem_closure_diff hrA
end DifferentialGeometry.Topology.PlanarJordan
