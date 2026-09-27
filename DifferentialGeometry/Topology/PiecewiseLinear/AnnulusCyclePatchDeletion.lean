/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.AnnulusPatchDeletion
import DifferentialGeometry.Topology.PiecewiseLinear.ManifoldDisjointUnion

open Set Topology

namespace DifferentialGeometry.Topology.PiecewiseLinear

local notation "E3" => EuclideanSpace ℝ (Fin 3)

private theorem annulus_ends_nonempty {C J₀ J₁ : Set E3}
    (h : IsPLAnnulusWithEnds C J₀ J₁) : J₀.Nonempty ∧ J₁.Nonempty := by
  obtain ⟨J, ρ, hJ, -, h₀, h₁⟩ := h
  rw [h₀, h₁]
  exact ⟨(hJ.nonempty.prod (singleton_nonempty (0 : ℝ))).image ρ,
    (hJ.nonempty.prod (singleton_nonempty (1 : ℝ))).image ρ⟩

theorem IsPLAnnulusWithEnds.exists_closed_surface_annulus_cycle
    {C₀ C₁ B₀ B₁ J₀ J₁ K₀ K₁ : Set E3}
    (hC₀ : IsPLAnnulusWithEnds C₀ J₀ J₁) (hC₁ : IsPLAnnulusWithEnds C₁ K₀ K₁)
    (hB₀ : IsPLAnnulusWithEnds B₀ J₀ K₀) (hB₁ : IsPLAnnulusWithEnds B₁ J₁ K₁)
    (hCC : Disjoint C₀ C₁) (hBB : Disjoint B₀ B₁)
    (h₀₀ : C₀ ∩ B₀ = J₀) (h₀₁ : C₀ ∩ B₁ = J₁)
    (h₁₀ : C₁ ∩ B₀ = K₀) (h₁₁ : C₁ ∩ B₁ = K₁) :
    ∃ Q : Geometry.SimplicialComplex ℝ E3, Q.faces.Finite ∧
      IsCombinatorialManifold 2 Q ∧ IsConnected Q.space ∧
      Q.space = (C₀ ∪ C₁) ∪ (B₀ ∪ B₁) := by
  classical
  let _ : DecidableEq E3 := fun a b => Classical.propDecidable (a = b)
  obtain ⟨R₀, hR₀fin, hR₀, hR₀c, hR₀s, hR₀b⟩ := hC₀.exists_complex
  obtain ⟨R₁, hR₁fin, hR₁, hR₁c, hR₁s, hR₁b⟩ := hC₁.exists_complex
  obtain ⟨T₀, hT₀fin, hT₀, hT₀c, hT₀s, hT₀b⟩ := hB₀.exists_complex
  obtain ⟨T₁, hT₁fin, hT₁, hT₁c, hT₁s, hT₁b⟩ := hB₁.exists_complex
  let _ : Finite R₀.faces := hR₀fin.to_subtype
  let _ : Finite R₁.faces := hR₁fin.to_subtype
  let _ : Finite T₀.faces := hT₀fin.to_subtype
  let _ : Finite T₁.faces := hT₁fin.to_subtype
  obtain ⟨R, hRfin, hR, hRs, hRb⟩ := hR₀.exists_space_disjoint_union R₀ R₁ hR₁
    (by simpa only [hR₀s, hR₁s] using hCC)
  obtain ⟨T, hTfin, hT, hTs, hTb⟩ := hT₀.exists_space_disjoint_union T₀ T₁ hT₁
    (by simpa only [hT₀s, hT₁s] using hBB)
  let _ : Finite R.faces := hRfin.to_subtype
  let _ : Finite T.faces := hTfin.to_subtype
  have hmeet : R.space ∩ T.space = (J₀ ∪ J₁) ∪ (K₀ ∪ K₁) := by
    rw [hRs, hTs, hR₀s, hR₁s, hT₀s, hT₁s, union_inter_distrib_right,
      inter_union_distrib_left, inter_union_distrib_left, h₀₀, h₀₁, h₁₀, h₁₁]
  have hmeetR : R.space ∩ T.space = (boundaryComplex 2 R).space := by
    rw [hmeet, hRb, hR₀b, hR₁b]
  have hmeetT : R.space ∩ T.space = (boundaryComplex 2 T).space := by
    rw [hmeet, hTb, hT₀b, hT₁b]
    ext x
    simp only [mem_union]
    tauto
  obtain ⟨Q, hQfin, hQ, hQs⟩ :=
    exists_isCombinatorialManifold_space_union R T hR hT hmeetR hmeetT
  have hspace : Q.space = (C₀ ∪ C₁) ∪ (B₀ ∪ B₁) := by
    rw [hQs, hRs, hTs, hR₀s, hR₁s, hT₀s, hT₁s]
  have hC₀c : IsConnected C₀ := hR₀s ▸ hR₀c
  have hC₁c : IsConnected C₁ := hR₁s ▸ hR₁c
  have hB₀c : IsConnected B₀ := hT₀s ▸ hT₀c
  have hB₁c : IsConnected B₁ := hT₁s ▸ hT₁c
  have hJ₀ne : (C₀ ∩ B₀).Nonempty := h₀₀.symm ▸ (annulus_ends_nonempty hC₀).1
  have hK₀ne : ((C₀ ∪ B₀) ∩ C₁).Nonempty := by
    obtain ⟨x, hx⟩ := (annulus_ends_nonempty hC₁).1
    have hxm := h₁₀.symm.subset hx
    exact ⟨x, Or.inr hxm.2, hxm.1⟩
  have hJ₁ne : (((C₀ ∪ B₀) ∪ C₁) ∩ B₁).Nonempty := by
    obtain ⟨x, hx⟩ := (annulus_ends_nonempty hC₀).2
    have hxm := h₀₁.symm.subset hx
    exact ⟨x, Or.inl (Or.inl hxm.1), hxm.2⟩
  have hconn := ((hC₀c.union hJ₀ne hB₀c).union hK₀ne hC₁c).union hJ₁ne hB₁c
  have hreorder : ((C₀ ∪ B₀) ∪ C₁) ∪ B₁ = (C₀ ∪ C₁) ∪ (B₀ ∪ B₁) := by
    ext x
    simp only [mem_union]
    tauto
  exact ⟨Q, hQfin, hQ, hspace.symm ▸ hreorder ▸ hconn, hspace⟩

theorem IsPLAnnulusWithEnds.separates_after_delete_annulus_cycle_patch
    {C₀ C₁ B₀ B₁ J₀ J₁ K₀ K₁ U S M : Set E3}
    (hC₀ : IsPLAnnulusWithEnds C₀ J₀ J₁) (hC₁ : IsPLAnnulusWithEnds C₁ K₀ K₁)
    (hB₀ : IsPLAnnulusWithEnds B₀ J₀ K₀) (hB₁ : IsPLAnnulusWithEnds B₁ J₁ K₁)
    (hCC : Disjoint C₀ C₁) (hBB : Disjoint B₀ B₁)
    (h₀₀ : C₀ ∩ B₀ = J₀) (h₀₁ : C₀ ∩ B₁ = J₁)
    (h₁₀ : C₁ ∩ B₀ = K₀) (h₁₁ : C₁ ∩ B₁ = K₁)
    (hU : IsOpen U) (hS : IsTopologicalSolidTorus S) (hSU : S ⊆ U)
    (hCS : (C₀ ∪ C₁) ∪ (B₀ ∪ B₁) ⊆ interior S)
    (hCM : (C₀ ∪ C₁) ∪ (B₀ ∪ B₁) ⊆ M)
    (hR : IsClosed (((↑) : U → E3) ⁻¹' (M \ (C₀ \ (J₀ ∪ J₁)))))
    {a b : E3} (haS : a ∉ S) (hbS : b ∉ S)
    (hsep : Separates (((↑) : U → E3) ⁻¹' M) (((↑) : U → E3) ⁻¹' {a})
      (((↑) : U → E3) ⁻¹' {b})) :
    Separates (((↑) : U → E3) ⁻¹' (M \ (C₀ \ (J₀ ∪ J₁))))
      (((↑) : U → E3) ⁻¹' {a}) (((↑) : U → E3) ⁻¹' {b}) := by
  classical
  let _ : DecidableEq E3 := fun a b => Classical.propDecidable (a = b)
  obtain ⟨Q, hQfin, hQ, hQc, hQs⟩ := hC₀.exists_closed_surface_annulus_cycle
    hC₁ hB₀ hB₁ hCC hBB h₀₀ h₀₁ h₁₀ h₁₁
  let _ : Finite Q.faces := hQfin.to_subtype
  have hQM : Q.space ⊆ M := hQs.subset.trans hCM
  have hCQ : C₀ ⊆ Q.space :=
    subset_union_left.trans (subset_union_left.trans hQs.symm.subset)
  have hout : M \ Q.space = (M \ (C₀ \ (J₀ ∪ J₁))) \ Q.space := by
    ext x
    exact ⟨fun hx => ⟨⟨hx.1, fun hc => hx.2 (hCQ hc.1)⟩, hx.2⟩,
      fun hx => ⟨hx.1.1, hx.2⟩⟩
  have hpatchEq : Q.space \ (M \ (C₀ \ (J₀ ∪ J₁))) = C₀ \ (J₀ ∪ J₁) := by
    ext x
    constructor
    · intro hx
      by_contra hn
      exact hx.2 ⟨hQM hx.1, hn⟩
    · intro hx
      exact ⟨hCQ hx.1, fun hr => hr.2 hx⟩
  have hpatch : IsPreconnected (Q.space \ (M \ (C₀ \ (J₀ ∪ J₁)))) := by
    rw [hpatchEq]
    obtain ⟨K, hKfin, hK, hKc, hKC, hKb⟩ := hC₀.exists_complex
    let _ : Finite K.faces := hKfin.to_subtype
    simpa only [hKC, hKb] using
      (hK.isConnected_sdiff_boundaryComplex_space hKc).isPreconnected
  exact hQ.separates_of_connected_surface_patch Q hQc hU hS hSU
    (hQs.subset.trans hCS) hR hout hpatch haS hbS hsep

end DifferentialGeometry.Topology.PiecewiseLinear
