/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.PLHomeomorphGluing

open Set

namespace DifferentialGeometry.Topology.PiecewiseLinear

private theorem image_sdiff_of_fixed_complement {α : Type*} {f : α → α} {P Q R O : Set α}
    (h : BijOn f P Q) (hRP : R ⊆ P) (hout : Q \ O = P \ O)
    (hfix : EqOn f id (P \ O)) : (f '' R) \ O = R \ O := by
  ext y
  constructor
  · rintro ⟨⟨x, hxR, rfl⟩, hfxO⟩
    have hfxP : f x ∈ P \ O := hout.subset ⟨h.mapsTo (hRP hxR), hfxO⟩
    have heq : x = f x := h.injOn (hRP hxR) hfxP.1 (hfix hfxP).symm
    exact ⟨heq ▸ hxR, hfxO⟩
  · rintro ⟨hyR, hyO⟩
    exact ⟨⟨y, hyR, hfix ⟨hRP hyR, hyO⟩⟩, hyO⟩

theorem exists_partition_of_isPLHomeomorphOn_union
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {P₀ P₁ D Q O : Set E} {f : E → E}
    (hP₀ : IsPolyhedron P₀) (hP₁ : IsPolyhedron P₁) (hD : IsPolyhedron D)
    (hdis : Disjoint (P₀ ∪ D) P₁) (hDO : D ⊆ O)
    (hf : IsPLHomeomorphOn f ((P₀ ∪ P₁) ∪ D) Q)
    (hout : Q \ O = (P₀ ∪ P₁) \ O) (hfix : EqOn f id ((P₀ ∪ P₁) \ O)) :
    ∃ Q₀ Q₁ : Set E, IsPLHomeomorphOn f (P₀ ∪ D) Q₀ ∧ IsPLHomeomorphOn f P₁ Q₁ ∧
      IsPolyhedron Q₀ ∧ IsPolyhedron Q₁ ∧ Disjoint Q₀ Q₁ ∧ Q = Q₀ ∪ Q₁ ∧
      Q₀ \ O = P₀ \ O ∧ Q₁ \ O = P₁ \ O := by
  have h₀sub : P₀ ∪ D ⊆ (P₀ ∪ P₁) ∪ D := by
    rintro x (hx₀ | hxD)
    · exact Or.inl (Or.inl hx₀)
    · exact Or.inr hxD
  have h₁sub : P₁ ⊆ (P₀ ∪ P₁) ∪ D := fun x hx => Or.inl (Or.inr hx)
  have hsource : (P₀ ∪ P₁) ∪ D = (P₀ ∪ D) ∪ P₁ := by
    ext x
    simp only [mem_union]
    tauto
  have hsourceOut : ((P₀ ∪ P₁) ∪ D) \ O = (P₀ ∪ P₁) \ O := by
    rw [union_sdiff_distrib, sdiff_eq_empty.mpr hDO, union_empty]
  have hfixed : EqOn f id (((P₀ ∪ P₁) ∪ D) \ O) := by
    rw [hsourceOut]
    exact hfix
  have htarget : Q \ O = ((P₀ ∪ P₁) ∪ D) \ O := hout.trans hsourceOut.symm
  have hf₀ := hf.restrict (hP₀.union hD) h₀sub
  have hf₁ := hf.restrict hP₁ h₁sub
  refine ⟨f '' (P₀ ∪ D), f '' P₁, hf₀, hf₁,
    (hP₀.union hD).image_of_isPiecewiseAffineOn hf₀.isPiecewiseAffineOn hf₀.bijOn.injOn,
    hP₁.image_of_isPiecewiseAffineOn hf₁.isPiecewiseAffineOn hf₁.bijOn.injOn, ?_, ?_, ?_, ?_⟩
  · apply disjoint_left.mpr
    rintro y ⟨a, ha, hay⟩ ⟨b, hb, hby⟩
    have hab := hf.bijOn.injOn (h₀sub ha) (h₁sub hb) (hay.trans hby.symm)
    exact disjoint_left.mp hdis ha (hab.symm ▸ hb)
  · rw [← hf.image_eq, hsource, image_union]
  · rw [image_sdiff_of_fixed_complement hf.bijOn h₀sub htarget hfixed,
      union_sdiff_distrib, sdiff_eq_empty.mpr hDO, union_empty]
  · exact image_sdiff_of_fixed_complement hf.bijOn h₁sub htarget hfixed

end DifferentialGeometry.Topology.PiecewiseLinear
