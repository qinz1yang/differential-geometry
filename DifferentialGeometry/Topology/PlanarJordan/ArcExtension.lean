import DifferentialGeometry.External.Schoenflies.JordanSchoenflies
import DifferentialGeometry.External.Schoenflies.MatchedArc
import DifferentialGeometry.Topology.Homeomorph.CompactGluing

open Set

namespace DifferentialGeometry.Topology.PlanarJordan

open Schoenflies

theorem exists_homeomorph_extending_two_arcs
    {A B A' B' : Set Plane} {p q p' q' : Plane}
    (hA : IsArcBetween A p q) (hB : IsArcBetween B p q)
    (hA' : IsArcBetween A' p' q') (hB' : IsArcBetween B' p' q')
    (hmeet : ∀ x ∈ A, x ∈ B → x = p ∨ x = q)
    (hmeet' : ∀ x ∈ A', x ∈ B' → x = p' ∨ x = q')
    (f : ArcHomeo A A' p q p' q') (g : ArcHomeo B B' p q p' q') :
    ∃ e : Plane ≃ₜ Plane, EqOn e f.toFun A ∧ EqOn e g.toFun B := by
  have hagree : EqOn f.toFun g.toFun (A ∩ B) := by
    intro x hx
    rcases hmeet x hx.1 hx.2 with rfl | rfl
    · rw [f.map_left, g.map_left]
    · rw [f.map_right, g.map_right]
  have hsurj : SurjOn f.toFun (A ∩ B) (A' ∩ B') := by
    intro y hy
    rcases hmeet' y hy.1 hy.2 with rfl | rfl
    · exact ⟨p, ⟨hA.left_mem, hB.left_mem⟩, f.map_left⟩
    · exact ⟨q, ⟨hA.right_mem, hB.right_mem⟩, f.map_right⟩
  have hfb : BijOn f.toFun A A' :=
    ⟨f.mapsTo, f.injOn, fun _ hy => f.image_eq.symm ▸ hy⟩
  have hgb : BijOn g.toFun B B' :=
    ⟨g.mapsTo, g.injOn, fun _ hy => g.image_eq.symm ▸ hy⟩
  obtain ⟨d, hdA, hdB⟩ := Homeomorph.exists_gluing_of_isCompact
    hA.isArc.isCompact hB.isArc.isCompact f.continuousOn_toFun g.continuousOn_toFun
    hfb hgb hagree hsurj
  obtain ⟨e, he⟩ := jordan_schoenflies_of_homeomorph
    (Schoenflies.isJordanCurve_union hA hB hmeet)
    (Schoenflies.isJordanCurve_union hA' hB' hmeet') d
  exact ⟨e, fun x hx => (he ⟨x, Or.inl hx⟩).trans (hdA x hx),
    fun x hx => (he ⟨x, Or.inr hx⟩).trans (hdB x hx)⟩

theorem exists_homeomorph_image_two_arcs
    {A B A' B' : Set Plane} {p q p' q' : Plane}
    (hA : IsArcBetween A p q) (hB : IsArcBetween B p q)
    (hA' : IsArcBetween A' p' q') (hB' : IsArcBetween B' p' q')
    (hmeet : ∀ x ∈ A, x ∈ B → x = p ∨ x = q)
    (hmeet' : ∀ x ∈ A', x ∈ B' → x = p' ∨ x = q') :
    ∃ e : Plane ≃ₜ Plane, e '' A = A' ∧ e '' B = B' ∧ e p = p' ∧ e q = q' := by
  obtain ⟨f⟩ := exists_arcHomeo hA hA'
  obtain ⟨g⟩ := exists_arcHomeo hB hB'
  obtain ⟨e, heA, heB⟩ :=
    exists_homeomorph_extending_two_arcs hA hB hA' hB' hmeet hmeet' f g
  exact ⟨e, heA.image_eq.trans f.image_eq, heB.image_eq.trans g.image_eq,
    (heA hA.left_mem).trans f.map_left, (heA hA.right_mem).trans f.map_right⟩

theorem exists_homeomorph_image_arc_polygonal
    {A B : Set Plane} {p q : Plane}
    (hA : IsArcBetween A p q) (hB : IsArcBetween B p q)
    (hmeet : ∀ x ∈ A, x ∈ B → x = p ∨ x = q) :
    ∃ e : Plane ≃ₜ Plane, IsPolygonal (e '' A) ∧ IsPolygonal (e '' B) := by
  obtain ⟨e, heA, heB, _, _⟩ := exists_homeomorph_image_two_arcs hA hB
    isArcBetween_upperSides isArcBetween_lowerSides.reverse hmeet upperSides_meet_lowerSides
  refine ⟨e, ?_, ?_⟩
  · rw [heA]
    exact ⟨[cornerNE, cornerNW, cornerSW], by
      rw [poly_cons_cons, poly_pair]; rfl⟩
  · rw [heB]
    exact ⟨[cornerSW, cornerSE, cornerNE], by
      rw [poly_cons_cons, poly_pair]; rfl⟩

end DifferentialGeometry.Topology.PlanarJordan
