import DifferentialGeometry.External.Schoenflies.JordanSchoenflies
import DifferentialGeometry.External.Schoenflies.MatchedArc

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
  classical
  let h := A.piecewise f.toFun g.toFun
  have hf : EqOn h f.toFun A := fun _ hx => piecewise_eq_of_mem A _ _ hx
  have hagree : EqOn f.toFun g.toFun (A ∩ B) := by
    intro x hx
    rcases hmeet x hx.1 hx.2 with rfl | rfl
    · rw [f.map_left, g.map_left]
    · rw [f.map_right, g.map_right]
  have hg : EqOn h g.toFun B := by
    intro x hx
    by_cases hxA : x ∈ A
    · exact (hf hxA).trans (hagree ⟨hxA, hx⟩)
    · exact piecewise_eq_of_notMem A _ _ hxA
  have hsurj : SurjOn f.toFun (A ∩ B) (A' ∩ B') := by
    intro y hy
    rcases hmeet' y hy.1 hy.2 with rfl | rfl
    · exact ⟨p, ⟨hA.left_mem, hB.left_mem⟩, f.map_left⟩
    · exact ⟨q, ⟨hA.right_mem, hB.right_mem⟩, f.map_right⟩
  have hcross {x y : Plane} (hx : x ∈ A) (hy : y ∈ B)
      (hxy : f.toFun x = g.toFun y) : x = y := by
    obtain ⟨z, hz, hzx⟩ := hsurj ⟨f.mapsTo hx, hxy.symm ▸ g.mapsTo hy⟩
    exact (f.injOn hz.1 hx hzx).symm.trans
      (g.injOn hz.2 hy ((hagree hz).symm.trans (hzx.trans hxy)))
  have hinj : InjOn h (A ∪ B) := by
    intro x hx y hy hxy
    rcases hx with hx | hx <;> rcases hy with hy | hy
    · rw [hf hx, hf hy] at hxy
      exact f.injOn hx hy hxy
    · rw [hf hx, hg hy] at hxy
      exact hcross hx hy hxy
    · rw [hg hx, hf hy] at hxy
      exact (hcross hy hx hxy.symm).symm
    · rw [hg hx, hg hy] at hxy
      exact g.injOn hx hy hxy
  have hbij : BijOn h (A ∪ B) (A' ∪ B') := by
    refine ⟨?_, hinj, ?_⟩
    · intro x hx
      rcases hx with hx | hx
      · rw [hf hx]
        exact Or.inl (f.mapsTo hx)
      · rw [hg hx]
        exact Or.inr (g.mapsTo hx)
    · intro y hy
      rcases hy with hy | hy
      · obtain ⟨x, hx, hxy⟩ := f.image_eq.symm ▸ hy
        exact ⟨x, Or.inl hx, (hf hx).trans hxy⟩
      · obtain ⟨x, hx, hxy⟩ := g.image_eq.symm ▸ hy
        exact ⟨x, Or.inr hx, (hg hx).trans hxy⟩
  have hc : ContinuousOn h (A ∪ B) :=
    (f.continuousOn_toFun.congr hf).union_of_isClosed
      (g.continuousOn_toFun.congr hg) hA.isArc.isClosed hB.isArc.isClosed
  let _ : CompactSpace ↥(A ∪ B) :=
    isCompact_iff_compactSpace.mp (hA.isArc.isCompact.union hB.isArc.isCompact)
  let d : ↥(A ∪ B) ≃ ↥(A' ∪ B') := hbij.equiv h
  have hd : Continuous d := hc.domRestrict.subtype_mk _
  obtain ⟨e, he⟩ := jordan_schoenflies_of_homeomorph
    (Schoenflies.isJordanCurve_union hA hB hmeet)
    (Schoenflies.isJordanCurve_union hA' hB' hmeet')
    hd.homeoOfEquivCompactToT2
  refine ⟨e, ?_, ?_⟩
  · intro x hx
    exact (he ⟨x, Or.inl hx⟩).trans (hf hx)
  · intro x hx
    exact (he ⟨x, Or.inr hx⟩).trans (hg hx)

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
