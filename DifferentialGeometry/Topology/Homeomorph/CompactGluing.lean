/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import Mathlib.Topology.Homeomorph.Lemmas

open Set

namespace Homeomorph

theorem exists_gluing_of_isCompact
    {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] [T2Space X] [T2Space Y]
    {P Q : Set X} {P' Q' : Set Y} (hP : IsCompact P) (hQ : IsCompact Q)
    {f g : X → Y} (hf : ContinuousOn f P) (hg : ContinuousOn g Q)
    (hfb : BijOn f P P') (hgb : BijOn g Q Q')
    (hfg : EqOn f g (P ∩ Q)) (hinter : SurjOn f (P ∩ Q) (P' ∩ Q')) :
    ∃ e : ↥(P ∪ Q) ≃ₜ ↥(P' ∪ Q'),
      (∀ (x : X) (hx : x ∈ P), (e ⟨x, Or.inl hx⟩ : Y) = f x) ∧
      ∀ (x : X) (hx : x ∈ Q), (e ⟨x, Or.inr hx⟩ : Y) = g x := by
  classical
  let h := P.piecewise f g
  have hPf : EqOn h f P := fun _ hx => piecewise_eq_of_mem P _ _ hx
  have hQg : EqOn h g Q := by
    intro x hxQ
    by_cases hxP : x ∈ P
    · exact (hPf hxP).trans (hfg ⟨hxP, hxQ⟩)
    · exact piecewise_eq_of_notMem P _ _ hxP
  have hcross {x y : X} (hx : x ∈ P) (hy : y ∈ Q) (hxy : f x = g y) : x = y := by
    obtain ⟨z, hz, hzx⟩ := hinter ⟨hfb.mapsTo hx, hxy.symm ▸ hgb.mapsTo hy⟩
    exact (hfb.injOn hz.1 hx hzx).symm.trans
      (hgb.injOn hz.2 hy ((hfg hz).symm.trans (hzx.trans hxy)))
  have hinj : InjOn h (P ∪ Q) := by
    intro x hx y hy hxy
    rcases hx with hx | hx <;> rcases hy with hy | hy
    · rw [hPf hx, hPf hy] at hxy
      exact hfb.injOn hx hy hxy
    · rw [hPf hx, hQg hy] at hxy
      exact hcross hx hy hxy
    · rw [hQg hx, hPf hy] at hxy
      exact (hcross hy hx hxy.symm).symm
    · rw [hQg hx, hQg hy] at hxy
      exact hgb.injOn hx hy hxy
  have hbij : BijOn h (P ∪ Q) (P' ∪ Q') := by
    refine ⟨?_, hinj, ?_⟩
    · intro x hx
      rcases hx with hx | hx
      · rw [hPf hx]
        exact Or.inl (hfb.mapsTo hx)
      · rw [hQg hx]
        exact Or.inr (hgb.mapsTo hx)
    · intro y hy
      rcases hy with hy | hy
      · obtain ⟨x, hx, hxy⟩ := hfb.surjOn hy
        exact ⟨x, Or.inl hx, (hPf hx).trans hxy⟩
      · obtain ⟨x, hx, hxy⟩ := hgb.surjOn hy
        exact ⟨x, Or.inr hx, (hQg hx).trans hxy⟩
  have hc : ContinuousOn h (P ∪ Q) :=
    (hf.congr hPf).union_of_isClosed (hg.congr hQg) hP.isClosed hQ.isClosed
  let _ : CompactSpace ↥(P ∪ Q) := isCompact_iff_compactSpace.mp (hP.union hQ)
  let d : ↥(P ∪ Q) ≃ ↥(P' ∪ Q') := hbij.equiv h
  have hd : Continuous d := hc.domRestrict.subtype_mk _
  exact ⟨hd.homeoOfEquivCompactToT2, fun _ hx => hPf hx, fun _ hx => hQg hx⟩

end Homeomorph
