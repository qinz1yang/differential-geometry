/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.ChartDiskMove
import DifferentialGeometry.Topology.PiecewiseLinear.SupportedCrossingRemoval

open Set

namespace DifferentialGeometry.Topology.PiecewiseLinear

local notation "Plane" => EuclideanSpace ℝ (Fin 2)

variable {X : Type*} [TopologicalSpace X]

theorem disjoint_image_inter_of_chart_disk_move (e : OpenPartialHomeomorph X (Plane × ℝ))
    {P A C : Set Plane} {δ : ℝ} (hδ : 0 ≤ δ)
    (hbox : P ×ˢ Icc (-δ) δ ⊆ e.target) {u : Plane → Plane} (hu : MapsTo u P P)
    {Φ : X → X} {B D : Set X}
    (hplane : ∀ x ∈ e.symm '' (P ×ˢ Icc (-δ) δ),
      (e (Φ x)).2 = 0 ↔ (e x).2 = 0)
    (hmodel : ∀ x ∈ P, Φ (e.symm (x, 0)) = e.symm (u x, 0))
    (hB : ∀ x ∈ P, e.symm (x, 0) ∈ B ↔ x ∈ A)
    (hD : ∀ z ∈ P ×ˢ Icc (-δ) δ, e.symm z ∈ D ↔ z.2 = 0 ∧ z.1 ∈ C)
    (hdisj : Disjoint (u '' (A ∩ P)) (C ∩ P)) :
    Disjoint (Φ '' (B ∩ e.symm '' (P ×ˢ Icc (-δ) δ)))
      (D ∩ e.symm '' (P ×ˢ Icc (-δ) δ)) := by
  refine disjoint_left.mpr ?_
  rintro y ⟨x, ⟨hxB, w, hw, rfl⟩, rfl⟩ ⟨hxD, z, hz, hzx⟩
  have hzD : e.symm z ∈ D := hzx.symm ▸ hxD
  have hz0 : z.2 = 0 := ((hD z hz).mp hzD).1
  have hw0 : w.2 = 0 := by
    have hp := (hplane (e.symm w) ⟨w, hw, rfl⟩).mp
      (show (e (Φ (e.symm w))).2 = 0 from by rw [← hzx, e.right_inv (hbox hz)]; exact hz0)
    rwa [e.right_inv (hbox hw)] at hp
  have hew : w = (w.1, 0) := Prod.ext rfl hw0
  have hwA : w.1 ∈ A := (hB w.1 hw.1).mp (hew ▸ hxB)
  have huw : (u w.1, (0 : ℝ)) ∈ P ×ˢ Icc (-δ) δ :=
    ⟨hu hw.1, neg_nonpos.mpr hδ, hδ⟩
  have heq : z = (u w.1, 0) := by
    apply e.symm.injOn (hbox hz) (hbox huw)
    rw [hzx, hew, hmodel w.1 hw.1]
  have huC : u w.1 ∈ C := by
    have hzC := ((hD z hz).mp hzD).2
    simpa only [heq] using hzC
  exact disjoint_left.mp hdisj ⟨w.1, ⟨hwA, hw.1⟩, rfl⟩ ⟨huC, hu hw.1⟩

theorem crossings_inter_chart_prism (e : OpenPartialHomeomorph X (Plane × ℝ))
    {P A C : Set Plane} {δ : ℝ} (hδ : 0 ≤ δ) {B D : Set X}
    (hB : ∀ x ∈ P, e.symm (x, 0) ∈ B ↔ x ∈ A)
    (hD : ∀ z ∈ P ×ˢ Icc (-δ) δ, e.symm z ∈ D ↔ z.2 = 0 ∧ z.1 ∈ C) :
    (B ∩ D) ∩ e.symm '' (P ×ˢ Icc (-δ) δ) =
      (fun x => e.symm (x, 0)) '' ((A ∩ C) ∩ P) := by
  ext y
  constructor
  · rintro ⟨⟨hyB, hyD⟩, z, hz, rfl⟩
    obtain ⟨hz0, hzC⟩ := (hD z hz).mp hyD
    have heq : z = (z.1, 0) := Prod.ext rfl hz0
    have hzA : z.1 ∈ A := (hB z.1 hz.1).mp (heq ▸ hyB)
    exact ⟨z.1, ⟨⟨hzA, hzC⟩, hz.1⟩, congrArg e.symm heq.symm⟩
  · rintro ⟨x, ⟨⟨hxA, hxC⟩, hxP⟩, rfl⟩
    have hxbox : (x, (0 : ℝ)) ∈ P ×ˢ Icc (-δ) δ :=
      ⟨hxP, neg_nonpos.mpr hδ, hδ⟩
    exact ⟨⟨(hB x hxP).mpr hxA, (hD (x, 0) hxbox).mpr ⟨rfl, hxC⟩⟩,
      (x, 0), hxbox, rfl⟩

end DifferentialGeometry.Topology.PiecewiseLinear
