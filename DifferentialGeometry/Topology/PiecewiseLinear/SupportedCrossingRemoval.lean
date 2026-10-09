/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import Mathlib.Topology.Homeomorph.Defs
import Mathlib.Data.Set.Card

open Set

namespace DifferentialGeometry.Topology.PiecewiseLinear

theorem image_inter_eq_sdiff_of_supported_disjoint {X : Type*} {f : X → X}
    (hf : Function.Injective f) {K A C : Set X} (hfix : EqOn f id Kᶜ)
    (hdisj : Disjoint (f '' (A ∩ K)) (C ∩ K)) :
    f '' A ∩ C = (A ∩ C) \ K := by
  have hmaps : MapsTo f K K := by
    intro x hx
    by_contra hfx
    exact hfx ((hf (hfix hfx)).symm ▸ hx)
  ext y
  constructor
  · rintro ⟨⟨x, hx, rfl⟩, hxc⟩
    have hxK : x ∉ K := fun hxK =>
      disjoint_left.mp hdisj ⟨x, ⟨hx, hxK⟩, rfl⟩ ⟨hxc, hmaps hxK⟩
    rw [hfix hxK] at hxc ⊢
    exact ⟨⟨hx, hxc⟩, hxK⟩
  · rintro ⟨⟨hyA, hyC⟩, hyK⟩
    exact ⟨⟨y, hyA, hfix hyK⟩, hyC⟩

theorem ncard_image_inter_add_two_of_supported_disjoint {X : Type*} {f : X → X}
    (hf : Function.Injective f) {K A C : Set X} (hfix : EqOn f id Kᶜ)
    (hdisj : Disjoint (f '' (A ∩ K)) (C ∩ K))
    {p q : X} (hpq : p ≠ q) (hcross : (A ∩ C) ∩ K = {p, q})
    (hfin : (A ∩ C).Finite) : (f '' A ∩ C).ncard + 2 = (A ∩ C).ncard := by
  rw [image_inter_eq_sdiff_of_supported_disjoint hf hfix hdisj]
  have hcard := ncard_inter_add_ncard_sdiff_eq_ncard (A ∩ C) K hfin
  rw [hcross, ncard_pair hpq] at hcard
  omega

end DifferentialGeometry.Topology.PiecewiseLinear
