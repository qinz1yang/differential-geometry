/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.CapLevelPolygons

open Set

namespace DifferentialGeometry.Topology.PiecewiseLinear

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem encard_levelPolygons_triangle_cap_pair_add_eq
    {A B D S : Set E} (hA : IsClosed A) (hB : IsClosed B)
    (hAB : A ∩ B ⊆ D) (hunion : A ∪ B = S) (H : E ≃ₜ E)
    (f : E → ℝ) (p : E)
    (hcap : ∀ x ∈ H '' D \ {H p}, f (H p) < f x) :
    (levelPolygons (H '' (A ∪ D)) f (f (H p))).encard +
        (levelPolygons (H '' (B ∪ D)) f (f (H p))).encard =
      (levelPolygons (H '' S) f (f (H p))).encard := by
  have hHA : IsClosed (H '' A) := H.isClosedMap A hA
  have hHB : IsClosed (H '' B) := H.isClosedMap B hB
  have hcapfiber : (H '' D) ∩ {x | f x = f (H p)} ⊆ {H p} := by
    intro x hx
    by_cases hxp : x = H p
    · exact hxp
    · exact ((hcap x ⟨hx.1, hxp⟩).ne hx.2.symm).elim
  have hinter : ((H '' A) ∩ (H '' B)) ∩ {x | f x = f (H p)} ⊆ {H p} := by
    intro x hx
    apply hcapfiber
    refine ⟨?_, hx.2⟩
    obtain ⟨a, ha, hax⟩ := hx.1.1
    obtain ⟨b, hb, hbx⟩ := hx.1.2
    have hab : a = b := H.injective (hax.trans hbx.symm)
    exact ⟨a, hAB ⟨ha, hab ▸ hb⟩, hax⟩
  calc
    (levelPolygons (H '' (A ∪ D)) f (f (H p))).encard +
        (levelPolygons (H '' (B ∪ D)) f (f (H p))).encard =
        (levelPolygons (H '' A) f (f (H p))).encard +
          (levelPolygons (H '' B) f (f (H p))).encard := by
      rw [image_union, image_union,
        levelPolygons_union_cap_of_fiber_subset_singleton hHA f (f (H p)) (H p) hcapfiber,
        levelPolygons_union_cap_of_fiber_subset_singleton hHB f (f (H p)) (H p) hcapfiber]
    _ = (levelPolygons ((H '' A) ∪ (H '' B)) f (f (H p))).encard :=
      (encard_levelPolygons_union_of_fiber_inter_subset_singleton
        hHA hHB f (f (H p)) (H p) hinter).symm
    _ = (levelPolygons (H '' S) f (f (H p))).encard := by
      rw [← image_union, hunion]

end DifferentialGeometry.Topology.PiecewiseLinear
