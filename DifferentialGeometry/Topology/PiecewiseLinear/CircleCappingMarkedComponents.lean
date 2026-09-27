/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.CircleCappingComponentInvariants
import DifferentialGeometry.Topology.PiecewiseLinear.PLHomeomorphComponents

open Set

namespace DifferentialGeometry.Topology.PiecewiseLinear

local notation "E3" => EuclideanSpace ℝ (Fin 3)

theorem IsCircleCapping.exists_component_equiv_preserving_marks
    (K Q : Geometry.SimplicialComplex ℝ E3) [Finite K.faces] [Finite Q.faces]
    {T B : Set E3} (hcap : IsCircleCapping K.space Q.space T B) :
    ∃ G ∈ traceCircles K.space T, boundsDiskIn G T ∧
      ∃ e : ConnectedComponents K.space ≃ ConnectedComponents Q.space,
        ∀ c, (B \ G) ∩ (connectedComponentComplex K c).space ⊆
          (connectedComponentComplex Q (e c)).space := by
  obtain ⟨D, r, f, hr, hDT, hmeet, hG, -, hf, hfix⟩ := hcap
  obtain ⟨c₀, e, -, hcomp, -, -⟩ :=
    IsPLHomeomorphOn.exists_component_eulerChar_of_disk_attachment K Q hr hmeet hf
  refine ⟨r '' stdSimplexBoundary 2, hG, ⟨D, r, hr, hDT, rfl⟩, e, ?_⟩
  intro c x hx
  have hfx : f x = x := hfix hx.1
  exact hfx ▸ (hcomp c).bijOn.mapsTo (Or.inl hx.2)

theorem IsPLHomeomorphOn.exists_component_equiv_preserving_marks
    (K Q : Geometry.SimplicialComplex ℝ E3) [Finite K.faces]
    {f : E3 → E3} {B : Set E3} (hf : IsPLHomeomorphOn f K.space Q.space)
    (hfix : EqOn f id B) :
    ∃ e : ConnectedComponents K.space ≃ ConnectedComponents Q.space,
      ∀ c, B ∩ (connectedComponentComplex K c).space ⊆
        (connectedComponentComplex Q (e c)).space := by
  obtain ⟨e, he⟩ := hf.exists_component_equiv K Q
  refine ⟨e, fun c x hx => ?_⟩
  have hfx : f x = x := hfix hx.1
  exact hfx ▸ (he c).bijOn.mapsTo hx.2

end DifferentialGeometry.Topology.PiecewiseLinear
