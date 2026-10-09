/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.CurveCrossingGeneralPosition
import DifferentialGeometry.Topology.PiecewiseLinear.Section34FaceBallUpdate

open Set Topology

namespace DifferentialGeometry.Topology.PiecewiseLinear

variable {M : Type*} [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]

theorem exists_chart_hasPLCurveCrossingOnAt_supported_image
    (Ψ : M ≃ₜ M) {K B Sf C : Set M} (hK : IsClosed K) (hfix : EqOn Ψ id Kᶜ)
    (hnew : Disjoint ((Ψ '' B) ∩ C) K)
    (hcross : ∀ y ∈ B ∩ C,
      ∃ c ∈ (plGroupoid 3).maximalAtlas M, y ∈ c.source ∧
        HasPLCurveCrossingOnAt (c '' (Sf ∩ c.source))
          (c '' (B ∩ Sf ∩ c.source)) (c '' (C ∩ c.source)) (c y)) :
    ∀ y ∈ (Ψ '' B) ∩ C,
      ∃ c ∈ (plGroupoid 3).maximalAtlas M, y ∈ c.source ∧
        HasPLCurveCrossingOnAt (c '' (Sf ∩ c.source))
          (c '' ((Ψ '' B) ∩ Sf ∩ c.source)) (c '' (C ∩ c.source)) (c y) := by
  have hmem : ∀ x ∈ Kᶜ, x ∈ Ψ '' B ↔ x ∈ B := by
    intro x hx
    constructor
    · rintro ⟨z, hz, hzx⟩
      exact Ψ.injective (hzx.trans (hfix hx).symm) ▸ hz
    · intro hxB
      exact ⟨x, hxB, hfix hx⟩
  have htrace : (B ∩ Sf) ∩ Kᶜ = ((Ψ '' B) ∩ Sf) ∩ Kᶜ := by
    ext x
    constructor
    · rintro ⟨⟨hxB, hxS⟩, hxK⟩
      exact ⟨⟨(hmem x hxK).mpr hxB, hxS⟩, hxK⟩
    · rintro ⟨⟨hxB, hxS⟩, hxK⟩
      exact ⟨⟨(hmem x hxK).mp hxB, hxS⟩, hxK⟩
  intro y hy
  have hyK : y ∈ Kᶜ := fun hyK => disjoint_left.mp hnew hy hyK
  obtain ⟨c, hc, hyc, hcy⟩ := hcross y ⟨(hmem y hyK).mp hy.1, hy.2⟩
  refine ⟨c, hc, hyc, hcy.congr (Filter.Eventually.of_forall (fun _ => Iff.rfl)) ?_
    (Filter.Eventually.of_forall (fun _ => Iff.rfl))⟩
  exact eventually_mem_image_inter_source_iff hK.isOpen_compl htrace hyK hyc

end DifferentialGeometry.Topology.PiecewiseLinear
