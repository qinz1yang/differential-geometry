/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.PLHomeomorphOpen
import DifferentialGeometry.Topology.PiecewiseLinear.PolyhedralTubeTraces
import Mathlib.Topology.OpenPartialHomeomorph.IsImage

open Set Topology

namespace DifferentialGeometry.Topology.PiecewiseLinear

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

theorem HasPLCrossingAt.exists_lineChart_of_regular_frontiers {F T : Set E} {x : E}
    (hcross : HasPLCrossingAt (frontier F) (frontier T) x)
    (hFc : IsClosed F) (hTc : IsClosed T)
    (hF : x ∈ closure (interior F)) (hT : x ∈ closure (interior T)) :
    ∃ (U : Set E) (φ : E → ℝ × ℝ × ℝ) (ρ : ℝ), IsOpen U ∧ x ∈ U ∧ 0 < ρ ∧
      IsPLHomeomorphOn φ U (Metric.ball 0 ρ) ∧ φ x = 0 ∧
        ∀ y ∈ U, (y ∈ frontier F ↔ (φ y).2.2 = 0) ∧
          (y ∈ frontier T ↔ (φ y).2.1 = 0) := by
  obtain ⟨U, φ, ρ, α, β, hU, hxU, hρ, hφ, hφx, hα, hβ, hloc⟩ :=
    hcross.exists_coordinateChart
  let N : (ℝ × ℝ × ℝ) ≃ₗ[ℝ] (ℝ × ℝ × ℝ) :=
    { toFun := fun z => (z.1, z.2.2, z.2.1)
      invFun := fun z => (z.1, z.2.2, z.2.1)
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  have hNapply : ∀ z, N z = (z.1, z.2.2, z.2.1) := fun _ => rfl
  have hNnorm : ∀ z, ‖N z‖ = ‖z‖ := fun z => by
    simp only [hNapply, Prod.norm_def, max_comm ‖z.2.2‖ ‖z.2.1‖]
  have hNball : (fun z => N z) '' Metric.ball (0 : ℝ × ℝ × ℝ) ρ =
      Metric.ball 0 ρ := by
    apply Subset.antisymm
    · rintro _ ⟨z, hz, rfl⟩
      rw [mem_ball_zero_iff, hNnorm]
      exact mem_ball_zero_iff.mp hz
    · intro z hz
      refine ⟨N z, ?_, N.apply_symm_apply z⟩
      rw [mem_ball_zero_iff, hNnorm]
      exact mem_ball_zero_iff.mp hz
  have hNφ : IsPLHomeomorphOn ((fun z => N z) ∘ φ) U (Metric.ball 0 ρ) := by
    have h := hφ.trans (isPLHomeomorphOn_linearEquiv N Metric.isOpen_ball)
    rwa [hNball] at h
  have hα0 : α = 0 := by
    rcases hα with h | hne
    · exact h
    · exfalso
      refine false_of_frontier_halfPlane hU hxU hNφ
        (by simp only [Function.comp_apply, hφx, map_zero])
        (β := α.comp N.toLinearMap) ?_ ?_ hFc hF
      · simpa [N] using hne
      · intro y hy
        simpa [Function.comp_apply, N] using (hloc y hy).1
  have hβ0 : β = 0 := hβ.resolve_right fun hne =>
    false_of_frontier_halfPlane hU hxU hφ hφx hne
      (fun y hy => (hloc y hy).2) hTc hT
  refine ⟨U, φ, ρ, hU, hxU, hρ, hφ, hφx, fun y hy => ⟨?_, ?_⟩⟩
  · simpa [hα0] using (hloc y hy).1
  · simpa [hβ0] using (hloc y hy).2

theorem HasPLCrossingAt.exists_lineChart_of_regular_frontiers_of_chart
    {M : Type*} [TopologicalSpace M] {c : OpenPartialHomeomorph M E}
    {F T : Set M} {x : M} (hx : x ∈ c.source)
    (hcross : HasPLCrossingAt (c '' (frontier F ∩ c.source))
      (c '' (frontier T ∩ c.source)) (c x))
    (hFc : IsClosed F) (hTc : IsClosed T)
    (hF : x ∈ closure (interior F)) (hT : x ∈ closure (interior T)) :
    ∃ e : OpenPartialHomeomorph M (ℝ × ℝ × ℝ), x ∈ e.source ∧ e x = 0 ∧
      ∀ y ∈ e.source, (y ∈ frontier F ↔ (e y).2.2 = 0) ∧
        (y ∈ frontier T ↔ (e y).2.1 = 0) := by
  have himg (S : Set M) : c.IsImage S (c '' (S ∩ c.source)) := by
    intro z hz
    constructor
    · rintro ⟨w, ⟨hwS, hws⟩, hwz⟩
      exact c.injOn hws hz hwz ▸ hwS
    · intro hzS
      exact ⟨z, ⟨hzS, hz⟩, rfl⟩
  let P := closure (c '' (F ∩ c.source))
  let Q := closure (c '' (T ∩ c.source))
  have hP : c.IsImage F P := by
    simpa only [hFc.closure_eq] using (himg F).closure
  have hQ : c.IsImage T Q := by
    simpa only [hTc.closure_eq] using (himg T).closure
  have hcrossPQ : HasPLCrossingAt (frontier P) (frontier Q) (c x) := by
    refine hcross.congr ?_ ?_
    · filter_upwards [c.open_target.mem_nhds (c.map_source hx)] with z hz
      exact ((himg (frontier F)).symm_apply_mem_iff hz).symm.trans
        (hP.frontier.symm_apply_mem_iff hz)
    · filter_upwards [c.open_target.mem_nhds (c.map_source hx)] with z hz
      exact ((himg (frontier T)).symm_apply_mem_iff hz).symm.trans
        (hQ.frontier.symm_apply_mem_iff hz)
  obtain ⟨U, φ, ρ, hU, hxU, -, hφ, hφx, hloc⟩ :=
    hcrossPQ.exists_lineChart_of_regular_frontiers isClosed_closure isClosed_closure
      ((hP.interior.closure hx).mpr hF) ((hQ.interior.closure hx).mpr hT)
  let e := c.trans (hφ.toOpenPartialHomeomorph hU Metric.isOpen_ball)
  refine ⟨e, ⟨hx, hxU⟩, hφx, ?_⟩
  intro y hy
  exact ⟨(hP.frontier hy.1).symm.trans ((hloc (c y) hy.2).1),
    (hQ.frontier hy.1).symm.trans ((hloc (c y) hy.2).2)⟩

end DifferentialGeometry.Topology.PiecewiseLinear
