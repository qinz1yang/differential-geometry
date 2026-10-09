/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.PolyhedralTubeTraces
import Mathlib.Topology.OpenPartialHomeomorph.IsImage

open Set Topology

namespace DifferentialGeometry.Topology.PiecewiseLinear

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

open Classical in
theorem HasPLCrossingAt.mem_closure_inter_interior {A X : Set E} {x : E}
    (hcross : HasPLCrossingAt A (frontier X) x) (hXc : IsClosed X)
    (hX : x ∈ closure (interior X)) : x ∈ closure (A ∩ interior X) := by
  obtain ⟨U, φ, ρ, α, β, hU, hxU, hρ, hφ, hφx, hα, hβ, hloc⟩ :=
    hcross.exists_coordinateChart
  have hβ0 : β = 0 := hβ.resolve_right fun hne =>
    false_of_frontier_halfPlane hU hxU hφ hφx hne
      (fun y hy => (hloc y hy).2) hXc hX
  have hBU : ∀ y ∈ U, y ∈ frontier X ↔ (φ y).2.1 = 0 := fun y hy => by
    simpa [hβ0] using (hloc y hy).2
  obtain ⟨b, hb, hside⟩ : ∃ b : ℝ, b ≠ 0 ∧
      ∀ y ∈ U, 0 < b * (φ y).2.1 → y ∈ interior X := by
    rcases side_of_frontier_plane hU hxU hφ hφx hBU hXc hX with hp | hm
    · refine ⟨1, one_ne_zero, fun y hy hpos => ?_⟩
      have hypos : 0 < (φ y).2.1 := by simpa only [one_mul] using hpos
      exact (mem_interior_iff_notMem_frontier ((hp y hy).mpr hypos.le)).mpr
        (fun hfr => hypos.ne' ((hBU y hy).mp hfr))
    · refine ⟨-1, neg_ne_zero.mpr one_ne_zero, fun y hy hpos => ?_⟩
      have hyneg : (φ y).2.1 < 0 := by linarith
      exact (mem_interior_iff_notMem_frontier ((hm y hy).mpr hyneg.le)).mpr
        (fun hfr => hyneg.ne ((hBU y hy).mp hfr))
  let v : ℝ × ℝ × ℝ := (-(α (0, b, 0) / α (1, 0, 0)), b, 0)
  have hvα : α v = 0 := by
    rcases hα with rfl | hαne
    · simp
    · have hv : v = (-(α (0, b, 0) / α (1, 0, 0))) • (1, 0, 0) + (0, b, 0) := by
        ext <;> simp [v]
      rw [hv, map_add, map_smul, smul_eq_mul, neg_mul, div_mul_cancel₀ _ hαne]
      ring
  let ψ := Function.invFunOn φ U
  have hψ0 : ψ 0 = x := by
    rw [← hφx]
    exact hφ.bijOn.invOn_invFunOn.1 hxU
  have h0ball : (0 : ℝ × ℝ × ℝ) ∈ Metric.ball 0 ρ := by
    simpa only [Metric.mem_ball, dist_self] using hρ
  have hψcont : ContinuousAt ψ 0 :=
    hφ.isPiecewiseAffineOn_invFunOn.continuousOn.continuousAt
      (Metric.isOpen_ball.mem_nhds h0ball)
  have hcont : Continuous (fun t : ℝ => t • v) := continuous_id.smul continuous_const
  have hline : Filter.Tendsto (fun t : ℝ => t • v) (𝓝[>] 0) (𝓝 0) := by
    simpa only [zero_smul] using
      (hcont.tendsto (0 : ℝ)).mono_left nhdsWithin_le_nhds
  have htend : Filter.Tendsto (fun t : ℝ => ψ (t • v)) (𝓝[>] 0) (𝓝 x) := by
    simpa only [hψ0, Function.comp_def] using hψcont.tendsto.comp hline
  refine mem_closure_of_tendsto htend ?_
  filter_upwards [self_mem_nhdsWithin,
    hline.eventually (Metric.isOpen_ball.mem_nhds h0ball)] with t ht htball
  have htpos : 0 < t := ht
  have hψU : ψ (t • v) ∈ U := hφ.bijOn.surjOn.mapsTo_invFunOn htball
  have hφψ : φ (ψ (t • v)) = t • v := hφ.bijOn.invOn_invFunOn.2 htball
  refine ⟨(hloc _ hψU).1.mpr ?_, hside _ hψU ?_⟩
  · rw [hφψ]
    exact ⟨by simp [v], by simp [map_smul, hvα]⟩
  · rw [hφψ]
    change 0 < b * (t * b)
    nlinarith [mul_pos htpos (sq_pos_of_ne_zero hb)]

theorem HasPLCrossingAt.mem_closure_inter_interior_of_chart
    {M : Type*} [TopologicalSpace M] {c : OpenPartialHomeomorph M E}
    {A X : Set M} {x : M} (hx : x ∈ c.source)
    (hcross : HasPLCrossingAt (c '' (A ∩ c.source))
      (c '' (frontier X ∩ c.source)) (c x))
    (hXc : IsClosed X) (hX : x ∈ closure (interior X)) :
    x ∈ closure (A ∩ interior X) := by
  have himg (S : Set M) : c.IsImage S (c '' (S ∩ c.source)) := by
    intro z hz
    constructor
    · rintro ⟨w, ⟨hwS, hws⟩, hwz⟩
      exact c.injOn hws hz hwz ▸ hwS
    · intro hzS
      exact ⟨z, ⟨hzS, hz⟩, rfl⟩
  let Q := closure (c '' (X ∩ c.source))
  have hQ : c.IsImage X Q := by
    simpa only [hXc.closure_eq] using (himg X).closure
  have hcrossQ : HasPLCrossingAt (c '' (A ∩ c.source)) (frontier Q) (c x) := by
    refine hcross.congr (Filter.Eventually.of_forall fun _ => Iff.rfl) ?_
    filter_upwards [c.open_target.mem_nhds (c.map_source hx)] with z hz
    exact ((himg (frontier X)).symm_apply_mem_iff hz).symm.trans
      (hQ.frontier.symm_apply_mem_iff hz)
  have hxQ : c x ∈ closure (interior Q) := (hQ.interior.closure hx).mpr hX
  exact (((himg A).inter hQ.interior).closure hx).mp
    (hcrossQ.mem_closure_inter_interior isClosed_closure hxQ)

end DifferentialGeometry.Topology.PiecewiseLinear
