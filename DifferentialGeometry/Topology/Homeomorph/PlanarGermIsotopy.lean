/-
Copyright (c) 2026 Yuan Liao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuan Liao
-/
import DifferentialGeometry.Topology.Homeomorph.Alexander
import DifferentialGeometry.Topology.Homeomorph.PlanarLocalization
import DifferentialGeometry.Topology.Homeomorph.RadialCompactification
import DifferentialGeometry.Topology.Homeomorph.ConjugateFamily

open Set Metric Filter Topology Schoenflies
open DifferentialGeometry.Topology

namespace OpenPartialHomeomorph

theorem exists_supported_isotopy_linearizing_germ (e : OpenPartialHomeomorph Plane Plane)
    (h0 : (0 : Plane) ∈ e.source) (he0 : e 0 = 0) :
    ∃ L : Plane ≃ₗᵢ[ℝ] Plane,
      (L = LinearIsometryEquiv.refl ℝ _ ∨ L = planarReflection) ∧
      ∃ R > 0, ∃ H : ℝ → Plane ≃ₜ Plane,
        Continuous (fun p : ℝ × Plane => H p.1 p.2) ∧
        Continuous (fun p : ℝ × Plane => (H p.1).symm p.2) ∧
        H 0 = Homeomorph.refl Plane ∧ (∀ t, H t 0 = 0) ∧
        (∀ t, EqOn (H t) id (ball 0 R)ᶜ ∧ EqOn (H t).symm id (ball 0 R)ᶜ) ∧
        (fun x => e (H 1 x)) =ᶠ[𝓝 0] L := by
  have ht : (0 : Plane) ∈ e.target := he0 ▸ e.map_source h0
  have hei0 : e.symm 0 = 0 := by simpa only [he0] using e.left_inv h0
  obtain ⟨L, hL, g, R, hR, hg, hfix⟩ := e.symm.exists_supported_eventuallyEq_or_reflection ht
  have hg0 : g 0 = 0 := by
    have h := hg.eq_of_nhds
    simpa only [Function.comp_apply, map_zero, hei0] using h
  obtain ⟨H, hH, hHi, hH0, hH1, hHfix, _, hHzero⟩ := g.alexander_trick hR.le hfix
  refine ⟨L, hL, R, hR, H, hH, hHi, hH0, hHzero hg0, hHfix, ?_⟩
  have hL0 : Tendsto L (𝓝 (0 : Plane)) (𝓝 0) := by
    simpa only [ContinuousAt, map_zero] using L.continuous.continuousAt (x := (0 : Plane))
  filter_upwards [hg, hL0.eventually (e.open_target.mem_nhds ht)] with x hx hxt
  rw [hH1, hx]
  exact e.right_inv hxt

theorem exists_isotopy_linearizing_germ_in_ball (e : OpenPartialHomeomorph Plane Plane)
    (h0 : (0 : Plane) ∈ e.source) (he0 : e 0 = 0) {η : ℝ} (hη : 0 < η) :
    ∃ L : Plane ≃ₗᵢ[ℝ] Plane,
      (L = LinearIsometryEquiv.refl ℝ _ ∨ L = planarReflection) ∧
      ∃ K : Set Plane, IsCompact K ∧ K ⊆ ball 0 η ∧
        ∃ H : ℝ → Plane ≃ₜ Plane,
          Continuous (fun p : ℝ × Plane => H p.1 p.2) ∧
          Continuous (fun p : ℝ × Plane => (H p.1).symm p.2) ∧
          H 0 = Homeomorph.refl Plane ∧ (∀ t, H t 0 = 0) ∧
          (∀ t, EqOn (H t) id Kᶜ ∧ EqOn (H t).symm id Kᶜ) ∧
          (fun x => e (H 1 x)) =ᶠ[𝓝 0] L := by
  obtain ⟨L, hL, R, hR, D, hD, hDi, hD0, hDz, hDfix, hDe⟩ :=
    e.exists_supported_isotopy_linearizing_germ h0 he0
  have ha : 0 < η / 2 := by positivity
  let s : Plane ≃ₜ Plane := Homeomorph.smulOfNeZero (η / 2) ha.ne'
  let q : OpenPartialHomeomorph Plane Plane :=
    s.symm.toOpenPartialHomeomorph.trans (radialCompression.trans s.toOpenPartialHomeomorph)
  have hqs : q.source = univ := by simp [q]
  have hnorm (x : Plane) : ‖s.symm x‖ = (η / 2)⁻¹ * ‖x‖ := by
    change ‖(η / 2)⁻¹ • x‖ = _
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr ha)]
  have hqsmall {x : Plane} (hx : x ∈ ball 0 (η / 2)) : q x = x ∧ q.symm x = x := by
    have hn : ‖s.symm x‖ ≤ 1 := by
      rw [hnorm]
      have hlt : ‖x‖ < η / 2 := mem_ball_zero_iff.mp hx
      exact (by simpa only [inv_mul_cancel₀ ha.ne'] using
        mul_le_mul_of_nonneg_left hlt.le (inv_nonneg.mpr ha.le))
    constructor
    · change s (radialCompression (s.symm x)) = x
      rw [radialCompression_eq_self hn, s.apply_symm_apply]
    · change s (radialCompression.symm (s.symm x)) = x
      rw [radialCompression_symm_eq_self hn, s.apply_symm_apply]
  have hqrange (x : Plane) : q x ∈ ball 0 η := by
    have hn : ‖radialCompression (s.symm x)‖ < 2 :=
      mem_ball_zero_iff.mp (radialCompression.map_source (mem_univ _))
    rw [mem_ball_zero_iff]
    change ‖(η / 2) • radialCompression (s.symm x)‖ < η
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos ha]
    nlinarith
  have hq0 := hqsmall (x := 0) (mem_ball_self ha)
  have hqt0 : (0 : Plane) ∈ q.target :=
    hq0.1 ▸ q.map_source (hqs ▸ mem_univ _)
  have hcompact : IsCompact (q '' closedBall (0 : Plane) R) :=
    (isCompact_closedBall (0 : Plane) R).image_of_continuousOn
      (q.continuousOn.mono (hqs ▸ subset_univ _))
  have hsub : q '' closedBall (0 : Plane) R ⊆ ball 0 η := by
    rintro _ ⟨x, _, rfl⟩
    exact hqrange x
  have hfix (t : ℝ) : EqOn (D t) id (closedBall (0 : Plane) R)ᶜ ∧
      EqOn (D t).symm id (closedBall (0 : Plane) R)ᶜ :=
    ⟨(hDfix t).1.mono (compl_subset_compl.mpr ball_subset_closedBall),
      (hDfix t).2.mono (compl_subset_compl.mpr ball_subset_closedBall)⟩
  obtain ⟨H, hH, hHi, hHe, hHfix⟩ := q.symm.exists_conjugate_homeomorph_family
    D hD hDi (isCompact_closedBall (0 : Plane) R) (by
      change closedBall (0 : Plane) R ⊆ q.source
      rw [hqs]
      exact subset_univ _) hfix
  have hHg : (H 1 : Plane → Plane) =ᶠ[𝓝 0] D 1 := by
    have ht : Tendsto (D 1) (𝓝 (0 : Plane)) (𝓝 0) := by
      simpa only [ContinuousAt, hDz] using (D 1).continuous.continuousAt (x := (0 : Plane))
    filter_upwards [q.open_target.mem_nhds hqt0, ball_mem_nhds _ ha,
      ht.eventually (ball_mem_nhds _ ha)] with x hx hxsmall hxD
    rw [(hHe 1 x).1, q.symm.conjugateMap_of_mem _ hx]
    change q (D 1 (q.symm x)) = D 1 x
    rw [(hqsmall hxsmall).2, (hqsmall hxD).1]
  refine ⟨L, hL, q '' closedBall 0 R, hcompact, hsub, H, hH, hHi, ?_, ?_, hHfix, ?_⟩
  · apply Homeomorph.ext
    intro x
    rw [(hHe 0 x).1, hD0]
    by_cases hx : x ∈ q.target
    · rw [q.symm.conjugateMap_of_mem _ hx]
      exact q.right_inv hx
    · exact q.symm.conjugateMap_of_notMem _ hx
  · intro t
    rw [(hHe t 0).1, q.symm.conjugateMap_of_mem _ hqt0]
    change q (D t (q.symm 0)) = 0
    rw [hq0.2, hDz, hq0.1]
  · filter_upwards [hHg, hDe] with x hx he
    rw [hx]
    exact he

end OpenPartialHomeomorph
