/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PlanarJordan.PlanarArcSmoothing
import DifferentialGeometry.Topology.Manifold.PartialDiffeomorph.Atlas
import Mathlib.Geometry.Manifold.ContMDiff.NormedSpace

open Set Metric Filter Manifold
open scoped Topology ContDiff Manifold

namespace DifferentialGeometry.Manifold

open Schoenflies (Plane)
open DifferentialGeometry.Topology.PlanarJordan

theorem polarStripMap_add_two_pi_mul (t y : ℝ) (m : ℤ) :
    polarStripMap (Plane.mk (t + 2 * Real.pi * m) y) = polarStripMap (Plane.mk t y) := by
  have hc : Real.cos (t + 2 * Real.pi * m) = Real.cos t := by
    rw [show t + 2 * Real.pi * m = t + (m : ℝ) * (2 * Real.pi) by ring]
    exact Real.cos_add_int_mul_two_pi t m
  have hs : Real.sin (t + 2 * Real.pi * m) = Real.sin t := by
    rw [show t + 2 * Real.pi * m = t + (m : ℝ) * (2 * Real.pi) by ring]
    exact Real.sin_add_int_mul_two_pi t m
  change (3 / 2 + y) • Plane.mk (Real.cos (t + 2 * Real.pi * m)) (Real.sin (t + 2 * Real.pi * m)) =
    (3 / 2 + y) • Plane.mk (Real.cos t) (Real.sin t)
  rw [hc, hs]

theorem polarStripMap_eq_polarStripMap {x y : Plane} (hx : |x 1| < 3 / 2) (hy : |y 1| < 3 / 2)
    (h : polarStripMap x = polarStripMap y) : x 1 = y 1 ∧ ∃ m : ℤ, x 0 = y 0 + 2 * Real.pi * m := by
  have hx' : 0 < 3 / 2 + x 1 := by linarith [neg_abs_le (x 1)]
  have hy' : 0 < 3 / 2 + y 1 := by linarith [neg_abs_le (y 1)]
  have hn := congrArg norm h
  rw [norm_polarStripMap, norm_polarStripMap, abs_of_pos hx', abs_of_pos hy'] at hn
  have h1 : x 1 = y 1 := by linarith
  refine ⟨h1, ?_⟩
  have hc : Real.cos (x 0) = Real.cos (y 0) := by
    have := congrArg (fun v : Plane => v 0) h
    simp only [polarStripMap_apply_zero, h1] at this
    exact mul_left_cancel₀ hy'.ne' this
  have hs : Real.sin (x 0) = Real.sin (y 0) := by
    have := congrArg (fun v : Plane => v 1) h
    simp only [polarStripMap_apply_one, h1] at this
    exact mul_left_cancel₀ hy'.ne' this
  have hc' := Real.cos_sub_cos (x 0) (y 0)
  have hs' := Real.sin_sub_sin (x 0) (y 0)
  rw [hc, sub_self] at hc'
  rw [hs, sub_self] at hs'
  have hd : Real.sin ((x 0 - y 0) / 2) = 0 := by
    by_contra hne
    have ha : Real.sin ((x 0 + y 0) / 2) = 0 := by
      rcases mul_eq_zero.mp hc'.symm with h3 | h3
      · rcases mul_eq_zero.mp h3 with h4 | h4
        · norm_num at h4
        · exact h4
      · exact absurd h3 hne
    have hb : Real.cos ((x 0 + y 0) / 2) = 0 := by
      rcases mul_eq_zero.mp hs'.symm with h3 | h3
      · rcases mul_eq_zero.mp h3 with h4 | h4
        · norm_num at h4
        · exact absurd h4 hne
      · exact h3
    have := Real.sin_sq_add_cos_sq ((x 0 + y 0) / 2)
    rw [ha, hb] at this
    norm_num at this
  obtain ⟨m, hm⟩ := Real.sin_eq_zero_iff.mp hd
  exact ⟨m, by linarith⟩

theorem symm_restr_polarBand_mem_maximalAtlas {S : Type*} [TopologicalSpace S]
    [ChartedSpace Plane S] [IsManifold 𝓘(ℝ, Plane) ∞ S] (F : OpenPartialHomeomorph Plane S)
    {δ : ℝ} (hδ : δ < 1 / 2) (hsrc : {x : Plane | |‖x‖ - 3 / 2| < δ} ⊆ F.source)
    (hsm : ∀ x : Plane, x 0 ∈ Ico 0 (2 * Real.pi) → |x 1| < δ → ∃ V : Set Plane, IsOpen V ∧
      x ∈ V ∧ (∀ z ∈ V, |z 1| < δ) ∧ ∃ b ∈ IsManifold.maximalAtlas 𝓘(ℝ, Plane) ∞ S,
        (∀ z ∈ V, F (polarStripMap z) ∈ b.source) ∧
        ContDiffOn ℝ ∞ (fun z => b (F (polarStripMap z))) V ∧
        ∀ z ∈ V, LinearMap.det
          (fderiv ℝ (fun z => b (F (polarStripMap z))) z : Plane →ₗ[ℝ] Plane) ≠ 0) :
    (F.restr {x : Plane | |‖x‖ - 3 / 2| < δ}).symm ∈
      IsManifold.maximalAtlas 𝓘(ℝ, Plane) ∞ S := by
  set B : Set Plane := {x : Plane | |‖x‖ - 3 / 2| < δ} with hBdef
  have hBo : IsOpen B := isOpen_lt (continuous_abs.comp (continuous_norm.sub continuous_const))
    continuous_const
  set c := F.restr B with hcdef
  have hcs : c.source = B := by
    rw [hcdef, OpenPartialHomeomorph.restr_source' _ _ hBo, inter_eq_right.mpr hsrc]
  have hcapp : ∀ x, c x = F x := fun x => rfl
  have hpolB : ∀ z : Plane, |z 1| < δ → polarStripMap z ∈ B := by
    intro z hz
    change |‖polarStripMap z‖ - 3 / 2| < δ
    rw [norm_polarStripMap, abs_of_pos (by linarith [neg_abs_le (z 1)] : 0 < 3 / 2 + z 1)]
    simpa using hz
  have hlocal : ∀ w ∈ B, ∃ x : Plane, polarStripMap x = w ∧ ∃ V : Set Plane, IsOpen V ∧
      x ∈ V ∧ (∀ z ∈ V, |z 1| < δ) ∧ ∃ b ∈ IsManifold.maximalAtlas 𝓘(ℝ, Plane) ∞ S,
        (∀ z ∈ V, F (polarStripMap z) ∈ b.source) ∧
        ContDiffOn ℝ ∞ (fun z => b (F (polarStripMap z))) V ∧
        ∀ z ∈ V, LinearMap.det
          (fderiv ℝ (fun z => b (F (polarStripMap z))) z : Plane →ₗ[ℝ] Plane) ≠ 0 := by
    intro w hw
    have hw' : |‖w‖ - 3 / 2| < δ := hw
    have hwpos : 0 < ‖w‖ := by
      rw [abs_lt] at hw'
      linarith
    obtain ⟨t, ht, htw⟩ := exists_polarStripMap_eq hwpos
    refine ⟨Plane.mk t (‖w‖ - 3 / 2), htw, hsm _ ht ?_⟩
    simpa using hw'
  refine DifferentialGeometry.OpenPartialHomeomorph.mem_maximalAtlas_of_contMDiffOn c.symm ?_ ?_
  · intro y hy
    have hy' : y ∈ c.target := hy
    set w := c.symm y with hwdef
    have hwB : w ∈ B := hcs ▸ c.map_target hy'
    have hcw : c w = y := c.right_inv hy'
    obtain ⟨x, hxw, V, hV, hxV, hVδ, b, hb, hVb, hsmooth, hdet⟩ := hlocal w hwB
    obtain ⟨Γ, hxΓ, hΓV, hΓg, hΓs⟩ := exists_openPartialHomeomorph_contDiffOn_symm hV hsmooth
      hdet hxV
    have hyb : y ∈ b.source := by
      rw [← hcw, hcapp, ← hxw]
      exact hVb x hxV
    have hgx : Γ x = b y := by
      rw [hΓg hxΓ]
      change b (F (polarStripMap x)) = b y
      rw [hxw, ← hcapp, hcw]
    have hbt : b y ∈ Γ.target := hgx ▸ Γ.map_source hxΓ
    have hbc : ContMDiffOn 𝓘(ℝ, Plane) 𝓘(ℝ, Plane) ∞ b b.source :=
      contMDiffOn_of_mem_maximalAtlas hb
    have hbcont : ContinuousAt b y :=
      (hbc.continuousOn.continuousAt (b.open_source.mem_nhds hyb))
    have hN : ∀ᶠ y' in 𝓝 y, y' ∈ b.source ∧ b y' ∈ Γ.target :=
      Filter.Eventually.and (b.open_source.mem_nhds hyb)
        (hbcont.preimage_mem_nhds (Γ.open_target.mem_nhds hbt))
    have heq : ∀ᶠ y' in 𝓝 y, c.symm y' = polarStripMap (Γ.symm (b y')) := by
      filter_upwards [hN] with y' hy'
      have hz : Γ.symm (b y') ∈ Γ.source := Γ.map_target hy'.2
      have hzV := hΓV hz
      have hpB : polarStripMap (Γ.symm (b y')) ∈ c.source := hcs ▸ hpolB _ (hVδ _ hzV)
      have hcz : c (polarStripMap (Γ.symm (b y'))) = y' := by
        rw [hcapp]
        have h1 : b (F (polarStripMap (Γ.symm (b y')))) = b y' := by
          have h3 : Γ (Γ.symm (b y')) = b (F (polarStripMap (Γ.symm (b y')))) := hΓg hz
          rw [← h3]
          exact Γ.right_inv hy'.2
        have h2 := congrArg b.symm h1
        rwa [b.left_inv (hVb _ hzV), b.left_inv hy'.1] at h2
      conv_lhs => rw [← hcz]
      exact c.left_inv hpB
    have hsmΓ : ContDiffAt ℝ ∞ Γ.symm (b y) :=
      hΓs.contDiffAt (Γ.open_target.mem_nhds hbt)
    have hcomp : ContMDiffAt 𝓘(ℝ, Plane) 𝓘(ℝ, Plane) ∞
        (fun y' => polarStripMap (Γ.symm (b y'))) y := by
      have h1 : ContMDiffAt 𝓘(ℝ, Plane) 𝓘(ℝ, Plane) ∞ (fun z => polarStripMap (Γ.symm z)) (b y) :=
        contMDiffAt_iff_contDiffAt.mpr (contDiff_polarStripMap.contDiffAt.comp _ hsmΓ)
      exact h1.comp y (hbc.contMDiffAt (b.open_source.mem_nhds hyb))
    exact (hcomp.congr_of_eventuallyEq heq).contMDiffWithinAt
  · intro w hw
    have hw' : w ∈ c.source := hw
    have hwB : w ∈ B := hcs ▸ hw'
    obtain ⟨x, hxw, V, hV, hxV, hVδ, b, hb, hVb, hsmooth, hdet⟩ := hlocal w hwB
    have hdetP : ∀ z ∈ V, LinearMap.det (fderiv ℝ polarStripMap z : Plane →ₗ[ℝ] Plane) ≠ 0 := by
      intro z hz
      rw [det_fderiv_polarStripMap]
      have := hVδ z hz
      rw [abs_lt] at this
      intro h0
      linarith
    obtain ⟨Λ, hxΛ, hΛV, hΛp, hΛs⟩ := exists_openPartialHomeomorph_contDiffOn_symm hV
      contDiff_polarStripMap.contDiffOn hdetP hxV
    have hwΛ : w ∈ Λ.target := by
      rw [← hxw, ← hΛp hxΛ]
      exact Λ.map_source hxΛ
    have hbs : ContMDiffOn 𝓘(ℝ, Plane) 𝓘(ℝ, Plane) ∞ b.symm b.target :=
      contMDiffOn_symm_of_mem_maximalAtlas hb
    have heq : ∀ᶠ w' in 𝓝 w, c.symm.symm w' =
        b.symm ((fun z => b (F (polarStripMap z))) (Λ.symm w')) := by
      filter_upwards [Λ.open_target.mem_nhds hwΛ, hBo.mem_nhds hwB] with w' hw'Λ hw'B
      have hz : Λ.symm w' ∈ Λ.source := Λ.map_target hw'Λ
      have hpz : polarStripMap (Λ.symm w') = w' := by
        rw [← hΛp hz]
        exact Λ.right_inv hw'Λ
      change c w' = b.symm (b (F (polarStripMap (Λ.symm w'))))
      rw [b.left_inv (hVb _ (hΛV hz)), hpz, hcapp]
    have hgx : ContDiffAt ℝ ∞ (fun z => b (F (polarStripMap z))) (Λ.symm w) := by
      have hx' : Λ.symm w = x := by
        rw [← hxw, ← hΛp hxΛ]
        exact Λ.left_inv hxΛ
      rw [hx']
      exact hsmooth.contDiffAt (hV.mem_nhds hxV)
    have hsmΛ : ContDiffAt ℝ ∞ Λ.symm w := hΛs.contDiffAt (Λ.open_target.mem_nhds hwΛ)
    have hbt : b (F (polarStripMap (Λ.symm w))) ∈ b.target :=
      b.map_source (hVb _ (hΛV (Λ.map_target hwΛ)))
    have hcomp : ContMDiffAt 𝓘(ℝ, Plane) 𝓘(ℝ, Plane) ∞
        (fun w' => b.symm ((fun z => b (F (polarStripMap z))) (Λ.symm w'))) w := by
      have h1 := contMDiffAt_iff_contDiffAt.mpr (hgx.comp w hsmΛ)
      exact (hbs.contMDiffAt (b.open_target.mem_nhds hbt)).comp w h1
    exact (hcomp.congr_of_eventuallyEq heq).contMDiffWithinAt

end DifferentialGeometry.Manifold
