/-
Copyright (c) 2026 Yuan Liao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuan Liao
-/
import DifferentialGeometry.Topology.Homeomorph.SphereExtension
import Mathlib.Topology.UnitInterval

open Set Metric Filter Topology

namespace DifferentialGeometry.Topology

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

theorem continuous_sphereRadialHomeomorph_family {T : Type*} [TopologicalSpace T]
    (H : T → sphere (0 : E) 1 ≃ₜ sphere (0 : F) 1)
    (hH : Continuous (fun p : T × sphere (0 : E) 1 => H p.1 p.2)) :
    Continuous (fun p : T × E => sphereRadialHomeomorph (H p.1) p.2) := by
  let V : Set (T × E) := {p | p.2 ≠ 0}
  have hc : ContinuousOn (fun p : T × E => sphereRadialHomeomorph (H p.1) p.2) V := by
    rw [continuousOn_iff_continuous_domRestrict]
    let d : V → ({0}ᶜ : Set E) := fun p => ⟨p.1.2, p.property⟩
    have hd : Continuous d := (continuous_snd.comp continuous_subtype_val).subtype_mk _
    have hθ := (homeomorphUnitSphereProd E).continuous.fst.comp hd
    have hh := hH.comp ((continuous_fst.comp continuous_subtype_val).prodMk hθ)
    have he := (continuous_snd.comp continuous_subtype_val).norm.smul
      (continuous_subtype_val.comp hh)
    convert he using 1
    funext p
    exact LocalDegree.sphereRadialExtension_apply_of_ne_zero _ p.property
  rw [continuous_iff_continuousAt]
  intro p
  by_cases hp : p.2 = 0
  · rw [ContinuousAt, hp, sphereRadialHomeomorph_zero, tendsto_zero_iff_norm_tendsto_zero]
    simpa only [ContinuousAt, norm_sphereRadialHomeomorph, hp, norm_zero] using
      (continuous_snd.norm.continuousAt (x := p))
  · exact hc.continuousAt ((isOpen_ne_fun continuous_snd continuous_const).mem_nhds hp)

noncomputable def sphereFamilyHomeomorph
    (H : ℝ → sphere (0 : E) 1 ≃ₜ sphere (0 : F) 1)
    (hH : Continuous (fun p : ℝ × sphere (0 : E) 1 => H p.1 p.2))
    (hHi : Continuous (fun p : ℝ × sphere (0 : F) 1 => (H p.1).symm p.2)) : E ≃ₜ F where
  toFun x := sphereRadialHomeomorph (H ‖x‖) x
  invFun x := sphereRadialHomeomorph (H ‖x‖).symm x
  left_inv x := by
    dsimp only
    rw [norm_sphereRadialHomeomorph]
    exact (sphereRadialHomeomorph (H ‖x‖)).symm_apply_apply x
  right_inv x := by
    dsimp only
    rw [norm_sphereRadialHomeomorph]
    exact (sphereRadialHomeomorph (H ‖x‖)).apply_symm_apply x
  continuous_toFun := (continuous_sphereRadialHomeomorph_family H hH).comp
    (continuous_norm.prodMk continuous_id)
  continuous_invFun := (continuous_sphereRadialHomeomorph_family (fun r => (H r).symm) hHi).comp
    (continuous_norm.prodMk continuous_id)

theorem sphereFamilyHomeomorph_apply
    (H : ℝ → sphere (0 : E) 1 ≃ₜ sphere (0 : F) 1)
    (hH : Continuous (fun p : ℝ × sphere (0 : E) 1 => H p.1 p.2))
    (hHi : Continuous (fun p : ℝ × sphere (0 : F) 1 => (H p.1).symm p.2)) (x : E) :
    sphereFamilyHomeomorph H hH hHi x = sphereRadialHomeomorph (H ‖x‖) x := rfl

@[simp]
theorem norm_sphereFamilyHomeomorph
    (H : ℝ → sphere (0 : E) 1 ≃ₜ sphere (0 : F) 1)
    (hH : Continuous (fun p : ℝ × sphere (0 : E) 1 => H p.1 p.2))
    (hHi : Continuous (fun p : ℝ × sphere (0 : F) 1 => (H p.1).symm p.2)) (x : E) :
    ‖sphereFamilyHomeomorph H hH hHi x‖ = ‖x‖ := norm_sphereRadialHomeomorph _ _

@[simp]
theorem sphereRadialHomeomorph_refl :
    sphereRadialHomeomorph (Homeomorph.refl (sphere (0 : E) 1)) = Homeomorph.refl E := by
  ext x
  by_cases hx : x = 0
  · simp [hx]
  · change LocalDegree.sphereRadialExtension
      (toContinuousMap (Homeomorph.refl (sphere (0 : E) 1))) x = x
    rw [LocalDegree.sphereRadialExtension_apply_of_ne_zero _ hx]
    change ‖x‖ • (((homeomorphUnitSphereProd E) ⟨x, hx⟩).1 : E) = x
    rw [homeomorphUnitSphereProd_apply_fst_coe, smul_inv_smul₀ (norm_ne_zero_iff.mpr hx)]

theorem exists_supported_homeomorph_of_sphere_isotopy
    (H : unitInterval → sphere (0 : E) 1 ≃ₜ sphere (0 : E) 1)
    (hH : Continuous (fun p : unitInterval × sphere (0 : E) 1 => H p.1 p.2))
    (hHi : Continuous (fun p : unitInterval × sphere (0 : E) 1 => (H p.1).symm p.2))
    (hH0 : H 0 = Homeomorph.refl _) :
    ∃ g : E ≃ₜ E, (∀ x, ‖g x‖ = ‖x‖) ∧
      (∀ x : sphere (0 : E) 1, g x = H 1 x) ∧ EqOn g id (ball 0 2)ᶜ := by
  let s (r : ℝ) : unitInterval := ⟨max 0 (min (2 - r) 1),
    le_max_left _ _, max_le zero_le_one (min_le_right _ _)⟩
  have hs : Continuous s :=
    (continuous_const.max ((continuous_const.sub continuous_id).min continuous_const)).subtype_mk _
  have hs1 : s 1 = 1 := by apply Subtype.ext; norm_num [s]
  have hs0 {r : ℝ} (hr : 2 ≤ r) : s r = 0 := by
    apply Subtype.ext
    change max 0 (min (2 - r) 1) = 0
    exact max_eq_left ((min_le_left _ _).trans (sub_nonpos.mpr hr))
  let G (r : ℝ) := H (s r)
  have hG : Continuous (fun p : ℝ × sphere (0 : E) 1 => G p.1 p.2) :=
    hH.comp ((hs.comp continuous_fst).prodMk continuous_snd)
  have hGi : Continuous (fun p : ℝ × sphere (0 : E) 1 => (G p.1).symm p.2) :=
    hHi.comp ((hs.comp continuous_fst).prodMk continuous_snd)
  refine ⟨sphereFamilyHomeomorph G hG hGi, norm_sphereFamilyHomeomorph G hG hGi, ?_, ?_⟩
  · intro x
    rw [sphereFamilyHomeomorph_apply, mem_sphere_zero_iff_norm.mp x.property]
    change sphereRadialHomeomorph (H (s 1)) x = H 1 x
    rw [hs1, sphereRadialHomeomorph_apply_sphere]
  · intro x hx
    have hx2 : 2 ≤ ‖x‖ := by
      simpa only [mem_compl_iff, mem_ball, dist_zero_right, not_lt] using hx
    rw [sphereFamilyHomeomorph_apply]
    change sphereRadialHomeomorph (H (s ‖x‖)) x = x
    rw [hs0 hx2, hH0, sphereRadialHomeomorph_refl]
    rfl

end DifferentialGeometry.Topology
