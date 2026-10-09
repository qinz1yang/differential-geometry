import DifferentialGeometry.Geometry.Hyperbolic.Hyperboloid.Boundary
import Mathlib.Analysis.Normed.Module.Normalize
import Mathlib.LinearAlgebra.Dimension.Finite

noncomputable section

namespace DifferentialGeometry.Hyperboloid

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

private def unitDirection (v : E) (hv : v ≠ 0) : Metric.sphere (0 : E) 1 :=
  ⟨NormedSpace.normalize v, by
    simpa only [Metric.mem_sphere, dist_zero_right] using NormedSpace.norm_normalize hv⟩

private theorem null_ray_of_boundary_identity (f : Hyperboloid E ≃ᵢ Hyperboloid E)
    (hf : boundaryHomeomorph f = Homeomorph.refl (Metric.sphere (0 : E) 1))
    (ξ : Metric.sphere (0 : E) 1) :
    lorentzExtension f (1, (ξ : E)) =
      (lorentzExtension f (1, (ξ : E))).1 • (1, (ξ : E)) := by
  have h := boundaryHomeomorph_apply_coe f ξ
  rw [hf] at h
  have ha := (lorentzExtension_sphere_time_pos f ξ).ne'
  have hm := congrArg (fun v : E => (lorentzExtension f (1, (ξ : E))).1 • v) h
  simp only [smul_smul, mul_inv_cancel₀ ha, one_smul] at hm
  apply Prod.ext
  · change (lorentzExtension f (1, (ξ : E))).1 =
      (lorentzExtension f (1, (ξ : E))).1 * 1
    rw [mul_one]
  · exact hm.symm

private theorem origin_space_eq_zero_of_boundary_identity (hdim : 2 ≤ Module.rank ℝ E)
    (f : Hyperboloid E ≃ᵢ Hyperboloid E)
    (hf : boundaryHomeomorph f = Homeomorph.refl (Metric.sphere (0 : E) 1)) :
    (lorentzExtension f (1, 0)).2 = 0 := by
  classical
  let u := (lorentzExtension f (1, 0)).2
  change u = 0
  have hcol (v : E) (hv : v ≠ 0) : ∃ c : ℝ, u = c • v := by
    let ξ := unitDirection v hv
    let η : Metric.sphere (0 : E) 1 := ⟨-(ξ : E), by simp⟩
    let a := (lorentzExtension f (1, (ξ : E))).1
    let b := (lorentzExtension f (1, (η : E))).1
    have hsum : (2 : ℝ) • lorentzExtension f (1, 0) =
        lorentzExtension f (1, (ξ : E)) + lorentzExtension f (1, (η : E)) := by
      rw [← map_smul, ← map_add]
      congr 1
      apply Prod.ext
      · norm_num
      · change (2 : ℝ) • (0 : E) = (ξ : E) + -(ξ : E)
        simp
    rw [null_ray_of_boundary_identity f hf ξ, null_ray_of_boundary_identity f hf η] at hsum
    have hsp := congrArg Prod.snd hsum
    change (2 : ℝ) • u = a • (ξ : E) + b • -(ξ : E) at hsp
    have hs : (2 : ℝ) • u = (a - b) • (ξ : E) := by
      rw [sub_smul]
      simpa only [smul_neg, sub_eq_add_neg] using hsp
    have hh := congrArg (fun w : E => (2 : ℝ)⁻¹ • w) hs
    simp only [smul_smul, inv_mul_cancel₀ (two_ne_zero : (2 : ℝ) ≠ 0), one_smul] at hh
    change u = ((2 : ℝ)⁻¹ * (a - b)) • (‖v‖⁻¹ • v) at hh
    exact ⟨(2 : ℝ)⁻¹ * (a - b) * ‖v‖⁻¹, by simpa only [smul_smul] using hh⟩
  obtain ⟨v, hv⟩ := exists_linearIndependent_of_le_rank (R := ℝ) (M := E) (n := 2) hdim
  obtain ⟨a, ha⟩ := hcol (v 0) (LinearIndependent.ne_zero 0 hv)
  obtain ⟨b, hb⟩ := hcol (v 1) (LinearIndependent.ne_zero 1 hv)
  by_contra hu
  have ha0 : a ≠ 0 := by
    intro hz
    apply hu
    simpa only [hz, zero_smul] using ha
  have hij := hv.eq_of_smul_apply_eq_smul_apply a b 0 1 ha0 (ha.symm.trans hb)
  have h01 : (0 : ℕ) = 1 := congrArg Fin.val hij
  norm_num at h01

private theorem isometry_eq_refl_of_boundary_identity (hdim : 2 ≤ Module.rank ℝ E)
    (f : Hyperboloid E ≃ᵢ Hyperboloid E)
    (hf : boundaryHomeomorph f = Homeomorph.refl (Metric.sphere (0 : E) 1)) :
    f = IsometryEquiv.refl (Hyperboloid E) := by
  have hs := origin_space_eq_zero_of_boundary_identity hdim f hf
  have ht : (lorentzExtension f (1, 0)).1 = 1 := by
    have h := (lorentzExtension f).map_app ((1, 0) : ℝ × E) (1, 0)
    rw [lorentzForm_apply, lorentzForm_apply, hs] at h
    simp only [inner_zero_left, one_mul, zero_sub] at h
    apply (sq_eq_sq₀ (lorentzExtension_origin_time_pos f).le zero_le_one).mp
    nlinarith only [h]
  have ho : lorentzExtension f (1, 0) = (1, 0) := Prod.ext ht hs
  have htime (z : ℝ × E) : (lorentzExtension f z).1 = z.1 := by
    have h := (lorentzExtension f).map_app z (1, 0)
    rw [ho] at h
    simp only [lorentzForm_apply, inner_zero_left, one_mul, zero_sub] at h
    linarith only [h]
  have hnull (ξ : Metric.sphere (0 : E) 1) :
      lorentzExtension f (1, (ξ : E)) = (1, (ξ : E)) := by
    rw [null_ray_of_boundary_identity f hf ξ, htime, one_smul]
  have hfixed (z : ℝ × E) : lorentzExtension f z = z := by
    rcases z with ⟨t, v⟩
    by_cases hv : v = 0
    · subst v
      have hd : (t, (0 : E)) = t • ((1 : ℝ), (0 : E)) := by ext <;> simp
      rw [hd, map_smul, ho]
    · let ξ := unitDirection v hv
      have hd : (t, v) = (t - ‖v‖) • ((1 : ℝ), (0 : E)) + ‖v‖ • (1, (ξ : E)) := by
        apply Prod.ext
        · change t = (t - ‖v‖) * 1 + ‖v‖ * 1
          ring
        · change v = (t - ‖v‖) • (0 : E) + ‖v‖ • NormedSpace.normalize v
          simp
      rw [hd, map_add, map_smul, map_smul, ho, hnull ξ]
  apply IsometryEquiv.ext
  intro x
  apply Hyperboloid.ext
  exact congrArg Prod.snd ((lorentzExtension_apply f x).symm.trans (hfixed (x.time, x.space)))

theorem boundaryHomeomorph_injective (hdim : 2 ≤ Module.rank ℝ E) :
    Function.Injective (boundaryHomeomorph (E := E) (F := E)) := by
  intro f g hfg
  have hb : boundaryHomeomorph (f.trans g.symm) = Homeomorph.refl (Metric.sphere (0 : E) 1) := by
    rw [boundaryHomeomorph_trans, ← boundaryHomeomorph_symm, hfg]
    exact Homeomorph.self_trans_symm (boundaryHomeomorph g)
  have he := isometry_eq_refl_of_boundary_identity hdim (f.trans g.symm) hb
  apply IsometryEquiv.ext
  intro x
  have hx := congrArg (fun k : Hyperboloid E ≃ᵢ Hyperboloid E => g (k x)) he
  change g (g.symm (f x)) = g x at hx
  simpa only [g.apply_symm_apply] using hx

end DifferentialGeometry.Hyperboloid
