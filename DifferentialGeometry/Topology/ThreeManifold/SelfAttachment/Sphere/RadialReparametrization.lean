import DifferentialGeometry.Analysis.Calculus.Inverse.LocalDiffeomorphStraightening
import Mathlib.Geometry.Manifold.Instances.Icc

set_option autoImplicit false
noncomputable section
open Set Filter
open scoped Manifold ContDiff Topology

namespace DifferentialGeometry.Topology.Manifold

theorem exists_stereographic_cylinder_reparametrization :
    ∃ D : ℝ ≃ₘ[ℝ] ℝ, StrictMono D ∧ D '' Icc (0 : ℝ) 1 = Icc (0 : ℝ) 1 ∧
      (D : ℝ → ℝ) =ᶠ[𝓝 0] (fun t => t / 15) ∧
      (D : ℝ → ℝ) =ᶠ[𝓝 1] (fun t => (16 / (2 - t) - 1) / 15) := by
  have h₀ : ContDiffOn ℝ ∞ (fun t : ℝ => t / 15) univ := by fun_prop
  have h₁ : ContDiffOn ℝ ∞ (fun t : ℝ => (16 / (2 - t) - 1) / 15) (Iio 2) := by
    exact ((contDiffOn_const.div (contDiffOn_const.sub contDiffOn_id)
      (fun t ht => by change t < 2 at ht; exact (sub_pos.mpr ht).ne')).sub contDiffOn_const).div_const 15
  have hd₀ : deriv (fun t : ℝ => t / 15) 0 = 1 / 15 := by
    exact ((hasDerivAt_id (0 : ℝ)).div_const 15).deriv
  have hd₁ : deriv (fun t : ℝ => (16 / (2 - t) - 1) / 15) 1 = 16 / 15 := by
    have h := (((hasDerivAt_const (1 : ℝ) 16).div
      ((hasDerivAt_const (1 : ℝ) 2).sub (hasDerivAt_id 1)) (by norm_num)).sub_const 1).div_const 15
    convert h.deriv using 1 <;> norm_num
  obtain ⟨D, hm, hlow, hupp, himg⟩ :=
    DifferentialGeometry.Analysis.exists_diffeomorph_eq_endpoint_germs (a := 0) (b := 1)
      (by norm_num) isOpen_univ (mem_univ _) h₀ isOpen_Iio (by norm_num) h₁
      (by norm_num) (by norm_num) (by rw [hd₀]; norm_num) (by rw [hd₁]; norm_num)
  exact ⟨D, hm, himg, hlow, hupp⟩


def unitIntervalRestriction (D : ℝ ≃ₘ[ℝ] ℝ) (hI : D '' Icc (0 : ℝ) 1 = Icc (0 : ℝ) 1) :
    Diffeomorph (𝓡∂ 1) (𝓡∂ 1) (Icc (0 : ℝ) 1) (Icc (0 : ℝ) 1) ∞ := by
  let H := (D.toHomeomorph.image (Icc (0 : ℝ) 1)).trans (Homeomorph.setCongr hI)
  have hval (t : Icc (0 : ℝ) 1) : (H t).val = D t.val := rfl
  have hival (t : Icc (0 : ℝ) 1) : (H.symm t).val = D.symm t.val := by
    apply D.injective
    change D (H.symm t).val = D (D.symm t.val)
    rw [← hval, Homeomorph.apply_symm_apply, D.apply_symm_apply]
  refine ⟨H.toEquiv, ?_, ?_⟩
  · apply contMDiff_iff_comp_subtypeVal_Icc.mpr
    refine ⟨H.continuous, ?_⟩
    exact D.contMDiff.comp contMDiff_subtypeVal_Icc
  · apply contMDiff_iff_comp_subtypeVal_Icc.mpr
    refine ⟨H.symm.continuous, ?_⟩
    exact (D.symm.contMDiff.comp contMDiff_subtypeVal_Icc).congr hival

theorem unitIntervalRestriction_apply (D : ℝ ≃ₘ[ℝ] ℝ)
    (hI : D '' Icc (0 : ℝ) 1 = Icc (0 : ℝ) 1) (t : Icc (0 : ℝ) 1) :
    (unitIntervalRestriction D hI t).val = D t.val := rfl

end DifferentialGeometry.Topology.Manifold
