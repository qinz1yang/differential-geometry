/-
Copyright (c) 2026 Yuan Liao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuan Liao
-/
import DifferentialGeometry.Topology.PiecewiseLinear.GeneralPosition
import DifferentialGeometry.Topology.Manifold.FramedCornerSmoothing

open Set Metric
open scoped ContDiff Manifold

namespace DifferentialGeometry.Topology.PiecewiseLinear

def cornerShear : (ℝ × ℝ) ≃ₜ (ℝ × ℝ) where
  toFun p := (p.1, |p.1| + p.2)
  invFun p := (p.1, p.2 - |p.1|)
  left_inv p := by simp
  right_inv p := by
    refine Prod.ext (by rfl) ?_
    change |p.1| + (p.2 - |p.1|) = p.2
    ring
  continuous_toFun := continuous_fst.prodMk (continuous_fst.abs.add continuous_snd)
  continuous_invFun := continuous_fst.prodMk (continuous_snd.sub continuous_fst.abs)

theorem cornerShear_apply (p : ℝ × ℝ) : cornerShear p = (p.1, |p.1| + p.2) := rfl

theorem cornerShear_symm_apply (p : ℝ × ℝ) :
    cornerShear.symm p = (p.1, p.2 - |p.1|) := rfl

theorem isPLHomeomorphOn_cornerShear : IsPLHomeomorphOn cornerShear univ univ := by
  have hf : IsPiecewiseAffineOn (Prod.fst : ℝ × ℝ → ℝ) univ :=
    isPiecewiseAffineOn_of_affine (LinearMap.fst ℝ ℝ ℝ).toAffineMap isOpen_univ
  have hg : IsPiecewiseAffineOn (Prod.snd : ℝ × ℝ → ℝ) univ :=
    isPiecewiseAffineOn_of_affine (LinearMap.snd ℝ ℝ ℝ).toAffineMap isOpen_univ
  have hpl : IsPiecewiseAffineOn cornerShear univ := hf.prod_mk (hf.abs.add hg)
  have hinv : IsPiecewiseAffineOn cornerShear.symm univ :=
    IsPiecewiseAffineOn.symm (e := cornerShear.toOpenPartialHomeomorph) hpl
  have hbij : BijOn cornerShear univ univ :=
    ⟨mapsTo_univ _ _, cornerShear.injective.injOn, fun y _ =>
      ⟨cornerShear.symm y, mem_univ _, cornerShear.apply_symm_apply y⟩⟩
  refine ⟨hbij, hpl, hinv.congr fun y hy => ?_⟩
  apply cornerShear.injective
  exact (hbij.invOn_invFunOn.2 hy).trans (cornerShear.apply_symm_apply y).symm

theorem not_differentiableAt_cornerShear :
    ¬ DifferentiableAt ℝ cornerShear (0 : ℝ × ℝ) := by
  intro h
  have hp : DifferentiableAt ℝ (fun x : ℝ => (x, (0 : ℝ))) 0 :=
    differentiableAt_id.prodMk (differentiableAt_const 0)
  have ha : DifferentiableAt ℝ (fun x : ℝ => (cornerShear (x, 0)).2) 0 :=
    h.snd.comp (f := fun x : ℝ => (x, (0 : ℝ))) 0 hp
  apply not_differentiableAt_abs_zero
  simpa only [Function.comp_def, cornerShear_apply, add_zero] using ha

theorem exists_isotopy_smoothing_cornerShear {η : ℝ} (hη : 0 < η) :
    ∃ δ : ℝ, 0 < δ ∧ δ < η / 8 ∧
      ∃ H : ℝ → (ℝ × ℝ) ≃ₜ (ℝ × ℝ),
        Continuous (fun z : ℝ × (ℝ × ℝ) => H z.1 z.2) ∧
        Continuous (fun z : ℝ × (ℝ × ℝ) => (H z.1).symm z.2) ∧
        H 0 = Homeomorph.refl (ℝ × ℝ) ∧
        (∀ t, EqOn (H t) id (ball (0 : ℝ × ℝ) η)ᶜ ∧
          EqOn (H t).symm id (ball (0 : ℝ × ℝ) η)ᶜ) ∧
        (∀ t p, dist (H t p) p < η) ∧
        ∃ d : (ℝ × ℝ) ≃ₘ[ℝ] (ℝ × ℝ),
          (∀ p, d p = (p.1, Real.smoothAbs δ p.1 + p.2)) ∧
          (∀ p, |p.2| ≤ η / 8 → H 1 (cornerShear p) = d p) ∧
          (∀ A ⊆ {p : ℝ × ℝ | |p.2| ≤ η / 8}, H 1 '' (cornerShear '' A) = d '' A) ∧
          H 1 ≠ Homeomorph.refl (ℝ × ℝ) := by
  obtain ⟨δ, hδ, hδη, H, hH, hHi, hH0, hfix, hdist, d, hd, hframe, hne⟩ :=
    Manifold.exists_isotopy_smoothing_framed_corner hη
  refine ⟨δ, hδ, hδη, H, hH, hHi, hH0, hfix, hdist, d, hd,
    fun p hp => hframe p.1 p.2 hp, ?_, hne⟩
  intro A hA
  rw [image_image]
  apply image_congr
  intro p hp
  exact hframe p.1 p.2 (hA hp)

end DifferentialGeometry.Topology.PiecewiseLinear
