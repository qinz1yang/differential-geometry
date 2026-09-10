import DifferentialGeometry.Analysis.ODE.Flow.GlobalSliceSmoothness
import Mathlib.Geometry.Manifold.Diffeomorph
import Mathlib.Analysis.Calculus.Deriv.Add

noncomputable section
open Set Filter Topology
open scoped ContDiff Manifold

namespace Poincare.Analysis

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

theorem contDiff_globalIntegralCurveFamily
    {v : E → E} (hv : ContDiff ℝ ∞ v) {Γ : E → ℝ → E}
    (hzero : ∀ x, Γ x 0 = x)
    (hderiv : ∀ x t, HasDerivAt (Γ x) (v (Γ x t)) t) :
    ContDiff ℝ ∞ (Function.uncurry Γ) := by
  have hcont (x : E) : Continuous (Γ x) := continuous_iff_continuousAt.mpr
    (fun t ↦ (hderiv x t).continuousAt)
  have hslice (t : ℝ) : ContDiff ℝ ∞ (fun x ↦ Γ x t) := by
    let R := |t| + 1
    have hR : 0 < R := by dsimp [R]; positivity
    apply contDiffOn_univ.mp
    apply DifferentialGeometry.Analysis.ODE.Flow.flow_slice_smooth hv isOpen_univ
      (a := -R) (b := R) (t₀ := 0) ⟨by linarith, hR⟩
      (fun x _ ↦ hzero x) (fun x _ ↦ (hcont x).continuousOn)
      (fun x _ t _ ↦ hderiv x t) t
    exact ⟨by dsimp [R]; linarith [neg_abs_le t], by dsimp [R]; linarith [le_abs_self t]⟩
  apply contDiff_iff_contDiffAt.mpr
  rintro ⟨x, t⟩
  have hjoint : ContDiffOn ℝ ∞ (Function.uncurry Γ) (univ ×ˢ Icc (t - 1) (t + 1)) :=
    DifferentialGeometry.Analysis.ODE.Flow.flow_joint_right_on isOpen_univ hv.contDiffOn
      isOpen_univ (hslice (t - 1)).contDiffOn
      (fun y _ ↦ ⟨rfl, fun s _ ↦ (hderiv y s).hasDerivWithinAt⟩)
      (fun _ _ _ _ ↦ mem_univ _)
  exact hjoint.contDiffAt (prod_mem_nhds Filter.univ_mem (Icc_mem_nhds (by linarith) (by linarith)))

omit [FiniteDimensional ℝ E] in
private theorem integralCurveFamily_add
    {v : E → E} (hv : ContDiff ℝ ∞ v) {Γ : E → ℝ → E}
    (hzero : ∀ x, Γ x 0 = x)
    (hderiv : ∀ x t, HasDerivAt (Γ x) (v (Γ x t)) t)
    (x : E) (s t : ℝ) : Γ x (s + t) = Γ (Γ x s) t := by
  let R := |t| + 1
  have hR : 0 < R := by dsimp [R]; positivity
  have hshift (r : ℝ) : HasDerivAt (fun r ↦ Γ x (s + r))
      (v (Γ x (s + r))) r := by
    simpa only [one_smul, zero_add, Pi.add_apply, id_eq, Function.comp_def] using
      (hderiv x (s + r)).scomp r
      ((hasDerivAt_const r s).add (hasDerivAt_id r))
  have heq := DifferentialGeometry.Analysis.ODE.Flow.orbit_unique_smooth
    (hv.of_le (by norm_num)) (a := -R) (b := R) (t₀ := 0)
    ⟨by linarith, hR⟩ (fun r _ ↦ hshift r) (fun r _ ↦ hderiv (Γ x s) r)
    (by simp [hzero])
  exact heq ⟨by dsimp [R]; linarith [neg_abs_le t], by dsimp [R]; linarith [le_abs_self t]⟩

theorem exists_smoothFlow_of_globalIntegralCurves
    {v : E → E} (hv : ContDiff ℝ ∞ v)
    (hcomplete : ∀ x : E, ∃ γ : ℝ → E, γ 0 = x ∧ ∀ t, HasDerivAt γ (v (γ t)) t) :
    ∃ D : ℝ → Diffeomorph 𝓘(ℝ, E) 𝓘(ℝ, E) E E ∞,
      ContDiff ℝ ∞ (fun p : ℝ × E ↦ D p.1 p.2) ∧
      (∀ x t, HasDerivAt (fun r ↦ D r x) (v (D t x)) t) ∧
      D 0 = Diffeomorph.refl 𝓘(ℝ, E) E ∞ ∧
      (∀ s t, D (s + t) = (D s).trans (D t)) ∧
      ∀ t, (D t).symm = D (-t) := by
  choose Γ hzero hderiv using hcomplete
  have hsmooth := contDiff_globalIntegralCurveFamily hv hzero hderiv
  have hadd := integralCurveFamily_add hv hzero hderiv
  let D (t : ℝ) : Diffeomorph 𝓘(ℝ, E) 𝓘(ℝ, E) E E ∞ :=
    { toEquiv :=
        { toFun := fun x ↦ Γ x t
          invFun := fun x ↦ Γ x (-t)
          left_inv := fun x ↦ by
            change Γ (Γ x t) (-t) = x
            rw [← hadd, add_neg_cancel, hzero]
          right_inv := fun x ↦ by
            change Γ (Γ x (-t)) t = x
            rw [← hadd, neg_add_cancel, hzero] }
      contMDiff_toFun := (hsmooth.comp (contDiff_id.prodMk contDiff_const)).contMDiff
      contMDiff_invFun := (hsmooth.comp (contDiff_id.prodMk contDiff_const)).contMDiff }
  refine ⟨D, hsmooth.comp (contDiff_snd.prodMk contDiff_fst), hderiv, ?_, ?_, ?_⟩
  · apply Diffeomorph.ext
    exact hzero
  · intro s t
    apply Diffeomorph.ext
    exact fun x ↦ hadd x s t
  · intro t
    apply Diffeomorph.ext
    exact fun _ ↦ rfl

end Poincare.Analysis
