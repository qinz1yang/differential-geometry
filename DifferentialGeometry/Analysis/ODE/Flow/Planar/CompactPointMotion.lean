import DifferentialGeometry.Analysis.ODE.Flow.Planar.ConstantOutsideCompactFlow
import DifferentialGeometry.Analysis.ODE.Flow.Planar.FlowSupport
import Mathlib.Analysis.Calculus.BumpFunction.InnerProduct

noncomputable section
open Set Metric
open scoped ContDiff Manifold

namespace DifferentialGeometry.Analysis

theorem exists_compact_isotopy_moving_point
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] (a b : E) :
    ∃ D : ℝ → Diffeomorph 𝓘(ℝ, E) 𝓘(ℝ, E) E E ∞,
      ContDiff ℝ ∞ (fun q : ℝ × E ↦ D q.1 q.2) ∧
      ContDiff ℝ ∞ (fun q : ℝ × E ↦ (D q.1).symm q.2) ∧
      D 0 = Diffeomorph.refl 𝓘(ℝ, E) E ∞ ∧ D 1 a = b ∧
      ∃ K : Set E, IsCompact K ∧
        ∀ p x, x ∉ K → D p x = x ∧ (D p).symm x = x := by
  let β : ContDiffBump a :=
    ⟨‖b - a‖ + 1, ‖b - a‖ + 2, by positivity, by linarith⟩
  let v : E → E := fun x ↦ β x • (b - a)
  have hv : ContDiff ℝ ∞ v := β.contDiff.smul contDiff_const
  have hvc : HasCompactSupport v := β.hasCompactSupport.smul_right
  obtain ⟨D, hD, hderiv, hzero, _, hinv⟩ := exists_smoothFlow_of_eq_const_off_compact hv 0
    (by simpa only [sub_zero] using hvc)
  have hDi : ContDiff ℝ ∞ (fun q : ℝ × E ↦ (D q.1).symm q.2) := by
    simp_rw [hinv]
    exact hD.comp (contDiff_fst.neg.prodMk contDiff_snd)
  let γ : ℝ → E := fun t ↦ a + t • (b - a)
  have hγderiv (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) : HasDerivAt γ (v (γ t)) t := by
    have hb : β (γ t) = 1 := β.one_of_mem_closedBall (by
      change dist (a + t • (b - a)) a ≤ ‖b - a‖ + 1
      rw [dist_eq_norm, add_sub_cancel_left, norm_smul, Real.norm_eq_abs, abs_of_nonneg ht.1]
      nlinarith [mul_le_mul_of_nonneg_right ht.2 (norm_nonneg (b - a))])
    rw [show v (γ t) = b - a by simp only [v, hb, one_smul]]
    simpa only [γ, id_eq, one_smul] using ((hasDerivAt_id t).smul_const (b - a)).const_add a
  have hmove : D 1 a = b := by
    have he := DifferentialGeometry.Analysis.ODE.Flow.orbit_unique_Icc hv
      (a := 0) (b := 1) (fun t _ ↦ (hderiv a t).hasDerivWithinAt)
      (fun t ht ↦ (hγderiv t ht).hasDerivWithinAt) (by rw [hzero]; simp [γ])
    have hh := he (show (1 : ℝ) ∈ Icc 0 1 by simp)
    simpa only [γ, one_smul, add_sub_cancel] using hh
  have hfix (p : ℝ) (x : E) (hx : x ∉ tsupport v) : D p x = x := by
    have hs := tsupport_integralCurveFamily_sub_subset (hv.of_le (by simp))
      (Γ := fun x t ↦ D t x) (fun x ↦ by rw [hzero]; rfl) hderiv p
    exact sub_eq_zero.mp (image_eq_zero_of_notMem_tsupport
      (f := fun x ↦ D p x - x) (fun h ↦ hx (hs h)))
  refine ⟨D, hD, hDi, hzero, hmove, tsupport v, hvc.isCompact, ?_⟩
  intro p x hx
  refine ⟨hfix p x hx, ?_⟩
  apply (D p).injective
  exact ((D p).apply_symm_apply x).trans (hfix p x hx).symm

end DifferentialGeometry.Analysis
