import DifferentialGeometry.Analysis.ODE.Flow.Planar.ConstantOutsideCompactFlow
import DifferentialGeometry.Analysis.ODE.Flow.Planar.FlowSupport
import Mathlib.Analysis.Calculus.BumpFunction.InnerProduct

noncomputable section
open Set Metric Filter Topology
open scoped ContDiff Manifold

namespace DifferentialGeometry.Analysis

theorem exists_compact_isotopy_realizing_flow_germ
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] {v : E → E} (hv : ContDiff ℝ ∞ v)
    (Γ : E × ℝ → E) (hΓ : Continuous Γ)
    (hΓzero : ∀ x, Γ (x, 0) = x)
    (hΓfix : ∀ t ∈ Icc (0 : ℝ) 1, Γ (0, t) = 0)
    (hΓderiv : ∀ x t, t ∈ Icc (0 : ℝ) 1 →
      HasDerivAt (fun s ↦ Γ (x, s)) (v (Γ (x, t))) t)
    (r : ℝ) (hr : 0 < r) :
    ∃ D : ℝ → Diffeomorph 𝓘(ℝ, E) 𝓘(ℝ, E) E E ∞,
      ContDiff ℝ ∞ (fun q : ℝ × E ↦ D q.1 q.2) ∧
      ContDiff ℝ ∞ (fun q : ℝ × E ↦ (D q.1).symm q.2) ∧
      D 0 = Diffeomorph.refl 𝓘(ℝ, E) E ∞ ∧
      (D 1 : E → E) =ᶠ[𝓝 0] (fun x ↦ Γ (x, 1)) ∧
      ∀ p x, x ∉ closedBall 0 (2 * r) → D p x = x ∧ (D p).symm x = x := by
  let β : ContDiffBump (0 : E) := ⟨r, 2 * r, hr, by linarith⟩
  let w : E → E := fun x ↦ β x • v x
  have hw : ContDiff ℝ ∞ w := β.contDiff.smul hv
  have hwc : HasCompactSupport w := β.hasCompactSupport.smul_right
  obtain ⟨D, hD, hderiv, hzero, _, hinv⟩ := exists_smoothFlow_of_eq_const_off_compact hw 0
    (by simpa only [sub_zero] using hwc)
  have hDi : ContDiff ℝ ∞ (fun q : ℝ × E ↦ (D q.1).symm q.2) := by
    simp_rw [hinv]
    exact hD.comp (contDiff_fst.neg.prodMk contDiff_snd)
  have hnear : ∀ᶠ x in 𝓝 (0 : E), ∀ t ∈ Icc (0 : ℝ) 1, Γ (x, t) ∈ ball 0 r := by
    apply isCompact_Icc.eventually_forall_of_forall_eventually
    intro t ht
    apply hΓ.continuousAt.preimage_mem_nhds
    apply isOpen_ball.mem_nhds
    rw [hΓfix t ht]
    exact mem_ball_self hr
  have hgerm : (D 1 : E → E) =ᶠ[𝓝 0] fun x ↦ Γ (x, 1) := by
    filter_upwards [hnear] with x hx
    have hcurve (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) :
        HasDerivAt (fun s ↦ Γ (x, s)) (w (Γ (x, t))) t := by
      have hβ : β (Γ (x, t)) = 1 := β.one_of_mem_closedBall (ball_subset_closedBall (hx t ht))
      rw [show w (Γ (x, t)) = v (Γ (x, t)) by simp only [w, hβ, one_smul]]
      exact hΓderiv x t ht
    have he := DifferentialGeometry.Analysis.ODE.Flow.orbit_unique_Icc hw
      (a := 0) (b := 1) (fun t _ ↦ (hderiv x t).hasDerivWithinAt)
      (fun t ht ↦ (hcurve t ht).hasDerivWithinAt) (by rw [hzero, hΓzero]; rfl)
    exact he (show (1 : ℝ) ∈ Icc 0 1 by simp)
  have hs : tsupport w ⊆ closedBall 0 (2 * r) := by
    have hh : tsupport w ⊆ tsupport (β : E → ℝ) := tsupport_smul_subset_left β v
    exact hh.trans_eq β.tsupport_eq
  have hfix (p : ℝ) (x : E) (hx : x ∉ closedBall 0 (2 * r)) : D p x = x := by
    have hDs := tsupport_integralCurveFamily_sub_subset (hw.of_le (by simp))
      (Γ := fun x t ↦ D t x) (fun x ↦ by rw [hzero]; rfl) hderiv p
    exact sub_eq_zero.mp (image_eq_zero_of_notMem_tsupport
      (f := fun x ↦ D p x - x) (fun h ↦ hx (hs (hDs h))))
  refine ⟨D, hD, hDi, hzero, hgerm, ?_⟩
  intro p x hx
  refine ⟨hfix p x hx, ?_⟩
  apply (D p).injective
  exact ((D p).apply_symm_apply x).trans (hfix p x hx).symm

theorem exists_compact_isotopy_realizing_exp_germ
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    (X : E →L[ℝ] E) (r : ℝ) (hr : 0 < r) :
    ∃ D : ℝ → Diffeomorph 𝓘(ℝ, E) 𝓘(ℝ, E) E E ∞,
      ContDiff ℝ ∞ (fun q : ℝ × E ↦ D q.1 q.2) ∧
      ContDiff ℝ ∞ (fun q : ℝ × E ↦ (D q.1).symm q.2) ∧
      D 0 = Diffeomorph.refl 𝓘(ℝ, E) E ∞ ∧
      (D 1 : E → E) =ᶠ[𝓝 0] (fun x ↦ NormedSpace.exp X x) ∧
      ∀ p z, z ∉ closedBall 0 (2 * r) → D p z = z ∧ (D p).symm z = z := by
  have hderiv (x : E) (t : ℝ) :
      HasDerivAt (fun s : ℝ ↦ NormedSpace.exp (s • X) x)
        (X (NormedSpace.exp (t • X) x)) t := by
    have h1 : HasStrictFDerivAt (fun u : ℝ ↦ NormedSpace.exp (u • X))
        (NormedSpace.exp (t • X) • (1 : ℝ →L[ℝ] ℝ).smulRight X) t :=
      hasStrictFDerivAt_exp_smul_const ℝ X t
    have hc : HasFDerivAt (fun u : ℝ ↦ ((ContinuousLinearMap.apply ℝ E) x)
        (NormedSpace.exp (u • X)))
        (((ContinuousLinearMap.apply ℝ E) x) ∘SL
          (NormedSpace.exp (t • X) • (1 : ℝ →L[ℝ] ℝ).smulRight X)) t :=
      (ContinuousLinearMap.hasFDerivAt ((ContinuousLinearMap.apply ℝ E) x)).comp t h1.hasFDerivAt
    have hval : (((ContinuousLinearMap.apply ℝ E) x) ∘SL
        (NormedSpace.exp (t • X) • (1 : ℝ →L[ℝ] ℝ).smulRight X)) 1 =
        X (NormedSpace.exp (t • X) x) := by
      simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.apply_apply, smul_apply,
        ContinuousLinearMap.smulRight_apply, one_apply_eq_self, one_smul, smul_eq_mul]
      rw [← mul_apply_eq_comp, ((Commute.refl X).smul_left t).exp_left.eq, mul_apply_eq_comp]
    have hd := hc.hasDerivAt
    rw [hval] at hd
    simpa only [ContinuousLinearMap.apply_apply] using hd
  have hexpcont : Continuous (NormedSpace.exp : (E →L[ℝ] E) → (E →L[ℝ] E)) :=
    continuous_iff_continuousAt.mpr fun x ↦ (NormedSpace.exp_analytic (𝕂 := ℝ) x).continuousAt
  have hΓcont : Continuous (fun q : E × ℝ ↦ NormedSpace.exp (q.2 • X) q.1) :=
    (hexpcont.comp (continuous_snd.smul continuous_const)).clm_apply continuous_fst
  have hΓzero : ∀ x : E, NormedSpace.exp ((0 : ℝ) • X) x = x := by
    intro x
    simp only [zero_smul, NormedSpace.exp_zero, one_apply_eq_self]
  have hΓfix : ∀ t ∈ Icc (0 : ℝ) 1, NormedSpace.exp (t • X) (0 : E) = 0 := by
    intro t _
    simp only [map_zero]
  obtain ⟨D, hD, hDi, hD0, hDg, hDfix⟩ :=
    exists_compact_isotopy_realizing_flow_germ (v := fun x ↦ X x) X.contDiff
      (fun q : E × ℝ ↦ NormedSpace.exp (q.2 • X) q.1) hΓcont hΓzero hΓfix
      (fun x t _ ↦ hderiv x t) r hr
  exact ⟨D, hD, hDi, hD0, by simpa only [one_smul] using hDg, hDfix⟩


end DifferentialGeometry.Analysis
