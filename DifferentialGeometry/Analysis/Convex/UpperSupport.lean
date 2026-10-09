import DifferentialGeometry.Geometry.Comparison.Toponogov.LowerSupportConvexity
import Mathlib.Analysis.Calculus.ContDiff.Operations

open Set Filter
open scoped Topology

namespace DifferentialGeometry.Analysis

theorem concaveOn_of_upper_support {D : Set ℝ} {f : ℝ → ℝ}
    (hD : Convex ℝ D) (hf : ContinuousOn f D)
    (hsupport : ∀ x ∈ interior D, ∃ φ : ℝ → ℝ,
      ContDiffAt ℝ 2 φ x ∧ φ x = f x ∧
        (∀ᶠ y in 𝓝 x, f y ≤ φ y) ∧ deriv (deriv φ) x ≤ 0) :
    ConcaveOn ℝ D f := by
  apply neg_convexOn_iff.mp
  refine Geometry.Comparison.Toponogov.convexOn_of_lower_support hD hf.neg ?_
  intro x hx
  obtain ⟨φ, hφ, hcontact, hupper, hsecond⟩ := hsupport x hx
  refine ⟨-φ, hφ.neg, congrArg Neg.neg hcontact, ?_, ?_⟩
  · exact hupper.mono fun y hy => neg_le_neg hy
  · simpa only [deriv.neg', deriv.fun_neg, neg_nonneg] using hsecond


private theorem second_deriv_sub {f g : ℝ → ℝ} {x : ℝ}
    (hf : ContDiffAt ℝ 2 f x) (hg : ContDiffAt ℝ 2 g x) :
    deriv (deriv (fun t => f t - g t)) x =
      deriv (deriv f) x - deriv (deriv g) x := by
  have hnf : ∀ᶠ t in 𝓝 x, DifferentiableAt ℝ f t :=
    (hf.eventually (by norm_num)).mono fun _ ht => ht.differentiableAt (by norm_num)
  have hng : ∀ᶠ t in 𝓝 x, DifferentiableAt ℝ g t :=
    (hg.eventually (by norm_num)).mono fun _ ht => ht.differentiableAt (by norm_num)
  have heq : deriv (fun t => f t - g t) =ᶠ[𝓝 x] fun t => deriv f t - deriv g t := by
    filter_upwards [hnf, hng] with t htf htg
    exact deriv_sub htf htg
  rw [heq.deriv_eq]
  exact deriv_sub ((hf.derivWithin (m := 1) (by norm_num)).differentiableAt (by norm_num))
    ((hg.derivWithin (m := 1) (by norm_num)).differentiableAt (by norm_num))

theorem concaveOn_sub_quadratic_of_upper_support {D : Set ℝ} {f : ℝ → ℝ} {C : ℝ}
    (hD : Convex ℝ D) (hf : ContinuousOn f D)
    (hsupport : ∀ x ∈ interior D, ∃ φ : ℝ → ℝ,
      ContDiffAt ℝ 2 φ x ∧ φ x = f x ∧
        (∀ᶠ y in 𝓝 x, f y ≤ φ y) ∧ deriv (deriv φ) x ≤ C) :
    ConcaveOn ℝ D (fun t => f t - C / 2 * t ^ 2) := by
  let Q : ℝ → ℝ := fun t => C / 2 * t ^ 2
  have hQ : ContDiff ℝ 2 Q := by dsimp [Q]; fun_prop
  have hQd (x : ℝ) : HasDerivAt Q (C * x) x := by
    have hid : HasDerivAt (fun t : ℝ => t) 1 x := hasDerivAt_id x
    have hsq := hid.mul hid
    convert! hsq.const_mul (C / 2) using 1
    · funext t
      simp only [Q, pow_two, Pi.mul_apply]
    · ring
  have hQderiv : deriv Q = fun x => C * x := funext fun x => (hQd x).deriv
  have hQsecond (x : ℝ) : deriv (deriv Q) x = C := by
    rw [hQderiv]
    have hid : HasDerivAt (fun t : ℝ => t) 1 x := hasDerivAt_id x
    simpa only [id_eq, mul_one] using (hid.const_mul C).deriv
  refine concaveOn_of_upper_support hD (hf.sub hQ.continuous.continuousOn) ?_
  intro x hx
  obtain ⟨φ, hφ, hcontact, hupper, hsecond⟩ := hsupport x hx
  refine ⟨fun t => φ t - Q t, hφ.sub hQ.contDiffAt, ?_, ?_, ?_⟩
  · exact congrArg (fun r => r - Q x) hcontact
  · exact hupper.mono fun y hy => sub_le_sub_right hy (Q y)
  · rw [second_deriv_sub hφ hQ.contDiffAt, hQsecond]
    exact sub_nonpos.mpr hsecond

end DifferentialGeometry.Analysis
