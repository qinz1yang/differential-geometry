import DifferentialGeometry.Analysis.Parabolic.MaximumPrinciple.Scalar.Weak
import Mathlib.Analysis.Calculus.ContDiff.RCLike

set_option autoImplicit false
noncomputable section
open Set Bundle Manifold DifferentialGeometry
open DifferentialGeometry.Geometry.Curvature DifferentialGeometry.Geometry.Operator
open DifferentialGeometry.Analysis.Parabolic
open scoped Manifold ContDiff Topology
namespace DifferentialGeometry.Analysis
variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [CompactSpace M]

theorem scalar_ode_upper_bound_compact
    (G : MetricConnectionFamily (I := I) (M := M) ℝ) (T : ℝ) (hT : 0 ≤ T)
    (X : ℝ → (x : M) → TangentSpace I x) (u : ℝ → M → ℝ) (v F : ℝ → ℝ)
    (hF : ContDiff ℝ 1 F)
    (hu : ContinuousOn (fun p : ℝ × M => u p.1 p.2) (Icc 0 T ×ˢ univ))
    (hv : ContinuousOn v (Icc 0 T))
    (htime : ∀ t ∈ Icc 0 T, 0 < t → ∀ x : M,
      DifferentiableWithinAt ℝ (fun r => u r x) (Icc 0 T) t)
    (hspace : ∀ t ∈ Icc 0 T, 0 < t → ContMDiff I 𝓘(ℝ, ℝ) ∞ (u t))
    (hheat : ∀ t ∈ Icc 0 T, 0 < t → ∀ x : M,
      parabolicOperatorWithDrift G T X u t x ≤ F (u t x))
    (hode : ∀ t ∈ Icc 0 T, 0 < t → HasDerivWithinAt v (F (v t)) (Icc 0 T) t)
    (hinit : ∀ x : M, u 0 x ≤ v 0) :
    ∀ t ∈ Icc 0 T, ∀ x : M, u t x ≤ v t := by
  by_cases hp : 0 < T
  · let Q := fun a : ℝ => -F (-a)
    have hQ : ContDiff ℝ 1 Q := (hF.comp contDiff_id.neg).neg
    have hs := scalarWeakMaximumPrincipleValueSet_isCompact T
      (fun t x => -u t x) (fun t => -v t) hu.neg hv.neg
    obtain ⟨K, hK⟩ := LocallyLipschitzOn.exists_lipschitzOnWith_of_compact hs
      hQ.locallyLipschitz.locallyLipschitzOn
    have hw (t : ℝ) (ht : t ∈ Icc 0 T) (htp : 0 < t) :
        ContMDiff I 𝓘(ℝ, ℝ) ∞ (fun x => Real.exp (-(K : ℝ) * t) * (-u t x - -v t)) :=
      contMDiff_const.mul ((hspace t ht htp).neg.sub contMDiff_const)
    have hz (t : ℝ) (ht : t ∈ Icc 0 T) (htp : 0 < t) :
        ContMDiff I 𝓘(ℝ, ℝ) ∞ (fun x => -u t x - -v t) :=
      (hspace t ht htp).neg.sub contMDiff_const
    apply scalar_weak_maximum_principle_ode_compare_subsolution G T hT X u v (fun a _ => F a) K
    · have he : Continuous (fun p : ℝ × M => Real.exp (-(K : ℝ) * p.1)) :=
        Real.continuous_exp.comp (continuous_const.mul continuous_fst)
      exact he.continuousOn.mul (hu.neg.sub (hv.neg.comp continuous_fst.continuousOn (fun _ h => h.1)))
    · exact fun t ht htpos x => (hw t ht htpos).mdifferentiableAt (by simp)
    · exact fun t ht htpos x => gradientFun_mdiffAt (G.metric t) (hw t ht htpos) x
    · exact fun t ht htpos x => (htime t ht htpos x).neg
    · exact fun t ht htpos => (hode t ht htpos).differentiableWithinAt.neg
    · exact fun t ht htpos x => (hspace t ht htpos).neg.mdifferentiableAt (by simp)
    · exact fun t ht htpos x => (hz t ht htpos).mdifferentiableAt (by simp)
    · exact fun t ht htpos x => gradientFun_mdiffAt (G.metric t) (hz t ht htpos) x
    · intro t ht htpos x
      rw [parabolic_neg G T X u t x (htime t ht htpos x)
        (fun y => (hspace t ht htpos).mdifferentiableAt (by simp))
        (gradientFun_mdiffAt (G.metric t) (hspace t ht htpos) x)]
      simpa only [neg_neg] using neg_le_neg (hheat t ht htpos x)
    · intro t ht htpos
      have hh := (hode t ht htpos).neg.derivWithin ((uniqueDiffOn_Icc hp) t ht)
      simp only [neg_neg]
      convert hh using 1
      all_goals rfl
    · exact hinit
    · exact fun _ _ => hK
  · have hz : T = 0 := le_antisymm (le_of_not_gt hp) hT
    subst T
    intro t ht x
    have ht0 : t = 0 := le_antisymm ht.2 ht.1
    simpa only [ht0] using hinit x

theorem scalar_quadratic_reaction_bound_compact
    (G : MetricConnectionFamily (I := I) (M := M) ℝ) (T : ℝ) (hT : 0 ≤ T)
    (X : ℝ → (x : M) → TangentSpace I x) (u : ℝ → M → ℝ)
    (c A : ℝ) (hc : 0 ≤ c) (hA : 0 ≤ A) (hsmall : c * (A + 1) * T ≤ 1 / 2)
    (hu : ContinuousOn (fun p : ℝ × M => u p.1 p.2) (Icc 0 T ×ˢ univ))
    (htime : ∀ t ∈ Icc 0 T, 0 < t → ∀ x : M,
      DifferentiableWithinAt ℝ (fun r => u r x) (Icc 0 T) t)
    (hspace : ∀ t ∈ Icc 0 T, 0 < t → ContMDiff I 𝓘(ℝ, ℝ) ∞ (u t))
    (hheat : ∀ t ∈ Icc 0 T, 0 < t → ∀ x : M,
      parabolicOperatorWithDrift G T X u t x ≤ c * (u t x + 1) ^ 2)
    (hinit : ∀ x : M, u 0 x ≤ A) :
    ∀ t ∈ Icc 0 T, ∀ x : M, u t x ≤ 2 * A + 1 := by
  let v := fun t : ℝ => (A + 1) / (1 - c * (A + 1) * t) - 1
  have hden (t : ℝ) (ht : t ∈ Icc 0 T) : 0 < 1 - c * (A + 1) * t := by
    have hh := mul_le_mul_of_nonneg_left ht.2 (mul_nonneg hc (by linarith : 0 ≤ A + 1))
    linarith
  have hv : ContinuousOn v (Icc 0 T) :=
    (continuousOn_const.div (continuousOn_const.sub (continuousOn_const.mul continuousOn_id))
      (fun t ht => (hden t ht).ne')).sub continuousOn_const
  have hd (t : ℝ) (ht : t ∈ Icc 0 T) :
      HasDerivWithinAt v (c * (v t + 1) ^ 2) (Icc 0 T) t := by
    have hlinear : HasDerivAt (fun r : ℝ => 1 - c * (A + 1) * r) (-(c * (A + 1))) t := by
      have hh := (hasDerivAt_const t (1 : ℝ)).sub
        ((hasDerivAt_id t).const_mul (c * (A + 1)))
      simp only [zero_sub, mul_one] at hh
      convert hh using 1
      all_goals rfl
    have hh := ((hasDerivAt_const t (A + 1)).div hlinear (hden t ht).ne').sub_const 1
    have he : (0 * (1 - c * (A + 1) * t) - (A + 1) * -(c * (A + 1))) /
        (1 - c * (A + 1) * t) ^ 2 = c * (v t + 1) ^ 2 := by
      dsimp only [v]
      rw [sub_add_cancel, div_pow]
      ring
    rw [he] at hh
    exact hh.hasDerivWithinAt
  have hb := scalar_ode_upper_bound_compact G T hT X u v (fun z => c * (z + 1) ^ 2)
    (contDiff_const.mul ((contDiff_id.add contDiff_const).pow 2)) hu hv htime hspace hheat
    (fun t ht _ => hd t ht) (by simpa only [v, mul_zero, sub_zero, div_one, add_sub_cancel_right] using hinit)
  intro t ht x
  apply (hb t ht x).trans
  have hs : c * (A + 1) * t ≤ 1 / 2 :=
    (mul_le_mul_of_nonneg_left ht.2 (mul_nonneg hc (by linarith : 0 ≤ A + 1))).trans hsmall
  have hvb : (A + 1) / (1 - c * (A + 1) * t) ≤ 2 * (A + 1) := by
    apply (div_le_iff₀ (hden t ht)).mpr
    nlinarith
  dsimp only [v]
  linarith
end DifferentialGeometry.Analysis
