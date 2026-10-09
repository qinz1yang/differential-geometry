import DifferentialGeometry.Geometry.Measure.Area.ConformalMetricDerivative
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

noncomputable section

open Bundle Filter Manifold
open scoped ContDiff Manifold Topology

namespace DifferentialGeometry.Geometry

private theorem hasDerivAt_deriv_sqrt_gram
    {a b c : ℝ → ℝ} {t : ℝ}
    (ha : ContDiffAt ℝ 2 a t) (hb : ContDiffAt ℝ 2 b t)
    (hc : ContDiffAt ℝ 2 c t) (hpos : 0 < a t)
    (heq : a t = b t) (horth : c t = 0) :
    HasDerivAt (deriv (fun r => Real.sqrt (a r * b r - c r ^ 2)))
      ((deriv (deriv a) t + deriv (deriv b) t) / 2 -
        ((deriv a t - deriv b t) ^ 2 + 4 * deriv c t ^ 2) / (4 * a t)) t := by
  have ha₀ := (ha.differentiableAt (by norm_num)).hasDerivAt
  have hb₀ := (hb.differentiableAt (by norm_num)).hasDerivAt
  have hc₀ := (hc.differentiableAt (by norm_num)).hasDerivAt
  have ha₁ := ((ha.derivWithin (m := 1) (by norm_num)).differentiableAt
    (by norm_num)).hasDerivAt
  have hb₁ := ((hb.derivWithin (m := 1) (by norm_num)).differentiableAt
    (by norm_num)).hasDerivAt
  have hc₁ := ((hc.derivWithin (m := 1) (by norm_num)).differentiableAt
    (by norm_num)).hasDerivAt
  have hdet : a t * b t - c t ^ 2 ≠ 0 := by
    rw [horth, ← heq]
    nlinarith
  have hsqrt : Real.sqrt (a t * b t - c t ^ 2) = a t := by
    rw [horth, ← heq]
    simpa using Real.sqrt_mul_self hpos.le
  have hnear : ∀ᶠ r in 𝓝 t, a r * b r - c r ^ 2 ≠ 0 :=
    ((ha.continuousAt.mul hb.continuousAt).sub (hc.continuousAt.pow 2)).eventually_ne hdet
  have hfirst : deriv (fun r => Real.sqrt (a r * b r - c r ^ 2)) =ᶠ[𝓝 t]
      fun r => (deriv a r * b r + a r * deriv b r - 2 * c r * deriv c r) /
        (2 * Real.sqrt (a r * b r - c r ^ 2)) := by
    filter_upwards [ha.eventually (by norm_num), hb.eventually (by norm_num),
      hc.eventually (by norm_num), hnear] with r har hbr hcr hdr
    have hd := (((har.differentiableAt (by norm_num)).hasDerivAt.mul
      (hbr.differentiableAt (by norm_num)).hasDerivAt).sub
      ((hcr.differentiableAt (by norm_num)).hasDerivAt.pow 2)).sqrt hdr
    simpa only [Pi.mul_apply, Pi.sub_apply, Pi.pow_apply, Nat.reduceSub, pow_one,
      Nat.cast_ofNat] using hd.deriv
  have hnum := ((ha₁.mul hb₀).add (ha₀.mul hb₁)).sub ((hc₀.const_mul 2).mul hc₁)
  have hden := (((ha₀.mul hb₀).sub (hc₀.pow 2)).sqrt hdet).const_mul 2
  have hden_ne : 2 * Real.sqrt (a t * b t - c t ^ 2) ≠ 0 := by
    rw [hsqrt]
    positivity
  have hquot := hnum.div hden hden_ne
  have hquot' := hquot.congr_of_eventuallyEq hfirst
  apply hquot'.congr_deriv
  simp only [Pi.mul_apply, Pi.sub_apply, Pi.add_apply, Pi.pow_apply, Nat.reduceSub,
    pow_one, Nat.cast_ofNat, hsqrt]
  simp only [horth, ← heq]
  field_simp [ne_of_gt hpos]
  ring

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

/-- The second metric derivative of the actual area density at a conformal tangent frame.
This is a density Hessian; identifying it with the Jacobi form of a normal variation
requires the geometric second derivatives of the induced metric. -/
theorem hasDerivAt_deriv_tangentTwoJacobian_at_conformal
    {G : ℝ → SmoothRiemannianMetric I M} {t : ℝ} {x : M} {v w : TangentSpace I x}
    (hA : ContDiffAt ℝ 2 (fun r => (G r).inner x v v) t)
    (hB : ContDiffAt ℝ 2 (fun r => (G r).inner x w w) t)
    (hC : ContDiffAt ℝ 2 (fun r => (G r).inner x v w) t)
    (horth : (G t).inner x v w = 0)
    (heq : (G t).inner x v v = (G t).inner x w w) :
    let a := fun r => (G r).inner x v v
    let b := fun r => (G r).inner x w w
    let c := fun r => (G r).inner x v w
    HasDerivAt (deriv (fun r => tangentTwoJacobian (G r) v w))
      ((deriv (deriv a) t + deriv (deriv b) t) / 2 -
        ((deriv a t - deriv b t) ^ 2 + 4 * deriv c t ^ 2) / (4 * a t)) t := by
  dsimp only
  by_cases hv : v = 0
  · subst v
    have hw : w = 0 := by
      by_contra hw
      have hp := (G t).pos x w hw
      have hz : (G t).inner x w w = 0 := by simpa using heq.symm
      linarith
    subst w
    simpa [tangentTwoJacobian] using hasDerivAt_const t (0 : ℝ)
  · exact hasDerivAt_deriv_sqrt_gram hA hB hC ((G t).pos x v hv) heq horth

end DifferentialGeometry.Geometry
