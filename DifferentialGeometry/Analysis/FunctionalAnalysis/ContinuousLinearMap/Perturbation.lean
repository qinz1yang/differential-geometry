import Mathlib.Analysis.Normed.Operator.Basic
import Mathlib.Topology.Algebra.Order.Field
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Abel
import Mathlib.Tactic.GCongr

open Filter Topology

namespace ContinuousLinearMap

variable {𝕜 X Y Z P : Type*} [NontriviallyNormedField 𝕜]
  [SeminormedAddCommGroup X] [NormedSpace 𝕜 X]
  [SeminormedAddCommGroup Y] [NormedSpace 𝕜 Y]
  [SeminormedAddCommGroup Z] [NormedSpace 𝕜 Z]

private theorem norm_sub_le_of_coercive_of_operator_perturbation
    (J : X →L[𝕜] Y) (Q₀ Q₁ : X →L[𝕜] Z) (x₀ x₁ : X) {C : ℝ}
    (hC : 0 ≤ C)
    (hcoercive : ∀ x, ‖x‖ ≤ C * max ‖J x‖ ‖Q₀ x‖)
    (hsmall : C * ‖Q₁ - Q₀‖ < 1) :
    ‖x₁ - x₀‖ ≤
      C * (‖J (x₁ - x₀)‖ + ‖Q₁ x₁ - Q₀ x₀‖ +
        ‖Q₁ - Q₀‖ * ‖x₀‖) / (1 - C * ‖Q₁ - Q₀‖) := by
  have hden : 0 < 1 - C * ‖Q₁ - Q₀‖ := sub_pos.mpr hsmall
  have hq : ‖Q₀ (x₁ - x₀)‖ ≤
      ‖Q₁ x₁ - Q₀ x₀‖ + ‖Q₁ - Q₀‖ * ‖x₀‖ +
        ‖Q₁ - Q₀‖ * ‖x₁ - x₀‖ := by
    calc
      ‖Q₀ (x₁ - x₀)‖ =
          ‖(Q₁ x₁ - Q₀ x₀) - (Q₁ - Q₀) x₀ -
            (Q₁ - Q₀) (x₁ - x₀)‖ := by
        congr 1
        simp only [sub_apply, map_sub]
        abel
      _ ≤ ‖Q₁ x₁ - Q₀ x₀‖ + ‖(Q₁ - Q₀) x₀‖ +
          ‖(Q₁ - Q₀) (x₁ - x₀)‖ := by
        exact (norm_sub_le _ _).trans (add_le_add (norm_sub_le _ _) le_rfl)
      _ ≤ ‖Q₁ x₁ - Q₀ x₀‖ + ‖Q₁ - Q₀‖ * ‖x₀‖ +
          ‖Q₁ - Q₀‖ * ‖x₁ - x₀‖ := by
        gcongr
        · exact (Q₁ - Q₀).le_opNorm _
        · exact (Q₁ - Q₀).le_opNorm _
  have hmax : max ‖J (x₁ - x₀)‖ ‖Q₀ (x₁ - x₀)‖ ≤
      ‖J (x₁ - x₀)‖ + ‖Q₁ x₁ - Q₀ x₀‖ + ‖Q₁ - Q₀‖ * ‖x₀‖ +
        ‖Q₁ - Q₀‖ * ‖x₁ - x₀‖ := by
    apply max_le
    · have hnonneg : 0 ≤ ‖Q₁ x₁ - Q₀ x₀‖ + ‖Q₁ - Q₀‖ * ‖x₀‖ +
          ‖Q₁ - Q₀‖ * ‖x₁ - x₀‖ := by positivity
      linarith
    · have hnonneg := norm_nonneg (J (x₁ - x₀))
      linarith
  have hmain : ‖x₁ - x₀‖ ≤ C *
      (‖J (x₁ - x₀)‖ + ‖Q₁ x₁ - Q₀ x₀‖ + ‖Q₁ - Q₀‖ * ‖x₀‖ +
        ‖Q₁ - Q₀‖ * ‖x₁ - x₀‖) :=
    (hcoercive (x₁ - x₀)).trans
      (mul_le_mul_of_nonneg_left hmax hC)
  apply (le_div_iff₀ hden).2
  nlinarith [norm_nonneg (x₁ - x₀), norm_nonneg (Q₁ - Q₀),
    norm_nonneg (Q₁ x₁ - Q₀ x₀), norm_nonneg (J (x₁ - x₀)),
    norm_nonneg x₀]

private theorem tendsto_of_coercive_of_operator_perturbation
    {l : Filter P} (J : X →L[𝕜] Y) (Q₀ : X →L[𝕜] Z)
    (Q₁ : P → X →L[𝕜] Z) (x₀ : X) (x₁ : P → X) {C : ℝ}
    (hC : 0 ≤ C)
    (hcoercive : ∀ x, ‖x‖ ≤ C * max ‖J x‖ ‖Q₀ x‖)
    (hsmall : ∀ᶠ p in l, C * ‖Q₁ p - Q₀‖ < 1)
    (hJ : Tendsto (fun p => ‖J (x₁ p - x₀)‖) l (𝓝 0))
    (hsource : Tendsto (fun p => ‖Q₁ p (x₁ p) - Q₀ x₀‖) l (𝓝 0))
    (hop : Tendsto (fun p => ‖Q₁ p - Q₀‖) l (𝓝 0)) :
    Tendsto x₁ l (𝓝 x₀) := by
  have hnum : Tendsto
      (fun p => C * (‖J (x₁ p - x₀)‖ + ‖Q₁ p (x₁ p) - Q₀ x₀‖ +
        ‖Q₁ p - Q₀‖ * ‖x₀‖)) l (𝓝 0) := by
    have hsum := hJ.add (hsource.add (hop.mul_const ‖x₀‖))
    simpa only [zero_mul, zero_add, add_zero, mul_zero, add_assoc] using
      hsum.const_mul C
  have hden : Tendsto (fun p => 1 - C * ‖Q₁ p - Q₀‖) l (𝓝 1) := by
    have hmul := hop.const_mul C
    simpa only [mul_zero, sub_zero] using tendsto_const_nhds.sub hmul
  have hratio : Tendsto (fun p =>
      C * (‖J (x₁ p - x₀)‖ + ‖Q₁ p (x₁ p) - Q₀ x₀‖ +
        ‖Q₁ p - Q₀‖ * ‖x₀‖) / (1 - C * ‖Q₁ p - Q₀‖)) l (𝓝 0) := by
    convert hnum.div hden one_ne_zero using 1
    · funext p
      rfl
    · norm_num
  apply (tendsto_iff_norm_sub_tendsto_zero).2
  apply squeeze_zero'
    (Eventually.of_forall fun p => norm_nonneg (x₁ p - x₀))
    (hsmall.mono fun p hp =>
      norm_sub_le_of_coercive_of_operator_perturbation J Q₀ (Q₁ p) x₀ (x₁ p)
        hC hcoercive hp)
    hratio

theorem tendsto_of_tendsto_apply_of_norm_le_max
    {l : Filter P} (J : X →L[𝕜] Y) (Q₀ : X →L[𝕜] Z)
    (Q₁ : P → X →L[𝕜] Z) (x₀ : X) (x₁ : P → X) {C : ℝ}
    (hC : 0 ≤ C)
    (hcoercive : ∀ x, ‖x‖ ≤ C * max ‖J x‖ ‖Q₀ x‖)
    (hQ : Tendsto Q₁ l (𝓝 Q₀))
    (hJ : Tendsto (fun p => J (x₁ p)) l (𝓝 (J x₀)))
    (hsource : Tendsto (fun p => Q₁ p (x₁ p)) l (𝓝 (Q₀ x₀))) :
    Tendsto x₁ l (𝓝 x₀) := by
  have hop : Tendsto (fun p => ‖Q₁ p - Q₀‖) l (𝓝 0) :=
    tendsto_iff_norm_sub_tendsto_zero.mp hQ
  have hmul : Tendsto (fun p => C * ‖Q₁ p - Q₀‖) l (𝓝 0) := by
    simpa only [mul_zero] using hop.const_mul C
  have hsmall : ∀ᶠ p in l, C * ‖Q₁ p - Q₀‖ < 1 :=
    hmul.eventually (gt_mem_nhds zero_lt_one)
  apply tendsto_of_coercive_of_operator_perturbation J Q₀ Q₁ x₀ x₁
    hC hcoercive hsmall
  · simpa only [map_sub] using tendsto_iff_norm_sub_tendsto_zero.mp hJ
  · exact tendsto_iff_norm_sub_tendsto_zero.mp hsource
  · exact hop

end ContinuousLinearMap
