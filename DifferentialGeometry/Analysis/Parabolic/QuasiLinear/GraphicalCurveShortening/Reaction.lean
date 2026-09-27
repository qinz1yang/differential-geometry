import DifferentialGeometry.Analysis.Parabolic.QuasiLinear.GraphicalCurveShortening.Coefficients

open Filter
open scoped ContDiff InnerProductSpace Topology

namespace DifferentialGeometry.Analysis.Parabolic

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

noncomputable def graphDerivativeReaction (p q : E) : E :=
  (-2 * graphDiffusionCoefficient p ^ 2 * ⟪p, q⟫_ℝ) • q

theorem graphDerivativeReaction_zero_left (q : E) :
    graphDerivativeReaction 0 q = 0 := by
  simp [graphDerivativeReaction]

theorem graphDerivativeReaction_zero_right (p : E) :
    graphDerivativeReaction p 0 = 0 := by
  simp [graphDerivativeReaction]

theorem contDiff_graphDerivativeReaction :
    ContDiff ℝ ∞ (fun z : E × E => graphDerivativeReaction z.1 z.2) := by
  exact ((contDiff_const.mul ((contDiff_graphDiffusionCoefficient.comp contDiff_fst).pow 2)).mul
    (contDiff_fst.inner ℝ contDiff_snd)).smul contDiff_snd

theorem graphDerivativeReaction_norm_le (p q : E) :
    ‖graphDerivativeReaction p q‖ ≤ 2 * ‖p‖ * ‖q‖ ^ 2 := by
  rw [graphDerivativeReaction, norm_smul, Real.norm_eq_abs]
  exact (mul_le_mul_of_nonneg_right (graphDiffusionCoefficient_derivative_bound p q)
    (norm_nonneg q)).trans_eq (by ring)

theorem graphDerivativeReaction_sub_norm_le (p q r s : E) :
    ‖graphDerivativeReaction p r - graphDerivativeReaction q s‖ ≤
      2 * ‖p‖ * (‖r‖ + ‖s‖) * ‖r - s‖ +
        (2 + 4 * (‖p‖ + ‖q‖) * ‖q‖) * ‖p - q‖ * ‖s‖ ^ 2 := by
  exact (graphDiffusionCoefficient_derivative_smul_sub_bound p q r s r s).trans_eq (by ring)

theorem graphDerivativeReaction_sub_norm_le_of_norm_le
    {p q r s : E} {R S : ℝ} (hp : ‖p‖ ≤ R) (hq : ‖q‖ ≤ R)
    (hr : ‖r‖ ≤ S) (hs : ‖s‖ ≤ S) :
    ‖graphDerivativeReaction p r - graphDerivativeReaction q s‖ ≤
      4 * R * S * ‖r - s‖ + (2 + 8 * R ^ 2) * S ^ 2 * ‖p - q‖ := by
  have hR : 0 ≤ R := (norm_nonneg p).trans hp
  have hS : 0 ≤ S := (norm_nonneg r).trans hr
  refine (graphDerivativeReaction_sub_norm_le p q r s).trans ?_
  have hsum : ‖r‖ + ‖s‖ ≤ 2 * S := by linarith
  have hmul : (‖p‖ + ‖q‖) * ‖q‖ ≤ 2 * R ^ 2 := by
    have h := mul_le_mul (show ‖p‖ + ‖q‖ ≤ 2 * R by linarith) hq
      (norm_nonneg q) (by positivity : (0 : ℝ) ≤ 2 * R)
    nlinarith only [h]
  have hcoef : 2 + 4 * (‖p‖ + ‖q‖) * ‖q‖ ≤ 2 + 8 * R ^ 2 := by
    nlinarith only [hmul]
  have hsq : ‖s‖ ^ 2 ≤ S ^ 2 := by nlinarith only [hs, norm_nonneg s, hS]
  calc
    _ ≤ 2 * R * (2 * S) * ‖r - s‖ +
        (2 + 8 * R ^ 2) * ‖p - q‖ * S ^ 2 := by
      gcongr
    _ = _ := by ring

theorem graph_slope_parabolic_eq
    {f : ℝ → ℝ → E} {U V : Set ℝ} (hU : IsOpen U) (hV : IsOpen V)
    (hf : ContDiffOn ℝ ∞ (Function.uncurry f) (U ×ˢ V))
    (heq : ∀ x ∈ U, ∀ t ∈ V, deriv (fun s => f x s) t =
      graphDiffusionCoefficient (deriv (fun y => f y t) x) •
        deriv (deriv (fun y => f y t)) x)
    {x t : ℝ} (hx : x ∈ U) (ht : t ∈ V) :
    deriv (fun s => deriv (fun y => f y s) x) t =
      graphDiffusionCoefficient (deriv (fun y => f y t) x) •
        deriv (deriv (deriv (fun y => f y t))) x +
      graphDerivativeReaction (deriv (fun y => f y t) x)
        (deriv (deriv (fun y => f y t)) x) := by
  have hfat : ContDiffAt ℝ ∞ (Function.uncurry f) (x, t) :=
    (hf (x, t) ⟨hx, ht⟩).contDiffAt ((hU.prod hV).mem_nhds ⟨hx, ht⟩)
  have hpat := contDiffAt_deriv_fst (m := ∞) hfat (by simp)
  have hqat := contDiffAt_deriv_fst (m := ∞) hpat (by simp)
  have hp : DifferentiableAt ℝ (fun y => deriv (fun z => f z t) y) x :=
    (hpat.comp x (contDiffAt_id.prodMk contDiffAt_const)).differentiableAt (by simp)
  have hq : DifferentiableAt ℝ (deriv (fun y => deriv (fun z => f z t) y)) x :=
    (hqat.comp x (contDiffAt_id.prodMk contDiffAt_const)).differentiableAt (by simp)
  rw [deriv_deriv_time_comm_on_open hU hV hf hx ht]
  have hnear : (fun y => deriv (fun s => f y s) t) =ᶠ[𝓝 x]
      fun y => graphDiffusionCoefficient (deriv (fun z => f z t) y) •
        deriv (deriv (fun z => f z t)) y := by
    filter_upwards [hU.mem_nhds hx] with y hy
    exact heq y hy t ht
  rw [hnear.deriv_eq]
  exact ((hasDerivAt_graphDiffusionCoefficient hp.hasDerivAt).smul hq.hasDerivAt).deriv

end DifferentialGeometry.Analysis.Parabolic
