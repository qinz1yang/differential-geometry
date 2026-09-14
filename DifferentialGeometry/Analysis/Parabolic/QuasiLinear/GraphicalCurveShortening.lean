import DifferentialGeometry.Analysis.Calculus.TimeJet.PartialDerivatives
import DifferentialGeometry.Analysis.Parabolic.Euclidean.VectorNorm
import DifferentialGeometry.Analysis.Parabolic.MaximumPrinciple.Scalar.IntervalReaction
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Positivity

open Filter
open scoped Topology InnerProductSpace ContDiff

namespace DifferentialGeometry.Analysis.Parabolic

variable {E : Type*} [NormedAddCommGroup E]

noncomputable def graphDiffusionCoefficient (p : E) : ℝ := (1 + ‖p‖ ^ 2)⁻¹

theorem graphDiffusionCoefficient_pos (p : E) : 0 < graphDiffusionCoefficient p := by
  unfold graphDiffusionCoefficient
  positivity

theorem graphDiffusionCoefficient_le_one (p : E) : graphDiffusionCoefficient p ≤ 1 := by
  unfold graphDiffusionCoefficient
  exact (inv_le_one₀ (by positivity)).2 (by nlinarith [sq_nonneg ‖p‖])

variable [InnerProductSpace ℝ E]

private theorem graph_reaction_square_bound (p q r : E) {a : ℝ} (ha : 0 ≤ a) :
    -2 * a * ‖r‖ ^ 2 - 8 * a ^ 2 * ⟪p, q⟫_ℝ * ⟪q, r⟫_ℝ -
      4 * a ^ 2 * ‖q‖ ^ 2 * ⟪p, r⟫_ℝ +
      16 * a ^ 3 * ⟪p, q⟫_ℝ ^ 2 * ‖q‖ ^ 2 - 4 * a ^ 2 * ‖q‖ ^ 4 ≤
        -a * ‖r‖ ^ 2 + a ^ 2 * (52 * a * ‖p‖ ^ 2 - 4) * ‖q‖ ^ 4 := by
  have hsquare := mul_nonneg ha (real_inner_self_nonneg (x :=
    r + (4 * a * ⟪p, q⟫_ℝ) • q + (2 * a * ‖q‖ ^ 2) • p))
  simp only [inner_add_left, inner_add_right, real_inner_smul_left, real_inner_smul_right,
    real_inner_self_eq_norm_sq, norm_smul, mul_pow, Real.norm_eq_abs, sq_abs] at hsquare
  have hcs := real_inner_mul_inner_self_le p q
  rw [real_inner_self_eq_norm_sq, real_inner_self_eq_norm_sq] at hcs
  have hscaled := mul_le_mul_of_nonneg_left hcs (by positivity : 0 ≤ 48 * a ^ 3 * ‖q‖ ^ 2)
  simp only [real_inner_comm] at hsquare hscaled ⊢
  linear_combination hscaled + hsquare

theorem graph_second_derivative_reaction_le (p q r : E) (hp : ‖p‖ ≤ 1 / 4) :
    let a := graphDiffusionCoefficient p;
    -2 * a * ‖r‖ ^ 2 - 8 * a ^ 2 * ⟪p, q⟫_ℝ * ⟪q, r⟫_ℝ -
      4 * a ^ 2 * ‖q‖ ^ 2 * ⟪p, r⟫_ℝ +
      16 * a ^ 3 * ⟪p, q⟫_ℝ ^ 2 * ‖q‖ ^ 2 - 4 * a ^ 2 * ‖q‖ ^ 4 ≤
        -(1 / 2 : ℝ) * ‖q‖ ^ 4 := by
  let a := graphDiffusionCoefficient p
  have ha : 0 < a := graphDiffusionCoefficient_pos p
  have ha1 : a ≤ 1 := graphDiffusionCoefficient_le_one p
  have hp2 : ‖p‖ ^ 2 ≤ 1 / 16 := by nlinarith [norm_nonneg p]
  have halower : (16 / 17 : ℝ) ≤ a := by
    dsimp [a, graphDiffusionCoefficient]
    rw [← one_div]
    apply (le_div_iff₀ (by positivity : 0 < 1 + ‖p‖ ^ 2)).2
    nlinarith only [hp2]
  have hneg : 52 * a * ‖p‖ ^ 2 - 4 ≤ -(3 / 4 : ℝ) := by
    have hmul := mul_le_mul_of_nonneg_right ha1 (sq_nonneg ‖p‖)
    nlinarith only [hmul, hp2]
  have hcoef : a ^ 2 * (52 * a * ‖p‖ ^ 2 - 4) ≤ -(1 / 2 : ℝ) := by
    have hmul := mul_le_mul_of_nonneg_left hneg (sq_nonneg a)
    have hasq : (16 / 17 : ℝ) ^ 2 ≤ a ^ 2 := by nlinarith only [halower, sq_nonneg (a - 16 / 17)]
    nlinarith only [hmul, hasq]
  have hbound := graph_reaction_square_bound p q r ha.le
  have hscaled := mul_le_mul_of_nonneg_right hcoef (by positivity : 0 ≤ ‖q‖ ^ 4)
  have hgrad : 0 ≤ a * ‖r‖ ^ 2 := by positivity
  exact hbound.trans (by nlinarith only [hscaled, hgrad])

theorem hasDerivAt_graphDiffusionCoefficient {p : ℝ → E} {q : E} {x : ℝ}
    (hp : HasDerivAt p q x) :
    HasDerivAt (fun y => graphDiffusionCoefficient (p y))
      (-2 * graphDiffusionCoefficient (p x) ^ 2 * ⟪p x, q⟫_ℝ) x := by
  have h := (hp.norm_sq.const_add 1).inv (by positivity : 1 + ‖p x‖ ^ 2 ≠ 0)
  convert h using 1 <;> first | rfl | (simp only [graphDiffusionCoefficient, div_eq_mul_inv, ← inv_pow]; ring)

theorem hasDerivAt_deriv_graphDiffusionCoefficient {p : ℝ → E} {x : ℝ}
    (hp : ∀ᶠ y in 𝓝 x, DifferentiableAt ℝ p y)
    (hp' : DifferentiableAt ℝ (deriv p) x) :
    HasDerivAt (deriv (fun y => graphDiffusionCoefficient (p y)))
      (8 * graphDiffusionCoefficient (p x) ^ 3 * ⟪p x, deriv p x⟫_ℝ ^ 2 -
        2 * graphDiffusionCoefficient (p x) ^ 2 *
          (‖deriv p x‖ ^ 2 + ⟪p x, deriv (deriv p) x⟫_ℝ)) x := by
  have heq : deriv (fun y => graphDiffusionCoefficient (p y)) =ᶠ[𝓝 x]
      fun y => -2 * graphDiffusionCoefficient (p y) ^ 2 * ⟪p y, deriv p y⟫_ℝ := by
    filter_upwards [hp] with y hy
    exact (hasDerivAt_graphDiffusionCoefficient hy.hasDerivAt).deriv
  have ha := hasDerivAt_graphDiffusionCoefficient hp.self_of_nhds.hasDerivAt
  have hi := hp.self_of_nhds.hasDerivAt.inner ℝ hp'.hasDerivAt
  have hd := (((ha.pow 2).const_mul (-2)).mul hi).congr_of_eventuallyEq heq
  rw [real_inner_self_eq_norm_sq] at hd
  simp only [Pi.pow_apply] at hd
  convert hd using 1 <;> first | rfl | ring

theorem graph_second_derivative_norm_sq_parabolic_eq {f : ℝ → ℝ → E} {U V : Set ℝ}
    (hU : IsOpen U) (hV : IsOpen V)
    (hf : ContDiffOn ℝ ∞ (Function.uncurry f) (U ×ˢ V))
    (heq : ∀ x ∈ U, ∀ t ∈ V, deriv (fun s => f x s) t =
      graphDiffusionCoefficient (deriv (fun y => f y t) x) •
        deriv (deriv (fun y => f y t)) x)
    {x t : ℝ} (hx : x ∈ U) (ht : t ∈ V) :
    let p := fun y s => deriv (fun z => f z s) y;
    let q := fun y s => deriv (fun z => p z s) y;
    let r := deriv (fun y => q y t) x;
    let a := graphDiffusionCoefficient (p x t);
    deriv (fun s => ‖q x s‖ ^ 2) t - a * deriv (deriv (fun y => ‖q y t‖ ^ 2)) x =
      -2 * a * ‖r‖ ^ 2 - 8 * a ^ 2 * ⟪p x t, q x t⟫_ℝ * ⟪q x t, r⟫_ℝ -
        4 * a ^ 2 * ‖q x t‖ ^ 2 * ⟪p x t, r⟫_ℝ +
        16 * a ^ 3 * ⟪p x t, q x t⟫_ℝ ^ 2 * ‖q x t‖ ^ 2 -
          4 * a ^ 2 * ‖q x t‖ ^ 4 := by
  let p := fun y s => deriv (fun z => f z s) y
  let q := fun y s => deriv (fun z => p z s) y
  let a := fun y => graphDiffusionCoefficient (p y t)
  have hfat (y : ℝ) (hy : y ∈ U) : ContDiffAt ℝ ∞ (Function.uncurry f) (y, t) :=
    (hf (y, t) ⟨hy, ht⟩).contDiffAt ((hU.prod hV).mem_nhds ⟨hy, ht⟩)
  have hpat (y : ℝ) (hy : y ∈ U) : ContDiffAt ℝ ∞ (Function.uncurry p) (y, t) :=
    contDiffAt_deriv_fst (hfat y hy) (by simp)
  have hqat (y : ℝ) (hy : y ∈ U) : ContDiffAt ℝ ∞ (Function.uncurry q) (y, t) :=
    contDiffAt_deriv_fst (hpat y hy) (by simp)
  have hps (y : ℝ) (hy : y ∈ U) : ContDiffAt ℝ ∞ (fun z => p z t) y :=
    (hpat y hy).comp y (contDiffAt_id.prodMk contDiffAt_const)
  have hqs (y : ℝ) (hy : y ∈ U) : ContDiffAt ℝ ∞ (fun z => q z t) y :=
    (hqat y hy).comp y (contDiffAt_id.prodMk contDiffAt_const)
  have hpe : ∀ᶠ y in 𝓝 x, DifferentiableAt ℝ (fun z => p z t) y := by
    filter_upwards [hU.mem_nhds hx] with y hy
    exact (hps y hy).differentiableAt (by simp)
  have hacd : ContDiffAt ℝ ∞ a x :=
    (contDiffAt_const.add ((hps x hx).norm_sq ℝ)).inv (by positivity : 1 + ‖p x t‖ ^ 2 ≠ 0)
  have hnorm := second_derivative_norm_sq_parabolic_eq (b := fun _ _ => (0 : E))
    (a := fun y s => graphDiffusionCoefficient (p y s)) hU hV hf
    (fun y hy s hs => by simpa only [add_zero] using heq y hy s hs) hx ht
    (hacd.of_le (by exact WithTop.coe_le_coe.mpr le_top)) contDiffAt_const
  have ha' := (hasDerivAt_graphDiffusionCoefficient hpe.self_of_nhds.hasDerivAt).deriv
  have ha'' := (hasDerivAt_deriv_graphDiffusionCoefficient hpe
    ((hqs x hx).differentiableAt (by simp))).deriv
  change deriv (fun s => ‖q x s‖ ^ 2) t - a x *
    deriv (deriv (fun y => ‖q y t‖ ^ 2)) x = _
  rw [hnorm]
  change deriv a x = -2 * a x ^ 2 * ⟪p x t, q x t⟫_ℝ at ha'
  change deriv (deriv a) x = 8 * a x ^ 3 * ⟪p x t, q x t⟫_ℝ ^ 2 -
    2 * a x ^ 2 * (‖q x t‖ ^ 2 + ⟪p x t, deriv (fun y => q y t) x⟫_ℝ) at ha''
  rw [ha', ha'']
  simp only [deriv_const', deriv_const, inner_zero_right, add_zero, mul_zero]
  dsimp [a, p, q]
  ring

theorem graph_second_derivative_norm_sq_parabolic_le {f : ℝ → ℝ → E} {U V : Set ℝ}
    (hU : IsOpen U) (hV : IsOpen V)
    (hf : ContDiffOn ℝ ∞ (Function.uncurry f) (U ×ˢ V))
    (heq : ∀ x ∈ U, ∀ t ∈ V, deriv (fun s => f x s) t =
      graphDiffusionCoefficient (deriv (fun y => f y t) x) •
        deriv (deriv (fun y => f y t)) x)
    {x t : ℝ} (hx : x ∈ U) (ht : t ∈ V)
    (hp : ‖deriv (fun y => f y t) x‖ ≤ 1 / 4) :
    let q := fun y s => deriv (deriv (fun z => f z s)) y;
    deriv (fun s => ‖q x s‖ ^ 2) t -
      graphDiffusionCoefficient (deriv (fun y => f y t) x) *
        deriv (deriv (fun y => ‖q y t‖ ^ 2)) x ≤ -(1 / 2 : ℝ) * (‖q x t‖ ^ 2) ^ 2 := by
  dsimp only
  rw [graph_second_derivative_norm_sq_parabolic_eq hU hV hf heq hx ht]
  simpa only [← pow_mul] using
    graph_second_derivative_reaction_le (deriv (fun y => f y t) x)
      (deriv (deriv (fun y => f y t)) x)
      (deriv (deriv (deriv (fun y => f y t))) x) hp

theorem graph_second_derivative_interior_bound_on_closed_time_interval {f : ℝ → ℝ → E} {R T : ℝ}
    (hR : 0 < R)
    (hf : ContDiffOn ℝ ∞ (Function.uncurry f) (Set.Ioo (-R) R ×ˢ Set.Ioo 0 T))
    (hcont : ContinuousOn
      (fun p : ℝ × ℝ => ‖deriv (deriv (fun y => f y p.2)) p.1‖ ^ 2)
      (Set.Icc (-R) R ×ˢ Set.Icc 0 T))
    (heq : ∀ x ∈ Set.Ioo (-R) R, ∀ t ∈ Set.Ioo 0 T,
      deriv (fun s => f x s) t = graphDiffusionCoefficient (deriv (fun y => f y t) x) •
        deriv (deriv (fun y => f y t)) x)
    (hp : ∀ x ∈ Set.Ioo (-R) R, ∀ t ∈ Set.Ioo 0 T,
      ‖deriv (fun y => f y t) x‖ ≤ 1 / 4) :
    ∀ t ∈ Set.Ioc 0 T, ∀ x ∈ Set.Icc (-R / 2) (R / 2),
      ‖deriv (deriv (fun y => f y t)) x‖ ^ 2 ≤ 32 / (9 * t) + 128 / R ^ 2 := by
  let u := fun x t => ‖deriv (deriv (fun y => f y t)) x‖ ^ 2
  let a := fun x t => graphDiffusionCoefficient (deriv (fun y => f y t) x)
  have huat (x : ℝ) (hx : x ∈ Set.Ioo (-R) R) (t : ℝ) (ht : t ∈ Set.Ioo 0 T) :
      ContDiffAt ℝ ∞ (Function.uncurry u) (x, t) := by
    have hfat := (hf (x, t) ⟨hx, ht⟩).contDiffAt
      ((isOpen_Ioo.prod isOpen_Ioo).mem_nhds ⟨hx, ht⟩)
    exact (contDiffAt_deriv_fst (m := ∞)
      (contDiffAt_deriv_fst (m := ∞) hfat (by simp)) (by simp)).norm_sq ℝ
  have hux (x : ℝ) (hx : x ∈ Set.Ioo (-R) R) (t : ℝ) (ht : t ∈ Set.Ioo 0 T) :
      ContDiffAt ℝ ∞ (fun y => u y t) x :=
    (huat x hx t ht).comp x (contDiffAt_id.prodMk contDiffAt_const)
  have hbound := quadratic_reaction_interior_upper_bound_on_closed_time_interval (u := u) (a := a)
    hR (by norm_num : 0 < (1 / 2 : ℝ)) (by norm_num : 0 ≤ (1 : ℝ)) hcont
    (fun t ht x hx => ((hux x hx t ht).differentiableAt (by simp)).differentiableWithinAt)
    (fun t ht x hx => (((hux x hx t ht).derivWithin (m := ∞) (by simp)).differentiableAt
      (by simp)).differentiableWithinAt)
    (fun x hx t ht => ((huat x hx t ht).comp t
      (contDiffAt_const.prodMk contDiffAt_id)).differentiableAt (by simp))
    (fun x _ t _ => ⟨(graphDiffusionCoefficient_pos _).le, graphDiffusionCoefficient_le_one _⟩)
    (fun x hx t ht => graph_second_derivative_norm_sq_parabolic_le
      isOpen_Ioo isOpen_Ioo hf heq hx ht (hp x hx t ht))
  intro t ht x hx
  convert hbound t ht x hx using 1
  field_simp
  ring

theorem graph_second_derivative_interior_bound {f : ℝ → ℝ → E} {R T : ℝ}
    (hR : 0 < R)
    (hf : ContDiffOn ℝ ∞ (Function.uncurry f) (Set.Ioo (-R) R ×ˢ Set.Ioo 0 T))
    (hcont : ContinuousOn
      (fun p : ℝ × ℝ => ‖deriv (deriv (fun y => f y p.2)) p.1‖ ^ 2)
      (Set.Icc (-R) R ×ˢ Set.Ico 0 T))
    (heq : ∀ x ∈ Set.Ioo (-R) R, ∀ t ∈ Set.Ioo 0 T,
      deriv (fun s => f x s) t = graphDiffusionCoefficient (deriv (fun y => f y t) x) •
        deriv (deriv (fun y => f y t)) x)
    (hp : ∀ x ∈ Set.Ioo (-R) R, ∀ t ∈ Set.Ioo 0 T,
      ‖deriv (fun y => f y t) x‖ ≤ 1 / 4) :
    ∀ t ∈ Set.Ioo 0 T, ∀ x ∈ Set.Icc (-R / 2) (R / 2),
      ‖deriv (deriv (fun y => f y t)) x‖ ^ 2 ≤ 32 / (9 * t) + 128 / R ^ 2 := by
  intro t ht x hx
  have htime : Set.Ioo 0 t ⊆ Set.Ioo 0 T :=
    fun s hs => ⟨hs.1, hs.2.trans ht.2⟩
  have hbound := graph_second_derivative_interior_bound_on_closed_time_interval
    hR (hf.mono (fun p hp => ⟨hp.1, htime hp.2⟩))
    (hcont.mono (fun p hp => ⟨hp.1, hp.2.1, hp.2.2.trans_lt ht.2⟩))
    (fun y hy s hs => heq y hy s (htime hs))
    (fun y hy s hs => hp y hy s (htime hs))
  exact hbound t ⟨ht.1, le_rfl⟩ x hx

end DifferentialGeometry.Analysis.Parabolic
