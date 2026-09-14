import DifferentialGeometry.Analysis.Calculus.Derivative.NormSq
import DifferentialGeometry.Analysis.Calculus.TimeJet.PartialDerivatives
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas

open Filter
open scoped Topology InnerProductSpace ContDiff

namespace DifferentialGeometry.Analysis.Parabolic

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

theorem norm_sq_parabolic_eq {u : ℝ → ℝ → E} {x t a : ℝ}
    (hx : ∀ᶠ y in 𝓝 x, DifferentiableAt ℝ (fun y => u y t) y)
    (hxx : DifferentiableAt ℝ (deriv (fun y => u y t)) x)
    (ht : DifferentiableAt ℝ (fun s => u x s) t) :
    deriv (fun s => ‖u x s‖ ^ 2) t - a * deriv (deriv (fun y => ‖u y t‖ ^ 2)) x =
      2 * ⟪u x t, deriv (fun s => u x s) t - a • deriv (deriv (fun y => u y t)) x⟫_ℝ -
        2 * a * ‖deriv (fun y => u y t) x‖ ^ 2 := by
  rw [ht.hasDerivAt.norm_sq.deriv, deriv_deriv_norm_sq hx hxx,
    inner_sub_right, real_inner_smul_right]
  ring

theorem second_derivative_norm_sq_parabolic_eq {f b : ℝ → ℝ → E} {a : ℝ → ℝ → ℝ}
    {U V : Set ℝ} (hU : IsOpen U) (hV : IsOpen V)
    (hf : ContDiffOn ℝ ∞ (Function.uncurry f) (U ×ˢ V))
    (heq : ∀ x ∈ U, ∀ t ∈ V, deriv (fun s => f x s) t =
      a x t • deriv (deriv (fun y => f y t)) x + b x t)
    {x t : ℝ} (hx : x ∈ U) (ht : t ∈ V)
    (ha : ContDiffAt ℝ 2 (fun y => a y t) x)
    (hb : ContDiffAt ℝ 2 (fun y => b y t) x) :
    let q := fun y s => deriv (deriv (fun z => f z s)) y;
    let r := deriv (fun y => q y t) x;
    deriv (fun s => ‖q x s‖ ^ 2) t - a x t * deriv (deriv (fun y => ‖q y t‖ ^ 2)) x =
      -2 * a x t * ‖r‖ ^ 2 + 4 * deriv (fun y => a y t) x * ⟪q x t, r⟫_ℝ +
        2 * deriv (deriv (fun y => a y t)) x * ‖q x t‖ ^ 2 +
          2 * ⟪q x t, deriv (deriv (fun y => b y t)) x⟫_ℝ := by
  let q := fun y s => deriv (deriv (fun z => f z s)) y
  have hfat (y : ℝ) (hy : y ∈ U) : ContDiffAt ℝ ∞ (Function.uncurry f) (y, t) :=
    (hf (y, t) ⟨hy, ht⟩).contDiffAt ((hU.prod hV).mem_nhds ⟨hy, ht⟩)
  have hqat (y : ℝ) (hy : y ∈ U) : ContDiffAt ℝ ∞ (Function.uncurry q) (y, t) :=
    contDiffAt_deriv_fst
      (contDiffAt_deriv_fst (m := ∞) (hfat y hy) (by simp)) (by simp)
  have hqs (y : ℝ) (hy : y ∈ U) : ContDiffAt ℝ ∞ (fun z => q z t) y :=
    (hqat y hy).comp y (contDiffAt_id.prodMk contDiffAt_const)
  have hqe : ∀ᶠ y in 𝓝 x, DifferentiableAt ℝ (fun z => q z t) y := by
    filter_upwards [hU.mem_nhds hx] with y hy
    exact (hqs y hy).differentiableAt (by simp)
  have hqxx : DifferentiableAt ℝ (deriv (fun y => q y t)) x :=
    ((hqs x hx).derivWithin (m := ∞) (by simp)).differentiableAt (by simp)
  have hqt : DifferentiableAt ℝ (fun s => q x s) t :=
    ((hqat x hx).comp t (contDiffAt_const.prodMk contDiffAt_id)).differentiableAt (by simp)
  have hq2 : ContDiffAt ℝ 2 (fun y => q y t) x :=
    (hqs x hx).of_le (by exact WithTop.coe_le_coe.mpr le_top)
  have hprod := iteratedDerivWithin_smul (n := 2) (Set.mem_univ x) uniqueDiffOn_univ
    ha.contDiffWithinAt hq2.contDiffWithinAt
  have hadd := iteratedDerivWithin_fun_add (n := 2) (Set.mem_univ x) uniqueDiffOn_univ
    (ha.smul hq2).contDiffWithinAt hb.contDiffWithinAt
  simp only [iteratedDerivWithin_univ] at hprod hadd
  norm_num [Finset.sum_range_succ, iteratedDeriv_succ, iteratedDeriv_zero] at hprod hadd
  have hpeq : (fun y => deriv (fun s => f y s) t) =ᶠ[𝓝 x]
      (fun y => a y t • q y t + b y t) := by
    filter_upwards [hU.mem_nhds hx] with y hy
    exact heq y hy t ht
  have hcomm : deriv (fun s => q x s) t =
      deriv (deriv (fun y => a y t • q y t + b y t)) x :=
    (deriv_deriv_deriv_time_comm hU hV hf hx ht).trans hpeq.deriv.deriv_eq
  change deriv (fun s => ‖q x s‖ ^ 2) t - a x t *
    deriv (deriv (fun y => ‖q y t‖ ^ 2)) x = _
  rw [norm_sq_parabolic_eq hqe hqxx hqt, hcomm]
  change deriv (deriv (fun y => a y t • q y t + b y t)) x =
    deriv (deriv (fun y => a y t • q y t)) x + deriv (deriv (fun y => b y t)) x at hadd
  change deriv (deriv (fun y => a y t • q y t)) x = _ at hprod
  rw [hadd, hprod]
  simp only [inner_sub_right, inner_add_right, real_inner_smul_right,
    real_inner_self_eq_norm_sq, two_smul]
  ring


end DifferentialGeometry.Analysis.Parabolic
