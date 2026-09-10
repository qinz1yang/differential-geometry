import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
import Mathlib.Analysis.Calculus.Deriv.Support
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Normed.Group.Bounded
import Mathlib.Geometry.Manifold.ContMDiff.NormedSpace
import Mathlib.Geometry.Manifold.Diffeomorph

open Set Function Manifold
open scoped Topology ContDiff
set_option autoImplicit false
noncomputable section
namespace Poincare.Manifold.Diffeomorph

theorem exists_compact_translation {r : ℝ} (hr : 0 < r) :
    ∃ a : ℝ, 0 < a ∧ a < r ∧
      ∃ d : Diffeomorph 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) ℝ ℝ ∞,
        StrictMono d ∧
        (∀ x ∈ Icc (-r) r, d x = x + a) ∧
        (∀ x, 2 * r ≤ |x| → d x = x) ∧
        (∀ x, 0 < deriv d x) ∧ HasCompactSupport (fun x => d x - x) := by
  let b : ContDiffBump (0 : ℝ) := ⟨r, 2 * r, hr, by linarith⟩
  have hb : ContDiff ℝ ∞ b := b.contDiff
  obtain ⟨C, hC⟩ := b.hasCompactSupport.deriv.exists_bound_of_continuous
    (hb.continuous_deriv (by norm_num))
  have hC0 : 0 ≤ C := (norm_nonneg _).trans (hC 0)
  let a := min (r / 2) (1 / (2 * (C + 1)))
  have ha : 0 < a := lt_min (by positivity) (by positivity)
  have har : a < r := (min_le_left _ _).trans_lt (by linarith)
  have haC : a * C < 1 := by
    have hh : a * (2 * (C + 1)) ≤ 1 :=
      (le_div_iff₀ (by positivity : 0 < 2 * (C + 1))).mp (min_le_right _ _)
    nlinarith
  let f : ℝ → ℝ := fun x => x + a * b x
  have hf : ContDiff ℝ ∞ f := contDiff_id.add (contDiff_const.mul hb)
  have hD (x : ℝ) : HasDerivAt f (1 + a * deriv b x) x :=
    (hasDerivAt_id x).add ((hb.differentiable (by norm_num) x).hasDerivAt.const_mul a)
  have hDpos (x : ℝ) : 0 < 1 + a * deriv b x := by
    have hh := (abs_le.mp (show |deriv b x| ≤ C from hC x)).1
    have hm := mul_le_mul_of_nonneg_left hh ha.le
    nlinarith
  have hmono : StrictMono f := strictMono_of_deriv_pos (fun x => by rw [(hD x).deriv]; exact hDpos x)
  have hfix (x : ℝ) (hx : 2 * r ≤ |x|) : f x = x := by
    have hh : b x = 0 := b.zero_of_le_dist (by simpa [b, Real.dist_eq] using hx)
    simp [f, hh]
  have hsurj : Surjective f := by
    intro y
    let R := max (2 * r) |y|
    have hR : 0 ≤ R := le_trans (by positivity : 0 ≤ 2 * r) (le_max_left _ _)
    have hL : f (-R) = -R := hfix _ (by rw [abs_neg, abs_of_nonneg hR]; exact le_max_left _ _)
    have hU : f R = R := hfix _ (by rw [abs_of_nonneg hR]; exact le_max_left _ _)
    have hy : y ∈ Icc (f (-R)) (f R) := by
      rw [hL, hU]
      exact ⟨le_trans (neg_le_neg (le_max_right _ _)) (neg_abs_le y),
        le_trans (le_abs_self y) (le_max_right _ _)⟩
    obtain ⟨x, _, hx⟩ := intermediate_value_Icc (by linarith : -R ≤ R) hf.continuous.continuousOn hy
    exact ⟨x, hx⟩
  let e : ℝ ≃ₜ ℝ := (hmono.orderIsoOfSurjective f hsurj).toHomeomorph
  have he : (e : ℝ → ℝ) = f := rfl
  have heinv : ContDiff ℝ ∞ e.symm :=
    e.contDiff_symm_deriv (fun x => (hDpos x).ne') (by simpa only [he] using hD) (by simpa only [he] using hf)
  let d : Diffeomorph 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) ℝ ℝ ∞ :=
    ⟨e.toEquiv, (by exact hf.contMDiff), heinv.contMDiff⟩
  refine ⟨a, ha, har, d, hmono, ?_, hfix, ?_, ?_⟩
  · intro x hx
    have hh : b x = 1 := b.one_of_mem_closedBall (by
      simpa [Metric.mem_closedBall, Real.dist_eq, b, abs_le] using hx)
    change f x = x + a
    simp [f, hh]
  · intro x
    change 0 < deriv f x
    rw [(hD x).deriv]
    exact hDpos x
  · have hh : (fun x => d x - x) = fun x => a * b x := by funext x; change f x - x = _; dsimp [f]; ring
    rw [hh]
    exact b.hasCompactSupport.mul_left

end Poincare.Manifold.Diffeomorph
