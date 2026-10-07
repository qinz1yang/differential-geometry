import DifferentialGeometry.Analysis.Calculus.Cutoff.IntervalCutoffEstimate
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Topology.Algebra.InfiniteSum.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Tactic.Ring

set_option autoImplicit false

noncomputable section

open Set Filter Topology
open scoped ContDiff

namespace DifferentialGeometry.Analysis

/-- A single derivative constant suffices to interpolate monotone heights at any
strictly increasing cofinal sequence of real knots. The interpolation is constant
on a neighborhood of each knot. -/
theorem exists_uniform_smooth_monotone_interpolation :
    ∃ D : ℝ, 0 < D ∧ ∀ (a b : ℕ → ℝ),
      StrictMono a → Tendsto a atTop atTop → Monotone b →
      ∃ f : ℝ → ℝ, ContDiff ℝ ∞ f ∧ Monotone f ∧
        (∀ n, f =ᶠ[𝓝 (a n)] fun _ => b n) ∧
        (∀ x, x ≤ a 0 → f x = b 0) ∧
        ∀ n x, x ∈ Icc (a n) (a (n + 1)) →
          |deriv f x| ≤ D * ((b (n + 1) - b n) / (a (n + 1) - a n)) := by
  classical
  obtain ⟨C, hC, hstep⟩ := exists_uniform_smooth_interval_step
  refine ⟨3 * C, by linarith, ?_⟩
  intro a b ha hato hb
  let l : ℕ → ℝ := fun n => a n + (a (n + 1) - a n) / 3
  let r : ℕ → ℝ := fun n => a n + 2 * (a (n + 1) - a n) / 3
  have hal (n : ℕ) : a n < l n := by
    dsimp only [l]
    linarith [ha (Nat.lt_succ_self n)]
  have hra (n : ℕ) : r n < a (n + 1) := by
    dsimp only [r]
    linarith [ha (Nat.lt_succ_self n)]
  have hlr (n : ℕ) : l n < r n := by
    dsimp only [l, r]
    linarith [ha (Nat.lt_succ_self n)]
  have hlmono : Monotone l := by
    intro m n hmn
    dsimp only [l]
    linarith [ha.monotone hmn, ha.monotone (Nat.succ_le_succ hmn)]
  have hrmono : Monotone r := by
    intro m n hmn
    dsimp only [r]
    linarith [ha.monotone hmn, ha.monotone (Nat.succ_le_succ hmn)]
  choose β hβsmooth hβmono _hβrange hβzero hβone hβderiv using
    fun n : ℕ => hstep (l n) (r n) (hlr n)
  let f : ℝ → ℝ := fun x => b 0 + ∑' n, (b (n + 1) - b n) * β n x
  have hsum (N : ℕ) (x : ℝ) (hx : x ≤ l N) :
      f x = b 0 + ∑ n ∈ Finset.range N, (b (n + 1) - b n) * β n x := by
    dsimp only [f]
    rw [tsum_eq_sum (s := Finset.range N)]
    intro n hn
    have hNn : N ≤ n := Nat.le_of_not_gt (by simpa only [Finset.mem_range] using hn)
    rw [hβzero n x (hx.trans (hlmono hNn)), mul_zero]
  have hlocal (x : ℝ) : ∃ N : ℕ,
      f =ᶠ[𝓝 x] fun y => b 0 + ∑ n ∈ Finset.range N, (b (n + 1) - b n) * β n y := by
    obtain ⟨N, hN⟩ := (hato.eventually (eventually_gt_atTop x)).exists
    refine ⟨N, ?_⟩
    filter_upwards [Iio_mem_nhds (hN.trans (hal N))] with y hy
    exact hsum N y hy.le
  have hsmooth : ContDiff ℝ ∞ f := by
    rw [contDiff_iff_contDiffAt]
    intro x
    obtain ⟨N, hN⟩ := hlocal x
    have hs : ContDiff ℝ ∞
        (fun y => b 0 + ∑ n ∈ Finset.range N, (b (n + 1) - b n) * β n y) :=
      contDiff_const.add (ContDiff.sum fun n _ => contDiff_const.mul (hβsmooth n))
    exact hs.contDiffAt.congr_of_eventuallyEq hN
  have hmono : Monotone f := by
    intro x y hxy
    obtain ⟨N, hN⟩ := (hato.eventually (eventually_gt_atTop y)).exists
    have hy : y ≤ l N := (hN.trans (hal N)).le
    rw [hsum N x (hxy.trans hy), hsum N y hy]
    exact add_le_add le_rfl (Finset.sum_le_sum fun n _ =>
      mul_le_mul_of_nonneg_left (hβmono n hxy)
        (sub_nonneg.mpr (hb (Nat.le_succ n))))
  have hflat (n : ℕ) : f =ᶠ[𝓝 (a n)] fun _ => b n := by
    cases n with
    | zero =>
      filter_upwards [Iio_mem_nhds (hal 0)] with x hx
      rw [hsum 0 x hx.le]
      simp
    | succ n =>
      filter_upwards [Ioo_mem_nhds (hra n) (hal (n + 1))] with x hx
      rw [hsum (n + 1) x hx.2.le]
      have hterms :
          (∑ j ∈ Finset.range (n + 1), (b (j + 1) - b j) * β j x) =
            ∑ j ∈ Finset.range (n + 1), (b (j + 1) - b j) := by
        apply Finset.sum_congr rfl
        intro j hj
        have hjn : j ≤ n := Nat.le_of_lt_succ (Finset.mem_range.mp hj)
        rw [hβone j x ((hrmono hjn).trans hx.1.le), mul_one]
      rw [hterms, Finset.sum_range_sub]
      ring
  refine ⟨f, hsmooth, hmono, hflat, ?_, ?_⟩
  · intro x hx
    rw [hsum 0 x (hx.trans (hal 0).le)]
    simp
  · intro n x hx
    have hprior : ∀ᶠ y in 𝓝 x, ∀ j ∈ Finset.range n, β j y = 1 := by
      rw [eventually_all_finset]
      intro j hj
      have hjn : j + 1 ≤ n := Nat.succ_le_of_lt (Finset.mem_range.mp hj)
      have hrjx : r j < x := (hra j).trans_le ((ha.monotone hjn).trans hx.1)
      filter_upwards [Ioi_mem_nhds hrjx] with y hy
      exact hβone j y hy.le
    have hformula : f =ᶠ[𝓝 x] fun y => b n + (b (n + 1) - b n) * β n y := by
      filter_upwards [Iio_mem_nhds (hx.2.trans_lt (hal (n + 1))), hprior] with y hy hp
      rw [hsum (n + 1) y hy.le, Finset.sum_range_succ]
      have hterms : (∑ j ∈ Finset.range n, (b (j + 1) - b j) * β j y) = b n - b 0 := by
        calc
          _ = ∑ j ∈ Finset.range n, (b (j + 1) - b j) := by
            apply Finset.sum_congr rfl
            intro j hj
            rw [hp j hj, mul_one]
          _ = b n - b 0 := Finset.sum_range_sub b n
      rw [hterms]
      ring
    rw [hformula.deriv_eq, deriv_const_add, deriv_const_mul_field, abs_mul,
      abs_of_nonneg (sub_nonneg.mpr (hb (Nat.le_succ n)))]
    calc
      _ ≤ (b (n + 1) - b n) * (C / (r n - l n)) :=
        mul_le_mul_of_nonneg_left (hβderiv n x) (sub_nonneg.mpr (hb (Nat.le_succ n)))
      _ = 3 * C * ((b (n + 1) - b n) / (a (n + 1) - a n)) := by
        have hwidth : r n - l n = (a (n + 1) - a n) / 3 := by
          dsimp only [r, l]
          ring
        rw [hwidth, div_div_eq_mul_div]
        ring

/-- A point beyond a specified knot belongs to a later consecutive interval of
a nondecreasing cofinal sequence of real knots. -/
theorem exists_mem_Ico_of_tendsto_atTop {a : ℕ → ℝ} (ha : Monotone a)
    (hato : Tendsto a atTop atTop) (N : ℕ) {x : ℝ} (hx : a N ≤ x) :
    ∃ n : ℕ, N ≤ n ∧ x ∈ Ico (a n) (a (n + 1)) := by
  have hex : ∃ k : ℕ, x < a k := (hato.eventually (eventually_gt_atTop x)).exists
  have hk0 : Nat.find hex ≠ 0 := by
    intro hk0
    have hk := Nat.find_spec hex
    rw [hk0] at hk
    exact (not_lt_of_ge ((ha (Nat.zero_le N)).trans hx)) hk
  obtain ⟨n, hn⟩ := Nat.exists_eq_succ_of_ne_zero hk0
  have hnx : a n ≤ x := by
    apply le_of_not_gt
    apply Nat.find_min hex
    rw [hn]
    exact Nat.lt_succ_self n
  have hxn : x < a (n + 1) := by
    simpa only [hn] using Nat.find_spec hex
  have hNn : N ≤ n := by
    by_contra hNn
    have hnN : n + 1 ≤ N := Nat.succ_le_of_lt (Nat.lt_of_not_ge hNn)
    exact (not_lt_of_ge ((ha hnN).trans hx)) hxn
  exact ⟨n, hNn, hnx, hxn⟩

/-- Bounds tending to zero on all sufficiently late consecutive knot intervals
force the function itself to tend to zero. -/
theorem tendsto_zero_of_eventual_interval_bounds {a : ℕ → ℝ} (ha : Monotone a)
    (hato : Tendsto a atTop atTop) {u : ℕ → ℝ} (hu : Tendsto u atTop (𝓝 0))
    {f : ℝ → ℝ}
    (hbound : ∀ᶠ n in atTop, ∀ x, x ∈ Icc (a n) (a (n + 1)) → |f x| ≤ u n) :
    Tendsto f atTop (𝓝 0) := by
  rw [Metric.tendsto_nhds]
  intro ε hε
  obtain ⟨N, hN⟩ := eventually_atTop.mp ((hu.eventually (Iio_mem_nhds hε)).and hbound)
  filter_upwards [eventually_ge_atTop (a N)] with x hx
  obtain ⟨n, hNn, hn⟩ := exists_mem_Ico_of_tendsto_atTop ha hato N hx
  have hfx : |f x| < ε := ((hN n hNn).2 x ⟨hn.1, hn.2.le⟩).trans_lt (hN n hNn).1
  simpa only [dist_zero_right, Real.norm_eq_abs] using hfx

/-- Interpolate the prescribed heights at the same positive times, with plateaus
near the joining times and a vanishing logarithmic speed. The numerical slopes
in logarithmic time, rather than derivatives of an assumed interpolant, are inputs. -/
theorem exists_slow_log_interpolation
    (T b : ℕ → ℝ) (hpos : ∀ n, 0 < T n)
    (hT : StrictMono T) (hTinf : Tendsto T atTop atTop)
    (hb : Monotone b) (hbinf : Tendsto b atTop atTop)
    (hslow : Tendsto
      (fun n => (b (n + 1) - b n) / Real.log (T (n + 1) / T n))
      atTop (𝓝 0)) :
    ∃ S : ℝ → ℝ, ContDiffOn ℝ ∞ S (Ioi 0) ∧
      MonotoneOn S (Ioi 0) ∧ Tendsto S atTop atTop ∧
      Tendsto (fun t => t * |deriv S t|) atTop (𝓝 0) ∧
      (∀ n, S =ᶠ[𝓝 (T n)] fun _ => b n) ∧
      ∀ n, MapsTo S (Icc (T n) (T (n + 1))) (Icc (b n) (b (n + 1))) := by
  let a : ℕ → ℝ := fun n => Real.log (T n)
  have ha : StrictMono a := fun m n hmn => Real.log_lt_log (hpos m) (hT hmn)
  have hato : Tendsto a atTop atTop := Real.tendsto_log_atTop.comp hTinf
  have hratio : Tendsto (fun n => (b (n + 1) - b n) / (a (n + 1) - a n))
      atTop (𝓝 0) := by
    apply hslow.congr
    intro n
    rw [Real.log_div (hpos (n + 1)).ne' (hpos n).ne']
  obtain ⟨D, _hD, hinterp⟩ := exists_uniform_smooth_monotone_interpolation
  obtain ⟨U, hUsmooth, hUmono, hUflat, _, hUbound⟩ := hinterp a b ha hato hb
  have hUvalues (n : ℕ) : U (a n) = b n := (hUflat n).eq_of_nhds
  have hUinf : Tendsto U atTop atTop := by
    have hcomp : Tendsto (U ∘ a) (atTop : Filter ℕ) atTop := by
      simpa only [Function.comp_def, hUvalues] using hbinf
    exact tendsto_atTop_of_monotone_of_subseq hUmono hcomp
  have hUderiv : Tendsto (deriv U) atTop (𝓝 0) := by
    apply tendsto_zero_of_eventual_interval_bounds ha.monotone hato (u := fun n =>
      D * ((b (n + 1) - b n) / (a (n + 1) - a n))) ?_
      (Eventually.of_forall hUbound)
    simpa only [mul_zero] using (tendsto_const_nhds.mul hratio)
  let S : ℝ → ℝ := U ∘ Real.log
  have hlog : ContDiffOn ℝ ∞ Real.log (Ioi 0) :=
    Real.contDiffOn_log.mono fun x hx => by
      simpa only [mem_compl_iff, mem_singleton_iff] using (ne_of_gt hx)
  have hSmono : MonotoneOn S (Ioi 0) := by
    intro x hx y _hy hxy
    exact hUmono (Real.log_le_log hx hxy)
  have hSflat (n : ℕ) : S =ᶠ[𝓝 (T n)] fun _ => b n :=
    (hUflat n).comp_tendsto (Real.continuousAt_log (hpos n).ne')
  refine ⟨S, hUsmooth.comp_contDiffOn hlog, hSmono,
    hUinf.comp Real.tendsto_log_atTop, ?_, hSflat, ?_⟩
  · have heq : (fun t => t * |deriv S t|) =ᶠ[atTop]
        fun t => |deriv U (Real.log t)| := by
      filter_upwards [eventually_gt_atTop (0 : ℝ)] with t ht
      have hd : deriv S t = deriv U (Real.log t) * t⁻¹ :=
        (((hUsmooth.differentiable (by simp)) (Real.log t)).hasDerivAt.comp t
          (Real.hasDerivAt_log ht.ne')).deriv
      rw [hd, abs_mul, abs_inv, abs_of_pos ht]
      calc
        _ = |deriv U (Real.log t)| * (t * t⁻¹) := by ring
        _ = |deriv U (Real.log t)| := by rw [mul_inv_cancel₀ ht.ne', mul_one]
    have habs : Tendsto (fun t => |deriv U (Real.log t)|) atTop (𝓝 0) := by
      simpa only [Function.comp_def, abs_zero] using (hUderiv.comp Real.tendsto_log_atTop).abs
    exact habs.congr' heq.symm
  · intro n t ht
    have htpos : t ∈ Ioi (0 : ℝ) := (hpos n).trans_le ht.1
    constructor
    · rw [← (hSflat n).eq_of_nhds]
      exact hSmono (hpos n) htpos ht.1
    · rw [← (hSflat (n + 1)).eq_of_nhds]
      exact hSmono htpos (hpos (n + 1)) ht.2

end DifferentialGeometry.Analysis
