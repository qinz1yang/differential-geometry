import DifferentialGeometry.Analysis.Elliptic.Euclidean.MaximumPrinciple
import DifferentialGeometry.Analysis.Elliptic.ComplexPlane.LogarithmicPotential.FundamentalSolution
import Mathlib.Analysis.Calculus.LocalExtr.Basic

set_option autoImplicit false
noncomputable section

open Set Filter Metric InnerProductSpace
open scoped Topology ContDiff

namespace DifferentialGeometry.Analysis

/-- A subharmonic function negative on the inner circle and nonpositive on the
outer circle has positive outward radial derivative at an outer zero. -/
theorem annulus_hopf_radial
    {q : ℂ → ℝ} {r : ℝ} (hr : 0 < r) (hr1 : r < 1)
    (hq : ∀ z ∈ closedBall (0 : ℂ) 1 ∩ (ball (0 : ℂ) r)ᶜ,
      ContDiffAt ℝ 2 q z)
    (hΔ : ∀ z ∈ interior (closedBall (0 : ℂ) 1 ∩ (ball (0 : ℂ) r)ᶜ),
      0 ≤ Laplacian.laplacian q z)
    (hinner : ∀ z ∈ sphere (0 : ℂ) r, q z < 0)
    (houter : ∀ z ∈ sphere (0 : ℂ) 1, q z ≤ 0)
    {p : ℂ} (hp : p ∈ sphere (0 : ℂ) 1) (hqp : q p = 0) :
    0 < fderiv ℝ q p p := by
  let K := closedBall (0 : ℂ) 1 ∩ (ball (0 : ℂ) r)ᶜ
  have hKclosed : IsClosed K := isClosed_closedBall.inter isOpen_ball.isClosed_compl
  have hK : IsCompact K := (isCompact_closedBall (0 : ℂ) 1).inter_right
    isOpen_ball.isClosed_compl
  have hnormp : ‖p‖ = 1 := mem_sphere_zero_iff_norm.mp hp
  have hpK : p ∈ K := by
    constructor
    · exact mem_closedBall_zero_iff.mpr hnormp.le
    · change ¬ p ∈ ball (0 : ℂ) r
      rw [mem_ball_zero_iff, hnormp]
      exact not_lt_of_ge hr1.le
  have hinnerK : sphere (0 : ℂ) r ⊆ K := by
    intro z hz
    have hn : ‖z‖ = r := mem_sphere_zero_iff_norm.mp hz
    constructor
    · exact mem_closedBall_zero_iff.mpr (hn.trans_le hr1.le)
    · change ¬ z ∈ ball (0 : ℂ) r
      rw [mem_ball_zero_iff, hn]
      exact lt_irrefl r
  have hqc : ContinuousOn q K := fun z hz =>
    (hq z hz).continuousAt.continuousWithinAt
  obtain ⟨z₀, hz₀, hzmax⟩ := (isCompact_sphere (0 : ℂ) r).exists_isMaxOn
    (NormedSpace.sphere_nonempty.mpr hr.le) (hqc.mono hinnerK)
  have hm : q z₀ < 0 := hinner z₀ hz₀
  have hlog : Real.log r < 0 := Real.log_neg hr hr1
  let c := q z₀ / Real.log r
  have hc : 0 < c := div_pos_of_neg_of_neg hm hlog
  have hcoeff : c * Real.log r = q z₀ := div_mul_cancel₀ _ hlog.ne
  let B : ℂ → ℝ := fun z => c * Real.log ‖z‖
  have hzne (z : ℂ) (hz : z ∈ K) : z ≠ 0 := by
    have hznot : ¬ z ∈ ball (0 : ℂ) r := hz.2
    rw [mem_ball_zero_iff] at hznot
    have hn : r ≤ ‖z‖ := not_lt.mp hznot
    exact norm_ne_zero_iff.mp (ne_of_gt (hr.trans_le hn))
  have hB (z : ℂ) (hz : z ∈ K) : HarmonicAt B z :=
    (harmonicAt_log_norm_complex (hzne z hz)).const_smul (c := c)
  have hBc : ContinuousOn B K := fun z hz =>
    (hB z hz).1.continuousAt.continuousWithinAt
  have hfront (z : ℂ) (hz : z ∈ frontier K) :
      z ∈ sphere (0 : ℂ) 1 ∨ z ∈ sphere (0 : ℂ) r := by
    rcases frontier_inter_subset (closedBall (0 : ℂ) 1) (ball (0 : ℂ) r)ᶜ hz with h | h
    · exact Or.inl (by simpa only [frontier_closedBall (0 : ℂ) one_ne_zero] using h.1)
    · exact Or.inr (by simpa only [frontier_compl, frontier_ball (0 : ℂ) hr.ne'] using h.2)
  have hcmp : ∀ z ∈ K, q z - B z ≤ 0 := by
    have hh := le_of_laplacian_nonneg_of_le_frontier (s := K) (f := q - B) (C := 0)
      (by simpa only [hKclosed.closure_eq] using hK)
      (by simpa only [hKclosed.closure_eq] using (hqc.sub hBc).upperSemicontinuousOn)
      (fun z hz => (hq z (interior_subset hz)).sub (hB z (interior_subset hz)).1)
      (fun z hz => by
        rw [(hq z (interior_subset hz)).laplacian_sub (hB z (interior_subset hz)).1,
          (hB z (interior_subset hz)).2.self_of_nhds]
        change 0 ≤ Laplacian.laplacian q z - 0
        simpa only [sub_zero] using hΔ z hz)
      (fun z hz => by
        change q z - B z ≤ 0
        apply sub_nonpos.mpr
        rcases hfront z hz with ho | hi
        · have hn := mem_sphere_zero_iff_norm.mp ho
          simpa only [B, hn, Real.log_one, mul_zero] using houter z ho
        · have hn := mem_sphere_zero_iff_norm.mp hi
          have hmaxi : q z ≤ q z₀ := hzmax hi
          simpa only [B, hn, hcoeff] using hmaxi)
    intro z hz
    exact hh z (subset_closure hz)
  have hvalue : q p - B p = 0 := by simp only [hqp, B, hnormp, Real.log_one, mul_zero, sub_self]
  have hmax : IsMaxOn (q - B) K p := by
    intro z hz
    change q z - B z ≤ q p - B p
    rw [hvalue]
    exact hcmp z hz
  have hdir : -p ∈ posTangentConeAt K p := by
    apply mem_posTangentConeAt_of_frequently_mem
    have hh : ∀ᶠ t : ℝ in 𝓝[>] 0, p + t • (-p) ∈ K := by
      filter_upwards [self_mem_nhdsWithin,
        mem_nhdsWithin_of_mem_nhds
          (isOpen_Iio.mem_nhds (show (0 : ℝ) < 1 - r by linarith))] with t ht htR
      change 0 < t at ht
      change t < 1 - r at htR
      have ht1 : t < 1 := by linarith
      have hn : ‖p + t • (-p)‖ = 1 - t := by
        rw [show p + t • (-p) = (1 - t) • p by
            rw [sub_smul, one_smul, smul_neg, sub_eq_add_neg],
          norm_smul, Real.norm_eq_abs, abs_of_pos (sub_pos.mpr ht1), hnormp, mul_one]
      constructor
      · exact mem_closedBall_zero_iff.mpr (by rw [hn]; linarith)
      · change ¬ p + t • (-p) ∈ ball (0 : ℂ) r
        rw [mem_ball_zero_iff, hn]
        exact not_lt_of_ge (by linarith)
    exact hh.frequently
  have hder := ((hq p hpK).differentiableAt (by norm_num)).hasFDerivAt.sub
    ((hasFDerivAt_log_norm_complex (hzne p hpK)).const_mul c)
  have hnon := hmax.isLocalMaxOn.hasFDerivWithinAt_nonpos hder.hasFDerivWithinAt hdir
  change (fderiv ℝ q p - c • ((‖p‖ ^ 2)⁻¹ • innerSL ℝ p)) (-p) ≤ 0 at hnon
  simp only [sub_apply, smul_apply, map_neg,
    innerSL_apply_apply, real_inner_self_eq_norm_sq, hnormp, one_pow, inv_one,
    one_smul, smul_eq_mul, mul_one] at hnon
  linarith

end DifferentialGeometry.Analysis
