import DifferentialGeometry.Analysis.Real.GeometricEndpointAverage
import DifferentialGeometry.Geometry.Metric.CurveEnergy

noncomputable section

namespace DifferentialGeometry.Geometry.Riemannian

open Set MeasureTheory
open scoped _root_.Manifold ContDiff BigOperators

variable {E H M : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

theorem exists_riemannianEDistOf_sq_div_le_curveEnergy
    (g : SmoothRiemannianMetric I M) (alpha : ℝ → M)
    (halpha : ContMDiff 𝓘(ℝ, ℝ) I 1 alpha) {L : ℝ} (hL : 0 < L) (n : ℕ) :
    ∃ j ≤ n,
      (riemannianEDistOf g (alpha 0) (alpha (L * (4 : ℝ) ^ j))).toReal ^ 2 /
          (L * (4 : ℝ) ^ j) ≤
        4 * curveEnergy g alpha 0 (L * (4 : ℝ) ^ n) / (n + 1 : ℝ) := by
  let t : ℕ → ℝ := fun j => L * (4 : ℝ) ^ j
  let e : ℕ → ℝ
    | 0 => curveEnergy g alpha 0 L
    | j + 1 => curveEnergy g alpha (t j) (t (j + 1))
  let d : ℕ → ℝ := fun j =>
    (riemannianEDistOf g (alpha 0) (alpha (t j))).toReal / Real.sqrt L
  have htpos (j : ℕ) : 0 < t j := mul_pos hL (pow_pos (by norm_num) _)
  have htmono (j : ℕ) : t j ≤ t (j + 1) := by
    dsimp only [t]
    rw [pow_succ]
    nlinarith [pow_nonneg (by norm_num : (0 : ℝ) ≤ 4) j]
  have hE (a b : ℝ) : IntegrableOn (fun r => g.inner (alpha r)
      (mfderiv 𝓘(ℝ, ℝ) I alpha r (1 : ℝ))
      (mfderiv 𝓘(ℝ, ℝ) I alpha r (1 : ℝ))) (Icc a b) :=
    integrableOn_inner_mfderiv_self_of_contMDiffOn g halpha.contMDiffOn
  have hInt {a b : ℝ} (hab : a ≤ b) : IntervalIntegrable (fun r => g.inner (alpha r)
      (mfderiv 𝓘(ℝ, ℝ) I alpha r (1 : ℝ))
      (mfderiv 𝓘(ℝ, ℝ) I alpha r (1 : ℝ))) volume a b := by
    apply MeasureTheory.IntegrableOn.intervalIntegrable
    simpa only [uIcc_of_le hab] using hE a b
  have hfin {a b : ℝ} (hab : a ≤ b) : riemannianEDistOf g (alpha a) (alpha b) ≠ ⊤ :=
    ne_top_of_le_ne_top ENNReal.ofReal_ne_top
      (edistOf_le_energy g hab halpha.contMDiffOn (hE a b))
  have hsum (m : ℕ) : (∑ j ∈ Finset.range (m + 1), e j) =
      curveEnergy g alpha 0 (t m) := by
    induction m with
    | zero => simp only [e, t, pow_zero, mul_one, zero_add, Finset.sum_range_one]
    | succ m ih =>
      rw [Finset.sum_range_succ e (m + 1), ih]
      change curveEnergy g alpha 0 (t m) + curveEnergy g alpha (t m) (t (m + 1)) = _
      exact intervalIntegral.integral_add_adjacent_intervals (hInt (htpos m).le) (hInt (htmono m))
  have hnonneg (j : ℕ) : 0 ≤ e j := by
    cases j with
    | zero => exact curveEnergy_nonneg g hL.le
    | succ j => exact curveEnergy_nonneg g (htmono j)
  have hsqrt : 0 < Real.sqrt L := Real.sqrt_pos.mpr hL
  have hinit : d 0 ^ 2 ≤ e 0 := by
    have hsq := riemannianEDistOf_toReal_sq_le_curveEnergy g hL.le
      halpha.contMDiffOn (hE 0 L)
    change ((riemannianEDistOf g (alpha 0) (alpha (L * (4 : ℝ) ^ 0))).toReal /
      Real.sqrt L) ^ 2 ≤ curveEnergy g alpha 0 L
    rw [pow_zero, mul_one, div_pow, Real.sq_sqrt hL.le]
    exact (div_le_iff₀ hL).mpr (by simpa only [sub_zero, mul_comm] using hsq)
  have hinc (j : ℕ) : d (j + 1) ≤ d j +
      (2 : ℝ) ^ (j + 1) * Real.sqrt (e (j + 1)) := by
    have hstep := edistOf_le_energy g (htmono j) halpha.contMDiffOn
      (hE (t j) (t (j + 1)))
    have hstepReal := ENNReal.toReal_mono ENNReal.ofReal_ne_top hstep
    rw [ENNReal.toReal_ofReal (by positivity)] at hstepReal
    have htri := DifferentialGeometry.riemannianEDistOf_toReal_triangle g
      (alpha 0) (alpha (t j)) (alpha (t (j + 1)))
      (hfin (htpos j).le) (hfin (htmono j))
    have hdist : (riemannianEDistOf g (alpha 0) (alpha (t (j + 1)))).toReal ≤
        (riemannianEDistOf g (alpha 0) (alpha (t j))).toReal +
          Real.sqrt (t (j + 1) - t j) * Real.sqrt (e (j + 1)) :=
      htri.trans (add_le_add_right hstepReal _)
    have hpower : ((2 : ℝ) ^ (j + 1)) ^ 2 = (4 : ℝ) ^ (j + 1) := by
      rw [← pow_mul, Nat.mul_comm, pow_mul]
      norm_num
    have hscale : Real.sqrt (t (j + 1) - t j) ≤
        Real.sqrt L * (2 : ℝ) ^ (j + 1) := by
      apply Real.sqrt_le_iff.mpr
      refine ⟨by positivity, ?_⟩
      rw [mul_pow, Real.sq_sqrt hL.le, hpower]
      simpa only [t] using sub_le_self (t (j + 1)) (htpos j).le
    have hmul := mul_le_mul_of_nonneg_right hscale (Real.sqrt_nonneg (e (j + 1)))
    have h := div_le_div_of_nonneg_right
      (hdist.trans (add_le_add_right hmul _)) hsqrt.le
    change d (j + 1) ≤ _
    refine h.trans_eq ?_
    dsimp only [d]
    rw [add_div]
    congr 1
    field_simp [hsqrt.ne']
  obtain ⟨j, hj, havg⟩ := DifferentialGeometry.Analysis.exists_sq_div_pow_four_le_of_increment_le
    d e n (fun j _ => div_nonneg ENNReal.toReal_nonneg hsqrt.le)
    (fun j _ => hnonneg j) hinit (fun j _ => hinc j)
  refine ⟨j, hj, ?_⟩
  rw [hsum n] at havg
  simpa only [d, t, div_pow, Real.sq_sqrt hL.le, div_div] using havg

end DifferentialGeometry.Geometry.Riemannian
