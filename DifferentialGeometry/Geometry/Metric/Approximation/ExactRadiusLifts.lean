import DifferentialGeometry.Geometry.Metric.Approximation.KleinerLottApproximation
import DifferentialGeometry.Geometry.Metric.L2Product
import DifferentialGeometry.Topology.MetricSpace.SegmentConcatenation
import Mathlib.Analysis.InnerProductSpace.PiL2

set_option autoImplicit false

open Set Metric

namespace GC.MetricGeometry

variable {X E Y ι : Type*} [MetricSpace X] [NormedAddCommGroup E] [NormedSpace ℝ E]
variable [MetricSpace Y] {p : X} {y : Y} {ε r : ℝ}

theorem KleinerLottApprox.exists_exact_radius_unit_vector_lifts
    (φ : KleinerLottApprox p (WithLp.toLp 2 ((0 : E), y)) ε)
    (hsegments : ∀ a b : X, ∃ c : Icc (0 : ℝ) 1 → X,
      Continuous c ∧ c ⟨0, by norm_num⟩ = a ∧ c ⟨1, by norm_num⟩ = b ∧
        ∀ s t, dist (c s) (c t) = dist a b * dist s t)
    (v : ι → E) (hv : ∀ j, ‖v j‖ = 1)
    (hr : 0 < r) (hbuffer : r + 5 * ε < ε⁻¹) :
    ∃ x a : ι → X,
      (∀ j, x j ∈ ball p ε⁻¹) ∧
      (∀ j, dist (φ.toFun (x j)) (WithLp.toLp 2 ((r + 4 * ε) • v j, y)) < 2 * ε) ∧
      (∀ j, r + ε < dist p (x j) ∧ dist p (x j) < r + 7 * ε) ∧
      (∀ j, dist p (a j) = r) ∧
      (∀ j, dist (a j) (x j) = dist p (x j) - r) ∧
      (∀ j, dist (φ.toFun (a j)) (WithLp.toLp 2 (r • v j, y)) < 14 * ε) ∧
      ∀ j l, |dist (a j) (a l) - r * ‖v j - v l‖| < 27 * ε := by
  classical
  have hε := φ.error_pos
  let s : ℝ := r + 4 * ε
  have hs : 0 < s := by dsimp [s]; positivity
  let z (j : ι) : WithLp 2 (E × Y) := WithLp.toLp 2 (s • v j, y)
  have hz (j : ι) : dist (z j) (WithLp.toLp 2 ((0 : E), y)) = s := by
    rw [(WithLp.isometry_prodMk_right (E := E) y).dist_eq, dist_zero_right,
      norm_smul, Real.norm_eq_abs, abs_of_pos hs, hv, mul_one]
  have hcover (j : ι) : dist (z j) (WithLp.toLp 2 ((0 : E), y)) < ε⁻¹ - ε := by
    rw [hz]
    dsimp [s]
    linarith
  choose x hxmem hxclose using fun j => φ.coverage_witness (z j) (hcover j)
  have hxlift (j : ι) : dist (φ.toFun (x j)) (z j) < 2 * ε := by
    simpa only [dist_comm] using hxclose j
  have hlength (j : ι) : |dist p (x j) - s| < 3 * ε := by
    have hrad := abs_le.mp (φ.radial_error (x j) (hxmem j))
    rw [dist_comm (x j) p] at hrad
    have hmodel := abs_le.mp (abs_dist_sub_le (φ.toFun (x j)) (z j)
      (WithLp.toLp 2 ((0 : E), y)))
    rw [hz] at hmodel
    exact abs_lt.mpr ⟨by linarith [hxlift j], by linarith [hxlift j]⟩
  have hlength' (j : ι) : r + ε < dist p (x j) ∧ dist p (x j) < r + 7 * ε := by
    have h := abs_lt.mp (hlength j)
    dsimp [s] at h
    constructor <;> linarith
  have hrx (j : ι) : r ≤ dist p (x j) := by linarith [(hlength' j).1]
  have hseg (j : ι) : ∃ q : Icc (0 : ℝ) (dist p (x j)) → X, Isometry q ∧
      q ⟨0, le_rfl, dist_nonneg⟩ = p ∧ q ⟨dist p (x j), dist_nonneg, le_rfl⟩ = x j := by
    obtain ⟨c, _, hc0, hc1, hcd⟩ := hsegments p (x j)
    exact exists_isometric_segment_of_dist_eq_mul hc0 hc1 hcd
  choose q hq hq0 hq1 using hseg
  let a (j : ι) : X := q j ⟨r, hr.le, hrx j⟩
  have harad (j : ι) : dist p (a j) = r := by
    rw [← hq0 j, (hq j).dist_eq, Subtype.dist_eq, Real.dist_eq,
      zero_sub, abs_neg, abs_of_pos hr]
  have hatail (j : ι) : dist (a j) (x j) = dist p (x j) - r := by
    conv_lhs => rw [← hq1 j, (hq j).dist_eq, Subtype.dist_eq, Real.dist_eq,
      abs_of_nonpos (sub_nonpos.mpr (hrx j))]
    ring
  have hatail_lt (j : ι) : dist (a j) (x j) < 7 * ε := by
    rw [hatail]
    linarith [(hlength' j).2]
  have hamem (j : ι) : a j ∈ ball p ε⁻¹ := by
    rw [mem_ball, dist_comm, harad]
    linarith
  have hmodel_move (j : ι) :
      dist (z j) (WithLp.toLp 2 (r • v j, y)) = 4 * ε := by
    rw [(WithLp.isometry_prodMk_right (E := E) y).dist_eq, dist_eq_norm,
      ← sub_smul, norm_smul, Real.norm_eq_abs, hv, mul_one]
    have hsr : s - r = 4 * ε := by dsimp [s]; ring
    rw [hsr, abs_of_pos (by positivity)]
  have hamap (j : ι) :
      dist (φ.toFun (a j)) (WithLp.toLp 2 (r • v j, y)) < 14 * ε := by
    have hd := (abs_le.mp (φ.distortion (a j) (hamem j) (x j) (hxmem j))).2
    have ht := dist_triangle (φ.toFun (a j)) (φ.toFun (x j)) (WithLp.toLp 2 (r • v j, y))
    have ht' := dist_triangle (φ.toFun (x j)) (z j) (WithLp.toLp 2 (r • v j, y))
    rw [hmodel_move] at ht'
    linarith [hatail_lt j, hxlift j]
  refine ⟨x, a, hxmem, hxlift, hlength', harad, hatail, hamap, ?_⟩
  intro j l
  have hmodel_pair : dist (z j) (z l) = s * ‖v j - v l‖ := by
    rw [(WithLp.isometry_prodMk_right (E := E) y).dist_eq, dist_eq_norm,
      ← smul_sub, norm_smul, Real.norm_eq_abs, abs_of_pos hs]
  have hliftpair : |dist (x j) (x l) - s * ‖v j - v l‖| < 5 * ε := by
    have hd := abs_le.mp (φ.distortion (x j) (hxmem j) (x l) (hxmem l))
    have ht := dist_dist_dist_le (φ.toFun (x j)) (φ.toFun (x l)) (z j) (z l)
    rw [Real.dist_eq, hmodel_pair] at ht
    have hh := abs_le.mp ht
    exact abs_lt.mpr ⟨by linarith [hxlift j, hxlift l], by linarith [hxlift j, hxlift l]⟩
  have htailpair : |dist (a j) (a l) - dist (x j) (x l)| < 14 * ε := by
    have ht := dist_dist_dist_le (a j) (a l) (x j) (x l)
    rw [Real.dist_eq] at ht
    linarith [hatail_lt j, hatail_lt l]
  have hnorm : ‖v j - v l‖ ≤ 2 := by
    calc
      ‖v j - v l‖ ≤ ‖v j‖ + ‖v l‖ := norm_sub_le _ _
      _ = 2 := by rw [hv, hv]; norm_num
  have hmodelchange : |s * ‖v j - v l‖ - r * ‖v j - v l‖| ≤ 8 * ε := by
    rw [← sub_mul, abs_mul, abs_of_nonneg (norm_nonneg _)]
    have hsr : s - r = 4 * ε := by dsimp [s]; ring
    rw [hsr, abs_of_pos (by positivity)]
    nlinarith
  calc
    |dist (a j) (a l) - r * ‖v j - v l‖| =
        |(dist (a j) (a l) - dist (x j) (x l)) +
          (dist (x j) (x l) - s * ‖v j - v l‖) +
          (s * ‖v j - v l‖ - r * ‖v j - v l‖)| := by congr 1; ring
    _ ≤ |dist (a j) (a l) - dist (x j) (x l)| +
        |dist (x j) (x l) - s * ‖v j - v l‖| +
        |s * ‖v j - v l‖ - r * ‖v j - v l‖| := abs_add_three _ _ _
    _ < 27 * ε := by linarith


theorem KleinerLottApprox.exists_exact_radius_signed_axis_lifts {k : ℕ}
    (φ : KleinerLottApprox p
      (WithLp.toLp 2 ((0 : EuclideanSpace ℝ (Fin k)), y)) ε)
    (hsegments : ∀ a b : X, ∃ c : Icc (0 : ℝ) 1 → X,
      Continuous c ∧ c ⟨0, by norm_num⟩ = a ∧ c ⟨1, by norm_num⟩ = b ∧
        ∀ s t, dist (c s) (c t) = dist a b * dist s t)
    (hr : 0 < r) (hbuffer : r + 5 * ε < ε⁻¹) :
    ∃ x a : Fin k × Bool → X,
      (∀ j, x j ∈ ball p ε⁻¹) ∧
      (∀ j, dist (φ.toFun (x j))
        (WithLp.toLp 2 (PiLp.single 2 j.1 (if j.2 then r + 4 * ε else -(r + 4 * ε)), y)) < 2 * ε) ∧
      (∀ j, r + ε < dist p (x j) ∧ dist p (x j) < r + 7 * ε) ∧
      (∀ j, dist p (a j) = r) ∧
      (∀ j, dist (a j) (x j) = dist p (x j) - r) ∧
      (∀ j, dist (φ.toFun (a j))
        (WithLp.toLp 2 (PiLp.single 2 j.1 (if j.2 then r else -r), y)) < 14 * ε) ∧
      ∀ j l, |dist (a j) (a l) - r *
        ‖(PiLp.single 2 j.1 (if j.2 then (1 : ℝ) else -1) : EuclideanSpace ℝ (Fin k)) -
          PiLp.single 2 l.1 (if l.2 then (1 : ℝ) else -1)‖| < 27 * ε := by
  let v (j : Fin k × Bool) : EuclideanSpace ℝ (Fin k) :=
    PiLp.single 2 j.1 (if j.2 then 1 else -1)
  have hv (j : Fin k × Bool) : ‖v j‖ = 1 := by
    rcases j with ⟨j, b⟩
    cases b <;> simp [v, PiLp.norm_single]
  have hsmul (c : ℝ) (j : Fin k × Bool) :
      c • v j = PiLp.single 2 j.1 (if j.2 then c else -c) := by
    rcases j with ⟨j, b⟩
    cases b <;> ext l <;> by_cases hl : l = j <;> simp [v, hl]
  obtain ⟨x, a, hxmem, hxlift, hlength, harad, hatail, hamap, hpair⟩ :=
    φ.exists_exact_radius_unit_vector_lifts hsegments v hv hr hbuffer
  refine ⟨x, a, hxmem, ?_, hlength, harad, hatail, ?_, hpair⟩
  · intro j
    simpa only [hsmul] using hxlift j
  · intro j
    simpa only [hsmul] using hamap j

end GC.MetricGeometry
