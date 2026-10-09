import DifferentialGeometry.Geometry.Collapse.Inhabitants.EdgeCapCarrier
import DifferentialGeometry.Analysis.Calculus.Cutoff.GraphPacketProfiles
/-! Actual smooth capped height, internal scale and complete slab bounds. -/

set_option autoImplicit false
noncomputable section
open DifferentialGeometry DifferentialGeometry.Geometry DifferentialGeometry.Geometry.Riemannian
open DifferentialGeometry.Geometry.Collapse.EdgeCapSurface
open DifferentialGeometry.Geometry.Collapse.EdgeCapProduct
open DifferentialGeometry.Geometry.Collapse.EdgeCapDistance
open DifferentialGeometry.Geometry.Collapse.EdgeCapCarrier
open DifferentialGeometry.Analysis
open scoped Manifold ContDiff

namespace DifferentialGeometry.Geometry.Collapse.EdgeCapHeight

def capRadialProfile (r : ℝ) : ℝ := r * (1 - edgeHeightProfile r)
theorem capRadialProfile_smooth : ContDiff ℝ ∞ capRadialProfile :=
  contDiff_id.mul (contDiff_const.sub edgeProfiles_contDiff.2.1)
theorem capRadialProfile_flat {r : ℝ} (hr : r ≤ 8) : capRadialProfile r = 0 := by
  rw [capRadialProfile, edgeHeightProfile,
    descendingIntervalProfile_one (by norm_num) hr]
  ring
theorem capRadialProfile_linear {r : ℝ} (hr : 9 ≤ r) : capRadialProfile r = r := by
  rw [capRadialProfile, edgeHeightProfile,
    descendingIntervalProfile_zero (by norm_num) hr]
  ring

def capCollarHeight (ε : ℝ) (x : E2) : ℝ := ε * capRadialProfile ‖x‖
theorem capCollarHeight_smooth (ε : ℝ) : ContDiff ℝ ∞ (capCollarHeight ε) := by
  apply contDiff_const.mul
  apply contDiff_comp_norm_of_eq_const_near_zero capRadialProfile_smooth
    (by norm_num : (0 : ℝ) < 8)
  intro r hr
  rw [capRadialProfile_flat hr, capRadialProfile_flat (by norm_num : (0 : ℝ) ≤ 8)]

theorem capCollarHeight_error (ε : ℝ) (hε : 0 ≤ ε) (x : E2) :
    |capCollarHeight ε x - ε * ‖x‖| ≤ 9 * ε := by
  have hp := (edgeProfiles_mem_Icc ‖x‖).2.1
  by_cases hn : 9 ≤ ‖x‖
  · rw [capCollarHeight, capRadialProfile_linear hn, sub_self, abs_zero]
    positivity
  · have hr : ‖x‖ ≤ 9 := (lt_of_not_ge hn).le
    have he : capCollarHeight ε x - ε * ‖x‖ = - (ε * ‖x‖ * edgeHeightProfile ‖x‖) := by
      unfold capCollarHeight capRadialProfile
      ring
    rw [he, abs_neg, abs_of_nonneg
      (mul_nonneg (mul_nonneg hε (norm_nonneg x)) hp.1)]
    have hmul := mul_le_mul_of_nonneg_left hp.2 (mul_nonneg hε (norm_nonneg x))
    have hrad := mul_le_mul_of_nonneg_left hr hε
    nlinarith [hmul, hrad]

theorem capCollarHeight_sublevel {ε : ℝ} (hε : 0 < ε) {R : ℝ} (hR : 9 * ε ≤ R)
    {x : E2} : capCollarHeight ε x ≤ R ↔ ε * ‖x‖ ≤ R := by
  have hp := (edgeProfiles_mem_Icc ‖x‖).2.1
  by_cases hn : 9 ≤ ‖x‖
  · rw [capCollarHeight, capRadialProfile_linear hn]
  · have hr : ‖x‖ ≤ 9 := (lt_of_not_ge hn).le
    have hd : ε * ‖x‖ ≤ R := (mul_le_mul_of_nonneg_left hr hε.le).trans
      (by simpa [mul_comm] using hR)
    have hu : capCollarHeight ε x ≤ ε * ‖x‖ := by
      unfold capCollarHeight capRadialProfile
      nlinarith [mul_nonneg hε.le (norm_nonneg x),
        mul_nonneg (mul_nonneg hε.le (norm_nonneg x)) hp.1]
    exact ⟨fun _ => hd, fun _ => hu.trans hd⟩

open DifferentialGeometry.PDE.RicciFlow.StandardCap

def capExampleDelta : ℝ := 100000000 + 10000 * capExampleEpsilon * (transitionEnd + 1)
theorem capExampleDelta_large : 100000000 ≤ capExampleDelta := by
  unfold capExampleDelta
  have h := capExampleEpsilon_pos
  have he := transitionEnd_pos
  have hm : 0 ≤ 10000 * capExampleEpsilon * (transitionEnd + 1) := by positivity
  linarith

theorem capExampleDelta_height_error : 9 * capExampleEpsilon < capExampleDelta / 100 := by
  unfold capExampleDelta
  have h := capExampleEpsilon_pos
  have he := transitionEnd_pos
  have hm := mul_pos h he
  nlinarith

theorem capCollarHeight_nonneg (ε : ℝ) (hε : 0 ≤ ε) (x : E2) :
    0 ≤ capCollarHeight ε x := by
  have hp := (edgeProfiles_mem_Icc ‖x‖).2.1
  unfold capCollarHeight capRadialProfile
  exact mul_nonneg hε (mul_nonneg (norm_nonneg x) (sub_nonneg.mpr hp.2))

theorem capCollarHeight_le_radius (ε : ℝ) (hε : 0 ≤ ε) (x : E2) :
    capCollarHeight ε x ≤ ε * ‖x‖ := by
  have hp := (edgeProfiles_mem_Icc ‖x‖).2.1
  unfold capCollarHeight capRadialProfile
  nlinarith [mul_nonneg (mul_nonneg hε (norm_nonneg x)) hp.1]

attribute [local instance] capExampleSigma capExampleMetricSpace capExampleEDist
  capExampleDist capExampleUniform capExampleEMetric capExamplePseudo capExampleBundle
  capExampleRiemannian capExampleContinuous capExampleComplete capExampleProper capExampleDimension

def capExampleF (x : E3) : ℝ :=
  capCollarHeight capExampleEpsilon (capProductCoordinates.symm x).2

theorem capExampleF_smooth : ContMDiff (𝓡 3) 𝓘(ℝ, ℝ) ∞ capExampleF :=
  (capCollarHeight_smooth capExampleEpsilon).contMDiff.comp
    (contMDiff_snd.comp capProductCoordinates.symm.contMDiff)

theorem capExampleF_error (x : E3) :
    |capExampleF x - Metric.infDist x capThreeAxis| ≤ 9 * capExampleEpsilon := by
  rw [capExample_axis_infDist]
  exact capCollarHeight_error capExampleEpsilon capExampleEpsilon_pos.le _

theorem capExampleF_sublevel {R : ℝ} (hR : 9 * capExampleEpsilon ≤ R) {x : E3} :
    capExampleF x ≤ R ↔ Metric.infDist x capThreeAxis ≤ R := by
  rw [capExample_axis_infDist]
  exact capCollarHeight_sublevel capExampleEpsilon_pos hR

theorem capExample_distance_axis_zero (x : E3) :
    dist x (capExampleAxis 0) ≤ |capThreeCoord x| + Metric.infDist x capThreeAxis := by
  have ht := dist_triangle x (capExampleAxis (capThreeCoord x)) (capExampleAxis 0)
  have hline := capExample_axis_isometry.dist_eq (capThreeCoord x) 0
  rw [capExample_axis_nearest, hline, Real.dist_eq, sub_zero] at ht
  rw [capExample_axis_infDist]
  simpa only [add_comm] using ht

theorem capExample_closed_slab_bound (x : E3)
    (hc : |capThreeCoord x| ≤ 4 * capExampleDelta) (hF : capExampleF x ≤ 4 * capExampleDelta) :
    dist x (capExampleAxis 0) ≤ 8 * capExampleDelta := by
  have hd := capExampleDelta_large
  have he := capExampleDelta_height_error
  have hr : 9 * capExampleEpsilon ≤ 4 * capExampleDelta := by linarith
  have ha := (capExampleF_sublevel hr (x := x)).mp hF
  exact (capExample_distance_axis_zero x).trans (by linarith)

theorem capExample_open_slab_bound (x : E3)
    (hc : |capThreeCoord x| < 5 * capExampleDelta) (hF : capExampleF x < 5 * capExampleDelta) :
    dist x (capExampleAxis 0) < 20 * capExampleDelta := by
  have hd := capExampleDelta_large
  have he := capExampleDelta_height_error
  have hr : 9 * capExampleEpsilon ≤ 5 * capExampleDelta := by linarith
  have ha := (capExampleF_sublevel hr (x := x)).mp hF.le
  have ht := capExample_distance_axis_zero x
  linarith

end DifferentialGeometry.Geometry.Collapse.EdgeCapHeight
