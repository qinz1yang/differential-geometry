import DifferentialGeometry.Geometry.Metric.Approximation.SlimChartCutoffSupport
import DifferentialGeometry.Geometry.Metric.Approximation.EdgeChartCutoffSupport
import Mathlib.Tactic

set_option autoImplicit false
open Set Metric DifferentialGeometry.Analysis GC.MetricGeometry

namespace SupportBufferRegression

private abbrev Plane := WithLp 2 (ℝ × ℝ)
private abbrev HalfPlane := {y : Plane // 0 ≤ y.snd}
private def origin : HalfPlane := ⟨0, by simp⟩
private def Q (x : HalfPlane) : Plane := x.val
private def bottom : Set HalfPlane := {x | x.val.snd = 0}
private def P (x : HalfPlane) : ℝ := x.val.snd
private noncomputable def error : ℝ := 1 / 10000000

private theorem model_distortion (x y : HalfPlane) : |dist (Q x) (Q y) - dist x y| ≤ error := by
  change |dist x.val y.val - dist x.val y.val| ≤ error
  norm_num [error]

private theorem model_coverage (y : Plane) (hy : y.snd ∈ Icc 0 (300 : ℝ))
    (hn : ‖y‖ < 200 - error) : infDist y (Q '' ball origin 200) ≤ error := by
  have hx : (⟨y, hy.1⟩ : HalfPlane) ∈ ball origin 200 := by
    change dist y 0 < 200
    rw [dist_zero_right]
    linarith [show 0 < error by norm_num [error]]
  have hh := infDist_le_dist_of_mem (x := y) (y := y)
    (show y ∈ Q '' ball origin 200 from ⟨⟨y, hy.1⟩, hx, rfl⟩)
  rw [dist_self] at hh
  exact hh.trans (by norm_num [error])

private theorem bottom_model (z : HalfPlane) (hz : z ∈ bottom) :
    ∃ W : HalfPlane → Plane, W z = 0 ∧ (∀ x ∈ ball z 1, 0 ≤ (W x).snd) ∧
      ∀ x ∈ ball z 1, ∀ y ∈ ball z 1, |dist (W x) (W y) - dist x y| ≤ error := by
  refine ⟨fun x => x.val - z.val, sub_self _, ?_, ?_⟩
  · intro x _
    change 0 ≤ x.val.snd - z.val.snd
    rw [show z.val.snd = 0 from hz, sub_zero]
    exact x.property
  · intro x _ y _
    rw [dist_sub_right]
    exact model_distortion x y

private theorem actual_distance_to_bottom (x : HalfPlane) : infDist x bottom = P x := by
  let q : HalfPlane := ⟨WithLp.toLp 2 (x.val.fst, 0), by simp⟩
  have hq : q ∈ bottom := rfl
  have hdist : dist x q = P x := by
    change dist x.val (WithLp.toLp 2 (x.val.fst, 0)) = x.val.snd
    simp only [WithLp.prod_dist_eq_of_L2, WithLp.toLp_fst, WithLp.toLp_snd, dist_self,
      zero_pow (by norm_num : (2 : ℕ) ≠ 0), zero_add, Real.dist_eq, sub_zero]
    rw [sq_abs, Real.sqrt_sq_eq_abs, abs_of_nonneg x.property]
  apply le_antisymm ((infDist_le_dist_of_mem hq).trans_eq hdist)
  apply (le_infDist (show bottom.Nonempty from ⟨origin, rfl⟩)).mpr
  intro y hy
  have h := WithLp.dist_snd_le x.val y.val
  change dist x.val.snd y.val.snd ≤ dist x y at h
  rw [show y.val.snd = 0 from hy, Real.dist_eq, sub_zero, abs_of_nonneg x.property] at h
  exact h

theorem actual_half_plane_padded_boundary :
    let z : HalfPlane := ⟨WithLp.toLp 2 ((100 : ℝ), 0), by simp⟩
    (Q z).snd < (1 : ℝ) / 10 := by
  intro z
  obtain ⟨W, hWz, hWh, hWd⟩ := bottom_model z rfl
  apply padded_strip_height_lt_of_half_plane_model (Δ := 1) (δ := error) (C := 300)
    (by norm_num) (by norm_num [error]) (by norm_num [error]) (by norm_num)
    Q W rfl hWz (fun x _ y _ => model_distortion x y)
    (by simpa using model_coverage) hWh hWd
  change dist z.val 0 < 120 * 1
  rw [dist_zero_right]
  norm_num [z, WithLp.prod_norm_eq_of_L2]

theorem actual_half_plane_with_asymmetric_errors :
    let z : HalfPlane := ⟨WithLp.toLp 2 ((100 : ℝ), 0), by simp⟩
    (Q z).snd < (1 : ℝ) / 100 := by
  intro z
  obtain ⟨W, hWz, hWh, hWd⟩ := bottom_model z rfl
  apply strip_height_lt_of_local_half_plane_model (R := 120) (S := 200) (r := 1)
    (t := 1 / 100) (δ := error) (ε := 10 * error) (C := 300)
    (by norm_num) (by norm_num [error]) (by norm_num [error]) (by norm_num [error])
    (by norm_num [error]) (by norm_num [error]) (by norm_num [error])
    Q W rfl hWz (fun x _ y _ => model_distortion x y) model_coverage hWh
    (fun x hx y hy => (hWd x hx y hy).trans (by norm_num [error]))
  change dist z.val 0 < 120
  rw [dist_zero_right]
  norm_num [z, WithLp.prod_norm_eq_of_L2]

private noncomputable def edgeCutoffOnChart : HalfPlane → ℝ :=
  (Subtype.val : ball origin 100 → HalfPlane).extend
    (fun x => edgeCoordinateProfile x.val.val.fst * edgeHeightProfile (P x.val)) 0

theorem actual_edge_cutoff_has_buffer :
    tsupport edgeCutoffOnChart ⊆ closedBall origin 15 ∧ closedBall origin 15 ⊆ ball origin 20 := by
  have h := tsupport_edge_chart_cutoff_subset (p := origin) (Δ := 1) (δ := error) (C := 300)
    (Λ := 0) (by norm_num) (by norm_num [error]) (by norm_num [error]) (by norm_num)
    (fun _ => 1) P (LipschitzWith.const 1) (fun _ => by norm_num) rfl (by norm_num)
    bottom ⟨origin, rfl⟩ (fun x _ => by rw [actual_distance_to_bottom]; norm_num)
    Q rfl (fun x _ y _ => model_distortion x y) (by simpa using model_coverage)
    (fun x _ => x.property) (fun z hz _ => bottom_model z hz)
    (fun x => x.val.val.fst) (fun _ => by norm_num [Q])
  dsimp only at h
  rw [show (100 : ℝ) * 1 = 100 by norm_num] at h
  simpa only [mul_one, one_mul, div_one, edgeCutoffOnChart] using h

theorem actual_edge_cutoff_is_nonzero : edgeCutoffOnChart origin = 1 := by
  have hpoint : origin ∈ ball origin 100 := mem_ball_self (by norm_num)
  have hf : edgeCoordinateProfile 0 = 1 := (edgeProfiles_plateaus).1 (by norm_num)
  have hg : edgeHeightProfile 0 = 1 := (edgeProfiles_low_height (by norm_num : (0 : ℝ) < 3 / 20)).1
  change Function.extend (Subtype.val : ball origin 100 → HalfPlane)
    (fun x => edgeCoordinateProfile x.val.val.fst * edgeHeightProfile (P x.val)) 0
    ((⟨origin, hpoint⟩ : ball origin 100).val) = 1
  rw [Subtype.val_injective.extend_apply]
  simpa only [origin, P, WithLp.zero_fst, WithLp.zero_snd, hf, hg] using (mul_one (1 : ℝ))

private noncomputable def slimCutoffOnChart : ℝ → ℝ :=
  (Subtype.val : ball (0 : ℝ) 2000000 → ℝ).extend
    (fun x => intervalPlateauProfile (-900000) (-800000) 800000 900000 (x.val / 2)) 0

theorem actual_slim_cutoff_has_buffer :
    tsupport slimCutoffOnChart ⊆ closedBall (0 : ℝ) 1802004 ∧
      closedBall (0 : ℝ) 1802004 ⊆ ball (0 : ℝ) 1900000 := by
  let φ : ball (0 : ℝ) (1000000 * 2) → WithLp 2 (ℝ × Unit) :=
    fun x => WithLp.toLp 2 (x.val, ())
  have h := tsupport_slim_chart_cutoff_subset (p := (0 : ℝ)) (Δ := 2) (by norm_num) ()
    φ Subtype.val rfl (fun x y => by
      have hh := WithLp.prod_dist_sub_dist_fst_le (φ x) (φ y)
      change |dist (φ x) (φ y) - dist x.val y.val| ≤ dist (() : Unit) () at hh
      rw [dist_self] at hh
      exact hh.trans (by norm_num))
    (fun _ => by simp) (fun _ => by norm_num [φ])
  dsimp only at h
  rw [show (1000000 : ℝ) * 2 = 2000000 by norm_num,
    show (901002 : ℝ) * 2 = 1802004 by norm_num,
    show (950000 : ℝ) * 2 = 1900000 by norm_num] at h
  exact h

theorem actual_slim_cutoff_preserves_large_plateau : slimCutoffOnChart 1600000 = 1 := by
  have hx : (1600000 : ℝ) ∈ ball 0 2000000 := by norm_num [mem_ball, Real.dist_eq]
  change Function.extend (Subtype.val : ball (0 : ℝ) 2000000 → ℝ)
    (fun x => intervalPlateauProfile (-900000) (-800000) 800000 900000 (x.val / 2)) 0
    ((⟨1600000, hx⟩ : ball (0 : ℝ) 2000000).val) = 1
  rw [Subtype.val_injective.extend_apply]
  exact intervalPlateauProfile_one (by norm_num) (by norm_num) (by norm_num)

end SupportBufferRegression
