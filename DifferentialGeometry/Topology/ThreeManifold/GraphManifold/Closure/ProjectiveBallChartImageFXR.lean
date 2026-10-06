import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.ProjectiveBallChartFXR

/-!
# The ball chart of `ℝP³` and the image of its open unit ball

Lane S-FIX-REG2 (suffix `_FXR`), G4 part 3. Continues `ProjectiveBallChartFXR`:

* `exists_rp3BallChart_FXR`: a `BallChart` `d` of `ℝP³` with `d x = [amb_true ((2/3) x)]` on the
  closed ball of radius `2`;
* `rp3BallChart_image_FXR`: `d '' ball 0 1 = {p₀² > 16/25}`;
* `exists_rp3OrientedBallChart_FXR`: an `OrientedBallChart` of `ℝP³` with the same image.
-/

set_option autoImplicit false

noncomputable section

open Set Function Metric Manifold
open scoped Manifold ContDiff Topology InnerProductSpace
open DifferentialGeometry DifferentialGeometry.Topology GC.Endpoint GC.GraphManifold
open GC.GraphManifold.Assembly GC.GraphManifold.Assembly.FC39P0

namespace GC.GraphManifold.Assembly

local notation "E3" => EuclideanSpace ℝ (Fin 3)
local notation "E4" => EuclideanSpace ℝ (Fin 4)

/-- A ball chart of `ℝP³`: the rescaled stereographic chart composed with the covering map. -/
theorem exists_rp3BallChart_FXR :
    ∃ d : BallChart 3 (𝓡 3) projectiveThreeSpaceLift.{0}.Carrier,
      ∀ x ∈ closedBall (0 : E3) 2,
        d.chart x = rp3Cover_FXR (cycleBallAmbient true ((2 / 3 : ℝ) • x)) := by
  have hU : ∀ x ∈ closedBall (0 : E3) 2, rp3SphereChart_FXR.chart x ∈ rp3Hemisphere_FXR := by
    intro x hx
    rw [rp3SphereChart_apply_FXR]
    change 0 < sphereHeight (cycleBallAmbient true ((2 / 3 : ℝ) • x))
    rw [sphereHeight_ambient_true]
    have hx2 : ‖x‖ ≤ 2 := by simpa [mem_closedBall, dist_eq_norm] using hx
    have hn : ‖(2 / 3 : ℝ) • x‖ ≤ 4 / 3 := by
      rw [norm_smul, Real.norm_eq_abs, abs_of_pos (by norm_num : (0 : ℝ) < 2 / 3)]
      linarith
    have h0 := norm_nonneg ((2 / 3 : ℝ) • x)
    have hneg : ‖(2 / 3 : ℝ) • x‖ ^ 2 - 4 < 0 := by nlinarith
    exact neg_pos.2 (div_neg_of_neg_of_pos hneg (by positivity))
  have hf : IsLocalDiffeomorph (𝓡 3) (𝓡 3) ∞
      (fun u : rp3Hemisphere_FXR => rp3Cover_FXR u.val) :=
    isLocalDiffeomorph_comp (f := (Subtype.val : rp3Hemisphere_FXR → sphereW.Carrier))
      (g := rp3Cover_FXR) isLocalDiffeomorph_rp3Cover_FXR
      (isLocalDiffeomorph_subtype_val (I := 𝓡 3) rp3Hemisphere_FXR)
  have hinj : Injective (fun u : rp3Hemisphere_FXR => rp3Cover_FXR u.val) := fun u v h =>
    Subtype.ext (rp3Cover_injOn_FXR _ _ u.2 v.2 h)
  obtain ⟨d, -, -, hd⟩ := BallChart.exists_ballChart_of_open_embedding rp3SphereChart_FXR
    rp3Hemisphere_FXR _ hf hinj hU
  exact ⟨d, fun x hx => (hd x hx).trans (congrArg rp3Cover_FXR (rp3SphereChart_apply_FXR x))⟩

/-- **The image of the open unit ball** under the ball chart is `{p₀² > 16/25}`. -/
theorem rp3BallChart_image_FXR (d : BallChart 3 (𝓡 3) projectiveThreeSpaceLift.{0}.Carrier)
    (hd : ∀ x ∈ closedBall (0 : E3) 2,
      d.chart x = rp3Cover_FXR (cycleBallAmbient true ((2 / 3 : ℝ) • x))) :
    d.chart '' ball (0 : E3) 1 = {y | 16 / 25 < rp3Height2_FXR y} := by
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩
    have hx1 : ‖x‖ < 1 := by simpa using hx
    have hxc : x ∈ closedBall (0 : E3) 2 := by
      rw [mem_closedBall, dist_zero_right]
      linarith
    rw [hd x hxc]
    change 16 / 25 < sphereHeight (cycleBallAmbient true ((2 / 3 : ℝ) • x)) ^ 2
    rw [sphereHeight_ambient_true]
    have hn : ‖(2 / 3 : ℝ) • x‖ < 2 / 3 := by
      rw [norm_smul, Real.norm_eq_abs, abs_of_pos (by norm_num : (0 : ℝ) < 2 / 3)]
      linarith
    have h45 := (neg_stereo_gt_iff_FXR (norm_nonneg ((2 / 3 : ℝ) • x))).2 hn
    nlinarith
  · intro hy
    obtain ⟨p, rfl⟩ := rp3Cover_surjective_FXR y
    have hp : 16 / 25 < sphereHeight p ^ 2 := hy
    -- a representative with positive height
    obtain ⟨p', hp'c, hp'h⟩ : ∃ p' : sphereW.Carrier, rp3Cover_FXR p' = rp3Cover_FXR p ∧
        4 / 5 < sphereHeight p' := by
      rcases lt_or_gt_of_ne (show sphereHeight p ≠ 0 by
          intro h
          rw [h] at hp
          norm_num at hp) with hneg | hpos
      · refine ⟨ULift.up (-spherePoint p), rp3Cover_neg_FXR p, ?_⟩
        rw [sphereHeight_neg_FXR]
        nlinarith
      · exact ⟨p, rfl, by nlinarith⟩
    have hne : spherePoint p' ≠ -cycleBallPole := by
      intro h
      rw [sphereHeight_eq_neg_one_iff.2 h] at hp'h
      norm_num at hp'h
    obtain ⟨y', hy'⟩ := exists_ambient_true hne
    have hh : 4 / 5 < -((‖y'‖ ^ 2 - 4) / (‖y'‖ ^ 2 + 4)) := by
      rw [← sphereHeight_ambient_true, hy']
      exact hp'h
    have hr : ‖y'‖ < 2 / 3 := (neg_stereo_gt_iff_FXR (norm_nonneg y')).1 hh
    refine ⟨(3 / 2 : ℝ) • y', ?_, ?_⟩
    · rw [mem_ball, dist_zero_right, norm_smul, Real.norm_eq_abs,
        abs_of_pos (by norm_num : (0 : ℝ) < 3 / 2)]
      linarith
    · have hxc : (3 / 2 : ℝ) • y' ∈ closedBall (0 : E3) 2 := by
        rw [mem_closedBall, dist_zero_right, norm_smul, Real.norm_eq_abs,
          abs_of_pos (by norm_num : (0 : ℝ) < 3 / 2)]
        linarith
      rw [hd _ hxc, smul_smul, show (2 / 3 : ℝ) * (3 / 2) = 1 by norm_num, one_smul, hy', hp'c]

/-- **An oriented ball chart of `ℝP³`** whose open unit-ball image is `{p₀² > 16/25}`. -/
theorem exists_rp3OrientedBallChart_FXR :
    ∃ c : OrientedBallChart projectiveThreeSpaceLift.{0}.toClosedOrientedManifold,
      c.chart '' ball (0 : E3) 1 = {y | 16 / 25 < rp3Height2_FXR y} := by
  obtain ⟨d, hd⟩ := exists_rp3BallChart_FXR
  have himg := rp3BallChart_image_FXR d hd
  rcases BallChart.exists_oriented d with ⟨c, hc⟩ | ⟨c, hc⟩
  · refine ⟨c, ?_⟩
    rw [← himg]
    exact image_congr (fun x _ => hc x)
  · refine ⟨⟨c.reflect.toBallChart, fun x hx => ?_⟩, ?_⟩
    · exact (c.reflect.preserves_orientation x hx).trans (neg_neg _)
    · rw [← himg]
      have hset : (fun x : E3 => d.chart (-x)) '' ball (0 : E3) 1 = d.chart '' ball (0 : E3) 1 := by
        rw [show (fun x : E3 => d.chart (-x)) = d.chart ∘ Neg.neg from rfl, image_comp]
        congr 1
        ext z
        simp
      rw [← hset]
      exact image_congr (fun x _ => by rw [OrientedBallChart.reflect_apply, hc])

end GC.GraphManifold.Assembly
