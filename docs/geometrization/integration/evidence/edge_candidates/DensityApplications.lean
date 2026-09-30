import DifferentialGeometry.Geometry.Metric.Approximation.StrongEdgeDensity
import DifferentialGeometry.Geometry.Metric.Approximation.IsometricKleinerLottApproximation
import DifferentialGeometry.Geometry.Metric.L2Product
import DifferentialGeometry.Geometry.Metric.Scaling.RescaleComposition

set_option autoImplicit false
open Set Metric GC.MetricGeometry

private abbrev Interval := Icc (0 : ℝ) 501
private def intervalOrigin : Interval := ⟨0, by norm_num⟩
private noncomputable def intervalMark : Interval := ⟨1 / 8, by norm_num⟩
private def rayOrigin : Ici (0 : ℝ) := ⟨0, by norm_num⟩
private noncomputable def rayMark : Ici (0 : ℝ) := ⟨1 / 8, by norm_num⟩

example :
    let X := WithLp 2 (ℝ × Interval)
    ∃ a : X, isEdgePoint.{0, 0} a 1 (1 / 1000) (1 / 1000) ∧
      dist a (WithLp.toLp 2 ((0 : ℝ), intervalMark)) < 1 := by
  let X := WithLp 2 (ℝ × Interval)
  let p : X := WithLp.toLp 2 ((0 : ℝ), intervalMark)
  let F : KleinerLottApprox p (WithLp.toLp 2 ((0 : ℝ), intervalMark)) (1 / 10^8) :=
    (IsometryEquiv.refl X).toKleinerLottApprox rfl (by norm_num) (by norm_num)
  let G : KleinerLottApprox intervalMark intervalMark (1 / 10^7) :=
    (IsometryEquiv.refl (Interval)).toKleinerLottApprox rfl (by norm_num) (by norm_num)
  let H : KleinerLottApprox p (WithLp.toLp 2 ((0 : ℝ), intervalMark)) (1 / 10^7) :=
    (IsometryEquiv.refl X).toKleinerLottApprox rfl (by norm_num) (by norm_num)
  have hρ : LipschitzWith (0 : NNReal) (fun _ : X => (1 : ℝ)) := LipschitzWith.const 1
  have hcompat : ∀ x ∈ ball p (1000 * (1 : ℝ)),
      dist (G.toFun (F.toFun x).snd) (H.toFun x).snd < 1 / 10^6 := by
    intro x _
    have heq : G.toFun (F.toFun x).snd = (H.toFun x).snd := rfl
    rw [heq, dist_self]
    norm_num
  obtain ⟨a, hed, hclose⟩ := exists_strong_edge_near_interval_model (Δ := 1)
    (βE := 1 / 1000) (s := 1 / 1000) (θ := 1 / 10^6) F G H hρ (fun _ => by norm_num) rfl
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num [intervalMark]) hcompat
  refine ⟨a, ?_, ?_⟩
  · have hm : (inferInstance : MetricSpace X).rescale (1 : ℝ)⁻¹ (by positivity) =
        (inferInstance : MetricSpace X) := by simp only [inv_one, MetricSpace.rescale_one]
    rw [hm] at hed
    exact hed
  · simpa only [mul_one] using hclose


example :
    let X := WithLp 2 (ℝ × Ici (0 : ℝ))
    ∃ a : X, isEdgePoint.{0, 0} a 1 (1 / 1000) (1 / 1000) ∧
      dist a (WithLp.toLp 2 ((0 : ℝ), rayMark)) < 1 := by
  let X := WithLp 2 (ℝ × Ici (0 : ℝ))
  let p : X := WithLp.toLp 2 ((0 : ℝ), rayMark)
  let F : KleinerLottApprox p (WithLp.toLp 2 ((0 : ℝ), rayMark)) (1 / 10^8) :=
    (IsometryEquiv.refl X).toKleinerLottApprox rfl (by norm_num) (by norm_num)
  let G : KleinerLottApprox rayMark rayMark (1 / 10^7) :=
    (IsometryEquiv.refl (Ici (0 : ℝ))).toKleinerLottApprox rfl (by norm_num) (by norm_num)
  let H : KleinerLottApprox p (WithLp.toLp 2 ((0 : ℝ), rayMark)) (1 / 10^7) :=
    (IsometryEquiv.refl X).toKleinerLottApprox rfl (by norm_num) (by norm_num)
  have hρ : LipschitzWith (0 : NNReal) (fun _ : X => (1 : ℝ)) := LipschitzWith.const 1
  have hcompat : ∀ x ∈ ball p (1000 * (1 : ℝ)),
      dist (G.toFun (F.toFun x).snd) (H.toFun x).snd < 1 / 10^6 := by
    intro x _
    have heq : G.toFun (F.toFun x).snd = (H.toFun x).snd := rfl
    rw [heq, dist_self]
    norm_num
  obtain ⟨a, hed, hclose⟩ := exists_strong_edge_near_ray_model (Δ := 1)
    (βE := 1 / 1000) (s := 1 / 1000) (θ := 1 / 10^6) F G H hρ (fun _ => by norm_num) rfl
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num [rayMark]) hcompat
  refine ⟨a, ?_, ?_⟩
  · have hm : (inferInstance : MetricSpace X).rescale (1 : ℝ)⁻¹ (by positivity) =
        (inferInstance : MetricSpace X) := by simp only [inv_one, MetricSpace.rescale_one]
    rw [hm] at hed
    exact hed
  · simpa only [mul_one] using hclose
