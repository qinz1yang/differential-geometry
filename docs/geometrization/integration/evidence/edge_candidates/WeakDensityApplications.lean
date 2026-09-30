import DifferentialGeometry.Geometry.Metric.Approximation.WeakEdgeDensity
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
    ∃ z : X, isEdgePoint.{0, 0} z 1 (1 / 10^9) (1 / 10^9) ∧
      ∃ a : X, isEdgePoint.{0, 0} a 1 (1 / 1000) (1 / 1000) ∧ dist z a < 1 := by
  let X := WithLp 2 (ℝ × Interval)
  let p : X := WithLp.toLp 2 ((0 : ℝ), intervalMark)
  let F : KleinerLottApprox p (WithLp.toLp 2 ((0 : ℝ), intervalMark)) (1 / 10^14) :=
    (IsometryEquiv.refl X).toKleinerLottApprox rfl (by norm_num) (by norm_num)
  let G : KleinerLottApprox intervalMark intervalMark (1 / 10^14) :=
    (IsometryEquiv.refl (Interval)).toKleinerLottApprox rfl (by norm_num) (by norm_num)
  let H : KleinerLottApprox p (WithLp.toLp 2 ((0 : ℝ), intervalMark)) (1 / 10^14) :=
    (IsometryEquiv.refl X).toKleinerLottApprox rfl (by norm_num) (by norm_num)
  have hρ : LipschitzWith (0 : NNReal) (fun _ : X => (1 : ℝ)) := LipschitzWith.const 1
  have hcompat : ∀ x ∈ ball p (1000 * (1 : ℝ)),
      dist (G.toFun (F.toFun x).snd) (H.toFun x).snd < 1 / 10^13 := by
    intro x _
    have heq : G.toFun (F.toFun x).snd = (H.toFun x).snd := rfl
    rw [heq, dist_self]
    norm_num
  obtain ⟨z, hrad, hzed, _⟩ := exists_strong_edge_interval_lift (Δ := 1)
    (βE := 1 / 10^9) (s := 1 / 10^9) (θ := 1 / 10^13) F G H hρ (fun _ => by norm_num) rfl
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num [intervalMark]) hcompat
    2 (by norm_num)
  have hz : z ∈ ball p (10 * (1 : ℝ)) := by
    simp only [mem_ball, mul_one]
    norm_num [intervalMark] at hrad
    linarith only [hrad]
  obtain ⟨a, haed, hclose⟩ := exists_strong_edge_near_weak_interval_model (Δ := 1)
    (βE := 1 / 1000) (s := 1 / 1000) (θ := 1 / 10^13) F G H hρ (fun _ => by norm_num) rfl
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num [intervalMark]) hcompat
    (by norm_num) (by norm_num) (by norm_num) hzed hz
  have hm : (inferInstance : MetricSpace X).rescale (1 : ℝ)⁻¹ (by positivity) =
      (inferInstance : MetricSpace X) := by simp only [inv_one, MetricSpace.rescale_one]
  rw [hm] at hzed haed
  exact ⟨z, hzed, a, haed, hclose⟩

example :
    let X := WithLp 2 (ℝ × Ici (0 : ℝ))
    ∃ z : X, isEdgePoint.{0, 0} z 1 (1 / 10^9) (1 / 10^9) ∧
      ∃ a : X, isEdgePoint.{0, 0} a 1 (1 / 1000) (1 / 1000) ∧ dist z a < 1 := by
  let X := WithLp 2 (ℝ × Ici (0 : ℝ))
  let p : X := WithLp.toLp 2 ((0 : ℝ), rayMark)
  let F : KleinerLottApprox p (WithLp.toLp 2 ((0 : ℝ), rayMark)) (1 / 10^14) :=
    (IsometryEquiv.refl X).toKleinerLottApprox rfl (by norm_num) (by norm_num)
  let G : KleinerLottApprox rayMark rayMark (1 / 10^14) :=
    (IsometryEquiv.refl (Ici (0 : ℝ))).toKleinerLottApprox rfl (by norm_num) (by norm_num)
  let H : KleinerLottApprox p (WithLp.toLp 2 ((0 : ℝ), rayMark)) (1 / 10^14) :=
    (IsometryEquiv.refl X).toKleinerLottApprox rfl (by norm_num) (by norm_num)
  have hρ : LipschitzWith (0 : NNReal) (fun _ : X => (1 : ℝ)) := LipschitzWith.const 1
  have hcompat : ∀ x ∈ ball p (1000 * (1 : ℝ)),
      dist (G.toFun (F.toFun x).snd) (H.toFun x).snd < 1 / 10^13 := by
    intro x _
    have heq : G.toFun (F.toFun x).snd = (H.toFun x).snd := rfl
    rw [heq, dist_self]
    norm_num
  obtain ⟨z, hrad, hzed, _⟩ := exists_strong_edge_ray_lift (Δ := 1)
    (βE := 1 / 10^9) (s := 1 / 10^9) (θ := 1 / 10^13) F G H hρ (fun _ => by norm_num) rfl
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num [rayMark]) hcompat
    2 (by norm_num)
  have hz : z ∈ ball p (10 * (1 : ℝ)) := by
    simp only [mem_ball, mul_one]
    norm_num [rayMark] at hrad
    linarith only [hrad]
  obtain ⟨a, haed, hclose⟩ := exists_strong_edge_near_weak_ray_model (Δ := 1)
    (βE := 1 / 1000) (s := 1 / 1000) (θ := 1 / 10^13) F G H hρ (fun _ => by norm_num) rfl
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num [rayMark]) hcompat
    (by norm_num) (by norm_num) (by norm_num) hzed hz
  have hm : (inferInstance : MetricSpace X).rescale (1 : ℝ)⁻¹ (by positivity) =
      (inferInstance : MetricSpace X) := by simp only [inv_one, MetricSpace.rescale_one]
  rw [hm] at hzed haed
  exact ⟨z, hzed, a, haed, hclose⟩
