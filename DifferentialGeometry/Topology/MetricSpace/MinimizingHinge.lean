import DifferentialGeometry.Topology.MetricSpace.SegmentExtension

set_option autoImplicit false

open Set

namespace Metric

structure MinimizingHinge {X : Type*} [MetricSpace X] (p q : X) where
  center : X
  left : Icc (0 : ℝ) (dist center p) → X
  right : Icc (0 : ℝ) (dist center q) → X
  left_isometry : Isometry left
  right_isometry : Isometry right
  left_zero : left ⟨0, ⟨le_rfl, dist_nonneg⟩⟩ = center
  right_zero : right ⟨0, ⟨le_rfl, dist_nonneg⟩⟩ = center
  left_end : left ⟨dist center p, ⟨dist_nonneg, le_rfl⟩⟩ = p
  right_end : right ⟨dist center q, ⟨dist_nonneg, le_rfl⟩⟩ = q

namespace MinimizingHinge

variable {X : Type*} [MetricSpace X] {p q : X}

def reverse (H : MinimizingHinge p q) : MinimizingHinge q p where
  center := H.center
  left := H.right
  right := H.left
  left_isometry := H.right_isometry
  right_isometry := H.left_isometry
  left_zero := H.right_zero
  right_zero := H.left_zero
  left_end := H.right_end
  right_end := H.left_end

theorem reverse_reverse (H : MinimizingHinge p q) : H.reverse.reverse = H := by
  cases H
  rfl

theorem left_radial (H : MinimizingHinge p q) {s : ℝ}
    (hs : s ∈ Icc (0 : ℝ) (dist H.center p)) :
    dist H.center (IccExtend dist_nonneg H.left s) = s := by
  have ht := H.left_isometry.IccExtend_forward_radial (h := 0) ⟨le_rfl, dist_nonneg⟩
    (s := s) (by simpa only [sub_zero] using hs)
  simpa only [zero_add, H.left_zero] using ht

theorem right_radial (H : MinimizingHinge p q) {s : ℝ}
    (hs : s ∈ Icc (0 : ℝ) (dist H.center q)) :
    dist H.center (IccExtend dist_nonneg H.right s) = s :=
  H.reverse.left_radial hs

theorem left_dist (H : MinimizingHinge p q) {s t : ℝ}
    (hs : s ∈ Icc (0 : ℝ) (dist H.center p)) (ht : t ∈ Icc (0 : ℝ) (dist H.center p)) :
    dist (IccExtend dist_nonneg H.left s) (IccExtend dist_nonneg H.left t) = |s - t| :=
  H.left_isometry.dist_IccExtend dist_nonneg hs ht

theorem right_dist (H : MinimizingHinge p q) {s t : ℝ}
    (hs : s ∈ Icc (0 : ℝ) (dist H.center q)) (ht : t ∈ Icc (0 : ℝ) (dist H.center q)) :
    dist (IccExtend dist_nonneg H.right s) (IccExtend dist_nonneg H.right t) = |s - t| :=
  H.reverse.left_dist hs ht

end MinimizingHinge

end Metric
