import DifferentialGeometry.Geometry.Comparison.CrossAngleArithmetic
import DifferentialGeometry.Geometry.Comparison.BalancedAngleDifference

set_option autoImplicit false

open Real Set

namespace DifferentialGeometry.Geometry.Comparison.Toponogov

variable {X : Type*} [MetricSpace X]

theorem balanced_cross_angles_near_pi_div_two
    {Ω : Set X} (hcomp : fourPointComparison 1 Ω)
    {x y z u v : X} (hx : x ∈ Ω) (hy : y ∈ Ω) (hz : z ∈ Ω)
    (hu : u ∈ Ω) (hv : v ∈ Ω) {a A ε δ τ : ℝ} (ha : 0 < a)
    (hxu : dist x u ∈ Icc a A) (hyu : dist y u ∈ Icc a A) (hzu : dist z u ∈ Icc a A)
    (hxv : dist x v ∈ Icc a A) (hyv : dist y v ∈ Icc a A) (hzv : dist z v ∈ Icc a A)
    (hs : 0 < dist z x) (hs1 : dist z x ≤ 1) (hsa : dist z x ≤ a / 2)
    (hbalance : dist z x = dist z y) (hε : 0 ≤ ε) (hδ : 0 ≤ δ) (hτ : 0 ≤ τ)
    (hcoord : |dist x u - dist y u| ≤ ε * dist x y)
    (hpairx : Real.pi - δ < comparisonAngleNegCurvature 1 (dist x u) (dist x v) (dist u v))
    (hpairy : Real.pi - δ < comparisonAngleNegCurvature 1 (dist y u) (dist y v) (dist u v))
    (hpairz : Real.pi - δ < comparisonAngleNegCurvature 1 (dist z u) (dist z v) (dist u v))
    (hnew : Real.pi - τ < comparisonAngleNegCurvature 1 (dist z x) (dist z y) (dist x y)) :
    let K := 4 * cosh (A + 1) / sinh a
    let E := 2 * δ + 3 * τ / 2 + 4 * (Real.pi * sqrt (K * dist z x)) +
      (Real.pi * sqrt (ε + K * dist z x)) / 2
    ∀ c ∈ ({u, v} : Set X), ∀ d ∈ ({x, y} : Set X),
      |comparisonAngleNegCurvature 1 (dist z c) (dist z d) (dist c d) - Real.pi / 2| ≤ E := by
  let θ (p b c : X) := comparisonAngleNegCurvature 1 (dist p b) (dist p c) (dist b c)
  have hsym (p b c : X) : θ p b c = θ p c b := by
    dsimp [θ]
    rw [comparisonAngleNegCurvature_comm, dist_comm b c]
  have hne {p b : X} (h : dist p b ∈ Icc a A) : b ≠ p := (dist_pos.mp (ha.trans_le h.1)).symm
  have hnx : x ≠ z := (dist_pos.mp hs).symm
  have hny : y ≠ z := (dist_pos.mp (hbalance ▸ hs)).symm
  have hfouru : θ z u x + θ z x y + θ z y u ≤ 2 * Real.pi :=
    hcomp z hz u hu x hx y hy (hne hzu) hnx hny
  have hfourv : θ z v x + θ z x y + θ z y v ≤ 2 * Real.pi :=
    hcomp z hz v hv x hx y hy (hne hzv) hnx hny
  rw [hsym z y u] at hfouru
  rw [hsym z y v] at hfourv
  change Real.pi - τ < θ z x y at hnew
  have hasum : θ z u x + θ z u y ≤ Real.pi + τ := by linarith
  have hgsum : θ z v x + θ z v y ≤ Real.pi + τ := by linarith
  have hd := abs_comparisonAngleNegCurvature_sub_le_of_balanced_coordinates
    ha hzu hs hs1 hsa hbalance hε hcoord
  have hpx := (comparisonAngleNegCurvature_complement_bounds hcomp hx hz hu hv ha
    hxu hzu hxv hzv (by rwa [dist_comm x z]) (by rwa [dist_comm x z])
    (by rwa [dist_comm x z]) hpairx hpairz).1
  have hpy := (comparisonAngleNegCurvature_complement_bounds hcomp hy hz hu hv ha
    hyu hzu hyv hzv (by rwa [dist_comm y z, ← hbalance])
    (by rwa [dist_comm y z, ← hbalance]) (by rwa [dist_comm y z, ← hbalance]) hpairy hpairz).1
  rw [dist_comm x z] at hpx
  have hdistyz : dist y z = dist z x := by rw [dist_comm]; exact hbalance.symm
  rw [hdistyz] at hpy
  obtain ⟨h1, h2, h3, h4⟩ := four_cross_angles_near_pi_div_two hδ hτ
    (show 0 ≤ Real.pi * sqrt ((4 * cosh (A + 1) / sinh a) * dist z x) by positivity)
    hd hasum hgsum hpx hpy
  intro K E c hc d hdmem
  rcases (by simpa only [mem_insert_iff, mem_singleton_iff] using hc : c = u ∨ c = v) with rfl | rfl <;>
    rcases (by simpa only [mem_insert_iff, mem_singleton_iff] using hdmem : d = x ∨ d = y) with rfl | rfl
  · exact h1
  · exact h2
  · exact h3
  · exact h4

end DifferentialGeometry.Geometry.Comparison.Toponogov
