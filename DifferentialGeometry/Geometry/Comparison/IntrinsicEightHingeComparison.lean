import DifferentialGeometry.Geometry.Comparison.EightNestedRadial
import DifferentialGeometry.Geometry.Comparison.IntrinsicLocalComparison

set_option autoImplicit false


open Set Filter Metric Topology

namespace Metric.MinimizingHinge

open DifferentialGeometry.Geometry.Comparison.Toponogov

variable {X : Type*} [MetricSpace X] [CompleteSpace X]
variable (hcurves : ∀ a b : X, ∀ ε : ℝ, 0 < ε →
  ∃ c : unitInterval → X, Continuous c ∧ c 0 = a ∧ c 1 = b ∧
    eVariationOn c univ < ENNReal.ofReal (dist a b + ε))
variable (o : X) {κ R : ℝ} (hκ : 0 < κ) (hR : 0 < R)
variable [LocallyCompactSpace (ball o (8 * R))]
variable (hlocal : ∀ z : ball o (8 * R), ∃ Ω : Set (ball o (8 * R)),
  @IsOpen (ball o (8 * R))
    (intrinsicBallMetricSpace hcurves o (by positivity : 0 < 8 * R)).toUniformSpace.toTopologicalSpace Ω ∧
  @fourPointComparison (ball o (8 * R))
    (intrinsicBallMetricSpace hcurves o (by positivity : 0 < 8 * R)) κ Ω ∧ z ∈ Ω)

include hcurves hκ hR hlocal

theorem comparisonAngle_le_of_intrinsic_8_buffer {p q : X} (H : MinimizingHinge p q)
    (hcenter : H.center ∈ ball o (R / 2)) (hp : p ∈ closedBall o R) (hq : q ∈ closedBall o R)
    (ha : 0 < dist H.center p) (hb : 0 < dist H.center q) :
    comparisonAngleNegCurvature κ (dist H.center p) (dist H.center q) (dist p q) ≤ H.germAngle κ := by
  let c : ball o (8 * R) := ⟨H.center, by
    have h : dist H.center o < R / 2 := hcenter
    change dist H.center o < 8 * R
    linarith⟩
  obtain ⟨Ω, hΩ, hcomp, hc⟩ :=
    (exists_local_fourPointComparison_intrinsicBall_iff hcurves o
      (by positivity : 0 < 8 * R) c).mp (hlocal c)
  have hlimit := tendsto_germComparisonAngle_of_local_fourPointComparison hκ.le ha hb hΩ hcomp hc
    (fun s hs => H.left_radial ⟨hs.1.le, hs.2⟩)
    (fun t ht => H.right_radial ⟨ht.1.le, ht.2⟩)
    (fun s hs t ht => H.left_dist ⟨hs.1.le, hs.2⟩ ⟨ht.1.le, ht.2⟩)
    (fun s hs t ht => H.right_dist ⟨hs.1.le, hs.2⟩ ⟨ht.1.le, ht.2⟩)
  apply ge_of_tendsto hlimit
  have hea : ∀ᶠ s in 𝓝[>] (0 : ℝ), s ∈ Ioc (0 : ℝ) (dist H.center p) := Ioc_mem_nhdsGT ha
  have heb : ∀ᶠ t in 𝓝[>] (0 : ℝ), t ∈ Ioc (0 : ℝ) (dist H.center q) := Ioc_mem_nhdsGT hb
  filter_upwards [hea.prod_inl _, heb.prod_inr _] with z hs ht
  have h := comparisonAngleNegCurvature_le_of_nested_radial_prefixes_intrinsic_8_buffer
    hcurves o hκ hR hlocal hcenter hp hq H.left H.right H.left_isometry H.right_isometry
    H.left_zero H.right_zero H.left_end H.right_end hs.1 hs.2 le_rfl ht.1 ht.2 le_rfl
  rw [H.left_end, H.right_end] at h
  rw [IccExtend_of_mem dist_nonneg H.left ⟨hs.1.le, hs.2⟩,
    IccExtend_of_mem dist_nonneg H.right ⟨ht.1.le, ht.2⟩]
  exact h

theorem modelSide_ge_dist_of_intrinsic_8_buffer {p q : X} (H : MinimizingHinge p q)
    (hcenter : H.center ∈ ball o (R / 2)) (hp : p ∈ closedBall o R) (hq : q ∈ closedBall o R) :
    dist p q ≤ H.modelSide κ := by
  by_cases ha : H.center = p
  · rw [H.modelSide_of_center_eq_left hκ.le ha]
  by_cases hb : H.center = q
  · rw [H.modelSide_of_center_eq_right hκ.le hb]
  exact (H.comparisonAngle_le_iff_dist_le_modelSide hκ.le (dist_pos.mpr ha) (dist_pos.mpr hb)).mp
    (H.comparisonAngle_le_of_intrinsic_8_buffer hcurves o hκ hR hlocal hcenter hp hq
      (dist_pos.mpr ha) (dist_pos.mpr hb))

end Metric.MinimizingHinge
