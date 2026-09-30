import DifferentialGeometry.Geometry.Comparison.HingeSuccessor
import DifferentialGeometry.Geometry.Comparison.CradleSmallHinges
import DifferentialGeometry.Topology.MetricSpace.CradleStepThreeFifths

set_option autoImplicit false


open Set

namespace Metric.MinimizingHinge

open DifferentialGeometry.Geometry.Comparison.Toponogov

variable {X : Type*} [MetricSpace X] {p q : X}

theorem exists_cradle_successor_of_modelSide_lt_three_fifths (H : MinimizingHinge p q)
    {κ ℓ : ℝ} (hκ : 0 ≤ κ) (hℓ : 0 < ℓ)
    (hsmall : endpointHingeComparison κ p (3 * ℓ / 5))
    (hjoins : ∀ z : X, dist z p + dist z q < ℓ →
      ∃ J : MinimizingHinge p q, J.center = z)
    (hlocal : ∀ z : X, dist z p + dist z q < ℓ →
      ∃ Ω : Set X, IsOpen Ω ∧ fourPointComparison κ Ω ∧ z ∈ Ω)
    (hsorted : dist H.center p ≤ dist H.center q)
    (hsum : dist H.center p + dist H.center q < ℓ)
    (hbad : H.modelSide κ < dist p q) :
    let h := (3 * ℓ / 5 - dist H.center p) / 3
    ∃ K : MinimizingHinge p q, K.center ∈ range H.right ∧
      dist H.center K.center = h ∧
      dist K.center p ≤ dist H.center p + h ∧
      dist K.center q = dist H.center q - h ∧
      dist K.center p + dist K.center q < ℓ ∧
      K.modelSide κ ≤ H.modelSide κ ∧
      comparisonAngleNegCurvature κ (dist H.center p) h (dist K.center p) ≤ H.germAngle κ := by
  dsimp only
  let h := (3 * ℓ / 5 - dist H.center p) / 3
  have ha : 0 < dist H.center p := by
    apply dist_pos.mpr
    intro heq
    rw [H.modelSide_of_center_eq_left hκ heq] at hbad
    exact (lt_irrefl _) hbad
  have hlower : 3 * ℓ / 5 ≤ dist H.center p + dist H.center q := by
    by_contra hn
    exact (not_le_of_gt hbad) (H.modelSide_ge_dist_of_endpoint_comparison hκ hsmall (lt_of_not_ge hn))
  obtain ⟨z, hzrange, hxz, hzq, hhlo, hhhi, hhb, hshort₁, hshort₂, hsumle, hzmem⟩ :=
    Metric.exists_cradle_step_on_segment_three_fifths hℓ hsorted hlower hsum H.right H.right_isometry
      H.right_zero H.right_end
  have hh : 0 < h := by change ℓ / 30 < h at hhlo; linarith
  have hhb' : h < dist H.center q := hhb
  have hz : z = H.right ⟨h, ⟨hh.le, hhb'.le⟩⟩ := by
    obtain ⟨t, ht⟩ := hzrange
    have hrad := H.right_radial t.property
    rw [IccExtend_val, ht] at hrad
    have heq : (t : ℝ) = h := hrad.symm.trans hxz
    exact ht.symm.trans (congrArg H.right (Subtype.ext heq))
  have hnewsum : dist z p + dist z q < ℓ := hsumle.trans_lt hsum
  have hc : 0 < dist z p := by
    apply dist_pos.mpr
    intro hzp
    have hbetween : dist H.center p + dist p q = dist H.center q := by
      have hx := hxz
      have hq := hzq
      rw [hzp] at hx hq
      linarith
    exact (not_le_of_gt hbad)
      (dist_le_modelSideNegCurvature_of_between hκ (H.germAngle_mem_Icc κ) hbetween)
  have hnewjoin : ∃ τ : Icc (0 : ℝ) (dist z p) → X,
      Isometry τ ∧ τ ⟨0, ⟨le_rfl, dist_nonneg⟩⟩ = z ∧
        τ ⟨dist z p, ⟨dist_nonneg, le_rfl⟩⟩ = p := by
    obtain ⟨J, hJ⟩ := hjoins z hnewsum
    rcases J with ⟨y, τ, ρ, hτ, hρ, hτ0, hρ0, hτp, hρq⟩
    change y = z at hJ
    subst y
    exact ⟨τ, hτ, hτ0, hτp⟩
  obtain ⟨Ω, hΩ, hcomp, hΩz⟩ := hlocal z hnewsum
  subst z
  obtain ⟨τ, hτ, hτ0, hτp⟩ := hnewjoin
  obtain ⟨K, hK, hKangle, hKside⟩ := H.exists_hinge_with_forward_right κ hh hhb' τ hτ hτ0 hτp
  have hside := hsmall.cradle_modelSide_le hκ ha hh hhb' H.left H.left_isometry
    H.left_zero H.left_end H.right H.right_isometry H.right_zero H.right_end hc
    τ hτ hτ0 hτp hshort₁ hshort₂ hΩ hcomp hΩz
  rw [hzq] at hside
  refine ⟨K, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hK]
    exact hzrange
  · rw [hK]
    exact hxz
  · rw [hK]
    have ht := dist_triangle (H.right ⟨h, ⟨hh.le, hhb'.le⟩⟩) H.center p
    rw [dist_comm _ H.center, hxz] at ht
    linarith
  · rw [hK]
    exact hzq
  · rwa [hK]
  · rw [hKside]
    exact hside
  · rw [hK]
    exact H.short_right_comparison hsmall ha hh hhb'.le hshort₁

end Metric.MinimizingHinge
