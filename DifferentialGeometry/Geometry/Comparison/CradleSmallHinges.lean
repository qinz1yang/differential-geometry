import DifferentialGeometry.Geometry.Comparison.EndpointHingeComparison
import DifferentialGeometry.Geometry.Comparison.CradleComparison

set_option autoImplicit false

open Set Metric

namespace DifferentialGeometry.Geometry.Comparison.Toponogov

theorem endpointHingeComparison.cradle_modelSide_le
    {X : Type*} [MetricSpace X] {κ r h : ℝ} (hκ : 0 ≤ κ)
    {x u v : X} (hsmall : endpointHingeComparison κ u r)
    (ha : 0 < dist x u) (hh : 0 < h) (hhb : h < dist x v)
    (η : Icc (0 : ℝ) (dist x u) → X) (hη : Isometry η)
    (hη0 : η ⟨0, ⟨le_rfl, dist_nonneg⟩⟩ = x)
    (hηu : η ⟨dist x u, ⟨dist_nonneg, le_rfl⟩⟩ = u)
    (σ : Icc (0 : ℝ) (dist x v) → X) (hσ : Isometry σ)
    (hσ0 : σ ⟨0, ⟨le_rfl, dist_nonneg⟩⟩ = x)
    (hσv : σ ⟨dist x v, ⟨dist_nonneg, le_rfl⟩⟩ = v)
    (hc : 0 < dist (σ ⟨h, ⟨hh.le, hhb.le⟩⟩) u)
    (τ : Icc (0 : ℝ) (dist (σ ⟨h, ⟨hh.le, hhb.le⟩⟩) u) → X)
    (hτ : Isometry τ)
    (hτ0 : τ ⟨0, ⟨le_rfl, dist_nonneg⟩⟩ = σ ⟨h, ⟨hh.le, hhb.le⟩⟩)
    (hτu : τ ⟨dist (σ ⟨h, ⟨hh.le, hhb.le⟩⟩) u, ⟨dist_nonneg, le_rfl⟩⟩ = u)
    (hshort₁ : dist x u + h < r)
    (hshort₂ : dist (σ ⟨h, ⟨hh.le, hhb.le⟩⟩) u + h < r)
    {Ω : Set X} (hΩ : IsOpen Ω) (hcomp : fourPointComparison κ Ω)
    (hp : σ ⟨h, ⟨hh.le, hhb.le⟩⟩ ∈ Ω) :
    modelSideNegCurvature κ (dist (σ ⟨h, ⟨hh.le, hhb.le⟩⟩) u)
      (dist (σ ⟨h, ⟨hh.le, hhb.le⟩⟩) v)
      (germComparisonAngle κ (IccExtend dist_nonneg τ)
        (fun t => IccExtend dist_nonneg σ (h + t))) ≤
    modelSideNegCurvature κ (dist x u) (dist x v)
      (germComparisonAngle κ (IccExtend dist_nonneg η) (IccExtend dist_nonneg σ)) := by
  let z := σ ⟨h, ⟨hh.le, hhb.le⟩⟩
  have hηrad : ∀ s ∈ Ioc (0 : ℝ) (dist x u), dist x (IccExtend dist_nonneg η s) = s := by
    intro s hs
    have ht := hη.IccExtend_forward_radial (h := 0) ⟨le_rfl, dist_nonneg⟩
      (s := s) (show s ∈ Icc (0 : ℝ) (dist x u - 0) by simpa using (show s ∈ Icc (0 : ℝ) (dist x u) from ⟨hs.1.le, hs.2⟩))
    simpa only [zero_add, hη0] using ht
  have hσrad : ∀ s ∈ Ioc (0 : ℝ) h, dist x (IccExtend dist_nonneg σ s) = s := by
    intro s hs
    have ht := hσ.IccExtend_forward_radial (h := 0) ⟨le_rfl, dist_nonneg⟩
      (s := s) (show s ∈ Icc (0 : ℝ) (dist x v - 0) by
        simpa only [sub_zero] using (show s ∈ Icc (0 : ℝ) (dist x v) from ⟨hs.1.le, hs.2.trans hhb.le⟩))
    simpa only [zero_add, hσ0] using ht
  have hτrad : ∀ s ∈ Ioc (0 : ℝ) (dist z u), dist z (IccExtend dist_nonneg τ s) = s := by
    intro s hs
    have ht := hτ.IccExtend_forward_radial (h := 0) ⟨le_rfl, dist_nonneg⟩
      (s := s) (show s ∈ Icc (0 : ℝ) (dist z u - 0) by simpa using (show s ∈ Icc (0 : ℝ) (dist z u) from ⟨hs.1.le, hs.2⟩))
    simpa only [zero_add, hτ0, z] using ht
  have hτmin : ∀ s ∈ Ioc (0 : ℝ) (dist z u), ∀ t ∈ Ioc (0 : ℝ) (dist z u),
      dist (IccExtend dist_nonneg τ s) (IccExtend dist_nonneg τ t) = |s - t| := by
    intro s hs t ht
    exact hτ.dist_IccExtend dist_nonneg ⟨hs.1.le, hs.2⟩ ⟨ht.1.le, ht.2⟩
  have hfirst := hsmall x (dist x u) h (IccExtend dist_nonneg η)
    (IccExtend dist_nonneg σ) ha hh hshort₁ (by rw [IccExtend_right, hηu])
    hηrad hσrad
    (fun s hs t ht => hη.dist_IccExtend dist_nonneg ⟨hs.1.le, hs.2⟩ ⟨ht.1.le, ht.2⟩)
    (fun s hs t ht => hσ.dist_IccExtend dist_nonneg ⟨hs.1.le, hs.2.trans hhb.le⟩
      ⟨ht.1.le, ht.2.trans hhb.le⟩)
  rw [IccExtend_of_mem dist_nonneg σ ⟨hh.le, hhb.le⟩, dist_comm u] at hfirst
  have hbackrad : ∀ s ∈ Ioc (0 : ℝ) h,
      dist z (IccExtend dist_nonneg σ (h - s)) = s := by
    intro s hs
    exact hσ.IccExtend_backward_radial ⟨hh.le, hhb.le⟩
      (by simpa only [sub_zero] using (show s ∈ Icc (0 : ℝ) h from ⟨hs.1.le, hs.2⟩))
  have hbackmin : ∀ s ∈ Ioc (0 : ℝ) h, ∀ t ∈ Ioc (0 : ℝ) h,
      dist (IccExtend dist_nonneg σ (h - s)) (IccExtend dist_nonneg σ (h - t)) = |s - t| := by
    intro s hs t ht
    exact hσ.IccExtend_backward_dist ⟨hh.le, hhb.le⟩
      (by simpa only [sub_zero] using (show s ∈ Icc (0 : ℝ) h from ⟨hs.1.le, hs.2⟩))
      (by simpa only [sub_zero] using (show t ∈ Icc (0 : ℝ) h from ⟨ht.1.le, ht.2⟩))
  have hsecond := hsmall z (dist z u) h (IccExtend dist_nonneg τ)
    (fun t => IccExtend dist_nonneg σ (h - t)) hc hh hshort₂
    (by rw [IccExtend_right, hτu]) hτrad hbackrad hτmin hbackmin
  rw [sub_self, IccExtend_left, hσ0, dist_comm u x] at hsecond
  exact modelSideNegCurvature_cradle_step_le hκ ha hh hhb σ hσ hσ0 hσv hc
    hΩ hcomp hp hτrad hτmin hfirst hsecond

end DifferentialGeometry.Geometry.Comparison.Toponogov
