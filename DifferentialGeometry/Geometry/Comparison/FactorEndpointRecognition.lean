import DifferentialGeometry.Geometry.Comparison.EndpointRecognition
import DifferentialGeometry.Geometry.Comparison.FactorGeometry

set_option autoImplicit false

open Set Metric
open DifferentialGeometry.Geometry.Comparison.Toponogov

namespace IsometryEquiv

variable {X E Y : Type*} [MetricSpace X] [MetricSpace E] [MetricSpace Y]

theorem exists_interval_or_ray_product_of_factor_endpoint [CompleteSpace X] [Nontrivial Y]
    (e : X ≃ᵢ WithLp 2 (E × Y)) (u : E)
    (hsegments : ∀ x y : X, ∃ f : Icc (0 : ℝ) 1 → X,
      Continuous f ∧ f ⟨0, by norm_num⟩ = x ∧ f ⟨1, by norm_num⟩ = y ∧
      ∀ s t, dist (f s) (f t) = dist x y * dist s t)
    (hcomp : fourPointComparison 0 (univ : Set X)) (hdim : dimH (univ : Set Y) ≤ 1)
    {w : Y} (hend : ∀ x y : Y, dist x w + dist w y = dist x y → x = w ∨ y = w) :
    (∃ L : ℝ, 0 < L ∧ ∃ F : X ≃ᵢ WithLp 2 (E × Icc (0 : ℝ) L),
      ∀ x, (F x).fst = (e x).fst ∧ ((F x).snd : ℝ) = dist w (e x).snd) ∨
    (∃ F : X ≃ᵢ WithLp 2 (E × Ici (0 : ℝ)),
      ∀ x, (F x).fst = (e x).fst ∧ ((F x).snd : ℝ) = dist w (e x).snd) := by
  let := e.completeSpace_l2_product_factor u
  rcases exists_interval_or_ray_isometry_of_endpoint_of_dimH_le_one
      (e.exists_segment_l2_product_factor u hsegments)
      (fourPointComparison_l2_product_factor hcomp e u) hdim hend with
    ⟨L, hL, φ, hφ⟩ | ⟨φ, hφ⟩
  · let F : X ≃ᵢ WithLp 2 (E × Icc (0 : ℝ) L) :=
      e.trans (withLpProdCongr 2 (IsometryEquiv.refl E) φ)
    refine Or.inl ⟨L, hL, F, ?_⟩
    intro x
    exact ⟨rfl, hφ (e x).snd⟩
  · let F : X ≃ᵢ WithLp 2 (E × Ici (0 : ℝ)) :=
      e.trans (withLpProdCongr 2 (IsometryEquiv.refl E) φ)
    refine Or.inr ⟨F, ?_⟩
    intro x
    exact ⟨rfl, hφ (e x).snd⟩

theorem exists_interval_or_ray_product_of_factor_half_interval_chart [CompleteSpace X] [Nontrivial Y]
    (e : X ≃ᵢ WithLp 2 (E × Y)) (u : E)
    (hsegments : ∀ x y : X, ∃ f : Icc (0 : ℝ) 1 → X,
      Continuous f ∧ f ⟨0, by norm_num⟩ = x ∧ f ⟨1, by norm_num⟩ = y ∧
      ∀ s t, dist (f s) (f t) = dist x y * dist s t)
    (hcomp : fourPointComparison 0 (univ : Set X)) (hdim : dimH (univ : Set Y) ≤ 1)
    {w : Y} {r : ℝ} (hr : 0 < r) (h : Ico (0 : ℝ) r ≃ᵢ ball w r)
    (hh : (h ⟨0, le_rfl, hr⟩ : Y) = w) :
    (∃ L : ℝ, 0 < L ∧ ∃ F : X ≃ᵢ WithLp 2 (E × Icc (0 : ℝ) L),
      ∀ x, (F x).fst = (e x).fst ∧ ((F x).snd : ℝ) = dist w (e x).snd) ∨
    (∃ F : X ≃ᵢ WithLp 2 (E × Ici (0 : ℝ)),
      ∀ x, (F x).fst = (e x).fst ∧ ((F x).snd : ℝ) = dist w (e x).snd) :=
  e.exists_interval_or_ray_product_of_factor_endpoint u hsegments hcomp hdim
    (metric_endpoint_of_pointed_half_interval_chart (e.exists_segment_l2_product_factor u hsegments) hr h hh)

end IsometryEquiv
