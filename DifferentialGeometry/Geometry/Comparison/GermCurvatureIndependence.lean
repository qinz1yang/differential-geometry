import DifferentialGeometry.Geometry.Comparison.CanonicalGermAngle
import DifferentialGeometry.Geometry.Comparison.Toponogov.HyperbolicComparisonAngle

set_option autoImplicit false

open Set Filter Topology

namespace DifferentialGeometry.Geometry.Comparison.Toponogov

theorem tendsto_comparisonAngleNegCurvature_sub_curvature_zero_of_radial
    {X : Type*} [MetricSpace X] {κ R S : ℝ}
    (hκ : 0 ≤ κ) (hR : 0 < R) (hS : 0 < S)
    (p : X) (γ β : ℝ → X)
    (hγrad : ∀ s ∈ Ioc 0 R, dist p (γ s) = s)
    (hβrad : ∀ s ∈ Ioc 0 S, dist p (β s) = s) :
    Tendsto (fun z : ℝ × ℝ =>
      comparisonAngleNegCurvature κ z.1 z.2 (dist (γ z.1) (β z.2)) -
      comparisonAngleNegCurvature 0 z.1 z.2 (dist (γ z.1) (β z.2)))
      (𝓝[>] (0 : ℝ) ×ˢ 𝓝[>] (0 : ℝ)) (𝓝 (0 : ℝ)) := by
  by_cases hk : κ = 0
  · subst κ
    simpa only [sub_self] using
      (tendsto_const_nhds : Tendsto (fun _ : ℝ × ℝ => (0 : ℝ)) _ (𝓝 0))
  · have hkpos : 0 < Real.sqrt κ := Real.sqrt_pos.mpr (lt_of_le_of_ne hκ (Ne.symm hk))
    have hgood : ∀ᶠ z : ℝ × ℝ in 𝓝[>] (0 : ℝ) ×ˢ 𝓝[>] (0 : ℝ),
        0 < Real.sqrt κ ∧ 0 < z.1 ∧ 0 < z.2 ∧
          |z.1 - z.2| ≤ dist (γ z.1) (β z.2) ∧ dist (γ z.1) (β z.2) ≤ z.1 + z.2 := by
      have heR : ∀ᶠ t : ℝ in 𝓝[>] (0 : ℝ), t ∈ Ioc 0 R := Ioc_mem_nhdsGT hR
      have heS : ∀ᶠ t : ℝ in 𝓝[>] (0 : ℝ), t ∈ Ioc 0 S := Ioc_mem_nhdsGT hS
      filter_upwards [heR.prod_inl _, heS.prod_inr _] with z hz₁ hz₂
      refine ⟨hkpos, hz₁.1, hz₂.1, ?_, ?_⟩
      · simpa only [dist_comm _ p, hγrad _ hz₁, hβrad _ hz₂] using
          abs_dist_sub_le (γ z.1) (β z.2) p
      · simpa only [dist_comm _ p, hγrad _ hz₁, hβrad _ hz₂] using
          dist_triangle (γ z.1) p (β z.2)
    have hid : Tendsto (fun t : ℝ => t) (𝓝[>] (0 : ℝ)) (𝓝 (0 : ℝ)) :=
      tendsto_nhdsWithin_of_tendsto_nhds tendsto_id
    have hfst : Tendsto (fun z : ℝ × ℝ => z.1)
        (𝓝[>] (0 : ℝ) ×ˢ 𝓝[>] (0 : ℝ)) (𝓝 (0 : ℝ)) := hid.comp tendsto_fst
    have hsnd : Tendsto (fun z : ℝ × ℝ => z.2)
        (𝓝[>] (0 : ℝ) ×ˢ 𝓝[>] (0 : ℝ)) (𝓝 (0 : ℝ)) := hid.comp tendsto_snd
    have hsmall : Tendsto (fun z : ℝ × ℝ => Real.sqrt κ * max z.1 z.2)
        (𝓝[>] (0 : ℝ) ×ˢ 𝓝[>] (0 : ℝ)) (𝓝 (0 : ℝ)) := by
      simpa using tendsto_const_nhds.mul (hfst.max hsnd)
    simpa only [comparisonAngleNegCurvature, ite_eq_right hk, ite_true] using
      tendsto_hyperbolic_comparison_angle_sub_euclidean hgood hsmall

theorem tendsto_curvature_zero_comparisonAngle_of_tendsto
    {X : Type*} [MetricSpace X] {κ R S α : ℝ}
    (hκ : 0 ≤ κ) (hR : 0 < R) (hS : 0 < S)
    (p : X) (γ β : ℝ → X)
    (hγrad : ∀ s ∈ Ioc 0 R, dist p (γ s) = s)
    (hβrad : ∀ s ∈ Ioc 0 S, dist p (β s) = s)
    (hangle : Tendsto (fun z : ℝ × ℝ =>
      comparisonAngleNegCurvature κ z.1 z.2 (dist (γ z.1) (β z.2)))
      (𝓝[>] (0 : ℝ) ×ˢ 𝓝[>] (0 : ℝ)) (𝓝 α)) :
    Tendsto (fun z : ℝ × ℝ =>
      comparisonAngleNegCurvature 0 z.1 z.2 (dist (γ z.1) (β z.2)))
      (𝓝[>] (0 : ℝ) ×ˢ 𝓝[>] (0 : ℝ)) (𝓝 α) := by
  have hdiff := tendsto_comparisonAngleNegCurvature_sub_curvature_zero_of_radial hκ hR hS p γ β
    hγrad hβrad
  simpa only [sub_sub_cancel, sub_zero] using hangle.sub hdiff

theorem germComparisonAngle_eq_curvature_zero_of_tendsto
    {X : Type*} [MetricSpace X] {κ R S α : ℝ}
    (hκ : 0 ≤ κ) (hR : 0 < R) (hS : 0 < S)
    (p : X) (γ β : ℝ → X)
    (hγrad : ∀ s ∈ Ioc 0 R, dist p (γ s) = s)
    (hβrad : ∀ s ∈ Ioc 0 S, dist p (β s) = s)
    (hangle : Tendsto (fun z : ℝ × ℝ =>
      comparisonAngleNegCurvature κ z.1 z.2 (dist (γ z.1) (β z.2)))
      (𝓝[>] (0 : ℝ) ×ˢ 𝓝[>] (0 : ℝ)) (𝓝 α)) :
    germComparisonAngle κ γ β = germComparisonAngle 0 γ β := by
  rw [germComparisonAngle_eq_of_tendsto hangle,
    germComparisonAngle_eq_of_tendsto
      (tendsto_curvature_zero_comparisonAngle_of_tendsto hκ hR hS p γ β hγrad hβrad hangle)]

end DifferentialGeometry.Geometry.Comparison.Toponogov
