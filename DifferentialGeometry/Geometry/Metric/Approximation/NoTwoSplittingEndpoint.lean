import DifferentialGeometry.Geometry.Metric.Approximation.NonslimEndpointRecognition
import DifferentialGeometry.Geometry.Metric.Approximation.RealSplitting
import DifferentialGeometry.Geometry.Collapse.RankStrata
import DifferentialGeometry.Topology.MetricSpace.SegmentCurves

/-!
# LFR42 with the rank-stratum hypotheses of LC16

Blueprint 207A, LFR42 (`lem:collapse-nonslim-endpoint-model`, A:28496–28533). The accepted kernel
`exists_nearby_endpoint_of_no_plane_approximation` excludes only an actual plane approximation and
takes almost-minimizing curves on the model. Here:

* `exists_nearby_endpoint_of_no_two_splitting`: the row's hypothesis "no `(2,β₂)`-splitting" in the
  LC16 form `¬ HasEuclideanSplitting p 2 β₂` (any residual universe), and the model hypotheses in the
  form produced by LFR39 (`exists_prescribed_one_dimensional_model_parameter`: continuous
  constant-speed segments, nonnegative four-point comparison, `dimH ≤ 1`, completeness).
* `splitting_one_and_no_two_of_mem_scaledSplittingStratum_one`: a point of the rank-one stratum of
  LC16 (in its own scale) has a `(1, β 1)`-splitting and no `(2, β 2)`-splitting.
* The verbatim blueprint form (`e < min (β₂/100) (1/(1000Δ))` and `500Δ < diam Y`) is the `example`
  at the end; the bound `e < 1/(1000Δ)` is not needed (strengthening), and the two-point form of the
  large-diameter premise also covers unbounded models (Mathlib's `diam` of an unbounded set is `0`).
-/

set_option autoImplicit false

open Set Metric
open DifferentialGeometry.Geometry.Comparison.Toponogov

namespace GC.MetricGeometry

universe u v w

/-- **LFR42** with the LC16 hypothesis: no `(2,β₂)`-splitting, a one-dimensional model `Y` as
produced by LFR39 with two points more than `500Δ` apart. The model is an interval of length
`> 500Δ` or a ray, with the original basepoint at height `< Δ/2`. -/
theorem exists_nearby_endpoint_of_no_two_splitting
    {X : Type u} {Y : Type w} [MetricSpace X] [MetricSpace Y] [CompleteSpace Y]
    {p : X} {q : Y} {e β₂ Δ : ℝ}
    (F : KleinerLottApprox p (WithLp.toLp 2 ((0 : ℝ), q)) e)
    (hβ₂ : 0 < β₂) (hβ₂small : β₂ < 1 / 100) (hΔ : 100 / β₂ < Δ) (he : e < β₂ / 100)
    (hno : ¬ HasEuclideanSplitting.{u, v} p 2 β₂)
    (hsegments : ∀ a b : Y, ∃ γ : Icc (0 : ℝ) 1 → Y, Continuous γ ∧
      γ ⟨0, by norm_num⟩ = a ∧ γ ⟨1, by norm_num⟩ = b ∧
      ∀ s t, dist (γ s) (γ t) = dist a b * dist s t)
    (hcomp : fourPointComparison 0 (univ : Set Y)) (hdim : dimH (univ : Set Y) ≤ 1)
    (hlarge : ∃ a b : Y, 500 * Δ < dist a b) :
    (∃ C : ℝ, 500 * Δ < C ∧ ∃ f : Y ≃ᵢ Icc (0 : ℝ) C, (f q).val < Δ / 2) ∨
      (∃ f : Y ≃ᵢ Ici (0 : ℝ), (f q).val < Δ / 2) :=
  exists_nearby_endpoint_of_no_plane_approximation F hβ₂ hβ₂small hΔ he
    (fun ⟨G⟩ => hno (hasEuclideanSplitting_two_of_plane_approximation.{u, v} G))
    (Metric.arbitrarily_short_curves_of_metric_segments hsegments) hcomp hdim hlarge

/-- A point of the LC16 rank-one stratum has, in its own scale, a `(1, β 1)`-splitting and no
`(2, β 2)`-splitting. -/
theorem splitting_one_and_no_two_of_mem_scaledSplittingStratum_one
    {M : Type u} [m : MetricSpace M] {ρ : M → ℝ} {hρ : ∀ p, 0 < ρ p} {β : ℕ → ℝ} {p : M}
    (hp : p ∈ scaledSplittingStratum.{u, v} ρ hρ β 1) :
    @HasEuclideanSplitting.{u, v} M (m.rescale (ρ p)⁻¹ (inv_pos.mpr (hρ p))) p 1 (β 1) ∧
      ¬ @HasEuclideanSplitting.{u, v} M (m.rescale (ρ p)⁻¹ (inv_pos.mpr (hρ p))) p 2 (β 2) := by
  obtain ⟨_, hyes, hno⟩ := scaledSplittingRank_eq_iff.mp hp
  exact ⟨hyes one_ne_zero, hno 2 (by decide) (by decide)⟩

/-- LFR42 verbatim: `e < min {β₂/100, (1000Δ)⁻¹}`, `Y` complete, proper, geodesic, nonnegative,
`dim_H Y ≤ 1` (the LFR39 output) and `diam Y > 500Δ`. -/
example {X : Type u} {Y : Type w} [MetricSpace X] [MetricSpace Y] [CompleteSpace Y]
    [ProperSpace Y] {p : X} {q : Y} {e β₂ Δ : ℝ}
    (hβ₂ : 0 < β₂) (hβ₂small : β₂ < 1 / 100) (hΔ : 100 / β₂ < Δ)
    (hno : ¬ HasEuclideanSplitting.{u, v} p 2 β₂)
    (F : KleinerLottApprox p (WithLp.toLp 2 ((0 : ℝ), q)) e)
    (he : e < min (β₂ / 100) (1 / (1000 * Δ)))
    (hsegments : ∀ a b : Y, ∃ γ : Icc (0 : ℝ) 1 → Y, Continuous γ ∧
      γ ⟨0, by norm_num⟩ = a ∧ γ ⟨1, by norm_num⟩ = b ∧
      ∀ s t, dist (γ s) (γ t) = dist a b * dist s t)
    (hcomp : fourPointComparison 0 (univ : Set Y)) (hdim : dimH (univ : Set Y) ≤ 1)
    (hdiam : 500 * Δ < diam (univ : Set Y)) :
    (∃ C : ℝ, 500 * Δ < C ∧ ∃ f : Y ≃ᵢ Icc (0 : ℝ) C, (f q).val < Δ / 2) ∨
      (∃ f : Y ≃ᵢ Ici (0 : ℝ), (f q).val < Δ / 2) := by
  have hΔpos : 0 < Δ := (div_pos (by norm_num) hβ₂).trans hΔ
  refine exists_nearby_endpoint_of_no_two_splitting F hβ₂ hβ₂small hΔ
    (he.trans_le (min_le_left _ _)) hno hsegments hcomp hdim ?_
  by_contra! hall
  exact (diam_le_of_forall_dist_le (by positivity) fun a _ b _ => hall a b).not_gt hdiam

end GC.MetricGeometry
