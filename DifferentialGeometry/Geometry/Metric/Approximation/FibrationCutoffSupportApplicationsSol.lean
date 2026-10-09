import DifferentialGeometry.Geometry.Metric.Approximation.PaddedStripBoundary
import DifferentialGeometry.Geometry.Metric.Approximation.SlimChartCutoffSupport
import DifferentialGeometry.Geometry.Metric.Approximation.EdgeChartCutoffSupport
import DifferentialGeometry.Geometry.Metric.SupportDomainBuffer

set_option autoImplicit false
open Set Metric DifferentialGeometry.Analysis

namespace GC.MetricGeometry.X81Sol

variable {X : Type*} [MetricSpace X]

theorem exists_universal_weak_edge_height_constant :
    ∃ τ : ℝ, τ ∈ Ioo 0 (1 / 100) ∧
      ∀ {p : X} {Δ δ C : ℝ}, 0 < Δ → 0 < δ → δ ≤ τ * Δ → 200 * Δ < C →
      ∀ (Q : X → WithLp 2 (ℝ × ℝ)), Q p = 0 →
      (∀ x ∈ ball p (200 * Δ), ∀ y ∈ ball p (200 * Δ),
        |dist (Q x) (Q y) - dist x y| ≤ δ) →
      (∀ y : WithLp 2 (ℝ × ℝ), y.snd ∈ Icc 0 C → ‖y‖ < 200 * Δ - δ →
        infDist y (Q '' ball p (200 * Δ)) ≤ δ) →
      ∀ (E : Set X),
      (∀ z ∈ E, z ∈ ball p (120 * Δ) → ∃ W : X → WithLp 2 (ℝ × ℝ),
        W z = 0 ∧ (∀ x ∈ ball z Δ, 0 ≤ (W x).snd) ∧
        ∀ x ∈ ball z Δ, ∀ y ∈ ball z Δ, |dist (W x) (W y) - dist x y| ≤ δ) →
      ∀ z ∈ E, z ∈ ball p (120 * Δ) → (Q z).snd < Δ / 10 := by
  refine ⟨1 / 1000000, by norm_num, ?_⟩
  intro p Δ δ C hΔ hδ hδsmall hC Q hQp hQdist hcover E hweak z hz hzD
  obtain ⟨W, hWz, hWh, hWd⟩ := hweak z hz hzD
  exact padded_strip_height_lt_of_half_plane_model hΔ hδ (by linarith) hC
    Q W hQp hWz hQdist hcover hWh hWd hzD

theorem slim_actual_cutoff_original_domain_buffer {Z : Type*} [MetricSpace Z]
    {p q : X} {Δ L : ℝ} (hΔ : 0 < Δ) (hL : 0 < L)
    (hgap : 4 * L < (1000000 - 901002) * Δ) (z₀ : Z)
    (φ : ball q (1000000 * Δ) → WithLp 2 (ℝ × Z))
    (η : ball q (1000000 * Δ) → ℝ)
    (hbase : φ ⟨q, mem_ball_self (by positivity)⟩ = WithLp.toLp 2 (0, z₀))
    (hdist : ∀ x y, |dist (φ x) (φ y) - dist x.val y.val| ≤ Δ)
    (hfactor : ∀ z : Z, dist z z₀ ≤ 1000 * Δ)
    (hvalue : ∀ x, |η x - (φ x).fst| ≤ Δ) :
    let ζ := (Subtype.val : ball q (1000000 * Δ) → X).extend
      (fun x => intervalPlateauProfile (-900000) (-800000) 800000 900000 (η x / Δ)) 0
    tsupport ζ ⊆ closedBall q (901002 * Δ) ∧
      ((tsupport ζ ∩ ball p L).Nonempty → ball p L ⊆ ball q (1000000 * Δ)) := by
  have hs := tsupport_slim_chart_cutoff_subset hΔ z₀ φ η hbase hdist hfactor hvalue
  refine ⟨hs.1, ?_⟩
  intro hmeet
  have hb := support_meeting_ball_buffer (r := 1) (rj := 1) (L := L)
    (c := 901002 * Δ) (b := 1000000 * Δ) (by norm_num) (by norm_num) hL
    (by norm_num) (by linarith) (by simpa using hs.1)
    (show ball q (1000000 * Δ * 1) ⊆ ball q (1000000 * Δ) by simp)
    (by simpa using hmeet)
  simpa using hb.1.trans hb.2.1

end GC.MetricGeometry.X81Sol
