import DifferentialGeometry.Geometry.Comparison.ModelAngleShortening
import DifferentialGeometry.Analysis.SpecialFunctions.Trigonometric.ShortenedAngleLimit
import Mathlib.Topology.Order.LiminfLimsup

open Filter
open scoped Topology

namespace DifferentialGeometry.Geometry.Comparison.Toponogov

theorem le_liminf_comparison_angle_of_shortening {κ L r c d θ : ℕ → ℝ} {θ₀ : ℝ}
    (hκ : ∀ i, 0 < κ i) (hr : ∀ i, 0 < r i) (hrL : ∀ i, r i ≤ L i)
    (hc : ∀ i, 0 ≤ c i) (hcL : ∀ i, c i ≤ 2 * L i)
    (hd : ∀ i, 0 ≤ d i) (hdr : ∀ i, d i ≤ 2 * r i)
    (htail : ∀ i, c i - 2 * (L i - r i) ≤ d i)
    (hθ₀ : 0 < θ₀) (hθ₀pi : θ₀ ≤ Real.pi)
    (hθ : Tendsto θ atTop (𝓝 θ₀))
    (hB : Tendsto (fun i => Real.sqrt (κ i) * r i) atTop atTop)
    (hangle : ∀ᶠ i in atTop, θ i ≤ comparisonAngleNegCurvature (κ i) (L i) (L i) (c i)) :
    θ₀ ≤ liminf (fun i => comparisonAngleNegCurvature (κ i) (r i) (r i) (d i)) atTop := by
  have hlim := Real.tendsto_shortened_angle_lower_bound hθ₀ hθ₀pi hθ hB
  have hθpos := hθ.eventually (lt_mem_nhds hθ₀)
  have hb : ∀ᶠ i in atTop,
      2 * Real.arcsin (max 0 (Real.sin (θ i / 2) -
        ((Real.sin (θ i / 2))⁻¹ - Real.sin (θ i / 2)) /
          (Real.exp (2 * (Real.sqrt (κ i) * r i)) - 1))) ≤
        comparisonAngleNegCurvature (κ i) (r i) (r i) (d i) := by
    filter_upwards [hθpos, hangle] with i hi ha
    exact Real.two_arcsin_max_le_of_le_sin_half
      (comparisonAngleNegCurvature_mem_Icc (κ i) (r i) (r i) (d i)).1
      (comparisonAngleNegCurvature_mem_Icc (κ i) (r i) (r i) (d i)).2
      (sin_half_comparison_angle_lower_bound_of_shortening (hκ i) (hr i) (hrL i)
        (hc i) (hcL i) (hd i) (hdr i) (htail i) hi ha)
  have hu : ∀ᶠ i in atTop, comparisonAngleNegCurvature (κ i) (r i) (r i) (d i) ≤ Real.pi :=
    Eventually.of_forall fun i => (comparisonAngleNegCurvature_mem_Icc (κ i) (r i) (r i) (d i)).2
  apply le_of_forall_lt
  intro a ha
  obtain ⟨b, hab, hbθ⟩ := exists_between ha
  apply hab.trans_le
  apply le_liminf_of_le (isBoundedUnder_of_eventually_le hu).isCobounded_flip
  filter_upwards [hlim.eventually (lt_mem_nhds hbθ), hb] with i hi hbi
  exact hi.le.trans hbi

end DifferentialGeometry.Geometry.Comparison.Toponogov
