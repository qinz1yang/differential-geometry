import DifferentialGeometry.Geometry.Comparison.EightRadialContraction
import DifferentialGeometry.Topology.MetricSpace.RadialChartNet

set_option autoImplicit false


open Set Metric Real

namespace DifferentialGeometry.Geometry.Comparison.Toponogov

theorem exists_closedBall_net_of_intrinsic_8_comparison_and_chart
    {X : Type*} [MetricSpace X] [CompleteSpace X]
    (hcurves : ∀ a b : X, ∀ ε : ℝ, 0 < ε →
      ∃ c : unitInterval → X, Continuous c ∧ c 0 = a ∧ c 1 = b ∧
        eVariationOn c univ < ENNReal.ofReal (dist a b + ε))
    (o : X) {R L δ₀ ε : ℝ} (hR : 0 < R) [LocallyCompactSpace (ball o (8 * R))]
    (hlocal : ∀ z : ball o (8 * R), ∃ Ω : Set (ball o (8 * R)),
      @IsOpen (ball o (8 * R))
        (intrinsicBallMetricSpace hcurves o (by positivity : 0 < 8 * R)).toUniformSpace.toTopologicalSpace Ω ∧
      @fourPointComparison (ball o (8 * R))
        (intrinsicBallMetricSpace hcurves o (by positivity : 0 < 8 * R)) 1 Ω ∧ z ∈ Ω)
    {q : X} (hq : q ∈ ball o (R / 2)) {n : ℕ} (hn : 0 < n)
    (hL : 1 ≤ L) (hδ₀ : 0 < δ₀) (hε : 0 < ε)
    (φ : ball q δ₀ → PiLp 2 (fun _ : Fin n => ℝ))
    (hφ0 : φ ⟨q, by simpa only [mem_ball, dist_self] using hδ₀⟩ = 0)
    (hφlower : ∀ u v : ball q δ₀, L⁻¹ * dist u v ≤ dist (φ u) (φ v))
    (hφupper : ∀ u v : ball q δ₀, dist (φ u) (φ v) ≤ L * dist u v) :
    ∃ T : Finset X, T.card ≤ (1 + ⌈4 * L ^ 2 * sqrt n * sinh (2 * R) / ε⌉₊) ^ n ∧
      (T : Set X) ⊆ closedBall o R ∧ ∀ x ∈ closedBall o R, ∃ y ∈ T, dist x y < ε := by
  let δ := min R δ₀ / 2
  have hδ : 0 < δ := div_pos (lt_min hR hδ₀) (by norm_num)
  have hδR : δ < R := by
    have h := min_le_left R δ₀
    dsimp only [δ]
    linarith
  have hδδ₀ : δ < δ₀ := by
    have h := min_le_right R δ₀
    dsimp only [δ]
    linarith
  obtain ⟨h, hmem, hlower⟩ := exists_radial_contraction_of_intrinsic_8_buffer
    hcurves o hR hlocal hq ⟨hδ, hδR⟩
  exact exists_net_of_radial_contraction_and_chart hn hL hR hδ hδ₀ hδδ₀ hε
    h hmem hlower φ hφ0 hφlower hφupper

end DifferentialGeometry.Geometry.Comparison.Toponogov
