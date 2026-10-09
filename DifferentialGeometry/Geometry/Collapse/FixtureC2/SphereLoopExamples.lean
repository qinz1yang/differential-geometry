import DifferentialGeometry.Geometry.Collapse.FixtureC2.SphereLoopRank

/-!
# Consumer of the sphere-loop kernel (S-FIXTURE-C2b, K2, G2 file 7)

`loopFixture_example_FXC2`: one explicit legal assignment (`R = 200 (D₀ + 1)`, `β 1 = 1/200`,
`ℓ = 1600 R`) at which the rank is exactly one at every point (the one-stratum is everything),
no point is a strong edge point (`Δ = 1`, `b = s = 1/200`), the carrier is oriented, and the
volume of the radius-`R` ball at `π_a (z, 0)` is bounded below uniformly in the shift `a`.
-/

set_option autoImplicit false
noncomputable section
open Bundle Manifold Set Metric
open DifferentialGeometry DifferentialGeometry.Geometry DifferentialGeometry.Geometry.Metric
open DifferentialGeometry.Geometry.Riemannian DifferentialGeometry.Geometry.Collapse
open GC.MetricGeometry
open scoped Manifold ContDiff

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace
attribute [local instance] sphereDimension cylinderDimension sphereCompact sphereConnected
  intrinsicMetric intrinsicUniform intrinsicEMetric intrinsicPseudoMetric intrinsicBundle
  cylinderRiemannian cylinderContinuous cylinderComplete
attribute [local instance] loopMS3_FXC2

namespace DifferentialGeometry.Geometry.Collapse

local notation "S2" => Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1

theorem loopFixture_example_FXC2 :
    ∃ (R : ℝ) (hR : 0 < R) (ℓ : LoopLen_FXC2) (β : ℕ → ℝ), 0 < β 1 ∧ β 1 < 1 ∧
      scaledSplittingStratum.{0, 0} (fun _ : LoopC_FXC2 ℓ => R) (fun _ => hR) β 1 = univ ∧
      (∀ p : LoopC_FXC2 ℓ, ¬ @isEdgePoint.{0, 0} (LoopC_FXC2 ℓ)
        ((loopMS3_FXC2 ℓ).rescale R⁻¹ (inv_pos.mpr hR)) p 1 (1 / 200) (1 / 200)) ∧
      Nonempty (ManifoldOrientation (𝓡 3) (LoopC_FXC2 ℓ) 3) ∧
      ∀ z : S2, ∃ w : ℝ, 0 < w ∧ ∀ a : ℝ, ENNReal.ofReal w ≤
        Integral.Measure.riemannianVolumeMeasure (𝓡 3) (LoopC_FXC2 ℓ) (loopMetric3_FXC2 ℓ)
          (riemannianBallOf (loopMetric3_FXC2 ℓ)
            (loopDiffeo_FXC2 ℓ (loopCoverS_FXC2 ℓ.1 a (z, 0))) R) := by
  obtain ⟨D0, hD00, hD0⟩ := exists_sphereDiam_FXC2
  have hR : 0 < 200 * (D0 + 1) := by positivity
  let ℓ : LoopLen_FXC2 := ⟨1600 * (200 * (D0 + 1)), by positivity⟩
  let β : ℕ → ℝ := fun _ => 1 / 200
  have hthin : β 1 / 2 + D0 / (200 * (D0 + 1)) ≤ 1 / 100 := by
    have h1 : D0 / (200 * (D0 + 1)) ≤ 1 / 200 := by
      rw [div_le_div_iff₀ (by positivity) (by norm_num)]
      nlinarith
    change 1 / 200 / 2 + _ ≤ _
    linarith
  have hℓ : 8 * (200 * (D0 + 1)) / β 1 ≤ ℓ.1 := by
    change 8 * (200 * (D0 + 1)) / (1 / 200) ≤ 1600 * (200 * (D0 + 1))
    apply le_of_eq
    field_simp
    ring
  refine ⟨200 * (D0 + 1), hR, ℓ, β, by simp [β], by norm_num [β],
    loopStratum_one_eq_univ_FXC2 ℓ hR hD0 (by simp [β]) (by norm_num [β]) (by norm_num [β])
      (by norm_num [β]) hthin hℓ,
    fun p => loopNotEdge_FXC2 ℓ hR hD0 (by simp [β]) (by norm_num [β]) hthin hℓ (by norm_num)
      (by norm_num) p,
    loopOrientation_FXC2 ℓ, fun z => ?_⟩
  obtain ⟨w, hw, h⟩ := exists_loopMetric3_volume_FXC2 hR z
  refine ⟨w, hw, fun a => h ℓ a ?_⟩
  change 2 * (200 * (D0 + 1)) ≤ 1600 * (200 * (D0 + 1))
  nlinarith

end DifferentialGeometry.Geometry.Collapse
