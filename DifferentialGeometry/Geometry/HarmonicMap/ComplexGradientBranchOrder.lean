import DifferentialGeometry.Analysis.Complex.FirstOrderSystems.FiniteOrderGrowth
import DifferentialGeometry.Geometry.HarmonicMap.ComplexGradientUniqueContinuation

set_option autoImplicit false
noncomputable section

open Set Metric Filter Manifold MeasureTheory
open DifferentialGeometry DifferentialGeometry.Topology
open scoped ContDiff Manifold Topology NNReal

namespace DifferentialGeometry.Geometry

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M]
  [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M]

theorem IsMorreyDisk.exists_finite_order_complex_gradient_gauge
    {g : SmoothRiemannianMetric 𝓘(ℝ, E) M} {γ : freeLoop M}
    {u : C(closedDisk, M)} (hu : IsMorreyDisk g γ u)
    (hγ : IsSmoothEmbeddedLoop (E := E) γ)
    {a : ℂ} (ha : a ∈ ball (0 : ℂ) 1) :
    ∃ (R : ℝ) (hR : 0 < R),
      closedBall a (2 * R) ⊆ ball (0 : ℂ) 1 ∧
      (∀ z ∈ closedBall a (2 * R),
        diskExtension u z ∈ (chartAt E (diskExtension u a)).source) ∧
      ∃ A_R : C(closedBall a R,
          (Fin (Module.finrank ℝ E) → ℂ) →L[ℂ]
            (Fin (Module.finrank ℝ E) → ℂ)),
        (∀ z : closedBall a R,
          A_R z = chartComplexGradientOperator g
            (diskExtension u a) (diskExtension u) (z : ℂ)) ∧
        4 * R * ‖A_R‖ < (1 / 4 : ℝ) ∧
        ∃ P : C(closedBall a R,
            (Fin (Module.finrank ℝ E) → ℂ) →L[ℂ]
              (Fin (Module.finrank ℝ E) → ℂ)),
          P = 1 + Analysis.diskCauchyTransform a R hR (A_R * P) ∧
          ‖P - 1‖ ≤ (4 * R * ‖A_R‖) / (1 - 4 * R * ‖A_R‖) ∧
          ‖P‖ ≤ 2 ∧
          (∀ z : closedBall a R, IsUnit (P z)) ∧
          (let P₀ : ℂ →
              ((Fin (Module.finrank ℝ E) → ℂ) →L[ℂ]
                (Fin (Module.finrank ℝ E) → ℂ)) := fun z =>
            1 + (Real.pi : ℂ)⁻¹ •
              ∫ w : closedBall a R,
                (z - (w : ℂ))⁻¹ • (A_R w * P w)
                ∂(volume.comap ((↑) : closedBall a R → ℂ))
           let ξ : ℂ → (Fin (Module.finrank ℝ E) → ℂ) := fun q k =>
             chartComplexGradient (diskExtension u a) (diskExtension u) k q
           let F : ℂ → (Fin (Module.finrank ℝ E) → ℂ) := fun q =>
             (Ring.inverse (P₀ q) :
               (Fin (Module.finrank ℝ E) → ℂ) →L[ℂ]
                 (Fin (Module.finrank ℝ E) → ℂ)) (ξ q)
           (∀ z : closedBall a R, P₀ (z : ℂ) = P z) ∧
           (∀ z ∈ closedBall a R, IsUnit (P₀ z)) ∧
           ContDiffOn ℝ 1 P₀ (ball a R) ∧
           AnalyticOnNhd ℂ F (ball a R) ∧
           (∀ q ∈ ball a R, ξ q = P₀ q (F q)) ∧
           (∀ q ∈ ball a R, F q = 0 ↔ ξ q = 0) ∧
           (∀ q ∈ ball a R,
             F q = 0 ↔ mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, E) (diskExtension u) q = 0) ∧
           analyticOrderAt F a ≠ ⊤ ∧
           ∃ G : ℂ → (Fin (Module.finrank ℝ E) → ℂ),
             AnalyticAt ℂ G a ∧ G a ≠ 0 ∧
             ContDiffAt ℝ 1 (fun z => P₀ z (G z)) a ∧ P₀ a (G a) ≠ 0 ∧
             (∀ᶠ z in 𝓝 a,
               ξ z = (z - a) ^ analyticOrderNatAt F a • P₀ z (G z)) ∧
             ∃ c C r : ℝ, 0 < c ∧ 0 < C ∧ 0 < r ∧ r ≤ R ∧
               ∀ z ∈ ball a r,
                 c * ‖z - a‖ ^ analyticOrderNatAt F a ≤ ‖ξ z‖ ∧
                   ‖ξ z‖ ≤ C * ‖z - a‖ ^ analyticOrderNatAt F a) := by
  obtain ⟨R, hR, hbuffer, hsrc, A_R, hA_R, hsmall, P, hP, hnear, hbound,
      hunit, _, _, hactual⟩ := hu.exists_analytic_complex_gradient_gauge ha
  let V := Fin (Module.finrank ℝ E) → ℂ
  let P₀ : ℂ → V →L[ℂ] V := fun z =>
    1 + (Real.pi : ℂ)⁻¹ •
      ∫ w : closedBall a R,
        (z - (w : ℂ))⁻¹ • (A_R w * P w)
        ∂(volume.comap ((↑) : closedBall a R → ℂ))
  let ξ : ℂ → V := fun q k =>
    chartComplexGradient (diskExtension u a) (diskExtension u) k q
  let F : ℂ → V := fun q => (Ring.inverse (P₀ q)) (ξ q)
  dsimp only at hactual
  obtain ⟨hP₀eq, hP₀unit, hP₀reg, _, _, _, hF, hfactor, hzero, hzeroD⟩ := hactual
  have haR : a ∈ ball a R := mem_ball_self hR
  have hPreg : ContDiffAt ℝ 1 P₀ a :=
    hP₀reg.contDiffAt (isOpen_ball.mem_nhds haR)
  have hPunit : IsUnit (P₀ a) := hP₀unit a (mem_closedBall_self hR.le)
  have hFanalytic : AnalyticAt ℂ F a := hF a haR
  have hξgerm : ¬ ∀ᶠ z in 𝓝 a, ξ z = 0 := by
    intro hξzero
    apply hu.not_eventually_mfderiv_eq_zero hγ ha
    filter_upwards [hξzero, isOpen_ball.mem_nhds haR] with z hz hzR
    exact (hzeroD z hzR).mp ((hzero z hzR).mpr hz)
  obtain ⟨horder, G, hG, hGzero, hPG, hPGzero, horderFactor⟩ :=
    Analysis.exists_finite_order_factor_of_analytic_inverse_gauge
      hPreg hPunit hFanalytic hξgerm
  obtain ⟨c, C, r, hc, hC, hr, hgrowth⟩ :=
    Analysis.exists_power_norm_bounds_of_analytic_inverse_gauge
      hPreg hPunit hFanalytic hξgerm
  refine ⟨R, hR, hbuffer, hsrc, A_R, hA_R, hsmall, P, hP, hnear, hbound,
    hunit, ?_⟩
  refine ⟨hP₀eq, hP₀unit, hP₀reg, hF, hfactor, hzero, hzeroD, horder,
    G, hG, hGzero, hPG, hPGzero, horderFactor,
    c, C, min R r, hc, hC, lt_min hR hr, min_le_left R r, ?_⟩
  intro z hz
  exact hgrowth z ((ball_subset_ball (min_le_right R r)) hz)

end DifferentialGeometry.Geometry
