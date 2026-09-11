import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.StandardSolution.TravelingPhaseCoefficients
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.StandardSolution.StandardShiftedSupport
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.StandardSolution.StandardPositiveSeed
import DifferentialGeometry.Geometry.Curvature.RicciRayleighOperator

set_option autoImplicit false
noncomputable section
open Set Filter Bundle Manifold DifferentialGeometry
open DifferentialGeometry.Geometry.Curvature DifferentialGeometry.Geometry.Operator
open DifferentialGeometry.PDE.RicciFlow DifferentialGeometry.Analysis.Parabolic
open DifferentialGeometry.Geometry.Curvature
open scoped Manifold ContDiff Topology ENNReal
namespace DifferentialGeometry.PDE.RicciFlow
private abbrev E3 := EuclideanSpace ℝ (Fin 3)

theorem PartialStandardSolution.leastUpperRicciAt_pos
    (S : PartialStandardSolution) (t₀ : ℝ) (ht₀ : t₀ ∈ S.domain)
    (htpos : 0 < t₀) (x₀ : E3) :
    0 < leastUpperRicciAt (S.metric t₀) x₀ := by
  obtain ⟨a, ha, hat, _haD, r, hr, eta, heta, hseed⟩ :=
    S.exists_positive_upperRicci_seed_before t₀ htpos ht₀
  have hTl := ((mem_lifetimeInterval_carrier
    S.lifetime S.lifetime_pos t₀).mp ht₀).2
  let Q := S.toSolutionOn.timeShift a
  let G := flowG Q
  let τ : ℝ := t₀ - a
  let u : ℝ → E3 → ℝ := fun s x => leastUpperRicciAt (S.metric (s + a)) x
  have hτ : 0 < τ := sub_pos.mpr hat
  obtain ⟨_hmetric, hcarrier, _hreg, C, c, hc, hphase, hgradient⟩ :=
    S.exists_traveling_phase_coefficients a t₀ ha hat hTl x₀ r hr
  have hcont : ContinuousOn (fun p : ℝ × E3 => u p.1 p.2)
      (spacetimeSlab (M := E3) τ) := by
    have hmap : Continuous (fun p : ℝ × E3 => (p.1 + a, p.2)) :=
      (continuous_fst.add continuous_const).prodMk continuous_snd
    have hm : MapsTo (fun p : ℝ × E3 => (p.1 + a, p.2))
        (spacetimeSlab (M := E3) τ) (S.domain ×ˢ (univ : Set E3)) :=
      fun p hp => ⟨hcarrier p.1 hp.1, mem_univ p.2⟩
    have hh := S.leastUpperRicciAt_continuousOn.comp hmap.continuousOn hm
    exact hh
  have hnonneg : ∀ s ∈ Icc 0 τ, ∀ x : E3, 0 ≤ u s x := by
    intro s hs x
    exact S.leastUpperRicciAt_nonneg (s + a) (hcarrier s hs) x
  have hinit : ∀ x ∈ Metric.closedBall (0 : E3) r, eta ≤ u 0 x := by
    intro x hx
    simpa only [u, zero_add] using hseed x hx
  have hsupport := S.shifted_leastUpperRicci_upper_support a t₀ ha.le hat hTl
  have hpos := DifferentialGeometry.Analysis.positive_of_traveling_ball_upper_supports
    G τ hτ x₀ r eta C c hr heta hc u hcont hnonneg hsupport hinit
    (fun s hs _hspos x hx => hphase s hs x hx)
    (fun s hs _hspos x _hx => hgradient s hs x)
  simpa only [u, τ, sub_add_cancel] using hpos

theorem PartialStandardSolution.curvatureOperator_positive
    (S : PartialStandardSolution) (t : ℝ) (ht : t ∈ S.domain)
    (htpos : 0 < t) (x : E3) (n : ℕ) (c : Fin n → ℝ)
    (v w : Fin n → TangentSpace (𝓡 3) x)
    (hvw : 0 < algebraicCurvatureIdentityQuadraticEval (S.metric t) c v w) :
    0 < algebraicCurvatureOperatorQuadraticEval
      (metricAlgebraicCurvatureTensorAt (S.metric t) x) c v w :=
  algebraicCurvatureOperatorQuadraticEval_pos_of_leastUpperRicciAt_pos
    (S.metric t) x (S.leastUpperRicciAt_pos t ht htpos x) n c v w hvw
end DifferentialGeometry.PDE.RicciFlow
