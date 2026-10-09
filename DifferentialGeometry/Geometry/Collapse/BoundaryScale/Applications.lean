import DifferentialGeometry.Geometry.Collapse.BoundaryScale.AnalyticData
import DifferentialGeometry.Geometry.Collapse.BoundaryScale.CurvatureBuffers
import DifferentialGeometry.Geometry.Hyperbolic.Cusp

/-!
# Consumers of the boundary-scale kernels (chapter 14, BSA/BCP)

* `curvatureRadius_cusp_lt_three`: the reference cusp metric (now with its PROVED curvature
  formula `cusp_constant_sectional_curvature_of_fields`) has curvature scale `< 3` at every point
  carrying a nondegenerate plane — the reference case of BSA01.b, through the BSA01 kernel.
* `boundary_standing_normalized_data`: on an actual compact carrier with the tree's static
  boundary hypotheses (volume collapse beyond distance `10`, whole-ball derivative control) and
  BSA01's near-boundary output, the BSA04.a standing inequality and the BSA06 sectional and
  derivative conclusions hold at EVERY point for any smooth-scale data `0 < ρ ≤ 2 r_p(w')`.
* `scaled_ball_subset_interior_of_negative_plane`: BSA01.c through a negative plane, combined
  with BSA06.a, puts the scaled buffers of centers with `d(p, ∂W) > 10` in the interior.
-/

set_option autoImplicit false

noncomputable section

open DifferentialGeometry DifferentialGeometry.Geometry.Riemannian GC.Endpoint
open DifferentialGeometry.Geometry.Curvature DifferentialGeometry.Geometry.Hyperbolic
open scoped Manifold ContDiff ENNReal

namespace DifferentialGeometry.Geometry.Collapse

universe u

/-- The reference cusp metric has curvature scale below `3` at every point with a nondegenerate
plane (BSA01.b for the reference metric). -/
theorem curvatureRadius_cusp_lt_three (Hc : HyperbolicCusp) (p : CuspHalfSpace)
    (v w : TangentSpace halfCollarModel p)
    (hgram : 0 < Hc.metric.inner p v v * Hc.metric.inner p w w - Hc.metric.inner p v w ^ 2) :
    curvatureRadius Hc.metric p < 3 := by
  apply curvatureRadius_lt_three_of_negative_plane Hc.metric p v w hgram
  rw [cusp_constant_sectional_curvature_of_fields Hc.torusMetric Hc.torus_flat Hc.metric
    Hc.metric_formula p v w]
  nlinarith

section Carrier

variable (W : CompactCarrier.{u}) (g : SmoothRiemannianMetric W.model W.Carrier)

/-- BSA04.a + BSA06 on an actual compact carrier: the standing inequality, the sectional buffer
and the whole-ball derivative bounds of the normalized metric at EVERY point. -/
theorem boundary_standing_normalized_data {K : ℕ} {A : ℝ → ℝ} {n δ w' ρ : ℝ}
    (hn : 3 ≤ n) (hδ : 0 ≤ δ) (hδn : δ * (16 * n ^ 4) ≤ 1)
    (hcoll : boundaryVolumeCollapsed W g δ)
    (hderiv : curvatureDerivativesControlled g K A δ)
    (hA : ∀ w, 0 < w → w < euclideanThreeUnitBallVolume → 0 < A w)
    (hnear : ∀ p, distanceToBoundary W g p ≤ ENNReal.ofReal 10 →
      1 ≤ curvatureRadius g p ∧ ∀ a : ℝ, 0 < a → a ≤ 1 →
        ballVolume g p a ≤ ENNReal.ofReal (1000 * δ ^ 2 * a))
    (hwn : n⁻¹ ≤ w') (hwc : w' < euclideanThreeUnitBallVolume)
    (p : W.Carrier) (hρ : 0 < ρ) (hρu : ρ ≤ 2 * firstVolumeScale g p w') :
    ENNReal.ofReal (2 * n * firstVolumeScale g p n⁻¹) < curvatureRadius g p ∧
      (∀ y ∈ riemannianBallOf (normalizedCenterMetric g ρ hρ) p (n / 4),
        SectionalBoundedBelowAt (normalizedCenterMetric g ρ hρ) y (-((n / 4) ^ 2)⁻¹)) ∧
      ∀ R, 0 < R → 2 * R + 2 < n → ∀ k ≤ K,
        ∀ y ∈ riemannianBallOf (normalizedCenterMetric g ρ hρ) p R,
          curvatureDerivativeNorm (normalizedCenterMetric g ρ hρ) k y ≤
            (2 : ℝ) ^ (K + 2) * boundaryDerivativeConstant A K (2 * R + 2) w' := by
  have hstand := ofReal_two_mul_firstVolumeScale_lt_curvatureRadius_of_boundary_data W g hn hδ
    hδn hcoll hnear p
  have hδn' : δ * n ^ 4 ≤ 1 := by nlinarith [pow_nonneg (show (0 : ℝ) ≤ n by linarith) 4]
  exact ⟨hstand,
    normalizedCenterMetric_sectional_of_standing g p (by linarith) hstand hwn hρ hρu,
    normalizedCenterMetric_derivative_bounds_of_standing g p hderiv hA (by linarith) hδn'
      hstand hwn hwc hρ hρu⟩

/-- BSA01.c through a negative plane, then BSA06.a: at a center with `d(p, ∂W) = D > 10` and a
point within `D + 1.01` carrying a plane with sectional curvature at most `-1/8`, the standing
inequality puts every scaled ball `B(p, B ρ)`, `B ≤ n/2`, `0 < ρ ≤ 2u`, in the interior. -/
theorem scaled_ball_subset_interior_of_negative_plane {p q : W.Carrier} {D n u ρ B : ℝ}
    (hDp : distanceToBoundary W g p = ENNReal.ofReal D) (hD : 10 < D)
    (hq : riemannianEDistOf g p q ≤ ENNReal.ofReal (D + 101 / 100))
    (v w : TangentSpace W.model q)
    (hgram : 0 < g.inner q v v * g.inner q w w - g.inner q v w ^ 2)
    (hneg : metricRm04StandardAt g q v w w v ≤
      -(1 / 8) * (g.inner q v v * g.inner q w w - g.inner q v w ^ 2))
    (hstand : ENNReal.ofReal (2 * n * u) < curvatureRadius g p)
    (hρ : 0 < ρ) (hρu : ρ ≤ 2 * u) (hB : B ≤ n / 2) :
    riemannianBallOf g p (B * ρ) ⊆ W.model.interior W.Carrier := by
  have hR := curvatureRadius_le_add_three_of_negative_plane g (by linarith) hq v w hgram hneg
  apply riemannianBallOf_scaled_subset_interior W g (by
    rw [hDp]
    exact (ENNReal.ofReal_lt_ofReal_iff (by linarith)).mpr hD) _ hstand hρ hρu hB
  rw [hDp, ← ENNReal.ofReal_add (by linarith) (by norm_num)]
  exact hR

end Carrier

end DifferentialGeometry.Geometry.Collapse
