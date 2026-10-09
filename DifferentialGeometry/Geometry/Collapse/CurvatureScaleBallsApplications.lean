import DifferentialGeometry.Geometry.Collapse.CurvatureScaleBalls

/-!
# Consumers of the curvature-scale toolkit on compact carriers

The toolkit of `CurvatureScaleBalls.lean` is applied to an arbitrary smooth metric on an actual
`GC.Endpoint.CompactCarrier`:

* a uniform positive floor `ρ` for the curvature scale (T3), together with positivity at every
  point (`curvatureRadius_pos`) and the sectional bound `-(ρ/2)⁻²` on every `ρ/2`-ball (T1);
* the floor of the rescaled metric `c g` is `√c ρ` (T3 + T4);
* on a connected carrier whose metric does not have nonnegative sectional curvature, every
  curvature scale is finite (`curvatureRadius_eq_top_iff`), the real scale is `1`-Lipschitz (T5)
  and the attained bound holds on every curvature-scale ball (attained T1).
-/

set_option autoImplicit false
noncomputable section
open DifferentialGeometry DifferentialGeometry.Geometry.Riemannian
open scoped Manifold ContDiff ENNReal
namespace DifferentialGeometry.Geometry.Collapse
universe u

/-- T3 on a compact carrier with `curvatureRadius_pos`: a uniform floor `ρ > 0`, positive scale
at every point, and sectional curvature at least `-(ρ/2)⁻²` on every ball of radius `ρ/2`. -/
theorem compactCarrier_curvatureScale_floor (W : GC.Endpoint.CompactCarrier.{u})
    (g : SmoothRiemannianMetric W.model W.Carrier) :
    ∃ ρ : ℝ, 0 < ρ ∧ ∀ p : W.Carrier,
      0 < curvatureRadius g p ∧ ENNReal.ofReal ρ ≤ curvatureRadius g p ∧
        ∀ q ∈ riemannianBallOf g p (ρ / 2),
          SectionalBoundedBelowAt g q (-((ρ / 2) ^ 2)⁻¹) := by
  obtain ⟨ρ, hρ, hfloor⟩ := exists_pos_le_curvatureRadius g
  refine ⟨ρ, hρ, fun p => ⟨curvatureRadius_pos g p, hfloor p, ?_⟩⟩
  have hlt : ENNReal.ofReal (ρ / 2) < curvatureRadius g p :=
    lt_of_lt_of_le ((ENNReal.ofReal_lt_ofReal_iff hρ).mpr (half_lt_self hρ)) (hfloor p)
  exact fun q hq => sectionalBoundedBelowAt_of_lt_curvatureRadius g hlt hq

/-- T3 + T4 on a compact carrier: the rescaled metric `c g` has curvature-scale floor `√c ρ`,
where `ρ` is a floor for `g`. -/
theorem compactCarrier_scaleMetric_curvatureScale_floor (W : GC.Endpoint.CompactCarrier.{u})
    (g : SmoothRiemannianMetric W.model W.Carrier) :
    ∃ ρ : ℝ, 0 < ρ ∧ ∀ (c : ℝ) (hc : 0 < c) (p : W.Carrier),
      ENNReal.ofReal (Real.sqrt c * ρ) ≤ curvatureRadius (scaleMetric c hc g) p := by
  obtain ⟨ρ, hρ, hfloor⟩ := exists_pos_le_curvatureRadius g
  refine ⟨ρ, hρ, fun c hc p => ?_⟩
  rw [curvatureRadius_scaleMetric g c hc p, ENNReal.ofReal_mul (Real.sqrt_nonneg c)]
  exact mul_le_mul' le_rfl (hfloor p)

/-- On a connected carrier, unless the metric has nonnegative sectional curvature, every curvature
scale is finite, the real curvature scale is `1`-Lipschitz (T5), it has a positive floor (T3),
and the attained sectional bound holds on each curvature-scale ball (T1). -/
theorem compactCarrier_curvatureScale_finite_lipschitz (W : GC.Endpoint.CompactCarrier.{u})
    [ConnectedSpace W.Carrier] (g : SmoothRiemannianMetric W.model W.Carrier)
    (hneg : ¬ SectionalBoundedBelow g 0) :
    (∀ p : W.Carrier, curvatureRadius g p ≠ ⊤) ∧
      (∃ ρ : ℝ, 0 < ρ ∧ ∀ p : W.Carrier, ρ ≤ (curvatureRadius g p).toReal) ∧
      (∀ p q : W.Carrier,
        |(curvatureRadius g p).toReal - (curvatureRadius g q).toReal| ≤
          (riemannianEDistOf (I := W.model) g p q).toReal) ∧
      ∀ p : W.Carrier, ∀ q ∈ riemannianBallOf g p (curvatureRadius g p).toReal,
        SectionalBoundedBelowAt g q (-(((curvatureRadius g p).toReal) ^ 2)⁻¹) := by
  have hfin : ∀ p : W.Carrier, curvatureRadius g p ≠ ⊤ :=
    fun p htop => hneg ((curvatureRadius_eq_top_iff p).mp htop)
  obtain ⟨ρ, hρ, hfloor⟩ := exists_pos_le_curvatureRadius g
  refine ⟨hfin, ⟨ρ, hρ, fun p => ?_⟩, abs_toReal_curvatureRadius_sub_le g hfin,
    fun p => sectionalBoundedBelowAt_of_curvatureRadius_ne_top g (hfin p)⟩
  have h := ENNReal.toReal_mono (hfin p) (hfloor p)
  rwa [ENNReal.toReal_ofReal hρ.le] at h

end DifferentialGeometry.Geometry.Collapse
