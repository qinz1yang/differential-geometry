import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch12.ThickLimitSeedLocalCore_S18
import DifferentialGeometry.Geometry.Compactness.CheegerGromov.Pointed.Convergence.Scaling

/-!
# CH12-S18 / V1a, group F: the seed at limit points of an actual parabolic limit

For an actual unscathed parabolic limit `Q` and a *canonical* pointed convergence `Φ` of
`t_j⁻¹ g(t_j s)` to `Q.metric s`, every limit point `x` has a seed of fixed constants `(a, v)` at
`Φ_j x` for the normalised slices `ḡ = (t_j s)⁻¹ g(t_j s)`, for all large `j`.  No completeness of
`Q` is used.  This is exactly the input `hseed` of `ricci_of_center_O5`.
-/

set_option autoImplicit false
noncomputable section
open DifferentialGeometry DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Hyperbolic DifferentialGeometry.Geometry.Collapse
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
open DifferentialGeometry.CheegerGromovCompactness
open GC.LongTime Set Filter
open scoped Manifold ContDiff ENNReal Topology
namespace GC.LongTime.Ch12
universe u

attribute [local instance] ActualUnscathedParabolicLimit_S13.topology
  ActualUnscathedParabolicLimit_S13.charts ActualUnscathedParabolicLimit_S13.smooth
  ActualUnscathedParabolicLimit_S13.hausdorff ActualUnscathedParabolicLimit_S13.sigmaCompact

variable {P : OrientedThreeStage.{u}} {g : P.Metric} {F : GC.Interface.RawSurgery P g}

/-- **V1a.** Seed of fixed constants at `Φ_j x` for all large `j`, from canonical convergence. -/
theorem hasNormalizedSeed_of_canonical_S18 (Q : ActualUnscathedParabolicLimit_S13 F) (s : ℝ)
    (hs : s ∈ Q.timeInterval)
    (Φ : PointedRiemannianConvergenceMaps (Q.seqAt_O5 s hs) (Q.limitAt_O5 s) id)
    (C : MetricConvergenceData Φ)
    (hcan : ∀ k, C.domain k = CanonicalMetricCompactness.canonicalSourceData Φ k)
    (x : Q.Carrier) :
    ∃ a v : ℝ, 0 < a ∧ 0 < v ∧
      ∀ᶠ j in atTop, HasNormalizedSeed_S13 (Q.slice j s hs) (Φ.map j x) a v := by
  have hs0 : 0 < s := Q.interval_pos hs
  have hc : 0 < s⁻¹ := inv_pos.mpr hs0
  obtain ⟨a, v, ha, hv, hev⟩ := exists_seed_at_limit_point_S18 (Φ.scaleMetric s⁻¹ hc)
    (C.scaleMetric s⁻¹ hc) (C.scaleMetric_domain_eq_canonical hcan s⁻¹ hc) x
  refine ⟨a, v, ha, hv, hev.mono fun j hj => ?_⟩
  have hmet : (Q.slice j s hs).normalizedMetric =
      ((Q.seqAt_O5 s hs).scaleMetric s⁻¹ hc |>.obj j).metric := by
    apply SmoothRiemannianMetric.ext_inner
    intro p v w
    change (scaleMetric (Q.slice j s hs).time⁻¹ _ (Q.slice j s hs).metric).inner p v w =
      (scaleMetric s⁻¹ hc (scaleMetric (Q.times j)⁻¹ (inv_pos.mpr (Q.times_pos j))
        (Q.slice j s hs).metric)).inner p v w
    rw [scaleMetric_inner, scaleMetric_inner, scaleMetric_inner, Q.slice_time j s hs, mul_inv]
    ring
  unfold HasNormalizedSeed_S13
  rw [hmet]
  exact hj

/-- **LTF01b (canonical form, seed discharged).** `ricci_of_center_O5` with `hseed` supplied by
`hasNormalizedSeed_of_canonical_S18`: only C1 (`hcenter`) and canonical convergence remain. -/
theorem ricci_of_center_canonical_S18
    (hcenter : ∀ (S : LatePointSequence_S13 F) (a v : ℝ), 0 < a → 0 < v →
      (∀ j, HasNormalizedSeed_S13 (S.slices j) (S.point j) a v) →
      ∀ ε : ℝ, 0 < ε → ∀ᶠ j in atTop, NormalizedRicciDefect_S13 (S.slices j) (S.point j) < ε)
    (Q : ActualUnscathedParabolicLimit_S13 F) (s : ℝ) (hs : s ∈ Q.timeInterval)
    (Φ : PointedRiemannianConvergenceMaps (Q.seqAt_O5 s hs) (Q.limitAt_O5 s) id)
    (C : MetricConvergenceData Φ)
    (hcan : ∀ k, C.domain k = CanonicalMetricCompactness.canonicalSourceData Φ k) :
    RicciEqualsMetricMultiple_S13 (Q.metric s) (-(2 * s)⁻¹) ∧
      hasConstantSectionalCurvature (Q.metric s) (-(4 * s)⁻¹) :=
  ricci_of_center_O5 hcenter Q s hs Φ C hcan (hasNormalizedSeed_of_canonical_S18 Q s hs Φ C hcan)

end GC.LongTime.Ch12
