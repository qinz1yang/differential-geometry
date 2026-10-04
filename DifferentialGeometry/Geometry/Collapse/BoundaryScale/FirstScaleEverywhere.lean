import DifferentialGeometry.Geometry.Collapse.BoundaryScale.BoundaryBallVolume

/-!
# First volume scales at boundary centres and at every point

The actual boundary half-ball estimate provides the small-radius barrier. The first
crossing is positive and attained; the interior result supplies the other centres.
-/

set_option autoImplicit false

noncomputable section

open DifferentialGeometry GC.Endpoint Bundle Manifold MeasureTheory Set
open DifferentialGeometry.Geometry.Riemannian.VolumeComparison
open scoped Manifold ContDiff ENNReal Topology

namespace DifferentialGeometry.Geometry.Collapse

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace

variable (W : CompactCarrier) (g : SmoothRiemannianMetric W.model W.Carrier)

theorem exists_ballVolume_gt_cube_of_boundary (p : W.Carrier)
    (hp : p ∈ W.model.boundary W.Carrier) {w : ℝ} (hw : 0 < w)
    (hwc : w < euclideanThreeUnitBallVolume / 2) :
    ∃ a > 0, ∀ r : ℝ, 0 < r → r ≤ a → w * r ^ 3 < (ballVolume g p r).toReal := by
  let c := euclideanThreeUnitBallVolume / 2
  have hc : 0 < c := by dsimp only [c, euclideanThreeUnitBallVolume]; positivity
  let b := (c + w) / 2
  have hb : 0 < b := by dsimp only [b]; linarith
  have hwb : w < b := by dsimp only [b, c]; linarith
  have hbc : b < c := by dsimp only [b, c]; linarith
  let ε := 1 - b / c
  have hε : 0 < ε := sub_pos.mpr ((div_lt_one hc).mpr hbc)
  have hε1 : ε < 1 := by dsimp only [ε]; linarith [div_pos hb hc]
  obtain ⟨ρ, hρ, hsmall⟩ := exists_ballVolume_boundary_ratio W g p hp ε hε hε1
  refine ⟨ρ / 2, half_pos hρ, ?_⟩
  intro r hr hra
  have hl := ENNReal.toReal_mono (ballVolume_ne_top g p r)
    (hsmall r hr (hra.trans_lt (half_lt_self hρ)))
  rw [ENNReal.toReal_ofReal (by positivity)] at hl
  have heq : (1 - ε) * c = b := by
    dsimp only [ε]
    rw [sub_sub_cancel, div_mul_cancel₀ b hc.ne']
  change (1 - ε) * c * r ^ 3 ≤ _ at hl
  rw [heq] at hl
  exact (mul_lt_mul_of_pos_right hwb (pow_pos hr 3)).trans_le hl

theorem firstVolumeScale_spec_of_boundary (p : W.Carrier)
    (hp : p ∈ W.model.boundary W.Carrier) {w : ℝ} (hw : 0 < w)
    (hwc : w < euclideanThreeUnitBallVolume / 2) :
    0 < firstVolumeScale g p w ∧
      (ballVolume g p (firstVolumeScale g p w)).toReal = w * firstVolumeScale g p w ^ 3 ∧
      ∀ r : ℝ, 0 < r → r < firstVolumeScale g p w →
        w * r ^ 3 < (ballVolume g p r).toReal :=
  Real.firstPositiveCrossing_cube_spec_of_bounded
    ((ballVolume_toReal_monotone g p).monotoneOn (Ioi 0))
    (fun r _ => ballVolume_toReal_continuousWithinAt_left g p r) hw
    (exists_ballVolume_gt_cube_of_boundary W g p hp hw hwc)
    ⟨(Integral.Measure.riemannianVolumeMeasure (I := W.model) (M := W.Carrier) g univ).toReal,
      fun r _ => ballVolume_toReal_le_total g p r⟩

theorem firstVolumeScale_pos_of_boundary (p : W.Carrier)
    (hp : p ∈ W.model.boundary W.Carrier) {w : ℝ} (hw : 0 < w)
    (hwc : w < euclideanThreeUnitBallVolume / 2) : 0 < firstVolumeScale g p w :=
  (firstVolumeScale_spec_of_boundary W g p hp hw hwc).1

private theorem distanceToBoundary_pos_of_interior (p : W.Carrier)
    (hp : p ∈ W.model.interior W.Carrier) : 0 < distanceToBoundary W g p := by
  let : IsManifold W.model 1 W.Carrier := IsManifold.of_le (n := ∞) (by decide)
  let : TopologicalSpace.MetrizableSpace W.Carrier := Manifold.metrizableSpace W.model W.Carrier
  let : T3Space W.Carrier := inferInstance
  let : RiemannianBundle (TangentSpace W.model : W.Carrier → Type _) := ⟨g.toRiemannianMetric⟩
  let : IsContinuousRiemannianBundle (EuclideanSpace ℝ (Fin 3))
      (TangentSpace W.model : W.Carrier → Type _) :=
    ⟨⟨g.inner, g.contMDiff.continuous, by intro x v w; rfl⟩⟩
  let em : EMetricSpace W.Carrier := EMetricSpace.ofRiemannianMetric W.model W.Carrier
  have hzero : riemannianClosedBallOf g p 0 ⊆ W.model.interior W.Carrier := by
    intro x hx
    change riemannianEDistOf g p x ≤ ENNReal.ofReal 0 at hx
    rw [ENNReal.ofReal_zero] at hx
    have hd : @edist W.Carrier em.toEDist p x = 0 := le_zero_iff.mp hx
    have heq := em.eq_of_edist_eq_zero hd
    rwa [← heq]
  simpa only [ENNReal.ofReal_zero] using
    (ofReal_lt_distanceToBoundary_iff (W := W) (g := g) (r := 0)).mpr hzero

theorem firstVolumeScale_spec_everywhere (p : W.Carrier) {w : ℝ} (hw : 0 < w)
    (hwc : w < euclideanThreeUnitBallVolume / 4) :
    0 < firstVolumeScale g p w ∧
      (ballVolume g p (firstVolumeScale g p w)).toReal = w * firstVolumeScale g p w ^ 3 ∧
      ∀ r : ℝ, 0 < r → r < firstVolumeScale g p w →
        w * r ^ 3 < (ballVolume g p r).toReal := by
  have hc : 0 < euclideanThreeUnitBallVolume := by
    dsimp only [euclideanThreeUnitBallVolume]; positivity
  rcases W.model.isInteriorPoint_or_isBoundaryPoint p with hi | hb
  · exact firstVolumeScale_spec_of_distanceToBoundary_pos W g p
      (distanceToBoundary_pos_of_interior W g p hi) hw (by
        change w < euclideanThreeUnitBallVolume
        linarith)
  · exact firstVolumeScale_spec_of_boundary W g p hb hw (by linarith)

theorem firstVolumeScale_pos_everywhere (p : W.Carrier) {w : ℝ} (hw : 0 < w)
    (hwc : w < euclideanThreeUnitBallVolume / 4) : 0 < firstVolumeScale g p w :=
  (firstVolumeScale_spec_everywhere W g p hw hwc).1

end DifferentialGeometry.Geometry.Collapse
