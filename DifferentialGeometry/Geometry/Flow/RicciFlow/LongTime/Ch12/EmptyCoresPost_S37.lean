import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch12.EmptyThickCores_S37

set_option autoImplicit false

/-!
# CH12-S37 / G2 (ii): from emptiness of the thick part on regular slices to `hempty` of
`BufferedPersistentCores.ofEmpty_S11`.

Regular times are transported with `postStage_regularSlice` / `postMetric_regularSlice`.
An event time `t ∈ F.observation.eventTimes` is the time of no `RegularSlice`
(`RegularSlice.regular : time ∉ eventTimes`), so the event-time case is the explicit
hypothesis `hevent`.
-/

noncomputable section
open DifferentialGeometry DifferentialGeometry.Topology
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
open DifferentialGeometry.Geometry.Collapse DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Riemannian
open GC.LongTime Set Filter
open scoped Manifold ContDiff ENNReal Topology
namespace GC.LongTime.Ch12
universe u

theorem hempty_postStage_of_slice_empty_S37 {P : OrientedThreeStage.{u}} {g : P.Metric}
    (F : GC.Interface.RawSurgery P g)
    (hslice : ∀ w : ℝ, 0 < w → ∃ T : ℝ, ∀ s : RegularSlice F.observation, T ≤ s.time →
      ∀ (p : s.stage.Carrier) (ρ : ℝ), 0 < ρ →
        curvatureRadius s.normalizedMetric p = ENNReal.ofReal ρ →
        ENNReal.ofReal (w * ρ ^ 3) ≤ ballVolume s.normalizedMetric p ρ → False)
    (hevent : ∀ w : ℝ, 0 < w → ∃ T : ℝ, ∀ (t : ℝ) (ht : 0 < t), T ≤ t →
      t ∈ F.observation.eventTimes →
      ∀ (p : (postStage F.observation t).Carrier) (r : ℝ), 0 < r →
        curvatureRadius (scaleMetric t⁻¹ (inv_pos.mpr ht) (postMetric F.observation t)) p =
          ENNReal.ofReal r →
        ENNReal.ofReal (w * r ^ 3) ≤
          ballVolume (scaleMetric t⁻¹ (inv_pos.mpr ht) (postMetric F.observation t)) p r →
        False) :
    ∀ w : ℝ, 0 < w → ∃ T : ℝ, ∀ (t : ℝ) (ht : 0 < t), T ≤ t →
      ∀ (p : (postStage F.observation t).Carrier) (r : ℝ), 0 < r →
        curvatureRadius (scaleMetric t⁻¹ (inv_pos.mpr ht) (postMetric F.observation t)) p =
          ENNReal.ofReal r →
        ENNReal.ofReal (w * r ^ 3) ≤
          ballVolume (scaleMetric t⁻¹ (inv_pos.mpr ht) (postMetric F.observation t)) p r →
        False := by
  intro w hw
  obtain ⟨T1, h1⟩ := hslice w hw
  obtain ⟨T2, h2⟩ := hevent w hw
  refine ⟨max T1 T2, fun t ht hT p r hr hcr hvol => ?_⟩
  by_cases hev : t ∈ F.observation.eventTimes
  · exact h2 t ht ((le_max_right _ _).trans hT) hev p r hr hcr hvol
  · obtain ⟨s, hst⟩ := regularSlice_exists_of_not_eventTime_S37 F.observation t ht hev
    subst hst
    have key : ∀ (Y : OrientedThreeStage.{u}) (hY : postStage F.observation s.time = Y)
        (m : Y.Metric), HEq (postMetric F.observation s.time) m →
        (∀ (p : Y.Carrier) (r : ℝ), 0 < r →
          curvatureRadius (scaleMetric s.time⁻¹ (inv_pos.mpr ht) m) p = ENNReal.ofReal r →
          ENNReal.ofReal (w * r ^ 3) ≤
            ballVolume (scaleMetric s.time⁻¹ (inv_pos.mpr ht) m) p r → False) →
        ∀ (p : (postStage F.observation s.time).Carrier) (r : ℝ), 0 < r →
          curvatureRadius (scaleMetric s.time⁻¹ (inv_pos.mpr ht)
            (postMetric F.observation s.time)) p = ENNReal.ofReal r →
          ENNReal.ofReal (w * r ^ 3) ≤ ballVolume (scaleMetric s.time⁻¹ (inv_pos.mpr ht)
            (postMetric F.observation s.time)) p r → False := by
      intro Y hY m hm hY'
      subst hY
      have := eq_of_heq hm
      subst this
      exact hY'
    exact key s.stage (postStage_eq_sliceStage_CX4 s) s.metric
      (postMetric_regularSlice F.observation s)
      (fun p r hr hcr hvol => h1 s ((le_max_left _ _).trans hT) p r hr hcr hvol) p r hr hcr hvol

/-- Buffered persistent cores with `count = 0` from emptiness of the thick part. -/
theorem bufferedPersistentCores_count_zero_of_slice_empty_S37 {P : OrientedThreeStage.{u}}
    {g : P.Metric} (F : GC.Interface.RawSurgery P g) (K : ℕ)
    (hslice : ∀ w : ℝ, 0 < w → ∃ T : ℝ, ∀ s : RegularSlice F.observation, T ≤ s.time →
      ∀ (p : s.stage.Carrier) (ρ : ℝ), 0 < ρ →
        curvatureRadius s.normalizedMetric p = ENNReal.ofReal ρ →
        ENNReal.ofReal (w * ρ ^ 3) ≤ ballVolume s.normalizedMetric p ρ → False)
    (hevent : ∀ w : ℝ, 0 < w → ∃ T : ℝ, ∀ (t : ℝ) (ht : 0 < t), T ≤ t →
      t ∈ F.observation.eventTimes →
      ∀ (p : (postStage F.observation t).Carrier) (r : ℝ), 0 < r →
        curvatureRadius (scaleMetric t⁻¹ (inv_pos.mpr ht) (postMetric F.observation t)) p =
          ENNReal.ofReal r →
        ENNReal.ofReal (w * r ^ 3) ≤
          ballVolume (scaleMetric t⁻¹ (inv_pos.mpr ht) (postMetric F.observation t)) p r →
        False) :
    ∃ B : BufferedPersistentCores F K, B.count = 0 :=
  ⟨BufferedPersistentCores.ofEmpty_S11 F K (hempty_postStage_of_slice_empty_S37 F hslice hevent),
    BufferedPersistentCores.ofEmpty_count_S11 F K (hempty_postStage_of_slice_empty_S37 F hslice hevent)⟩

end GC.LongTime.Ch12
