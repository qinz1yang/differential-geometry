import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch12.EventRightFamily_S38

set_option autoImplicit false

/-!
# CH12-S38 / G2 reduction: `hevent` of S37 from right-limit persistence

`hevent_of_persist_S38`: the event-time emptiness hypothesis of
`hempty_postStage_of_slice_empty_S37` follows from the slice emptiness `hslice` and the pure-geometry
persistence of thickness along a smooth one-parameter family of metrics (`hpersist`, an inline
hypothesis whose proof is not in the tree).
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

theorem hevent_of_persist_S38 {P : OrientedThreeStage.{u}} {g : P.Metric}
    (F : GC.Interface.RawSurgery P g)
    (hslice : ∀ w : ℝ, 0 < w → ∃ T : ℝ, ∀ s : RegularSlice F.observation, T ≤ s.time →
      ∀ (p : s.stage.Carrier) (ρ : ℝ), 0 < ρ →
        curvatureRadius s.normalizedMetric p = ENNReal.ofReal ρ →
        ENNReal.ofReal (w * ρ ^ 3) ≤ ballVolume s.normalizedMetric p ρ → False)
    (hpersist : ∀ (Q : OrientedThreeStage.{u}) (G : ℝ → Q.Metric) (a ε0 : ℝ) (ha : 0 < a),
      0 < ε0 → Q.MetricSmoothUpTo G (Icc a (a + ε0)) → ∀ w : ℝ, 0 < w →
      ∀ (p : Q.Carrier) (r : ℝ), 0 < r →
        curvatureRadius (scaleMetric a⁻¹ (inv_pos.mpr ha) (G a)) p = ENNReal.ofReal r →
        ENNReal.ofReal (w * r ^ 3) ≤ ballVolume (scaleMetric a⁻¹ (inv_pos.mpr ha) (G a)) p r →
        ∃ ε1 : ℝ, 0 < ε1 ∧ ∀ (t : ℝ) (ht : a < t), t ≤ a + ε1 →
          ∃ (p' : Q.Carrier) (ρ : ℝ), 0 < ρ ∧
            curvatureRadius (scaleMetric t⁻¹ (inv_pos.mpr (ha.trans ht)) (G t)) p' =
              ENNReal.ofReal ρ ∧
            ENNReal.ofReal (w / 2 * ρ ^ 3) ≤
              ballVolume (scaleMetric t⁻¹ (inv_pos.mpr (ha.trans ht)) (G t)) p' ρ) :
    ∀ w : ℝ, 0 < w → ∃ T : ℝ, ∀ (t : ℝ) (ht : 0 < t), T ≤ t →
      t ∈ F.observation.eventTimes →
      ∀ (p : (postStage F.observation t).Carrier) (r : ℝ), 0 < r →
        curvatureRadius (scaleMetric t⁻¹ (inv_pos.mpr ht) (postMetric F.observation t)) p =
          ENNReal.ofReal r →
        ENNReal.ofReal (w * r ^ 3) ≤
          ballVolume (scaleMetric t⁻¹ (inv_pos.mpr ht) (postMetric F.observation t)) p r →
        False := by
  intro w hw
  obtain ⟨T, hT⟩ := hslice (w / 2) (half_pos hw)
  refine ⟨T, fun t ht hTt hev p r hr hcr hvol => ?_⟩
  obtain ⟨Q, G, ε0, hε0, hsm, hQ, hpost, hslices⟩ :=
    exists_smooth_right_family_S38 F.observation hev
  subst hQ
  have hpe := eq_of_heq hpost
  rw [hpe] at hcr hvol
  obtain ⟨ε1, hε1, hex⟩ := hpersist _ G t ε0 ht hε0 hsm w hw p r hr hcr hvol
  obtain ⟨ε2, hε2, -, hgap⟩ := exists_eventFree_gap_S38 F.observation (te := t)
  have hδ : 0 < min (min ε0 ε1) ε2 := lt_min (lt_min hε0 hε1) hε2
  have hnot : t + min (min ε0 ε1) ε2 ∉ F.observation.eventTimes := fun hmem =>
    hgap _ hmem (by linarith) (by linarith [min_le_right (min ε0 ε1) ε2])
  obtain ⟨s, hs⟩ := regularSlice_exists_of_not_eventTime_S37 F.observation _
    (by linarith) hnot
  have hs1 : t < s.time := by rw [hs]; linarith
  have hs2 : s.time ≤ t + ε0 := by
    rw [hs]; linarith [min_le_left (min ε0 ε1) ε2, min_le_left ε0 ε1]
  have hs3 : s.time ≤ t + ε1 := by
    rw [hs]; linarith [min_le_left (min ε0 ε1) ε2, min_le_right ε0 ε1]
  obtain ⟨hst, hsm'⟩ := hslices s hs1 hs2
  obtain ⟨p', ρ, hρ, hc, hv⟩ := hex s.time hs1 hs3
  have key : ∀ (Y : OrientedThreeStage.{u}) (_ : s.stage = Y) (m : Y.Metric), HEq s.metric m →
      ∀ (q : Y.Carrier) (ρ : ℝ), 0 < ρ →
        curvatureRadius (scaleMetric s.time⁻¹ (inv_pos.mpr s.positive) m) q = ENNReal.ofReal ρ →
        ENNReal.ofReal (w / 2 * ρ ^ 3) ≤
          ballVolume (scaleMetric s.time⁻¹ (inv_pos.mpr s.positive) m) q ρ → False := by
    intro Y hY m hm q ρ hρ hc hv
    subst hY
    have := eq_of_heq hm
    subst this
    exact hT s (hTt.trans hs1.le) q ρ hρ hc hv
  exact key _ hst (G s.time) hsm' p' ρ hρ hc hv

/-- Buffered persistent cores with `count = 0`, from slice emptiness and right-limit persistence. -/
theorem bufferedPersistentCores_count_zero_of_persist_S38 {P : OrientedThreeStage.{u}}
    {g : P.Metric} (F : GC.Interface.RawSurgery P g) (K : ℕ)
    (hslice : ∀ w : ℝ, 0 < w → ∃ T : ℝ, ∀ s : RegularSlice F.observation, T ≤ s.time →
      ∀ (p : s.stage.Carrier) (ρ : ℝ), 0 < ρ →
        curvatureRadius s.normalizedMetric p = ENNReal.ofReal ρ →
        ENNReal.ofReal (w * ρ ^ 3) ≤ ballVolume s.normalizedMetric p ρ → False)
    (hpersist : ∀ (Q : OrientedThreeStage.{u}) (G : ℝ → Q.Metric) (a ε0 : ℝ) (ha : 0 < a),
      0 < ε0 → Q.MetricSmoothUpTo G (Icc a (a + ε0)) → ∀ w : ℝ, 0 < w →
      ∀ (p : Q.Carrier) (r : ℝ), 0 < r →
        curvatureRadius (scaleMetric a⁻¹ (inv_pos.mpr ha) (G a)) p = ENNReal.ofReal r →
        ENNReal.ofReal (w * r ^ 3) ≤ ballVolume (scaleMetric a⁻¹ (inv_pos.mpr ha) (G a)) p r →
        ∃ ε1 : ℝ, 0 < ε1 ∧ ∀ (t : ℝ) (ht : a < t), t ≤ a + ε1 →
          ∃ (p' : Q.Carrier) (ρ : ℝ), 0 < ρ ∧
            curvatureRadius (scaleMetric t⁻¹ (inv_pos.mpr (ha.trans ht)) (G t)) p' =
              ENNReal.ofReal ρ ∧
            ENNReal.ofReal (w / 2 * ρ ^ 3) ≤
              ballVolume (scaleMetric t⁻¹ (inv_pos.mpr (ha.trans ht)) (G t)) p' ρ) :
    ∃ B : BufferedPersistentCores F K, B.count = 0 :=
  bufferedPersistentCores_count_zero_of_slice_empty_S37 F K hslice
    (hevent_of_persist_S38 F hslice hpersist)

end GC.LongTime.Ch12
