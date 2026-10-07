import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch12.ThickScaleQ1_S37
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch12.BufferedCoresEmpty
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch12.ThickLimitBasic_CX6
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch12.SeamImage_CX4

set_option autoImplicit false

/-!
# CH12-S37 / G2: empty thick part, hence empty cores

(i) non-negative branch: `Q1-scale` and vanishing normalized volume leave no `w`-thick point;
(ii) transport of slice-emptiness to `postStage`, with the event-time case kept as an explicit
hypothesis (a `RegularSlice` never sits at an event time);
(iii) negative branch via `eventually_no_thick_points_CX6`.
-/

noncomputable section
open DifferentialGeometry DifferentialGeometry.Topology
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
open DifferentialGeometry.Geometry.Collapse DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Riemannian DifferentialGeometry.Geometry.Hyperbolic
open DifferentialGeometry.CheegerGromovCompactness
open GC.LongTime Set Filter
open scoped Manifold ContDiff ENNReal Topology
namespace GC.LongTime.Ch12
universe u

/-- (i) Non-negative scalar branch: for every `w > 0` the `w`-thick part is eventually empty. -/
theorem no_thick_slice_points_of_not_negative_S37 {P : OrientedThreeStage.{u}} {g : P.Metric}
    {F : GC.Interface.RawSurgery P g} {δ : ℝ → ℝ} (Hp : AnalyticSurgeryProfile F δ) (K : ℕ)
    (hW1 : ∃ (b T C : ℝ → ℝ), (∀ w : ℝ, 0 < w → 0 < b w) ∧ (∀ w, 0 < C w) ∧
      ∀ w : ℝ, 0 < w → ∀ s : RegularSlice F.observation, T w ≤ s.time →
      ∀ (p : s.stage.Carrier) (r : ℝ), 0 < r → r ≤ b w →
        (∃ z ∈ connectedComponent p,
          ¬ SectionalBoundedBelowAt s.normalizedMetric z 0) →
        (∀ q ∈ riemannianBallOf s.normalizedMetric p r,
          SectionalBoundedBelowAt s.normalizedMetric q (-(r ^ 2)⁻¹)) →
        ENNReal.ofReal (w * r ^ 3) ≤ ballVolume s.normalizedMetric p r →
        ∀ k : ℕ, k ≤ K → ∀ q ∈ riemannianBallOf s.normalizedMetric p r,
          curvatureDerivativeNorm s.normalizedMetric k q ≤ C w * (r ^ (k + 2))⁻¹)
    (hn : ¬ EventuallyNegativeScalar_S13 F) :
    ∀ w : ℝ, 0 < w → ∃ T : ℝ, ∀ s : RegularSlice F.observation, T ≤ s.time →
      ∀ (p : s.stage.Carrier) (ρ : ℝ), 0 < ρ →
        curvatureRadius s.normalizedMetric p = ENNReal.ofReal ρ →
        ENNReal.ofReal (w * ρ ^ 3) ≤ ballVolume s.normalizedMetric p ρ → False := by
  intro w hw
  obtain ⟨a, ha, T1, hT1⟩ := thick_scale_lower_bound_S37 Hp K hW1 w hw
  obtain ⟨T2, hT2⟩ := normalizedVolumeVanishes_of_not_negative_R2 Hp hn (w * a ^ 3)
    (mul_pos hw (pow_pos ha 3))
  refine ⟨max T1 T2, fun s hs p ρ hρ hcr hvol => ?_⟩
  have hρa := hT1 s ((le_max_left _ _).trans hs) p ρ hρ hcr hvol
  have htot := hT2 s ((le_max_right _ _).trans hs)
  have h1 : ENNReal.ofReal (w * a ^ 3) ≤ ballVolume s.normalizedMetric p ρ :=
    (ENNReal.ofReal_le_ofReal (by gcongr)).trans hvol
  have h2 : ballVolume s.normalizedMetric p ρ ≤ normalizedTotalVolume_S13 s :=
    MeasureTheory.measure_mono (Set.subset_univ _)
  exact absurd (h1.trans h2) (not_le.mpr htot)

/-- (iii) Negative branch: the hypotheses are exactly those of `eventually_no_thick_points_CX6`,
for every `w`. -/
theorem no_thick_slice_points_of_negative_S37 {P : OrientedThreeStage.{u}} {g : P.Metric}
    {F : GC.Interface.RawSurgery P g} {δ : ℝ → ℝ} (Hp : AnalyticSurgeryProfile F δ)
    (hdec : ∀ ε : ℝ, 0 < ε → ∃ B : ℝ, ∀ t : ℝ, B < t → δ t < ε)
    (hneg : EventuallyNegativeScalar_S13 F)
    (hextract : ∀ w : ℝ, 0 < w → ThickSequenceHasHyperbolicSubsequence_S13 Hp hdec hneg w)
    (hempty : ∀ w : ℝ, 0 < w → ∀ M : FiniteVolumeHyperbolicModel.{u}, ¬ IsActualWThickLimit_S13 F w M) :
    ∀ w : ℝ, 0 < w → ∃ T : ℝ, ∀ s : RegularSlice F.observation, T ≤ s.time →
      ∀ (p : s.stage.Carrier) (ρ : ℝ), 0 < ρ →
        curvatureRadius s.normalizedMetric p = ENNReal.ofReal ρ →
        ENNReal.ofReal (w * ρ ^ 3) ≤ ballVolume s.normalizedMetric p ρ → False := by
  intro w hw
  obtain ⟨T, hT⟩ := eventually_no_thick_points_CX6 Hp hdec hneg w hw (hextract w hw) (hempty w hw)
  exact ⟨T + 1, fun s hs p ρ hρ hcr hvol =>
    hT s (by linarith) p ⟨ρ, hρ, hcr, hvol⟩⟩

/-- A positive non-event time is the time of a regular slice. -/
theorem regularSlice_exists_of_not_eventTime_S37 {P : OrientedThreeStage.{u}} {g : P.Metric}
    (O : ObservationTower P g) (t : ℝ) (ht : 0 < t) (hnot : t ∉ O.eventTimes) :
    ∃ s : RegularSlice O, s.time = t := by
  refine ⟨⟨t, ht, hnot, ?_⟩, rfl⟩
  have hle := (O.observe t ht.le).time_le_horizon_at (Fin.last (O.observe t ht.le).eventCount)
  refine lt_of_le_of_ne hle ?_
  intro heq
  rcases Fin.eq_zero_or_eq_succ (Fin.last (O.observe t ht.le).eventCount) with h0 | ⟨j, hj⟩
  · rw [h0, (O.observe t ht.le).time_zero] at heq
    exact ht.ne heq
  · apply hnot
    have hmem : t ∈ (O.observe t ht.le).eventTimes :=
      ⟨j, by change (O.observe t ht.le).time j.succ = t; rw [← hj]; exact heq⟩
    rw [← O.eventTimes_inter t ht.le] at hmem
    exact hmem.1

end GC.LongTime.Ch12
