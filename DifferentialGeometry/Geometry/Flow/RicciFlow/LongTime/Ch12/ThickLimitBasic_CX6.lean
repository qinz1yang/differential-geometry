import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch12.ThickLimitInterfaceProps
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch12.VolumeBridgeUnconditional_S10
import DifferentialGeometry.Geometry.Compactness.CheegerGromov.Pointed.Convergence.Volume

set_option autoImplicit false

/-! # CH12-CX6: actual sequences, the empty-family alternative, and total limit volume -/

noncomputable section
open DifferentialGeometry DifferentialGeometry.Topology DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Hyperbolic DifferentialGeometry.Geometry.Collapse
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
open DifferentialGeometry.CheegerGromovCompactness
open GC.LongTime Set Filter MeasureTheory
open scoped Manifold ContDiff ENNReal Topology

namespace GC.LongTime.Ch12
universe u

variable {P : OrientedThreeStage.{u}} {g : P.Metric} {F : GC.Interface.RawSurgery P g}

theorem thick_subsequence_CX6 {S : LatePointSequence_S13 F} {w : ℝ}
    (h : IsWThickSequence_S13 S w) (σ : ℕ → ℕ) (hσ : StrictMono σ) :
    IsWThickSequence_S13 (S.subsequence σ hσ) w := fun j => h (σ j)

/-- The empty actual-limit family forces eventual emptiness of the fixed thick
part.  No nonempty model is postulated in this alternative. -/
theorem eventually_no_thick_points_CX6 {δ : ℝ → ℝ} (Hp : AnalyticSurgeryProfile F δ)
    (hdec : ∀ ε : ℝ, 0 < ε → ∃ B : ℝ, ∀ t : ℝ, B < t → δ t < ε)
    (hneg : EventuallyNegativeScalar_S13 F) (w : ℝ) (hw : 0 < w)
    (hextract : ThickSequenceHasHyperbolicSubsequence_S13 Hp hdec hneg w)
    (hempty : ∀ M : FiniteVolumeHyperbolicModel.{u}, ¬ IsActualWThickLimit_S13 F w M) :
    ∃ T : ℝ, ∀ s : RegularSlice F.observation, T < s.time → ∀ p : s.stage.Carrier,
      ¬ ∃ r : ℝ, 0 < r ∧ curvatureRadius s.normalizedMetric p = ENNReal.ofReal r ∧
        ENNReal.ofReal (w * r ^ 3) ≤ ballVolume s.normalizedMetric p r := by
  classical
  by_contra hn
  push Not at hn
  choose s hs p r hr hrad hvol using fun n : ℕ => hn (n : ℝ)
  let S : LatePointSequence_S13 F :=
    { slices := s
      times_tendsto := tendsto_atTop_mono (fun n => (hs n).le) tendsto_natCast_atTop_atTop
      point := p }
  have hthick : IsWThickSequence_S13 S w := fun n => ⟨r n, hr n, hrad n, hvol n⟩
  obtain ⟨σ, hσ, M, hconv⟩ := hextract hw S hthick
  exact hempty M ⟨S.subsequence σ hσ, thick_subsequence_CX6 hthick σ hσ, hconv⟩

attribute [local instance] PointedRiemannianManifold.topology
  PointedRiemannianManifold.charted PointedRiemannianManifold.smooth
  PointedRiemannianManifold.t2 PointedRiemannianManifold.sigmaCompact
  PointedRiemannianManifold.t2TangentBundle

/-- The unconditional S10 volume budget bounds the *total* volume of every
canonical pointed limit of actual normalized slices. -/
theorem canonical_limit_volume_bound_CX6 {δ : ℝ → ℝ} (Hp : AnalyticSurgeryProfile F δ) :
    ∃ V : ℝ, 0 < V ∧ ∀ (S : LatePointSequence_S13 F) (σ : ℕ → ℕ), StrictMono σ →
      ∀ (L : PointedRiemannianManifold.{u, 0, 0} ThreeModel)
        (Φ : PointedRiemannianConvergenceMaps S.pointedSeq L σ)
        (C : MetricConvergenceData Φ),
        (∀ n, C.domain n = CanonicalMetricCompactness.canonicalSourceData Φ n) →
        Integral.Measure.riemannianVolumeMeasure ThreeModel L.M L.metric univ ≤ ENNReal.ofReal V := by
  obtain ⟨V, hV, hvolume⟩ := normalizedVolumeBounded_S13_unconditional_S10 Hp
  refine ⟨V, hV, ?_⟩
  intro S σ hσ L Φ C hcan
  let ν := Integral.Measure.riemannianVolumeMeasure ThreeModel L.M L.metric
  have htime : ∀ᶠ n in atTop, 1 ≤ (S.slices (σ n)).time :=
    (S.times_tendsto.comp hσ.tendsto_atTop).eventually (eventually_ge_atTop 1)
  have hcompact : ∀ K : Set L.M, IsCompact K → ν K ≤ ENNReal.ofReal V := by
    intro K hK
    have hlim : Tendsto (fun n => Integral.Measure.riemannianVolumeMeasure ThreeModel
        (S.slices (σ n)).stage.Carrier (S.slices (σ n)).normalizedMetric (Φ.map n '' K))
        atTop (𝓝 (ν K)) := by
      have h := Φ.tendsto_setLIntegral_image C hcan hK
        (fun _ _ => (1 : ℝ≥0∞)) (fun _ => measurable_const) (f := fun _ => 1) (B := 1)
        ENNReal.one_ne_top (Eventually.of_forall fun _ _ _ => le_rfl)
        (fun _ _ => tendsto_const_nhds)
      dsimp only [LatePointSequence_S13.pointedSeq] at h
      have h' : Tendsto (fun n => Integral.Measure.riemannianVolumeMeasure ThreeModel
          (S.slices (σ n)).stage.Carrier (S.slices (σ n)).normalizedMetric (Φ.map n '' K))
          atTop (𝓝 (∫⁻ _x in K, (1 : ℝ≥0∞) ∂ν)) :=
        h.congr' (Eventually.of_forall fun n => by
          exact (setLIntegral_const (Φ.map n '' K) (1 : ℝ≥0∞)).trans (one_mul _))
      simpa only [setLIntegral_const, one_mul, ν] using h'
    apply le_of_tendsto hlim
    filter_upwards [htime] with n hn
    exact (measure_mono (subset_univ _)).trans (hvolume _ hn)
  have hlin : ∫⁻ _x, (1 : ℝ≥0∞) ∂ν ≤ ENNReal.ofReal V := by
    calc
      _ = ∫⁻ _x in ⋃ n, compactCovering L.M n, (1 : ℝ≥0∞) ∂ν := by
        rw [iUnion_compactCovering, setLIntegral_univ]
      _ = ⨆ n, ∫⁻ _x in compactCovering L.M n, (1 : ℝ≥0∞) ∂ν :=
        setLIntegral_iUnion_of_directed (fun _ => 1) (fun m n => ⟨max m n,
          compactCovering_subset L.M (le_max_left _ _), compactCovering_subset L.M (le_max_right _ _)⟩)
      _ ≤ _ := iSup_le fun n => by
        simpa only [setLIntegral_const, one_mul] using hcompact _ (isCompact_compactCovering L.M n)
  simpa only [lintegral_const, one_mul] using hlin

end GC.LongTime.Ch12
