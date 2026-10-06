import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch12.ScalarNonnegativeHistory_CX9
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch12.ThickLimitInterface

set_option autoImplicit false

/-!
# CH12-R2 Q1: the nonnegative scalar branch

The three definitions and implications follow review-CH12-R2, Q1(c).1, and
disposition D-R2-1 at commit 7219cf77d. Nonnegativity is on the entire slice.
Vanishing total volume excludes fixed-radius seeds; no assertion about shrinking
curvature-radius thick points is made here.
-/

noncomputable section

open Set Filter MeasureTheory DifferentialGeometry DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Integral.Measure DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
open DifferentialGeometry.Geometry.Collapse GC.LongTime
open scoped Manifold ContDiff ENNReal Topology

namespace GC.LongTime.Ch12

universe u

def EventuallyNonnegativeScalar_R2 {P : OrientedThreeStage.{u}} {g : P.Metric}
    (F : GC.Interface.RawSurgery P g) : Prop :=
  ∃ T : ℝ, ∀ s : RegularSlice F.observation, T ≤ s.time →
    ∀ x : s.stage.Carrier, 0 ≤ metricScalarAt s.metric x

def NormalizedVolumeVanishes_R2 {P : OrientedThreeStage.{u}} {g : P.Metric}
    (F : GC.Interface.RawSurgery P g) : Prop :=
  ∀ η : ℝ, 0 < η → ∃ T : ℝ,
    ∀ s : RegularSlice F.observation, T ≤ s.time →
      normalizedTotalVolume_S13 s < ENNReal.ofReal η

def NoFixedNormalizedSeedSequence_R2 {P : OrientedThreeStage.{u}} {g : P.Metric}
    (F : GC.Interface.RawSurgery P g) : Prop :=
  ∀ (S : LatePointSequence_S13 F) (a v : ℝ), 0 < a → 0 < v →
    ¬ (∀ j, HasNormalizedSeed_S13 (S.slices j) (S.point j) a v)

variable {P : OrientedThreeStage.{u}} {g : P.Metric}
  {F : GC.Interface.RawSurgery P g} {δ : ℝ → ℝ}

/-- The logical negation of the negative branch supplies whole nonempty slices. -/
theorem exists_nonnegative_slice_after_CX9
    (hn : ¬ EventuallyNegativeScalar_S13 F) (B : ℝ) :
    ∃ s : RegularSlice F.observation, B < s.time ∧ Nonempty s.stage.Carrier ∧
      ∀ x, 0 ≤ metricScalarAt s.metric x := by
  classical
  simp only [EventuallyNegativeScalar_S13, not_exists, not_forall, not_lt] at hn
  obtain ⟨s, hs, hne, hR⟩ := hn B
  exact ⟨s, hs, hne, hR⟩

/-- The nonnegative branch persists through every later recorded surgery. -/
theorem eventuallyNonnegativeScalar_of_not_negative_R2
    (H : AnalyticSurgeryProfile F δ) (hn : ¬ EventuallyNegativeScalar_S13 F) :
    EventuallyNonnegativeScalar_R2 F := by
  obtain ⟨s₀, _, _, h₀⟩ := exists_nonnegative_slice_after_CX9 hn 0
  exact ⟨s₀.time, fun s hs => (regularSlice_nonnegative_volume_CX9 H s₀ s hs h₀).1⟩

/-- A uniform bound on physical total volume makes the normalized total volume vanish. -/
theorem normalizedVolumeVanishes_of_physical_bound_CX9
    (s₀ : RegularSlice F.observation)
    (hbound : ∀ s : RegularSlice F.observation, s₀.time ≤ s.time →
      sliceTotalVolume_S10 s ≤ sliceTotalVolume_S10 s₀) :
    NormalizedVolumeVanishes_R2 F := by
  let V := (sliceTotalVolume_S10 s₀).toReal
  have hfin : sliceTotalVolume_S10 s₀ ≠ ⊤ :=
    (riemannianVolumeMeasure_isFiniteMeasure_of_compactSpace
      (I := ThreeModel) (M := s₀.stage.Carrier) s₀.metric).measure_univ_lt_top.ne
  have hlimit : Tendsto (fun t : ℝ => (Real.sqrt t⁻¹) ^ 3 * V) atTop (𝓝 0) := by
    have hi : Tendsto (fun t : ℝ => t⁻¹) atTop (𝓝 0) := tendsto_inv_atTop_zero
    have hs := Real.continuous_sqrt.continuousAt.tendsto.comp hi
    simpa only [Function.comp_def, Real.sqrt_zero, zero_pow (by decide : 3 ≠ 0), zero_mul] using
      (hs.pow 3).mul_const V
  intro η hη
  obtain ⟨T, hT⟩ := eventually_atTop.mp (hlimit.eventually (gt_mem_nhds hη))
  refine ⟨max s₀.time T, fun s hs => ?_⟩
  have htime : s₀.time ≤ s.time := (le_max_left _ _).trans hs
  have hsmall := hT s.time ((le_max_right _ _).trans hs)
  change normalizedTotalVolume s < ENNReal.ofReal η
  rw [normalizedTotalVolume_eq_S10]
  calc ENNReal.ofReal (Real.sqrt s.time⁻¹) ^ 3 * sliceTotalVolume_S10 s
      ≤ ENNReal.ofReal (Real.sqrt s.time⁻¹) ^ 3 * sliceTotalVolume_S10 s₀ := by
        gcongr
        exact hbound s htime
    _ = ENNReal.ofReal ((Real.sqrt s.time⁻¹) ^ 3 * V) := by
      rw [ENNReal.ofReal_mul (pow_nonneg (Real.sqrt_nonneg _) _),
        ENNReal.ofReal_pow (Real.sqrt_nonneg _), ENNReal.ofReal_toReal hfin]
    _ < ENNReal.ofReal η := (ENNReal.ofReal_lt_ofReal_iff hη).mpr hsmall

/-- The physical-volume bound is obtained from the profile, with no negative-branch input. -/
theorem normalizedVolumeVanishes_of_not_negative_R2
    (H : AnalyticSurgeryProfile F δ) (hn : ¬ EventuallyNegativeScalar_S13 F) :
    NormalizedVolumeVanishes_R2 F := by
  obtain ⟨s₀, _, _, h₀⟩ := exists_nonnegative_slice_after_CX9 hn 0
  exact normalizedVolumeVanishes_of_physical_bound_CX9 s₀
    (fun s hs => (regularSlice_nonnegative_volume_CX9 H s₀ s hs h₀).2)

/-- Vanishing total volume excludes fixed positive-radius, positive-volume seeds. -/
theorem noFixedNormalizedSeedSequence_of_volumeVanishes_R2
    (hvol : NormalizedVolumeVanishes_R2 F) : NoFixedNormalizedSeedSequence_R2 F := by
  intro S a v ha hv hseed
  obtain ⟨T, hT⟩ := hvol (v * a ^ 3) (mul_pos hv (pow_pos ha _))
  obtain ⟨j, hj⟩ := ((tendsto_atTop.mp S.times_tendsto) T).exists
  have hball : ballVolume (S.slices j).normalizedMetric (S.point j) a ≤
      normalizedTotalVolume_S13 (S.slices j) := measure_mono (subset_univ _)
  exact (not_lt_of_ge ((hseed j).2.trans hball)) (hT (S.slices j) hj)

end GC.LongTime.Ch12
