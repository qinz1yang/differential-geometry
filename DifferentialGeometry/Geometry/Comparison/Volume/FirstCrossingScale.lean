import DifferentialGeometry.Analysis.Calculus.FirstPositiveCrossing
import DifferentialGeometry.Analysis.Integration.Measure.NormalizedHausdorffMeasure
import DifferentialGeometry.Analysis.Integration.Measure.OpenSubtypeBall
import DifferentialGeometry.Bundle.FiberBundleHausdorff
import DifferentialGeometry.Geometry.Comparison.Volume.SmallRadius
import DifferentialGeometry.Geometry.Comparison.Volume.SmallBall
import DifferentialGeometry.Geometry.Collapse.CurvatureScale
import Mathlib.MeasureTheory.Measure.Continuity
import Mathlib.Topology.Order.AtTopBotIxx

/-!
# First volume scales on closed Riemannian three-manifolds

Open sublevel measures are left-continuous by continuity from below. Applied to the
metric-specific Riemannian volume, compactness and the sharp Euclidean small-ball
estimate give a positive attained first cubic volume scale. No sphere-null premise is used.
-/

set_option autoImplicit false

noncomputable section

open Bundle Filter Manifold MeasureTheory Set
open scoped ContDiff ENNReal Manifold Topology

namespace MeasureTheory

theorem measure_lt_ofReal_monotone {X : Type*} [MeasurableSpace X]
    (μ : Measure X) (D : X → ℝ≥0∞) :
    Monotone (fun r : ℝ => μ {x | D x < ENNReal.ofReal r}) := by
  intro r s hrs
  exact measure_mono (fun x hx => hx.trans_le (ENNReal.ofReal_le_ofReal hrs))

theorem measure_lt_ofReal_continuousWithinAt_left {X : Type*} [MeasurableSpace X]
    (μ : Measure X) (D : X → ℝ≥0∞) (r : ℝ) :
    ContinuousWithinAt (fun s : ℝ => μ {x | D x < ENNReal.ofReal s}) (Iio r) r := by
  let A : Iio r → Set X := fun s => {x | D x < ENNReal.ofReal s.val}
  have hmono : Monotone A := by
    intro s t hst x hx
    exact hx.trans_le (ENNReal.ofReal_le_ofReal hst)
  have hunion : (⋃ s, A s) = {x | D x < ENNReal.ofReal r} := by
    ext x
    constructor
    · intro hx
      obtain ⟨s, hs⟩ := mem_iUnion.mp hx
      exact hs.trans_le (ENNReal.ofReal_le_ofReal s.property.le)
    · intro hx
      have hevent : ∀ᶠ s in 𝓝[<] r, D x < ENNReal.ofReal s :=
        ENNReal.continuous_ofReal.continuousAt.continuousWithinAt
          (Ioi_mem_nhds hx)
      have hleft : ∀ᶠ s in 𝓝[<] r, s < r := self_mem_nhdsWithin
      obtain ⟨s, hs, hDs⟩ := (hleft.and hevent).exists
      exact mem_iUnion.mpr ⟨⟨s, hs⟩, hDs⟩
  have h := tendsto_measure_iUnion_atTop (μ := μ) hmono
  rw [hunion] at h
  exact (tendsto_comp_coe_Iio_atTop (a := r)).mp h

theorem normalizedHausdorffMeasure_eball_monotone {X : Type*}
    [EMetricSpace X] [MeasurableSpace X] [BorelSpace X] (n : ℕ) (p : X) :
    Monotone (fun r : ℝ => normalizedHausdorffMeasure n
      (Metric.eball p (ENNReal.ofReal r))) :=
  measure_lt_ofReal_monotone (normalizedHausdorffMeasure n) (fun x => edist x p)

theorem normalizedHausdorffMeasure_eball_continuousWithinAt_left {X : Type*}
    [EMetricSpace X] [MeasurableSpace X] [BorelSpace X] (n : ℕ) (p : X) (r : ℝ) :
    ContinuousWithinAt (fun s : ℝ => normalizedHausdorffMeasure n
      (Metric.eball p (ENNReal.ofReal s))) (Iio r) r :=
  measure_lt_ofReal_continuousWithinAt_left
    (normalizedHausdorffMeasure n) (fun x => edist x p) r

end MeasureTheory

namespace DifferentialGeometry.Geometry.Collapse

open DifferentialGeometry
open DifferentialGeometry.Geometry.Riemannian
open DifferentialGeometry.Geometry.Riemannian.VolumeComparison
open DifferentialGeometry.Integral.Measure

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [T2Space M] [SigmaCompactSpace M]

private local instance : MeasurableSpace M := borel M
private local instance : BorelSpace M := ⟨rfl⟩

theorem ballVolume_monotone (g : SmoothRiemannianMetric I M) (p : M) :
    Monotone (ballVolume g p) :=
  measure_lt_ofReal_monotone (riemannianVolumeMeasure (I := I) (M := M) g)
    (riemannianEDistOf (I := I) g p)

theorem ballVolume_continuousWithinAt_left
    (g : SmoothRiemannianMetric I M) (p : M) (r : ℝ) :
    ContinuousWithinAt (ballVolume g p) (Iio r) r :=
  measure_lt_ofReal_continuousWithinAt_left
    (riemannianVolumeMeasure (I := I) (M := M) g) (riemannianEDistOf (I := I) g p) r

variable [CompactSpace M]

theorem ballVolume_ne_top (g : SmoothRiemannianMetric I M) (p : M) (r : ℝ) :
    ballVolume g p r ≠ ⊤ := by
  let := riemannianVolumeMeasure_isFiniteMeasure_of_compactSpace (I := I) (M := M) g
  exact measure_ne_top (riemannianVolumeMeasure (I := I) (M := M) g) _

theorem ballVolume_toReal_monotone (g : SmoothRiemannianMetric I M) (p : M) :
    Monotone (fun r => (ballVolume g p r).toReal) := by
  intro r s hrs
  exact ENNReal.toReal_mono (ballVolume_ne_top g p s) (ballVolume_monotone g p hrs)

theorem ballVolume_toReal_continuousWithinAt_left
    (g : SmoothRiemannianMetric I M) (p : M) (r : ℝ) :
    ContinuousWithinAt (fun s => (ballVolume g p s).toReal) (Iio r) r :=
  (ENNReal.tendsto_toReal (ballVolume_ne_top g p r)).comp
    (ballVolume_continuousWithinAt_left g p r)

theorem ballVolume_toReal_pos
    (g : SmoothRiemannianMetric I M) (p : M) {r : ℝ} (hr : 0 < r) :
    0 < (ballVolume g p r).toReal :=
  edist_vol_pos (I := I) g p hr

theorem ballVolume_toReal_le_total
    (g : SmoothRiemannianMetric I M) (p : M) (r : ℝ) :
    (ballVolume g p r).toReal ≤
      (riemannianVolumeMeasure (I := I) (M := M) g univ).toReal := by
  let := riemannianVolumeMeasure_isFiniteMeasure_of_compactSpace (I := I) (M := M) g
  exact ENNReal.toReal_mono (measure_ne_top _ _) (measure_mono (subset_univ _))

def firstVolumeScale (g : SmoothRiemannianMetric I M) (p : M) (w : ℝ) : ℝ :=
  Real.firstPositiveCrossing (fun r => (ballVolume g p r).toReal) (fun r => w * r ^ 3)

theorem euclideanUnitBallVolume_three_eq :
    euclideanUnitBallVolume 3 = 4 * Real.pi / 3 := by
  rw [← euclidean_volume_unitBall 3 (by norm_num), EuclideanSpace.volume_ball_fin_three]
  simp only [ENNReal.ofReal_one, one_pow, one_mul]
  rw [ENNReal.toReal_ofReal (by positivity)]
  ring

variable [I.Boundaryless]

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
private theorem exists_ballVolume_gt_cube_connected [ConnectedSpace M]
    (g : SmoothRiemannianMetric I M) (hdim : Module.finrank ℝ E = 3)
    (p : M) {w : ℝ} (hw : 0 < w) (hwc : w < 4 * Real.pi / 3) :
    ∃ a > 0, ∀ r, 0 < r → r ≤ a → w * r ^ 3 < (ballVolume g p r).toReal := by
  let : IsManifold I 1 M := IsManifold.of_le (n := ∞) (by decide)
  let : T2Space (TangentBundle I M) := inferInstance
  let : NeZero (Module.finrank ℝ E) := ⟨by rw [hdim]; norm_num⟩
  let : RiemannianBundle (fun x : M => TangentSpace I x) := ⟨g.toRiemannianMetric⟩
  let : IsContinuousRiemannianBundle E (fun x : M => TangentSpace I x) := by
    refine ⟨g.inner, g.contMDiff.continuous, ?_⟩
    intro x v z
    rfl
  let : PseudoEMetricSpace M := PseudoEMetricSpace.ofRiemannianMetric I M
  have hEnorm : IsMetricNorm (I := I) (M := M) g := by
    intro x v
    rw [← ofReal_norm, norm_eq_sqrt_real_inner]
    rfl
  have hvolume (r : ℝ) : VolumeComparison.ballVolume g p r = ballVolume g p r := rfl
  let c := euclideanUnitBallVolume 3
  have hc : 0 < c := euclideanUnitBallVolume_pos 3
  have hwc' : w < c := by simpa only [c, euclideanUnitBallVolume_three_eq] using hwc
  let b := (c + w) / 2
  have hb : 0 < b := by dsimp only [b]; linarith
  have hwb : w < b := by dsimp only [b]; linarith
  have hbc : b < c := by dsimp only [b]; linarith
  let ε := 1 - b / c
  have hε : 0 < ε := sub_pos.mpr ((div_lt_one hc).mpr hbc)
  have hε1 : ε < 1 := by dsimp only [ε]; linarith [div_pos hb hc]
  obtain ⟨ρ, hρ, hsmall⟩ := exists_ballVolume_euclidean_ratio (I := I) g hEnorm p ε hε hε1
  refine ⟨ρ / 2, half_pos hρ, ?_⟩
  intro r hr hra
  have hrρ : r < ρ := hra.trans_lt (half_lt_self hρ)
  have hlow := (hsmall hr hrρ).1
  rw [hvolume] at hlow
  have hreal := ENNReal.toReal_mono (ballVolume_ne_top g p r) hlow
  rw [volume_unitBall_eq_ofReal_euclideanUnitBallVolume (E := E), hdim] at hreal
  simp only [ENNReal.toReal_mul, ENNReal.toReal_ofReal (sub_nonneg.mpr hε1.le),
    ENNReal.toReal_ofReal (pow_nonneg hr.le 3),
    ENNReal.toReal_ofReal (euclideanUnitBallVolume_pos 3).le] at hreal
  have hcoeff : (1 - ε) * c = b := by
    dsimp only [ε]
    rw [sub_sub_cancel, div_mul_cancel₀ b hc.ne']
  have hlower : b * r ^ 3 ≤ (ballVolume g p r).toReal := by
    calc
      b * r ^ 3 = (1 - ε) * (r ^ 3 * c) := by rw [← hcoeff]; ring
      _ ≤ (ballVolume g p r).toReal := hreal
  exact (mul_lt_mul_of_pos_right hwb (pow_pos hr 3)).trans_le hlower

theorem exists_ballVolume_gt_cube
    (g : SmoothRiemannianMetric I M) (hdim : Module.finrank ℝ E = 3)
    (p : M) {w : ℝ} (hw : 0 < w) (hwc : w < 4 * Real.pi / 3) :
    ∃ a > 0, ∀ r, 0 < r → r ≤ a → w * r ^ 3 < (ballVolume g p r).toReal := by
  let U := connectedComponentOpen (I := I) p
  let q : U := connectedComponentPoint (I := I) p
  let : ConnectedSpace U := connectedComponentOpen_connectedSpace (I := I) p
  let : CompactSpace U := connectedComponentOpen_compactSpace (I := I) p
  let : SigmaCompactSpace U := isSigmaCompact_iff_sigmaCompactSpace.mp
    (Geometry.isSigmaCompact_of_isOpen I U.isOpen)
  have hU : IsClosed (U : Set M) := isClosed_connectedComponent
  have hvolume (r : ℝ) : ballVolume (g.restrictOpen U) q r = ballVolume g p r :=
    riemannianVolumeMeasure_ball_restrictOpen_of_isClosed g U hU q r
  obtain ⟨a, ha, hsmall⟩ :=
    exists_ballVolume_gt_cube_connected (g.restrictOpen U) hdim q hw hwc
  refine ⟨a, ha, ?_⟩
  intro r hr hra
  simpa only [hvolume] using hsmall r hr hra

theorem firstVolumeScale_spec
    (g : SmoothRiemannianMetric I M) (hdim : Module.finrank ℝ E = 3)
    (p : M) {w : ℝ} (hw : 0 < w) (hwc : w < 4 * Real.pi / 3) :
    0 < firstVolumeScale g p w ∧
      (ballVolume g p (firstVolumeScale g p w)).toReal =
        w * firstVolumeScale g p w ^ 3 ∧
      ∀ r, 0 < r → r < firstVolumeScale g p w →
        w * r ^ 3 < (ballVolume g p r).toReal := by
  apply Real.firstPositiveCrossing_cube_spec_of_bounded
    ((ballVolume_toReal_monotone g p).monotoneOn (Ioi 0))
  · intro r hr
    exact ballVolume_toReal_continuousWithinAt_left g p r
  · exact hw
  · exact exists_ballVolume_gt_cube g hdim p hw hwc
  · refine ⟨(riemannianVolumeMeasure (I := I) (M := M) g univ).toReal, ?_⟩
    intro r hr
    exact ballVolume_toReal_le_total g p r

theorem ballVolume_firstVolumeScale
    (g : SmoothRiemannianMetric I M) (hdim : Module.finrank ℝ E = 3)
    (p : M) {w : ℝ} (hw : 0 < w) (hwc : w < 4 * Real.pi / 3) :
    ballVolume g p (firstVolumeScale g p w) =
      ENNReal.ofReal (w * firstVolumeScale g p w ^ 3) := by
  rw [← (firstVolumeScale_spec g hdim p hw hwc).2.1]
  exact (ENNReal.ofReal_toReal (ballVolume_ne_top g p (firstVolumeScale g p w))).symm

theorem firstVolumeScale_eq_firstPositiveLevel
    (g : SmoothRiemannianMetric I M) (hdim : Module.finrank ℝ E = 3)
    (p : M) {w : ℝ} (hw : 0 < w) (hwc : w < 4 * Real.pi / 3) :
    firstVolumeScale g p w =
      Real.firstPositiveLevel (fun r => (ballVolume g p r).toReal / r ^ 3) w := by
  apply Real.firstPositiveCrossing_cube_eq_firstPositiveLevel
    ((ballVolume_toReal_monotone g p).monotoneOn (Ioi 0))
  · intro r hr
    exact ballVolume_toReal_continuousWithinAt_left g p r
  · exact exists_ballVolume_gt_cube g hdim p hw hwc
  · obtain ⟨hpos, heq, hbefore⟩ := firstVolumeScale_spec g hdim p hw hwc
    exact ⟨firstVolumeScale g p w, hpos, heq.le⟩

theorem firstVolumeScale_strictAntiOn
    (g : SmoothRiemannianMetric I M) (hdim : Module.finrank ℝ E = 3) (p : M) :
    StrictAntiOn (firstVolumeScale g p) (Ioo 0 (4 * Real.pi / 3)) := by
  intro u hu v hv huv
  obtain ⟨hru, heu, hbu⟩ := firstVolumeScale_spec g hdim p hu.1 hu.2
  obtain ⟨hrv, hev, hbv⟩ := firstVolumeScale_spec g hdim p hv.1 hv.2
  by_contra! h
  rcases h.eq_or_lt with h | h
  · rw [← h, heu] at hev
    exact (mul_lt_mul_of_pos_right huv (pow_pos hru 3)).ne hev
  · have hh := hbv (firstVolumeScale g p u) hru h
    rw [heu] at hh
    linarith [mul_lt_mul_of_pos_right huv (pow_pos hru 3)]

end DifferentialGeometry.Geometry.Collapse
