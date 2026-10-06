import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.RegularSlice
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.ObservationTower
import DifferentialGeometry.Geometry.Collapse.CurvatureScale
import DifferentialGeometry.Geometry.Curvature.Metric.DerivativeNormScaling
import DifferentialGeometry.Geometry.Measure.BallComparison
import DifferentialGeometry.Geometry.Comparison.SectionalLowerBoundScaling

set_option autoImplicit false

noncomputable section

open DifferentialGeometry DifferentialGeometry.Topology
open DifferentialGeometry.PDE.RicciFlow DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
open DifferentialGeometry.Geometry.Collapse DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Riemannian Set
open scoped Manifold ContDiff ENNReal

namespace GC.LongTime.RegularSlice

universe u

theorem curvatureDerivativeNorm_normalizedMetric_le_of_physical_whole_ball
    {P : OrientedThreeStage.{u}} {g : P.Metric} {O : ObservationTower P g}
    (s : RegularSlice O) (K : ℕ) (w b : ℝ) (A : ℕ → ℝ)
    (hphysical : ∀ (p : s.stage.Carrier) (ρ : ℝ), 0 < ρ →
      ρ ≤ b * Real.sqrt s.time →
      (∃ z ∈ connectedComponent p, ¬ SectionalBoundedBelowAt s.metric z 0) →
      (∀ q ∈ riemannianBallOf s.metric p ρ,
        SectionalBoundedBelowAt s.metric q (-(ρ ^ 2)⁻¹)) →
      ENNReal.ofReal (w * ρ ^ 3) ≤ ballVolume s.metric p ρ →
      ∀ k : ℕ, k ≤ K → ∀ q ∈ riemannianBallOf s.metric p ρ,
        curvatureDerivativeNorm s.metric k q ≤ A k * (ρ ^ (k + 2))⁻¹) :
    ∀ (p : s.stage.Carrier) (r : ℝ), 0 < r → r ≤ b →
      (∃ z ∈ connectedComponent p,
        ¬ SectionalBoundedBelowAt s.normalizedMetric z 0) →
      (∀ q ∈ riemannianBallOf s.normalizedMetric p r,
        SectionalBoundedBelowAt s.normalizedMetric q (-(r ^ 2)⁻¹)) →
      ENNReal.ofReal (w * r ^ 3) ≤ ballVolume s.normalizedMetric p r →
      ∀ k : ℕ, k ≤ K → ∀ q ∈ riemannianBallOf s.normalizedMetric p r,
        curvatureDerivativeNorm s.normalizedMetric k q ≤ A k * (r ^ (k + 2))⁻¹ := by
  intro p r hr hrb hnegative hsectional hvolume
  let ρ := Real.sqrt s.time * r
  have ht : 0 < Real.sqrt s.time := Real.sqrt_pos.mpr s.positive
  have hρ : 0 < ρ := mul_pos ht hr
  have hρb : ρ ≤ b * Real.sqrt s.time := by
    simpa only [ρ, mul_comm b] using mul_le_mul_of_nonneg_left hrb ht.le
  have hundo : scaleMetric s.time s.positive s.normalizedMetric = s.metric := by
    apply SmoothRiemannianMetric.ext_inner
    intro x v z
    simp only [normalizedMetric, scaleMetric_inner, ← mul_assoc,
      mul_inv_cancel₀ s.positive.ne', one_mul]
  have hball : riemannianBallOf s.normalizedMetric p r =
      riemannianBallOf s.metric p ρ := by
    simpa only [hundo] using
      (riemannianBallOf_scaleMetric s.time s.positive s.normalizedMetric p r).symm
  have hnegativePhysical : ∃ z ∈ connectedComponent p,
      ¬ SectionalBoundedBelowAt s.metric z 0 := by
    obtain ⟨z, hzp, hz⟩ := hnegative
    refine ⟨z, hzp, ?_⟩
    intro hnonnegative
    apply hz
    simpa only [normalizedMetric, zero_div] using hnonnegative.scaleMetric
      s.time⁻¹ (inv_pos.mpr s.positive)
  have hsectionalPhysical : ∀ q ∈ riemannianBallOf s.metric p ρ,
      SectionalBoundedBelowAt s.metric q (-(ρ ^ 2)⁻¹) := by
    intro q hq
    have hqnormalized : q ∈ riemannianBallOf s.normalizedMetric p r := by
      rwa [hball]
    have hscaled := (hsectional q hqnormalized).scaleMetric
      s.time s.positive
    have hcoefficient : -(r ^ 2)⁻¹ / s.time = -(ρ ^ 2)⁻¹ := by
      dsimp [ρ]
      rw [mul_pow, Real.sq_sqrt s.positive.le]
      simp only [div_eq_mul_inv, mul_inv_rev]
      ring
    simpa only [hundo, hcoefficient] using hscaled
  have hweight (a : ℝ) (ha : 0 ≤ a) :
      ENNReal.ofReal (w * a ^ 3) = ENNReal.ofReal w * ENNReal.ofReal a ^ 3 := by
    rw [mul_comm w, ENNReal.ofReal_mul (pow_nonneg ha 3),
      ENNReal.ofReal_pow ha, mul_comm]
  have hvolumeScaling :
      ENNReal.ofReal w * ENNReal.ofReal ρ ^ 3 ≤
        ballVolume (scaleMetric s.time s.positive s.normalizedMetric) p ρ ↔
      ENNReal.ofReal w * ENNReal.ofReal r ^ 3 ≤ ballVolume s.normalizedMetric p r := by
    simpa [ρ, ballVolume, ThreeSpace] using
      Geometry.Measure.riemannianVolumeMeasure_ball_ge_scaleMetric_iff
        s.normalizedMetric s.time s.positive p r (ENNReal.ofReal w)
  have hvolumePhysical : ENNReal.ofReal (w * ρ ^ 3) ≤ ballVolume s.metric p ρ := by
    rw [hweight ρ hρ.le]
    have hscaled := hvolumeScaling.mpr (by rwa [← hweight r hr.le])
    rwa [hundo] at hscaled
  have hbound := hphysical p ρ hρ hρb hnegativePhysical hsectionalPhysical hvolumePhysical
  intro k hk q hq
  have hqphysical : q ∈ riemannianBallOf s.metric p ρ := by
    rwa [← hball]
  have hnorm : curvatureDerivativeNorm s.normalizedMetric k q =
      (Real.sqrt s.time) ^ (k + 2) * curvatureDerivativeNorm s.metric k q :=
    curvatureDerivativeNorm_scaleMetric_inv s.metric s.time s.positive k q
  rw [hnorm]
  calc
    (Real.sqrt s.time) ^ (k + 2) * curvatureDerivativeNorm s.metric k q ≤
        (Real.sqrt s.time) ^ (k + 2) * (A k * (ρ ^ (k + 2))⁻¹) :=
      mul_le_mul_of_nonneg_left (hbound k hk q hqphysical) (pow_nonneg ht.le _)
    _ = A k * (r ^ (k + 2))⁻¹ := by
      dsimp [ρ]
      rw [mul_pow, mul_inv_rev]
      calc
        (Real.sqrt s.time) ^ (k + 2) *
            (A k * ((r ^ (k + 2))⁻¹ * ((Real.sqrt s.time) ^ (k + 2))⁻¹)) =
            (A k * (r ^ (k + 2))⁻¹) *
              ((Real.sqrt s.time) ^ (k + 2) * ((Real.sqrt s.time) ^ (k + 2))⁻¹) := by ring
        _ = A k * (r ^ (k + 2))⁻¹ := by
          rw [mul_inv_cancel₀ (pow_ne_zero _ ht.ne'), mul_one]

end GC.LongTime.RegularSlice
