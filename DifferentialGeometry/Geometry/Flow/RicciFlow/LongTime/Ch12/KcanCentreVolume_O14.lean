import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.SpatialCanonicalWitnessBallVolume
import DifferentialGeometry.Geometry.Measure.BallComparison

/-!
# CH12-O14, group 2: the centre volume of the K-can leaf from a canonical witness

`centre_volume_of_witness_O14`: a (non-round) spatial canonical witness at `x` gives, in the
metric normalized by `Q = R(x)`, `vol B(x, b) ≥ κ b³` for every `0 < b ≤ C2^{-1/2}`, with
`κ = κ(ε, C1, C2)` from `exists_ball_volume_of_spatialCanonicalWitness`.  This is the hypothesis
`hvx` of `normalized_ball_volume_of_centre_O14` at a blow-up centre (uniform in the centre, no κ(t)).
-/

set_option autoImplicit false

noncomputable section

open Set
open scoped Manifold ContDiff ENNReal

namespace GC.LongTime.Ch12

open DifferentialGeometry DifferentialGeometry.Geometry.Riemannian
open DifferentialGeometry.Geometry.Curvature DifferentialGeometry.Integral.Measure
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
open DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn
open DifferentialGeometry.Tensor0SBundle

universe u

theorem centre_volume_of_witness_O14 (ε C1 C2 : ℝ) (hC2 : 0 < C2) :
    ∃ κ : ℝ, 0 < κ ∧ ∀ {P : OrientedThreeStage.{u}} {g : P.Metric} {x : P.Carrier}
      (W : SpatialCanonicalWitness g ε C1 C2 x), W.capTubeHasNeckChart ε →
      W.alternative.requiresVolume →
      ∀ b : ℝ, 0 < b → b ≤ (Real.sqrt C2)⁻¹ →
        ENNReal.ofReal (κ * b ^ 3) ≤
          riemannianVolumeMeasure ThreeModel P.Carrier
            (scaleMetric (metricScalarAt g x) W.Q_pos g)
            (riemannianBallOf (scaleMetric (metricScalarAt g x) W.Q_pos g) x b) := by
  obtain ⟨κ, hκ, hW⟩ := exists_ball_volume_of_spatialCanonicalWitness.{u} ε C1 C2
  refine ⟨κ, hκ, ?_⟩
  intro P g x W hchart hreq b hb hbC
  set Q := metricScalarAt g x with hQdef
  have hQ : 0 < Q := W.Q_pos
  have hsq : 0 < Real.sqrt Q := Real.sqrt_pos.mpr hQ
  set r := b / Real.sqrt Q with hrdef
  have hr : 0 < r := div_pos hb hsq
  -- curvature condition at the centre: r⁴ |Rm(x)|² ≤ 1
  have hx : x ∈ W.domain.carrier := interior_subset W.center_inside
  have hrm := W.rm_bound x hx
  have hcurv : r ^ 4 * normSq0S g x 4 (metricRm04At g x) ≤ 1 := by
    have hle : normSq0S (I := ThreeModel) g x 4 (metricRm04 g x) ≤ (C2 * Q) ^ 2 := by
      by_cases hN : 0 ≤ normSq0S (I := ThreeModel) g x 4 (metricRm04 g x)
      · rw [← Real.sq_sqrt hN]
        exact pow_le_pow_left₀ (Real.sqrt_nonneg _) hrm 2
      · push Not at hN
        nlinarith [sq_nonneg (C2 * Q)]
    have hr4 : r ^ 4 = b ^ 4 / Q ^ 2 := by
      rw [hrdef, div_pow]
      congr 1
      rw [show (4 : ℕ) = 2 * 2 from rfl, pow_mul, Real.sq_sqrt hQ.le]
    have hb2 : b ^ 2 ≤ C2⁻¹ := by
      have := pow_le_pow_left₀ hb.le hbC 2
      rwa [inv_pow, Real.sq_sqrt hC2.le] at this
    have hb4 : b ^ 4 * C2 ^ 2 ≤ 1 := by
      have h0 : 0 ≤ b ^ 2 := by positivity
      have : b ^ 2 * C2 ≤ 1 := by
        have := mul_le_mul_of_nonneg_right hb2 hC2.le
        rwa [inv_mul_cancel₀ hC2.ne'] at this
      have hu0 : 0 ≤ b ^ 2 * C2 := by positivity
      calc b ^ 4 * C2 ^ 2 = (b ^ 2 * C2) ^ 2 := by ring
        _ ≤ 1 := pow_le_one₀ hu0 this
    change r ^ 4 * normSq0S (I := ThreeModel) g x 4 (metricRm04 g x) ≤ 1
    rw [hr4]
    calc b ^ 4 / Q ^ 2 * normSq0S (I := ThreeModel) g x 4 (metricRm04 g x)
        ≤ b ^ 4 / Q ^ 2 * (C2 * Q) ^ 2 :=
          mul_le_mul_of_nonneg_left hle (by positivity)
      _ = b ^ 4 * C2 ^ 2 := by field_simp
      _ ≤ 1 := hb4
  have hv := hW W hchart hreq r hr hcurv
  have hdim : Module.finrank ℝ ThreeSpace = 3 := by simp [ThreeSpace]
  have hscaled :=
    (DifferentialGeometry.Geometry.Measure.riemannianVolumeMeasure_ball_ge_scaleMetric_iff
      g Q hQ x r (ENNReal.ofReal κ)).mpr (by
        rw [hdim, ← ENNReal.ofReal_pow hr.le, ← ENNReal.ofReal_mul hκ.le]; exact hv)
  have hscale : Real.sqrt Q * r = b := mul_div_cancel₀ _ hsq.ne'
  rw [hscale, hdim] at hscaled
  simpa only [ENNReal.ofReal_mul hκ.le, ENNReal.ofReal_pow hb.le] using hscaled

end GC.LongTime.Ch12
