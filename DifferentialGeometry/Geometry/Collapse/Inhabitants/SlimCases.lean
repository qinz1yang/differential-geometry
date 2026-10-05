import DifferentialGeometry.Geometry.Collapse.Inhabitants.SlimSpherePacket
import DifferentialGeometry.Geometry.Collapse.FiniteSurface.SlimSurfaceFactorApplications
import DifferentialGeometry.Geometry.Metric.Approximation.IsometricKleinerLottApproximation

/-!
The fixed round cylinder supplies a packet, a product model and its surface factor at one
arbitrarily small common approximation scale. The geometric splitting and curvature bounds
are reused from the cylinder factory; both thresholds are imposed on the same approximation.
-/

set_option autoImplicit false

noncomputable section

open Bundle Manifold Set Metric
open DifferentialGeometry DifferentialGeometry.Geometry DifferentialGeometry.Geometry.Metric
open DifferentialGeometry.Geometry.Riemannian DifferentialGeometry.Geometry.Collapse
open GC.MetricGeometry
open scoped Manifold ContDiff

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace
attribute [local instance] threeMetric threeUniform threeEMetric threePseudoMetric threeBundle
  threeRiemannian threeContinuous threeComplete threeSigmaCompact

open private exists_slimSphereThree_orientation
from DifferentialGeometry.Geometry.Collapse.Inhabitants.SlimSpherePacket

namespace DifferentialGeometry.Geometry.Collapse

theorem exists_slimCylinder_packet_model_surface (τ : ℝ) (hτ : 0 < τ) :
    ∃ Δ β : ℝ, 1 ≤ Δ ∧ 0 < β ∧ β < τ ∧ β < 1 ∧
      ∃ (Y : Type) (mY : MetricSpace Y), letI factorMetric := mY
      ∃ (y : Y) (p : sphereCylinderRechart)
        (α : KleinerLottApprox p (WithLp.toLp 2 ((0 : ℝ), y)) β),
        (∀ a b : Y, @dist Y factorMetric.toDist a b ≤ 10 ^ 3 * Δ) ∧
        ∃ P : SlimPacket slimSphereThreeMetric slimSphereThreeMetricNorm Δ (1 / 100) α,
        ∃ Q : SlimProductModel P.toSlimChart 5, Nonempty (SlimSurfaceFactor Q) := by
  obtain ⟨Δ, hΔ, Y, mY, y, e, he, hdiam⟩ := exists_slimSphereThree_splitting
  let factorMetric : MetricSpace Y := mY
  obtain ⟨o⟩ := exists_slimSphereThree_orientation
  obtain ⟨A, hA⟩ := exists_slimSphereThree_curvature_bounds 5
  let p := sphereCylinderRechartDiffeomorph (slimSphereLine 0)
  let μ := Integral.Measure.riemannianVolumeMeasure (𝓡 3)
    sphereCylinderRechart slimSphereThreeMetric
  let volumePositive : MeasureTheory.Measure.IsOpenPosMeasure μ :=
    Integral.Measure.riemannianVolumeMeasure_isOpenPosMeasure slimSphereThreeMetric
  have hvol0 : 0 < μ (ball p 1) := isOpen_ball.measure_pos μ ⟨p, mem_ball_self zero_lt_one⟩
  obtain ⟨v, hv, hvμ⟩ := ENNReal.lt_iff_exists_nnreal_btwn.mp hvol0
  have hvreal : 0 < (v : ℝ) := by exact_mod_cast hv
  have hvol : ENNReal.ofReal (v : ℝ) ≤ μ (ball p 1) := by simpa using hvμ.le
  obtain ⟨βP, hβP, packet⟩ := exists_slimPacket_threshold hΔ
    (by norm_num : 0 < (1 / 100 : ℝ)) le_rfl 5 (by decide)
    zero_lt_one hvreal (Function.const ℝ A)
  obtain ⟨βS, hβS, surface⟩ := slimChart_model_surface_threshold hΔ
    (by norm_num : 0 < (1 / 100 : ℝ)) le_rfl 5 (by decide)
    zero_lt_one hvreal (Function.const ℝ A) zero_lt_one 1
  let bound := min (min βP βS) (min τ 1)
  have hbound : 0 < bound := lt_min (lt_min hβP hβS) (lt_min hτ zero_lt_one)
  let β := bound / 2
  have hβ : 0 < β := half_pos hbound
  have hβbound : β < bound := half_lt_self hbound
  have hβP' : β < βP := hβbound.trans_le ((min_le_left _ _).trans (min_le_left _ _))
  have hβS' : β < βS := hβbound.trans_le ((min_le_left _ _).trans (min_le_right _ _))
  have hβτ : β < τ := hβbound.trans_le ((min_le_right _ _).trans (min_le_left _ _))
  have hβ1 : β < 1 := hβbound.trans_le ((min_le_right _ _).trans (min_le_right _ _))
  let α := e.toKleinerLottApprox he hβ hβ1
  have derivatives : ∀ R, 0 < R → R < β⁻¹ → ∀ k ≤ 5,
      ∀ x ∈ ball p R, CheegerGromovCompactness.curvDerivNorm k slimSphereThreeMetric x ≤ A :=
    fun R hR hRβ k hk x hx => hA k hk x
  have sectional : ∀ x ∈ ball p β⁻¹,
      SectionalBoundedBelowAt slimSphereThreeMetric x (-β ^ 2) := by
    intro x hx v w
    exact (mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr (sq_nonneg β))
      (sectionalCurvatureDenominator_nonneg slimSphereThreeMetric x v w)).trans
        (by simpa only [zero_mul] using slimSphereThree_sectional_nonneg x v w)
  obtain ⟨⟨P⟩, every⟩ := packet β hβ hβP' sphereCylinderRechart slimSphereThreeMetric
    slimSphereThreeMetricNorm o p hvol derivatives sectional Y y α hdiam
  obtain ⟨Q, source, comparison, S, classification⟩ := surface β hβ hβS'
    sphereCylinderRechart slimSphereThreeMetric slimSphereThreeMetricNorm o p
    hvol derivatives sectional Y y α hdiam P.toSlimChart
  exact ⟨Δ, β, hΔ, hβ, hβτ, hβ1, Y, mY, y, p, α, hdiam, P, Q, ⟨S⟩⟩

end DifferentialGeometry.Geometry.Collapse
