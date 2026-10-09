import DifferentialGeometry.Geometry.Collapse.Inhabitants.SlimSphere
import DifferentialGeometry.Geometry.Collapse.Inhabitants.SphereRechart
import DifferentialGeometry.Geometry.Collapse.FiniteSurface.SlimFibreTypeThresholdApplications
import DifferentialGeometry.Geometry.Collapse.FiniteSurface.SlimModelEmbeddingThreshold
import DifferentialGeometry.Geometry.Metric.PullbackCompleteness
import DifferentialGeometry.Geometry.Curvature.CurvatureOperator.Derivatives.Pullback
import DifferentialGeometry.Geometry.Curvature.Naturality.Pullback.Cross
import DifferentialGeometry.Analysis.Integration.Measure.Riemannian.Properties
import DifferentialGeometry.Topology.Manifold.ProductOrientation
import DifferentialGeometry.Topology.Manifold.SphereOrientation
import DifferentialGeometry.Topology.Manifold.SmoothOrientationPullback
import DifferentialGeometry.Topology.Manifold.SmoothOrientationCompatible

/-!
The actual recharted round cylinder has an intrinsic metric, a slim packet and a product
model for the same chosen chart. All geometric data precede the common threshold choice.
-/

set_option autoImplicit false
noncomputable section
open Bundle Manifold Set Metric
open DifferentialGeometry DifferentialGeometry.Geometry DifferentialGeometry.Geometry.Metric
open DifferentialGeometry.Geometry.Riemannian
open DifferentialGeometry.Geometry.Collapse GC.MetricGeometry
open scoped Manifold ContDiff
attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace
attribute [local instance] sphereDimension cylinderDimension sphereCompact sphereConnected
  intrinsicMetric intrinsicUniform intrinsicEMetric intrinsicPseudoMetric intrinsicBundle
  cylinderRiemannian cylinderContinuous cylinderComplete

namespace DifferentialGeometry.Geometry.Collapse

local notation "C" => sphereCylinderRechart

def slimSphereThreeMetric : SmoothRiemannianMetric (𝓡 3) C :=
  Diffeomorph.pullbackMetricCross slimSphereMetric sphereCylinderRechartDiffeomorph.symm

abbrev slimSphereThreeMetricSpace : MetricSpace C := inducedMetricSpace slimSphereThreeMetric
local instance threeMetric : MetricSpace C := slimSphereThreeMetricSpace
local instance threeUniform : UniformSpace C := threeMetric.toUniformSpace
local instance threeEMetric : PseudoEMetricSpace C := threeMetric.toPseudoEMetricSpace
local instance threePseudoMetric : PseudoMetricSpace C := threeMetric.toPseudoMetricSpace
abbrev slimSphereThreeRiemannianBundle : RiemannianBundle (fun x : C => TangentSpace (𝓡 3) x) :=
  ⟨slimSphereThreeMetric.toRiemannianMetric⟩
local instance threeBundle : RiemannianBundle (fun x : C => TangentSpace (𝓡 3) x) :=
  slimSphereThreeRiemannianBundle

theorem slimSphereThreeMetricNorm : IsMetricNorm slimSphereThreeMetric :=
  isMetricNorm_of_smoothRiemannianMetric slimSphereThreeMetric

local instance threeRiemannian : IsRiemannianManifold (𝓡 3) C :=
  inducedMetricSpace_isRiemannianManifold slimSphereThreeMetric
local instance threeContinuous : IsContinuousRiemannianBundle (EuclideanSpace ℝ (Fin 3))
    (fun x : C => TangentSpace (𝓡 3) x) :=
  isContinuousRiemannianBundle_of_smoothRiemannianMetric slimSphereThreeMetric
local instance threeSigmaCompact : SigmaCompactSpace C :=
  sphereCylinderRechartDiffeomorph.symm.toHomeomorph.isClosedEmbedding.sigmaCompactSpace
local instance threeComplete : CompleteSpace C :=
  (RiemannianMetricComplete.pullbackCross slimSphereMetric
    sphereCylinderRechartDiffeomorph.symm
    ((RiemannianMetricComplete.of_compact
      (roundMetric (E := EuclideanSpace ℝ (Fin 3)) (n := 2))).prod
        (euclideanMetric_complete (E := ℝ)))).complete
local instance threeDimension : NeZero (Module.finrank ℝ (EuclideanSpace ℝ (Fin 3))) :=
  ⟨by simp⟩

open private slimSphereLine_isometry slimSphere_factor_bound slimSphere_dist_upper
from DifferentialGeometry.Geometry.Collapse.Inhabitants.SlimSphere

local notation "M" => sphereCylinder
local notation "IC" => ModelWithCorners.prod (𝓡 2) 𝓘(ℝ, ℝ)

local instance threeC1 : IsManifold (𝓡 3) 1 C :=
  IsManifold.of_le (n := ∞) (by decide)
local instance sourceC1 : IsManifold IC 1 M :=
  IsManifold.of_le (n := ∞) (by decide)

def slimSphereThreeIsometry : C ≃ᵢ M where
  toEquiv := sphereCylinderRechartDiffeomorph.symm.toEquiv
  isometry_toFun := by
    apply Isometry.of_dist_eq
    intro a b
    change (riemannianEDistOf slimSphereMetric
      (sphereCylinderRechartDiffeomorph.symm a)
      (sphereCylinderRechartDiffeomorph.symm b)).toReal =
        (riemannianEDistOf slimSphereThreeMetric a b).toReal
    exact congrArg ENNReal.toReal
      (riemannianEDistOf_pullbackMetricCross slimSphereMetric
        sphereCylinderRechartDiffeomorph.symm a b).symm

theorem slimSphereThree_sectional_nonneg (x : C) :
    SectionalBoundedBelowAt slimSphereThreeMetric x 0 := by
  intro v w
  rw [zero_mul]
  rw [slimSphereThreeMetric, Curvature.metricRm04Standard_pullbackCross]
  simpa only [zero_mul] using slimSphereMetric_sectional_nonneg
    (sphereCylinderRechartDiffeomorph.symm x)
    (mfderiv (𝓡 3) IC sphereCylinderRechartDiffeomorph.symm x v)
    (mfderiv (𝓡 3) IC sphereCylinderRechartDiffeomorph.symm x w)

theorem exists_slimSphereThree_curvature_bounds (K : ℕ) :
    ∃ A : ℝ, ∀ k ≤ K, ∀ x : C,
      CheegerGromovCompactness.curvDerivNorm k slimSphereThreeMetric x ≤ A := by
  obtain ⟨A, hA⟩ := exists_slimSphere_curvature_bounds K
  refine ⟨A, fun k hk x => ?_⟩
  exact (PDE.RicciFlow.Perelman.KappaSolutions.curvDerivNorm_pullbackMetricCross
    slimSphereMetric sphereCylinderRechartDiffeomorph.symm k x).trans_le
      (hA k hk (sphereCylinderRechartDiffeomorph.symm x))

private theorem exists_slimSphereThree_orientation :
    Nonempty (ManifoldOrientation (𝓡 3) C 3) := by
  let realSmooth := Topology.Manifold.euclideanSmoothOrientation ℝ
    (Module.finBasis ℝ ℝ).orientation
  obtain ⟨realOrientation, hreal⟩ :=
    Topology.Manifold.exists_manifoldOrientation_eq_of_smoothOrientation 𝓘(ℝ, ℝ) realSmooth
  have realOne : ManifoldOrientation 𝓘(ℝ, ℝ) ℝ 1 := by simpa using realOrientation
  let product := productOrientation (𝓡 2) 𝓘(ℝ, ℝ) (by decide) (by decide)
    (sphereOrientation 2 (by decide)) realOne
  let sourceSmooth := Topology.Manifold.smoothOrientationOfManifoldOrientation IC
    (by simpa using product)
  let targetSmooth := Topology.Manifold.pullbackSmoothOrientation (𝓡 3) IC
    sphereCylinderRechartDiffeomorph.symm sphereCylinderRechartDiffeomorph.symm.contMDiff
    (fun x => (sphereCylinderRechartDiffeomorph.symm.mfderivToContinuousLinearEquiv
      (by simp) x).bijective) sourceSmooth
  obtain ⟨O, hO⟩ :=
    Topology.Manifold.exists_manifoldOrientation_eq_of_smoothOrientation (𝓡 3) targetSmooth
  exact ⟨by simpa using O⟩

theorem exists_slimSphereThree_splitting :
    ∃ Δ : ℝ, 1 ≤ Δ ∧
      ∃ (Y : Type) (mY : MetricSpace Y), letI := mY
      ∃ (y : Y) (e : C ≃ᵢ WithLp 2 (ℝ × Y)),
        e (sphereCylinderRechartDiffeomorph (slimSphereLine 0)) =
          WithLp.toLp 2 ((0 : ℝ), y) ∧ ∀ a b : Y, dist a b ≤ 10 ^ 3 * Δ := by
  obtain ⟨hproper, hcomp, hsegments⟩ := model_lcp04_clauses_of_sectional_nonneg
    slimSphereMetric slimSphereMetricNorm slimSphereMetric_sectional_nonneg
  obtain ⟨D, hD, hb⟩ := slimSphere_factor_bound
  let Y := {x : M // Comparison.Toponogov.lineCoordinate slimSphereLine x = 0}
  let y : Y := ⟨slimSphereLine 0,
    Comparison.Toponogov.lineCoordinate_apply_isometry slimSphereLine_isometry 0⟩
  let e₀ := Comparison.Toponogov.lineSplitting hcomp slimSphereLine_isometry hsegments
  let e := slimSphereThreeIsometry.trans e₀
  have height (x : Y) : |x.val.2| ≤ D := by
    have hc := (Comparison.Toponogov.lipschitzWith_lineCoordinate hcomp
      slimSphereLine_isometry).dist_le_mul x.val (slimSphereLine x.val.2)
    have hd := slimSphere_dist_upper D hD hb x.val (slimSphereLine x.val.2)
    rw [x.property, Comparison.Toponogov.lineCoordinate_apply_isometry
      slimSphereLine_isometry, Real.dist_eq, zero_sub, abs_neg] at hc
    simp only [NNReal.coe_one, one_mul] at hc
    exact hc.trans (by simpa only [slimSphereLine, sub_self, abs_zero, add_zero] using hd)
  let Δ := max 1 (3 * D)
  refine ⟨Δ, le_max_left _ _, Y, inferInstance, y, e, ?_, ?_⟩
  · change e₀ (sphereCylinderRechartDiffeomorph.symm
      (sphereCylinderRechartDiffeomorph (slimSphereLine 0))) = _
    rw [sphereCylinderRechartDiffeomorph.symm_apply_apply]
    exact Comparison.Toponogov.lineSplitting_apply_line hcomp slimSphereLine_isometry hsegments 0
  · intro a b
    have hu := slimSphere_dist_upper D hD hb a.val b.val
    have hab : |a.val.2 - b.val.2| ≤ |a.val.2| + |b.val.2| := abs_sub a.val.2 b.val.2
    change dist a.val b.val ≤ _
    have hΔ : 1 ≤ Δ := le_max_left _ _
    have hDΔ : 3 * D ≤ Δ := le_max_right _ _
    nlinarith [height a, height b]

theorem exists_slimSpherePacket :
    ∃ Δ β : ℝ, 1 ≤ Δ ∧ 0 < β ∧ β < 1 ∧
      ∃ (Y : Type) (mY : MetricSpace Y), letI := mY
      ∃ (y : Y) (p : C) (α : KleinerLottApprox p (WithLp.toLp 2 ((0 : ℝ), y)) β),
        (∀ a b : Y, dist a b ≤ 10 ^ 3 * Δ) ∧
        ∃ P : SlimPacket slimSphereThreeMetric slimSphereThreeMetricNorm Δ (1 / 100) α,
          Nonempty (SlimProductModel P.toSlimChart 5) := by
  obtain ⟨Δ, hΔ, Y, mY, y, e, he, hdiam⟩ := exists_slimSphereThree_splitting
  let factorMetric : MetricSpace Y := mY
  let p := sphereCylinderRechartDiffeomorph (slimSphereLine 0)
  obtain ⟨o⟩ := exists_slimSphereThree_orientation
  obtain ⟨A, hA⟩ := exists_slimSphereThree_curvature_bounds 5
  let μ := Integral.Measure.riemannianVolumeMeasure (𝓡 3) C slimSphereThreeMetric
  let volumePositive : MeasureTheory.Measure.IsOpenPosMeasure μ :=
    Integral.Measure.riemannianVolumeMeasure_isOpenPosMeasure slimSphereThreeMetric
  have hvol0 : 0 < μ (ball p 1) := isOpen_ball.measure_pos μ ⟨p, mem_ball_self zero_lt_one⟩
  obtain ⟨v, hv, hvμ⟩ := ENNReal.lt_iff_exists_nnreal_btwn.mp hvol0
  have hvreal : 0 < (v : ℝ) := by exact_mod_cast hv
  have hvol : ENNReal.ofReal (v : ℝ) ≤ μ (ball p 1) := by simpa using hvμ.le
  obtain ⟨β₁, hβ₁, hpacket⟩ := exists_slimPacket_threshold hΔ
    (by norm_num : 0 < (1 / 100 : ℝ)) le_rfl 5 (by decide) zero_lt_one hvreal (Function.const ℝ A)
  obtain ⟨β₂, hβ₂, hmodel⟩ := slimChart_model_embedding_threshold hΔ
    (by norm_num : 0 < (1 / 100 : ℝ)) le_rfl 5 (by decide) zero_lt_one hvreal (Function.const ℝ A)
  let β := min (min β₁ β₂) 1 / 2
  have hbmin : 0 < min (min β₁ β₂) 1 := lt_min (lt_min hβ₁ hβ₂) zero_lt_one
  have hβ : 0 < β := half_pos hbmin
  have hβ₁lt : β < β₁ :=
    (half_lt_self hbmin).trans_le ((min_le_left _ _).trans (min_le_left _ _))
  have hβ₂lt : β < β₂ :=
    (half_lt_self hbmin).trans_le ((min_le_left _ _).trans (min_le_right _ _))
  have hβone : β < 1 := (half_lt_self hbmin).trans_le (min_le_right _ _)
  let α : KleinerLottApprox p (WithLp.toLp 2 ((0 : ℝ), y)) β :=
    { error_pos := hβ
      error_lt_one := hβone
      toFun := e
      basepoint := he
      distortion := fun a ha b hb => by
        rw [e.dist_eq, sub_self, abs_zero]
        exact hβ.le
      coverage := fun a ha => by
        have hr : e.symm a ∈ ball p β⁻¹ := by
          rw [mem_ball, ← e.dist_eq, e.apply_symm_apply, he]
          linarith
        have hm : a ∈ e '' ball p β⁻¹ :=
          ⟨e.symm a, hr, e.apply_symm_apply a⟩
        exact (Metric.infDist_le_dist_of_mem hm).trans (by simpa using hβ.le) }
  have hcurv : ∀ R, 0 < R → R < β⁻¹ → ∀ k ≤ 5, ∀ x ∈ ball p R,
      CheegerGromovCompactness.curvDerivNorm k slimSphereThreeMetric x ≤ A :=
    fun R hR hRβ k hk x hx => hA k hk x
  have hsec : ∀ x ∈ ball p β⁻¹, SectionalBoundedBelowAt slimSphereThreeMetric x (-β ^ 2) := by
    intro x hx v w
    exact (mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr (sq_nonneg β))
      (sectionalCurvatureDenominator_nonneg slimSphereThreeMetric x v w)).trans
        (by simpa only [zero_mul] using slimSphereThree_sectional_nonneg x v w)
  obtain ⟨⟨P⟩, hevery⟩ := hpacket β hβ hβ₁lt C slimSphereThreeMetric
    slimSphereThreeMetricNorm o p hvol hcurv hsec Y y α hdiam
  have hm := hmodel β hβ hβ₂lt C slimSphereThreeMetric slimSphereThreeMetricNorm
    o p hvol hcurv hsec Y y α hdiam P.toSlimChart
  exact ⟨Δ, β, hΔ, hβ, hβone, Y, mY, y, p, α, hdiam, P, hm⟩

end DifferentialGeometry.Geometry.Collapse
