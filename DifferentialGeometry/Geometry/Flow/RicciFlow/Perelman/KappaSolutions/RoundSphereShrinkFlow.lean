import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.HarnackLimit
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.TerminalHarnack
import DifferentialGeometry.Geometry.Flow.RicciFlow.HamiltonHarnack.TraceCorollaries
import DifferentialGeometry.Geometry.Flow.RicciFlow.Soliton.Solution
import DifferentialGeometry.Geometry.Flow.RicciFlow.Soliton.NonnegativeCurvature
import DifferentialGeometry.Geometry.Metric.RicciSoliton.Models
import DifferentialGeometry.Geometry.Metric.Sphere.Round.Metric
import DifferentialGeometry.Geometry.Curvature.Metric.Sectional
import DifferentialGeometry.Geometry.Curvature.Metric.Scaling
import DifferentialGeometry.Geometry.Curvature.Algebraic.CurvatureOperatorCone
import DifferentialGeometry.Geometry.Curvature.Algebraic.CurvatureOperatorConeMetric
import DifferentialGeometry.Geometry.Metric.TensorInner.Tensor0S.Scaling
import DifferentialGeometry.Geometry.Metric.TensorInner.FiberMetric.Tensor0SMetric
import DifferentialGeometry.Geometry.Metric.Convergence.Naturality.PullbackCross
import DifferentialGeometry.Tensor.Metric.CompactBounds
import Mathlib.Analysis.InnerProductSpace.ExteriorPower

set_option autoImplicit false
noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions

open Bundle Filter Manifold Set
open DifferentialGeometry.Tensor0SBundle
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.CheegerGromovCompactness
open CanonicalNeighborhood
open scoped Manifold ContDiff _root_.Topology RealInnerProductSpace

private instance roundSphereShrinkFlowFinrank :
    Fact (Module.finrank ℝ (EuclideanSpace ℝ (Fin 4)) = 3 + 1) := ⟨by simp⟩

abbrev RoundSphereShrinkSpace := Metric.sphere (0 : EuclideanSpace ℝ (Fin 4)) 1

local instance roundSphereShrinkSpaceConnected : ConnectedSpace RoundSphereShrinkSpace := by
  refine Subtype.connectedSpace
    (isConnected_sphere (E := EuclideanSpace ℝ (Fin 4)) ?_ 0 zero_le_one)
  rw [← Module.finrank_eq_rank]
  simp

abbrev roundSphereShrinkFlowMetric : SmoothRiemannianMetric (𝓡 3) RoundSphereShrinkSpace :=
  Geometry.roundSphereShrinkerMetric (A := EuclideanSpace ℝ (Fin 4)) (n := 3) (by decide)

abbrev roundSphereShrinkFlowPotential : C^∞⟮𝓡 3, RoundSphereShrinkSpace; ℝ⟯ :=
  Geometry.roundSphereShrinkerPotential (A := EuclideanSpace ℝ (Fin 4)) (n := 3)

private abbrev roundSphereShrinkFlowComplete :
    RiemannianMetricComplete (I := 𝓡 3) roundSphereShrinkFlowMetric :=
  Geometry.roundSphereShrinkerMetric_complete (A := EuclideanSpace ℝ (Fin 4)) (n := 3) (by decide)

private abbrev roundSphereShrinkFlowSoliton :
    Geometry.gradientRicciSoliton (I := 𝓡 3) roundSphereShrinkFlowMetric
      roundSphereShrinkFlowPotential 1 :=
  Geometry.gradientRicciSoliton_roundSphere (A := EuclideanSpace ℝ (Fin 4)) (n := 3) (by decide)

theorem roundSphereShrinkFlow_domain :
    ancientTimeInterval.carrier ⊆ Soliton.canonicalTimeDomain 1 := by
  intro t ht
  rw [Soliton.mem_canonicalTimeDomain_iff]
  simp only [one_mul]
  simp only [ancientTimeInterval_carrier, Set.mem_Iic] at ht
  linarith

abbrev roundSphereShrinkFlow :
    PointedFlowData.{0, 0, 0} (I := 𝓡 3) ancientTimeInterval where
  M := RoundSphereShrinkSpace
  basepoint := ⟨EuclideanSpace.single 0 1, by simp⟩
  S := Soliton.canonicalSolutionOn roundSphereShrinkFlowMetric roundSphereShrinkFlowPotential 1
    roundSphereShrinkFlowComplete roundSphereShrinkFlowSoliton ancientTimeInterval
  isSolution := Soliton.canonicalSolutionOn_isSolutionOn roundSphereShrinkFlowMetric
    roundSphereShrinkFlowPotential 1 roundSphereShrinkFlowComplete roundSphereShrinkFlowSoliton
    ancientTimeInterval roundSphereShrinkFlow_domain

theorem roundSphereShrinkFlow_metric_zero :
    roundSphereShrinkFlow.S.base.metric 0 = roundSphereShrinkFlowMetric :=
  Soliton.canonicalSolutionOn_metric_zero _ _ _ _ _ _

theorem roundSphereShrinkFlow_scalar_zero (x : RoundSphereShrinkSpace) :
    roundSphereShrinkFlow.S.scalar 0 x = (3 / 2 : ℝ) := by
  have h : roundSphereShrinkFlow.S.scalar 0 x =
      metricScalarAt (I := 𝓡 3) (roundSphereShrinkFlow.S.base.metric 0) x := rfl
  rw [h, roundSphereShrinkFlow_metric_zero]
  exact Geometry.roundSphereShrinkerMetric_scalarCurvature
    (A := EuclideanSpace ℝ (Fin 4)) (n := 3) (by decide) x

theorem roundSphereShrinkFlow_complete (t : ℝ) (ht : t ∈ ancientTimeInterval.carrier) :
    MetricComplete (I := 𝓡 3) (roundSphereShrinkFlow.atTime (I := 𝓡 3) t) := by
  have h : RiemannianMetricComplete (I := 𝓡 3) (roundSphereShrinkFlow.S.base.metric t) :=
    Soliton.canonicalSolutionOn_complete roundSphereShrinkFlowMetric roundSphereShrinkFlowPotential
      1 roundSphereShrinkFlowComplete roundSphereShrinkFlowSoliton ancientTimeInterval
      roundSphereShrinkFlow_domain ht
  exact h.complete

theorem roundSphereShrinkFlow_notFlat : PointedFlowNotFlat (I := 𝓡 3) roundSphereShrinkFlow := by
  refine pointedFlowNotFlat_of_scalar_ne_zero roundSphereShrinkFlow (t := 0) ?_
    roundSphereShrinkFlow.basepoint ?_
  · simpa only [ancientTimeInterval_carrier, Set.mem_Iic] using (le_rfl : (0 : ℝ) ≤ 0)
  · change metricScalarAt (I := 𝓡 3) (roundSphereShrinkFlow.S.base.metric 0)
        roundSphereShrinkFlow.basepoint ≠ 0
    rw [roundSphereShrinkFlow_metric_zero,
      Geometry.roundSphereShrinkerMetric_scalarCurvature (A := EuclideanSpace ℝ (Fin 4))
        (n := 3) (by decide) roundSphereShrinkFlow.basepoint]
    norm_num

theorem roundSphereShrinkFlow_rmNormSq_ne_zero :
    roundSphereShrinkFlow.rmNormSq (I := 𝓡 3) 0 roundSphereShrinkFlow.basepoint ≠ 0 := by
  intro hzero
  have hscalar : roundSphereShrinkFlow.S.scalar 0 roundSphereShrinkFlow.basepoint = 0 := by
    change metricScalarAt (I := 𝓡 3) (roundSphereShrinkFlow.S.base.metric 0)
      roundSphereShrinkFlow.basepoint = 0
    have hbound := DifferentialGeometry.Geometry.Curvature.scalar_abs_le_rm (I := 𝓡 3)
      (M := RoundSphereShrinkSpace) (roundSphereShrinkFlow.S.base.metric 0)
      roundSphereShrinkFlow.basepoint
    have hrw : Real.sqrt (Tensor0SBundle.normSq0S (I := 𝓡 3)
        (roundSphereShrinkFlow.S.base.metric 0) roundSphereShrinkFlow.basepoint 4
        (metricRm04At (I := 𝓡 3) (M := RoundSphereShrinkSpace)
          (roundSphereShrinkFlow.S.base.metric 0) roundSphereShrinkFlow.basepoint)) = 0 := by
      have hz : Tensor0SBundle.normSq0S (I := 𝓡 3)
          (roundSphereShrinkFlow.S.base.metric 0) roundSphereShrinkFlow.basepoint 4
          (metricRm04At (I := 𝓡 3) (M := RoundSphereShrinkSpace)
            (roundSphereShrinkFlow.S.base.metric 0) roundSphereShrinkFlow.basepoint) = 0 := by
        simpa only [PointedFlowData.rmNormSq, SolutionOn.family_metric, SolutionFamily.rm04,
          metricRm04_apply] using hzero
      rw [hz, Real.sqrt_zero]
    rw [hrw, mul_zero] at hbound
    exact abs_eq_zero.mp (le_antisymm hbound (abs_nonneg _))
  rw [roundSphereShrinkFlow_scalar_zero] at hscalar
  norm_num at hscalar

private theorem exterior_quad_nonneg {F : Type*} [NormedAddCommGroup F]
    [InnerProductSpace ℝ F] [FiniteDimensional ℝ F] {n : ℕ} (V W : Fin n → F)
    (c : Fin n → ℝ) :
    0 ≤ ∑ i, ∑ j, c i * c j *
      (⟪W i, W j⟫ * ⟪V i, V j⟫ - ⟪V i, W j⟫ * ⟪W i, V j⟫) := by
  have key :
      ∑ i, ∑ j, c i * c j *
          (⟪W i, W j⟫ * ⟪V i, V j⟫ - ⟪V i, W j⟫ * ⟪W i, V j⟫) =
        ⟪∑ i, c i • exteriorPower.ιMulti ℝ 2 ![V i, W i],
          ∑ j, c j • exteriorPower.ιMulti ℝ 2 ![V j, W j]⟫ := by
    rw [sum_inner]
    apply Finset.sum_congr rfl
    intro i _
    rw [inner_sum]
    apply Finset.sum_congr rfl
    intro j _
    rw [real_inner_smul_left, real_inner_smul_right,
      exteriorPower.inner_ιMulti_ιMulti, Matrix.det_fin_two]
    simp only [Matrix.of_apply, Matrix.cons_val_zero, Matrix.cons_val_one]
    ring
  rw [key]
  exact real_inner_self_nonneg

private abbrev roundSphereShrinkUnitMetric : SmoothRiemannianMetric (𝓡 3) RoundSphereShrinkSpace :=
  Geometry.roundMetric (E := EuclideanSpace ℝ (Fin 4)) (n := 3)

private theorem roundSphereShrinkUnitMetric_quad_nonneg (y : RoundSphereShrinkSpace) (n : ℕ)
    (c : Fin n → ℝ) (v w : Fin n → TangentSpace (𝓡 3) y) :
    0 ≤ ∑ i, ∑ j, c i * c j *
      metricRm04StandardAt (I := 𝓡 3) roundSphereShrinkUnitMetric y (v i) (w i) (w j) (v j) := by
  have hsec : ∀ X Y : TangentSpace (𝓡 3) y,
      metricRm04StandardAt (I := 𝓡 3) roundSphereShrinkUnitMetric y X Y Y X =
        (1 : ℝ) * (roundSphereShrinkUnitMetric.inner y X X *
          roundSphereShrinkUnitMetric.inner y Y Y -
          roundSphereShrinkUnitMetric.inner y X Y *
          roundSphereShrinkUnitMetric.inner y X Y) := by
    intro X Y
    rw [one_mul]
    exact Geometry.roundMetric_sec_value (E := EuclideanSpace ℝ (Fin 4)) (n := 3) y X Y
  have hfull := metricRm_of_sec (I := 𝓡 3) roundSphereShrinkUnitMetric y 1 hsec
  have hterm (i j : Fin n) :
      metricRm04StandardAt (I := 𝓡 3) roundSphereShrinkUnitMetric y
          (v i) (w i) (w j) (v j) =
        ⟪Geometry.dIncl (n := 3) y (w i), Geometry.dIncl (n := 3) y (w j)⟫ *
          ⟪Geometry.dIncl (n := 3) y (v i), Geometry.dIncl (n := 3) y (v j)⟫ -
          ⟪Geometry.dIncl (n := 3) y (v i), Geometry.dIncl (n := 3) y (w j)⟫ *
            ⟪Geometry.dIncl (n := 3) y (w i), Geometry.dIncl (n := 3) y (v j)⟫ := by
    rw [hfull (v i) (w i) (w j) (v j)]
    simp only [one_mul, Geometry.roundMetric_inner]
  simp_rw [hterm]
  exact exterior_quad_nonneg (fun i => Geometry.dIncl (n := 3) y (v i))
    (fun i => Geometry.dIncl (n := 3) y (w i)) c

theorem roundSphereShrinkMetric_curvatureOperatorNonnegative (y : RoundSphereShrinkSpace) :
    metricAlgebraicCurvatureTensorAt (I := 𝓡 3) roundSphereShrinkFlowMetric y ∈
      algebraicCurvatureOperatorNonnegativeCone (I := 𝓡 3) (M := RoundSphereShrinkSpace) := by
  rw [metricAlgebraicCurvatureTensorAt_mem_curvatureOperatorNonnegativeCone_iff]
  intro n c v w
  have hg : roundSphereShrinkFlowMetric = scaleMetric (I := 𝓡 3)
      (Geometry.roundSphereShrinkerRadius 3 ^ 2)
      (sq_pos_of_pos (Geometry.roundSphereShrinkerRadius_pos (by decide : 2 ≤ 3)))
      roundSphereShrinkUnitMetric := rfl
  simp_rw [hg, metricRmStandard_scale]
  rw [show (∑ i, ∑ j, c i * c j *
        (Geometry.roundSphereShrinkerRadius 3 ^ 2 *
          metricRm04StandardAt (I := 𝓡 3) roundSphereShrinkUnitMetric y
            (v i) (w i) (w j) (v j))) =
      Geometry.roundSphereShrinkerRadius 3 ^ 2 * ∑ i, ∑ j, c i * c j *
        metricRm04StandardAt (I := 𝓡 3) roundSphereShrinkUnitMetric y
          (v i) (w i) (w j) (v j) by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j _
    ring]
  exact mul_nonneg
    (le_of_lt (sq_pos_of_pos (Geometry.roundSphereShrinkerRadius_pos (by decide : 2 ≤ 3))))
    (roundSphereShrinkUnitMetric_quad_nonneg y n c v w)

theorem roundSphereShrinkFlow_nonnegativeCurvatureOperator (t : ℝ)
    (ht : t ∈ ancientTimeInterval.carrier) :
    PointedFlowNonnegativeCurvatureOperator (I := 𝓡 3) roundSphereShrinkFlow t := by
  intro x n c v w
  have htD : t ∈ Soliton.canonicalTimeDomain 1 := roundSphereShrinkFlow_domain ht
  have hconeT := Soliton.canonicalMetric_curvatureOperator_nonnegative roundSphereShrinkFlowMetric
    roundSphereShrinkFlowPotential 1 roundSphereShrinkFlowComplete roundSphereShrinkFlowSoliton
    roundSphereShrinkMetric_curvatureOperatorNonnegative htD x
  have hquad := (mem_algebraicCurvatureOperatorNonnegativeCone.mp hconeT) n c v w
  have hmetric : roundSphereShrinkFlow.S.base.metric t =
      Soliton.canonicalMetric roundSphereShrinkFlowMetric roundSphereShrinkFlowPotential 1
        roundSphereShrinkFlowComplete roundSphereShrinkFlowSoliton htD := by
    rw [Soliton.canonicalSolutionOn_metric]
    exact Soliton.canonicalMetricFamily_eq roundSphereShrinkFlowMetric
      roundSphereShrinkFlowPotential 1 roundSphereShrinkFlowComplete
      roundSphereShrinkFlowSoliton htD
  simp only [SolutionFamily.rm04]
  rw [hmetric]
  simpa only [algebraicCurvatureOperatorQuadraticEval, tensor04StandardAt_apply,
    metricAlgebraicCurvatureTensorAt_coe, metricRm04_apply] using hquad

private theorem normSq0S_metricRm04At_scaleMetric (c : ℝ) (hc : 0 < c)
    (x : RoundSphereShrinkSpace) :
    Tensor0SBundle.normSq0S (I := 𝓡 3)
        (scaleMetric (I := 𝓡 3) c hc roundSphereShrinkFlowMetric) x 4
        (metricRm04At (I := 𝓡 3) (M := RoundSphereShrinkSpace)
          (scaleMetric (I := 𝓡 3) c hc roundSphereShrinkFlowMetric) x) =
      (c⁻¹) ^ 2 * Tensor0SBundle.normSq0S (I := 𝓡 3) roundSphereShrinkFlowMetric x 4
        (metricRm04At (I := 𝓡 3) (M := RoundSphereShrinkSpace) roundSphereShrinkFlowMetric x) := by
  simp only [← metricRm04_apply]
  rw [metricRm_scale, normSq0S_smul, normSq0S_scale]
  field_simp

theorem roundSphereShrinkFlow_curvature_bound :
    ∀ a b : ℝ, Set.Icc a b ⊆ ancientTimeInterval.carrier →
      ∃ C : ℝ, ∀ t ∈ Set.Icc a b, ∀ x : RoundSphereShrinkSpace,
        Tensor0SBundle.normSq0S (I := 𝓡 3) (roundSphereShrinkFlow.S.base.metric t) x 4
          (roundSphereShrinkFlow.S.base.rm04 t x) ≤ C := by
  intro a b hab
  by_cases hle : a ≤ b
  · have hble : b ≤ 0 := by
      have h := hab (Set.mem_Icc.mpr ⟨hle, le_rfl⟩)
      simpa only [ancientTimeInterval_carrier, Set.mem_Iic] using h
    obtain ⟨B, hBpos, hB⟩ := DifferentialGeometry.Geometry.Tensor.exists_pos_bound_norm_on_compact
      (I := 𝓡 3) (M := RoundSphereShrinkSpace) roundSphereShrinkFlowMetric
      (metricRm04 (I := 𝓡 3) (M := RoundSphereShrinkSpace) roundSphereShrinkFlowMetric)
      (isCompact_univ)
    refine ⟨(1 - 1 * b)⁻¹ ^ 2 * B ^ 2, fun t ht x => ?_⟩
    have htc : t ∈ Soliton.canonicalTimeDomain 1 :=
      roundSphereShrinkFlow_domain (hab ht)
    have htpos : (0 : ℝ) < 1 - 1 * t := Soliton.mem_canonicalTimeDomain_iff.mp htc
    have hb0 : (0 : ℝ) < 1 - 1 * b := by linarith [hble]
    set Phi := Soliton.canonicalFlowDiffeomorph (I := 𝓡 3) roundSphereShrinkFlowMetric
      roundSphereShrinkFlowPotential 1 roundSphereShrinkFlowComplete roundSphereShrinkFlowSoliton
      (Soliton.canonicalFlowParameter 1 t) with hPhi
    have hmetric : roundSphereShrinkFlow.S.base.metric t =
        Diffeomorph.pullbackMetric (I := 𝓡 3)
          (scaleMetric (I := 𝓡 3) (1 - 1 * t) htpos roundSphereShrinkFlowMetric) Phi := by
      rw [Soliton.canonicalSolutionOn_metric,
        Soliton.canonicalMetricFamily_eq roundSphereShrinkFlowMetric roundSphereShrinkFlowPotential 1
          roundSphereShrinkFlowComplete roundSphereShrinkFlowSoliton htc]
      simp only [Soliton.canonicalMetric]
      rw [← hPhi]
    have hboundPhi : Tensor0SBundle.normSq0S (I := 𝓡 3) roundSphereShrinkFlowMetric (Phi x) 4
        (metricRm04At (I := 𝓡 3) (M := RoundSphereShrinkSpace) roundSphereShrinkFlowMetric
          (Phi x)) ≤ B ^ 2 := by
      have hs : Real.sqrt (Tensor0SBundle.normSq0S (I := 𝓡 3) roundSphereShrinkFlowMetric
          (Phi x) 4 (metricRm04At (I := 𝓡 3) (M := RoundSphereShrinkSpace)
            roundSphereShrinkFlowMetric (Phi x))) ≤ B := by
        simpa only [metricRm04_apply] using hB (Phi x) (Set.mem_univ (Phi x))
      have hnn : 0 ≤ Tensor0SBundle.normSq0S (I := 𝓡 3) roundSphereShrinkFlowMetric (Phi x) 4
          (metricRm04At (I := 𝓡 3) (M := RoundSphereShrinkSpace) roundSphereShrinkFlowMetric
            (Phi x)) :=
        normSq0S_nonneg (I := 𝓡 3) roundSphereShrinkFlowMetric (Phi x) 4 _
      have hz : (Real.sqrt (Tensor0SBundle.normSq0S (I := 𝓡 3) roundSphereShrinkFlowMetric
          (Phi x) 4 (metricRm04At (I := 𝓡 3) (M := RoundSphereShrinkSpace)
            roundSphereShrinkFlowMetric (Phi x)))) ^ 2 ≤ B ^ 2 := by
        nlinarith [Real.sqrt_nonneg (Tensor0SBundle.normSq0S (I := 𝓡 3)
          roundSphereShrinkFlowMetric (Phi x) 4 (metricRm04At (I := 𝓡 3)
            (M := RoundSphereShrinkSpace) roundSphereShrinkFlowMetric (Phi x))), hs, hBpos.le]
      rwa [Real.sq_sqrt hnn] at hz
    have hcoef : (1 - 1 * t)⁻¹ ^ 2 ≤ (1 - 1 * b)⁻¹ ^ 2 := by
      have h1 : (1 - 1 * t)⁻¹ ≤ (1 - 1 * b)⁻¹ := by
        rw [inv_eq_one_div, inv_eq_one_div]
        exact one_div_le_one_div_of_le hb0 (by linarith [ht.2])
      have h2 := mul_self_le_mul_self (inv_nonneg.mpr htpos.le) h1
      simpa only [pow_two] using h2
    simp only [SolutionFamily.rm04]
    rw [hmetric, ← Diffeomorph.pullbackMetricCross_eq_pullbackMetric, metricRm04_apply,
      riemannNormSq_cross, normSq0S_metricRm04At_scaleMetric]
    calc (1 - 1 * t)⁻¹ ^ 2 * Tensor0SBundle.normSq0S (I := 𝓡 3) roundSphereShrinkFlowMetric
          (Phi x) 4
          (metricRm04At (I := 𝓡 3) (M := RoundSphereShrinkSpace) roundSphereShrinkFlowMetric
            (Phi x))
        ≤ (1 - 1 * t)⁻¹ ^ 2 * B ^ 2 := mul_le_mul_of_nonneg_left hboundPhi (sq_nonneg _)
      _ ≤ (1 - 1 * b)⁻¹ ^ 2 * B ^ 2 := mul_le_mul_of_nonneg_right hcoef (sq_nonneg _)
  · refine ⟨0, fun t ht x => ?_⟩
    exact absurd (le_trans ht.1 ht.2) hle

theorem roundSphereShrinkFlow_traceHarnack (t : ℝ) (ht : t ∈ ancientTimeInterval.carrier)
    (x : RoundSphereShrinkSpace) (V : TangentSpace (𝓡 3) x) :
    0 ≤ derivWithin (fun s : ℝ => roundSphereShrinkFlow.S.scalar s x)
          ancientTimeInterval.carrier t +
      2 * (roundSphereShrinkFlow.S.base.metric t).inner x
        (gradientAt (I := 𝓡 3) (flowG (I := 𝓡 3) roundSphereShrinkFlow.S) t
          (roundSphereShrinkFlow.S.scalar t) x) V +
      2 * metricRicci (I := 𝓡 3) (M := RoundSphereShrinkSpace)
        (roundSphereShrinkFlow.S.base.metric t) x (vec2 V V) := by
  have hcomplete : ∀ s ∈ ancientTimeInterval.carrier,
      RiemannianMetricComplete (I := 𝓡 3) (roundSphereShrinkFlow.S.base.metric s) :=
    fun s hs => Soliton.canonicalSolutionOn_complete roundSphereShrinkFlowMetric
      roundSphereShrinkFlowPotential 1 roundSphereShrinkFlowComplete roundSphereShrinkFlowSoliton
      ancientTimeInterval roundSphereShrinkFlow_domain hs
  have hR : ∀ s ∈ ancientTimeInterval.carrier, ∀ y : RoundSphereShrinkSpace,
      metricAlgebraicCurvatureTensorAt (I := 𝓡 3) (roundSphereShrinkFlow.S.base.metric s) y ∈
        algebraicCurvatureOperatorNonnegativeCone (I := 𝓡 3)
          (M := RoundSphereShrinkSpace) := by
    intro s hs y
    have hsC : s ∈ Soliton.canonicalTimeDomain 1 := roundSphereShrinkFlow_domain hs
    have hmetric : roundSphereShrinkFlow.S.base.metric s =
        Soliton.canonicalMetric roundSphereShrinkFlowMetric roundSphereShrinkFlowPotential 1
          roundSphereShrinkFlowComplete roundSphereShrinkFlowSoliton hsC := by
      rw [Soliton.canonicalSolutionOn_metric,
        Soliton.canonicalMetricFamily_eq roundSphereShrinkFlowMetric roundSphereShrinkFlowPotential
          1 roundSphereShrinkFlowComplete roundSphereShrinkFlowSoliton hsC]
    rw [hmetric]
    exact Soliton.canonicalMetric_curvatureOperator_nonnegative roundSphereShrinkFlowMetric
      roundSphereShrinkFlowPotential 1 roundSphereShrinkFlowComplete roundSphereShrinkFlowSoliton
      roundSphereShrinkMetric_curvatureOperatorNonnegative hsC y
  by_cases ht0 : t = 0
  · subst t
    exact hamilton_ancient_trace_harnack_at_terminal roundSphereShrinkFlow.S
      roundSphereShrinkFlow.isSolution ancientTimeInterval_carrier ancientTimeInterval_regular
      hcomplete (fun a b hab => roundSphereShrinkFlow_curvature_bound a b hab)
      (fun s hs y => hR s hs y) x V
  · have htneg : t < 0 := lt_of_le_of_ne
      (by simpa only [ancientTimeInterval_carrier, Set.mem_Iic] using ht) ht0
    have htreg : t ∈ ancientTimeInterval.regular := by
      simpa only [ancientTimeInterval_regular, Set.mem_Iio] using htneg
    rw [derivWithin_of_mem_nhds (ancientTimeInterval.regular_mem_nhds htreg)]
    apply hamilton_ancient_trace_harnack roundSphereShrinkFlow.S roundSphereShrinkFlow.isSolution
      (fun s hs => hcomplete s (ancientTimeInterval.regular_subset hs))
      (fun a b hab => roundSphereShrinkFlow_curvature_bound a b
        (hab.trans ancientTimeInterval.regular_subset))
      (fun s hs y => hR s (ancientTimeInterval.regular_subset hs) y) _ x V
    intro s hs
    simpa only [ancientTimeInterval_regular, Set.mem_Iio] using hs.trans_lt htneg

theorem roundSphereShrinkFlow_kLim_iff_noncollapsed {kappa : ℝ} (hkappa : 0 < kappa) :
    KLim (I := 𝓡 3) kappa roundSphereShrinkFlow ↔
      PointedFlowNoncollapsedAllScales (I := 𝓡 3) roundSphereShrinkFlow kappa := by
  constructor
  · intro hK
    exact hK.noncollapsed
  · intro hnc
    exact
      { dimension_ge_two := by norm_num [finrank_euclideanSpace_fin, Fintype.card_fin]
        kappa_pos := hkappa
        carrier_eq := rfl
        regular_eq := rfl
        connected := roundSphereShrinkSpaceConnected
        complete := roundSphereShrinkFlow_complete
        nonnegativeCurvatureOperator := roundSphereShrinkFlow_nonnegativeCurvatureOperator
        noncollapsed := hnc
        notFlat := roundSphereShrinkFlow_notFlat
        traceHarnack := roundSphereShrinkFlow_traceHarnack }

end DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions
