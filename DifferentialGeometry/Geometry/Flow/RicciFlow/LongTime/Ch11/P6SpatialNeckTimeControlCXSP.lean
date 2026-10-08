import DifferentialGeometry.Geometry.Neck.SpatialNormalization
import DifferentialGeometry.Geometry.Metric.BilinearPerturbation
import DifferentialGeometry.Geometry.Curvature.Bounds.MetricDerivatives
import DifferentialGeometry.Geometry.Curvature.CurvatureOperator.Derivatives.Pullback
import DifferentialGeometry.Geometry.Curvature.CurvatureOperator.Derivatives.Restriction
import DifferentialGeometry.Geometry.Curvature.CurvatureOperator.Derivatives.Scaling
import DifferentialGeometry.Geometry.Flow.RicciFlow.Compactness.Bounds.Curvature.TowerBridge
import DifferentialGeometry.Geometry.Flow.RicciFlow.Evolution.Curvature.IteratedCovariantDerivativeBridge
import DifferentialGeometry.Geometry.Flow.RicciFlow.Evolution.Scalar.IntrinsicDerivation
import DifferentialGeometry.Geometry.Flow.RicciFlow.Estimates.ScalarLaplacian
import DifferentialGeometry.Geometry.Flow.RicciFlow.Uniqueness.Forward.Data.UniformBounds

set_option autoImplicit false

/-!
# CX-SPINE: actual scalar time control from a spatial neck

The universal constants precede every manifold, metric, neck accuracy and flow query.
Only the time-zero spatial jets of a SpatialNeck are used. The fixed domain is
neckBuffer 1, and its fixed compact test set supplies reference curvature bounds.
The error bound eps < 1/11 gives metric equivalence with L=2 and spatial jets through
order four. No additional accuracy tolerance or backward time domain is required.

This produces a new auxiliary coefficient Cneck. It does not assert Cneck <= Gamma.Ctime.
The actual PDE statement requires a regular time and controls the left derivative there.
-/

noncomputable section

open Set Bundle Manifold
open DifferentialGeometry
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Connection
open DifferentialGeometry.Geometry.Metric
open DifferentialGeometry.Tensor0SBundle
open DifferentialGeometry.CheegerGromovCompactness
open DifferentialGeometry.PDE.RicciFlow
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
open scoped Manifold ContDiff Topology

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn

universe u

private local instance neckBufferSigma (O : TopologicalSpace.Opens NeckCylinder) :
    SigmaCompactSpace O :=
  isSigmaCompact_iff_sigmaCompactSpace.mp
    (DifferentialGeometry.Geometry.isSigmaCompact_of_isOpen NeckCylinderModel O.isOpen)

/-- Static bounds on |Rm|/R and |nabla^2 Rm|/R^2 from the actual neck comparison. -/
private theorem exists_spatial_neck_curvature_constants_CXSP :
    ∃ B0 B2 : ℝ, 0 < B0 ∧ 0 < B2 ∧
      ∀ (M : Type u) [TopologicalSpace M] [ChartedSpace ThreeSpace M]
        [IsManifold I3 ∞ M] [T2Space M]
        (g : SmoothRiemannianMetric I3 M) (eps : ℝ) (x : M),
        SpatialNeck g eps x →
        curvDerivNorm 0 g x ≤ B0 * metricScalarAt g x ∧
        curvDerivNorm 2 g x ≤ B2 * metricScalarAt g x ^ 2 := by
  let U := neckBuffer (1 : ℝ)
  let G := roundCylinderMetric.restrictOpen U
  let K := neckClosedTest (1 : ℝ)
  have hK : IsCompact K := isCompact_neckClosedTest 1
  obtain ⟨B0, hB0, hb0⟩ :=
    exists_pos_bound_intrinsic_curvature_derivative_on_compact_of_metric_jets
      G hK 0 2 (Real.sqrt 3 + 1) (by norm_num) (by positivity)
  obtain ⟨B2, hB2, hb2⟩ :=
    exists_pos_bound_intrinsic_curvature_derivative_on_compact_of_metric_jets
      G hK 2 2 (Real.sqrt 3 + 1) (by norm_num) (by positivity)
  refine ⟨B0, B2, hB0, hB2, ?_⟩
  intro M _ _ _ _ g eps x nk
  let Q := metricScalarAt g x
  have hQ : 0 < Q := nk.Q_pos
  have hinv : (4 : ℝ) ≤ eps⁻¹ := by
    rw [inv_eq_one_div]
    apply (le_div_iff₀ nk.eps_pos).mpr
    linarith [nk.eps_small]
  have hfit : (1 : ℝ)⁻¹ + 1 ≤ eps⁻¹ := by
    norm_num
    linarith
  have h4 : 4 ≤ ⌈eps⁻¹⌉₊ := by
    exact_mod_cast hinv.trans (Nat.le_ceil eps⁻¹)
  obtain ⟨V, Phi, hPhi, hjets⟩ := nk.exists_neckBuffer_pullback_bound hfit
  let P := Diffeomorph.pullbackMetricCross (g.restrictOpen V) Phi
  let gN := scaleMetric Q hQ P
  let z : U := ⟨(nk.center, 0), by
    change -(1 : ℝ)⁻¹ - 1 < 0 ∧ 0 < (1 : ℝ)⁻¹ + 1
    norm_num⟩
  have hzK : z ∈ K := by
    change (0 : ℝ) ∈ Icc (-(1 : ℝ)⁻¹) (1 : ℝ)⁻¹
    norm_num
  have herr (a : ℕ) (ha : a ≤ 4) : metricDerivNorm a gN G G z ≤ eps :=
    hjets a (ha.trans h4) z
  have hequiv (v : TangentSpace IC z) :
      (2 : ℝ)⁻¹ * G.inner z v v ≤ gN.inner z v v ∧
        gN.inner z v v ≤ 2 * G.inner z v v := by
    have hhalf : metricDerivNorm 0 gN G G z ≤ 1 / 2 :=
      (herr 0 (by norm_num)).trans (by linarith [nk.eps_small])
    obtain ⟨hl, hu⟩ := inner_bounds_of_metricDerivNorm_le G gN z hhalf v
    have hn := metric_inner_self_nonneg G z v
    have hcoef : (1 : ℝ) - 1 / 2 = (2 : ℝ)⁻¹ := by norm_num
    rw [hcoef] at hl
    exact ⟨hl, by nlinarith only [hu, hn]⟩
  have hcov (a : ℕ) (ha : a ≤ 4) :
      metricCovDerivNorm a gN G z ≤ Real.sqrt 3 + 1 := by
    have hself : metricCovDerivNorm a G G z ≤ Real.sqrt 3 := by
      cases a with
      | zero =>
        rw [metricCovDerivNorm_self_zero]
        simp [Module.finrank_prod]
      | succ a =>
        rw [covNorm_self_succ]
        exact Real.sqrt_nonneg _
    have herror : metricDerivNorm a gN G G z ≤ 1 :=
      (herr a ha).trans (by linarith [nk.eps_small])
    exact (covNorm_le_add a gN G G z).trans (add_le_add hself herror)
  have hnorm (j : ℕ) : curvDerivNorm j gN z =
      Real.sqrt (normSq0S gN z (4 + j) (iterCov gN 4 (metricRm04 gN) j z)) := by
    unfold curvDerivNorm curvDerivNormSq
    rw [curvCovDeriv_normSq_eq]
  have h0 : curvDerivNorm 0 gN z ≤ B0 := by
    rw [hnorm]
    exact hb0 gN z hzK hequiv (fun a ha => hcov a (by omega))
  have h2 : curvDerivNorm 2 gN z ≤ B2 := by
    rw [hnorm]
    exact hb2 gN z hzK hequiv (fun a ha => hcov a (by omega))
  have hzmap : (Phi z : M) = x := (hPhi z).trans nk.center_eq
  have htransport (j : ℕ) : curvDerivNorm j gN z =
      curvDerivNorm j g x / (Q * Real.sqrt Q ^ j) := by
    dsimp only [gN, P]
    rw [curvDerivNorm_scaleMetric,
      KappaSolutions.curvDerivNorm_pullbackMetricCross, curvDerivNorm_restrictOpen, hzmap]
  rw [htransport 0, pow_zero, mul_one] at h0
  rw [htransport 2, Real.sq_sqrt hQ.le] at h2
  refine ⟨(div_le_iff₀ hQ).mp h0, ?_⟩
  have hh := (div_le_iff₀ (mul_pos hQ hQ)).mp h2
  simpa only [pow_two, mul_assoc] using hh

/-- A universal auxiliary coefficient controls actual scalar evolution at spatial neck points.
No StrongNeck, mixed time jets, derivative supply or backward-window premise is used. -/
theorem exists_spatial_neck_scalar_time_constant_CXSP :
    ∃ Cneck : ℝ, 0 < Cneck ∧
      ∀ (M : Type u) [TopologicalSpace M] [ChartedSpace ThreeSpace M]
        [IsManifold I3 ∞ M] [T2Space M] [SigmaCompactSpace M]
        {D : RealTimeInterval} (S : SolutionOn (I := I3) (M := M) D),
        IsSolutionOn S → ∀ t : ℝ, t ∈ D.regular → ∀ (x : M) (eps : ℝ),
        SpatialNeck (S.base.metric t) eps x →
          |derivWithin (fun r => S.scalar r x) (Iic t) t| ≤ Cneck * S.scalar t x ^ 2 := by
  obtain ⟨B0, B2, hB0, hB2, hbound⟩ := exists_spatial_neck_curvature_constants_CXSP.{u}
  refine ⟨3 ^ 6 * B2 + 2 * 3 ^ 4 * B0 ^ 2, by positivity, ?_⟩
  intro M _ _ _ _ _ D S hS t ht x eps nk
  let _ : IsManifold I3 1 M := IsManifold.of_le (n := ∞) (by decide)
  let _ : IsManifold I3 2 M := IsManifold.of_le (n := ∞) (by decide)
  let _ : NeZero (Module.finrank ℝ ThreeSpace) := ⟨by simp [ThreeSpace]⟩
  let Q := S.scalar t x
  have hQ : 0 < Q := nk.Q_pos
  obtain ⟨hR0, hR2⟩ := hbound M (S.base.metric t) eps x nk
  change curvDerivNorm 0 (S.base.metric t) x ≤ B0 * Q at hR0
  change curvDerivNorm 2 (S.base.metric t) x ≤ B2 * Q ^ 2 at hR2
  have hzero : nablaKRm04NormSqIntrinsic S 0 t x ≤ (B0 * Q) ^ 2 := by
    rw [nablaKRm04NormSqIntrinsic_eq_curvDerivNorm_sq]
    exact (sq_le_sq₀ (Real.sqrt_nonneg _) (mul_nonneg hB0.le hQ.le)).mpr hR0
  have hevol := scalar_curvature_evolution S hS ⟨t, ht⟩ x
  have hd := (hevol.hasDerivAt (D.regular_mem_nhds ht)).hasDerivWithinAt.derivWithin
    (uniqueDiffWithinAt_Iic t)
  have hlap := CanonicalNeighborhood.abs_laplacian_scalar_le_second_curvature S t x
  rw [sqrt_nablaKRm04NormSqIntrinsic_eq_curvDerivNorm] at hlap
  have hric := ricciSq_le_rm04 (S.base.metric t) (S.base.metric t) x
  have hdim : Module.finrank ℝ ThreeSpace = 3 := by simp [ThreeSpace]
  rw [hdim] at hlap hric
  have hlap' : |laplacianAt (flowG S) t (S.scalar t) x| ≤ 3 ^ 6 * (B2 * Q ^ 2) :=
    hlap.trans (mul_le_mul_of_nonneg_left hR2 (by norm_num))
  have hric' : normSq0S (S.family.metric t) x 2 (S.ricci t x) ≤
      3 ^ 4 * (B0 * Q) ^ 2 :=
    hric.trans (mul_le_mul_of_nonneg_left hzero (by norm_num))
  have hric0 := normSq0S_nonneg (S.family.metric t) x 2 (S.ricci t x)
  rw [hd]
  calc
    _ ≤ |laplacianAt (flowG S) t (S.scalar t) x| +
        |2 * normSq0S (S.family.metric t) x 2 (S.ricci t x)| := abs_add_le _ _
    _ ≤ 3 ^ 6 * (B2 * Q ^ 2) + 2 * (3 ^ 4 * (B0 * Q) ^ 2) := by
      rw [abs_of_nonneg (mul_nonneg (by norm_num) hric0)]
      linarith
    _ = (3 ^ 6 * B2 + 2 * 3 ^ 4 * B0 ^ 2) * S.scalar t x ^ 2 := by
      dsimp only [Q]
      ring

end DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn

end
