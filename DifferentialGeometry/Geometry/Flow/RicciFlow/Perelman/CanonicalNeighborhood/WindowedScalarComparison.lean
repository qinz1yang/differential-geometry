import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.WindowedWitnessTransport
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.ScalarComparison
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.WindowedCanonicalDomain
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.GoodPointDerivatives
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.CanonicalStrictBounds

set_option autoImplicit false
noncomputable section
open Bundle Set
open scoped Manifold ContDiff Topology

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn

open DifferentialGeometry.CheegerGromovCompactness DifferentialGeometry.Tensor0SBundle
open DifferentialGeometry.Geometry.Curvature DifferentialGeometry.Geometry.Connection
open DifferentialGeometry.Geometry.Riemannian
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

universe u

attribute [local instance] PointedFlowData.topology PointedFlowData.charted
  PointedFlowData.smooth PointedFlowData.t2 PointedFlowData.sigmaCompact
  PointedFlowData.t2TangentBundle

variable {M : Type u} [TopologicalSpace M] [ChartedSpace ThreeSpace M]
  [IsManifold I3 ∞ M] [T2Space M] [SigmaCompactSpace M]
  {D : RealTimeInterval} {S : SolutionOn (I := I3) (M := M) D}

private local instance scalarComparisonSourceC1 : IsManifold I3 1 M :=
  IsManifold.of_le (n := ∞) (by decide)

private theorem abs_ricciTensor_le_of_rmNormSq_le
    {N : Type u} [TopologicalSpace N] [ChartedSpace ThreeSpace N]
    [IsManifold I3 ∞ N] [T2Space N]
    (g : SmoothRiemannianMetric I3 N) (z : N) {K : ℝ} (hK : 0 ≤ K)
    (hrm : normSq0S g z 4 (metricRm04At g z) ≤ K ^ 2)
    (v w : TangentSpace I3 z) :
    |ricciTensor g z v w| ≤ (3 * K) * Real.sqrt (g.inner z v v) * Real.sqrt (g.inner z w w) := by
  have hKr (a b c : TangentSpace I3 z) :
      Real.sqrt (g.inner z (riemannOp (cov := LeviCivita g) z a b c)
        (riemannOp (cov := LeviCivita g) z a b c)) ≤
        K * Real.sqrt (g.inner z a a) * Real.sqrt (g.inner z b b) * Real.sqrt (g.inner z c c) := by
    apply (Real.sqrt_le_iff).mpr
    refine ⟨by positivity, ?_⟩
    calc
      _ ≤ K ^ 2 * g.inner z a a * g.inner z b b * g.inner z c c :=
        riemannOp_normSq_le_of_rmNormSq_le g z hrm a b c
      _ = _ := by
        rw [mul_pow, mul_pow, mul_pow, Real.sq_sqrt (inner_self_nonneg g z a),
          Real.sq_sqrt (inner_self_nonneg g z b), Real.sq_sqrt (inner_self_nonneg g z c)]
  have hh := abs_ricciTensor_le_of_riemannOp_le g hKr v w
  simpa only [show Module.finrank ℝ ThreeSpace = 3 from by simp [ThreeSpace], Nat.cast_ofNat] using hh

theorem WindowedModelWitness.scalar_sub_le_of_model_curvature_bound
    {delta kappa K : ℝ} {x : M} {t : ℝ}
    (W : WindowedModelWitness delta kappa S x t) (hK : 0 ≤ K)
    {s : ℝ} (hs : s ∈ Icc (-modelDepth delta) 0) {y : W.model.M}
    (hy : y ∈ riemannianClosedBallOf (W.model.S.base.metric 0) W.model.basepoint (modelRadius delta))
    (hrm : W.model.rmNormSq s y ≤ K ^ 2) :
    |metricScalarAt (rescaledMetric S t (S.scalar t x) W.scalar_pos s) (W.embedding y) -
      W.model.S.scalar s y| ≤ scalarComparisonC 3 delta (3 * K) := by
  let F := W.embedding
  let h := fun r => W.model.S.base.metric r
  let ghat := rescaledMetric S t (S.scalar t x) W.scalar_pos
  have hysrc : y ∈ F.source := W.buffered_ball
    (riemannianClosedBallOf_mono (h 0) W.model.basepoint (by linarith) hy)
  let y' : sourceOpen F := ⟨y, hysrc⟩
  let : SigmaCompactSpace (sourceOpen F) := isSigmaCompact_iff_sigmaCompactSpace.mp
    (DifferentialGeometry.Geometry.isSigmaCompact_of_isOpen I3 (sourceOpen F).isOpen)
  have hcomplete : RiemannianMetricComplete (h 0) := by
    refine ⟨?_⟩
    exact MetricComplete.complete (W.model.atTime 0)
      (W.model_ancient.complete 0 (by change (0 : ℝ) ≤ 0; exact le_rfl))
  have hR : 0 < modelRadius delta := inv_pos.mpr (Real.sqrt_pos.mpr W.eps_pos)
  have horder : 2 ≤ modelOrder delta := by
    have hh := Nat.one_le_ceil_iff.mpr (inv_pos.mpr W.eps_pos)
    change 2 ≤ ⌈delta⁻¹⌉₊ + 1
    omega
  have hEq := W.comparison.metricUniformEquivalentOn W.eps_pos.le W.eps_lt_one hs
  have hJet1 := W.comparison.metricCovDerivOrderBoundOn (h 0) hcomplete W.model.basepoint hR
    hs (a := 1) le_rfl (by omega)
  have hJet2 := W.comparison.metricCovDerivOrderBoundOn (h 0) hcomplete W.model.basepoint hR
    hs (a := 2) (by omega) horder
  have hmodelnorm : normSq0S (witnessModelMetric F h s) y' 4
      (metricRm04At (witnessModelMetric F h s) y') ≤ K ^ 2 := by
    rw [witnessModelMetric, rmNormSq_restrictOpen (h s) (sourceOpen F) y']
    exact hrm
  have hric := abs_ricciTensor_le_of_rmNormSq_le (witnessModelMetric F h s) y' hK hmodelnorm
  have hmain := abs_metricScalarAt_sub_le_of_jetBounds (I := I3)
    (witnessModelMetric F h s) (witnessPullbackMetric F ghat s) hEq hJet1 hJet2
    (show y' ∈ Subtype.val ⁻¹' riemannianClosedBallOf (h 0) W.model.basepoint (modelRadius delta)
      from hy) hric
  rw [witnessPullbackMetric, openPullbackMetric_scalar, witnessModelMetric,
    metricScalarAt_restrictOpen] at hmain
  simpa only [show Module.finrank ℝ ThreeSpace = 3 from by simp [ThreeSpace], Nat.cast_ofNat,
    scalarComparisonC, witnessRiemannC, F, h, ghat, y', SolutionOn.scalar, SolutionFamily.scalar] using hmain

theorem WindowedModelWitness.scalar_bounds_on_canonical_domain
    {delta kappa eps C1 C2 : ℝ} {x : M} {t : ℝ}
    (W : WindowedModelWitness delta kappa S x t)
    (K : CanonicalWitness W.model.S eps C1 C2 W.model.basepoint 0)
    (hdelta : delta ≤ 1 / 4) (hbuffer : 2 * C1 ≤ modelRadius delta)
    (hsmall : 486 * C2 * (1 + 3 * C2) * delta ≤ 1)
    {y : W.model.M} (hy : y ∈ K.domain.carrier) :
    (2 * C2)⁻¹ * S.scalar t x ≤ S.scalar t (W.embedding y) ∧
      S.scalar t (W.embedding y) ≤ (2 * C2) * S.scalar t x := by
  have hC2 : 0 < C2 := zero_lt_one.trans_le K.one_le_comparison_constant
  have hbase : W.model.S.scalar 0 W.model.basepoint = 1 := W.model_scalar_base
  have hrm : W.model.rmNormSq 0 y ≤ C2 ^ 2 := by
    have hb := K.rm_bound y hy
    rw [hbase, mul_one] at hb
    change Real.sqrt (W.model.rmNormSq 0 y) ≤ C2 at hb
    have heq := Real.sq_sqrt (pointedFlow_rmNormSq_nonneg W.model 0 y)
    nlinarith [Real.sqrt_nonneg (W.model.rmNormSq 0 y)]
  have hcomp := W.scalar_sub_le_of_model_curvature_bound hC2.le
    (show (0 : ℝ) ∈ Icc (-modelDepth delta) 0 from
      ⟨neg_nonpos.mpr (inv_nonneg.mpr W.eps_pos.le), le_rfl⟩)
    (W.canonical_domain_subset_comparison_ball K hbuffer hy) hrm
  have hnorm : metricScalarAt (rescaledMetric S t (S.scalar t x) W.scalar_pos 0)
      (W.embedding y) = (S.scalar t x)⁻¹ * S.scalar t (W.embedding y) := by
    simp only [rescaledMetric, parabolicTime, zero_div, add_zero, metricScalarAt_scaleMetric,
      SolutionOn.scalar, SolutionFamily.scalar]
  rw [hnorm] at hcomp
  have hc := scalarComparisonC_le (n := 3) W.eps_pos.le hdelta
    (mul_nonneg (by norm_num : (0 : ℝ) ≤ 3) hC2.le)
  norm_num only [Nat.cast_ofNat, Nat.cast_pow, Nat.cast_mul, Nat.cast_add] at hc
  have hi : (2 * C2) * (2 * C2)⁻¹ = 1 := mul_inv_cancel₀ (by positivity)
  have he : scalarComparisonC 3 delta (3 * C2) ≤ (2 * C2)⁻¹ := by
    have hm := mul_le_mul_of_nonneg_left hc (by positivity : 0 ≤ 2 * C2)
    nlinarith
  have hmod := K.scalar_bounds y hy
  rw [hbase, mul_one, mul_one] at hmod
  have hinv : C2⁻¹ = 2 * (2 * C2)⁻¹ := by
    field_simp
  have hinvle : (2 * C2)⁻¹ ≤ C2 := by
    have hh := inv_anti₀ (by norm_num : (0 : ℝ) < 1)
      (by linarith [K.one_le_comparison_constant] : (1 : ℝ) ≤ 2 * C2)
    norm_num only [inv_one] at hh
    exact hh.trans K.one_le_comparison_constant
  obtain ⟨hneg, hpos⟩ := abs_le.mp (hcomp.trans he)
  have hlow : (2 * C2)⁻¹ ≤ (S.scalar t x)⁻¹ * S.scalar t (W.embedding y) := by
    rw [hinv] at hmod
    linarith
  have hupp : (S.scalar t x)⁻¹ * S.scalar t (W.embedding y) ≤ 2 * C2 := by linarith
  have hscale : S.scalar t x * ((S.scalar t x)⁻¹ * S.scalar t (W.embedding y)) =
      S.scalar t (W.embedding y) := by rw [← mul_assoc, mul_inv_cancel₀ W.scalar_pos.ne', one_mul]
  constructor
  · have hh := mul_le_mul_of_nonneg_left hlow W.scalar_pos.le
    rw [hscale] at hh
    simpa only [mul_comm] using hh
  · have hh := mul_le_mul_of_nonneg_left hupp W.scalar_pos.le
    rw [hscale] at hh
    simpa only [mul_comm] using hh

end DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn
