import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.ComparisonCurvatureBounds
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.CanonicalStrictBounds
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.CanonicalInnerRadius
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.WitnessBallCapture
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.StandardHarnackLimit
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.KLimCurvatureBounds
import DifferentialGeometry.Geometry.Curvature.Bounds.ScalarNorm

set_option autoImplicit false
noncomputable section
open Set Filter
open scoped Manifold ContDiff Topology

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn

open DifferentialGeometry.CheegerGromovCompactness DifferentialGeometry.Tensor0SBundle
open DifferentialGeometry.Geometry.Curvature DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

universe u

attribute [local instance] PointedFlowData.topology PointedFlowData.charted
  PointedFlowData.smooth PointedFlowData.t2 PointedFlowData.sigmaCompact
  PointedRiemannianManifold.topology PointedRiemannianManifold.charted
  PointedRiemannianManifold.smooth PointedRiemannianManifold.t2
  PointedRiemannianManifold.sigmaCompact

theorem CanonicalWitness.eventually_ancient_curvature_bounds_of_comparisons
    (P : ℕ → PointedFlowData.{u, 0, 0} I3 ancientTimeInterval)
    {kappa : ℕ → ℝ} (hP : ∀ i, IsAncientKappaSolution (kappa i) (P i))
    (L : PointedFlowData.{u, 0, 0} I3 ancientTimeInterval)
    (hcomplete : MetricComplete (L.atTime 0)) {phi : ℕ → ℕ}
    (F : PointedRiemannianConvergenceMaps ⟨fun i => (P i).atTime 0⟩ (L.atTime 0) phi)
    (hcmp : ∀ A : Set L.M, IsCompact A → ∀ᶠ i in atTop,
      Nonempty (MetricComparisonOn L.S.base.metric (P (phi i)).S.base.metric
        (F.map i) A {0} 2 (1 / 4)))
    {eps C1 C2 : ℝ} (K : CanonicalWitness L.S eps C1 C2 L.basepoint 0)
    (hscalar : L.S.scalar 0 L.basepoint = 1) :
    ∀ᶠ i in atTop, ∀ t : ℝ, t ≤ 0 → ∀ y ∈
      riemannianClosedBallOf ((P (phi i)).S.base.metric 0) (P (phi i)).basepoint 2,
      (P (phi i)).rmNormSq t y ≤ (18 * sourceCurvatureBound 3 C2) ^ 2 := by
  let _ : TopologicalSpace L.M := L.topology
  let _ : ChartedSpace ThreeSpace L.M := L.charted
  let _ : IsManifold I3 ∞ L.M := L.smooth
  let _ : T2Space L.M := L.t2
  let _ : SigmaCompactSpace L.M := L.sigmaCompact
  let _ : IsManifold I3 1 L.M := IsManifold.of_le (n := ∞) (by decide)
  have hC2 : 0 < C2 := zero_lt_one.trans_le K.one_le_comparison_constant
  have hc : RiemannianMetricComplete (L.S.base.metric 0) :=
    ⟨MetricComplete.complete (L.atTime 0) hcomplete⟩
  let B := riemannianClosedBallOf (L.S.base.metric 0) L.basepoint 9
  have hBc : IsCompact B := hc.closedEBall_isCompact L.basepoint 9
  have hBK : B ⊆ K.domain.carrier := K.closedBall_nine_subset_of_scalar_one hscalar
  obtain ⟨i0, hi0⟩ := F.source_subset hBc
  have hsrc : ∀ᶠ i in atTop, B ⊆ (F.partialDiffeomorph i).source :=
    eventually_atTop.2 ⟨i0, hi0⟩
  filter_upwards [hsrc, hcmp B hBc] with i hsource hcomparison
  obtain ⟨cmp⟩ := hcomparison
  let _ : TopologicalSpace (P (phi i)).M := (P (phi i)).topology
  let _ : ChartedSpace ThreeSpace (P (phi i)).M := (P (phi i)).charted
  let _ : IsManifold I3 ∞ (P (phi i)).M := (P (phi i)).smooth
  let _ : T2Space (P (phi i)).M := (P (phi i)).t2
  let _ : SigmaCompactSpace (P (phi i)).M := (P (phi i)).sigmaCompact
  let _ : IsManifold I3 1 (P (phi i)).M := IsManifold.of_le (n := ∞) (by decide)
  have hlow : ∀ z ∈ B, ∀ v : TangentSpace I3 z,
      (L.S.base.metric 0).inner z v v ≤ (2 : ℝ) ^ 2 *
        ((P (phi i)).S.base.metric 0).inner (F.map i z)
          (mfderiv I3 I3 (F.map i) z v) (mfderiv I3 I3 (F.map i) z v) := by
    intro z hz v
    have hh := (cmp.equivalence 0 (by simp) z hz v).1
    rw [cmp.pullback_eq 0 z hz (fun _ => v)] at hh
    change (1 - (1 / 4 : ℝ)) * (L.S.base.metric 0).inner z v v ≤
      ((P (phi i)).S.base.metric 0).inner (F.map i z)
        (mfderiv I3 I3 (F.map i) z v) (mfderiv I3 I3 (F.map i) z v) at hh
    have hnn := inner_self_nonneg (I := I3) (L.S.base.metric 0) z v
    norm_num only at hh ⊢
    linarith
  have hcapture := closedBall_subset_image_of_metric_lower
    (L.S.base.metric 0) ((P (phi i)).S.base.metric 0) (F.partialDiffeomorph i)
    L.basepoint (R := 9) (L := 2) (r := 2) (by norm_num) (by norm_num)
    (by norm_num) hBc hsource hlow
  have hbase : F.partialDiffeomorph i L.basepoint = (P (phi i)).basepoint := F.basepoint_map i
  rw [hbase] at hcapture
  intro t ht y hy
  obtain ⟨z, hz, rfl⟩ := hcapture hy
  have hrm : normSq0S (L.S.base.metric 0) z 4 (metricRm04At (L.S.base.metric 0) z) ≤ C2 ^ 2 := by
    have hh := K.rm_bound z (hBK hz)
    rw [hscalar, mul_one] at hh
    exact le_sq_of_sqrt_le (normSq0S_nonneg _ _ _ _) hh
  have hnorm := MetricComparisonOn.rmNormSq_le_on_closedBall
    (N := L.M) (M := (P (phi i)).M) (L.S.base.metric 0) hc L.basepoint
    (by norm_num : (0 : ℝ) < 9) (h := L.S.base.metric)
    (g := (P (phi i)).S.base.metric) (F := F.partialDiffeomorph i) cmp
    (by norm_num) le_rfl le_rfl hC2.le (by simp : (0 : ℝ) ∈ ({0} : Set ℝ))
    (hsource hz) hz hrm
  have hroot := Real.sqrt_le_sqrt hnorm
  rw [Real.sqrt_sq (sourceCurvatureBound_pos 3 hC2.le).le] at hroot
  have hs := scalar_abs_le_rm ((P (phi i)).S.base.metric 0) (F.partialDiffeomorph i z)
  change |(P (phi i)).S.scalar 0 (F.partialDiffeomorph i z)| ≤
    (Module.finrank ℝ ThreeSpace : ℝ) ^ 2 *
      Real.sqrt ((P (phi i)).rmNormSq 0 (F.partialDiffeomorph i z)) at hs
  rw [show Module.finrank ℝ ThreeSpace = 3 from by simp [ThreeSpace]] at hs
  norm_num only at hs
  have hterminal : (P (phi i)).S.scalar 0 (F.partialDiffeomorph i z) ≤
      9 * sourceCurvatureBound 3 C2 := by
    exact (le_abs_self _).trans (hs.trans (mul_le_mul_of_nonneg_left hroot (by norm_num)))
  have hlim := KappaSolutions.ancientKappaThree_toKLim (P (phi i)) (hP (phi i))
    (by simp [ThreeSpace])
  have hh := hlim.rmNormSq_le_of_terminal_scalar_le (P (phi i))
    (by simp [ThreeSpace]) ht (F.partialDiffeomorph i z) hterminal
  nlinarith [sq_nonneg (sourceCurvatureBound 3 C2)]

end DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn

end
