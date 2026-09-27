import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.StandardCap.WindowScalarBounds
import DifferentialGeometry.Geometry.Metric.Convergence.ScalingLimit
import DifferentialGeometry.Geometry.Curvature.Naturality.Pullback.LocalCross
import DifferentialGeometry.Geometry.Metric.PullbackScaling

noncomputable section

open Set Filter Function Manifold
open DifferentialGeometry.CheegerGromovCompactness DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
open scoped Manifold ContDiff Topology ENNReal

namespace DifferentialGeometry.PDE.RicciFlow.StandardCap

universe v

private local instance (D : ℝ) : SigmaCompactSpace (standardCapWindow D) :=
  isSigmaCompact_iff_sigmaCompactSpace.mp
    (DifferentialGeometry.Geometry.isSigmaCompact_of_isOpen ThreeModel (standardCapWindow D).isOpen)

theorem exists_scalar_normalized_marked_window_limit
    {D r : ℝ} (hmark : transitionEnd ≤ r) (hrD : r < D + 1)
    {N : ℕ} (hN : 2 ≤ N)
    (g : ℕ → SmoothRiemannianMetric ThreeModel (standardCapWindow D))
    (hconv : MetricCPConvergenceOn {z : standardCapWindow D | ‖z.val‖ ≤ r} N g
      (metric.restrictOpen (standardCapWindow D)) (metric.restrictOpen (standardCapWindow D)))
    (u : ℕ → standardCapWindow D) (hu : ∀ n, ‖(u n).val‖ ≤ transitionEnd)
    (M : ℕ → Type v) [∀ n, TopologicalSpace (M n)] [∀ n, ChartedSpace ThreeSpace (M n)]
    [∀ n, IsManifold ThreeModel ∞ (M n)] [∀ n, T2Space (M n)]
    (h : ∀ n, SmoothRiemannianMetric ThreeModel (M n))
    (q : ℕ → ℝ) (hq : ∀ n, 0 < q n)
    (Phi : ∀ n, standardCapWindow D → M n)
    (hPhi : ∀ n, IsLocalDiffeomorph ThreeModel ThreeModel ∞ (Phi n))
    (x : ∀ n, M n) (hpoint : ∀ n, Phi n (u n) = x n)
    (hmetric : ∀ n (z : standardCapWindow D) (v w : TangentSpace ThreeModel z),
      (g n).inner z v w = (scaleMetric (q n) (hq n) (h n)).inner (Phi n z)
        (mfderiv ThreeModel ThreeModel (Phi n) z v) (mfderiv ThreeModel ThreeModel (Phi n) z w)) :
    ∃ (phi : ℕ → ℕ) (z : standardCapWindow D), StrictMono phi ∧
      ‖z.val‖ ≤ transitionEnd ∧ Tendsto (u ∘ phi) atTop (𝓝 z) ∧
      ∃ hlim : 1 ≤ metricScalarAt metric z.val,
      Tendsto (fun n => metricScalarAt (h (phi n)) (x (phi n)) / q (phi n)) atTop
        (𝓝 (metricScalarAt metric z.val)) ∧
      ∃ hR : ∀ n, 0 < metricScalarAt (h (phi n)) (x (phi n)),
        MetricCPConvergenceOn {y : standardCapWindow D | ‖y.val‖ ≤ r} N
          (fun n => localPullMetric
            (scaleMetric (metricScalarAt (h (phi n)) (x (phi n))) (hR n) (h (phi n)))
            (Phi (phi n)) (hPhi (phi n)))
          (scaleMetric (metricScalarAt metric z.val) (lt_of_lt_of_le zero_lt_one hlim)
            (metric.restrictOpen (standardCapWindow D)))
          (scaleMetric (metricScalarAt metric z.val) (lt_of_lt_of_le zero_lt_one hlim)
            (metric.restrictOpen (standardCapWindow D))) := by
  classical
  let gRef := metric.restrictOpen (standardCapWindow D)
  let K : Set (standardCapWindow D) := {y | ‖y.val‖ ≤ r}
  have hK : IsCompact K := by
    have hc : IsCompact {z : ThreeSpace | ‖z‖ ≤ r} := by
      simpa only [Metric.closedBall, dist_zero_right] using isCompact_closedBall (0 : ThreeSpace) r
    exact _root_.Topology.IsInducing.subtypeVal.isCompact_preimage' hc (by
      intro z hz
      exact ⟨⟨z, hz.trans_lt hrD⟩, rfl⟩)
  have hmetricEq (n : ℕ) : g n = localPullMetric (scaleMetric (q n) (hq n) (h n))
      (Phi n) (hPhi n) := by
    apply SmoothRiemannianMetric.ext_inner
    intro z v w
    rw [localPullMetric_inner]
    exact hmetric n z v w
  have hscalarEq (n : ℕ) : metricScalarAt (g n) (u n) =
      metricScalarAt (h n) (x n) / q n := by
    rw [hmetricEq, metricScalarAt_localPull, metricScalarAt_scaleMetric, hpoint]
    ring
  obtain ⟨phi, z, hphi, hz, hmarklim, hscalarlim, hlim, hpositive⟩ :=
    exists_subseq_marked_scalar_limit_of_metric_cp_convergence D r hmark hrD N hN g hconv u hu
  obtain ⟨N0, hN0⟩ := eventually_atTop.mp hpositive
  let ind : ℕ → ℕ := fun n => phi (n + N0)
  have hshift : StrictMono (fun n : ℕ => n + N0) := strictMono_id.add_const N0
  have hind : StrictMono ind := hphi.comp hshift
  have hmarklim' : Tendsto (u ∘ ind) atTop (𝓝 z) := hmarklim.comp hshift.tendsto_atTop
  have hscalarlim' : Tendsto (fun n => metricScalarAt (g (ind n)) (u (ind n))) atTop
      (𝓝 (metricScalarAt gRef z)) := hscalarlim.comp hshift.tendsto_atTop
  have hgpos (n : ℕ) : 0 < metricScalarAt (g (ind n)) (u (ind n)) := by
    have hi : N0 ≤ ind n := (Nat.le_add_left N0 n).trans (hphi.id_le (n + N0))
    exact (by norm_num : (0 : ℝ) < 1 / 2).trans (hN0 _ hi)
  have hR (n : ℕ) : 0 < metricScalarAt (h (ind n)) (x (ind n)) := by
    have hh := hgpos n
    rw [hscalarEq] at hh
    exact (div_pos_iff_of_pos_right (hq (ind n))).mp hh
  have hconv' : MetricCPConvergenceOn K N (fun n => g (ind n)) gRef gRef := by
    intro eps heps
    obtain ⟨N1, hN1⟩ := hconv eps heps
    exact ⟨N1, fun n hn => hN1 (ind n) (hn.trans (hind.id_le n))⟩
  have hlimpos : 0 < metricScalarAt gRef z := zero_lt_one.trans_le hlim
  have hnorm := hconv'.scaleMetric_of_tendsto hK hgpos hlimpos hscalarlim'
  have hnormalEq (n : ℕ) :
      scaleMetric (metricScalarAt (g (ind n)) (u (ind n))) (hgpos n) (g (ind n)) =
        localPullMetric (scaleMetric (metricScalarAt (h (ind n)) (x (ind n))) (hR n)
          (h (ind n))) (Phi (ind n)) (hPhi (ind n)) := by
    apply SmoothRiemannianMetric.ext_inner
    intro z v w
    rw [scaleMetric_inner, hmetric (ind n), localPullMetric_inner, scaleMetric_inner,
      scaleMetric_inner, hscalarEq]
    field_simp [(hq (ind n)).ne']
  have hlimAmbient : metricScalarAt gRef z = metricScalarAt metric z.val :=
    metricScalarAt_restrictOpen metric (standardCapWindow D) z
  refine ⟨ind, z, hind, hz, hmarklim', hlimAmbient ▸ hlim, ?_, hR, ?_⟩
  · simpa only [hscalarEq, hlimAmbient] using hscalarlim'
  · simpa only [hnormalEq, hlimAmbient] using hnorm

end DifferentialGeometry.PDE.RicciFlow.StandardCap
