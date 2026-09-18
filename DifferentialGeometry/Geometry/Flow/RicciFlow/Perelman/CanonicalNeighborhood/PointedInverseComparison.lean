import DifferentialGeometry.Geometry.Compactness.CheegerGromov.Pointed.Convergence.InverseApproximation
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.StaticMetricApproximation
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.StaticRescalingComparison
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.PointedScalarCompactControl

set_option autoImplicit false
noncomputable section
open Set Filter
open scoped Manifold ContDiff Topology

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn

open DifferentialGeometry.CheegerGromovCompactness DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

universe u

attribute [local instance] PointedRiemannianManifold.topology
  PointedRiemannianManifold.charted PointedRiemannianManifold.smooth
  PointedRiemannianManifold.t2 PointedRiemannianManifold.sigmaCompact

variable {X : PointedRiemannianSeq.{u, 0, 0} I3}
  {L : PointedRiemannianManifold.{u, 0, 0} I3} {subseq : ℕ → ℕ}
  {Phi : PointedRiemannianConvergenceMaps X L subseq}

theorem eventually_scalar_normalized_inverse_comparison
    (C : MetricConvergenceData Phi)
    (hcanonical : ∀ k, C.domain k = CanonicalMetricCompactness.canonicalSourceData Phi k)
    (K : Set L.M) (hK : IsCompact K) (order : ℕ) {eps : ℝ} (heps : 0 < eps) :
    ∀ᶠ k in atTop, K ⊆ Phi.source k ∧
      ∀ x ∈ K, ∀ hscalar : 2 ≤ metricScalarAt L.metric x,
        ∃ hq : 0 < metricScalarAt (X.obj (subseq k)).metric (Phi.map k x),
          ∀ A : Set L.M, A ⊆ interior K → Nonempty (MetricComparisonOn
            (fun _ => scaleMetric (metricScalarAt (X.obj (subseq k)).metric (Phi.map k x))
              hq (X.obj (subseq k)).metric)
            (fun _ => scaleMetric (metricScalarAt L.metric x)
              (lt_of_lt_of_le (by norm_num : (0 : ℝ) < 2) hscalar) L.metric)
            ((Phi.partialDiffeomorph k).symm : (X.obj (subseq k)).M → L.M)
            (Phi.map k '' A) {0} order eps) := by
  let n : ℝ := Real.sqrt (Module.finrank ℝ ThreeSpace : ℝ)
  have hn : 0 ≤ n := Real.sqrt_nonneg _
  let eta := min 1 (eps / (4 * (n + 1)))
  have heta : 0 < eta := lt_min zero_lt_one (by positivity)
  have heta1 : eta ≤ 1 := min_le_left _ _
  have hetan : eta * n ≤ eps / 4 := by
    have h := (le_div_iff₀ (by positivity : 0 < 4 * (n + 1))).mp
      (min_le_right 1 (eps / (4 * (n + 1))))
    change eta * (4 * (n + 1)) ≤ eps at h
    nlinarith [heta.le]
  let beta := min (1 / 2) (eps / 4)
  have hbeta : 0 < beta := lt_min (by norm_num) (by positivity)
  have hbeta1 : beta < 1 := lt_of_le_of_lt (min_le_left _ _) (by norm_num)
  have hbudget : (1 + eta) * beta + eta * n ≤ eps := by
    have hb : beta ≤ eps / 4 := min_le_right _ _
    have hmul := mul_le_mul_of_nonneg_right (show 1 + eta ≤ 2 by linarith) hbeta.le
    linarith
  let gamma := min (1 / 2) eta
  have hgamma : 0 < gamma := lt_min (by norm_num) heta
  obtain ⟨i0, hi0⟩ := KappaSolutions.pointedScalar_uniform_on_compact_of_canonical_domains
    C hcanonical K hK gamma hgamma
  filter_upwards [C.eventually_inverse_map_metric_approximation hcanonical K hK
    order hbeta hbeta1, eventually_ge_atTop i0] with k hInv hk
  refine ⟨hInv.1, ?_⟩
  intro x hx hscalar
  let q := metricScalarAt (X.obj (subseq k)).metric (Phi.map k x)
  let c := metricScalarAt L.metric x
  have hc : 0 < c := lt_of_lt_of_le (by norm_num) hscalar
  have herr : |q - c| < gamma := (hi0 k hk).2 x hx
  have hq1 : 1 ≤ q := by
    have hhalf : gamma ≤ 1 / 2 := min_le_left _ _
    have hlower := (abs_lt.mp herr).1
    change 2 ≤ c at hscalar
    linarith
  have hratio : |c / q - 1| ≤ eta := by
    have hq : 0 < q := zero_lt_one.trans_le hq1
    rw [show c / q - 1 = (c - q) / q by field_simp,
      abs_div, abs_of_pos hq, abs_sub_comm]
    exact (div_le_self (abs_nonneg _) hq1).trans
      (herr.le.trans (min_le_right _ _))
  refine ⟨zero_lt_one.trans_le hq1, ?_⟩
  intro A hA
  obtain ⟨D⟩ := hInv.2 A hA
  exact ⟨(MetricComparisonOn.ofMapMetricApproximation D ({0} : Set ℝ)).staticRescaleOfOneLe (t := 0)
    (by simp) q c hq1 hc hbeta.le hratio hbudget⟩

end DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn
