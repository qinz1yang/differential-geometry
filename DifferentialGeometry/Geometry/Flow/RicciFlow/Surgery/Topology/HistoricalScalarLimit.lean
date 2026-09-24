import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.HistoricalParabolicCompactness
import DifferentialGeometry.Geometry.Curvature.Naturality.Pullback.PartialDiffeomorph
import DifferentialGeometry.Geometry.Compactness.CheegerGromov.Limit.Metric.ScalarConvergence

set_option autoImplicit false
noncomputable section
open Set Bundle Manifold Filter
open DifferentialGeometry.CheegerGromovCompactness DifferentialGeometry.Geometry.Curvature
open scoped Manifold ContDiff Topology

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
universe u

private local instance {H : ObservedHistory.{u}} {i : Fin H.eventCount}
    {first : Fin (H.eventCount + 1)} {hle : first ≤ i.castSucc}
    (K : Set (H.event i).incoming.terminalRegularOpen) :
    SigmaCompactSpace (H.backwardSurvivorFootprintInterior first i hle K) := by
  let : SigmaCompactSpace (H.backwardSurvivorDomain first i.castSucc hle) :=
    isSigmaCompact_iff_sigmaCompactSpace.mp
      (Geometry.isSigmaCompact_of_isOpen ThreeModel
        (H.backwardSurvivorDomain first i.castSucc hle).isOpen)
  let : SigmaCompactSpace (H.backwardSurvivorTerminalFace first i hle) :=
    isSigmaCompact_iff_sigmaCompactSpace.mp
      (Geometry.isSigmaCompact_of_isOpen ThreeModel
        (H.backwardSurvivorTerminalFace first i hle).isOpen)
  exact isSigmaCompact_iff_sigmaCompactSpace.mp
    (Geometry.isSigmaCompact_of_isOpen ThreeModel
      (H.backwardSurvivorFootprintInterior first i hle K).isOpen)

theorem metricScalarAt_eq_one_of_historical_footprint_limit
    (A : ℕ → ObservedHistory.{u}) (i : ∀ n, Fin (A n).eventCount)
    (first : ∀ n, Fin ((A n).eventCount + 1)) (hle : ∀ n, first n ≤ (i n).castSucc)
    (δ : ℕ → ℝ) (k : ℕ → ℕ)
    (N : ∀ n, NormalizedNeck ((A n).event (i n)).terminal.metric (δ n) (k n))
    (K : ∀ n, Set ((A n).event (i n)).incoming.terminalRegularOpen)
    (p : ∀ n, (A n).backwardSurvivorFootprintInterior (first n) (i n) (hle n) (K n))
    (hp : ∀ n, (A n).backwardSurvivorFootprintMap (first n) (i n) (hle n) (K n) (p n) =
      (N n).center)
    (S : ∀ n, SmoothRiemannianMetric ThreeModel
      ((A n).backwardSurvivorFootprintInterior (first n) (i n) (hle n) (K n)))
    (hS : ∀ n, S n = scaleMetric (N n).scale (N n).scale_pos
      (localPullMetric ((A n).event (i n)).terminal.metric
        ((A n).backwardSurvivorFootprintMap (first n) (i n) (hle n) (K n))
        ((A n).backwardSurvivorFootprintMap_isLocalDiffeomorph
          (first n) (i n) (hle n) (K n))))
    {Q : Type*} [TopologicalSpace Q] [ChartedSpace ThreeSpace Q]
    [IsManifold ThreeModel ∞ Q] [T2Space Q] [SigmaCompactSpace Q]
    (V : TopologicalSpace.Opens Q) (q : V) (phi : ℕ → ℕ)
    (F : ∀ n, PartialDiffeomorph ThreeModel ThreeModel Q
      ((A (phi n)).backwardSurvivorFootprintInterior
        (first (phi n)) (i (phi n)) (hle (phi n)) (K (phi n))) ∞)
    (hsource : ∀ n, (V : Set Q) ⊆ (F n).source)
    (hbase : ∀ n, F n q = p (phi n))
    (G : ℕ → SmoothRiemannianMetric ThreeModel V) (g r : SmoothRiemannianMetric ThreeModel V)
    (hmetric : ∀ n (x : V) (v w : TangentSpace ThreeModel x),
      (G n).inner x v w = (S (phi n)).inner (F n x)
        (mfderiv ThreeModel ThreeModel (F n) x v)
        (mfderiv ThreeModel ThreeModel (F n) x w))
    (hconv : MetricCInfConvergenceOnCompacts G g r) :
    metricScalarAt g q = 1 := by
  let _ : SigmaCompactSpace V := isSigmaCompact_iff_sigmaCompactSpace.mp
    (Geometry.isSigmaCompact_of_isOpen ThreeModel V.isOpen)
  have hscalar (n : ℕ) : metricScalarAt (G n) q = 1 := by
    rw [metricScalarAt_eq_of_partialDiffeomorph_restriction
      (F n) V (hsource n) (G n) (S (phi n)) (hmetric n) q, hbase, hS,
      metricScalarAt_scaleMetric, metricScalarAt_localPull, hp, ← (N (phi n)).scale_scalar]
    exact inv_mul_cancel₀ (N (phi n)).scale_pos.ne'
  have hcompact : MetricCPConvergenceOn {q} 2 G g r := hconv {q} isCompact_singleton 2
  have hlimit := (hcompact.tendstoUniformlyOn_metricScalarAt isCompact_singleton).tendsto_at
    (mem_singleton q)
  have hconstant : Tendsto (fun n => metricScalarAt (G n) q) atTop (𝓝 (1 : ℝ)) := by
    simpa only [hscalar] using (tendsto_const_nhds : Tendsto (fun _ : ℕ => (1 : ℝ)) atTop (𝓝 1))
  exact tendsto_nhds_unique hlimit hconstant

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
