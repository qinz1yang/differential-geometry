import DifferentialGeometry.Geometry.Metric.Convergence.FiniteOrderNorm
import DifferentialGeometry.Geometry.Metric.Pullback.PartialDiffeomorph.Basic

set_option autoImplicit false

noncomputable section

namespace DifferentialGeometry.PartialDiffeomorph

open scoped Manifold ContDiff ENNReal

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]

local instance : CompleteSpace E := FiniteDimensional.complete ℝ E

variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [T2Space M] [IsManifold I ∞ M]
  {N : Type*} [TopologicalSpace N] [ChartedSpace H N]
  [T2Space N] [IsManifold I ∞ N]

def metricCkErrorOn (Φ : PartialDiffeomorph I I M N ∞)
    (K : Set M) (p : ℕ) (g : SmoothRiemannianMetric I M)
    (h : SmoothRiemannianMetric I N) : ℝ≥0∞ :=
  let U : TopologicalSpace.Opens M := ⟨Φ.source, Φ.open_source⟩
  CheegerGromovCompactness.metricCkENormOn (Subtype.val ⁻¹' K) p
    (pullbackMetricOn Φ U Set.Subset.rfl h)
    (g.restrictOpen U) (g.restrictOpen U)

def isMetricApproximationOn (Φ : PartialDiffeomorph I I M N ∞)
    (K : Set M) (p : ℕ) (ε : ℝ) (g : SmoothRiemannianMetric I M)
    (h : SmoothRiemannianMetric I N) : Prop :=
  K ⊆ Φ.source ∧ metricCkErrorOn Φ K p g h < ENNReal.ofReal ε

theorem metricCkErrorOn_mono_set (Φ : PartialDiffeomorph I I M N ∞)
    {K L : Set M} (hKL : K ⊆ L) (p : ℕ)
    (g : SmoothRiemannianMetric I M) (h : SmoothRiemannianMetric I N) :
    metricCkErrorOn Φ K p g h ≤ metricCkErrorOn Φ L p g h :=
  CheegerGromovCompactness.metricCkENormOn_mono_set
    (Set.preimage_mono hKL) p _ _ _

theorem metricCkErrorOn_mono_order (Φ : PartialDiffeomorph I I M N ∞)
    (K : Set M) {p q : ℕ} (hpq : p ≤ q)
    (g : SmoothRiemannianMetric I M) (h : SmoothRiemannianMetric I N) :
    metricCkErrorOn Φ K p g h ≤ metricCkErrorOn Φ K q g h :=
  CheegerGromovCompactness.metricCkENormOn_mono_order _ hpq _ _ _

theorem isMetricApproximationOn.epsilon_pos
    {Φ : PartialDiffeomorph I I M N ∞} {K : Set M} {p : ℕ} {ε : ℝ}
    {g : SmoothRiemannianMetric I M} {h : SmoothRiemannianMetric I N}
    (hΦ : isMetricApproximationOn Φ K p ε g h) : 0 < ε :=
  ENNReal.ofReal_pos.mp (lt_of_le_of_lt zero_le hΦ.2)

theorem isMetricApproximationOn.mono
    {Φ : PartialDiffeomorph I I M N ∞} {K L : Set M} {p q : ℕ} {ε δ : ℝ}
    {g : SmoothRiemannianMetric I M} {h : SmoothRiemannianMetric I N}
    (hΦ : isMetricApproximationOn Φ L q ε g h)
    (hKL : K ⊆ L) (hpq : p ≤ q) (hεδ : ε ≤ δ) :
    isMetricApproximationOn Φ K p δ g h := by
  refine ⟨hKL.trans hΦ.1, ?_⟩
  exact ((metricCkErrorOn_mono_set Φ hKL p g h).trans
    (metricCkErrorOn_mono_order Φ L hpq g h)).trans_lt
      (hΦ.2.trans_le (ENNReal.ofReal_le_ofReal hεδ))

theorem isMetricApproximationOn.metricDerivNorm_zero_lt
    {Φ : PartialDiffeomorph I I M N ∞} {K : Set M} {p : ℕ} {ε : ℝ}
    {g : SmoothRiemannianMetric I M} {h : SmoothRiemannianMetric I N}
    (hΦ : isMetricApproximationOn Φ K p ε g h) {x : M} (hx : x ∈ K) :
    let U : TopologicalSpace.Opens M := ⟨Φ.source, Φ.open_source⟩
    CheegerGromovCompactness.metricDerivNorm (I := I) 0
      (pullbackMetricOn Φ U Set.Subset.rfl h)
      (g.restrictOpen U) (g.restrictOpen U) ⟨x, hΦ.1 hx⟩ < ε := by
  exact CheegerGromovCompactness.metricDerivNorm_zero_lt_of_metricCkENormOn_lt
    _ p _ _ _ hΦ.2 hx

end DifferentialGeometry.PartialDiffeomorph
