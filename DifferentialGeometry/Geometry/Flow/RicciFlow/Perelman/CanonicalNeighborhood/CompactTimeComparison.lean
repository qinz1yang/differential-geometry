import DifferentialGeometry.Geometry.Flow.RicciFlow.Compactness.Metric.OpenTimeJetExtension
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.WitnessComparisonConstruction

set_option autoImplicit false
noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn
open Bundle Filter Set
open scoped _root_.Manifold ContDiff _root_.Topology
open DifferentialGeometry.CheegerGromovCompactness DifferentialGeometry.Tensor0SBundle
open DifferentialGeometry.Geometry.Curvature DifferentialGeometry.Integral.Measure
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
open DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [CompleteSpace E] [NeZero (Module.finrank ℝ E)]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {N : Type*} [TopologicalSpace N] [ChartedSpace H N] [IsManifold I ∞ N]
  [T2Space N] [SigmaCompactSpace N] [BoundarylessManifold I N]
  {M : ℕ → Type*} [∀ n, TopologicalSpace (M n)] [∀ n, ChartedSpace ThreeSpace (M n)]
  [∀ n, IsManifold I3 ∞ (M n)]

theorem eventually_metricComparisonOn_of_local_flow_convergence
    (U : TopologicalSpace.Opens N) {D : RealTimeInterval}
    (S : ℕ → SolutionOn (I := I) (M := U) D) (hS : ∀ n, IsSolutionOn (S n))
    (G : SolutionOn (I := I) (M := N) D) (hG : IsSolutionOn G)
    {a c b : ℝ} (hac : a < c) (hcb : c < b)
    (hcarrier : D.carrier = Icc a b) (hregular : Ioo a b ⊆ D.regular)
    (R : SmoothRiemannianMetric I U)
    (hconv : ∀ K : Set U, IsCompact K → ∀ r : ℕ, ∀ epsilon : ℝ, 0 < epsilon →
      ∃ N : ℕ, ∀ n ≥ N, ∀ t ∈ Icc c b,
        metricDerivNormSupOn K r ((S n).base.metric t)
          ((G.base.metric t).restrictOpen U) R < epsilon)
    (g : ∀ n, ℝ → SmoothRiemannianMetric I3 (M n)) (F : ∀ n, N → M n)
    (hpair : ∀ n t, ∀ x : U, ∀ v w : TangentSpace I x,
      ((S n).base.metric t).inner x v w =
        (g n t).inner (F n x) (mfderiv I I3 (F n) (x : N) v) (mfderiv I I3 (F n) (x : N) w))
    {J : Set ℝ} (hJ : UniqueDiffOn ℝ J) (hJsub : J ⊆ Icc c b)
    {K : Set N} (hK : IsCompact K) (hKU : K ⊆ U)
    (order : ℕ) {epsilon : ℝ} (hepsilon : 0 < epsilon) :
    ∀ᶠ n in atTop, Nonempty (MetricComparisonOn G.base.metric (g n) (F n)
      K J order epsilon) := by
  obtain ⟨B, C, hBzero, hCzero, hB, hC, hbound⟩ :=
    exists_metric_time_jets_extension_on_compact U S hS G hG hac hcb hcarrier hregular
      R hconv hK hKU
  have hclose : ∀ᶠ n in atTop, ∀ p q : Fin (order + 1), ∀ t ∈ Icc c b, ∀ x ∈ K,
      tensor02CovDerivNormWith (p : ℕ) (B n (q : ℕ) t - C (q : ℕ) t)
        (G.base.metric t) (G.base.metric t) x ≤ epsilon := by
    rw [Filter.eventually_all]
    intro p
    rw [Filter.eventually_all]
    intro q
    exact eventually_atTop.mpr (hbound p q epsilon hepsilon)
  filter_upwards [hclose] with n hn
  refine ⟨metricComparisonOnOfGenuineTimeTowers G.base.metric (g n) (F n) K J
    hJ order epsilon (B n) C ?_ ?_ ?_ ?_ ?_⟩
  · intro t x hx v
    exact (hBzero n t x hx v).trans (hpair n t ⟨x, hKU hx⟩ (v 0) (v 1))
  · intro t x v
    rw [hCzero, metricTensorField_apply]
  · intro q t ht x _hx
    exact (hB n q t (hJsub ht) x).mono hJsub
  · intro q t ht x _hx
    exact (hC q t (hJsub ht) x).mono hJsub
  · intro p q hpq t ht x hx
    exact hn ⟨p, by omega⟩ ⟨q, by omega⟩ t (hJsub ht) x hx
end DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn
