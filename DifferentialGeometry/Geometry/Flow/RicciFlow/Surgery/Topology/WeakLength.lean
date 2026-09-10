import DifferentialGeometry.Geometry.Metric.Comparison.DistanceScaling
import DifferentialGeometry.Analysis.Integration.Measure.Riemannian.Invariance
import Mathlib.Topology.EMetricSpace.BoundedVariation

noncomputable section

open Set Filter MeasureTheory
open scoped Manifold ContDiff NNReal ENNReal Topology

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    {H G : Type*} [TopologicalSpace H] [TopologicalSpace G]
    {I : ModelWithCorners ℝ E H} {J : ModelWithCorners ℝ F G}
    {M N : Type*} [TopologicalSpace M] [TopologicalSpace N]
    [ChartedSpace H M] [ChartedSpace G N] [IsManifold I ∞ M] [IsManifold J ∞ N]

def riemannianCurveLength (g : SmoothRiemannianMetric I M) (γ : ℝ → M)
    (a b : ℝ) : ℝ≥0∞ :=
  ⨆ p : ℕ × {u : ℕ → ℝ // Monotone u ∧ ∀ i, u i ∈ Icc a b},
    ∑ i ∈ Finset.range p.1,
      riemannianEDistOf g (γ (p.2.1 (i + 1))) (γ (p.2.1 i))

theorem riemannianCurveLength_comp_le (g : SmoothRiemannianMetric I M)
    (h : SmoothRiemannianMetric J N) (f : M → N) (L : ℝ≥0)
    (hf : ∀ x y, riemannianEDistOf h (f x) (f y) ≤ L * riemannianEDistOf g x y)
    (γ : ℝ → M) (a b : ℝ) :
    riemannianCurveLength h (f ∘ γ) a b ≤ L * riemannianCurveLength g γ a b := by
  unfold riemannianCurveLength
  refine iSup_le fun p => ?_
  calc
    _ ≤ ∑ i ∈ Finset.range p.1,
        (L : ℝ≥0∞) * riemannianEDistOf g (γ (p.2.1 (i + 1))) (γ (p.2.1 i)) :=
      Finset.sum_le_sum fun i _ => hf _ _
    _ = (L : ℝ≥0∞) * ∑ i ∈ Finset.range p.1,
        riemannianEDistOf g (γ (p.2.1 (i + 1))) (γ (p.2.1 i)) :=
      (Finset.mul_sum ..).symm
    _ ≤ _ := mul_le_mul_right (α := ℝ≥0∞)
      (le_iSup (fun q : ℕ × {v : ℕ → ℝ // Monotone v ∧ ∀ i, v i ∈ Icc a b} =>
        ∑ i ∈ Finset.range q.1,
          riemannianEDistOf g (γ (q.2.1 (i + 1))) (γ (q.2.1 i))) p) (L : ℝ≥0∞)

theorem rfs_local_to_global_length [FiniteDimensional ℝ E] [FiniteDimensional ℝ F]
    [T2Space M] [T2Space N] [SecondCountableTopology M] [SecondCountableTopology N]
    [ConnectedSpace M] [ConnectedSpace N]
    (g : SmoothRiemannianMetric I M) (h : SmoothRiemannianMetric J N)
    (f : C(M, N)) (L : ℝ≥0)
    (hloc : ∀ x : M, ∃ U ∈ 𝓝 x, ∀ (a b : ℝ) (γ : ℝ → M),
      a ≤ b → ContinuousOn γ (Icc a b) → MapsTo γ (Icc a b) U →
      riemannianCurveLength g γ a b ≠ ⊤ →
      riemannianCurveLength h (f ∘ γ) a b ≤ L * riemannianCurveLength g γ a b) :
    ∀ x y, riemannianEDistOf h (f x) (f y) ≤ L * riemannianEDistOf g x y := by
  sorry

theorem rfs_weak_length [FiniteDimensional ℝ E] [FiniteDimensional ℝ F]
    [T2Space M] [T2Space N] [SecondCountableTopology M] [SecondCountableTopology N]
    (g : SmoothRiemannianMetric I M) (h : SmoothRiemannianMetric J N)
    (f : C(M, N))
    (hloc : ∀ x : M, ∃ U ∈ 𝓝 x, ∃ L : ℝ≥0, ∀ y ∈ U, ∀ z ∈ U,
      riemannianEDistOf h (f y) (f z) ≤ L * riemannianEDistOf g y z)
    (hdf : letI : LocallyCompactSpace M := Manifold.locallyCompact_of_finiteDimensional I
      ∀ᵐ x ∂(Integral.Measure.riemannianVolumeMeasure (I := I) (M := M) g),
      MDifferentiableAt I J f x → ∀ v : TangentSpace I x,
        h.inner (f x) (mfderiv I J f x v) (mfderiv I J f x v) ≤ g.inner x v v)
    (γ : ℝ → M) (a b : ℝ) (hab : a ≤ b) (hγ : ContinuousOn γ (Icc a b))
    (hrect : riemannianCurveLength g γ a b ≠ ⊤) :
    riemannianCurveLength h (f ∘ γ) a b ≤ riemannianCurveLength g γ a b := by
  sorry

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
