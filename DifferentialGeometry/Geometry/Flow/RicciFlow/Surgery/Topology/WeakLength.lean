import DifferentialGeometry.Geometry.Metric.Comparison.DistanceScaling
import DifferentialGeometry.Analysis.Integration.Measure.Riemannian.Invariance
import DifferentialGeometry.Geometry.Metric.WeakLength
import Mathlib.Topology.EMetricSpace.BoundedVariation

noncomputable section

open Set Filter MeasureTheory Bundle Manifold
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

section ChartedSpaceInstances

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {H : Type*} [TopologicalSpace H]
    {M : Type*} [TopologicalSpace M]

theorem regularSpace_of_chartedSpace
    (I : ModelWithCorners ℝ E H) [ChartedSpace H M] [T2Space M] : RegularSpace M := by
  have : LocallyCompactSpace H := I.locallyCompactSpace
  have : LocallyCompactSpace M := ChartedSpace.locallyCompactSpace H M
  have : WeaklyLocallyCompactSpace M := inferInstance
  have : R1Space M := T2Space.r1Space
  infer_instance

theorem sigmaCompactSpace_of_chartedSpace
    (I : ModelWithCorners ℝ E H) [ChartedSpace H M] [T2Space M]
    [SecondCountableTopology M] : SigmaCompactSpace M := by
  have : LocallyCompactSpace H := I.locallyCompactSpace
  have : LocallyCompactSpace M := ChartedSpace.locallyCompactSpace H M
  infer_instance

end ChartedSpaceInstances

section CurveLengthVariation

variable {E' : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E']
    {H' : Type*} [TopologicalSpace H']
    {I' : ModelWithCorners ℝ E' H'}
    {M' : Type*} [TopologicalSpace M'] [ChartedSpace H' M'] [IsManifold I' ∞ M']
    [RegularSpace M']

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
theorem riemannianCurveLength_eq_eVariationOn
    (g : SmoothRiemannianMetric I' M') (γ : ℝ → M') (a b : ℝ) :
    riemannianCurveLength g γ a b =
      (letI : RiemannianBundle (TangentSpace I' : M' → Type _) := ⟨g.toRiemannianMetric⟩
       letI : IsContinuousRiemannianBundle E' (TangentSpace I' : M' → Type _) :=
         ⟨g.inner, g.contMDiff.continuous, fun _ _ _ => rfl⟩
       letI : PseudoEMetricSpace M' := .ofRiemannianMetric I' M'
       eVariationOn γ (Icc a b)) := rfl

end CurveLengthVariation

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

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
theorem rfs_weak_length [FiniteDimensional ℝ E] [FiniteDimensional ℝ F]
    [T2Space M] [T2Space N] [SecondCountableTopology M] [SecondCountableTopology N]
    [I.Boundaryless] [J.Boundaryless]
    (g : SmoothRiemannianMetric I M) (h : SmoothRiemannianMetric J N)
    (f : C(M, N))
    (hloc : ∀ x : M, ∃ U ∈ 𝓝 x, ∃ L : ℝ≥0, ∀ y ∈ U, ∀ z ∈ U,
      riemannianEDistOf h (f y) (f z) ≤ L * riemannianEDistOf g y z)
    (hdf : letI : LocallyCompactSpace M := Manifold.locallyCompact_of_finiteDimensional I
      ∀ᵐ x ∂(Integral.Measure.riemannianVolumeMeasure (I := I) (M := M) g),
      MDifferentiableAt I J f x → ∀ v : TangentSpace I x,
        h.inner (f x) (mfderiv I J f x v) (mfderiv I J f x v) ≤ g.inner x v v)
    (γ : ℝ → M) (a b : ℝ) (hγ : ContinuousOn γ (Icc a b)) :
    riemannianCurveLength h (f ∘ γ) a b ≤ riemannianCurveLength g γ a b := by
  have : LocallyCompactSpace H := I.locallyCompactSpace
  have : LocallyCompactSpace M := ChartedSpace.locallyCompactSpace H M
  have : RegularSpace M := regularSpace_of_chartedSpace I
  have : SigmaCompactSpace M := sigmaCompactSpace_of_chartedSpace I
  have : LocallyCompactSpace G := J.locallyCompactSpace
  have : LocallyCompactSpace N := ChartedSpace.locallyCompactSpace G N
  have : RegularSpace N := regularSpace_of_chartedSpace J
  have : SigmaCompactSpace N := sigmaCompactSpace_of_chartedSpace J
  have hf : ∀ p : M, ∃ L : ℝ≥0, ∃ t ∈ 𝓝 p, ∀ x ∈ t, ∀ y ∈ t,
      riemannianEDistOf h (f x) (f y) ≤ L * riemannianEDistOf g x y :=
    fun p => let ⟨U, hU, L, hL⟩ := hloc p; ⟨L, U, hU, hL⟩
  have hdf' : ∀ᵐ x ∂(Integral.Measure.riemannianVolumeMeasure (I := I) (M := M) g),
      MDifferentiableAt I J (f : M → N) x → ∀ v : TangentSpace I x,
        Real.sqrt (h.inner (f x) (mfderiv I J (f : M → N) x v)
          (mfderiv I J (f : M → N) x v)) ≤ Real.sqrt (g.inner x v v) := by
    filter_upwards [hdf] with x hx hxd v
    exact Real.sqrt_le_sqrt (hx hxd v)
  have hmain := DifferentialGeometry.Geometry.Metric.eVariationOn_comp_le_of_ae_mfderiv
    g h (f : M → N) hf hdf' γ a b hγ
  rw [← riemannianCurveLength_eq_eVariationOn h (f ∘ γ) a b,
    ← riemannianCurveLength_eq_eVariationOn g γ a b] at hmain
  exact hmain

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
