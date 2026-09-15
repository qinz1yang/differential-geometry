import DifferentialGeometry.Geometry.Metric.CurveVariation.Basic
import DifferentialGeometry.Topology.Manifold.LocalCompactness
import DifferentialGeometry.Geometry.Metric.WeakLength

noncomputable section

open Set Filter MeasureTheory Bundle Manifold
open scoped Manifold ContDiff NNReal ENNReal Topology

namespace DifferentialGeometry.Geometry

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    {H G : Type*} [TopologicalSpace H] [TopologicalSpace G]
    {I : ModelWithCorners ℝ E H} {J : ModelWithCorners ℝ F G}
    {M N : Type*} [TopologicalSpace M] [TopologicalSpace N]
    [ChartedSpace H M] [ChartedSpace G N] [IsManifold I ∞ M] [IsManifold J ∞ N]

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
theorem riemannianCurveVariation_comp_le_of_ae_mfderiv [FiniteDimensional ℝ E] [FiniteDimensional ℝ F]
    [T2Space M] [T2Space N] [SecondCountableTopology M]
    [I.Boundaryless] [J.Boundaryless]
    (g : SmoothRiemannianMetric I M) (h : SmoothRiemannianMetric J N)
    (f : M → N)
    (hloc : ∀ x : M, ∃ U ∈ 𝓝 x, ∃ L : ℝ≥0, ∀ y ∈ U, ∀ z ∈ U,
      riemannianEDistOf h (f y) (f z) ≤ L * riemannianEDistOf g y z)
    (hdf : letI : LocallyCompactSpace M := Manifold.locallyCompact_of_finiteDimensional I
      ∀ᵐ x ∂(Integral.Measure.riemannianVolumeMeasure (I := I) (M := M) g),
      MDifferentiableAt I J f x → ∀ v : TangentSpace I x,
        h.inner (f x) (mfderiv I J f x v) (mfderiv I J f x v) ≤ g.inner x v v)
    (γ : ℝ → M) (a b : ℝ) (hγ : ContinuousOn γ (Icc a b)) :
    riemannianCurveVariation h (f ∘ γ) a b ≤ riemannianCurveVariation g γ a b := by
  have : LocallyCompactSpace H := I.locallyCompactSpace
  have : LocallyCompactSpace M := ChartedSpace.locallyCompactSpace H M
  have : RegularSpace M := DifferentialGeometry.Topology.Manifold.regularSpace_of_chartedSpace I
  have : SigmaCompactSpace M := DifferentialGeometry.Topology.Manifold.sigmaCompactSpace_of_chartedSpace I
  have : LocallyCompactSpace G := J.locallyCompactSpace
  have : LocallyCompactSpace N := ChartedSpace.locallyCompactSpace G N
  have : RegularSpace N := DifferentialGeometry.Topology.Manifold.regularSpace_of_chartedSpace J
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
  rw [← riemannianCurveVariation_eq_eVariationOn h (f ∘ γ) a b,
    ← riemannianCurveVariation_eq_eVariationOn g γ a b] at hmain
  exact hmain


end DifferentialGeometry.Geometry
