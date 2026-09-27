import DifferentialGeometry.Geometry.Metric.CurveVariation.Comparison
import DifferentialGeometry.Geometry.Metric.CurveVariation.Distance
import DifferentialGeometry.Geometry.Metric.CurveVariation.WeakDerivative
import DifferentialGeometry.Topology.Manifold.LocalCompactness

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


abbrev riemannianCurveLength (g : SmoothRiemannianMetric I M) (γ : ℝ → M)
    (a b : ℝ) : ℝ≥0∞ := Geometry.riemannianCurveVariation g γ a b

alias regularSpace_of_chartedSpace := DifferentialGeometry.Topology.Manifold.regularSpace_of_chartedSpace
alias sigmaCompactSpace_of_chartedSpace := DifferentialGeometry.Topology.Manifold.sigmaCompactSpace_of_chartedSpace

theorem riemannianCurveLength_comp_le (g : SmoothRiemannianMetric I M)
    (h : SmoothRiemannianMetric J N) (f : M → N) (L : ℝ≥0)
    (hf : ∀ x y, riemannianEDistOf h (f x) (f y) ≤ L * riemannianEDistOf g x y)
    (γ : ℝ → M) (a b : ℝ) :
    riemannianCurveLength h (f ∘ γ) a b ≤ L * riemannianCurveLength g γ a b := by
  exact Geometry.riemannianCurveVariation_comp_le g h f L hf γ a b

theorem riemannianCurveLength_mono (g : SmoothRiemannianMetric I M) (γ : ℝ → M)
    {a b c d : ℝ} (hac : a ≤ c) (hdb : d ≤ b) :
    riemannianCurveLength g γ c d ≤ riemannianCurveLength g γ a b := by
  exact Geometry.riemannianCurveVariation_mono g γ hac hdb

theorem riemannianCurveLength_comp_le_of_local [RegularSpace M] [RegularSpace N]
    (g : SmoothRiemannianMetric I M) (h : SmoothRiemannianMetric J N) (f : C(M, N))
    (L : ℝ≥0)
    (hloc : ∀ x : M, ∃ U ∈ 𝓝 x, ∀ (a b : ℝ) (γ : ℝ → M),
      a ≤ b → ContinuousOn γ (Icc a b) → MapsTo γ (Icc a b) U →
      riemannianCurveLength g γ a b ≠ ⊤ →
      riemannianCurveLength h (f ∘ γ) a b ≤ L * riemannianCurveLength g γ a b)
    {γ : ℝ → M} {a b : ℝ} (hγ : ContinuousOn γ (Icc a b))
    (hfin : riemannianCurveLength g γ a b ≠ ⊤) :
    riemannianCurveLength h (f ∘ γ) a b ≤ L * riemannianCurveLength g γ a b := by
  exact Geometry.riemannianCurveVariation_comp_le_of_local g h f L hloc hγ hfin

theorem riemannianEDistOf_le_riemannianCurveLength
    (g : SmoothRiemannianMetric I M) (γ : ℝ → M) {a b : ℝ} (hab : a ≤ b) :
    riemannianEDistOf g (γ a) (γ b) ≤ riemannianCurveLength g γ a b := by
  exact Geometry.riemannianEDistOf_le_riemannianCurveVariation g γ hab

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
theorem riemannianCurveLength_le_pathELength
    (g : SmoothRiemannianMetric I M) {γ : ℝ → M} {a b : ℝ}
    (hγ : ContMDiffOn 𝓘(ℝ, ℝ) I 1 γ (Icc a b)) :
    (let : RiemannianBundle (TangentSpace I : M → Type _) := ⟨g.toRiemannianMetric⟩
     let : IsContinuousRiemannianBundle E (TangentSpace I : M → Type _) :=
       ⟨g.inner, g.contMDiff.continuous, fun _ _ _ => rfl⟩
     riemannianCurveLength g γ a b ≤ pathELength I γ a b) := by
  exact Geometry.riemannianCurveVariation_le_pathELength g hγ

theorem rfs_weak_length [FiniteDimensional ℝ E] [FiniteDimensional ℝ F]
    [T2Space M] [T2Space N] [SecondCountableTopology M]
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
  exact Geometry.riemannianCurveVariation_comp_le_of_ae_mfderiv g h f hloc hdf γ a b hγ

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
       eVariationOn γ (Icc a b)) := by
  exact Geometry.riemannianCurveVariation_eq_eVariationOn g γ a b

end CurveLengthVariation

theorem rfs_local_to_global_length [FiniteDimensional ℝ E] [FiniteDimensional ℝ F]
    [T2Space M] [T2Space N]
    [ConnectedSpace M]
    (g : SmoothRiemannianMetric I M) (h : SmoothRiemannianMetric J N)
    (f : C(M, N)) (L : ℝ≥0)
    (hloc : ∀ x : M, ∃ U ∈ 𝓝 x, ∀ (a b : ℝ) (γ : ℝ → M),
      a ≤ b → ContinuousOn γ (Icc a b) → MapsTo γ (Icc a b) U →
      riemannianCurveLength g γ a b ≠ ⊤ →
      riemannianCurveLength h (f ∘ γ) a b ≤ L * riemannianCurveLength g γ a b) :
    ∀ x y, riemannianEDistOf h (f x) (f y) ≤ L * riemannianEDistOf g x y := by
  have : RegularSpace M := regularSpace_of_chartedSpace I
  have : RegularSpace N := regularSpace_of_chartedSpace J
  exact Geometry.riemannianEDistOf_comp_le_of_local_riemannianCurveVariation g h f L hloc

theorem rfs_local_to_global_length_of_ne_top [FiniteDimensional ℝ E] [FiniteDimensional ℝ F]
    [T2Space M] [T2Space N]
    (g : SmoothRiemannianMetric I M) (h : SmoothRiemannianMetric J N)
    (f : C(M, N)) (L : ℝ≥0)
    (hloc : ∀ x : M, ∃ U ∈ 𝓝 x, ∀ (a b : ℝ) (γ : ℝ → M),
      a ≤ b → ContinuousOn γ (Icc a b) → MapsTo γ (Icc a b) U →
      riemannianCurveLength g γ a b ≠ ⊤ →
      riemannianCurveLength h (f ∘ γ) a b ≤ L * riemannianCurveLength g γ a b)
    {x y : M} (hgfin : riemannianEDistOf g x y ≠ ⊤) :
    riemannianEDistOf h (f x) (f y) ≤ L * riemannianEDistOf g x y := by
  have : RegularSpace M := regularSpace_of_chartedSpace I
  have : RegularSpace N := regularSpace_of_chartedSpace J
  exact Geometry.riemannianEDistOf_comp_le_of_local_riemannianCurveVariation_of_ne_top g h f L hloc hgfin

theorem rfs_local_to_global_length_of_ne_zero [FiniteDimensional ℝ E] [FiniteDimensional ℝ F]
    [T2Space M] [T2Space N]
    (g : SmoothRiemannianMetric I M) (h : SmoothRiemannianMetric J N)
    (f : C(M, N)) (L : ℝ≥0) (hL : L ≠ 0)
    (hloc : ∀ x : M, ∃ U ∈ 𝓝 x, ∀ (a b : ℝ) (γ : ℝ → M),
      a ≤ b → ContinuousOn γ (Icc a b) → MapsTo γ (Icc a b) U →
      riemannianCurveLength g γ a b ≠ ⊤ →
      riemannianCurveLength h (f ∘ γ) a b ≤ L * riemannianCurveLength g γ a b) :
    ∀ x y, riemannianEDistOf h (f x) (f y) ≤ L * riemannianEDistOf g x y := by
  have : RegularSpace M := regularSpace_of_chartedSpace I
  have : RegularSpace N := regularSpace_of_chartedSpace J
  exact Geometry.riemannianEDistOf_comp_le_of_local_riemannianCurveVariation_of_ne_zero g h f L hL hloc

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
