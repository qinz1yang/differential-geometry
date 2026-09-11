import DifferentialGeometry.Geometry.Metric.BundleAlternating
import DifferentialGeometry.Geometry.Connection.MetricCompatibility.Multilinear
import DifferentialGeometry.Geometry.Connection.TensorNabla.Alternating

noncomputable section

open Bundle
open scoped Manifold ContDiff

namespace CovariantDerivative

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  {V : M → Type*} [TopologicalSpace (TotalSpace F V)]
  [∀ x, NormedAddCommGroup (V x)] [∀ x, InnerProductSpace ℝ (V x)]
  [FiberBundle F V] [VectorBundle ℝ F V] [ContMDiffVectorBundle ∞ F V I]
  [IsContMDiffRiemannianBundle I 1 F V]

theorem IsMetricCompatible.alternating_mvfderiv_inner
    {cov : CovariantDerivative I F V} (hcov : cov.IsMetricCompatible) (k : ℕ)
    {a b : ∀ x, V x [⋀^Fin k]→L[ℝ] ℝ} {x : M}
    (ha : MDifferentiableAt I (I.prod 𝓘(ℝ, F [⋀^Fin k]→L[ℝ] ℝ))
      (fun y => (⟨y, a y⟩ : TotalSpace (F [⋀^Fin k]→L[ℝ] ℝ)
        (Bundle.continuousAlternatingMap ℝ (Fin k) F V ℝ (Bundle.Trivial M ℝ)))) x)
    (hb : MDifferentiableAt I (I.prod 𝓘(ℝ, F [⋀^Fin k]→L[ℝ] ℝ))
      (fun y => (⟨y, b y⟩ : TotalSpace (F [⋀^Fin k]→L[ℝ] ℝ)
        (Bundle.continuousAlternatingMap ℝ (Fin k) F V ℝ (Bundle.Trivial M ℝ)))) x)
    (X : TangentSpace I x) :
    mfderiv I 𝓘(ℝ, ℝ)
        (fun y => (alternatingRiemannianMetric (F := F) V k).inner y (a y) (b y)) x X =
      (alternatingRiemannianMetric (F := F) V k).inner x (alternating cov k a x X) (b x) +
      (alternatingRiemannianMetric (F := F) V k).inner x (a x) (alternating cov k b x X) := by
  simp only [alternatingRiemannianMetric_inner, alternating_toMultilinear cov k ha X,
    alternating_toMultilinear cov k hb X]
  exact hcov.multilinear_mvfderiv_inner k ha.alternating_bundle_toMultilinear
    hb.alternating_bundle_toMultilinear X

theorem IsMetricCompatible.alternating {cov : CovariantDerivative I F V}
    (hcov : cov.IsMetricCompatible) (k : ℕ) :
    letI : RiemannianBundle
        (Bundle.continuousAlternatingMap ℝ (Fin k) F V ℝ (Bundle.Trivial M ℝ)) :=
      ⟨(alternatingContMDiffRiemannianMetric (IB := I) (n := 1) (F := F) V k).toRiemannianMetric⟩
    let alternatingNorm : ∀ x, NormedAddCommGroup (V x [⋀^Fin k]→L[ℝ] ℝ) :=
      fun x => Bundle.instNormedAddCommGroupOfRiemannianBundleOfIsTopologicalAddGroupOfContinuousConstSMulReal
        (E := Bundle.continuousAlternatingMap ℝ (Fin k) F V ℝ (Bundle.Trivial M ℝ)) x
    let _ : ∀ x, SeminormedAddCommGroup (V x [⋀^Fin k]→L[ℝ] ℝ) :=
      fun x => (alternatingNorm x).toSeminormedAddCommGroup
    let _ : ∀ x, InnerProductSpace ℝ (V x [⋀^Fin k]→L[ℝ] ℝ) :=
      fun x => Bundle.instInnerProductSpaceReal
        (E := Bundle.continuousAlternatingMap ℝ (Fin k) F V ℝ (Bundle.Trivial M ℝ)) x
    let _ : IsContMDiffRiemannianBundle I 1 (F [⋀^Fin k]→L[ℝ] ℝ)
        (Bundle.continuousAlternatingMap ℝ (Fin k) F V ℝ (Bundle.Trivial M ℝ)) :=
      ⟨(alternatingRiemannianMetric (F := F) V k).inner,
        contMDiff_alternatingRiemannianMetric_inner (IB := I) (n := 1) V k,
        fun _ _ _ => rfl⟩
    let _ : FiniteDimensional ℝ (F [⋀^Fin k]→L[ℝ] ℝ) :=
      (ContinuousAlternatingMap.elementaryCovectorBasis (k := k)
        (Module.finBasis ℝ F)).finiteDimensional_of_finite
    (alternating cov k).IsMetricCompatible := by
  let _ : FiniteDimensional ℝ (F [⋀^Fin k]→L[ℝ] ℝ) :=
    (ContinuousAlternatingMap.elementaryCovectorBasis (k := k)
      (Module.finBasis ℝ F)).finiteDimensional_of_finite
  let _ : RiemannianBundle
      (Bundle.continuousAlternatingMap ℝ (Fin k) F V ℝ (Bundle.Trivial M ℝ)) :=
    ⟨(alternatingContMDiffRiemannianMetric (IB := I) (n := 1) (F := F) V k).toRiemannianMetric⟩
  let alternatingNorm : ∀ x, NormedAddCommGroup (V x [⋀^Fin k]→L[ℝ] ℝ) :=
    fun x => Bundle.instNormedAddCommGroupOfRiemannianBundleOfIsTopologicalAddGroupOfContinuousConstSMulReal
      (E := Bundle.continuousAlternatingMap ℝ (Fin k) F V ℝ (Bundle.Trivial M ℝ)) x
  let _ : ∀ x, SeminormedAddCommGroup (V x [⋀^Fin k]→L[ℝ] ℝ) :=
    fun x => (alternatingNorm x).toSeminormedAddCommGroup
  let _ : ∀ x, InnerProductSpace ℝ (V x [⋀^Fin k]→L[ℝ] ℝ) :=
    fun x => Bundle.instInnerProductSpaceReal
      (E := Bundle.continuousAlternatingMap ℝ (Fin k) F V ℝ (Bundle.Trivial M ℝ)) x
  dsimp only
  apply (isMetricCompatible_iff _).mpr
  intro x X a b _ ha hb
  exact hcov.alternating_mvfderiv_inner k ha hb (X x)

end CovariantDerivative
