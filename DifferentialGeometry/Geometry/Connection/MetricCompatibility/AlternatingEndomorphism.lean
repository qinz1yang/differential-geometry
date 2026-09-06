import DifferentialGeometry.Geometry.Connection.MetricCompatibility.Alternating

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

theorem IsMetricCompatible.alternating_endomorphism_self_adjoint
    {cov : CovariantDerivative I F V} (hcov : cov.IsMetricCompatible) (k : ℕ)
    (A : ContMDiffSection I ((F [⋀^Fin k]→L[ℝ] ℝ) →L[ℝ] F [⋀^Fin k]→L[ℝ] ℝ) ∞
      (fun x => (V x [⋀^Fin k]→L[ℝ] ℝ) →L[ℝ] V x [⋀^Fin k]→L[ℝ] ℝ))
    (hA : ∀ y a b, (alternatingRiemannianMetric (F := F) V k).inner y (A y a) b =
      (alternatingRiemannianMetric (F := F) V k).inner y a (A y b))
    (x : M) (X : TangentSpace I x) (a b : V x [⋀^Fin k]→L[ℝ] ℝ) :
    let _ : FiniteDimensional ℝ (F [⋀^Fin k]→L[ℝ] ℝ) :=
      (ContinuousAlternatingMap.elementaryCovectorBasis (k := k)
        (Module.finBasis ℝ F)).finiteDimensional_of_finite
    let D := DifferentialGeometry.HomConnectionGen.homBundleCovariantDerivativeGen I M
      (F [⋀^Fin k]→L[ℝ] ℝ)
      (Bundle.continuousAlternatingMap ℝ (Fin k) F V ℝ (Bundle.Trivial M ℝ))
      (F [⋀^Fin k]→L[ℝ] ℝ)
      (Bundle.continuousAlternatingMap ℝ (Fin k) F V ℝ (Bundle.Trivial M ℝ))
      (CovariantDerivative.alternating cov k) (CovariantDerivative.alternating cov k)
    (alternatingRiemannianMetric (F := F) V k).inner x (D A x X a) b =
      (alternatingRiemannianMetric (F := F) V k).inner x a (D A x X b) := by
  let _ : FiniteDimensional ℝ (F [⋀^Fin k]→L[ℝ] ℝ) :=
    (ContinuousAlternatingMap.elementaryCovectorBasis (k := k)
      (Module.finBasis ℝ F)).finiteDimensional_of_finite
  let _ : RiemannianBundle
      (Bundle.continuousAlternatingMap ℝ (Fin k) F V ℝ (Bundle.Trivial M ℝ)) :=
    ⟨(alternatingContMDiffRiemannianMetric (IB := I) (n := 1) (F := F) V k).toRiemannianMetric⟩
  let alternatingNorm : ∀ y, NormedAddCommGroup (V y [⋀^Fin k]→L[ℝ] ℝ) :=
    fun y => Bundle.instNormedAddCommGroupOfRiemannianBundleOfIsTopologicalAddGroupOfContinuousConstSMulReal
      (E := Bundle.continuousAlternatingMap ℝ (Fin k) F V ℝ (Bundle.Trivial M ℝ)) y
  let _ : ∀ y, SeminormedAddCommGroup (V y [⋀^Fin k]→L[ℝ] ℝ) :=
    fun y => (alternatingNorm y).toSeminormedAddCommGroup
  let _ : ∀ y, InnerProductSpace ℝ (V y [⋀^Fin k]→L[ℝ] ℝ) :=
    fun y => Bundle.instInnerProductSpaceReal
      (E := Bundle.continuousAlternatingMap ℝ (Fin k) F V ℝ (Bundle.Trivial M ℝ)) y
  let _ : IsContMDiffRiemannianBundle I 1 (F [⋀^Fin k]→L[ℝ] ℝ)
      (Bundle.continuousAlternatingMap ℝ (Fin k) F V ℝ (Bundle.Trivial M ℝ)) :=
    ⟨(alternatingRiemannianMetric (F := F) V k).inner,
      contMDiff_alternatingRiemannianMetric_inner (IB := I) (n := 1) V k,
      fun _ _ _ => rfl⟩
  have hcov' : (CovariantDerivative.alternating cov k).IsMetricCompatible := hcov.alternating k
  have hA' : ∀ y, (A y : (V y [⋀^Fin k]→L[ℝ] ℝ) →ₗ[ℝ]
      V y [⋀^Fin k]→L[ℝ] ℝ).IsSymmetric := hA
  exact DifferentialGeometry.HomConnectionGen.homBundleCovariantDerivativeGen_isSymmetric
    (CovariantDerivative.alternating cov k) hcov' A hA' x X a b

end CovariantDerivative
