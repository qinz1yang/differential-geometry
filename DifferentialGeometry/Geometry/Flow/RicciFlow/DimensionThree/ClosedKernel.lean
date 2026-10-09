import DifferentialGeometry.Geometry.Flow.RicciFlow.DimensionThree.ClosedRank
import DifferentialGeometry.Geometry.Flow.RicciFlow.Estimates.Uhlenbeck.TerminalKernel
import DifferentialGeometry.Geometry.Connection.ParallelTransport.SubbundleInvariance
import DifferentialGeometry.Geometry.Connection.ParallelTransport.Kernel
import DifferentialGeometry.Geometry.Connection.MetricCompatibility.ExteriorSubmodule
import DifferentialGeometry.Geometry.Connection.LeviCivita.Pullback
import DifferentialGeometry.Geometry.Curvature.DimensionThree.ExteriorKernel
import DifferentialGeometry.Geometry.Curvature.CurvatureOperator.Smoothness
import DifferentialGeometry.Bundle.SmoothSubbundle.Kernel
import DifferentialGeometry.Geometry.Metric.BundlePullbackSmooth
import DifferentialGeometry.Geometry.Connection.ModelNorm

noncomputable section

open Bundle
open DifferentialGeometry.Geometry.Connection
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Tensor0SBundle (MetricFiberData)
open scoped Manifold ContDiff RealInnerProductSpace

namespace DifferentialGeometry.PDE.RicciFlow

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M] [SigmaCompactSpace M]
  {F : Type*} [oldNorm : NormedAddCommGroup F] [oldSpace : NormedSpace ℝ F]
  [FiniteDimensional ℝ F]
  {V : M → Type*} [TopologicalSpace (TotalSpace F V)]
  [∀ x, NormedAddCommGroup (V x)] [∀ x, NormedSpace ℝ (V x)]
  [FiberBundle F V] [VectorBundle ℝ F V] [ContMDiffVectorBundle ∞ F V I]

private theorem curvature_kernel_covariantly_invariant_metric_at_right_endpoint
    {D : RealTimeInterval} (S : SolutionOn (I := I) (M := M) D) (hS : IsSolutionOn S)
    (hdim : Module.finrank ℝ F = 3)
    {a b : ℝ} (hab : a < b) (hslab : Set.Icc a b ⊆ D.carrier)
    (hreg : Set.Ioo a b ⊆ D.regular)
    (h : ContMDiffRiemannianMetric I ∞ F V)
    (ι₀ : ∀ x, V x ≃L[ℝ] TangentSpace I x)
    (hι₀ : ContMDiff I (I.prod 𝓘(ℝ, F →L[ℝ] E)) ∞
      (fun x => TotalSpace.mk' (F →L[ℝ] E) x (ι₀ x).toContinuousLinearMap))
    (h₀ : ∀ x v w, (S.family.metric b).inner x (ι₀ x v) (ι₀ x w) = h.inner x v w)
    (hR : ∀ t ∈ Set.Icc a b, ∀ x,
      (⟨metricRm04At (S.family.metric t) x,
        metricRm04At_mem_algebraicCurvatureTensorSubmodule (S.family.metric t) x⟩ :
          algebraicCurvatureTensorSubmodule (I := I) (M := M) x) ∈
            algebraicCurvatureOperatorNonnegativeCone (I := I) (M := M)) :
      IsCovariantlyInvariantSubmoduleFamily
        (CovariantDerivative.alternating (LeviCivita (S.family.metric b)) 2)
        (fun x => curvatureOperatorKernelAt (S.family.metric b) x
          ⟨metricRm04At (S.family.metric b) x,
            metricRm04At_mem_algebraicCurvatureTensorSubmodule (S.family.metric b) x⟩) := by
  let : ∀ x, FiniteDimensional ℝ (V x) := fun x => VectorBundle.finiteDimensional ℝ F V x
  let : RiemannianBundle V := ⟨h.toRiemannianMetric⟩
  let sourceNorm : ∀ y, NormedAddCommGroup (V y) := fun y =>
    Bundle.instNormedAddCommGroupOfRiemannianBundleOfIsTopologicalAddGroupOfContinuousConstSMulReal y
  let : ∀ y, NormedAddCommGroup (V y) := sourceNorm
  let : ∀ y, SeminormedAddCommGroup (V y) := fun y => (sourceNorm y).toSeminormedAddCommGroup
  let : ∀ y, InnerProductSpace ℝ (V y) := fun y => Bundle.instInnerProductSpaceReal y
  let : IsContMDiffRiemannianBundle I ∞ F V := ⟨h.inner, h.contMDiff, fun _ _ _ => rfl⟩
  let m := MetricFiberData.ofFiniteDimensional F
  have hιwithin := fun y =>
    (contMDiffWithinAt_hom_totalSpace_domain_model_metric_iff
      (IA := I) (IB := I) (F := E) (V := TangentSpace I) (W := V) m
      (n := ∞) (f := fun z => TotalSpace.mk' (F →L[ℝ] E) z (ι₀ z).toContinuousLinearMap)
      (s := Set.univ) (x := y)).mpr ((hι₀ y).contMDiffWithinAt (s := Set.univ))
  let vb := vector_bundle_model_metric (V := V) m
  let svb := contMDiffVectorBundle_model_metric (IB := I) (V := V) (n := ∞) m
  let rm := isContMDiffRiemannianBundle_model_metric (IB := I) (V := V) (n := ∞) m
  let : NormedAddCommGroup F := m.toNormedAddCommGroupOfTopology
  let : InnerProductSpace ℝ F := @MetricFiberData.toInnerProductSpaceOfTopology F oldNorm.toAddCommGroup oldSpace.toModule
      _ _ (by let : SeminormedAddCommGroup F := oldNorm.toSeminormedAddCommGroup
              let : NormedSpace ℝ F := oldSpace
              infer_instance) _ _ m
  let : VectorBundle ℝ F V := vb
  let : ContMDiffVectorBundle ∞ F V I := svb
  let : IsContMDiffRiemannianBundle I ∞ F V := rm
  have hιnew : ContMDiff I (I.prod 𝓘(ℝ, F →L[ℝ] E)) ∞
      (fun y => TotalSpace.mk' (F →L[ℝ] E) y (ι₀ y).toContinuousLinearMap) :=
    fun y => contMDiffWithinAt_univ.mp (hιwithin y)
  have hK := curvatureOperator_kernel_isCovariantlyInvariant_terminal_of_solution
    (F := F) (V := V) S hS hab hslab hreg hdim hR ι₀ hιnew h₀
  have hD := CovariantDerivative.isMetricCompatible_pullback_leviCivita
    (S.family.metric b) ι₀ (hιnew.of_le (show (1 : ℕ∞ω) ≤ ∞ by simp)) h₀
  have htransfer := isCovariantlyInvariantSubmoduleFamily_musical_pullback
    (LeviCivita (S.family.metric b)) ι₀ hιnew 2 _ hD hK
  convert htransfer using 1
  funext x
  exact (map_traceNormalizedCurvatureEndomorphism_ker
    ((VectorBundle.finrank_eq ℝ F V x).trans hdim) (S.family.metric b) x
    ⟨metricRm04At (S.family.metric b) x,
      metricRm04At_mem_algebraicCurvatureTensorSubmodule (S.family.metric b) x⟩
    (ι₀ x) (h₀ x)).symm

theorem curvatureOperatorKernelAt_covariantly_invariant_at_right_endpoint
    {D : RealTimeInterval} (S : SolutionOn (I := I) (M := M) D) (hS : IsSolutionOn S)
    (hdim : Module.finrank ℝ E = 3)
    {a b : ℝ} (hab : a < b) (hslab : Set.Icc a b ⊆ D.carrier)
    (hreg : Set.Ioo a b ⊆ D.regular)
    (hR : ∀ r ∈ Set.Icc a b, ∀ x,
      metricAlgebraicCurvatureTensorAt (S.family.metric r) x ∈
        algebraicCurvatureOperatorNonnegativeCone (I := I) (M := M)) :
    IsCovariantlyInvariantSubmoduleFamily
      (CovariantDerivative.alternating (LeviCivita (S.family.metric b)) 2)
      (fun x => curvatureOperatorKernelAt (S.family.metric b) x
        (metricAlgebraicCurvatureTensorAt (S.family.metric b) x)) := by
  exact curvature_kernel_covariantly_invariant_metric_at_right_endpoint
    (F := E) (V := TangentSpace I) S hS hdim hab hslab hreg (S.family.metric b)
    (fun x => ContinuousLinearEquiv.refl ℝ (TangentSpace I x))
    (show ContMDiff I (I.prod 𝓘(ℝ, E →L[ℝ] E)) ∞
      (fun x : M => TotalSpace.mk' (E →L[ℝ] E) x
        (ContinuousLinearMap.id ℝ (TangentSpace I x))) from
      (contMDiff_id : ContMDiff I I ∞ (fun x : M => x)).clm_bundle_id)
    (fun _ _ _ => rfl) hR

theorem exists_covariantly_invariant_curvatureOperatorKernelSubbundle_at_right_endpoint
    [ConnectedSpace M]
    {D : RealTimeInterval} (S : SolutionOn (I := I) (M := M) D) (hS : IsSolutionOn S)
    (hdim : Module.finrank ℝ E = 3)
    {a t : ℝ} (hat : a < t) (hslab : Set.Icc a t ⊆ D.carrier)
    (hreg : Set.Ioo a t ⊆ D.regular)
    (hR : ∀ r ∈ Set.Icc a t, ∀ x,
      (⟨metricRm04At (S.family.metric r) x,
        metricRm04At_mem_algebraicCurvatureTensorSubmodule (S.family.metric r) x⟩ :
          algebraicCurvatureTensorSubmodule (I := I) (M := M) x) ∈
            algebraicCurvatureOperatorNonnegativeCone (I := I) (M := M)) :
    ∃ K : ContMDiffVectorSubbundle (I := I) (F := E [⋀^Fin 2]→L[ℝ] ℝ)
        (V := fun x : M => TangentSpace I x [⋀^Fin 2]→L[ℝ] ℝ) (n := ∞),
      (∀ x, K.fiber x = curvatureOperatorKernelAt (S.family.metric t) x
        ⟨metricRm04At (S.family.metric t) x,
          metricRm04At_mem_algebraicCurvatureTensorSubmodule (S.family.metric t) x⟩) ∧
      IsCovariantlyInvariantSubmoduleFamily
        (CovariantDerivative.alternating (LeviCivita (S.family.metric t)) 2) K.fiber := by
  let g := S.family.metric t
  let A := curvatureOperatorEndomorphismField g (metricRm04 g)
    (fun x => metricRm04At_mem_algebraicCurvatureTensorSubmodule g x)
  let : FiniteDimensional ℝ (E [⋀^Fin 2]→L[ℝ] ℝ) :=
    (ContinuousAlternatingMap.elementaryCovectorBasis (k := 2) (Module.finBasis ℝ E)).finiteDimensional_of_finite
  let : ∀ x : M, FiniteDimensional ℝ (TangentSpace I x [⋀^Fin 2]→L[ℝ] ℝ) := fun x =>
    (ContinuousAlternatingMap.elementaryCovectorBasis (k := 2)
      (Module.finBasis ℝ (TangentSpace I x))).finiteDimensional_of_finite
  let x₀ : M := Classical.choice (inferInstance : Nonempty M)
  have hdim₂ (x : M) : Module.finrank ℝ (TangentSpace I x [⋀^Fin 2]→L[ℝ] ℝ) = 3 := by
    rw [ContinuousAlternatingMap.finrank_continuousAlternatingMap]
    change (Module.finrank ℝ E).choose 2 = 3
    rw [hdim]
    norm_num
  have hker : ∀ x, Module.finrank ℝ (A x).ker = Module.finrank ℝ (A x₀).ker := by
    intro x
    have hx := (A x).toLinearMap.finrank_range_add_finrank_ker
    have h₀ := (A x₀).toLinearMap.finrank_range_add_finrank_ker
    rw [hdim₂ x] at hx
    rw [hdim₂ x₀] at h₀
    have hr : Module.finrank ℝ (A x).range = Module.finrank ℝ (A x₀).range :=
      curvatureOperatorImageAt_finrank_eq_at_right_endpoint S hS hdim hat hslab hreg hR x x₀
    omega
  obtain ⟨K, -, hK⟩ := ContMDiffVectorSubbundle.exists_smooth_kernel A
    (curvatureOperatorEndomorphismField_contMDiff g (metricRm04 g)
      (fun x => metricRm04At_mem_algebraicCurvatureTensorSubmodule g x))
    (Module.finrank ℝ (A x₀).ker) hker
  have hKeq (x : M) : K.fiber x = curvatureOperatorKernelAt g x
      ⟨metricRm04At g x, metricRm04At_mem_algebraicCurvatureTensorSubmodule g x⟩ :=
    (hK x).trans (curvatureOperatorEndomorphismAt_ker g x _)
  refine ⟨K, hKeq, ?_⟩
  have hinv := curvatureOperatorKernelAt_covariantly_invariant_at_right_endpoint S hS hdim hat hslab hreg hR
  have hfun : K.fiber = fun x => curvatureOperatorKernelAt g x
      ⟨metricRm04At g x, metricRm04At_mem_algebraicCurvatureTensorSubmodule g x⟩ := funext hKeq
  rw [hfun]
  exact hinv

private instance twoFormModelFiniteDimensional : FiniteDimensional ℝ (E [⋀^Fin 2]→L[ℝ] ℝ) :=
  (ContinuousAlternatingMap.elementaryCovectorBasis (k := 2) (Module.finBasis ℝ E)).finiteDimensional_of_finite

theorem curvatureOperatorKernelAt_parallel_at_right_endpoint
    [ConnectedSpace M]
    {D : RealTimeInterval} (S : SolutionOn (I := I) (M := M) D) (hS : IsSolutionOn S)
    (hdim : Module.finrank ℝ E = 3)
    {a t : ℝ} (hat : a < t) (hslab : Set.Icc a t ⊆ D.carrier)
    (hreg : Set.Ioo a t ⊆ D.regular)
    (hR : ∀ r ∈ Set.Icc a t, ∀ x,
      (⟨metricRm04At (S.family.metric r) x,
        metricRm04At_mem_algebraicCurvatureTensorSubmodule (S.family.metric r) x⟩ :
          algebraicCurvatureTensorSubmodule (I := I) (M := M) x) ∈
            algebraicCurvatureOperatorNonnegativeCone (I := I) (M := M)) :
    IsParallelContinuousAlternatingSubmoduleFamily (S.family.metric t)
      (fun x => curvatureOperatorKernelAt (S.family.metric t) x
        ⟨metricRm04At (S.family.metric t) x,
          metricRm04At_mem_algebraicCurvatureTensorSubmodule (S.family.metric t) x⟩) := by
  obtain ⟨K, hK, hcov⟩ := exists_covariantly_invariant_curvatureOperatorKernelSubbundle_at_right_endpoint
    S hS hdim hat hslab hreg hR
  have h := K.isParallelContinuousAlternatingSubmoduleFamily_of_covariantly_invariant
    (S.family.metric t) hcov
  have heq : K.fiber = fun x => curvatureOperatorKernelAt (S.family.metric t) x
      ⟨metricRm04At (S.family.metric t) x,
        metricRm04At_mem_algebraicCurvatureTensorSubmodule (S.family.metric t) x⟩ := funext hK
  rw [heq] at h
  exact h

end DifferentialGeometry.PDE.RicciFlow
