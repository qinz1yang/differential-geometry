import DifferentialGeometry.Geometry.Flow.RicciFlow.DimensionThree.ClosedRank
import DifferentialGeometry.Geometry.Flow.RicciFlow.Estimates.Uhlenbeck.TerminalSections
import DifferentialGeometry.Analysis.Parabolic.MaximumPrinciple.TerminalKernel
import DifferentialGeometry.Geometry.Curvature.DimensionThree.CurvatureOperatorRankRigidity

set_option autoImplicit false
noncomputable section
open Bundle CovariantDerivative
open scoped Manifold ContDiff RealInnerProductSpace
namespace DifferentialGeometry.PDE.RicciFlow
open DifferentialGeometry.Geometry.Connection DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Curvature.DimensionThree
open DifferentialGeometry.Tensor0SBundle (MetricFiberData)

section IsometricBundle

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M]
  [SigmaCompactSpace M] [ConnectedSpace M]
  {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]
  {V : M → Type*} [TopologicalSpace (TotalSpace F V)]
  [∀ x, NormedAddCommGroup (V x)] [∀ x, InnerProductSpace ℝ (V x)]
  [FiberBundle F V] [VectorBundle ℝ F V] [ContMDiffVectorBundle ∞ F V I]
  [IsContMDiffRiemannianBundle I ∞ F V]

private theorem curvature_rank_trichotomy_at_right_endpoint_isometric
    {D : RealTimeInterval} (S : SolutionOn (I := I) (M := M) D) (hS : IsSolutionOn S)
    {a b : ℝ} (hab : a < b) (hslab : Set.Icc a b ⊆ D.carrier)
    (hreg : Set.Ioo a b ⊆ D.regular) (hdim : Module.finrank ℝ F = 3)
    (hcone : ∀ t ∈ Set.Icc a b, ∀ x,
      metricAlgebraicCurvatureTensorAt (S.family.metric t) x ∈
        algebraicCurvatureOperatorNonnegativeCone (I := I) (M := M))
    (ι₀ : ∀ x, V x ≃L[ℝ] TangentSpace I x)
    (hι₀ : ContMDiff I (I.prod 𝓘(ℝ, F →L[ℝ] E)) ∞
      (fun x => TotalSpace.mk' (F →L[ℝ] E) x (ι₀ x).toContinuousLinearMap))
    (h₀ : ∀ x v w, (S.family.metric b).inner x (ι₀ x v) (ι₀ x w) = ⟪v, w⟫) :
    ∀ x, Module.finrank ℝ (curvatureOperatorImageAt (S.family.metric b) x
        (metricAlgebraicCurvatureTensorAt (S.family.metric b) x)) = 0 ∨
      Module.finrank ℝ (curvatureOperatorImageAt (S.family.metric b) x
        (metricAlgebraicCurvatureTensorAt (S.family.metric b) x)) = 1 ∨
      Module.finrank ℝ (curvatureOperatorImageAt (S.family.metric b) x
        (metricAlgebraicCurvatureTensorAt (S.family.metric b) x)) = 3 := by
  let _ : ∀ y, FiniteDimensional ℝ (V y) := fun y => VectorBundle.finiteDimensional ℝ F V y
  let _ := Bundle.ExteriorPower.totalSpaceTopology F V 2
  let _ := Bundle.ExteriorPower.fiberBundle F V 2
  let _ := Bundle.ExteriorPower.vector_bundle F V 2
  let _ := Bundle.ExteriorPower.contMDiffVectorBundle (IB := I) (n := ∞) F V 2
  let _ := Bundle.ExteriorPower.isContMDiffRiemannianBundle (IB := I) (n := ∞) F V 2
  let cov := CovariantDerivative.pullbackFiberwiseLinearEquiv
    (fun y => (ι₀ y).toLinearEquiv)
    (hι₀.of_le (show (1 : ℕ∞ω) ≤ ∞ by simp)).clm_bundle_map
    (LeviCivita (S.family.metric b))
  obtain ⟨ι, hinit, A, hA, hpos, hsmooth, hmetric, hevo⟩ :=
    exists_nonnegative_curvatureOperator_sections_terminal_evolution
      (F := F) (V := V) S hS hab hslab hreg hdim hcone ι₀ hι₀ h₀
  let _ : ContMDiffCovariantDerivative (cov.exteriorPower 2) ∞ := hsmooth
  let x₀ : M := Classical.choice (inferInstance : Nonempty M)
  have hdimE : Module.finrank ℝ E = 3 := by
    change Module.finrank ℝ (TangentSpace I x₀) = 3
    rw [← (ι₀ x₀).toLinearEquiv.finrank_eq, VectorBundle.finrank_eq ℝ F V x₀, hdim]
  have hdimExterior (x : M) : Module.finrank ℝ (⋀[ℝ]^2 (V x)) = 3 := by
    rw [exteriorPower.finrank_eq, VectorBundle.finrank_eq ℝ F V x, hdim]
    norm_num
  have hrank (x : M) : Module.finrank ℝ (A b x).range =
      Module.finrank ℝ (curvatureOperatorImageAt (S.family.metric b) x
        (metricAlgebraicCurvatureTensorAt (S.family.metric b) x)) := by
    rw [hA b x]
    exact traceNormalizedCurvatureEndomorphism_pullback_finrank_range
      ((VectorBundle.finrank_eq ℝ F V x).trans hdim) (S.family.metric b) x
      (metricAlgebraicCurvatureTensorAt (S.family.metric b) x) (ι b x)
      (fun v w => by rw [hinit x]; exact h₀ x v w)
  have hker : ∀ x, Module.finrank ℝ (A b x).ker = Module.finrank ℝ (A b x₀).ker := by
    intro x
    have hx := (A b x).toLinearMap.finrank_range_add_finrank_ker
    have hy := (A b x₀).toLinearMap.finrank_range_add_finrank_ker
    rw [hdimExterior x, hrank x] at hx
    rw [hdimExterior x₀, hrank x₀] at hy
    have heq := curvatureOperatorImageAt_finrank_eq_at_right_endpoint
      S hS hdimE hab hslab hreg hcone x x₀
    omega
  obtain ⟨K, _, _, _, _, hann⟩ := PositiveSystem.exists_parallel_kernel_at_right_endpoint_of_constant_rank
    (S.family.metric b) (cov.exteriorPower 2) hmetric A hab hpos
    (fun _ => 0)
    (fun x => (curvatureOperatorReactionEndomorphism3 (A b x).toLinearMap).toContinuousLinearMap)
    (fun x v _ => (curvatureOperatorReactionEndomorphism3_isPositive
      (hpos b ⟨hab.le, le_rfl⟩ x).toLinearMap).inner_nonneg_left v)
    (fun x => by simpa only [map_zero, add_zero] using hevo x)
    (Module.finrank ℝ (A b x₀).ker) hker
  intro x
  have hnull : ∀ v, (A b x).toLinearMap v = 0 →
      curvatureOperatorReactionEndomorphism3 (A b x).toLinearMap v = 0 := by
    intro v hv
    exact ((curvatureOperatorReactionEndomorphism3_isPositive
      (hpos b ⟨hab.le, le_rfl⟩ x).toLinearMap).inner_apply_self_eq_zero_iff v).mp (hann x v hv)
  have h := curvatureOperatorEndomorphism_finrank_range_trichotomy
    (hdimExterior x) (A b x).toLinearMap (hpos b ⟨hab.le, le_rfl⟩ x).toLinearMap hnull
  simpa only [← hrank x] using h

end IsometricBundle

section MetricBundle

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M] [SigmaCompactSpace M]
  {F : Type*} [oldNorm : NormedAddCommGroup F] [oldSpace : NormedSpace ℝ F]
  [FiniteDimensional ℝ F]
  {V : M → Type*} [TopologicalSpace (TotalSpace F V)]
  [∀ x, NormedAddCommGroup (V x)] [∀ x, NormedSpace ℝ (V x)]
  [FiberBundle F V] [VectorBundle ℝ F V] [ContMDiffVectorBundle ∞ F V I]

private theorem curvature_rank_trichotomy_metric_at_right_endpoint
    [ConnectedSpace M]
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
    ∀ x, Module.finrank ℝ (curvatureOperatorImageAt (S.family.metric b) x
        (metricAlgebraicCurvatureTensorAt (S.family.metric b) x)) = 0 ∨
      Module.finrank ℝ (curvatureOperatorImageAt (S.family.metric b) x
        (metricAlgebraicCurvatureTensorAt (S.family.metric b) x)) = 1 ∨
      Module.finrank ℝ (curvatureOperatorImageAt (S.family.metric b) x
        (metricAlgebraicCurvatureTensorAt (S.family.metric b) x)) = 3 := by
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
  exact curvature_rank_trichotomy_at_right_endpoint_isometric
    (F := F) (V := V) S hS hab hslab hreg hdim hR ι₀ hιnew h₀

end MetricBundle

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M] [SigmaCompactSpace M]
  [ConnectedSpace M]

theorem curvatureOperatorImageAt_finrank_trichotomy_at_right_endpoint
    {D : RealTimeInterval} (S : SolutionOn (I := I) (M := M) D) (hS : IsSolutionOn S)
    (hdim : Module.finrank ℝ E = 3)
    {a b : ℝ} (hab : a < b) (hslab : Set.Icc a b ⊆ D.carrier)
    (hreg : Set.Ioo a b ⊆ D.regular)
    (hR : ∀ r ∈ Set.Icc a b, ∀ x,
      metricAlgebraicCurvatureTensorAt (S.family.metric r) x ∈
        algebraicCurvatureOperatorNonnegativeCone (I := I) (M := M)) :
    (∀ x, Module.finrank ℝ (curvatureOperatorImageAt (S.family.metric b) x
        (metricAlgebraicCurvatureTensorAt (S.family.metric b) x)) = 0) ∨
      (∀ x, Module.finrank ℝ (curvatureOperatorImageAt (S.family.metric b) x
        (metricAlgebraicCurvatureTensorAt (S.family.metric b) x)) = 1) ∨
      (∀ x, Module.finrank ℝ (curvatureOperatorImageAt (S.family.metric b) x
        (metricAlgebraicCurvatureTensorAt (S.family.metric b) x)) = 3) := by
  have hpoint := curvature_rank_trichotomy_metric_at_right_endpoint
    (F := E) (V := TangentSpace I) S hS hdim hab hslab hreg (S.family.metric b)
    (fun x => ContinuousLinearEquiv.refl ℝ (TangentSpace I x))
    (show ContMDiff I (I.prod 𝓘(ℝ, E →L[ℝ] E)) ∞
      (fun x : M => TotalSpace.mk' (E →L[ℝ] E) x
        (ContinuousLinearMap.id ℝ (TangentSpace I x))) from
      (contMDiff_id : ContMDiff I I ∞ (fun x : M => x)).clm_bundle_id)
    (fun _ _ _ => rfl) hR
  let x₀ : M := Classical.choice (inferInstance : Nonempty M)
  have hr := curvatureOperatorImageAt_finrank_eq_at_right_endpoint S hS hdim hab hslab hreg hR
  rcases hpoint x₀ with h | h | h
  · exact Or.inl (fun x => (hr x x₀).trans h)
  · exact Or.inr (Or.inl (fun x => (hr x x₀).trans h))
  · exact Or.inr (Or.inr (fun x => (hr x x₀).trans h))

end DifferentialGeometry.PDE.RicciFlow
