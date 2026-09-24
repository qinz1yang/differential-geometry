import DifferentialGeometry.Geometry.Curvature.DimensionThree.ExteriorKyFan
import DifferentialGeometry.Geometry.Curvature.CurvatureOperator.ExteriorPositivity
import DifferentialGeometry.Geometry.Curvature.DimensionThree.CurvatureReactionPositivity
import DifferentialGeometry.Geometry.Flow.RicciFlow.Estimates.Uhlenbeck.CurvatureOperatorSectionEvolution
import DifferentialGeometry.Analysis.Parabolic.MaximumPrinciple.KyFanSupport
import DifferentialGeometry.Geometry.Metric.BundlePullbackSmooth
import DifferentialGeometry.Geometry.Connection.ModelNorm

noncomputable section

namespace DifferentialGeometry.Analysis.Parabolic

open Bundle CovariantDerivative
open DifferentialGeometry.Geometry.Connection
open DifferentialGeometry.Geometry.Curvature
open scoped Manifold ContDiff

private theorem upperSupport_of_hasDerivAt
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M]
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
    {V : M → Type*} [TopologicalSpace (TotalSpace F V)]
    [∀ y, NormedAddCommGroup (V y)] [∀ y, InnerProductSpace ℝ (V y)]
    [FiberBundle F V] [VectorBundle ℝ F V] [ContMDiffVectorBundle ∞ F V I]
    [IsContMDiffRiemannianBundle I ∞ F V]
    (G : MetricConnectionFamily (I := I) (M := M) ℝ)
    (cov : CovariantDerivative I F V)
    [ContMDiffCovariantDerivative cov ∞] (hcov : cov.IsMetricCompatible)
    {T t : ℝ} (hT : 0 < T) (ht : t ∈ Set.Icc 0 T)
    (A : ℝ → Cₛ^∞⟮I; F →L[ℝ] F, (fun y : M => V y →L[ℝ] V y)⟯)
    (hsym : ∀ s y, (A s y).toLinearMap.IsSymmetric)
    {k : ℕ} (hk : k ≤ Module.finrank ℝ F) (x : M) (hx : I.IsInteriorPoint x)
    (reaction : V x →L[ℝ] V x) (hr : reaction.IsPositive)
    (hconn : G.connection t = LeviCivita (G.metric t))
    (hevol : HasDerivAt (fun s => A s x)
      (rawBundleEndomorphismConnLap (G.metric t) cov (fun y => A t y) x + reaction) t) :
    let _ : ∀ y, FiniteDimensional ℝ (V y) :=
      fun y => VectorBundle.finiteDimensional ℝ F V y
    Nonempty (ParabolicUpperSupportAt G T (fun _ _ => 0)
      (fun s y => (hsym s y).lowerKyFanSum k) t x) := by
  exact nonempty_parabolicUpperSupportAt_lowerKyFanSum_of_evolution
    G cov hcov hT ht A hsym hk x hx (fun _ _ => 0) reaction hr hconn
    hevol.differentiableAt (by simpa only [map_zero, add_zero] using hevol.deriv)

end DifferentialGeometry.Analysis.Parabolic

namespace DifferentialGeometry.PDE.RicciFlow

open Bundle CovariantDerivative Filter Set
open DifferentialGeometry.Analysis.Parabolic
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Curvature.DimensionThree
open DifferentialGeometry.Tensor0SBundle (MetricFiberData)
open scoped Manifold ContDiff Topology RealInnerProductSpace

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M]

private theorem curvature_upperSupport_of_sections
    {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]
    {V : M → Type*} [TopologicalSpace (TotalSpace F V)]
    [∀ y, NormedAddCommGroup (V y)] [∀ y, InnerProductSpace ℝ (V y)]
    [FiberBundle F V] [VectorBundle ℝ F V]
    [∀ y, FiniteDimensional ℝ (V y)]
    [TopologicalSpace (TotalSpace (⋀[ℝ]^2 F) (fun y => ⋀[ℝ]^2 (V y)))]
    [FiberBundle (⋀[ℝ]^2 F) (fun y => ⋀[ℝ]^2 (V y))]
    [VectorBundle ℝ (⋀[ℝ]^2 F) (fun y => ⋀[ℝ]^2 (V y))]
    [ContMDiffVectorBundle ∞ (⋀[ℝ]^2 F) (fun y => ⋀[ℝ]^2 (V y)) I]
    [IsContMDiffRiemannianBundle I ∞ (⋀[ℝ]^2 F) (fun y => ⋀[ℝ]^2 (V y))]
    {D : RealTimeInterval} (S : SolutionOn (I := I) (M := M) D)
    {J : Set ℝ} (hJ : IsOpen J)
    (hdim : Module.finrank ℝ F = 3) {T t : ℝ} (hT : 0 < T)
    (ht : t ∈ Icc 0 T) (htJ : t ∈ J)
    (ι : ℝ → ∀ y, V y ≃L[ℝ] TangentSpace I y)
    (hm : ∀ s ∈ J, ∀ y v w, (S.family.metric s).inner y (ι s y v) (ι s y w) = ⟪v, w⟫)
    (A : ℝ → Cₛ^∞⟮I; (⋀[ℝ]^2 F) →L[ℝ] ⋀[ℝ]^2 F,
      (fun y : M => (⋀[ℝ]^2 (V y)) →L[ℝ] ⋀[ℝ]^2 (V y))⟯)
    (hA : ∀ s ∈ J, ∀ y, A s y =
      exteriorPower.traceNormalizedCurvatureEndomorphism
        ((S.base.rm04 s y).compContinuousLinearMap (fun _ => (ι s y).toContinuousLinearMap))
        ((mem_algebraicCurvatureTensorSubmodule.mp
          (metricRm04At_mem_algebraicCurvatureTensorSubmodule
            (S.base.metric s) y)).compContinuousLinearMap
            (ι s y).toContinuousLinearMap))
    (hAsym : ∀ s y, (A s y).toLinearMap.IsSymmetric)
    (cov : CovariantDerivative I (⋀[ℝ]^2 F) (fun y => ⋀[ℝ]^2 (V y)))
    [ContMDiffCovariantDerivative cov ∞] (hcovmetric : cov.IsMetricCompatible)
    (x : M)
    (hdiff : HasDerivWithinAt (fun s => A s x)
      (DifferentialGeometry.Geometry.Connection.rawBundleEndomorphismConnLap
        (S.family.metric t) cov (fun y => A t y) x +
          (curvatureOperatorReactionEndomorphism3 (A t x).toLinearMap).toContinuousLinearMap) J t)
    (hR : (⟨metricRm04At (S.family.metric t) x,
      metricRm04At_mem_algebraicCurvatureTensorSubmodule (S.family.metric t) x⟩ :
        algebraicCurvatureTensorSubmodule (I := I) (M := M) x) ∈
          algebraicCurvatureOperatorNonnegativeCone (I := I) (M := M)) :
    Nonempty (ParabolicUpperSupportAt (flowG S) T (fun _ _ => 0)
      (fun s y => 2 * leastCurvatureOperatorEigenvalueAt (S.base.metric s) y
        ⟨S.base.rm04 s y,
          metricRm04At_mem_algebraicCurvatureTensorSubmodule (S.base.metric s) y⟩) t x) := by
  have hAtpos : (A t x).IsPositive := by
    rw [hA t htJ x]
    exact traceNormalizedCurvatureEndomorphism_pullback_isPositive_of_mem_nonnegativeCone
      ⟨metricRm04At (S.family.metric t) x,
        metricRm04At_mem_algebraicCurvatureTensorSubmodule (S.family.metric t) x⟩
      hR (ι t x).toContinuousLinearMap
  have hreact : (curvatureOperatorReactionEndomorphism3
      (A t x).toLinearMap).toContinuousLinearMap.IsPositive :=
    (ContinuousLinearMap.isPositive_toLinearMap_iff _).mp
      (curvatureOperatorReactionEndomorphism3_isPositive hAtpos.toLinearMap)
  have hdim₂ : 1 ≤ Module.finrank ℝ (⋀[ℝ]^2 F) := by
    rw [exteriorPower.finrank_eq, hdim]
    norm_num
  obtain ⟨U⟩ := upperSupport_of_hasDerivAt
    (I := I) (F := ⋀[ℝ]^2 F) (V := fun y => ⋀[ℝ]^2 (V y)) (k := 1)
    (flowG S) cov hcovmetric hT ht A hAsym hdim₂ x
    BoundarylessManifold.isInteriorPoint
    (curvatureOperatorReactionEndomorphism3 (A t x).toLinearMap).toContinuousLinearMap
    hreact rfl (hdiff.hasDerivAt (hJ.mem_nhds htJ))
  have heq (s : ℝ) (hs : s ∈ J) (y : M) :
      (hAsym s y).lowerKyFanSum 1 =
        2 * leastCurvatureOperatorEigenvalueAt (S.base.metric s) y
          ⟨S.base.rm04 s y,
            metricRm04At_mem_algebraicCurvatureTensorSubmodule (S.base.metric s) y⟩ := by
    simpa only [← hA s hs y] using
      traceNormalizedCurvatureEndomorphism_pullback_lowerKyFanSum_one
      ((VectorBundle.finrank_eq ℝ F V y).trans hdim) (S.base.metric s) y
      ⟨S.base.rm04 s y,
        metricRm04At_mem_algebraicCurvatureTensorSubmodule (S.base.metric s) y⟩
      (ι s y) (hm s hs y)
  refine ⟨{ U with eq_at := U.eq_at.trans (heq t htJ x), upper_nhds := ?_ }⟩
  have hlocal : ∀ᶠ p : ℝ × M in 𝓝 (t, x), p.1 ∈ J :=
    continuousAt_fst.eventually (hJ.mem_nhds htJ)
  filter_upwards [U.upper_nhds, hlocal.filter_mono inf_le_left] with p hp hpJ
  rw [← heq p.1 hpJ p.2]
  exact hp

private theorem curvature_upperSupport_of_uhlenbeck_isometry
    {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]
    {V : M → Type*} [TopologicalSpace (TotalSpace F V)]
    [∀ y, NormedAddCommGroup (V y)] [∀ y, InnerProductSpace ℝ (V y)]
    [FiberBundle F V] [VectorBundle ℝ F V] [ContMDiffVectorBundle ∞ F V I]
    [IsContMDiffRiemannianBundle I ∞ F V]
    {D : RealTimeInterval} (S : SolutionOn (I := I) (M := M) D) (hS : IsSolutionOn S)
    {J : Set ℝ} (hJ : IsOpen J) (hJD : J ⊆ D.regular)
    (hdim : Module.finrank ℝ F = 3) {T t : ℝ} (hT : 0 < T)
    (ht : t ∈ Icc 0 T) (htJ : t ∈ J)
    (ι : ℝ → ∀ y, V y ≃L[ℝ] TangentSpace I y)
    (hι : ContMDiffOn (𝓘(ℝ, ℝ).prod I) (I.prod 𝓘(ℝ, F →L[ℝ] E)) ∞
      (fun p : ℝ × M => TotalSpace.mk' (F →L[ℝ] E) p.2
        (E := fun y => V y →L[ℝ] TangentSpace I y)
        (ι p.1 p.2).toContinuousLinearMap) (J ×ˢ (univ : Set M)))
    (hm : ∀ s ∈ J, ∀ y v w, (S.family.metric s).inner y (ι s y v) (ι s y w) = ⟪v, w⟫)
    (hode : ∀ y v, ∀ s ∈ J, HasDerivWithinAt (fun r => ι r y v)
      (ricciSharp (I := I) (S.family.metric s) y (ι s y v)) J s)
    (x : M)
    (hR : (⟨metricRm04At (S.family.metric t) x,
      metricRm04At_mem_algebraicCurvatureTensorSubmodule (S.family.metric t) x⟩ :
        algebraicCurvatureTensorSubmodule (I := I) (M := M) x) ∈
          algebraicCurvatureOperatorNonnegativeCone (I := I) (M := M)) :
    Nonempty (ParabolicUpperSupportAt (flowG S) T (fun _ _ => 0)
      (fun s y => 2 * leastCurvatureOperatorEigenvalueAt (S.base.metric s) y
        ⟨S.base.rm04 s y,
          metricRm04At_mem_algebraicCurvatureTensorSubmodule (S.base.metric s) y⟩) t x) := by
  let _ : ∀ y, NormedSpace ℝ (V y) := fun y => inferInstance
  let _ : ∀ y, Module ℝ (V y) := fun y => inferInstance
  let _ : ∀ y, FiniteDimensional ℝ (V y) := fun y => VectorBundle.finiteDimensional ℝ F V y
  let _ : TopologicalSpace (TotalSpace (⋀[ℝ]^2 F) (fun y => ⋀[ℝ]^2 (V y))) :=
    Bundle.ExteriorPower.totalSpaceTopology F V 2
  let _ : FiberBundle (⋀[ℝ]^2 F) (fun y => ⋀[ℝ]^2 (V y)) :=
    Bundle.ExteriorPower.fiberBundle F V 2
  let _ : VectorBundle ℝ (⋀[ℝ]^2 F) (fun y => ⋀[ℝ]^2 (V y)) :=
    Bundle.ExteriorPower.vector_bundle F V 2
  let _ : ContMDiffVectorBundle ∞ (⋀[ℝ]^2 F) (fun y => ⋀[ℝ]^2 (V y)) I :=
    Bundle.ExteriorPower.contMDiffVectorBundle (IB := I) (n := ∞) F V 2
  let _ : IsContMDiffRiemannianBundle I ∞ (⋀[ℝ]^2 F) (fun y => ⋀[ℝ]^2 (V y)) :=
    Bundle.ExteriorPower.isContMDiffRiemannianBundle (IB := I) (n := ∞) F V 2
  obtain ⟨A, hA, hAsym, -, -⟩ :=
    exists_traceNormalizedCurvatureEndomorphism_pullback_sections
      (F := F) (V := V) S hS ι hJD hι
  have hιt : ContMDiff I (I.prod 𝓘(ℝ, F →L[ℝ] E)) ∞
      (fun y => TotalSpace.mk' (F →L[ℝ] E) y (ι t y).toContinuousLinearMap) :=
    hι.comp_contMDiff (contMDiff_const.prodMk contMDiff_id) (fun y => ⟨htJ, mem_univ y⟩)
  let cov := (CovariantDerivative.pullbackFiberwiseLinearEquiv
    (fun y => (ι t y).toLinearEquiv)
    (hιt.of_le (show (1 : ℕ∞ω) ≤ ∞ by simp)).clm_bundle_map
    (DifferentialGeometry.Geometry.Connection.LeviCivita (S.family.metric t))).exteriorPower 2
  have hp := traceNormalizedCurvatureEndomorphism_pullback_section_hasDerivWithinAt_of_ricci_ode
    (F := F) (V := V) S hS ι hJD htJ hιt (hm t htJ) hdim
    (fun y v => hode y v t htJ)
  have hcovsmooth : ContMDiffCovariantDerivative cov ∞ := hp.1
  have hcovmetric : cov.IsMetricCompatible := hp.2.1
  have hderiv := hp.2.2 A hA
  let _ : ContMDiffCovariantDerivative cov ∞ := hcovsmooth
  apply curvature_upperSupport_of_sections
    (E := E) (H := H) (I := I) (M := M) (F := F) (V := V)
    (D := D) (J := J) (T := T) (t := t) S hJ hdim hT ht htJ ι hm A hA hAsym
    cov hcovmetric x ?_ hR
  exact hderiv x

private theorem curvature_upperSupport_of_initial_isometry
    {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]
    {V : M → Type*} [TopologicalSpace (TotalSpace F V)]
    [∀ y, NormedAddCommGroup (V y)] [∀ y, InnerProductSpace ℝ (V y)]
    [FiberBundle F V] [VectorBundle ℝ F V] [ContMDiffVectorBundle ∞ F V I]
    [IsContMDiffRiemannianBundle I ∞ F V]
    {D : RealTimeInterval} (S : SolutionOn (I := I) (M := M) D) (hS : IsSolutionOn S)
    {J : Set ℝ} (hJ : IsOpen J) (hord : J.OrdConnected) (hJD : J ⊆ D.regular)
    (hdim : Module.finrank ℝ F = 3) {T t : ℝ} (hT : 0 < T)
    (ht : t ∈ Icc 0 T) (htJ : t ∈ J)
    (ι₀ : ∀ y, V y ≃L[ℝ] TangentSpace I y)
    (hι₀ : ContMDiff I (I.prod 𝓘(ℝ, F →L[ℝ] E)) ∞
      (fun y => TotalSpace.mk' (F →L[ℝ] E) y (ι₀ y).toContinuousLinearMap))
    (h₀ : ∀ y v w, (S.family.metric t).inner y (ι₀ y v) (ι₀ y w) = ⟪v, w⟫)
    (x : M)
    (hR : (⟨metricRm04At (S.family.metric t) x,
      metricRm04At_mem_algebraicCurvatureTensorSubmodule (S.family.metric t) x⟩ :
        algebraicCurvatureTensorSubmodule (I := I) (M := M) x) ∈
          algebraicCurvatureOperatorNonnegativeCone (I := I) (M := M)) :
    Nonempty (ParabolicUpperSupportAt (flowG S) T (fun _ _ => 0)
      (fun s y => 2 * leastCurvatureOperatorEigenvalueAt (S.base.metric s) y
        ⟨S.base.rm04 s y,
          metricRm04At_mem_algebraicCurvatureTensorSubmodule (S.base.metric s) y⟩) t x) := by
  obtain ⟨ι, -, hι, -, hode, hm⟩ := exists_uhlenbeck_isometry_on_interval
    (F := F) (V := V) S hS hord htJ hJD
    (RiemannianMetric.ofInnerProductSpace V) ι₀ hι₀ h₀
  exact curvature_upperSupport_of_uhlenbeck_isometry
    (F := F) (V := V) S hS hJ hJD hdim hT ht htJ ι hι hm hode x hR

private theorem curvature_upperSupport_of_initial_metric
    {F : Type*} [oldNorm : NormedAddCommGroup F] [oldSpace : NormedSpace ℝ F]
    [FiniteDimensional ℝ F]
    {V : M → Type*} [TopologicalSpace (TotalSpace F V)]
    [∀ y, NormedAddCommGroup (V y)] [∀ y, NormedSpace ℝ (V y)]
    [FiberBundle F V] [VectorBundle ℝ F V] [ContMDiffVectorBundle ∞ F V I]
    {D : RealTimeInterval} (S : SolutionOn (I := I) (M := M) D) (hS : IsSolutionOn S)
    {J : Set ℝ} (hJ : IsOpen J) (hord : J.OrdConnected) (hJD : J ⊆ D.regular)
    (hdim : Module.finrank ℝ F = 3) {T t : ℝ} (hT : 0 < T)
    (ht : t ∈ Icc 0 T) (htJ : t ∈ J)
    (h : ContMDiffRiemannianMetric I ∞ F V)
    (ι₀ : ∀ y, V y ≃L[ℝ] TangentSpace I y)
    (hι₀ : ContMDiff I (I.prod 𝓘(ℝ, F →L[ℝ] E)) ∞
      (fun y => TotalSpace.mk' (F →L[ℝ] E) y (ι₀ y).toContinuousLinearMap))
    (h₀ : ∀ y v w, (S.family.metric t).inner y (ι₀ y v) (ι₀ y w) = h.inner y v w)
    (x : M)
    (hR : (⟨metricRm04At (S.family.metric t) x,
      metricRm04At_mem_algebraicCurvatureTensorSubmodule (S.family.metric t) x⟩ :
        algebraicCurvatureTensorSubmodule (I := I) (M := M) x) ∈
          algebraicCurvatureOperatorNonnegativeCone (I := I) (M := M)) :
    Nonempty (ParabolicUpperSupportAt (flowG S) T (fun _ _ => 0)
      (fun s y => 2 * leastCurvatureOperatorEigenvalueAt (S.base.metric s) y
        ⟨S.base.rm04 s y,
          metricRm04At_mem_algebraicCurvatureTensorSubmodule (S.base.metric s) y⟩) t x) := by
  let _ : RiemannianBundle V := ⟨h.toRiemannianMetric⟩
  let sourceNorm : ∀ y, NormedAddCommGroup (V y) := fun y =>
    instNormedAddCommGroupOfRiemannianBundleOfIsTopologicalAddGroupOfContinuousConstSMulReal y
  let _ : ∀ y, NormedAddCommGroup (V y) := sourceNorm
  let _ : ∀ y, SeminormedAddCommGroup (V y) :=
    fun y => (sourceNorm y).toSeminormedAddCommGroup
  let _ : ∀ y, InnerProductSpace ℝ (V y) := fun y => Bundle.instInnerProductSpaceReal y
  let _ : IsContMDiffRiemannianBundle I ∞ F V := ⟨h.inner, h.contMDiff, fun _ _ _ => rfl⟩
  let m := MetricFiberData.ofFiniteDimensional F
  have hιwithin := fun y =>
    (contMDiffWithinAt_hom_totalSpace_domain_model_metric_iff
      (IA := I) (IB := I) (F := E) (V := TangentSpace I) (W := V) m
      (n := ∞) (f := fun z => TotalSpace.mk' (F →L[ℝ] E) z (ι₀ z).toContinuousLinearMap)
      (s := Set.univ) (x := y)).mpr ((hι₀ y).contMDiffWithinAt (s := Set.univ))
  let vb := vector_bundle_model_metric (V := V) m
  let svb := contMDiffVectorBundle_model_metric (IB := I) (V := V) (n := ∞) m
  let rm := isContMDiffRiemannianBundle_model_metric (IB := I) (V := V) (n := ∞) m
  let _ : NormedAddCommGroup F := m.toNormedAddCommGroupOfTopology
  let _ : InnerProductSpace ℝ F :=
    @MetricFiberData.toInnerProductSpaceOfTopology F oldNorm.toAddCommGroup oldSpace.toModule
      _ _ (by let _ : SeminormedAddCommGroup F := oldNorm.toSeminormedAddCommGroup
              let _ : NormedSpace ℝ F := oldSpace
              infer_instance) _ _ m
  let _ : VectorBundle ℝ F V := vb
  let _ : ContMDiffVectorBundle ∞ F V I := svb
  let _ : IsContMDiffRiemannianBundle I ∞ F V := rm
  have hιnew : ContMDiff I (I.prod 𝓘(ℝ, F →L[ℝ] E)) ∞
      (fun y => TotalSpace.mk' (F →L[ℝ] E) y (ι₀ y).toContinuousLinearMap) :=
    fun y => contMDiffWithinAt_univ.mp (hιwithin y)
  exact curvature_upperSupport_of_initial_isometry (F := F) (V := V) S hS hJ hord hJD hdim hT ht htJ
    ι₀ hιnew h₀ x hR

theorem nonempty_parabolicUpperSupportAt_twice_leastCurvatureOperatorEigenvalueAt
    {D : RealTimeInterval} (S : SolutionOn (I := I) (M := M) D) (hS : IsSolutionOn S)
    (hdim : Module.finrank ℝ E = 3) {T t : ℝ} (hT : 0 < T)
    (ht : t ∈ Icc 0 T) (htD : t ∈ D.regular) (x : M)
    (hR : (⟨metricRm04At (S.family.metric t) x,
      metricRm04At_mem_algebraicCurvatureTensorSubmodule (S.family.metric t) x⟩ :
        algebraicCurvatureTensorSubmodule (I := I) (M := M) x) ∈
          algebraicCurvatureOperatorNonnegativeCone (I := I) (M := M)) :
    Nonempty (ParabolicUpperSupportAt (flowG S) T (fun _ _ => 0)
      (fun s y => 2 * leastCurvatureOperatorEigenvalueAt (S.base.metric s) y
        ⟨S.base.rm04 s y,
          metricRm04At_mem_algebraicCurvatureTensorSubmodule (S.base.metric s) y⟩) t x) := by
  obtain ⟨a, b, htJ, hJD⟩ :=
    mem_nhds_iff_exists_Ioo_subset.mp (D.regular_isOpen.mem_nhds htD)
  exact curvature_upperSupport_of_initial_metric (F := E) (V := TangentSpace I)
    S hS isOpen_Ioo ordConnected_Ioo hJD hdim hT ht htJ (S.family.metric t)
    (fun y => ContinuousLinearEquiv.refl ℝ (TangentSpace I y))
    (show ContMDiff I (I.prod 𝓘(ℝ, E →L[ℝ] E)) ∞
      (fun y : M => TotalSpace.mk' (E →L[ℝ] E) y
        (ContinuousLinearMap.id ℝ (TangentSpace I y))) from
      (contMDiff_id : ContMDiff I I ∞ (fun y : M => y)).clm_bundle_id)
    (fun _ _ _ => rfl) x hR

end DifferentialGeometry.PDE.RicciFlow
