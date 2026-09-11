import DifferentialGeometry.Geometry.Flow.RicciFlow.Estimates.Uhlenbeck.CurvatureOperatorSectionEvolution
import DifferentialGeometry.Analysis.Parabolic.CurvatureOperatorRank
import DifferentialGeometry.Geometry.Curvature.DimensionThree.ExteriorRank
import DifferentialGeometry.Geometry.Curvature.CurvatureOperator.ExteriorPositivity

set_option autoImplicit false

noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow

open Bundle CovariantDerivative Set
open DifferentialGeometry.Geometry.Connection
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Curvature.DimensionThree
open DifferentialGeometry.Geometry.Operator
open scoped Manifold ContDiff Topology RealInnerProductSpace

private theorem hasDerivAt_of_isOpen {W : Type*} [AddCommGroup W]
    [Module ℝ W] [TopologicalSpace W] [ContinuousSMul ℝ W]
    {f : ℝ → W} {f' : W} {s : Set ℝ} {t : ℝ}
    (h : HasDerivWithinAt f f' s t) (hs : IsOpen s) (ht : t ∈ s) :
    HasDerivAt f f' t := by
  unfold HasDerivWithinAt at h
  rw [nhdsWithin_eq_nhds.mpr (hs.mem_nhds ht)] at h
  exact h

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M]
  {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]
  {V : M → Type*} [TopologicalSpace (TotalSpace F V)]
  [∀ x, NormedAddCommGroup (V x)] [∀ x, InnerProductSpace ℝ (V x)]
  [FiberBundle F V] [VectorBundle ℝ F V] [ContMDiffVectorBundle ∞ F V I]
  [IsContMDiffRiemannianBundle I ∞ F V]

private theorem pullback_curvature_section_evolution_at
    {D : RealTimeInterval} (S : SolutionOn (I := I) (M := M) D) (hS : IsSolutionOn S)
    (ι : ℝ → ∀ x, V x ≃L[ℝ] TangentSpace I x)
    {J : Set ℝ} (hJ : IsOpen J) (hJD : J ⊆ D.regular)
    {t : ℝ} (ht : t ∈ J)
    (hιt : ContMDiff I (I.prod 𝓘(ℝ, F →L[ℝ] E)) ∞
      (fun y => TotalSpace.mk' (F →L[ℝ] E) y (ι t y).toContinuousLinearMap))
    (hmetric : ∀ x v w, (S.family.metric t).inner x (ι t x v) (ι t x w) = ⟪v, w⟫)
    (hdim : Module.finrank ℝ F = 3)
    (hode : ∀ x v, HasDerivWithinAt (fun s => ι s x v)
      (ricciSharp (I := I) (S.family.metric t) x (ι t x v)) J t) :
    letI : ∀ y, FiniteDimensional ℝ (V y) := fun y => VectorBundle.finiteDimensional ℝ F V y
    letI := Bundle.ExteriorPower.totalSpaceTopology F V 2
    letI := Bundle.ExteriorPower.fiberBundle F V 2
    letI := Bundle.ExteriorPower.vector_bundle F V 2
    letI := Bundle.ExteriorPower.contMDiffVectorBundle (IB := I) (n := ∞) F V 2
    letI := Bundle.ExteriorPower.isContMDiffRiemannianBundle (IB := I) (n := ∞) F V 2
    let R := fun s y => exteriorPower.traceNormalizedCurvatureEndomorphism
      ((S.base.rm04 s y).compContinuousLinearMap (fun _ => (ι s y).toContinuousLinearMap))
      (by
        have hT := mem_algebraicCurvatureTensorSubmodule.mp
          (metricRm04At_mem_algebraicCurvatureTensorSubmodule (I := I) (S.base.metric s) y)
        exact hT.compContinuousLinearMap (ι s y).toContinuousLinearMap)
    let hι₁ := hιt.of_le (show (1 : ℕ∞ω) ≤ ∞ by simp)
    let cov := CovariantDerivative.pullbackFiberwiseLinearEquiv
      (fun y => (ι t y).toLinearEquiv) hι₁.clm_bundle_map (LeviCivita (S.family.metric t))
    ContMDiffCovariantDerivative (cov.exteriorPower 2) ∞ ∧
      (cov.exteriorPower 2).IsMetricCompatible ∧
      ∀ A : ℝ → Cₛ^∞⟮I; (⋀[ℝ]^2 F) →L[ℝ] ⋀[ℝ]^2 F,
        (fun y : M => (⋀[ℝ]^2 (V y)) →L[ℝ] ⋀[ℝ]^2 (V y))⟯,
        (∀ s ∈ J, ∀ y, A s y = R s y) →
        ∀ x, HasDerivAt (fun s => A s x)
          (rawBundleEndomorphismConnLap (S.family.metric t) (cov.exteriorPower 2)
            (fun y => A t y) x +
            (curvatureOperatorReactionEndomorphism3 (A t x).toLinearMap).toContinuousLinearMap) t := by
  dsimp only
  have hp := traceNormalizedCurvatureEndomorphism_pullback_section_hasDerivWithinAt_of_ricci_ode
    (F := F) S hS ι hJD ht hιt hmetric hdim hode
  refine ⟨hp.1, hp.2.1, ?_⟩
  intro A hA x
  exact hasDerivAt_of_isOpen (hp.2.2 A hA x) hJ ht

theorem traceNormalizedCurvatureEndomorphism_pullback_smooth_parallel_kernel_at_right_endpoint
    {D : RealTimeInterval} (S : SolutionOn (I := I) (M := M) D) (hS : IsSolutionOn S)
    (hdim : Module.finrank ℝ F = 3)
    (ι : ℝ → ∀ x, V x ≃L[ℝ] TangentSpace I x)
    {J : Set ℝ} (hJ : IsOpen J) (hreg : J ⊆ D.regular)
    {a b : ℝ} (hab : a < b) (hsub : Ioc a b ⊆ J)
    (hι : ContMDiffOn (𝓘(ℝ, ℝ).prod I) (I.prod 𝓘(ℝ, F →L[ℝ] E)) ∞
      (fun p : ℝ × M => TotalSpace.mk' (F →L[ℝ] E) p.2
        (E := fun y => V y →L[ℝ] TangentSpace I y)
        (ι p.1 p.2).toContinuousLinearMap) (J ×ˢ (univ : Set M)))
    (hmetric : ∀ t ∈ J, ∀ x v w,
      (S.family.metric t).inner x (ι t x v) (ι t x w) = ⟪v, w⟫)
    (hode : ∀ t ∈ J, ∀ x v, HasDerivWithinAt (fun s => ι s x v)
      (ricciSharp (S.family.metric t) x (ι t x v)) J t)
    (hR : ∀ t ∈ Ioc a b, ∀ x,
      (⟨metricRm04At (S.family.metric t) x,
        metricRm04At_mem_algebraicCurvatureTensorSubmodule (S.family.metric t) x⟩ :
          algebraicCurvatureTensorSubmodule (I := I) (M := M) x) ∈
            algebraicCurvatureOperatorNonnegativeCone (I := I) (M := M))
    (q : ℕ) (hrank : ∀ t ∈ Ioc a b, ∀ x,
      Module.finrank ℝ (curvatureOperatorImageAt (S.family.metric t) x
        ⟨metricRm04At (S.family.metric t) x,
          metricRm04At_mem_algebraicCurvatureTensorSubmodule (S.family.metric t) x⟩) = q) :
    letI : ∀ y, FiniteDimensional ℝ (V y) := fun y => VectorBundle.finiteDimensional ℝ F V y
    letI := Bundle.ExteriorPower.totalSpaceTopology F V 2
    letI := Bundle.ExteriorPower.fiberBundle F V 2
    letI := Bundle.ExteriorPower.vector_bundle F V 2
    letI := Bundle.ExteriorPower.contMDiffVectorBundle (IB := I) (n := ∞) F V 2
    let hιt : ContMDiff I (I.prod 𝓘(ℝ, F →L[ℝ] E)) ∞
        (fun y => TotalSpace.mk' (F →L[ℝ] E) y (ι b y).toContinuousLinearMap) :=
      hι.comp_contMDiff (contMDiff_const.prodMk contMDiff_id) (fun y => ⟨hsub ⟨hab, le_rfl⟩, mem_univ y⟩)
    let cov := CovariantDerivative.pullbackFiberwiseLinearEquiv
      (fun y => (ι b y).toLinearEquiv)
      (hιt.of_le (show (1 : ℕ∞ω) ≤ ∞ by simp)).clm_bundle_map
      (LeviCivita (S.family.metric b))
    let R := fun r y => exteriorPower.traceNormalizedCurvatureEndomorphism
      ((S.base.rm04 r y).compContinuousLinearMap (fun _ => (ι r y).toContinuousLinearMap))
      ((mem_algebraicCurvatureTensorSubmodule.mp
        (metricRm04At_mem_algebraicCurvatureTensorSubmodule (S.base.metric r) y)).compContinuousLinearMap
          (ι r y).toContinuousLinearMap)
    ∃ K : ContMDiffVectorSubbundle (I := I) (F := ⋀[ℝ]^2 F)
      (V := fun x => ⋀[ℝ]^2 (V x)) (n := ∞),
      (∀ x, K.fiber x = (R b x).ker) ∧
      IsCovariantlyInvariantSubmoduleFamily (cov.exteriorPower 2) K.fiber ∧
      ∀ x v, v ∈ K.fiber x →
        curvatureOperatorReactionEndomorphism3 (R b x).toLinearMap v = 0 := by
  dsimp only
  classical
  have hb : b ∈ J := hsub ⟨hab, le_rfl⟩
  have hoo : Ioo a b ⊆ J := fun r hr => hsub ⟨hr.1, hr.2.le⟩
  let _ : ∀ y, FiniteDimensional ℝ (V y) := fun y => VectorBundle.finiteDimensional ℝ F V y
  let _ := Bundle.ExteriorPower.totalSpaceTopology F V 2
  let _ := Bundle.ExteriorPower.fiberBundle F V 2
  let _ := Bundle.ExteriorPower.vector_bundle F V 2
  let _ := Bundle.ExteriorPower.contMDiffVectorBundle (IB := I) (n := ∞) F V 2
  let _ := Bundle.ExteriorPower.isContMDiffRiemannianBundle (IB := I) (n := ∞) F V 2
  obtain ⟨A, hA, -, hAspace, -⟩ :=
    exists_traceNormalizedCurvatureEndomorphism_pullback_sections (F := F) S hS ι hreg hι
  have hslice (r : ℝ) (hr : r ∈ J) :
      ContMDiff I (I.prod 𝓘(ℝ, F →L[ℝ] E)) ∞
        (fun y => TotalSpace.mk' (F →L[ℝ] E) y (ι r y).toContinuousLinearMap) :=
    hι.comp_contMDiff (contMDiff_const.prodMk contMDiff_id) (fun y => ⟨hr, mem_univ y⟩)
  let pull (r : ℝ) (hr : r ∈ J) := CovariantDerivative.pullbackFiberwiseLinearEquiv
    (fun y => (ι r y).toLinearEquiv)
    ((hslice r hr).of_le (show (1 : ℕ∞ω) ≤ ∞ by simp)).clm_bundle_map
    (LeviCivita (S.family.metric r))
  have hp (r : ℝ) (hr : r ∈ J) :=
    pullback_curvature_section_evolution_at
      (F := F) S hS ι hJ hreg hr (hslice r hr) (hmetric r hr) hdim (hode r hr)
  let cov := fun r => if hr : r ∈ J then (pull r hr).exteriorPower 2
    else (pull b hb).exteriorPower 2
  have hcovsmooth : ∀ r, ContMDiffCovariantDerivative (cov r) ∞ := by
    intro r
    dsimp only [cov]
    split_ifs with hr
    · exact (hp r hr).1
    · exact (hp b hb).1
  let _ := hcovsmooth
  have hcovmetric : ∀ r, (cov r).IsMetricCompatible := by
    intro r
    dsimp only [cov]
    split_ifs with hr
    · exact (hp r hr).2.1
    · exact (hp b hb).2.1
  have hevol0 : ∀ r ∈ Ioc a b, ∀ y, HasDerivAt (fun u => A u y)
      (rawBundleEndomorphismConnLap (S.family.metric r) (cov r) (fun z => A r z) y +
        (curvatureOperatorReactionEndomorphism3 (A r y).toLinearMap).toContinuousLinearMap) r := by
    intro r hr y
    simp only [cov, dif_pos (hsub hr)]
    exact (hp r (hsub hr)).2.2 A hA y
  have hArank : ∀ r ∈ Ioc a b, ∀ y, Module.finrank ℝ (A r y).range = q := by
    intro r hr y
    rw [hA r (hsub hr) y]
    exact (traceNormalizedCurvatureEndomorphism_pullback_finrank_range
      ((VectorBundle.finrank_eq ℝ F V y).trans hdim) (S.family.metric r) y
      ⟨metricRm04At (S.family.metric r) y,
        metricRm04At_mem_algebraicCurvatureTensorSubmodule (S.family.metric r) y⟩
      (ι r y) (hmetric r (hsub hr) y)).trans (hrank r hr y)
  have hApos : ∀ r ∈ Ioc a b, ∀ y, (A r y).IsPositive := by
    intro r hr y
    rw [hA r (hsub hr) y]
    exact traceNormalizedCurvatureEndomorphism_pullback_isPositive_of_mem_nonnegativeCone
      ⟨metricRm04At (S.family.metric r) y,
        metricRm04At_mem_algebraicCurvatureTensorSubmodule (S.family.metric r) y⟩
      (hR r hr y) (ι r y).toContinuousLinearMap
  obtain ⟨K, hK, hparallel, hQ⟩ :=
    DifferentialGeometry.Analysis.Parabolic.curvatureOperator_smooth_parallel_kernel_at_right_endpoint
      S.family.metric cov hcovmetric A hab (hAspace.mono (Set.prod_mono hoo Set.Subset.rfl))
      q hArank hApos (fun _ _ => 0) (by
        intro r hr y
        simpa only [map_zero, add_zero] using hevol0 r hr y)
  refine ⟨K, ?_, ?_, ?_⟩
  · intro x
    rw [hK x, hA b hb x]
  · simpa only [cov, dif_pos hb, pull, hslice] using hparallel
  · intro x v hv
    have h := hQ x v hv
    rw [hA b hb x] at h
    exact h

theorem exists_uhlenbeck_isometry_with_smooth_parallel_curvatureOperator_kernel_at_right_endpoint
    {D : RealTimeInterval} (S : SolutionOn (I := I) (M := M) D) (hS : IsSolutionOn S)
    (hdim : Module.finrank ℝ F = 3)
    {J : Set ℝ} {t₀ : ℝ} (hJ : IsOpen J) (hJconn : J.OrdConnected)
    (ht₀ : t₀ ∈ J) (hreg : J ⊆ D.regular)
    {a b : ℝ} (hab : a < b) (hsub : Ioc a b ⊆ J)
    (ι₀ : ∀ x, V x ≃L[ℝ] TangentSpace I x)
    (hι₀ : ContMDiff I (I.prod 𝓘(ℝ, F →L[ℝ] E)) ∞
      (fun x => TotalSpace.mk' (F →L[ℝ] E) x (ι₀ x).toContinuousLinearMap))
    (h₀ : ∀ x v w, (S.family.metric t₀).inner x (ι₀ x v) (ι₀ x w) = ⟪v, w⟫)
    (hR : ∀ t ∈ Ioc a b, ∀ x,
      (⟨metricRm04At (S.family.metric t) x,
        metricRm04At_mem_algebraicCurvatureTensorSubmodule (S.family.metric t) x⟩ :
          algebraicCurvatureTensorSubmodule (I := I) (M := M) x) ∈
            algebraicCurvatureOperatorNonnegativeCone (I := I) (M := M))
    (q : ℕ) (hrank : ∀ t ∈ Ioc a b, ∀ x,
      Module.finrank ℝ (curvatureOperatorImageAt (S.family.metric t) x
        ⟨metricRm04At (S.family.metric t) x,
          metricRm04At_mem_algebraicCurvatureTensorSubmodule (S.family.metric t) x⟩) = q) :
    ∃ ι : ℝ → ∀ x, V x ≃L[ℝ] TangentSpace I x,
      (∀ x, ι t₀ x = ι₀ x) ∧
      ContMDiffOn (𝓘(ℝ, ℝ).prod I) (I.prod 𝓘(ℝ, F →L[ℝ] E)) ∞
        (fun p : ℝ × M => TotalSpace.mk' (F →L[ℝ] E) p.2
          (E := fun y => V y →L[ℝ] TangentSpace I y)
          (ι p.1 p.2).toContinuousLinearMap) (J ×ˢ (univ : Set M)) ∧
      ContMDiffOn (𝓘(ℝ, ℝ).prod I) (I.prod 𝓘(ℝ, E →L[ℝ] F)) ∞
        (fun p : ℝ × M => TotalSpace.mk' (E →L[ℝ] F) p.2
          (E := fun y => TangentSpace I y →L[ℝ] V y)
          (ι p.1 p.2).symm.toContinuousLinearMap) (J ×ˢ (univ : Set M)) ∧
      (∀ t ∈ J, ∀ x v, HasDerivWithinAt (fun s => ι s x v)
        (ricciSharp (S.family.metric t) x (ι t x v)) J t) ∧
      (∀ t ∈ J, ∀ x v w,
        (S.family.metric t).inner x (ι t x v) (ι t x w) = ⟪v, w⟫) ∧
      letI : ∀ y, FiniteDimensional ℝ (V y) := fun y => VectorBundle.finiteDimensional ℝ F V y
      letI := Bundle.ExteriorPower.totalSpaceTopology F V 2
      letI := Bundle.ExteriorPower.fiberBundle F V 2
      letI := Bundle.ExteriorPower.vector_bundle F V 2
      letI := Bundle.ExteriorPower.contMDiffVectorBundle (IB := I) (n := ∞) F V 2
      ∃ hιt : ContMDiff I (I.prod 𝓘(ℝ, F →L[ℝ] E)) ∞
          (fun y => TotalSpace.mk' (F →L[ℝ] E) y (ι b y).toContinuousLinearMap),
      let cov := CovariantDerivative.pullbackFiberwiseLinearEquiv
        (fun y => (ι b y).toLinearEquiv)
        (hιt.of_le (show (1 : ℕ∞ω) ≤ ∞ by simp)).clm_bundle_map
        (LeviCivita (S.family.metric b))
      let R := fun r y => exteriorPower.traceNormalizedCurvatureEndomorphism
        ((S.base.rm04 r y).compContinuousLinearMap (fun _ => (ι r y).toContinuousLinearMap))
        ((mem_algebraicCurvatureTensorSubmodule.mp
          (metricRm04At_mem_algebraicCurvatureTensorSubmodule (S.base.metric r) y)).compContinuousLinearMap
            (ι r y).toContinuousLinearMap)
      ∃ K : ContMDiffVectorSubbundle (I := I) (F := ⋀[ℝ]^2 F)
        (V := fun x => ⋀[ℝ]^2 (V x)) (n := ∞),
        (∀ x, K.fiber x = (R b x).ker) ∧
        IsCovariantlyInvariantSubmoduleFamily (cov.exteriorPower 2) K.fiber ∧
        ∀ x v, v ∈ K.fiber x →
          curvatureOperatorReactionEndomorphism3 (R b x).toLinearMap v = 0 := by
  obtain ⟨ι, hinit, hι, hinv, hode, hmetric⟩ :=
    exists_uhlenbeck_isometry_on_interval (F := F) (V := V) S hS hJconn ht₀ hreg
      (RiemannianMetric.ofInnerProductSpace V) ι₀ hι₀ h₀
  refine ⟨ι, hinit, hι, hinv, (fun t ht x v => hode x v t ht), hmetric, ?_⟩
  dsimp only
  let hιb : ContMDiff I (I.prod 𝓘(ℝ, F →L[ℝ] E)) ∞
      (fun y => TotalSpace.mk' (F →L[ℝ] E) y (ι b y).toContinuousLinearMap) :=
    hι.comp_contMDiff (contMDiff_const.prodMk contMDiff_id)
      (fun y => ⟨hsub ⟨hab, le_rfl⟩, mem_univ y⟩)
  refine ⟨hιb, ?_⟩
  exact traceNormalizedCurvatureEndomorphism_pullback_smooth_parallel_kernel_at_right_endpoint
    S hS hdim ι hJ hreg hab hsub hι hmetric (fun t ht x v => hode x v t ht) hR q hrank

end DifferentialGeometry.PDE.RicciFlow
