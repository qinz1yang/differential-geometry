import DifferentialGeometry.Geometry.Flow.RicciFlow.Estimates.Uhlenbeck.CurvatureOperatorRegularity
import DifferentialGeometry.Geometry.Flow.RicciFlow.Estimates.Uhlenbeck.CurvatureOperatorEvolution
import DifferentialGeometry.Analysis.Parabolic.CurvatureOperatorRank
import DifferentialGeometry.Geometry.Curvature.CurvatureOperator.ExteriorPositivity
import DifferentialGeometry.Geometry.Curvature.CurvatureOperator.ExteriorSmooth
import DifferentialGeometry.Geometry.Curvature.AlgebraicTensorMetric
import DifferentialGeometry.Tensor.Multilinear.BundleComp

set_option autoImplicit false

noncomputable section

open Bundle CovariantDerivative Filter Set
open DifferentialGeometry.Geometry.Connection
open DifferentialGeometry.Geometry.Curvature.DimensionThree
open DifferentialGeometry.Geometry.Operator
open scoped Manifold ContDiff Topology RealInnerProductSpace

namespace DifferentialGeometry.PDE.RicciFlow

open DifferentialGeometry.Geometry.Curvature

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M]
  {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]
  {V : M → Type*} [TopologicalSpace (TotalSpace F V)]
  [∀ x, NormedAddCommGroup (V x)] [∀ x, InnerProductSpace ℝ (V x)]
  [FiberBundle F V] [VectorBundle ℝ F V] [ContMDiffVectorBundle ∞ F V I]
  [IsContMDiffRiemannianBundle I ∞ F V]

omit [ContMDiffVectorBundle ∞ F V I] [IsContMDiffRiemannianBundle I ∞ F V]
    [I.Boundaryless] in
private theorem riemann_pullback_isAlgCurvForm
    {D : RealTimeInterval} (S : SolutionOn (I := I) (M := M) D) (t : ℝ) (x : M)
    (ι : V x ≃L[ℝ] TangentSpace I x) :
    IsAlgCurvForm (fun a b c d =>
      (S.base.rm04 t x).compContinuousLinearMap
        (fun _ => ι.toContinuousLinearMap) ![a, b, c, d]) := by
  have hT := mem_algebraicCurvatureTensorSubmodule.mp
    (metricRm04At_mem_algebraicCurvatureTensorSubmodule (I := I) (S.base.metric t) x)
  change IsAlgCurvForm (fun a b c d => S.base.rm04 t x ![a, b, c, d]) at hT
  exact hT.compContinuousLinearMap ι.toContinuousLinearMap

private theorem curvature_pullback_hasDerivAt
    {D : RealTimeInterval} (S : SolutionOn (I := I) (M := M) D) (hS : IsSolutionOn S)
    (ι : ℝ → ∀ x, V x ≃L[ℝ] TangentSpace I x)
    {J : Set ℝ} (hJ : IsOpen J) {t : ℝ} (ht : t ∈ J) (htD : t ∈ D.regular)
    (hιt : ContMDiff I (I.prod 𝓘(ℝ, F →L[ℝ] E)) ∞
      (fun x => TotalSpace.mk' (F →L[ℝ] E) x (ι t x).toContinuousLinearMap))
    (hmetric : ∀ x v w, (S.family.metric t).inner x (ι t x v) (ι t x w) = ⟪v, w⟫)
    (x : M) (hdim : Module.finrank ℝ (V x) = 3)
    (hode : ∀ v, HasDerivWithinAt (fun s => ι s x v)
      (ricciSharp (I := I) (S.family.metric t) x (ι t x v)) J t) :
    letI : ∀ x, FiniteDimensional ℝ (V x) := fun x => VectorBundle.finiteDimensional ℝ F V x
    letI := Bundle.ExteriorPower.totalSpaceTopology F V 2
    letI := Bundle.ExteriorPower.fiberBundle F V 2
    letI := Bundle.ExteriorPower.vector_bundle F V 2
    letI := Bundle.ExteriorPower.contMDiffVectorBundle (IB := I) (n := ∞) F V 2
    let cov := CovariantDerivative.pullbackFiberwiseLinearEquiv
      (fun x => (ι t x).toLinearEquiv)
      (hιt.of_le (show (1 : ℕ∞ω) ≤ ∞ by simp)).clm_bundle_map
      (LeviCivita (S.family.metric t))
    let R := fun s y => exteriorPower.traceNormalizedCurvatureEndomorphism
      ((S.base.rm04 s y).compContinuousLinearMap (fun _ => (ι s y).toContinuousLinearMap))
      (riemann_pullback_isAlgCurvForm S s y (ι s y))
    HasDerivAt (fun s => R s x)
      (rawBundleEndomorphismConnLap (S.family.metric t) (cov.exteriorPower 2) (R t) x +
        (curvatureOperatorReactionEndomorphism3 (R t x).toLinearMap).toContinuousLinearMap) t := by
  dsimp only
  let _ : ∀ x, FiniteDimensional ℝ (V x) := fun x => VectorBundle.finiteDimensional ℝ F V x
  let _ := Bundle.ExteriorPower.totalSpaceTopology F V 2
  let _ := Bundle.ExteriorPower.fiberBundle F V 2
  let _ := Bundle.ExteriorPower.vector_bundle F V 2
  let _ := Bundle.ExteriorPower.contMDiffVectorBundle (IB := I) (n := ∞) F V 2
  exact (traceNormalizedCurvatureEndomorphism_pullback_hasDerivWithinAt_of_ricci_ode
    S hS ⟨t, htD⟩ ι hιt hmetric x hdim hode).hasDerivAt (hJ.mem_nhds ht)

private theorem exists_Ioo_superset_Icc_of_isOpen
    {U : Set ℝ} (hU : IsOpen U) {a b : ℝ} (hab : a ≤ b)
    (hsub : Icc a b ⊆ U) :
    ∃ c d : ℝ, Icc a b ⊆ Ioo c d ∧ Ioo c d ⊆ U := by
  obtain ⟨c, v, ha, hcv⟩ :=
    mem_nhds_iff_exists_Ioo_subset.mp (hU.mem_nhds (hsub ⟨le_rfl, hab⟩))
  obtain ⟨w, d, hb, hwd⟩ :=
    mem_nhds_iff_exists_Ioo_subset.mp (hU.mem_nhds (hsub ⟨hab, le_rfl⟩))
  refine ⟨c, d, fun x hx => ⟨ha.1.trans_le hx.1, hx.2.trans_lt hb.2⟩, ?_⟩
  intro x hx
  by_cases hax : a ≤ x
  · by_cases hxb : x ≤ b
    · exact hsub ⟨hax, hxb⟩
    · exact hwd ⟨hb.1.trans (lt_of_not_ge hxb), hx.2⟩
  · exact hcv ⟨hx.1, (lt_of_not_ge hax).trans ha.2⟩

omit [ContMDiffVectorBundle ∞ F V I] [IsContMDiffRiemannianBundle I ∞ F V] in
private theorem curvature_pullback_connection_smooth
    (g : SmoothRiemannianMetric I M) (ι : ∀ x, V x ≃L[ℝ] TangentSpace I x)
    (hι : ContMDiff I (I.prod 𝓘(ℝ, F →L[ℝ] E)) ∞
      (fun x => TotalSpace.mk' (F →L[ℝ] E) x (ι x).toContinuousLinearMap)) :
    CovariantDerivative.ContMDiffCovariantDerivative
      (CovariantDerivative.pullbackFiberwiseLinearEquiv
        (fun x => (ι x).toLinearEquiv)
        (hι.of_le (show (1 : ℕ∞ω) ≤ ∞ by simp)).clm_bundle_map (LeviCivita g)) ∞ := by
  let _ : CompleteSpace F := FiniteDimensional.complete ℝ F
  have hiinv : ContMDiff I (I.prod 𝓘(ℝ, E →L[ℝ] F)) ∞
      (fun x => TotalSpace.mk' (E →L[ℝ] F) x (ι x).symm.toContinuousLinearMap) := by
    simpa only [ContinuousLinearMap.inverse_equiv] using
      hι.clm_bundle_inverse (fun _ => ContinuousLinearMap.isInvertible_equiv)
  exact CovariantDerivative.ContMDiffCovariantDerivative.pullbackFiberwiseLinearEquiv
    (fun x => (ι x).toLinearEquiv) hι.clm_bundle_map hiinv.clm_bundle_map (LeviCivita g)

private def smoothSectionExtension
    {J : Set ℝ}
    (R : ℝ → (x : M) → V x →L[ℝ] V x)
    (hR : ∀ t ∈ J, ContMDiff I (I.prod 𝓘(ℝ, F →L[ℝ] F)) ∞
      (fun x => TotalSpace.mk' (F →L[ℝ] F) x (R t x))) :
    ℝ → Cₛ^∞⟮I; F →L[ℝ] F, (fun x : M => V x →L[ℝ] V x)⟯ := by
  classical
  exact fun t => if ht : t ∈ J then ⟨R t, hR t ht⟩ else 0

omit [FiniteDimensional ℝ E] [I.Boundaryless] [IsManifold I ∞ M] [T2Space M]
    [FiniteDimensional ℝ F] [ContMDiffVectorBundle ∞ F V I]
    [IsContMDiffRiemannianBundle I ∞ F V] in
private theorem smoothSectionExtension_eq
    {J : Set ℝ}
    (R : ℝ → (x : M) → V x →L[ℝ] V x)
    (hR : ∀ t ∈ J, ContMDiff I (I.prod 𝓘(ℝ, F →L[ℝ] F)) ∞
      (fun x => TotalSpace.mk' (F →L[ℝ] F) x (R t x)))
    (t : ℝ) (ht : t ∈ J) (x : M) :
    smoothSectionExtension R hR t x = R t x := by
  classical
  simp only [smoothSectionExtension, dif_pos ht]
  rfl

omit [FiniteDimensional ℝ E] [I.Boundaryless] [IsManifold I ∞ M] [T2Space M]
    [FiniteDimensional ℝ F] [ContMDiffVectorBundle ∞ F V I]
    [IsContMDiffRiemannianBundle I ∞ F V] in
private theorem smoothSectionExtension_symmetric
    {J : Set ℝ}
    (R : ℝ → (x : M) → V x →L[ℝ] V x)
    (hR : ∀ t ∈ J, ContMDiff I (I.prod 𝓘(ℝ, F →L[ℝ] F)) ∞
      (fun x => TotalSpace.mk' (F →L[ℝ] F) x (R t x)))
    (hsym : ∀ t x, (R t x).IsSymmetric) :
    ∀ t x, (smoothSectionExtension R hR t x).IsSymmetric := by
  classical
  intro t x
  by_cases ht : t ∈ J
  · rw [smoothSectionExtension_eq R hR t ht x]
    exact hsym t x
  · change ((if ht : t ∈ J then (⟨R t, hR t ht⟩ :
      Cₛ^∞⟮I; F →L[ℝ] F, (fun x : M => V x →L[ℝ] V x)⟯) else 0) x).IsSymmetric
    rw [dif_neg ht]
    intro v w
    simp

omit [FiniteDimensional ℝ E] [I.Boundaryless] [IsManifold I ∞ M] [T2Space M]
    [FiniteDimensional ℝ F] [ContMDiffVectorBundle ∞ F V I]
    [IsContMDiffRiemannianBundle I ∞ F V] in
private theorem smoothSectionExtension_continuousOn
    {J K : Set ℝ} (hKJ : K ⊆ J)
    (R : ℝ → (x : M) → V x →L[ℝ] V x)
    (hR : ∀ t ∈ J, ContMDiff I (I.prod 𝓘(ℝ, F →L[ℝ] F)) ∞
      (fun x => TotalSpace.mk' (F →L[ℝ] F) x (R t x)))
    (hc : ContinuousOn (fun p : ℝ × M =>
      TotalSpace.mk' (F →L[ℝ] F) (E := fun x => V x →L[ℝ] V x) p.2 (R p.1 p.2))
      (J ×ˢ (Set.univ : Set M))) :
    ContinuousOn (fun p : ℝ × M =>
      TotalSpace.mk' (F →L[ℝ] F) (E := fun x => V x →L[ℝ] V x) p.2
        (smoothSectionExtension R hR p.1 p.2)) (K ×ˢ (Set.univ : Set M)) := by
  exact (hc.mono (Set.prod_mono hKJ Set.Subset.rfl)).congr
    (fun p hp => congrArg (TotalSpace.mk' (F →L[ℝ] F) p.2)
      (smoothSectionExtension_eq R hR p.1 (hKJ hp.1) p.2))

private def connectionExtension
    {J : Set ℝ} (cov : ∀ t ∈ J, CovariantDerivative I F V) {t₀ : ℝ} (ht₀ : t₀ ∈ J) :
    ℝ → CovariantDerivative I F V := by
  classical
  exact fun t => if ht : t ∈ J then cov t ht else cov t₀ ht₀

omit [FiniteDimensional ℝ E] [I.Boundaryless] [IsManifold I ∞ M] [T2Space M]
    [FiniteDimensional ℝ F] [VectorBundle ℝ F V] [ContMDiffVectorBundle ∞ F V I]
    [IsContMDiffRiemannianBundle I ∞ F V] in
private theorem connectionExtension_eq
    {J : Set ℝ} (cov : ∀ t ∈ J, CovariantDerivative I F V) {t₀ : ℝ} (ht₀ : t₀ ∈ J)
    {t : ℝ} (ht : t ∈ J) : connectionExtension cov ht₀ t = cov t ht := by
  classical
  simp only [connectionExtension, dif_pos ht]

omit [FiniteDimensional ℝ E] [I.Boundaryless] [T2Space M]
    [FiniteDimensional ℝ F] [ContMDiffVectorBundle ∞ F V I]
    [IsContMDiffRiemannianBundle I ∞ F V] in
private theorem connectionExtension_smooth
    {J : Set ℝ} (cov : ∀ t ∈ J, CovariantDerivative I F V) {t₀ : ℝ} (ht₀ : t₀ ∈ J)
    (hs : ∀ t ht, ContMDiffCovariantDerivative (cov t ht) ∞) :
    ∀ t, ContMDiffCovariantDerivative (connectionExtension cov ht₀ t) ∞ := by
  classical
  intro t
  unfold connectionExtension
  split_ifs with ht
  · exact hs t ht
  · exact hs t₀ ht₀

omit [FiniteDimensional ℝ E] [I.Boundaryless] [IsManifold I ∞ M] [T2Space M] in
private theorem connectionExtension_metric
    {J : Set ℝ} (cov : ∀ t ∈ J, CovariantDerivative I F V) {t₀ : ℝ} (ht₀ : t₀ ∈ J)
    (hm : ∀ t ht, (cov t ht).IsMetricCompatible) :
    ∀ t, (connectionExtension cov ht₀ t).IsMetricCompatible := by
  classical
  intro t
  unfold connectionExtension
  split_ifs with ht
  · exact hm t ht
  · exact hm t₀ ht₀

omit [I.Boundaryless] [IsContMDiffRiemannianBundle I ∞ F V] in
private theorem smoothSectionExtension_evolution
    {J : Set ℝ} (hJ : IsOpen J)
    (R : ℝ → (x : M) → V x →L[ℝ] V x)
    (hR : ∀ t ∈ J, ContMDiff I (I.prod 𝓘(ℝ, F →L[ℝ] F)) ∞
      (fun x => TotalSpace.mk' (F →L[ℝ] F) x (R t x)))
    (g : SmoothRiemannianMetric I M) (cov : CovariantDerivative I F V)
    {t : ℝ} (ht : t ∈ J) (x : M)
    (Q : (V x →L[ℝ] V x) → V x →L[ℝ] V x)
    (he : HasDerivAt (fun s => R s x)
      (rawBundleEndomorphismConnLap g cov (R t) x + Q (R t x)) t) :
    HasDerivAt (fun s => smoothSectionExtension R hR s x)
      (rawBundleEndomorphismConnLap g cov (fun y => smoothSectionExtension R hR t y) x +
        Q (smoothSectionExtension R hR t x)) t := by
  have he' := he.congr_of_eventuallyEq (by
    filter_upwards [hJ.mem_nhds ht] with s hs
    exact smoothSectionExtension_eq R hR s hs x)
  have hfun : (fun y => smoothSectionExtension R hR t y) = R t :=
    funext (smoothSectionExtension_eq R hR t ht)
  simpa only [map_zero, add_zero, hfun] using he'

omit [FiniteDimensional ℝ E] [I.Boundaryless] [IsManifold I ∞ M] [T2Space M]
    [FiniteDimensional ℝ F] [IsContMDiffRiemannianBundle I ∞ F V] in
private theorem smoothSectionExtension_spacetime
    {J K : Set ℝ} (hKJ : K ⊆ J)
    (R : ℝ → (x : M) → V x →L[ℝ] V x)
    (hR : ∀ t ∈ J, ContMDiff I (I.prod 𝓘(ℝ, F →L[ℝ] F)) ∞
      (fun x => TotalSpace.mk' (F →L[ℝ] F) x (R t x)))
    (hc : ContMDiffOnSpacetimeEndomorphism (I := I) (F := F) (V := V) (n := ∞)
      R (J ×ˢ (Set.univ : Set M))) :
    ContMDiffOnSpacetimeEndomorphism (I := I) (F := F) (V := V) (n := ∞)
      (fun t x => smoothSectionExtension R hR t x) (K ×ˢ (Set.univ : Set M)) := by
  let c : C^∞⟮𝓘(ℝ, ℝ).prod I, ℝ × M; I, M⟯ := ContMDiffMap.snd
  let _ : TopologicalSpace (TotalSpace F (fun p : ℝ × M => V p.2)) := by
    change TopologicalSpace (TotalSpace F (c *ᵖ V)); infer_instance
  let _ : FiberBundle F (fun p : ℝ × M => V p.2) := by
    change FiberBundle F (c *ᵖ V); infer_instance
  let _ : VectorBundle ℝ F (fun p : ℝ × M => V p.2) := by
    change VectorBundle ℝ F (c *ᵖ V); infer_instance
  let _ : ContMDiffVectorBundle ∞ F (fun p : ℝ × M => V p.2)
      (𝓘(ℝ, ℝ).prod I) := by
    change ContMDiffVectorBundle ∞ F (c *ᵖ V) (𝓘(ℝ, ℝ).prod I); infer_instance
  have hc' := hc.mono (Set.prod_mono hKJ Set.Subset.rfl)
  unfold ContMDiffOnSpacetimeEndomorphism at hc' ⊢
  exact hc'.congr (fun p hp => congrArg (TotalSpace.mk' (F →L[ℝ] F) p)
    (smoothSectionExtension_eq R hR p.1 (hKJ hp.1) p.2))

omit [I.Boundaryless] in
private theorem curvature_pullback_slice_smooth
    {D : RealTimeInterval} (S : SolutionOn (I := I) (M := M) D) (t : ℝ)
    (ι : ∀ x, V x ≃L[ℝ] TangentSpace I x)
    (hι : ContMDiff I (I.prod 𝓘(ℝ, F →L[ℝ] E)) ∞
      (fun x => TotalSpace.mk' (F →L[ℝ] E) x (ι x).toContinuousLinearMap)) :
    letI : ∀ x, FiniteDimensional ℝ (V x) := fun x => VectorBundle.finiteDimensional ℝ F V x
    letI := Bundle.ExteriorPower.totalSpaceTopology F V 2
    letI := Bundle.ExteriorPower.fiberBundle F V 2
    letI := Bundle.ExteriorPower.vector_bundle F V 2
    letI := Bundle.ExteriorPower.contMDiffVectorBundle (IB := I) (n := ∞) F V 2
    ContMDiff I (I.prod 𝓘(ℝ, (⋀[ℝ]^2 F) →L[ℝ] ⋀[ℝ]^2 F)) ∞
      (fun x => TotalSpace.mk' ((⋀[ℝ]^2 F) →L[ℝ] ⋀[ℝ]^2 F) x
        (exteriorPower.traceNormalizedCurvatureEndomorphism
          ((S.base.rm04 t x).compContinuousLinearMap (fun _ => (ι x).toContinuousLinearMap))
          (riemann_pullback_isAlgCurvForm S t x (ι x)))) := by
  let _ : ∀ x, FiniteDimensional ℝ (V x) := fun x => VectorBundle.finiteDimensional ℝ F V x
  let _ := Bundle.ExteriorPower.totalSpaceTopology F V 2
  let _ := Bundle.ExteriorPower.fiberBundle F V 2
  let _ := Bundle.ExteriorPower.vector_bundle F V 2
  let _ := Bundle.ExteriorPower.contMDiffVectorBundle (IB := I) (n := ∞) F V 2
  apply Bundle.ExteriorPower.contMDiff_traceNormalizedCurvatureEndomorphism F V ∞ le_rfl
  exact (S.base.rm04 t).contMDiff.multilinear_bundle_comp (fun _ => hι)

private theorem exists_curvature_pullback_evolution
    {D : RealTimeInterval} (S : SolutionOn (I := I) (M := M) D) (hS : IsSolutionOn S)
    (hdim : Module.finrank ℝ F = 3)
    {J : Set ℝ} (hJ : IsOpen J) (hJD : J ⊆ D.regular)
    {T : ℝ} (hT : 0 < T) (hTJ : Set.Icc 0 T ⊆ J)
    (ι : ℝ → ∀ x, V x ≃L[ℝ] TangentSpace I x)
    (hι : ContMDiffOn (𝓘(ℝ, ℝ).prod I) (I.prod 𝓘(ℝ, F →L[ℝ] E)) ∞
      (fun p : ℝ × M => TotalSpace.mk' (F →L[ℝ] E) p.2
        (E := fun x => V x →L[ℝ] TangentSpace I x)
        (ι p.1 p.2).toContinuousLinearMap) (J ×ˢ (Set.univ : Set M)))
    (hmetric : ∀ t ∈ J, ∀ x v w, (S.family.metric t).inner x (ι t x v) (ι t x w) = ⟪v, w⟫)
    (hode : ∀ x v, ∀ t ∈ J, HasDerivWithinAt (fun s => ι s x v)
      (ricciSharp (I := I) (S.family.metric t) x (ι t x v)) J t)
    (hR : ∀ t ∈ Set.Icc 0 T, ∀ x,
      (⟨metricRm04At (S.family.metric t) x,
        metricRm04At_mem_algebraicCurvatureTensorSubmodule (S.family.metric t) x⟩ :
          algebraicCurvatureTensorSubmodule (I := I) (M := M) x) ∈
            algebraicCurvatureOperatorNonnegativeCone (I := I) (M := M)) :
    letI : ∀ x, FiniteDimensional ℝ (V x) := fun x => VectorBundle.finiteDimensional ℝ F V x
    letI := Bundle.ExteriorPower.totalSpaceTopology F V 2
    letI := Bundle.ExteriorPower.fiberBundle F V 2
    letI := Bundle.ExteriorPower.vector_bundle F V 2
    letI := Bundle.ExteriorPower.contMDiffVectorBundle (IB := I) (n := ∞) F V 2
    letI := Bundle.ExteriorPower.isContMDiffRiemannianBundle (IB := I) (n := ∞) F V 2
    let R := fun t x => exteriorPower.traceNormalizedCurvatureEndomorphism
      ((S.base.rm04 t x).compContinuousLinearMap (fun _ => (ι t x).toContinuousLinearMap))
      (riemann_pullback_isAlgCurvForm S t x (ι t x))
    ∃ A : ℝ → Cₛ^∞⟮I; (⋀[ℝ]^2 F) →L[ℝ] ⋀[ℝ]^2 F,
        (fun x : M => (⋀[ℝ]^2 (V x)) →L[ℝ] ⋀[ℝ]^2 (V x))⟯,
      ∃ cov : ℝ → CovariantDerivative I (⋀[ℝ]^2 F) (fun x => ⋀[ℝ]^2 (V x)),
      (∀ t, ContMDiffCovariantDerivative (cov t) ∞) ∧
      (∀ t, (cov t).IsMetricCompatible) ∧
      (∀ t ∈ J, ∀ x, A t x = R t x) ∧
      (∀ t ∈ J, ∃ hιt : ContMDiff I (I.prod 𝓘(ℝ, F →L[ℝ] E)) ∞
        (fun x => TotalSpace.mk' (F →L[ℝ] E) x (ι t x).toContinuousLinearMap),
        cov t = (CovariantDerivative.pullbackFiberwiseLinearEquiv
          (fun x => (ι t x).toLinearEquiv)
          (hιt.of_le (show (1 : ℕ∞ω) ≤ ∞ by simp)).clm_bundle_map
          (LeviCivita (S.family.metric t))).exteriorPower 2) ∧
      ContMDiffOnSpacetimeEndomorphism (I := I) (F := ⋀[ℝ]^2 F)
        (V := fun x => ⋀[ℝ]^2 (V x)) (n := ∞)
        (fun t x => A t x) (Set.Ioo 0 T ×ˢ (Set.univ : Set M)) ∧
      (∀ t x, (A t x).IsSymmetric) ∧
      (∀ t ∈ Set.Icc 0 T, ∀ x, (A t x).IsPositive) ∧
      ContinuousOn (fun p : ℝ × M =>
        TotalSpace.mk' ((⋀[ℝ]^2 F) →L[ℝ] ⋀[ℝ]^2 F)
          (E := fun x => (⋀[ℝ]^2 (V x)) →L[ℝ] ⋀[ℝ]^2 (V x)) p.2 (A p.1 p.2))
        (Set.Icc 0 T ×ˢ (Set.univ : Set M)) ∧
      (∀ t ∈ Set.Ioc 0 T, ∀ x, HasDerivAt (fun s => A s x)
        (rawBundleEndomorphismConnLap (S.family.metric t) (cov t) (fun y => A t y) x +
          (curvatureOperatorReactionEndomorphism3 (A t x).toLinearMap).toContinuousLinearMap) t) := by
  dsimp only
  classical
  let _ : ∀ x, FiniteDimensional ℝ (V x) := fun x => VectorBundle.finiteDimensional ℝ F V x
  let _ := Bundle.ExteriorPower.totalSpaceTopology F V 2
  let _ := Bundle.ExteriorPower.fiberBundle F V 2
  let _ := Bundle.ExteriorPower.vector_bundle F V 2
  let _ := Bundle.ExteriorPower.contMDiffVectorBundle (IB := I) (n := ∞) F V 2
  let _ := Bundle.ExteriorPower.isContMDiffRiemannianBundle (IB := I) (n := ∞) F V 2
  let R := fun t x => exteriorPower.traceNormalizedCurvatureEndomorphism
    ((S.base.rm04 t x).compContinuousLinearMap (fun _ => (ι t x).toContinuousLinearMap))
    (riemann_pullback_isAlgCurvForm S t x (ι t x))
  have hιslice (t : ℝ) (ht : t ∈ J) : ContMDiff I (I.prod 𝓘(ℝ, F →L[ℝ] E)) ∞
      (fun x => TotalSpace.mk' (F →L[ℝ] E) x (ι t x).toContinuousLinearMap) :=
    hι.comp_contMDiff (contMDiff_const.prodMk contMDiff_id) (fun x => ⟨ht, Set.mem_univ x⟩)
  have hRslice := fun t ht => curvature_pullback_slice_smooth S t (ι t) (hιslice t ht)
  let A := smoothSectionExtension R hRslice
  have hAeq (t : ℝ) (ht : t ∈ J) (x : M) : A t x = R t x := smoothSectionExtension_eq R hRslice t ht x
  have hRcont := traceNormalizedCurvatureEndomorphism_pullback_continuousOn S hS ι
    (fun t ht => D.regular_subset (hJD ht)) hι.continuousOn
  have hAcont := smoothSectionExtension_continuousOn hTJ R hRslice hRcont
  have hApos : ∀ t ∈ Set.Icc 0 T, ∀ x, (A t x).IsPositive := by
    intro t ht x
    rw [hAeq t (hTJ ht) x]
    exact (ContinuousLinearMap.isPositive_toLinearMap_iff _).mp
      (traceNormalizedCurvatureEndomorphism_metric_pullback_isPositive
        (S.family.metric t) x (hR t ht x) (ι t x).toContinuousLinearMap)
  have hAsymm : ∀ t x, (A t x).IsSymmetric :=
    smoothSectionExtension_symmetric R hRslice
      (fun t x => exteriorPower.traceNormalizedCurvatureEndomorphism_isSymmetric _ _)
  let uCov (t : ℝ) (ht : t ∈ J) := CovariantDerivative.pullbackFiberwiseLinearEquiv
    (fun x => (ι t x).toLinearEquiv)
    ((hιslice t ht).of_le (show (1 : ℕ∞ω) ≤ ∞ by simp)).clm_bundle_map
    (LeviCivita (S.family.metric t))
  have hCovSmooth (t : ℝ) (ht : t ∈ J) :
      CovariantDerivative.ContMDiffCovariantDerivative (uCov t ht) ∞ :=
    curvature_pullback_connection_smooth (S.family.metric t) (ι t) (hιslice t ht)
  have hCovMetric (t : ℝ) (ht : t ∈ J) : (uCov t ht).IsMetricCompatible :=
    CovariantDerivative.isMetricCompatible_pullback_leviCivita
      (S.family.metric t) (ι t)
      ((hιslice t ht).of_le (show (1 : ℕ∞ω) ≤ ∞ by simp)) (hmetric t ht)
  have hzJ : 0 ∈ J := hTJ ⟨le_rfl, hT.le⟩
  let cov := connectionExtension (fun t ht => (uCov t ht).exteriorPower 2) hzJ
  let _ : ∀ t, CovariantDerivative.ContMDiffCovariantDerivative (cov t) ∞ :=
    connectionExtension_smooth _ hzJ (fun t ht => by
      let _ := hCovSmooth t ht
      exact (uCov t ht).exteriorPower_contMDiff 2)
  have hcov : ∀ t, (cov t).IsMetricCompatible :=
    connectionExtension_metric _ hzJ (fun t ht => (hCovMetric t ht).exteriorPower 2)
  have hevolR (t : ℝ) (ht : t ∈ J) (x : M) :
      HasDerivAt (fun s => R s x)
        (rawBundleEndomorphismConnLap (S.family.metric t) (cov t) (R t) x +
          (curvatureOperatorReactionEndomorphism3 (R t x).toLinearMap).toContinuousLinearMap) t := by
    have he := curvature_pullback_hasDerivAt S hS ι hJ ht (hJD ht) (hιslice t ht)
      (hmetric t ht) x ((VectorBundle.finrank_eq ℝ F V x).trans hdim)
      (fun v => hode x v t ht)
    simpa only [cov, connectionExtension_eq _ hzJ ht] using he
  have hevolA (t : ℝ) (ht : t ∈ Set.Ioc 0 T) (x : M) :=
    smoothSectionExtension_evolution hJ R hRslice (S.family.metric t) (cov t)
      (hTJ ⟨ht.1.le, ht.2⟩) x
      (fun B => (curvatureOperatorReactionEndomorphism3 B.toLinearMap).toContinuousLinearMap)
      (hevolR t (hTJ ⟨ht.1.le, ht.2⟩) x)
  have hAspace := smoothSectionExtension_spacetime
    (fun q (hq : q ∈ Set.Ioo 0 T) => hTJ ⟨hq.1.le, hq.2.le⟩) R hRslice
    (traceNormalizedCurvatureEndomorphism_pullback_contMDiffOnSpacetimeEndomorphism
      S hS ι hJD hι)
  refine ⟨A, cov, inferInstance, hcov, hAeq, ?_, hAspace, hAsymm, hApos, hAcont, hevolA⟩
  intro t ht
  exact ⟨hιslice t ht, connectionExtension_eq _ hzJ ht⟩

private theorem curvature_pullback_rank_spreading
    [ConnectedSpace M]
    {D : RealTimeInterval} (S : SolutionOn (I := I) (M := M) D) (hS : IsSolutionOn S)
    (hdim : Module.finrank ℝ F = 3)
    {J : Set ℝ} (hJ : IsOpen J) (hJD : J ⊆ D.regular)
    {T : ℝ} (hT : 0 < T) (hTJ : Set.Icc 0 T ⊆ J)
    (ι : ℝ → ∀ x, V x ≃L[ℝ] TangentSpace I x)
    (hι : ContMDiffOn (𝓘(ℝ, ℝ).prod I) (I.prod 𝓘(ℝ, F →L[ℝ] E)) ∞
      (fun p : ℝ × M => TotalSpace.mk' (F →L[ℝ] E) p.2
        (E := fun x => V x →L[ℝ] TangentSpace I x)
        (ι p.1 p.2).toContinuousLinearMap) (J ×ˢ (Set.univ : Set M)))
    (hmetric : ∀ t ∈ J, ∀ x v w, (S.family.metric t).inner x (ι t x v) (ι t x w) = ⟪v, w⟫)
    (hode : ∀ x v, ∀ t ∈ J, HasDerivWithinAt (fun s => ι s x v)
      (ricciSharp (I := I) (S.family.metric t) x (ι t x v)) J t)
    (hR : ∀ t ∈ Set.Icc 0 T, ∀ x,
      (⟨metricRm04At (S.family.metric t) x,
        metricRm04At_mem_algebraicCurvatureTensorSubmodule (S.family.metric t) x⟩ :
          algebraicCurvatureTensorSubmodule (I := I) (M := M) x) ∈
            algebraicCurvatureOperatorNonnegativeCone (I := I) (M := M)) :
    letI : ∀ x, FiniteDimensional ℝ (V x) := fun x => VectorBundle.finiteDimensional ℝ F V x
    let R := fun t x => exteriorPower.traceNormalizedCurvatureEndomorphism
      ((S.base.rm04 t x).compContinuousLinearMap (fun _ => (ι t x).toContinuousLinearMap))
      (riemann_pullback_isAlgCurvForm S t x (ι t x))
    ∀ s t, 0 ≤ s → s < t → t ≤ T → ∀ x y,
      Module.finrank ℝ (R s x).range ≤ Module.finrank ℝ (R t y).range := by
  dsimp only
  let _ : ∀ x, FiniteDimensional ℝ (V x) := fun x => VectorBundle.finiteDimensional ℝ F V x
  let _ := Bundle.ExteriorPower.totalSpaceTopology F V 2
  let _ := Bundle.ExteriorPower.fiberBundle F V 2
  let _ := Bundle.ExteriorPower.vector_bundle F V 2
  let _ := Bundle.ExteriorPower.contMDiffVectorBundle (IB := I) (n := ∞) F V 2
  let _ := Bundle.ExteriorPower.isContMDiffRiemannianBundle (IB := I) (n := ∞) F V 2
  let R := fun t x => exteriorPower.traceNormalizedCurvatureEndomorphism
    ((S.base.rm04 t x).compContinuousLinearMap (fun _ => (ι t x).toContinuousLinearMap))
    (riemann_pullback_isAlgCurvForm S t x (ι t x))
  obtain ⟨A, cov, hcovsmooth, hcov, hAeq, hcov_eq, hAspace, hAsymm, hApos, hAcont, hevolA⟩ :=
    exists_curvature_pullback_evolution S hS hdim hJ hJD hT hTJ ι hι hmetric hode hR
  let _ := hcovsmooth
  obtain ⟨x₀⟩ := (inferInstance : Nonempty M)
  have hE : Module.finrank ℝ E = 3 := by
    calc
      Module.finrank ℝ E = Module.finrank ℝ (V x₀) := (ι 0 x₀).toLinearEquiv.finrank_eq.symm
      _ = Module.finrank ℝ F := VectorBundle.finrank_eq ℝ F V x₀
      _ = 3 := hdim
  let _ : NeZero (Module.finrank ℝ E) := ⟨by omega⟩
  let G : MetricConnectionFamily (I := I) (M := M) ℝ :=
    ⟨S.family.metric, fun t => LeviCivita (S.family.metric t),
      fun t => leviCivitaConnectionOfMetric_isMetricCompatible (S.family.metric t)⟩
  have hconn : ∀ t ∈ Set.Icc 0 T, G.connection t = LeviCivita (G.metric t) := by
    intro t _
    rfl
  have hzero : ContinuousOn (fun p : ℝ × M =>
      (TotalSpace.mk' E p.2 (0 : TangentSpace I p.2) : TangentBundle I M))
      (Set.Icc 0 T ×ˢ (Set.univ : Set M)) := by
    exact ((Bundle.contMDiff_zeroSection ℝ (TangentSpace I) (IB := I) (F := E)
      (n := ∞)).continuous.comp continuous_snd).continuousOn
  intro s t hs hst ht x y
  have hmain := DifferentialGeometry.Analysis.Parabolic.curvatureOperator_finrank_range_le_at_later_time
    G cov hcov hT A hAsymm hApos hAcont (fun _ _ => 0)
    hS.smoothMetric (hTJ.trans hJD) hzero hconn (by
      intro q hq z
      simpa only [map_zero, add_zero] using hevolA q hq z) hs hst ht x y
  change Module.finrank ℝ (R s x).range ≤ Module.finrank ℝ (R t y).range
  rw [hAeq s (hTJ ⟨hs, hst.le.trans ht⟩) x,
    hAeq t (hTJ ⟨hs.trans hst.le, ht⟩) y] at hmain
  exact hmain

omit [FiniteDimensional ℝ E] [I.Boundaryless] [IsManifold I ∞ M] [T2Space M]
    [FiniteDimensional ℝ F] [VectorBundle ℝ F V] [ContMDiffVectorBundle ∞ F V I]
    [IsContMDiffRiemannianBundle I ∞ F V] in
private theorem kernel_parallel_congr
    (cov cov' : CovariantDerivative I F V) (hcov : cov = cov')
    (A B : ∀ x, V x →L[ℝ] V x) (hAB : ∀ x, A x = B x)
    (h : IsCovariantlyInvariantSubmoduleFamily cov (fun x => (A x).ker)) :
    IsCovariantlyInvariantSubmoduleFamily cov' (fun x => (B x).ker) := by
  have hfun : (fun x => (A x).ker) = (fun x => (B x).ker) := by
    funext x
    rw [hAB x]
  rw [hcov, hfun] at h
  exact h

private theorem curvature_pullback_rank_and_kernel
    [ConnectedSpace M]
    {D : RealTimeInterval} (S : SolutionOn (I := I) (M := M) D) (hS : IsSolutionOn S)
    (hdim : Module.finrank ℝ F = 3)
    {J : Set ℝ} (hJ : IsOpen J) (hJD : J ⊆ D.regular)
    {T : ℝ} (hT : 0 < T) (hTJ : Set.Icc 0 T ⊆ J)
    (ι : ℝ → ∀ x, V x ≃L[ℝ] TangentSpace I x)
    (hι : ContMDiffOn (𝓘(ℝ, ℝ).prod I) (I.prod 𝓘(ℝ, F →L[ℝ] E)) ∞
      (fun p : ℝ × M => TotalSpace.mk' (F →L[ℝ] E) p.2
        (E := fun x => V x →L[ℝ] TangentSpace I x)
        (ι p.1 p.2).toContinuousLinearMap) (J ×ˢ (Set.univ : Set M)))
    (hmetric : ∀ t ∈ J, ∀ x v w, (S.family.metric t).inner x (ι t x v) (ι t x w) = ⟪v, w⟫)
    (hode : ∀ x v, ∀ t ∈ J, HasDerivWithinAt (fun s => ι s x v)
      (ricciSharp (I := I) (S.family.metric t) x (ι t x v)) J t)
    (hR : ∀ t ∈ Set.Icc 0 T, ∀ x,
      (⟨metricRm04At (S.family.metric t) x,
        metricRm04At_mem_algebraicCurvatureTensorSubmodule (S.family.metric t) x⟩ :
          algebraicCurvatureTensorSubmodule (I := I) (M := M) x) ∈
            algebraicCurvatureOperatorNonnegativeCone (I := I) (M := M)) :
    letI : ∀ x, FiniteDimensional ℝ (V x) := fun x => VectorBundle.finiteDimensional ℝ F V x
    letI := Bundle.ExteriorPower.totalSpaceTopology F V 2
    letI := Bundle.ExteriorPower.fiberBundle F V 2
    letI := Bundle.ExteriorPower.vector_bundle F V 2
    letI := Bundle.ExteriorPower.contMDiffVectorBundle (IB := I) (n := ∞) F V 2
    letI := Bundle.ExteriorPower.isContMDiffRiemannianBundle (IB := I) (n := ∞) F V 2
    let R := fun t x => exteriorPower.traceNormalizedCurvatureEndomorphism
      ((S.base.rm04 t x).compContinuousLinearMap (fun _ => (ι t x).toContinuousLinearMap))
      (riemann_pullback_isAlgCurvForm S t x (ι t x))
    (∀ t ∈ Ioc 0 T, ∀ x y,
      Module.finrank ℝ (R t x).range = Module.finrank ℝ (R t y).range) ∧
    (∀ t ∈ Ioc 0 T, ∃ ε ∈ Ioc 0 t, ∀ s ∈ Ioc (t - ε) t, ∀ x,
      (R s x).ker = (R t x).ker ∧ (R s x).range = (R t x).range) ∧
    (∀ t ∈ Ioc 0 T, ∀ x v, R t x v = 0 →
      curvatureOperatorReactionEndomorphism3 (R t x).toLinearMap v = 0) ∧
    (∀ t ∈ Ioc 0 T, ∀ x, Module.finrank ℝ (R t x).range = 0 ∨
      Module.finrank ℝ (R t x).range = 1 ∨ Module.finrank ℝ (R t x).range = 3) ∧
    (∀ t ∈ Ioc 0 T, ∃ hιt : ContMDiff I (I.prod 𝓘(ℝ, F →L[ℝ] E)) ∞
      (fun x => TotalSpace.mk' (F →L[ℝ] E) x (ι t x).toContinuousLinearMap),
      IsCovariantlyInvariantSubmoduleFamily
        ((CovariantDerivative.pullbackFiberwiseLinearEquiv
          (fun x => (ι t x).toLinearEquiv)
          (hιt.of_le (show (1 : ℕ∞ω) ≤ ∞ by simp)).clm_bundle_map
          (LeviCivita (S.family.metric t))).exteriorPower 2) (fun x => (R t x).ker)) := by
  dsimp only
  let _ : ∀ x, FiniteDimensional ℝ (V x) := fun x => VectorBundle.finiteDimensional ℝ F V x
  let _ := Bundle.ExteriorPower.totalSpaceTopology F V 2
  let _ := Bundle.ExteriorPower.fiberBundle F V 2
  let _ := Bundle.ExteriorPower.vector_bundle F V 2
  let _ := Bundle.ExteriorPower.contMDiffVectorBundle (IB := I) (n := ∞) F V 2
  let _ := Bundle.ExteriorPower.isContMDiffRiemannianBundle (IB := I) (n := ∞) F V 2
  let R := fun t x => exteriorPower.traceNormalizedCurvatureEndomorphism
    ((S.base.rm04 t x).compContinuousLinearMap (fun _ => (ι t x).toContinuousLinearMap))
    (riemann_pullback_isAlgCurvForm S t x (ι t x))
  obtain ⟨A, cov, hcovsmooth, hcov, hAeq, hcov_eq, hAspace, hAsymm, hApos, hAcont, hevolA⟩ :=
    exists_curvature_pullback_evolution S hS hdim hJ hJD hT hTJ ι hι hmetric hode hR
  let _ := hcovsmooth
  obtain ⟨x₀⟩ := (inferInstance : Nonempty M)
  have hE : Module.finrank ℝ E = 3 := by
    calc
      Module.finrank ℝ E = Module.finrank ℝ (V x₀) := (ι 0 x₀).toLinearEquiv.finrank_eq.symm
      _ = Module.finrank ℝ F := VectorBundle.finrank_eq ℝ F V x₀
      _ = 3 := hdim
  let _ : NeZero (Module.finrank ℝ E) := ⟨by omega⟩
  let G : MetricConnectionFamily (I := I) (M := M) ℝ :=
    ⟨S.family.metric, fun t => LeviCivita (S.family.metric t),
      fun t => leviCivitaConnectionOfMetric_isMetricCompatible (S.family.metric t)⟩
  have hconn : ∀ t ∈ Set.Icc 0 T, G.connection t = LeviCivita (G.metric t) := by
    intro t _
    rfl
  have hzero : ContinuousOn (fun p : ℝ × M =>
      (TotalSpace.mk' E p.2 (0 : TangentSpace I p.2) : TangentBundle I M))
      (Set.Icc 0 T ×ˢ (Set.univ : Set M)) := by
    exact ((Bundle.contMDiff_zeroSection ℝ (TangentSpace I) (IB := I) (F := E)
      (n := ∞)).continuous.comp continuous_snd).continuousOn
  have hevol : ∀ q ∈ Ioc 0 T, ∀ z, HasDerivAt (fun s => A s z)
      (rawBundleEndomorphismConnLap (G.metric q) (cov q) (fun y => A q y) z +
        HomConnectionGen.homBundleCovariantDerivativeGen I M
          (⋀[ℝ]^2 F) (fun y => ⋀[ℝ]^2 (V y)) (⋀[ℝ]^2 F) (fun y => ⋀[ℝ]^2 (V y))
          (cov q) (cov q) (fun y => A q y) z 0 +
        (curvatureOperatorReactionEndomorphism3 (A q z).toLinearMap).toContinuousLinearMap) q := by
    intro q hq z
    simpa only [map_zero, add_zero] using hevolA q hq z
  have hAeq' (q : ℝ) (hq : q ∈ Ioc 0 T) := hAeq q (hTJ ⟨hq.1.le, hq.2⟩)
  have hrank := DifferentialGeometry.Analysis.Parabolic.curvatureOperator_rank_spatially_constant_and_locally_constant_from_left
    G cov hcov hT A hAsymm hApos hAcont (fun _ _ => 0)
    hS.smoothMetric (hTJ.trans hJD) hzero hconn hevol
  have hkernel (t : ℝ) (ht : t ∈ Ioc 0 T) := DifferentialGeometry.Analysis.Parabolic.curvatureOperator_kernel_and_range_locally_constant_from_left
    G cov hcov hT A hAsymm hApos hAcont hAspace (fun _ _ => 0)
    hS.smoothMetric (hTJ.trans hJD) hzero hconn hevol ht
  have hreaction (t : ℝ) (ht : t ∈ Ioc 0 T) := DifferentialGeometry.Analysis.Parabolic.curvatureOperator_reaction_annihilates_kernel_at_positive_time
    G cov hcov hT A hAsymm hApos hAcont hAspace (fun _ _ => 0)
    hS.smoothMetric (hTJ.trans hJD) hzero hconn hevol ht
  have hF : Module.finrank ℝ (⋀[ℝ]^2 F) = 3 := by
    rw [exteriorPower.finrank_eq, hdim]
    decide
  have htri (t : ℝ) (ht : t ∈ Ioc 0 T) := DifferentialGeometry.Analysis.Parabolic.curvatureOperator_finrank_range_trichotomy_at_positive_time
    hF G cov hcov hT A hAsymm hApos hAcont hAspace (fun _ _ => 0)
    hS.smoothMetric (hTJ.trans hJD) hzero hconn hevol ht
  have hparallel (t : ℝ) (ht : t ∈ Ioc 0 T) := DifferentialGeometry.Analysis.Parabolic.curvatureOperator_kernel_parallel_at_positive_time
    G cov hcov hT A hAsymm hApos hAcont hAspace (fun _ _ => 0)
    hS.smoothMetric (hTJ.trans hJD) hzero hconn hevol ht
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro t ht x y
    have h := hrank.1 t ht x y
    rw [hAeq' t ht x, hAeq' t ht y] at h
    exact h
  · intro t ht
    obtain ⟨ε, hε, hk⟩ := hkernel t ht
    refine ⟨ε, hε, ?_⟩
    intro q hq x
    have hqT : q ∈ Ioc 0 T := ⟨by linarith [hε.2, hq.1], hq.2.trans ht.2⟩
    have h := hk q hq x
    rw [hAeq' q hqT x, hAeq' t ht x] at h
    exact h
  · intro t ht x v hv
    have hvA : A t x v = 0 := by rw [hAeq' t ht x]; exact hv
    have h := hreaction t ht x v hvA
    rw [hAeq' t ht x] at h
    exact h
  · intro t ht x
    have h := htri t ht x
    rw [hAeq' t ht x] at h
    exact h
  · intro t ht
    obtain ⟨hιt, hc⟩ := hcov_eq t (hTJ ⟨ht.1.le, ht.2⟩)
    refine ⟨hιt, ?_⟩
    exact kernel_parallel_congr (cov t) _ hc (fun x => A t x) (R t)
      (hAeq' t ht) (hparallel t ht)

theorem exists_uhlenbeck_isometry_with_curvatureOperator_rank_and_kernel
    [ConnectedSpace M]
    {D : RealTimeInterval} (S : SolutionOn (I := I) (M := M) D) (hS : IsSolutionOn S)
    (hdim : Module.finrank ℝ F = 3)
    {T : ℝ} (hT : 0 < T) (hreg : Set.Icc 0 T ⊆ D.regular)
    (ι₀ : ∀ x, V x ≃L[ℝ] TangentSpace I x)
    (hι₀ : ContMDiff I (I.prod 𝓘(ℝ, F →L[ℝ] E)) ∞
      (fun x => TotalSpace.mk' (F →L[ℝ] E) x (ι₀ x).toContinuousLinearMap))
    (h₀ : ∀ x v w, (S.family.metric 0).inner x (ι₀ x v) (ι₀ x w) = ⟪v, w⟫)
    (hR : ∀ t ∈ Set.Icc 0 T, ∀ x,
      (⟨metricRm04At (S.family.metric t) x,
        metricRm04At_mem_algebraicCurvatureTensorSubmodule (S.family.metric t) x⟩ :
          algebraicCurvatureTensorSubmodule (I := I) (M := M) x) ∈
            algebraicCurvatureOperatorNonnegativeCone (I := I) (M := M)) :
    ∃ ι : ℝ → ∀ x, V x ≃L[ℝ] TangentSpace I x,
      (∀ x, ι 0 x = ι₀ x) ∧
      ContMDiffOn (𝓘(ℝ, ℝ).prod I) (I.prod 𝓘(ℝ, F →L[ℝ] E)) ∞
        (fun p : ℝ × M => TotalSpace.mk' (F →L[ℝ] E) p.2
          (E := fun x => V x →L[ℝ] TangentSpace I x)
          (ι p.1 p.2).toContinuousLinearMap) (Set.Icc 0 T ×ˢ (Set.univ : Set M)) ∧
      ContMDiffOn (𝓘(ℝ, ℝ).prod I) (I.prod 𝓘(ℝ, E →L[ℝ] F)) ∞
        (fun p : ℝ × M => TotalSpace.mk' (E →L[ℝ] F) p.2
          (E := fun x => TangentSpace I x →L[ℝ] V x)
          (ι p.1 p.2).symm.toContinuousLinearMap) (Set.Icc 0 T ×ˢ (Set.univ : Set M)) ∧
      (∀ x v, ∀ t ∈ Set.Icc 0 T, HasDerivWithinAt (fun s => ι s x v)
        (ricciSharp (I := I) (S.family.metric t) x (ι t x v)) (Set.Icc 0 T) t) ∧
      (∀ t ∈ Set.Icc 0 T, ∀ x v w,
        (S.family.metric t).inner x (ι t x v) (ι t x w) = ⟪v, w⟫) ∧
      (letI : ∀ x, FiniteDimensional ℝ (V x) := fun x => VectorBundle.finiteDimensional ℝ F V x
       letI := Bundle.ExteriorPower.totalSpaceTopology F V 2
       letI := Bundle.ExteriorPower.fiberBundle F V 2
       letI := Bundle.ExteriorPower.vector_bundle F V 2
       letI := Bundle.ExteriorPower.contMDiffVectorBundle (IB := I) (n := ∞) F V 2
       letI := Bundle.ExteriorPower.isContMDiffRiemannianBundle (IB := I) (n := ∞) F V 2
       let R := fun t x => exteriorPower.traceNormalizedCurvatureEndomorphism
         ((S.base.rm04 t x).compContinuousLinearMap (fun _ => (ι t x).toContinuousLinearMap))
         (riemann_pullback_isAlgCurvForm S t x (ι t x))
       (∀ s t, 0 ≤ s → s < t → t ≤ T → ∀ x y,
         Module.finrank ℝ (R s x).range ≤ Module.finrank ℝ (R t y).range) ∧
    (∀ t ∈ Ioc 0 T, ∀ x y,
      Module.finrank ℝ (R t x).range = Module.finrank ℝ (R t y).range) ∧
    (∀ t ∈ Ioc 0 T, ∃ ε ∈ Ioc 0 t, ∀ s ∈ Ioc (t - ε) t, ∀ x,
      (R s x).ker = (R t x).ker ∧ (R s x).range = (R t x).range) ∧
    (∀ t ∈ Ioc 0 T, ∀ x v, R t x v = 0 →
      curvatureOperatorReactionEndomorphism3 (R t x).toLinearMap v = 0) ∧
    (∀ t ∈ Ioc 0 T, ∀ x, Module.finrank ℝ (R t x).range = 0 ∨
      Module.finrank ℝ (R t x).range = 1 ∨ Module.finrank ℝ (R t x).range = 3) ∧
    (∀ t ∈ Ioc 0 T, ∃ hιt : ContMDiff I (I.prod 𝓘(ℝ, F →L[ℝ] E)) ∞
      (fun x => TotalSpace.mk' (F →L[ℝ] E) x (ι t x).toContinuousLinearMap),
      IsCovariantlyInvariantSubmoduleFamily
        ((CovariantDerivative.pullbackFiberwiseLinearEquiv
          (fun x => (ι t x).toLinearEquiv)
          (hιt.of_le (show (1 : ℕ∞ω) ≤ ∞ by simp)).clm_bundle_map
          (LeviCivita (S.family.metric t))).exteriorPower 2) (fun x => (R t x).ker))) := by
  obtain ⟨a, b, hTJ, hJD⟩ := exists_Ioo_superset_Icc_of_isOpen
    D.regular_isOpen hT.le hreg
  obtain ⟨ι, hinit, hsmooth, hinverse, hode, hmetric⟩ :=
    exists_uhlenbeck_isometry_on_interval (F := F) (V := V) S hS
      (J := Set.Ioo a b) (t₀ := 0) Set.ordConnected_Ioo (hTJ ⟨le_rfl, hT.le⟩) hJD
      (RiemannianMetric.ofInnerProductSpace V) ι₀ hι₀ h₀
  refine ⟨ι, hinit, hsmooth.mono (Set.prod_mono hTJ Set.Subset.rfl),
    hinverse.mono (Set.prod_mono hTJ Set.Subset.rfl), ?_, ?_, ?_⟩
  · intro x v t ht
    exact (hode x v t (hTJ ht)).mono hTJ
  · exact fun t ht => hmetric t (hTJ ht)
  · exact ⟨curvature_pullback_rank_spreading S hS hdim isOpen_Ioo hJD hT hTJ
      ι hsmooth hmetric hode hR,
      curvature_pullback_rank_and_kernel S hS hdim isOpen_Ioo hJD hT hTJ
        ι hsmooth hmetric hode hR⟩

end DifferentialGeometry.PDE.RicciFlow
