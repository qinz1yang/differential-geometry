import DifferentialGeometry.Geometry.Curvature.CurvatureOperator.ExteriorSmooth
import DifferentialGeometry.Geometry.Connection.LeviCivita.Pullback
import DifferentialGeometry.Geometry.Flow.RicciFlow.Estimates.Uhlenbeck.PulledCurvatureEvolution
import DifferentialGeometry.Geometry.Curvature.Algebraic.TensorMetric
import DifferentialGeometry.Analysis.Calculus.InjectiveDerivative
import DifferentialGeometry.Geometry.Connection.Laplacian.ExteriorEndomorphism
import DifferentialGeometry.Geometry.Curvature.DimensionThree.ExteriorReaction
import DifferentialGeometry.Analysis.Parabolic.CurvatureOperatorEvolution

set_option autoImplicit false

noncomputable section

open Bundle
open DifferentialGeometry DifferentialGeometry.Geometry.Connection
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Curvature.DimensionThree
open DifferentialGeometry.Tensor0SBundle
open scoped Bundle Manifold ContDiff RealInnerProductSpace

namespace DifferentialGeometry.PDE.RicciFlow

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M]

private theorem riemann_pullback_isAlgCurvForm
    {D : RealTimeInterval} (S : SolutionOn (I := I) (M := M) D) (t : ℝ) (x : M)
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (ι : F ≃L[ℝ] TangentSpace I x) :
    IsAlgCurvForm (fun a b c d =>
      (S.base.rm04 t x).compContinuousLinearMap (fun _ => ι.toContinuousLinearMap) ![a, b, c, d]) := by
  have hT := mem_algebraicCurvatureTensorSubmodule.mp
    (metricRm04At_mem_algebraicCurvatureTensorSubmodule (I := I) (S.base.metric t) x)
  change IsAlgCurvForm (fun a b c d => S.base.rm04 t x ![a, b, c, d]) at hT
  exact hT.compContinuousLinearMap ι.toContinuousLinearMap

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]
  {V : M → Type*} [TopologicalSpace (TotalSpace F V)]
  [∀ x, NormedAddCommGroup (V x)] [∀ x, InnerProductSpace ℝ (V x)]
  [FiberBundle F V] [VectorBundle ℝ F V] [ContMDiffVectorBundle ∞ F V I]
  [IsContMDiffRiemannianBundle I ∞ F V]

omit [ContMDiffVectorBundle ∞ F V I] [IsContMDiffRiemannianBundle I ∞ F V] in
private theorem riemann_pullback_contMDiff
    {D : RealTimeInterval} (S : SolutionOn (I := I) (M := M) D) (t : ℝ)
    (ι : ∀ x, V x ≃L[ℝ] TangentSpace I x)
    (hι : ContMDiff I (I.prod 𝓘(ℝ, F →L[ℝ] E)) ∞
      (fun x => TotalSpace.mk' (F →L[ℝ] E) x (ι x).toContinuousLinearMap)) :
    ContMDiff I (I.prod 𝓘(ℝ, ContinuousMultilinearMap ℝ (fun _ : Fin 4 => F) ℝ)) ∞
      (fun x => TotalSpace.mk'
        (ContinuousMultilinearMap ℝ (fun _ : Fin 4 => F) ℝ)
        (E := Bundle.continuousMultilinearMap ℝ 4 F V) x
        ((S.base.rm04 t x).compContinuousLinearMap (fun _ => (ι x).toContinuousLinearMap))) := by
  exact (S.base.rm04 t).contMDiff.multilinear_bundle_comp (fun _ => hι)

end DifferentialGeometry.PDE.RicciFlow

namespace DifferentialGeometry.PDE.RicciFlow

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M]
  {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]
  {V : M → Type*} [TopologicalSpace (TotalSpace F V)]
  [∀ x, NormedAddCommGroup (V x)] [∀ x, InnerProductSpace ℝ (V x)]
  [FiberBundle F V] [VectorBundle ℝ F V] [ContMDiffVectorBundle ∞ F V I]
  [IsContMDiffRiemannianBundle I ∞ F V]

theorem traceNormalizedCurvatureEndomorphism_pullback_hasDerivWithinAt_of_evolution
    {D : RealTimeInterval} (S : SolutionOn (I := I) (M := M) D)
    (t : ℝ)
    (ι : ℝ → ∀ x, V x ≃L[ℝ] TangentSpace I x) {J : Set ℝ}
    (hι : ContMDiff I (I.prod 𝓘(ℝ, F →L[ℝ] E)) ∞
      (fun x => TotalSpace.mk' (F →L[ℝ] E) x (ι t x).toContinuousLinearMap))
    (hmetric : ∀ x v w, (S.family.metric t).inner x (ι t x v) (ι t x w) = ⟪v, w⟫)
    (x : M) (hdim : Module.finrank ℝ (V x) = 3)
    (hRm : HasDerivWithinAt (fun s => S.base.rm04 s x)
      (roughLap0SField (S.family.metric t) (S.base.rm04 t) x -
        (2 : ℝ) • curvatureQuadraticCombination (S.family.metric t) (S.base.rm04 t) x -
        ricciDrift04 (S.family.metric t) x) J t)
    (hode : ∀ v, HasDerivWithinAt (fun s => ι s x v)
      (ricciSharp (I := I) (S.family.metric t) x (ι t x v)) J t) :
    letI : ∀ y, FiniteDimensional ℝ (V y) := fun y => VectorBundle.finiteDimensional ℝ F V y
    letI := Bundle.ExteriorPower.totalSpaceTopology F V 2
    letI := Bundle.ExteriorPower.fiberBundle F V 2
    letI := Bundle.ExteriorPower.vector_bundle F V 2
    letI := Bundle.ExteriorPower.contMDiffVectorBundle (IB := I) (n := ∞) F V 2
    let hι₁ := hι.of_le (show (1 : ℕ∞ω) ≤ ∞ from by simp)
    let cov := CovariantDerivative.pullbackFiberwiseLinearEquiv
      (fun y => (ι t y).toLinearEquiv) hι₁.clm_bundle_map (LeviCivita (S.family.metric t))
    let R := fun s y => exteriorPower.traceNormalizedCurvatureEndomorphism
      ((S.base.rm04 s y).compContinuousLinearMap (fun _ => (ι s y).toContinuousLinearMap))
      (riemann_pullback_isAlgCurvForm S s y (ι s y))
    HasDerivWithinAt (fun s => R s x)
      (rawBundleEndomorphismConnLap (S.family.metric t) (cov.exteriorPower 2) (R t) x +
        (curvatureOperatorReactionEndomorphism3 (R t x).toLinearMap).toContinuousLinearMap) J t := by
  dsimp only
  let : ∀ y, FiniteDimensional ℝ (V y) := fun y => VectorBundle.finiteDimensional ℝ F V y
  let := Bundle.ExteriorPower.totalSpaceTopology F V 2
  let := Bundle.ExteriorPower.fiberBundle F V 2
  let := Bundle.ExteriorPower.vector_bundle F V 2
  let := Bundle.ExteriorPower.contMDiffVectorBundle (IB := I) (n := ∞) F V 2
  let hι₁ := hι.of_le (show (1 : ℕ∞ω) ≤ ∞ from by simp)
  let cov := CovariantDerivative.pullbackFiberwiseLinearEquiv
    (fun y => (ι t y).toLinearEquiv) hι₁.clm_bundle_map (LeviCivita (S.family.metric t))
  let T := fun s y => (S.base.rm04 s y).compContinuousLinearMap
    (fun _ => (ι s y).toContinuousLinearMap)
  let hT := fun s y => riemann_pullback_isAlgCurvForm S s y (ι s y)
  let R := fun s y => exteriorPower.traceNormalizedCurvatureEndomorphism (T s y) (hT s y)
  have hTsmooth := riemann_pullback_contMDiff S t (ι t) hι
  have hRsmooth := Bundle.ExteriorPower.contMDiff_traceNormalizedCurvatureEndomorphism F V
    2 (WithTop.coe_le_coe.mpr le_top) (T t) (hT t)
      (hTsmooth.of_le (WithTop.coe_le_coe.mpr le_top))
  let : CompleteSpace F := FiniteDimensional.complete ℝ F
  have hιinv : ContMDiff I (I.prod 𝓘(ℝ, E →L[ℝ] F)) ∞
      (fun y => TotalSpace.mk' (E →L[ℝ] F) y (ι t y).symm.toContinuousLinearMap) := by
    simpa only [ContinuousLinearMap.inverse_equiv] using
      hι.clm_bundle_inverse (fun _ => ContinuousLinearMap.isInvertible_equiv)
  let hcov : CovariantDerivative.ContMDiffCovariantDerivative cov ∞ :=
    CovariantDerivative.ContMDiffCovariantDerivative.pullbackFiberwiseLinearEquiv
      (fun y => (ι t y).toLinearEquiv) hι.clm_bundle_map hιinv.clm_bundle_map
      (LeviCivita (S.family.metric t))
  have hcompat : cov.IsMetricCompatible :=
    CovariantDerivative.isMetricCompatible_pullback_leviCivita
      (S.family.metric t) (ι t) hι₁ hmetric
  let L := (exteriorPower.endomorphismTensorLinear (E := V x) 2).toContinuousLinearMap
  apply L.hasDerivWithinAt_of_injective (exteriorPower.endomorphismTensor_injective 2)
  have hd := riemann_pullback_tensor_hasDerivWithinAt_laplacian_of_evolution
    S t ι hι₁ x hRm hode
  have hrep : (fun y => exteriorPower.endomorphismTensor 2 (R t y)) =
      (fun y => (-2 : ℝ) • T t y) := by
    funext y
    exact exteriorPower.endomorphismTensor_traceNormalizedCurvatureEndomorphism (T t y) (hT t y)
  have hlap := hcompat.rawBundleConnLap_multilinear_endomorphismTensor 2
    (S.family.metric t) (R t) hRsmooth x
  rw [hrep, rawBundleConnLap_const_smul (S.family.metric t) (cov.multilinear 4)
    inferInstance (T t) (hTsmooth.of_le (WithTop.coe_le_coe.mpr le_top)) (-2) x] at hlap
  have hreaction := endomorphismTensor_curvatureOperatorReactionEndomorphism3_pullback
    (S.family.metric t) x (ι t x) (hmetric x) hdim (S.base.rm04 t)
    (by
      convert hT t x using 1
      ext a c d e
      change S.base.rm04 t x ![ι t x a, ι t x c, ι t x d, ι t x e] =
        S.base.rm04 t x (fun q => ι t x (![a, c, d, e] q))
      congr 1
      ext q
      fin_cases q <;> rfl)
  convert hd.const_smul (-2 : ℝ) using 1
  · funext s
    exact exteriorPower.endomorphismTensor_traceNormalizedCurvatureEndomorphism (T s x) (hT s x)
  · rw [map_add]
    change exteriorPower.endomorphismTensor 2
        (rawBundleEndomorphismConnLap (S.family.metric t) (cov.exteriorPower 2) (R t) x) +
        exteriorPower.endomorphismTensor 2
          (curvatureOperatorReactionEndomorphism3 (R t x).toLinearMap).toContinuousLinearMap = _
    erw [rawBundleEndomorphismConnLap_def, ← hlap, hreaction]
    module

theorem traceNormalizedCurvatureEndomorphism_pullback_hasDerivWithinAt_of_ricci_ode
    {D : RealTimeInterval} (S : SolutionOn (I := I) (M := M) D)
    (hS : IsSolutionOn S) (t : D.RegularTime)
    (ι : ℝ → ∀ x, V x ≃L[ℝ] TangentSpace I x) {J : Set ℝ}
    (hι : ContMDiff I (I.prod 𝓘(ℝ, F →L[ℝ] E)) ∞
      (fun x => TotalSpace.mk' (F →L[ℝ] E) x (ι t x).toContinuousLinearMap))
    (hmetric : ∀ x v w, (S.family.metric t).inner x (ι t x v) (ι t x w) = ⟪v, w⟫)
    (x : M) (hdim : Module.finrank ℝ (V x) = 3)
    (hode : ∀ v, HasDerivWithinAt (fun s => ι s x v)
      (ricciSharp (I := I) (S.family.metric t) x (ι t x v)) J t) :
    letI : ∀ y, FiniteDimensional ℝ (V y) := fun y => VectorBundle.finiteDimensional ℝ F V y
    letI := Bundle.ExteriorPower.totalSpaceTopology F V 2
    letI := Bundle.ExteriorPower.fiberBundle F V 2
    letI := Bundle.ExteriorPower.vector_bundle F V 2
    letI := Bundle.ExteriorPower.contMDiffVectorBundle (IB := I) (n := ∞) F V 2
    let hι₁ := hι.of_le (show (1 : ℕ∞ω) ≤ ∞ from by simp)
    let cov := CovariantDerivative.pullbackFiberwiseLinearEquiv
      (fun y => (ι t y).toLinearEquiv) hι₁.clm_bundle_map (LeviCivita (S.family.metric t))
    let R := fun s y => exteriorPower.traceNormalizedCurvatureEndomorphism
      ((S.base.rm04 s y).compContinuousLinearMap (fun _ => (ι s y).toContinuousLinearMap))
      (riemann_pullback_isAlgCurvForm S s y (ι s y))
    HasDerivWithinAt (fun s => R s x)
      (rawBundleEndomorphismConnLap (S.family.metric t) (cov.exteriorPower 2) (R t) x +
        (curvatureOperatorReactionEndomorphism3 (R t x).toLinearMap).toContinuousLinearMap) J t :=
  traceNormalizedCurvatureEndomorphism_pullback_hasDerivWithinAt_of_evolution S t ι hι hmetric x hdim
    (riemann_tensor_hasDerivAt_of_solution S hS t x).hasDerivWithinAt hode

end DifferentialGeometry.PDE.RicciFlow

namespace DifferentialGeometry.PDE.RicciFlow

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M]
  {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]
  {V : M → Type*} [TopologicalSpace (TotalSpace F V)]
  [∀ x, NormedAddCommGroup (V x)] [∀ x, InnerProductSpace ℝ (V x)]
  [FiberBundle F V] [VectorBundle ℝ F V] [ContMDiffVectorBundle ∞ F V I]
  [IsContMDiffRiemannianBundle I ∞ F V]

theorem exists_uhlenbeck_isometry_with_traceNormalizedCurvatureEndomorphism_evolution
    {D : RealTimeInterval} (S : SolutionOn (I := I) (M := M) D)
    (hS : IsSolutionOn S) (hdim : Module.finrank ℝ F = 3)
    {J : Set ℝ} {t₀ : ℝ} (hJ : J.OrdConnected) (ht₀ : t₀ ∈ J)
    (hJD : J ⊆ D.regular) (ι₀ : ∀ x, V x ≃L[ℝ] TangentSpace I x)
    (hι₀ : ContMDiff I (I.prod 𝓘(ℝ, F →L[ℝ] E)) ∞
      (fun x => TotalSpace.mk' (F →L[ℝ] E) x (ι₀ x).toContinuousLinearMap))
    (h₀ : ∀ x v w, (S.family.metric t₀).inner x (ι₀ x v) (ι₀ x w) = ⟪v, w⟫) :
    ∃ ι : ℝ → ∀ x, V x ≃L[ℝ] TangentSpace I x,
      (∀ x, ι t₀ x = ι₀ x) ∧
      ContMDiffOn (𝓘(ℝ, ℝ).prod I) (I.prod 𝓘(ℝ, F →L[ℝ] E)) ∞
        (fun p : ℝ × M => TotalSpace.mk' (F →L[ℝ] E) p.2
          (E := fun x => V x →L[ℝ] TangentSpace I x)
          (ι p.1 p.2).toContinuousLinearMap) (J ×ˢ (Set.univ : Set M)) ∧
      ContMDiffOn (𝓘(ℝ, ℝ).prod I) (I.prod 𝓘(ℝ, E →L[ℝ] F)) ∞
        (fun p : ℝ × M => TotalSpace.mk' (E →L[ℝ] F) p.2
          (E := fun x => TangentSpace I x →L[ℝ] V x)
          (ι p.1 p.2).symm.toContinuousLinearMap) (J ×ˢ (Set.univ : Set M)) ∧
      (∀ x v, ∀ t ∈ J, HasDerivWithinAt (fun s => ι s x v)
        (ricciSharp (I := I) (S.family.metric t) x (ι t x v)) J t) ∧
      (∀ t ∈ J, ∀ x v w,
        (S.family.metric t).inner x (ι t x v) (ι t x w) = ⟪v, w⟫) ∧
      ∀ t ∈ J, ∃ hιt : ContMDiff I (I.prod 𝓘(ℝ, F →L[ℝ] E)) ∞
          (fun x => TotalSpace.mk' (F →L[ℝ] E) x (ι t x).toContinuousLinearMap),
        letI : ∀ y, FiniteDimensional ℝ (V y) :=
          fun y => VectorBundle.finiteDimensional ℝ F V y
        letI := Bundle.ExteriorPower.totalSpaceTopology F V 2
        letI := Bundle.ExteriorPower.fiberBundle F V 2
        letI := Bundle.ExteriorPower.vector_bundle F V 2
        letI := Bundle.ExteriorPower.contMDiffVectorBundle (IB := I) (n := ∞) F V 2
        let hι₁ := hιt.of_le (show (1 : ℕ∞ω) ≤ ∞ from by simp)
        let cov := CovariantDerivative.pullbackFiberwiseLinearEquiv
          (fun y => (ι t y).toLinearEquiv) hι₁.clm_bundle_map (LeviCivita (S.family.metric t))
        let R := fun s y => exteriorPower.traceNormalizedCurvatureEndomorphism
          ((S.base.rm04 s y).compContinuousLinearMap (fun _ => (ι s y).toContinuousLinearMap))
          (riemann_pullback_isAlgCurvForm S s y (ι s y))
        ∀ x, HasDerivWithinAt (fun s => R s x)
          (rawBundleEndomorphismConnLap (S.family.metric t) (cov.exteriorPower 2) (R t) x +
            (curvatureOperatorReactionEndomorphism3 (R t x).toLinearMap).toContinuousLinearMap)
          J t := by
  obtain ⟨ι, hinit, hsmooth, hinverse, hderiv, hmetric⟩ :=
    exists_uhlenbeck_isometry_on_interval (F := F) (V := V) S hS hJ ht₀ hJD
      (RiemannianMetric.ofInnerProductSpace V) ι₀ hι₀ h₀
  refine ⟨ι, hinit, hsmooth, hinverse, hderiv, hmetric, ?_⟩
  intro t ht
  have hpair : ContMDiff I (𝓘(ℝ, ℝ).prod I) ∞ (fun x : M => (t, x)) :=
    contMDiff_const.prodMk contMDiff_id
  have hιt := hsmooth.comp_contMDiff hpair (fun x => ⟨ht, Set.mem_univ x⟩)
  refine ⟨hιt, ?_⟩
  dsimp only
  intro x
  exact traceNormalizedCurvatureEndomorphism_pullback_hasDerivWithinAt_of_ricci_ode
    (F := F) (V := V) S hS ⟨t, hJD ht⟩ ι hιt (hmetric t ht) x
    ((VectorBundle.finrank_eq ℝ F V x).trans hdim) (fun v => hderiv x v t ht)

theorem traceNormalizedCurvatureSelfAdjoint_pullback_hasDerivWithinAt_of_evolution
    {D : RealTimeInterval} (S : SolutionOn (I := I) (M := M) D)
    (t : ℝ)
    (ι : ℝ → ∀ x, V x ≃L[ℝ] TangentSpace I x) {J : Set ℝ}
    (hι : ContMDiff I (I.prod 𝓘(ℝ, F →L[ℝ] E)) ∞
      (fun x => TotalSpace.mk' (F →L[ℝ] E) x (ι t x).toContinuousLinearMap))
    (hmetric : ∀ x v w, (S.family.metric t).inner x (ι t x v) (ι t x w) = ⟪v, w⟫)
    (x : M) (hdim : Module.finrank ℝ (V x) = 3)
    (hRm : HasDerivWithinAt (fun s => S.base.rm04 s x)
      (roughLap0SField (S.family.metric t) (S.base.rm04 t) x -
        (2 : ℝ) • curvatureQuadraticCombination (S.family.metric t) (S.base.rm04 t) x -
        ricciDrift04 (S.family.metric t) x) J t)
    (hode : ∀ v, HasDerivWithinAt (fun s => ι s x v)
      (ricciSharp (I := I) (S.family.metric t) x (ι t x v)) J t) :
    letI : ∀ y, FiniteDimensional ℝ (V y) := fun y => VectorBundle.finiteDimensional ℝ F V y
    letI := Bundle.ExteriorPower.totalSpaceTopology F V 2
    letI := Bundle.ExteriorPower.fiberBundle F V 2
    letI := Bundle.ExteriorPower.vector_bundle F V 2
    letI := Bundle.ExteriorPower.contMDiffVectorBundle (IB := I) (n := ∞) F V 2
    letI := Bundle.ExteriorPower.isContMDiffRiemannianBundle (IB := I) (n := ∞) F V 2
    let P := selfAdjointSubbundle (I := I) (F := ⋀[ℝ]^2 F)
      (V := fun y => ⋀[ℝ]^2 (V y)) (n := ∞)
    letI := P.totalSpaceTopology
    letI := P.fiberBundle
    let hι₁ := hι.of_le (show (1 : ℕ∞ω) ≤ ∞ from by simp)
    let cov := CovariantDerivative.pullbackFiberwiseLinearEquiv
      (fun y => (ι t y).toLinearEquiv) hι₁.clm_bundle_map (LeviCivita (S.family.metric t))
    let hc := CovariantDerivative.isMetricCompatible_pullback_leviCivita
      (S.family.metric t) (ι t) hι₁ hmetric
    let T := fun s y => (S.base.rm04 s y).compContinuousLinearMap
      (fun _ => (ι s y).toContinuousLinearMap)
    let hT := fun s y => riemann_pullback_isAlgCurvForm S s y (ι s y)
    let R : ℝ → ∀ y, P.fiber y := fun s y =>
      exteriorPower.traceNormalizedCurvatureSelfAdjoint (T s y) (hT s y)
    let Q : P.fiber x := curvatureOperatorReactionSelfAdjoint3 (R t x)
    HasDerivWithinAt (fun s => R s x)
      (rawBundleConnLap (F := Fin P.rank → ℝ) (V := fun y => P.fiber y)
        (S.family.metric t)
        ((cov.exteriorPower 2).selfAdjoint
          (F := ⋀[ℝ]^2 F) (V := fun y => ⋀[ℝ]^2 (V y))
          (hc.exteriorPower 2)) (R t) x + Q) J t := by
  dsimp only
  let : ∀ y, FiniteDimensional ℝ (V y) := fun y => VectorBundle.finiteDimensional ℝ F V y
  let := Bundle.ExteriorPower.totalSpaceTopology F V 2
  let := Bundle.ExteriorPower.fiberBundle F V 2
  let := Bundle.ExteriorPower.vector_bundle F V 2
  let := Bundle.ExteriorPower.contMDiffVectorBundle (IB := I) (n := ∞) F V 2
  let := Bundle.ExteriorPower.isContMDiffRiemannianBundle (IB := I) (n := ∞) F V 2
  let P := selfAdjointSubbundle (I := I) (F := ⋀[ℝ]^2 F)
    (V := fun y => ⋀[ℝ]^2 (V y)) (n := ∞)
  let := P.totalSpaceTopology
  let := P.fiberBundle
  let hι₁ := hι.of_le (show (1 : ℕ∞ω) ≤ ∞ from by simp)
  let cov := CovariantDerivative.pullbackFiberwiseLinearEquiv
    (fun y => (ι t y).toLinearEquiv) hι₁.clm_bundle_map (LeviCivita (S.family.metric t))
  have hc : cov.IsMetricCompatible :=
    CovariantDerivative.isMetricCompatible_pullback_leviCivita
      (S.family.metric t) (ι t) hι₁ hmetric
  let : CompleteSpace F := FiniteDimensional.complete ℝ F
  have hιinv : ContMDiff I (I.prod 𝓘(ℝ, E →L[ℝ] F)) ∞
      (fun y => TotalSpace.mk' (E →L[ℝ] F) y (ι t y).symm.toContinuousLinearMap) := by
    simpa only [ContinuousLinearMap.inverse_equiv] using
      hι.clm_bundle_inverse (fun _ => ContinuousLinearMap.isInvertible_equiv)
  let : CovariantDerivative.ContMDiffCovariantDerivative cov ∞ :=
    CovariantDerivative.ContMDiffCovariantDerivative.pullbackFiberwiseLinearEquiv
      (fun y => (ι t y).toLinearEquiv) hι.clm_bundle_map hιinv.clm_bundle_map
      (LeviCivita (S.family.metric t))
  let T := fun s y => (S.base.rm04 s y).compContinuousLinearMap
    (fun _ => (ι s y).toContinuousLinearMap)
  let hT := fun s y => riemann_pullback_isAlgCurvForm S s y (ι s y)
  have h := traceNormalizedCurvatureEndomorphism_pullback_hasDerivWithinAt_of_evolution
    (F := F) (V := V) S t ι hι hmetric x hdim hRm hode
  exact hc.hasDerivWithinAt_traceNormalizedCurvatureSelfAdjoint (F := F) (V := V)
    (S.family.metric t) T hT t (riemann_pullback_contMDiff S t (ι t) hι) x J h

theorem traceNormalizedCurvatureSelfAdjoint_pullback_hasDerivWithinAt_of_ricci_ode
    {D : RealTimeInterval} (S : SolutionOn (I := I) (M := M) D)
    (hS : IsSolutionOn S) (t : D.RegularTime)
    (ι : ℝ → ∀ x, V x ≃L[ℝ] TangentSpace I x) {J : Set ℝ}
    (hι : ContMDiff I (I.prod 𝓘(ℝ, F →L[ℝ] E)) ∞
      (fun x => TotalSpace.mk' (F →L[ℝ] E) x (ι t x).toContinuousLinearMap))
    (hmetric : ∀ x v w, (S.family.metric t).inner x (ι t x v) (ι t x w) = ⟪v, w⟫)
    (x : M) (hdim : Module.finrank ℝ (V x) = 3)
    (hode : ∀ v, HasDerivWithinAt (fun s => ι s x v)
      (ricciSharp (I := I) (S.family.metric t) x (ι t x v)) J t) :
    letI : ∀ y, FiniteDimensional ℝ (V y) := fun y => VectorBundle.finiteDimensional ℝ F V y
    letI := Bundle.ExteriorPower.totalSpaceTopology F V 2
    letI := Bundle.ExteriorPower.fiberBundle F V 2
    letI := Bundle.ExteriorPower.vector_bundle F V 2
    letI := Bundle.ExteriorPower.contMDiffVectorBundle (IB := I) (n := ∞) F V 2
    letI := Bundle.ExteriorPower.isContMDiffRiemannianBundle (IB := I) (n := ∞) F V 2
    let P := selfAdjointSubbundle (I := I) (F := ⋀[ℝ]^2 F)
      (V := fun y => ⋀[ℝ]^2 (V y)) (n := ∞)
    letI := P.totalSpaceTopology
    letI := P.fiberBundle
    let hι₁ := hι.of_le (show (1 : ℕ∞ω) ≤ ∞ from by simp)
    let cov := CovariantDerivative.pullbackFiberwiseLinearEquiv
      (fun y => (ι t y).toLinearEquiv) hι₁.clm_bundle_map (LeviCivita (S.family.metric t))
    let hc := CovariantDerivative.isMetricCompatible_pullback_leviCivita
      (S.family.metric t) (ι t) hι₁ hmetric
    let T := fun s y => (S.base.rm04 s y).compContinuousLinearMap
      (fun _ => (ι s y).toContinuousLinearMap)
    let hT := fun s y => riemann_pullback_isAlgCurvForm S s y (ι s y)
    let R : ℝ → ∀ y, P.fiber y := fun s y =>
      exteriorPower.traceNormalizedCurvatureSelfAdjoint (T s y) (hT s y)
    let Q : P.fiber x := curvatureOperatorReactionSelfAdjoint3 (R t x)
    HasDerivWithinAt (fun s => R s x)
      (rawBundleConnLap (F := Fin P.rank → ℝ) (V := fun y => P.fiber y)
        (S.family.metric t)
        ((cov.exteriorPower 2).selfAdjoint
          (F := ⋀[ℝ]^2 F) (V := fun y => ⋀[ℝ]^2 (V y))
          (hc.exteriorPower 2)) (R t) x + Q) J t :=
  traceNormalizedCurvatureSelfAdjoint_pullback_hasDerivWithinAt_of_evolution S t ι hι hmetric x hdim
    (riemann_tensor_hasDerivAt_of_solution S hS t x).hasDerivWithinAt hode

theorem exists_uhlenbeck_isometry_with_traceNormalizedCurvatureSelfAdjoint_evolution
    {D : RealTimeInterval} (S : SolutionOn (I := I) (M := M) D)
    (hS : IsSolutionOn S) (hdim : Module.finrank ℝ F = 3)
    {J : Set ℝ} {t₀ : ℝ} (hJ : J.OrdConnected) (ht₀ : t₀ ∈ J)
    (hJD : J ⊆ D.regular) (ι₀ : ∀ x, V x ≃L[ℝ] TangentSpace I x)
    (hι₀ : ContMDiff I (I.prod 𝓘(ℝ, F →L[ℝ] E)) ∞
      (fun x => TotalSpace.mk' (F →L[ℝ] E) x (ι₀ x).toContinuousLinearMap))
    (h₀ : ∀ x v w, (S.family.metric t₀).inner x (ι₀ x v) (ι₀ x w) = ⟪v, w⟫) :
    ∃ ι : ℝ → ∀ x, V x ≃L[ℝ] TangentSpace I x,
      (∀ x, ι t₀ x = ι₀ x) ∧
      ContMDiffOn (𝓘(ℝ, ℝ).prod I) (I.prod 𝓘(ℝ, F →L[ℝ] E)) ∞
        (fun p : ℝ × M => TotalSpace.mk' (F →L[ℝ] E) p.2
          (E := fun x => V x →L[ℝ] TangentSpace I x)
          (ι p.1 p.2).toContinuousLinearMap) (J ×ˢ (Set.univ : Set M)) ∧
      ContMDiffOn (𝓘(ℝ, ℝ).prod I) (I.prod 𝓘(ℝ, E →L[ℝ] F)) ∞
        (fun p : ℝ × M => TotalSpace.mk' (E →L[ℝ] F) p.2
          (E := fun x => TangentSpace I x →L[ℝ] V x)
          (ι p.1 p.2).symm.toContinuousLinearMap) (J ×ˢ (Set.univ : Set M)) ∧
      (∀ x v, ∀ t ∈ J, HasDerivWithinAt (fun s => ι s x v)
        (ricciSharp (I := I) (S.family.metric t) x (ι t x v)) J t) ∧
      ∃ hmetric : ∀ t ∈ J, ∀ x v w,
          (S.family.metric t).inner x (ι t x v) (ι t x w) = ⟪v, w⟫,
        ∀ t ht, ∃ hιt : ContMDiff I (I.prod 𝓘(ℝ, F →L[ℝ] E)) ∞
            (fun x => TotalSpace.mk' (F →L[ℝ] E) x (ι t x).toContinuousLinearMap),
          letI : ∀ y, FiniteDimensional ℝ (V y) :=
            fun y => VectorBundle.finiteDimensional ℝ F V y
          letI := Bundle.ExteriorPower.totalSpaceTopology F V 2
          letI := Bundle.ExteriorPower.fiberBundle F V 2
          letI := Bundle.ExteriorPower.vector_bundle F V 2
          letI := Bundle.ExteriorPower.contMDiffVectorBundle (IB := I) (n := ∞) F V 2
          letI := Bundle.ExteriorPower.isContMDiffRiemannianBundle (IB := I) (n := ∞) F V 2
          let P := selfAdjointSubbundle (I := I) (F := ⋀[ℝ]^2 F)
            (V := fun y => ⋀[ℝ]^2 (V y)) (n := ∞)
          letI := P.totalSpaceTopology
          letI := P.fiberBundle
          let hι₁ := hιt.of_le (show (1 : ℕ∞ω) ≤ ∞ from by simp)
          let cov := CovariantDerivative.pullbackFiberwiseLinearEquiv
            (fun y => (ι t y).toLinearEquiv) hι₁.clm_bundle_map (LeviCivita (S.family.metric t))
          let hc := CovariantDerivative.isMetricCompatible_pullback_leviCivita
            (S.family.metric t) (ι t) hι₁ (hmetric t ht)
          let T := fun s y => (S.base.rm04 s y).compContinuousLinearMap
            (fun _ => (ι s y).toContinuousLinearMap)
          let hT := fun s y => riemann_pullback_isAlgCurvForm S s y (ι s y)
          let R : ℝ → ∀ y, P.fiber y := fun s y =>
            exteriorPower.traceNormalizedCurvatureSelfAdjoint (T s y) (hT s y)
          ∀ x, let Q : P.fiber x := curvatureOperatorReactionSelfAdjoint3 (R t x)
            HasDerivWithinAt (fun s => R s x)
              (rawBundleConnLap (F := Fin P.rank → ℝ) (V := fun y => P.fiber y)
                (S.family.metric t)
                ((cov.exteriorPower 2).selfAdjoint
                  (F := ⋀[ℝ]^2 F) (V := fun y => ⋀[ℝ]^2 (V y))
                  (hc.exteriorPower 2)) (R t) x + Q) J t := by
  have he := exists_uhlenbeck_isometry_on_interval (F := F) (V := V) S hS hJ ht₀ hJD
      (RiemannianMetric.ofInnerProductSpace V) ι₀ hι₀ h₀
  rcases he with ⟨ι, hinit, hsmooth, hinverse, hderiv, hmetric⟩
  refine ⟨ι, hinit, hsmooth, hinverse, hderiv, hmetric, ?_⟩
  intro t ht
  have hpair : ContMDiff I (𝓘(ℝ, ℝ).prod I) ∞ (fun x : M => (t, x)) :=
    contMDiff_const.prodMk contMDiff_id
  have hιt := hsmooth.comp_contMDiff hpair (fun x => ⟨ht, Set.mem_univ x⟩)
  refine ⟨hιt, ?_⟩
  dsimp only
  intro x
  exact traceNormalizedCurvatureSelfAdjoint_pullback_hasDerivWithinAt_of_ricci_ode
    (F := F) (V := V) S hS ⟨t, hJD ht⟩ ι hιt (hmetric t ht) x
    ((VectorBundle.finrank_eq ℝ F V x).trans hdim) (fun v => hderiv x v t ht)


end DifferentialGeometry.PDE.RicciFlow
