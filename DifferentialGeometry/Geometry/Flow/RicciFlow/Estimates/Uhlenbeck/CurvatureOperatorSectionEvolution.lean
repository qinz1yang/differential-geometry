import DifferentialGeometry.Geometry.Flow.RicciFlow.Estimates.Uhlenbeck.CurvatureOperatorRegularity
import DifferentialGeometry.Geometry.Flow.RicciFlow.Estimates.Uhlenbeck.CurvatureOperatorEvolution

set_option autoImplicit false

noncomputable section

open Bundle
open DifferentialGeometry DifferentialGeometry.Geometry.Connection
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Curvature.DimensionThree
open CovariantDerivative
open scoped Bundle Manifold ContDiff Topology RealInnerProductSpace

namespace DifferentialGeometry.PDE.RicciFlow

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M]
  {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]
  {V : M → Type*} [TopologicalSpace (TotalSpace F V)]
  [∀ x, NormedAddCommGroup (V x)] [∀ x, InnerProductSpace ℝ (V x)]
  [FiberBundle F V] [VectorBundle ℝ F V] [ContMDiffVectorBundle ∞ F V I]
  [IsContMDiffRiemannianBundle I ∞ F V]

theorem traceNormalizedCurvatureEndomorphism_pullback_section_hasDerivWithinAt_of_ricci_ode
    {D : RealTimeInterval} (S : SolutionOn (I := I) (M := M) D) (hS : IsSolutionOn S)
    (ι : ℝ → ∀ x, V x ≃L[ℝ] TangentSpace I x)
    {J : Set ℝ} (hJD : J ⊆ D.regular)
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
        ∀ x, HasDerivWithinAt (fun s => A s x)
          (rawBundleEndomorphismConnLap (S.family.metric t) (cov.exteriorPower 2)
            (fun y => A t y) x +
            (curvatureOperatorReactionEndomorphism3 (A t x).toLinearMap).toContinuousLinearMap) J t := by
  dsimp only
  let _ : ∀ y, FiniteDimensional ℝ (V y) := fun y => VectorBundle.finiteDimensional ℝ F V y
  let _ := Bundle.ExteriorPower.totalSpaceTopology F V 2
  let _ := Bundle.ExteriorPower.fiberBundle F V 2
  let _ := Bundle.ExteriorPower.vector_bundle F V 2
  let _ := Bundle.ExteriorPower.contMDiffVectorBundle (IB := I) (n := ∞) F V 2
  let _ := Bundle.ExteriorPower.isContMDiffRiemannianBundle (IB := I) (n := ∞) F V 2
  let cov := CovariantDerivative.pullbackFiberwiseLinearEquiv
    (fun y => (ι t y).toLinearEquiv)
    (hιt.of_le (show (1 : ℕ∞ω) ≤ ∞ by simp)).clm_bundle_map
    (LeviCivita (S.family.metric t))
  let hcovsmooth : ContMDiffCovariantDerivative cov ∞ := by
    let _ := FiniteDimensional.complete ℝ F
    have hiinv : ContMDiff I (I.prod 𝓘(ℝ, E →L[ℝ] F)) ∞
        (fun y => TotalSpace.mk' (E →L[ℝ] F) y (ι t y).symm.toContinuousLinearMap) := by
      simpa only [ContinuousLinearMap.inverse_equiv] using
        hιt.clm_bundle_inverse (fun _ => ContinuousLinearMap.isInvertible_equiv)
    exact CovariantDerivative.ContMDiffCovariantDerivative.pullbackFiberwiseLinearEquiv
      (fun y => (ι t y).toLinearEquiv) hιt.clm_bundle_map hiinv.clm_bundle_map
      (LeviCivita (S.family.metric t))
  have hcovmetric : cov.IsMetricCompatible :=
    CovariantDerivative.isMetricCompatible_pullback_leviCivita
      (S.family.metric t) (ι t) (hιt.of_le (show (1 : ℕ∞ω) ≤ ∞ by simp)) hmetric
  refine ⟨cov.exteriorPower_contMDiff 2, hcovmetric.exteriorPower 2, ?_⟩
  intro A hA x
  have hR := traceNormalizedCurvatureEndomorphism_pullback_hasDerivWithinAt_of_ricci_ode
    (F := F) (V := V) S hS ⟨t, hJD ht⟩ ι hιt hmetric x
    ((VectorBundle.finrank_eq ℝ F V x).trans hdim) (hode x)
  have hfun := funext (hA t ht)
  have hd := hR.congr_of_mem (fun s hs => hA s hs x) ht
  simpa only [← hfun, ← hA t ht x] using hd

theorem exists_uhlenbeck_curvatureOperator_sections_evolution {D : RealTimeInterval} (S : SolutionOn (I := I) (M := M) D) (hS : IsSolutionOn S)
    {J : Set ℝ} {t₀ : ℝ} (hJ : J.OrdConnected) (ht₀ : t₀ ∈ J)
    (hJD : J ⊆ D.regular) (hdim : Module.finrank ℝ F = 3)
    (ι₀ : ∀ x, V x ≃L[ℝ] TangentSpace I x)
    (hι₀ : ContMDiff I (I.prod 𝓘(ℝ, F →L[ℝ] E)) ∞
      (fun x => TotalSpace.mk' (F →L[ℝ] E) x (ι₀ x).toContinuousLinearMap))
    (h₀ : ∀ x v w, (S.family.metric t₀).inner x (ι₀ x v) (ι₀ x w) = ⟪v, w⟫) :
    letI : ∀ y, FiniteDimensional ℝ (V y) := fun y => VectorBundle.finiteDimensional ℝ F V y
    letI := Bundle.ExteriorPower.totalSpaceTopology F V 2
    letI := Bundle.ExteriorPower.fiberBundle F V 2
    letI := Bundle.ExteriorPower.vector_bundle F V 2
    letI := Bundle.ExteriorPower.contMDiffVectorBundle (IB := I) (n := ∞) F V 2
    letI := Bundle.ExteriorPower.isContMDiffRiemannianBundle (IB := I) (n := ∞) F V 2
    ∃ ι : ℝ → ∀ x, V x ≃L[ℝ] TangentSpace I x,
      (∀ x, ι t₀ x = ι₀ x) ∧
      (∀ t ∈ J, ∀ x v w, (S.family.metric t).inner x (ι t x v) (ι t x w) = ⟪v, w⟫) ∧
      let R := fun t x => exteriorPower.traceNormalizedCurvatureEndomorphism
        ((S.base.rm04 t x).compContinuousLinearMap (fun _ => (ι t x).toContinuousLinearMap))
        (by
          have hT := mem_algebraicCurvatureTensorSubmodule.mp
            (metricRm04At_mem_algebraicCurvatureTensorSubmodule (I := I) (S.base.metric t) x)
          exact hT.compContinuousLinearMap (ι t x).toContinuousLinearMap)
      ∃ A : ℝ → Cₛ^∞⟮I; (⋀[ℝ]^2 F) →L[ℝ] ⋀[ℝ]^2 F,
        (fun x : M => (⋀[ℝ]^2 (V x)) →L[ℝ] ⋀[ℝ]^2 (V x))⟯,
      (∀ t ∈ J, ∀ x, A t x = R t x) ∧
      (∀ t x, (A t x).toLinearMap.IsSymmetric) ∧
      ContMDiffOnSpacetimeEndomorphism (I := I) (F := ⋀[ℝ]^2 F)
        (V := fun x => ⋀[ℝ]^2 (V x)) (n := ∞) (fun t x => A t x)
        (J ×ˢ (Set.univ : Set M)) ∧
      ContinuousOn (fun p : ℝ × M =>
        TotalSpace.mk' ((⋀[ℝ]^2 F) →L[ℝ] ⋀[ℝ]^2 F)
          (E := fun x => (⋀[ℝ]^2 (V x)) →L[ℝ] ⋀[ℝ]^2 (V x)) p.2 (A p.1 p.2))
        (J ×ˢ (Set.univ : Set M)) ∧
      ∀ t ∈ J, ∃ cov : CovariantDerivative I (⋀[ℝ]^2 F) (fun y => ⋀[ℝ]^2 (V y)),
        CovariantDerivative.ContMDiffCovariantDerivative cov ∞ ∧ cov.IsMetricCompatible ∧
        ∀ x, HasDerivWithinAt (fun s => A s x)
          (rawBundleEndomorphismConnLap (S.family.metric t) cov (fun y => A t y) x +
            (curvatureOperatorReactionEndomorphism3 (A t x).toLinearMap).toContinuousLinearMap) J t := by
  let _ : ∀ y, FiniteDimensional ℝ (V y) := fun y => VectorBundle.finiteDimensional ℝ F V y
  let _ := Bundle.ExteriorPower.totalSpaceTopology F V 2
  let _ := Bundle.ExteriorPower.fiberBundle F V 2
  let _ := Bundle.ExteriorPower.vector_bundle F V 2
  let _ := Bundle.ExteriorPower.contMDiffVectorBundle (IB := I) (n := ∞) F V 2
  let _ := Bundle.ExteriorPower.isContMDiffRiemannianBundle (IB := I) (n := ∞) F V 2
  obtain ⟨ι, hinit, hι, _, hder, hmetric, _⟩ :=
    exists_uhlenbeck_isometry_with_traceNormalizedCurvatureEndomorphism_evolution
      (F := F) S hS hdim hJ ht₀ hJD ι₀ hι₀ h₀
  obtain ⟨A, hA, hAsym, hAspace, hAcont⟩ := exists_traceNormalizedCurvatureEndomorphism_pullback_sections
    (F := F) (V := V) S hS ι hJD hι
  refine ⟨ι, hinit, hmetric, A, hA, hAsym, hAspace, hAcont, ?_⟩
  intro t ht
  have hpair : ContMDiff I (𝓘(ℝ, ℝ).prod I) ∞ (fun y : M => (t, y)) :=
    contMDiff_const.prodMk contMDiff_id
  have hιt : ContMDiff I (I.prod 𝓘(ℝ, F →L[ℝ] E)) ∞
      (fun y => TotalSpace.mk' (F →L[ℝ] E) y (ι t y).toContinuousLinearMap) :=
    hι.comp_contMDiff hpair (fun y => ⟨ht, Set.mem_univ y⟩)
  let cov := CovariantDerivative.pullbackFiberwiseLinearEquiv
    (fun y => (ι t y).toLinearEquiv)
    (hιt.of_le (show (1 : ℕ∞ω) ≤ ∞ by simp)).clm_bundle_map
    (LeviCivita (S.family.metric t))
  have hp := traceNormalizedCurvatureEndomorphism_pullback_section_hasDerivWithinAt_of_ricci_ode
    (F := F) (V := V) S hS ι hJD ht hιt (hmetric t ht) hdim
    (fun x v => hder x v t ht)
  exact ⟨cov.exteriorPower 2, hp.1, hp.2.1, hp.2.2 A hA⟩

end DifferentialGeometry.PDE.RicciFlow
