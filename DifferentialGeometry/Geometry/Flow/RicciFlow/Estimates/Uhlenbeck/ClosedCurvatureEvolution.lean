import DifferentialGeometry.Geometry.Flow.RicciFlow.Estimates.Uhlenbeck.ClosedMetricGauge
import DifferentialGeometry.Geometry.Flow.RicciFlow.Estimates.Uhlenbeck.CurvatureOperatorSectionEvolution

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

theorem exists_uhlenbeck_curvatureOperator_sections_evolution_on_closed_interval
    [SigmaCompactSpace M] {D : RealTimeInterval} (S : SolutionOn (I := I) (M := M) D) (hS : IsSolutionOn S)
    {a c b : ℝ} (hac : a < c) (hcb : c < b)
    (hslab : Set.Icc a b ⊆ D.carrier) (hreg : Set.Ioo a b ⊆ D.regular)
    {t₀ : ℝ} (ht₀ : t₀ ∈ Set.Icc c b) (hdim : Module.finrank ℝ F = 3)
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
      (∀ t ∈ Set.Icc c b, ∀ x v w, (S.family.metric t).inner x (ι t x v) (ι t x w) = ⟪v, w⟫) ∧
      let R := fun t x => exteriorPower.traceNormalizedCurvatureEndomorphism
        ((S.base.rm04 t x).compContinuousLinearMap (fun _ => (ι t x).toContinuousLinearMap))
        (by
          have hT := mem_algebraicCurvatureTensorSubmodule.mp
            (metricRm04At_mem_algebraicCurvatureTensorSubmodule (I := I) (S.base.metric t) x)
          exact hT.compContinuousLinearMap (ι t x).toContinuousLinearMap)
      ∃ A : ℝ → Cₛ^∞⟮I; (⋀[ℝ]^2 F) →L[ℝ] ⋀[ℝ]^2 F,
        (fun x : M => (⋀[ℝ]^2 (V x)) →L[ℝ] ⋀[ℝ]^2 (V x))⟯,
      (∀ t ∈ Set.Icc c b, ∀ x, A t x = R t x) ∧
      (∀ t x, (A t x).toLinearMap.IsSymmetric) ∧
      ContMDiffOnSpacetimeEndomorphism (I := I) (F := ⋀[ℝ]^2 F)
        (V := fun x => ⋀[ℝ]^2 (V x)) (n := ∞) (fun t x => A t x)
        (Set.Ioo c b ×ˢ (Set.univ : Set M)) ∧
      ContinuousOn (fun p : ℝ × M =>
        TotalSpace.mk' ((⋀[ℝ]^2 F) →L[ℝ] ⋀[ℝ]^2 F)
          (E := fun x => (⋀[ℝ]^2 (V x)) →L[ℝ] ⋀[ℝ]^2 (V x)) p.2 (A p.1 p.2))
        (Set.Icc c b ×ˢ (Set.univ : Set M)) ∧
      ∀ t ∈ Set.Ioo c b, ∃ cov : CovariantDerivative I (⋀[ℝ]^2 F) (fun y => ⋀[ℝ]^2 (V y)),
        CovariantDerivative.ContMDiffCovariantDerivative cov ∞ ∧ cov.IsMetricCompatible ∧
        ∀ x, HasDerivAt (fun s => A s x)
          (rawBundleEndomorphismConnLap (S.family.metric t) cov (fun y => A t y) x +
            (curvatureOperatorReactionEndomorphism3 (A t x).toLinearMap).toContinuousLinearMap) t := by
  let _ : ∀ y, FiniteDimensional ℝ (V y) := fun y => VectorBundle.finiteDimensional ℝ F V y
  let _ := Bundle.ExteriorPower.totalSpaceTopology F V 2
  let _ := Bundle.ExteriorPower.fiberBundle F V 2
  let _ := Bundle.ExteriorPower.vector_bundle F V 2
  let _ := Bundle.ExteriorPower.contMDiffVectorBundle (IB := I) (n := ∞) F V 2
  let _ := Bundle.ExteriorPower.isContMDiffRiemannianBundle (IB := I) (n := ∞) F V 2
  obtain ⟨ι, hinit, hι, _, hder, hmetric⟩ :=
    exists_uhlenbeck_isometry_on_closed_interval (F := F) (V := V) S hS
      hac hcb hslab hreg ht₀ (RiemannianMetric.ofInnerProductSpace V) ι₀ hι₀ h₀
  have hclosed : Set.Icc c b ⊆ D.carrier :=
    fun _ ht => hslab ⟨hac.le.trans ht.1, ht.2⟩
  have hopen : Set.Ioo c b ⊆ D.regular :=
    fun _ ht => hreg ⟨hac.trans ht.1, ht.2⟩
  obtain ⟨A, hA, hAsym, hAspace, hAcont⟩ := exists_traceNormalizedCurvatureEndomorphism_pullback_sections_on_carrier
    (F := F) (V := V) S hS ι hclosed hι
  refine ⟨ι, hinit, hmetric, A, hA, hAsym, ?_, hAcont, ?_⟩
  · exact hAspace.mono (Set.prod_mono
      (fun t ht => ⟨⟨ht.1.le, ht.2.le⟩, hopen ht⟩) Set.Subset.rfl)
  intro t ht
  have htclosed : t ∈ Set.Icc c b := ⟨ht.1.le, ht.2.le⟩
  have hpair : ContMDiff I (𝓘(ℝ, ℝ).prod I) ∞ (fun y : M => (t, y)) :=
    contMDiff_const.prodMk contMDiff_id
  have hιt : ContMDiff I (I.prod 𝓘(ℝ, F →L[ℝ] E)) ∞
      (fun y => TotalSpace.mk' (F →L[ℝ] E) y (ι t y).toContinuousLinearMap) :=
    hι.comp_contMDiff hpair (fun y => ⟨htclosed, Set.mem_univ y⟩)
  let cov := CovariantDerivative.pullbackFiberwiseLinearEquiv
    (fun y => (ι t y).toLinearEquiv)
    (hιt.of_le (show (1 : ℕ∞ω) ≤ ∞ by simp)).clm_bundle_map
    (LeviCivita (S.family.metric t))
  have hp := traceNormalizedCurvatureEndomorphism_pullback_section_hasDerivWithinAt_of_ricci_ode
    (F := F) (V := V) S hS ι hopen ht hιt (hmetric t htclosed) hdim
    (fun x v => (hder x v t htclosed).mono Set.Ioo_subset_Icc_self)
  refine ⟨cov.exteriorPower 2, hp.1, hp.2.1, ?_⟩
  intro x
  exact (hp.2.2 A (fun s hs => hA s ⟨hs.1.le, hs.2.le⟩) x).hasDerivAt
    (isOpen_Ioo.mem_nhds ht)

end DifferentialGeometry.PDE.RicciFlow
