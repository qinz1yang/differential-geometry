import DifferentialGeometry.Geometry.Flow.RicciFlow.Estimates.Uhlenbeck.CurvatureOperatorSectionEvolution
import DifferentialGeometry.Analysis.Parabolic.CurvatureOperatorRank
import DifferentialGeometry.Geometry.Curvature.DimensionThree.ExteriorRank
import DifferentialGeometry.Geometry.Curvature.CurvatureOperator.ExteriorPositivity

noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow

open Bundle CovariantDerivative Set
open DifferentialGeometry.Geometry.Connection
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Curvature.DimensionThree
open DifferentialGeometry.Geometry.Operator
open scoped Manifold ContDiff Topology RealInnerProductSpace

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M]
  {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]
  {V : M → Type*} [TopologicalSpace (TotalSpace F V)]
  [∀ x, NormedAddCommGroup (V x)] [∀ x, InnerProductSpace ℝ (V x)]
  [FiberBundle F V] [VectorBundle ℝ F V] [ContMDiffVectorBundle ∞ F V I]
  [IsContMDiffRiemannianBundle I ∞ F V]

theorem traceNormalizedCurvatureEndomorphism_pullback_kernel_and_range_eq_of_constant_rank
    {D : RealTimeInterval} (S : SolutionOn (I := I) (M := M) D) (hS : IsSolutionOn S)
    (hdim : Module.finrank ℝ F = 3)
    (ι : ℝ → ∀ x, V x ≃L[ℝ] TangentSpace I x)
    {a b : ℝ} (hreg : Ioo a b ⊆ D.regular)
    (hι : ContMDiffOn (𝓘(ℝ, ℝ).prod I) (I.prod 𝓘(ℝ, F →L[ℝ] E)) ∞
      (fun p : ℝ × M => TotalSpace.mk' (F →L[ℝ] E) p.2
        (E := fun y => V y →L[ℝ] TangentSpace I y)
        (ι p.1 p.2).toContinuousLinearMap) (Ioo a b ×ˢ (univ : Set M)))
    (hmetric : ∀ t ∈ Ioo a b, ∀ x v w,
      (S.family.metric t).inner x (ι t x v) (ι t x w) = ⟪v, w⟫)
    (hode : ∀ t ∈ Ioo a b, ∀ x v, HasDerivWithinAt (fun s => ι s x v)
      (ricciSharp (S.family.metric t) x (ι t x v)) (Ioo a b) t)
    (hR : ∀ t ∈ Ioo a b, ∀ x,
      (⟨metricRm04At (S.family.metric t) x,
        metricRm04At_mem_algebraicCurvatureTensorSubmodule (S.family.metric t) x⟩ :
          algebraicCurvatureTensorSubmodule (I := I) (M := M) x) ∈
            algebraicCurvatureOperatorNonnegativeCone (I := I) (M := M))
    (q : ℕ) (hrank : ∀ t ∈ Ioo a b, ∀ x,
      Module.finrank ℝ (curvatureOperatorImageAt (S.family.metric t) x
        ⟨metricRm04At (S.family.metric t) x,
          metricRm04At_mem_algebraicCurvatureTensorSubmodule (S.family.metric t) x⟩) = q)
    {s t : ℝ} (hs : s ∈ Ioo a b) (ht : t ∈ Ioo a b) (x : M) :
    letI : ∀ y, FiniteDimensional ℝ (V y) := fun y => VectorBundle.finiteDimensional ℝ F V y
    let R := fun r y => exteriorPower.traceNormalizedCurvatureEndomorphism
      ((S.base.rm04 r y).compContinuousLinearMap (fun _ => (ι r y).toContinuousLinearMap))
      ((mem_algebraicCurvatureTensorSubmodule.mp
        (metricRm04At_mem_algebraicCurvatureTensorSubmodule (S.base.metric r) y)).compContinuousLinearMap
          (ι r y).toContinuousLinearMap)
    (R s x).ker = (R t x).ker ∧ (R s x).range = (R t x).range := by
  dsimp only
  classical
  let _ : ∀ y, FiniteDimensional ℝ (V y) := fun y => VectorBundle.finiteDimensional ℝ F V y
  let _ := Bundle.ExteriorPower.totalSpaceTopology F V 2
  let _ := Bundle.ExteriorPower.fiberBundle F V 2
  let _ := Bundle.ExteriorPower.vector_bundle F V 2
  let _ := Bundle.ExteriorPower.contMDiffVectorBundle (IB := I) (n := ∞) F V 2
  let _ := Bundle.ExteriorPower.isContMDiffRiemannianBundle (IB := I) (n := ∞) F V 2
  let R := fun r y => exteriorPower.traceNormalizedCurvatureEndomorphism
    ((S.base.rm04 r y).compContinuousLinearMap (fun _ => (ι r y).toContinuousLinearMap))
    ((mem_algebraicCurvatureTensorSubmodule.mp
      (metricRm04At_mem_algebraicCurvatureTensorSubmodule (S.base.metric r) y)).compContinuousLinearMap
        (ι r y).toContinuousLinearMap)
  obtain ⟨A, hA, -, hAspace, -⟩ :=
    exists_traceNormalizedCurvatureEndomorphism_pullback_sections (F := F) S hS ι hreg hι
  have hevolution : ∀ r ∈ Ioo a b,
      ∃ cov : CovariantDerivative I (⋀[ℝ]^2 F) (fun y => ⋀[ℝ]^2 (V y)),
        ContMDiffCovariantDerivative cov ∞ ∧ cov.IsMetricCompatible ∧
        ∀ y, HasDerivAt (fun u => A u y)
          (rawBundleEndomorphismConnLap (S.family.metric r) cov (fun z => A r z) y +
            (curvatureOperatorReactionEndomorphism3 (A r y).toLinearMap).toContinuousLinearMap) r := by
    intro r hr
    have hιr := hι.comp_contMDiff (contMDiff_const.prodMk contMDiff_id)
      (fun y => ⟨hr, mem_univ y⟩)
    have hp := traceNormalizedCurvatureEndomorphism_pullback_section_hasDerivWithinAt_of_ricci_ode
      (F := F) S hS ι hreg hr hιr (hmetric r hr) hdim (hode r hr)
    refine ⟨_, hp.1, hp.2.1, ?_⟩
    intro y
    exact (hp.2.2 A hA y).hasDerivAt (isOpen_Ioo.mem_nhds hr)
  let cov := fun r => if hr : r ∈ Ioo a b then (hevolution r hr).choose
    else (hevolution s hs).choose
  have hcovsmooth : ∀ r, ContMDiffCovariantDerivative (cov r) ∞ := by
    intro r
    dsimp only [cov]
    split_ifs with hr
    · exact (hevolution r hr).choose_spec.1
    · exact (hevolution s hs).choose_spec.1
  let _ := hcovsmooth
  have hcovmetric : ∀ r, (cov r).IsMetricCompatible := by
    intro r
    dsimp only [cov]
    split_ifs with hr
    · exact (hevolution r hr).choose_spec.2.1
    · exact (hevolution s hs).choose_spec.2.1
  have hevol : ∀ r ∈ Ioo a b, ∀ y, HasDerivAt (fun u => A u y)
      (rawBundleEndomorphismConnLap (S.family.metric r) (cov r) (fun z => A r z) y +
        HomConnectionGen.homBundleCovariantDerivativeGen I M
          (⋀[ℝ]^2 F) (fun z => ⋀[ℝ]^2 (V z)) (⋀[ℝ]^2 F) (fun z => ⋀[ℝ]^2 (V z))
          (cov r) (cov r) (fun z => A r z) y 0 +
        (curvatureOperatorReactionEndomorphism3 (A r y).toLinearMap).toContinuousLinearMap) r := by
    intro r hr y
    simpa only [cov, dif_pos hr, map_zero, add_zero] using (hevolution r hr).choose_spec.2.2 y
  have hArank : ∀ r ∈ Ioo a b, ∀ y, Module.finrank ℝ (A r y).range = q := by
    intro r hr y
    rw [hA r hr y]
    exact (traceNormalizedCurvatureEndomorphism_pullback_finrank_range
      ((VectorBundle.finrank_eq ℝ F V y).trans hdim) (S.family.metric r) y
      ⟨metricRm04At (S.family.metric r) y,
        metricRm04At_mem_algebraicCurvatureTensorSubmodule (S.family.metric r) y⟩
      (ι r y) (hmetric r hr y)).trans (hrank r hr y)
  have hApos : ∀ r ∈ Ioo a b, ∀ y, (A r y).IsPositive := by
    intro r hr y
    rw [hA r hr y]
    exact traceNormalizedCurvatureEndomorphism_pullback_isPositive_of_mem_nonnegativeCone
      ⟨metricRm04At (S.family.metric r) y,
        metricRm04At_mem_algebraicCurvatureTensorSubmodule (S.family.metric r) y⟩
      (hR r hr y) (ι r y).toContinuousLinearMap
  have h := DifferentialGeometry.Analysis.Parabolic.curvatureOperator_kernel_and_range_eq_of_constant_rank
    S.family.metric cov hcovmetric A hAspace q hArank hApos (fun _ _ => 0) hevol hs ht (x := x)
  rw [hA s hs x, hA t ht x] at h
  exact h


theorem exists_uhlenbeck_isometry_with_constant_curvatureOperator_kernel_and_range
    {D : RealTimeInterval} (S : SolutionOn (I := I) (M := M) D) (hS : IsSolutionOn S)
    (hdim : Module.finrank ℝ F = 3)
    {a b t₀ : ℝ} (ht₀ : t₀ ∈ Ioo a b) (hreg : Ioo a b ⊆ D.regular)
    (ι₀ : ∀ x, V x ≃L[ℝ] TangentSpace I x)
    (hι₀ : ContMDiff I (I.prod 𝓘(ℝ, F →L[ℝ] E)) ∞
      (fun x => TotalSpace.mk' (F →L[ℝ] E) x (ι₀ x).toContinuousLinearMap))
    (h₀ : ∀ x v w, (S.family.metric t₀).inner x (ι₀ x v) (ι₀ x w) = ⟪v, w⟫)
    (hR : ∀ t ∈ Ioo a b, ∀ x,
      (⟨metricRm04At (S.family.metric t) x,
        metricRm04At_mem_algebraicCurvatureTensorSubmodule (S.family.metric t) x⟩ :
          algebraicCurvatureTensorSubmodule (I := I) (M := M) x) ∈
            algebraicCurvatureOperatorNonnegativeCone (I := I) (M := M))
    (q : ℕ) (hrank : ∀ t ∈ Ioo a b, ∀ x,
      Module.finrank ℝ (curvatureOperatorImageAt (S.family.metric t) x
        ⟨metricRm04At (S.family.metric t) x,
          metricRm04At_mem_algebraicCurvatureTensorSubmodule (S.family.metric t) x⟩) = q) :
    ∃ ι : ℝ → ∀ x, V x ≃L[ℝ] TangentSpace I x,
      (∀ x, ι t₀ x = ι₀ x) ∧
      ContMDiffOn (𝓘(ℝ, ℝ).prod I) (I.prod 𝓘(ℝ, F →L[ℝ] E)) ∞
        (fun p : ℝ × M => TotalSpace.mk' (F →L[ℝ] E) p.2
          (E := fun y => V y →L[ℝ] TangentSpace I y)
          (ι p.1 p.2).toContinuousLinearMap) (Ioo a b ×ˢ (univ : Set M)) ∧
      ContMDiffOn (𝓘(ℝ, ℝ).prod I) (I.prod 𝓘(ℝ, E →L[ℝ] F)) ∞
        (fun p : ℝ × M => TotalSpace.mk' (E →L[ℝ] F) p.2
          (E := fun y => TangentSpace I y →L[ℝ] V y)
          (ι p.1 p.2).symm.toContinuousLinearMap) (Ioo a b ×ˢ (univ : Set M)) ∧
      (∀ t ∈ Ioo a b, ∀ x v, HasDerivWithinAt (fun s => ι s x v)
        (ricciSharp (S.family.metric t) x (ι t x v)) (Ioo a b) t) ∧
      (∀ t ∈ Ioo a b, ∀ x v w,
        (S.family.metric t).inner x (ι t x v) (ι t x w) = ⟪v, w⟫) ∧
      letI : ∀ y, FiniteDimensional ℝ (V y) := fun y => VectorBundle.finiteDimensional ℝ F V y
      let R := fun r y => exteriorPower.traceNormalizedCurvatureEndomorphism
        ((S.base.rm04 r y).compContinuousLinearMap (fun _ => (ι r y).toContinuousLinearMap))
        ((mem_algebraicCurvatureTensorSubmodule.mp
          (metricRm04At_mem_algebraicCurvatureTensorSubmodule (S.base.metric r) y)).compContinuousLinearMap
            (ι r y).toContinuousLinearMap)
      ∀ s ∈ Ioo a b, ∀ t ∈ Ioo a b, ∀ x,
        (R s x).ker = (R t x).ker ∧ (R s x).range = (R t x).range := by
  obtain ⟨ι, hinit, hι, hinv, hode, hmetric, -⟩ :=
    exists_uhlenbeck_isometry_with_traceNormalizedCurvatureEndomorphism_evolution
      (F := F) S hS hdim ordConnected_Ioo ht₀ hreg ι₀ hι₀ h₀
  refine ⟨ι, hinit, hι, hinv, (fun t ht x v => hode x v t ht), hmetric, ?_⟩
  dsimp only
  intro s hs t ht x
  exact traceNormalizedCurvatureEndomorphism_pullback_kernel_and_range_eq_of_constant_rank
    S hS hdim ι hreg hι hmetric (fun t ht x v => hode x v t ht) hR q hrank hs ht x

end DifferentialGeometry.PDE.RicciFlow
