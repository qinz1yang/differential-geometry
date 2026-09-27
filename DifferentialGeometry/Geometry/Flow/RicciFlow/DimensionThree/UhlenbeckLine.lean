import DifferentialGeometry.Geometry.Flow.RicciFlow.DimensionThree.CurvatureNullity
import DifferentialGeometry.Geometry.Flow.RicciFlow.DimensionThree.CurvatureKernel
import DifferentialGeometry.Geometry.Curvature.CurvatureOperator.ImageLine
import DifferentialGeometry.Geometry.Flow.RicciFlow.Estimates.Uhlenbeck.CurvatureOperatorTimeInvariance
import DifferentialGeometry.Geometry.Flow.RicciFlow.Estimates.Uhlenbeck.Nullity
import DifferentialGeometry.Geometry.Curvature.CurvatureOperator.RicciNullity

noncomputable section

open Bundle Set
open DifferentialGeometry.Geometry.Connection
open DifferentialGeometry.Geometry.Curvature
open scoped Manifold ContDiff RealInnerProductSpace

namespace DifferentialGeometry.PDE.RicciFlow

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M]

variable
  {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F]
  [FiniteDimensional ℝ F]
  {V : M → Type*} [TopologicalSpace (TotalSpace F V)]
  [∀ x, NormedAddCommGroup (V x)] [∀ x, InnerProductSpace ℝ (V x)]
  [FiberBundle F V] [VectorBundle ℝ F V] [ContMDiffVectorBundle ∞ F V I]
  [IsContMDiffRiemannianBundle I ∞ F V]

theorem uhlenbeck_section_eq_and_inner_eq_of_mem_curvatureOperatorImageAnnihilatorAt
    {D : RealTimeInterval} (S : SolutionOn (I := I) (M := M) D) (hS : IsSolutionOn S)
    (hdim : Module.finrank ℝ F = 3)
    (ι : ℝ → ∀ x, V x ≃L[ℝ] TangentSpace I x)
    {J : Set ℝ} (hJ : J.OrdConnected) (hreg : J ⊆ D.regular)
    (hι : ContMDiffOn (𝓘(ℝ, ℝ).prod I) (I.prod 𝓘(ℝ, F →L[ℝ] E)) ∞
      (fun p : ℝ × M => TotalSpace.mk' (F →L[ℝ] E) p.2
        (E := fun y => V y →L[ℝ] TangentSpace I y)
        (ι p.1 p.2).toContinuousLinearMap) (J ×ˢ (univ : Set M)))
    (hmetric : ∀ t ∈ J, ∀ x v w,
      (S.family.metric t).inner x (ι t x v) (ι t x w) = ⟪v, w⟫)
    (hode : ∀ t ∈ J, ∀ x v, HasDerivWithinAt (fun s => ι s x v)
      (ricciSharp (S.family.metric t) x (ι t x v)) J t)
    (hR : ∀ t ∈ J, ∀ x,
      (⟨metricRm04At (S.family.metric t) x,
        metricRm04At_mem_algebraicCurvatureTensorSubmodule (S.family.metric t) x⟩ :
          algebraicCurvatureTensorSubmodule (I := I) (M := M) x) ∈
            algebraicCurvatureOperatorNonnegativeCone (I := I) (M := M))
    (q : ℕ) (hrank : ∀ t ∈ J, ∀ x,
      Module.finrank ℝ (curvatureOperatorImageAt (S.family.metric t) x
        ⟨metricRm04At (S.family.metric t) x,
          metricRm04At_mem_algebraicCurvatureTensorSubmodule (S.family.metric t) x⟩) = q)
    {t₀ : ℝ} (ht₀ : t₀ ∈ J) (x : M) (v : V x)
    (hv : ι t₀ x v ∈ curvatureOperatorImageAnnihilatorAt (S.family.metric t₀) x
      ⟨metricRm04At (S.family.metric t₀) x,
        metricRm04At_mem_algebraicCurvatureTensorSubmodule (S.family.metric t₀) x⟩) :
    (∀ s ∈ J, ∀ t ∈ J, ι s x v = ι t x v) ∧
    (∀ s ∈ J, ∀ t ∈ J, ∀ w : TangentSpace I x,
      (S.family.metric s).inner x (ι s x v) w =
        (S.family.metric t).inner x (ι t x v) w) := by
  let _ : ∀ y, FiniteDimensional ℝ (V y) := fun y => VectorBundle.finiteDimensional ℝ F V y
  have hfixed s (hs : s ∈ J) t (ht : t ∈ J) :=
    traceNormalizedCurvatureEndomorphism_pullback_kernel_and_range_eq_on_interval
      S hS hdim ι hJ hreg hι hmetric hode hR q hrank hs ht x
  dsimp only at hfixed
  let R := fun r => exteriorPower.traceNormalizedCurvatureEndomorphism
    ((S.base.rm04 r x).compContinuousLinearMap (fun _ => (ι r x).toContinuousLinearMap))
    ((mem_algebraicCurvatureTensorSubmodule.mp
      (metricRm04At_mem_algebraicCurvatureTensorSubmodule (S.base.metric r) x)).compContinuousLinearMap
        (ι r x).toContinuousLinearMap)
  have hiff (r : ℝ) (hr : r ∈ J) (z : V x) :
      ι r x z ∈ curvatureOperatorImageAnnihilatorAt (S.family.metric r) x
        ⟨metricRm04At (S.family.metric r) x,
          metricRm04At_mem_algebraicCurvatureTensorSubmodule (S.family.metric r) x⟩ ↔
      z ∈ ContinuousAlternatingMap.contractionAnnihilator
        (Submodule.map (exteriorPower.musicalEquiv (E := V x) 2).toLinearMap (R r).range) := by
    exact mem_curvatureOperatorImageAnnihilatorAt_pullback_musical_iff
      ((VectorBundle.finrank_eq ℝ F V x).trans hdim) (S.family.metric r) x
      ⟨metricRm04At (S.family.metric r) x,
        metricRm04At_mem_algebraicCurvatureTensorSubmodule (S.family.metric r) x⟩
      (ι r x) (hmetric r hr x) z
  have hmem (r : ℝ) (hr : r ∈ J) :
      ι r x v ∈ curvatureOperatorImageAnnihilatorAt (S.family.metric r) x
        ⟨metricRm04At (S.family.metric r) x,
          metricRm04At_mem_algebraicCurvatureTensorSubmodule (S.family.metric r) x⟩ := by
    apply (hiff r hr v).mpr
    have hv' : v ∈ ContinuousAlternatingMap.contractionAnnihilator
        (Submodule.map (exteriorPower.musicalEquiv (E := V x) 2).toLinearMap (R t₀).range) := by
      rw [← hiff t₀ ht₀ v]
      exact hv
    rw [← (hfixed t₀ ht₀ r hr).2]
    exact hv'
  have hzero (r : ℝ) (hr : r ∈ J) :
      ricciSharp (S.family.metric r) x (ι r x v) = 0 :=
    ricciSharp_eq_zero_of_mem_curvatureOperatorImageAnnihilatorAt
      (S.family.metric r) x (hmem r hr)
  exact uhlenbeck_section_eq_and_inner_eq_of_ricciSharp_eq_zero
    S hS hJ hreg x (fun r => ι r x v)
    (fun r hr => hode r hr x v) hzero

theorem exists_uhlenbeck_isometry_with_rank_one_fixed_section
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
    (hrank : ∀ t ∈ Ioo a b, ∀ x,
      Module.finrank ℝ (curvatureOperatorImageAt (S.family.metric t) x
        ⟨metricRm04At (S.family.metric t) x,
          metricRm04At_mem_algebraicCurvatureTensorSubmodule (S.family.metric t) x⟩) = 1) :
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
      (∀ t ∈ Ioo a b, ∀ x z,
        HasDerivWithinAt (fun r => ι r x z)
          (ricciSharp (S.family.metric t) x (ι t x z)) (Ioo a b) t) ∧
      (∀ t ∈ Ioo a b, ∀ x z w,
        (S.family.metric t).inner x (ι t x z) (ι t x w) = ⟪z, w⟫) ∧
      ∀ (x : M) (v : V x),
        ι₀ x v ∈ curvatureOperatorImageAnnihilatorAt (S.family.metric t₀) x
          ⟨metricRm04At (S.family.metric t₀) x,
            metricRm04At_mem_algebraicCurvatureTensorSubmodule (S.family.metric t₀) x⟩ →
        (∀ s ∈ Ioo a b, ∀ t ∈ Ioo a b, ι s x v = ι t x v) ∧
        (∀ s ∈ Ioo a b, ∀ t ∈ Ioo a b, ∀ w : TangentSpace I x,
          (S.family.metric s).inner x (ι s x v) w =
            (S.family.metric t).inner x (ι t x v) w) := by
  obtain ⟨ι, hinit, hι, hinv, hode, hmetric, -⟩ :=
    exists_uhlenbeck_isometry_with_constant_curvatureOperator_kernel_and_range
      (F := F) S hS hdim ht₀ hreg ι₀ hι₀ h₀ hR 1 hrank
  refine ⟨ι, hinit, hι, hinv, hode, hmetric, ?_⟩
  intro x v hv
  exact uhlenbeck_section_eq_and_inner_eq_of_mem_curvatureOperatorImageAnnihilatorAt
    S hS hdim ι ordConnected_Ioo hreg hι hmetric hode hR 1 hrank ht₀ x v
      (by simpa only [hinit x] using hv)

theorem uhlenbeck_unit_section_parallel_and_fixed_on_interval
    [ConnectedSpace M]
    {D : RealTimeInterval} (S : SolutionOn (I := I) (M := M) D) (hS : IsSolutionOn S)
    (hdim : Module.finrank ℝ E = 3)
    (ι : ℝ → ∀ x, V x ≃L[ℝ] TangentSpace I x)
    {α β : ℝ} (hreg : Ioo α β ⊆ D.regular)
    {J : Set ℝ} (hJ : J.OrdConnected) (hsub : J ⊆ Ioo α β)
    {t₀ : ℝ} (ht₀ : t₀ ∈ J)
    (hι : ContMDiffOn (𝓘(ℝ, ℝ).prod I) (I.prod 𝓘(ℝ, F →L[ℝ] E)) ∞
      (fun p : ℝ × M => TotalSpace.mk' (F →L[ℝ] E) p.2
        (E := fun y => V y →L[ℝ] TangentSpace I y)
        (ι p.1 p.2).toContinuousLinearMap) (J ×ˢ (univ : Set M)))
    (hmetric : ∀ t ∈ J, ∀ x v w,
      (S.family.metric t).inner x (ι t x v) (ι t x w) = ⟪v, w⟫)
    (hode : ∀ t ∈ J, ∀ x v, HasDerivWithinAt (fun s => ι s x v)
      (ricciSharp (S.family.metric t) x (ι t x v)) J t)
    (hR : ∀ t ∈ Ioo α β, ∀ x,
      (⟨metricRm04At (S.family.metric t) x,
        metricRm04At_mem_algebraicCurvatureTensorSubmodule (S.family.metric t) x⟩ :
          algebraicCurvatureTensorSubmodule (I := I) (M := M) x) ∈
            algebraicCurvatureOperatorNonnegativeCone (I := I) (M := M))
    (hrank : ∀ t ∈ J, ∀ x,
      Module.finrank ℝ (curvatureOperatorImageAt (S.family.metric t) x
        ⟨metricRm04At (S.family.metric t) x,
          metricRm04At_mem_algebraicCurvatureTensorSubmodule (S.family.metric t) x⟩) = 1)
    {U : Set M} (hU : IsOpen U) (v : ∀ x, V x)
    (hv : ContMDiffOn I (I.prod 𝓘(ℝ, F)) ∞
      (fun x => TotalSpace.mk' F x (v x)) U)
    (hunit : ∀ x ∈ U, ⟪v x, v x⟫ = (1 : ℝ))
    (hmem : ∀ x ∈ U,
      ι t₀ x (v x) ∈ curvatureOperatorImageAnnihilatorAt (S.family.metric t₀) x
        ⟨metricRm04At (S.family.metric t₀) x,
          metricRm04At_mem_algebraicCurvatureTensorSubmodule (S.family.metric t₀) x⟩) :
    (∀ t ∈ J, ContMDiffOn I (I.prod 𝓘(ℝ, E)) ∞
      (fun x => TotalSpace.mk' E x (ι t x (v x))) U) ∧
    (∀ t ∈ J, ∀ x ∈ U, (S.family.metric t).inner x (ι t x (v x)) (ι t x (v x)) = 1) ∧
    (∀ t ∈ J, ∀ x ∈ U,
      ι t x (v x) ∈ curvatureOperatorImageAnnihilatorAt (S.family.metric t) x
        ⟨metricRm04At (S.family.metric t) x,
          metricRm04At_mem_algebraicCurvatureTensorSubmodule (S.family.metric t) x⟩) ∧
    (∀ t ∈ J, ∀ x ∈ U, ∀ w : TangentSpace I x,
      (LeviCivita (S.family.metric t)) (fun y => ι t y (v y)) x w = 0) ∧
    (∀ s ∈ J, ∀ t ∈ J, ∀ x ∈ U, ι s x (v x) = ι t x (v x)) ∧
    (∀ s ∈ J, ∀ t ∈ J, ∀ x ∈ U, ∀ w : TangentSpace I x,
      (S.family.metric s).inner x (ι s x (v x)) w =
        (S.family.metric t).inner x (ι t x (v x)) w) := by
  let _ : ∀ y, FiniteDimensional ℝ (V y) := fun y => VectorBundle.finiteDimensional ℝ F V y
  have hdimF : Module.finrank ℝ F = 3 := by
    let x : M := Classical.choice (inferInstance : Nonempty M)
    exact (VectorBundle.finrank_eq ℝ F V x).symm.trans
      ((ι t₀ x).toLinearEquiv.finrank_eq.trans hdim)
  have hfixed x (hx : x ∈ U) :=
    uhlenbeck_section_eq_and_inner_eq_of_mem_curvatureOperatorImageAnnihilatorAt
      S hS hdimF ι hJ (hsub.trans hreg) hι hmetric hode
        (fun t ht => hR t (hsub ht)) 1 hrank ht₀ x (v x) (hmem x hx)
  have hVsmooth t (ht : t ∈ J) : ContMDiffOn I (I.prod 𝓘(ℝ, E)) ∞
      (fun x => TotalSpace.mk' E x (ι t x (v x))) U := by
    have hιt := hι.comp_contMDiff (contMDiff_const.prodMk contMDiff_id)
      (fun x => ⟨ht, mem_univ x⟩)
    exact hιt.contMDiffOn.clm_bundle_apply hv
  have hVunit t (ht : t ∈ J) x (hx : x ∈ U) :
      (S.family.metric t).inner x (ι t x (v x)) (ι t x (v x)) = 1 :=
    (hmetric t ht x (v x) (v x)).trans (hunit x hx)
  have hVmem t (ht : t ∈ J) x (hx : x ∈ U) :
      ι t x (v x) ∈ curvatureOperatorImageAnnihilatorAt (S.family.metric t) x
        ⟨metricRm04At (S.family.metric t) x,
          metricRm04At_mem_algebraicCurvatureTensorSubmodule (S.family.metric t) x⟩ := by
    have hline := (curvatureOperatorImageAnnihilatorAt_eq_and_inner_eq_of_rank_one_on_interval
      S hS hdim hJ (hsub.trans hreg) (fun t ht => hR t (hsub ht)) hrank ht ht₀ x).1
    dsimp only at hline
    rw [hline]
    rw [(hfixed x hx).1 t ht t₀ ht₀]
    exact hmem x hx
  refine ⟨hVsmooth, hVunit, hVmem, ?_,
    (fun s hs t ht x hx => (hfixed x hx).1 s hs t ht),
    (fun s hs t ht x hx w => (hfixed x hx).2 s hs t ht w)⟩
  intro t ht x hx w
  have hprev : (α + t) / 2 < t := by have := (hsub ht).1; linarith
  have hslab : Icc ((α + t) / 2) t ⊆ Ioo α β := by
    intro r hr
    exact ⟨by have := (hsub ht).1; linarith [hr.1], lt_of_le_of_lt hr.2 (hsub ht).2⟩
  obtain ⟨L, hLrank, hLfiber, hLparallel⟩ :=
    exists_smooth_parallel_curvatureOperatorImageLine hdim (S.family.metric t)
      (metricRm04 (S.family.metric t))
      (fun y => metricRm04At_mem_algebraicCurvatureTensorSubmodule (S.family.metric t) y)
      (hrank t ht)
      (curvatureOperatorKernelAt_parallel_at_later_time S hS hdim hprev
        (hslab.trans hreg) (fun r hr => hR r (hslab hr)))
  exact L.covariantDerivative_eq_zero_on_of_unit_of_rank_eq_one (S.family.metric t)
    hLrank hLparallel U hU (fun y => ι t y (v y))
    ((hVsmooth t ht).mdifferentiableOn (by simp))
    (fun y hy => (hLfiber y).symm ▸ hVmem t ht y hy) (hVunit t ht) x hx w

end DifferentialGeometry.PDE.RicciFlow
