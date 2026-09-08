import DifferentialGeometry.Geometry.Flow.RicciFlow.DimensionThree.CurvatureNullity
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
  let _ : ∀ y, FiniteDimensional ℝ (V y) := fun y => VectorBundle.finiteDimensional ℝ F V y
  obtain ⟨ι, hinit, hι, hinv, hode, hmetric, hfixed⟩ :=
    exists_uhlenbeck_isometry_with_constant_curvatureOperator_kernel_and_range
      (F := F) S hS hdim ht₀ hreg ι₀ hι₀ h₀ hR 1 hrank
  dsimp only at hfixed
  refine ⟨ι, hinit, hι, hinv, hode, hmetric, ?_⟩
  intro x v hv
  let R := fun r => exteriorPower.traceNormalizedCurvatureEndomorphism
    ((S.base.rm04 r x).compContinuousLinearMap (fun _ => (ι r x).toContinuousLinearMap))
    ((mem_algebraicCurvatureTensorSubmodule.mp
      (metricRm04At_mem_algebraicCurvatureTensorSubmodule (S.base.metric r) x)).compContinuousLinearMap
        (ι r x).toContinuousLinearMap)
  have hiff (r : ℝ) (hr : r ∈ Ioo a b) (z : V x) :
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
  have hmem (r : ℝ) (hr : r ∈ Ioo a b) :
      ι r x v ∈ curvatureOperatorImageAnnihilatorAt (S.family.metric r) x
        ⟨metricRm04At (S.family.metric r) x,
          metricRm04At_mem_algebraicCurvatureTensorSubmodule (S.family.metric r) x⟩ := by
    apply (hiff r hr v).mpr
    have hv' : v ∈ ContinuousAlternatingMap.contractionAnnihilator
        (Submodule.map (exteriorPower.musicalEquiv (E := V x) 2).toLinearMap (R t₀).range) := by
      rw [← hiff t₀ ht₀ v]
      rw [hinit x]
      exact hv
    rw [← (hfixed t₀ ht₀ r hr x).2]
    exact hv'
  have hzero (r : ℝ) (hr : r ∈ Ioo a b) :
      ricciSharp (S.family.metric r) x (ι r x v) = 0 :=
    ricciSharp_eq_zero_of_mem_curvatureOperatorImageAnnihilatorAt
      (S.family.metric r) x (hmem r hr)
  exact uhlenbeck_section_eq_and_inner_eq_of_ricciSharp_eq_zero
    S hS ordConnected_Ioo hreg x (fun r => ι r x v)
    (fun r hr => hode r hr x v) hzero

end DifferentialGeometry.PDE.RicciFlow
