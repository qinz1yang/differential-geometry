import DifferentialGeometry.Geometry.Flow.RicciFlow.Estimates.Uhlenbeck.FixedRicciGauge
import DifferentialGeometry.Geometry.Flow.RicciFlow.Estimates.Uhlenbeck.TerminalEvolution
import DifferentialGeometry.Geometry.Flow.RicciFlow.Estimates.Uhlenbeck.CurvatureOperatorRegularity
import DifferentialGeometry.Geometry.Curvature.CurvatureOperator.ExteriorPositivity

noncomputable section

open Bundle
open DifferentialGeometry DifferentialGeometry.Geometry.Connection
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Curvature.DimensionThree
open CovariantDerivative
open scoped Bundle Manifold ContDiff RealInnerProductSpace

namespace DifferentialGeometry.PDE.RicciFlow

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [CompleteSpace E] [NeZero (Module.finrank ℝ E)]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [T2Space M] [SigmaCompactSpace M] [BoundarylessManifold I M]
  {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]
  {V : M → Type*} [TopologicalSpace (TotalSpace F V)]
  [∀ x, NormedAddCommGroup (V x)] [∀ x, InnerProductSpace ℝ (V x)]
  [FiberBundle F V] [VectorBundle ℝ F V] [ContMDiffVectorBundle ∞ F V I]
  [IsContMDiffRiemannianBundle I ∞ F V]

theorem exists_nonnegative_curvatureOperator_sections_terminal_evolution
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
    letI : ∀ y, FiniteDimensional ℝ (V y) := fun y => VectorBundle.finiteDimensional ℝ F V y
    letI := Bundle.ExteriorPower.totalSpaceTopology F V 2
    letI := Bundle.ExteriorPower.fiberBundle F V 2
    letI := Bundle.ExteriorPower.vector_bundle F V 2
    letI := Bundle.ExteriorPower.contMDiffVectorBundle (IB := I) (n := ∞) F V 2
    letI := Bundle.ExteriorPower.isContMDiffRiemannianBundle (IB := I) (n := ∞) F V 2
    let cov := CovariantDerivative.pullbackFiberwiseLinearEquiv
      (fun y => (ι₀ y).toLinearEquiv)
      (hι₀.of_le (show (1 : ℕ∞ω) ≤ ∞ by simp)).clm_bundle_map
      (LeviCivita (S.family.metric b))
    ∃ ι : ℝ → ∀ x, V x ≃L[ℝ] TangentSpace I x,
      (∀ x, ι b x = ι₀ x) ∧
      let R := fun t x => exteriorPower.traceNormalizedCurvatureEndomorphism
        ((S.base.rm04 t x).compContinuousLinearMap (fun _ => (ι t x).toContinuousLinearMap))
        (by
          have hT := mem_algebraicCurvatureTensorSubmodule.mp
            (metricRm04At_mem_algebraicCurvatureTensorSubmodule (I := I) (S.base.metric t) x)
          exact hT.compContinuousLinearMap (ι t x).toContinuousLinearMap)
      ∃ A : ℝ → Cₛ^∞⟮I; (⋀[ℝ]^2 F) →L[ℝ] ⋀[ℝ]^2 F,
        (fun x : M => (⋀[ℝ]^2 (V x)) →L[ℝ] ⋀[ℝ]^2 (V x))⟯,
        (∀ t x, A t x = R t x) ∧
        (∀ t ∈ Set.Icc a b, ∀ x, (A t x).IsPositive) ∧
        ContMDiffCovariantDerivative (cov.exteriorPower 2) ∞ ∧
        (cov.exteriorPower 2).IsMetricCompatible ∧
        ∀ x, HasDerivWithinAt (fun s => A s x)
          (rawBundleEndomorphismConnLap (S.family.metric b) (cov.exteriorPower 2)
            (fun y => A b y) x +
            (curvatureOperatorReactionEndomorphism3 (A b x).toLinearMap).toContinuousLinearMap)
          (Set.Iic b) b := by
  dsimp only
  let _ : ∀ y, FiniteDimensional ℝ (V y) := fun y => VectorBundle.finiteDimensional ℝ F V y
  let _ := Bundle.ExteriorPower.totalSpaceTopology F V 2
  let _ := Bundle.ExteriorPower.fiberBundle F V 2
  let _ := Bundle.ExteriorPower.vector_bundle F V 2
  let _ := Bundle.ExteriorPower.contMDiffVectorBundle (IB := I) (n := ∞) F V 2
  let _ := Bundle.ExteriorPower.isContMDiffRiemannianBundle (IB := I) (n := ∞) F V 2
  obtain ⟨ι, hinit, hιsmooth, _, hode⟩ :=
    exists_gauge_with_fixed_ricci_generator (S.family.metric b) b ι₀ hι₀
  have hinitfun : ι b = ι₀ := funext hinit
  subst ι₀
  have hιslice (t : ℝ) : ContMDiff I (I.prod 𝓘(ℝ, F →L[ℝ] E)) ∞
      (fun x => TotalSpace.mk' (F →L[ℝ] E) x (ι t x).toContinuousLinearMap) :=
    hιsmooth.comp (contMDiff_const.prodMk contMDiff_id)
  let T := fun t x => (S.base.rm04 t x).compContinuousLinearMap
    (fun _ => (ι t x).toContinuousLinearMap)
  have hT (t : ℝ) (x : M) : IsAlgCurvForm (fun v w z y => T t x ![v, w, z, y]) :=
    (mem_algebraicCurvatureTensorSubmodule.mp
      (metricRm04At_mem_algebraicCurvatureTensorSubmodule (I := I) (S.base.metric t) x))
      |>.compContinuousLinearMap (ι t x).toContinuousLinearMap
  let R := fun t x => exteriorPower.traceNormalizedCurvatureEndomorphism (T t x) (hT t x)
  have hRsmooth (t : ℝ) :
      ContMDiff I (I.prod 𝓘(ℝ, (⋀[ℝ]^2 F) →L[ℝ] ⋀[ℝ]^2 F)) ∞
        (fun x => TotalSpace.mk' ((⋀[ℝ]^2 F) →L[ℝ] ⋀[ℝ]^2 F) x (R t x)) := by
    apply Bundle.ExteriorPower.contMDiff_traceNormalizedCurvatureEndomorphism F V ∞ le_rfl
    exact (S.base.rm04 t).contMDiff.multilinear_bundle_comp (fun _ => hιslice t)
  let A : ℝ → Cₛ^∞⟮I; (⋀[ℝ]^2 F) →L[ℝ] ⋀[ℝ]^2 F,
      (fun x : M => (⋀[ℝ]^2 (V x)) →L[ℝ] ⋀[ℝ]^2 (V x))⟯ :=
    fun t => ⟨R t, hRsmooth t⟩
  have hAeq (t : ℝ) (x : M) : A t x = R t x := rfl
  let cov := CovariantDerivative.pullbackFiberwiseLinearEquiv
    (fun y => ((ι b) y).toLinearEquiv)
    (hι₀.of_le (show (1 : ℕ∞ω) ≤ ∞ by simp)).clm_bundle_map
    (LeviCivita (S.family.metric b))
  let hcovsmooth : ContMDiffCovariantDerivative cov ∞ := by
    let _ : CompleteSpace F := FiniteDimensional.complete ℝ F
    have hiinv : ContMDiff I (I.prod 𝓘(ℝ, E →L[ℝ] F)) ∞
        (fun y => TotalSpace.mk' (E →L[ℝ] F) y ((ι b) y).symm.toContinuousLinearMap) := by
      simpa only [ContinuousLinearMap.inverse_equiv] using
        hι₀.clm_bundle_inverse (fun _ => ContinuousLinearMap.isInvertible_equiv)
    exact ContMDiffCovariantDerivative.pullbackFiberwiseLinearEquiv
      (fun y => ((ι b) y).toLinearEquiv) hι₀.clm_bundle_map hiinv.clm_bundle_map
      (LeviCivita (S.family.metric b))
  have hcovmetric : cov.IsMetricCompatible :=
    CovariantDerivative.isMetricCompatible_pullback_leviCivita
      (S.family.metric b) (ι b) (hι₀.of_le (show (1 : ℕ∞ω) ≤ ∞ by simp)) h₀
  refine ⟨ι, hinit, A, hAeq, ?_, cov.exteriorPower_contMDiff 2, hcovmetric.exteriorPower 2, ?_⟩
  · intro t ht x
    exact (traceNormalizedCurvatureEndomorphism_pullback_isPositive_of_mem_nonnegativeCone
      (metricAlgebraicCurvatureTensorAt (S.family.metric t) x) (hcone t ht x)
      (ι t x).toContinuousLinearMap)
  · intro x
    have hm : ∀ y v w, (S.family.metric b).inner y (ι b y v) (ι b y w) = ⟪v, w⟫ := by
      exact h₀
    have hd := traceNormalizedCurvatureEndomorphism_pullback_hasDerivWithinAt_terminal_of_solution
      (F := F) (V := V) S hS hab hslab hreg ι (hιslice b) hm x
      ((VectorBundle.finrank_eq ℝ F V x).trans hdim)
      (fun v => (hode x v b).hasDerivWithinAt)
    exact hd

end DifferentialGeometry.PDE.RicciFlow
