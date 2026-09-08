import DifferentialGeometry.Geometry.Connection.PullbackMetric
import DifferentialGeometry.Geometry.Connection.LeviCivita.Defs
import DifferentialGeometry.Bundle.Hom.Regularity

set_option autoImplicit false

noncomputable section

open Bundle CovariantDerivative
open DifferentialGeometry DifferentialGeometry.Geometry.Connection
open scoped Bundle Manifold ContDiff RealInnerProductSpace

namespace CovariantDerivative

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M]
  [BoundarylessManifold I M]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  {V : M → Type*} [TopologicalSpace (TotalSpace F V)]
  [∀ x, NormedAddCommGroup (V x)] [∀ x, InnerProductSpace ℝ (V x)]
  [FiberBundle F V] [VectorBundle ℝ F V] [ContMDiffVectorBundle ∞ F V I]
  [IsContMDiffRiemannianBundle I 1 F V]

theorem isMetricCompatible_pullback_leviCivita
    (g : SmoothRiemannianMetric I M)
    (ι : ∀ x, V x ≃L[ℝ] TangentSpace I x)
    (hι : ContMDiff I (I.prod 𝓘(ℝ, F →L[ℝ] E)) 1
      (fun x => TotalSpace.mk' (F →L[ℝ] E) x (ι x).toContinuousLinearMap))
    (hmetric : ∀ x v w, g.inner x (ι x v) (ι x w) = ⟪v, w⟫) :
    (pullbackFiberwiseLinearEquiv (fun y => (ι y).toLinearEquiv) hι.clm_bundle_map
      (LeviCivita g)).IsMetricCompatible := by
  let : RiemannianBundle (TangentSpace I : M → Type _) := ⟨g.toRiemannianMetric⟩
  let targetNorm : ∀ x : M, NormedAddCommGroup (TangentSpace I x) := fun x =>
    Bundle.instNormedAddCommGroupOfRiemannianBundleOfIsTopologicalAddGroupOfContinuousConstSMulReal x
  let : ∀ x : M, SeminormedAddCommGroup (TangentSpace I x) :=
    fun x => (targetNorm x).toSeminormedAddCommGroup
  let : ∀ x : M, InnerProductSpace ℝ (TangentSpace I x) := fun x => Bundle.instInnerProductSpaceReal x
  let : IsContMDiffRiemannianBundle I 1 E (TangentSpace I : M → Type _) :=
    ⟨g.inner, g.contMDiff.of_le (by simp), fun _ _ _ => rfl⟩
  have hc : @CovariantDerivative.IsMetricCompatible E _ _ H _ I M _ _ E _ _
      (TangentSpace I : M → Type _) _ targetNorm _ _ (LeviCivita g) _ _ _ _ := by
    apply (isMetricCompatible_iff _).mpr
    intro x X σ τ _ hσ hτ
    exact (LeviCivita_isMetricCompatible g).apply hσ hτ (X x)
  exact hc.pullbackFiberwiseLinearEquiv (fun x => (ι x).toLinearEquiv) hι.clm_bundle_map hmetric

section

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  {F G : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  [NormedAddCommGroup G] [NormedSpace ℝ G]
  {V : M → Type*} [TopologicalSpace (TotalSpace F V)]
  [∀ x, NormedAddCommGroup (V x)] [∀ x, NormedSpace ℝ (V x)]
  [FiberBundle F V] [VectorBundle ℝ F V]
  {W : M → Type*} [TopologicalSpace (TotalSpace G W)]
  [∀ x, NormedAddCommGroup (W x)] [∀ x, NormedSpace ℝ (W x)]
  [FiberBundle G W] [VectorBundle ℝ G W]

theorem pullback_leviCivita_conjugate
    (g : DifferentialGeometry.SmoothRiemannianMetric I M)
    (ι : ∀ x, V x ≃L[ℝ] TangentSpace I x)
    (κ : ∀ x, W x ≃L[ℝ] TangentSpace I x)
    (U : ∀ x, W x ≃L[ℝ] V x)
    (hι : ContMDiff I (I.prod 𝓘(ℝ, F →L[ℝ] E)) 1
      (fun x => TotalSpace.mk' (F →L[ℝ] E) x (ι x).toContinuousLinearMap))
    (hκ : ContMDiff I (I.prod 𝓘(ℝ, G →L[ℝ] E)) 1
      (fun x => TotalSpace.mk' (G →L[ℝ] E) x (κ x).toContinuousLinearMap))
    (hU : ContMDiff I (I.prod 𝓘(ℝ, G →L[ℝ] F)) 1
      (fun x => TotalSpace.mk' (G →L[ℝ] F) x (U x).toContinuousLinearMap))
    (heq : ∀ x, κ x = (U x).trans (ι x)) :
    pullbackFiberwiseLinearEquiv (fun y => (κ y).toLinearEquiv) hκ.clm_bundle_map (LeviCivita g) =
      pullbackFiberwiseLinearEquiv (fun y => (U y).toLinearEquiv) hU.clm_bundle_map
        (pullbackFiberwiseLinearEquiv (fun y => (ι y).toLinearEquiv) hι.clm_bundle_map
          (LeviCivita g)) := by
  have hk : κ = fun y => (U y).trans (ι y) := funext heq
  subst κ
  exact pullbackFiberwiseLinearEquiv_trans (fun y => (U y).toLinearEquiv) hU.clm_bundle_map
    (fun y => (ι y).toLinearEquiv) hι.clm_bundle_map (LeviCivita g)


end

end CovariantDerivative
