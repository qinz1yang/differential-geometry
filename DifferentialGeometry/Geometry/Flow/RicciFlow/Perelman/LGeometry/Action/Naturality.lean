import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.LGeometry.Defs
import DifferentialGeometry.Geometry.Flow.RicciFlow.Compactness.Solutions.Pullback
import DifferentialGeometry.Geometry.Flow.RicciFlow.Compactness.Solutions.OpenRestriction
import DifferentialGeometry.Topology.Manifold.Diffeomorph
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.LGeometry.Action.Regularized.Defs
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.LGeometry.Cost.Defs

set_option autoImplicit false

noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow.Perelman

open Bundle
open scoped Manifold ContDiff
open DifferentialGeometry.Geometry.Curvature

universe uM uN uE uH

variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace Real E]
  [FiniteDimensional Real E]
variable {H : Type uH} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H} [I.Boundaryless]
variable {M : Type uM} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [T2Space M]
variable {D : RealTimeInterval}

section Pullback

variable [SigmaCompactSpace M]
variable {N : Type uN} [TopologicalSpace N] [ChartedSpace H N]
  [IsManifold I ∞ N] [T2Space N]

theorem lDensity_pullback
    (S : SolutionOn (I := I) (M := N) D) (Φ : M ≃ₘ⟮I, I⟯ N)
    (T : Real) (alpha : Real → M) (s : Real) :
    lDensity (solutionOnPullback (I := I) S Φ) T alpha s =
      lDensity S T (fun r => Φ (alpha r)) s := by
  have hvel : lVelocity (I := I) (fun r => Φ (alpha r)) s =
      mfderiv I I Φ (alpha s) (lVelocity (I := I) alpha s) := by
    change (mfderiv 𝓘(Real, Real) I (Φ ∘ alpha) s) (1 : Real) = _
    rw [Φ.mfderiv_comp (by decide)]
    rfl
  unfold lDensity lSpeedSq
  rw [scalar_pullback (I := I) S Φ]
  rw [show (solutionOnPullback (I := I) S Φ).base.metric (T - s) =
      Diffeomorph.pullbackMetric (I := I) (S.base.metric (T - s)) Φ from rfl]
  rw [Diffeomorph.pullbackMetric_inner, hvel]

theorem lLength_pullback
    (S : SolutionOn (I := I) (M := N) D) (Φ : M ≃ₘ⟮I, I⟯ N)
    (T : Real) (alpha : Real → M) (a b : Real) :
    lLength (solutionOnPullback (I := I) S Φ) T alpha a b =
      lLength S T (fun r => Φ (alpha r)) a b := by
  unfold lLength
  apply intervalIntegral.integral_congr
  intro s _
  exact lDensity_pullback S Φ T alpha s

end Pullback

theorem lDensity_restrictOpen
    (S : SolutionOn (I := I) (M := M) D)
    (U : TopologicalSpace.Opens M) [SigmaCompactSpace U]
    (T : Real) (gamma : Real → U) (s : Real) :
    lDensity (CheegerGromovCompactness.solutionOnRestrictOpen (I := I) S U) T gamma s =
      lDensity S T (fun r => (gamma r : M)) s := by
  have hvel : lVelocity (I := I) (fun r => (gamma r : M)) s =
      lVelocity (I := I) gamma s := by
    unfold lVelocity
    rw [mfderiv_subtypeVal_comp]
    rfl
  unfold lDensity lSpeedSq
  rw [CheegerGromovCompactness.scalar_restrictOpen]
  change Real.sqrt s *
      (S.scalar (T - s) (gamma s : M) +
        ((S.base.metric (T - s)).restrictOpen (I := I) U).inner
          (gamma s) (lVelocity (I := I) gamma s) (lVelocity (I := I) gamma s)) = _
  rw [SmoothRiemannianMetric.restrictOpen_inner, hvel]

theorem lLength_restrictOpen
    (S : SolutionOn (I := I) (M := M) D)
    (U : TopologicalSpace.Opens M) [SigmaCompactSpace U]
    (T : Real) (gamma : Real → U) (a b : Real) :
    lLength (CheegerGromovCompactness.solutionOnRestrictOpen (I := I) S U) T gamma a b =
      lLength S T (fun s => (gamma s : M)) a b := by
  unfold lLength
  apply intervalIntegral.integral_congr
  intro s _
  exact lDensity_restrictOpen S U T gamma s

section CrossModel

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
  [FiniteDimensional ℝ F]
  {G : Type*} [TopologicalSpace G] {J : ModelWithCorners ℝ F G} [J.Boundaryless]
  {N : Type*} [TopologicalSpace N] [ChartedSpace G N] [IsManifold J ∞ N]
  [T2Space N]

theorem lDensity_pullback_cross
    (S : SolutionOn (I := J) (M := N) D) (Φ : M ≃ₘ⟮I, J⟯ N)
    (T : ℝ) (alpha : ℝ → M) (s : ℝ) :
    lDensity (S.pullback Φ) T alpha s =
      lDensity S T (fun r => Φ (alpha r)) s := by
  have hvel : lVelocity (I := J) (fun r => Φ (alpha r)) s =
      mfderiv I J Φ (alpha s) (lVelocity (I := I) alpha s) := by
    change (mfderiv 𝓘(ℝ, ℝ) J (Φ ∘ alpha) s) (1 : ℝ) = _
    rw [Φ.mfderiv_comp (by decide)]
    rfl
  unfold lDensity lSpeedSq
  rw [SolutionOn.pullback_scalar]
  rw [show (S.pullback Φ).base.metric (T - s) =
      Diffeomorph.pullbackMetricCross (S.base.metric (T - s)) Φ from rfl]
  rw [Diffeomorph.pullbackMetricCross_inner, hvel]

theorem lLength_pullback_cross
    (S : SolutionOn (I := J) (M := N) D) (Φ : M ≃ₘ⟮I, J⟯ N)
    (T : ℝ) (alpha : ℝ → M) (a b : ℝ) :
    lLength (S.pullback Φ) T alpha a b =
      lLength S T (fun r => Φ (alpha r)) a b := by
  unfold lLength
  apply intervalIntegral.integral_congr
  intro s _
  exact lDensity_pullback_cross S Φ T alpha s

end CrossModel

end DifferentialGeometry.PDE.RicciFlow.Perelman

noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow.Perelman

open DifferentialGeometry.Geometry.Curvature
open scoped Manifold ContDiff

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
  [FiniteDimensional ℝ F]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {G : Type*} [TopologicalSpace G] {J : ModelWithCorners ℝ F G}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  {N : Type*} [TopologicalSpace N] [ChartedSpace G N] [IsManifold J ∞ N]
  [T2Space M] [T2Space N]
  [BoundarylessManifold I M] [BoundarylessManifold J N]
  {D : RealTimeInterval}

theorem lRegularizedLagrangian_pullback
    (S : SolutionOn (I := J) (M := N) D) (Phi : M ≃ₘ⟮I, J⟯ N)
    (T : ℝ) (alpha : ℝ → M) (s : ℝ) :
    lRegularizedLagrangian (S.pullback Phi) T alpha s =
      lRegularizedLagrangian S T (Phi ∘ alpha) s := by
  have hvel : lVelocity (I := J) (Phi ∘ alpha) s =
      mfderiv I J Phi (alpha s) (lVelocity (I := I) alpha s) := by
    change (mfderiv 𝓘(ℝ, ℝ) J (Phi ∘ alpha) s) 1 = _
    rw [Phi.mfderiv_comp (by decide)]
    rfl
  simp only [lRegularizedLagrangian, SolutionOn.pullback_scalar, hvel]
  congr 1

theorem lRegularizedAction_pullback
    (S : SolutionOn (I := J) (M := N) D) (Phi : M ≃ₘ⟮I, J⟯ N)
    (T : ℝ) (alpha : ℝ → M) (a b : ℝ) :
    lRegularizedAction (S.pullback Phi) T alpha a b =
      lRegularizedAction S T (Phi ∘ alpha) a b := by
  unfold lRegularizedAction
  congr 1
  funext s
  exact lRegularizedLagrangian_pullback S Phi T alpha s

theorem lRegularizedCostC1_pullback
    (S : SolutionOn (I := J) (M := N) D) (Phi : M ≃ₘ⟮I, J⟯ N)
    (T a b : ℝ) (x y : M) :
    lRegularizedCostC1 (S.pullback Phi) T a b x y =
      lRegularizedCostC1 S T a b (Phi x) (Phi y) := by
  unfold lRegularizedCostC1
  apply congrArg sInf
  ext r
  constructor
  · rintro ⟨alpha, halpha, hstart, hend, hact⟩
    refine ⟨Phi ∘ alpha, (Phi.contMDiff.of_le (by simp)).comp halpha, ?_, ?_, ?_⟩
    · exact congrArg Phi hstart
    · exact congrArg Phi hend
    · rw [← lRegularizedAction_pullback S Phi]
      exact hact
  · rintro ⟨alpha, halpha, hstart, hend, hact⟩
    refine ⟨Phi.symm ∘ alpha, (Phi.symm.contMDiff.of_le (by simp)).comp halpha, ?_, ?_, ?_⟩
    · simpa only [Function.comp_apply, Phi.symm_apply_apply] using congrArg Phi.symm hstart
    · simpa only [Function.comp_apply, Phi.symm_apply_apply] using congrArg Phi.symm hend
    · rw [lRegularizedAction_pullback S Phi]
      have heq : Phi ∘ (Phi.symm ∘ alpha) = alpha := by
        funext s
        exact Phi.apply_symm_apply (alpha s)
      rw [heq]
      exact hact

theorem lCost_pullback
    (S : SolutionOn (I := J) (M := N) D) (Phi : M ≃ₘ⟮I, J⟯ N)
    (T : ℝ) (x y : M) (tau : ℝ) :
    lCost (S.pullback Phi) T x y tau = lCost S T (Phi x) (Phi y) tau := by
  have hlength (alpha : ℝ → M) (a b : ℝ) :
      lLength (S.pullback Phi) T alpha a b =
        lLength S T (Phi ∘ alpha) a b := by
    unfold lLength
    congr 1
    funext s
    have hvel : lVelocity (I := J) (Phi ∘ alpha) s =
        mfderiv I J Phi (alpha s) (lVelocity (I := I) alpha s) := by
      change (mfderiv 𝓘(ℝ, ℝ) J (Phi ∘ alpha) s) 1 = _
      rw [Phi.mfderiv_comp (by decide)]
      rfl
    simp only [lDensity, lSpeedSq, SolutionOn.pullback_scalar, hvel]
    congr 2
  unfold lCost
  apply congrArg sInf
  ext r
  constructor
  · rintro ⟨alpha, halpha, hstart, hend, hact⟩
    refine ⟨Phi ∘ alpha, (Phi.contMDiff.of_le (by simp)).comp halpha, ?_, ?_, ?_⟩
    · exact congrArg Phi hstart
    · exact congrArg Phi hend
    · rw [show squareRootReparametrization (Phi ∘ alpha) =
        Phi ∘ squareRootReparametrization alpha from rfl, ← hlength]
      exact hact
  · rintro ⟨alpha, halpha, hstart, hend, hact⟩
    refine ⟨Phi.symm ∘ alpha, (Phi.symm.contMDiff.of_le (by simp)).comp halpha, ?_, ?_, ?_⟩
    · simpa only [Function.comp_apply, Phi.symm_apply_apply] using congrArg Phi.symm hstart
    · simpa only [Function.comp_apply, Phi.symm_apply_apply] using congrArg Phi.symm hend
    · rw [hlength]
      have heq : Phi ∘ squareRootReparametrization (Phi.symm ∘ alpha) =
          squareRootReparametrization alpha := by
        funext s
        exact Phi.apply_symm_apply _
      rw [heq]
      exact hact

end DifferentialGeometry.PDE.RicciFlow.Perelman

end
