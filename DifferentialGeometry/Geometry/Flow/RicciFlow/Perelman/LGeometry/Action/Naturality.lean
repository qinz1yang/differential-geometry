import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.LGeometry.Defs
import DifferentialGeometry.Geometry.Flow.RicciFlow.Compactness.Solutions.Pullback
import DifferentialGeometry.Geometry.Flow.RicciFlow.Compactness.Solutions.OpenRestriction
import DifferentialGeometry.Topology.Manifold.Diffeomorph

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
