import DifferentialGeometry.Geometry.Curvature.LocalPullbackRicci
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.StandardSolution.ShrinkingCylinder
import DifferentialGeometry.Geometry.Curvature.RicciRestriction
import DifferentialGeometry.Geometry.Metric.CylinderRotation
import DifferentialGeometry.Geometry.Metric.RoundCylinder

set_option autoImplicit false
noncomputable section
open Set TopologicalSpace Manifold DifferentialGeometry
open DifferentialGeometry.Geometry DifferentialGeometry.Geometry.Connection
open DifferentialGeometry.Geometry.Curvature DifferentialGeometry.Tensor0SBundle
open DifferentialGeometry.CheegerGromovCompactness
open scoped Manifold ContDiff

namespace DifferentialGeometry.PDE.RicciFlow

open DifferentialGeometry.Geometry.Metric DifferentialGeometry.Geometry.Curvature

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [Fact (Module.finrank ℝ E = 2 + 1)]

private local instance : FiniteDimensional ℝ E :=
  FiniteDimensional.of_fact_finrank_eq_succ 2

private theorem shrinkingCylinderMetric_affine_eval {t : ℝ} (ht : t < 1)
    (x : Metric.sphere (0 : E) 1 × ℝ)
    (v w : TangentSpace ((𝓡 2).prod 𝓘(ℝ)) x) :
    (shrinkingCylinderMetric (E := E) t).inner x v w =
      (shrinkingCylinderMetric (E := E) 0).inner x v w -
        (2 * t) * ricciTensor (shrinkingCylinderMetric (E := E) 0) x v w := by
  have h := congrFun (shrinkingCylinderMetric_affine (E := E) ht) x
  exact congrArg (fun b => b v w) h

theorem localPullMetric_shrinkingCylinderMetric_of_initial
    (U V : Opens (Metric.sphere (0 : E) 1 × ℝ)) (f : U → V)
    (hf : IsLocalDiffeomorph ((𝓡 2).prod 𝓘(ℝ)) ((𝓡 2).prod 𝓘(ℝ)) ∞ f)
    (hzero : localPullMetric ((shrinkingCylinderMetric (E := E) 0).restrictOpen V) f hf =
      (shrinkingCylinderMetric (E := E) 0).restrictOpen U)
    {t : ℝ} (ht : t < 1) :
    localPullMetric ((shrinkingCylinderMetric (E := E) t).restrictOpen V) f hf =
      (shrinkingCylinderMetric (E := E) t).restrictOpen U := by
  let : SigmaCompactSpace U := isSigmaCompact_iff_sigmaCompactSpace.mp
    (isSigmaCompact_of_isOpen ((𝓡 2).prod 𝓘(ℝ)) U.isOpen)
  let : SigmaCompactSpace V := isSigmaCompact_iff_sigmaCompactSpace.mp
    (isSigmaCompact_of_isOpen ((𝓡 2).prod 𝓘(ℝ)) V.isOpen)
  have hric (x : U) (v w : TangentSpace ((𝓡 2).prod 𝓘(ℝ)) x) :
      ricciTensor (shrinkingCylinderMetric (E := E) 0)
          (f x : Metric.sphere (0 : E) 1 × ℝ)
          (mfderiv ((𝓡 2).prod 𝓘(ℝ)) ((𝓡 2).prod 𝓘(ℝ)) f x v)
          (mfderiv ((𝓡 2).prod 𝓘(ℝ)) ((𝓡 2).prod 𝓘(ℝ)) f x w) =
        ricciTensor (shrinkingCylinderMetric (E := E) 0)
          (x : Metric.sphere (0 : E) 1 × ℝ) v w := by
    have h := ricciTensor_localPullMetric
      ((shrinkingCylinderMetric (E := E) 0).restrictOpen V) f hf x v w
    rw [hzero, ricciTensor_restrictOpen, ricciTensor_restrictOpen] at h
    simpa only [mfderiv_subtype_val_apply] using h.symm
  apply SmoothRiemannianMetric.ext_inner
  intro x v w
  have hz := congrArg
    (fun g : SmoothRiemannianMetric ((𝓡 2).prod 𝓘(ℝ)) U => g.inner x v w) hzero
  rw [localPullMetric_inner, SmoothRiemannianMetric.restrictOpen_inner,
    SmoothRiemannianMetric.restrictOpen_inner] at hz
  have ha := shrinkingCylinderMetric_affine_eval ht
    (f x : Metric.sphere (0 : E) 1 × ℝ)
    (mfderiv ((𝓡 2).prod 𝓘(ℝ)) ((𝓡 2).prod 𝓘(ℝ)) f x v)
    (mfderiv ((𝓡 2).prod 𝓘(ℝ)) ((𝓡 2).prod 𝓘(ℝ)) f x w)
  have hb := shrinkingCylinderMetric_affine_eval ht
    (x : Metric.sphere (0 : E) 1 × ℝ) v w
  have hc := congrArg₂ (fun a b : ℝ => a - (2 * t) * b) hz (hric x v w)
  rw [localPullMetric_inner, SmoothRiemannianMetric.restrictOpen_inner,
    SmoothRiemannianMetric.restrictOpen_inner]
  exact ha.trans (hc.trans hb.symm)

theorem pullback_shrinkingCylinderMetric_of_initial
    (U V : Opens (Metric.sphere (0 : E) 1 × ℝ))
    (Φ : U ≃ₘ⟮(𝓡 2).prod 𝓘(ℝ), (𝓡 2).prod 𝓘(ℝ)⟯ V)
    (hzero : Diffeomorph.pullbackMetric
      ((shrinkingCylinderMetric (E := E) 0).restrictOpen V) Φ =
        (shrinkingCylinderMetric (E := E) 0).restrictOpen U)
    {t : ℝ} (ht : t < 1) :
    Diffeomorph.pullbackMetric ((shrinkingCylinderMetric (E := E) t).restrictOpen V) Φ =
      (shrinkingCylinderMetric (E := E) t).restrictOpen U := by
  have hlocal (s : ℝ) :
      localPullMetric ((shrinkingCylinderMetric (E := E) s).restrictOpen V)
          Φ Φ.isLocalDiffeomorph =
        Diffeomorph.pullbackMetric ((shrinkingCylinderMetric (E := E) s).restrictOpen V) Φ := by
    apply SmoothRiemannianMetric.ext_inner
    intro x v w
    rw [localPullMetric_inner, Diffeomorph.pullbackMetric_inner]
  have h := localPullMetric_shrinkingCylinderMetric_of_initial U V Φ
    Φ.isLocalDiffeomorph ((hlocal 0).trans hzero) ht
  rw [hlocal t] at h
  exact h

theorem pullback_shrinkingCylinderMetric_roundCylinderRestrict
    (e : E ≃ₗᵢ[ℝ] E) (a : ℝ) (U : Opens (Metric.sphere (0 : E) 1 × ℝ))
    {t : ℝ} (ht : t < 1) :
    Diffeomorph.pullbackMetric
      ((shrinkingCylinderMetric (E := E) t).restrictOpen
        (roundCylinderImage (n := 2) e a U))
      (roundCylinderRestrict (n := 2) e a U) =
        (shrinkingCylinderMetric (E := E) t).restrictOpen U := by
  apply pullback_shrinkingCylinderMetric_of_initial U
    (roundCylinderImage (n := 2) e a U) (roundCylinderRestrict (n := 2) e a U) _ ht
  simpa only [shrinkingCylinderMetric_zero] using
    pullback_roundCylinderMetric_roundCylinderRestrict (n := 2) e a U

end DifferentialGeometry.PDE.RicciFlow

end
