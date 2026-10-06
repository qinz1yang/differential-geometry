import DifferentialGeometry.Geometry.Comparison.Variation.Covariant.ChainRule
import DifferentialGeometry.Geometry.Connection.LeviCivita.SelfDerivative
import DifferentialGeometry.Geometry.Comparison.Variation.SecondVariation
import DifferentialGeometry.Topology.Diffeomorph.Flow

set_option autoImplicit false

noncomputable section

open Bundle Filter Manifold Set
open scoped ContDiff Manifold Topology

namespace DifferentialGeometry.Geometry

open Connection Curvature Riemannian Riemannian.Variation
open Riemannian.CovariantDerivativeAlong

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H}
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

variable [I.Boundaryless] [T2Space M]

/-- The covariant acceleration of the actual compact-support flow is the self
covariant derivative of its generating field, at the same flow point. -/
theorem covariantAcceleration_compactSupportFlow
    (g : SmoothRiemannianMetric I M) (X : ∀ x : M, TangentSpace I x)
    (hX : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞
      (fun x => (⟨x, X x⟩ : TangentBundle I M)))
    (hXc : HasCompactSupport X) (x : M) (t : ℝ) :
    let Φ := Diffeomorph.compactSupportFlow X hX hXc
    covDerivAlong (I := I) g (fun s : ℝ => Φ s x)
        (fun s => mfderiv 𝓘(ℝ, ℝ) I (fun r : ℝ => Φ r x) s (1 : ℝ)) t =
      (LeviCivita (I := I) g).toFun X (Φ t x) (X (Φ t x)) := by
  let Φ := Diffeomorph.compactSupportFlow X hX hXc
  let γ : ℝ → M := fun s => Φ s x
  have hγ : ContMDiff 𝓘(ℝ, ℝ) I ∞ γ :=
    (Diffeomorph.contMDiff_compactSupportFlow X hX hXc).comp
      (contMDiff_id.prodMk contMDiff_const)
  have hvelocity (s : ℝ) :
      (mfderiv 𝓘(ℝ, ℝ) I γ s (1 : ℝ) : E) = X (γ s) := by
    have hd := (Diffeomorph.isMIntegralCurve_compactSupportFlow X hX hXc x s).mfderiv
    have hv := congrArg (fun L : ℝ →L[ℝ] E => L (1 : ℝ)) hd
    change (mfderiv 𝓘(ℝ, ℝ) I γ s (1 : ℝ) : E) = (1 : ℝ) • X (γ s) at hv
    simpa only [one_smul] using hv
  have hacc := covDerivAlong_eq_leviCivita_of_eventuallyEq g γ t
    (hγ.contMDiffAt.of_le (by simp))
    (hX.mdifferentiableAt (by simp)) (Eventually.of_forall hvelocity)
  exact hacc.trans (congrArg ((LeviCivita (I := I) g).toFun X (γ t)) (hvelocity t))

/-- Restricting the same flow to an arbitrary source curve identifies its central
variation acceleration. No spatial smoothness of the source curve is needed. -/
theorem centralVariationAcceleration_compactSupportFlow
    (g : SmoothRiemannianMetric I M) (X : ∀ x : M, TangentSpace I x)
    (hX : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞
      (fun x => (⟨x, X x⟩ : TangentBundle I M)))
    (hXc : HasCompactSupport X) (U : ℝ → M) (r : ℝ) :
    let Φ := Diffeomorph.compactSupportFlow X hX hXc
    (centralVariationAcceleration (I := I) g (fun t s => Φ t (U s)) r : E) =
      (LeviCivita (I := I) g).toFun X (U r) (X (U r)) := by
  have hacc := covariantAcceleration_compactSupportFlow g X hX hXc (U r) 0
  have hzero : Diffeomorph.compactSupportFlow X hX hXc 0 (U r) = U r :=
    DFunLike.congr_fun (Diffeomorph.compactSupportFlow_zero X hX hXc) (U r)
  exact hacc.trans (congrArg
    (fun p : M => ((LeviCivita (I := I) g).toFun X p (X p) : E)) hzero)

/-- The acceleration derivative occurring in the actual second Gram formula is
the covariant derivative of the ambient acceleration along the original source. -/
theorem covDerivAlong_centralAcceleration_compactSupportFlow
    (g : SmoothRiemannianMetric I M) (X : ∀ x : M, TangentSpace I x)
    (hX : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞
      (fun x => (⟨x, X x⟩ : TangentBundle I M)))
    (hXc : HasCompactSupport X) (U : ℝ → M) (r : ℝ) :
    let Φ := Diffeomorph.compactSupportFlow X hX hXc
    (covDerivAlong (I := I) g (fun s => Φ 0 (U s))
        (centralVariationAcceleration (I := I) g (fun t s => Φ t (U s))) r : E) =
      covDerivAlong (I := I) g U
        (fun s => (LeviCivita (I := I) g).toFun X (U s) (X (U s))) r := by
  apply covDerivAlong_congr_curve g _ _
  · exact Eventually.of_forall fun s =>
      DFunLike.congr_fun (Diffeomorph.compactSupportFlow_zero X hX hXc) (U s)
  · exact Eventually.of_forall (centralVariationAcceleration_compactSupportFlow g X hX hXc U)

end DifferentialGeometry.Geometry
