import DifferentialGeometry.Geometry.Connection.ProductAlongCurve
import DifferentialGeometry.Geometry.Submanifold.SecondFundamentalForm.AlongCurve
import DifferentialGeometry.Bundle.VelocityLift

noncomputable section

open Bundle Manifold
open scoped Manifold ContDiff

namespace DifferentialGeometry.Geometry

open Riemannian.CovariantDerivativeAlong

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
    {K : Type*} [TopologicalSpace K] {J : ModelWithCorners ℝ F K}
    {N : Type*} [TopologicalSpace N] [ChartedSpace K N] [IsManifold J ∞ N]
    [T2Space M] [T2Space N] [BoundarylessManifold I M] [BoundarylessManifold J N]

theorem hasVanishingSecondFundamentalFormAlongCurves_prod_left
    (g : SmoothRiemannianMetric I M) (h : SmoothRiemannianMetric J N) (q : N) :
    hasVanishingSecondFundamentalFormAlongCurves g (g.prod h) (fun p : M => (p, q)) := by
  intro γ t hγ
  have hV : MDifferentiableAt 𝓘(ℝ, ℝ) I.tangent
      (fun s => (⟨γ s, mfderiv 𝓘(ℝ, ℝ) I γ s (1 : ℝ)⟩ : TangentBundle I M)) t :=
    ((hγ t).velocityLift (m := ∞) (by simp)).mdifferentiableAt (by simp)
  have hVq : MDifferentiableAt 𝓘(ℝ, ℝ) J.tangent
      (fun _ : ℝ => (⟨q, (0 : TangentSpace J q)⟩ : TangentBundle J N)) t :=
    mdifferentiableAt_const
  have hsplit := Connection.covDerivAlong_prod g h γ (fun _ => q)
    (fun s => mfderiv 𝓘(ℝ, ℝ) I γ s (1 : ℝ)) (fun _ => (0 : TangentSpace J q)) t hV hVq
  have hv (s : ℝ) :
      mfderiv 𝓘(ℝ, ℝ) (I.prod J) (fun u => (γ u, q)) s (1 : ℝ) =
        (mfderiv 𝓘(ℝ, ℝ) I γ s (1 : ℝ), (0 : TangentSpace J q)) := by
    rw [mfderiv_prodMk (hγ.mdifferentiableAt (by simp)) mdifferentiableAt_const,
      mfderiv_const]
    rfl
  apply sub_eq_zero.mpr
  change covDerivAlong (g.prod h) (fun s => (γ s, q))
      (fun s => mfderiv 𝓘(ℝ, ℝ) (I.prod J) (fun u => (γ u, q)) s (1 : ℝ)) t = _
  have hfields : (fun s => mfderiv 𝓘(ℝ, ℝ) (I.prod J) (fun u => (γ u, q)) s (1 : ℝ)) =
      (fun s => (mfderiv 𝓘(ℝ, ℝ) I γ s (1 : ℝ), (0 : TangentSpace J q))) := funext hv
  calc
    _ = covDerivAlong (g.prod h) (fun s => (γ s, q))
        (fun s => (mfderiv 𝓘(ℝ, ℝ) I γ s (1 : ℝ), (0 : TangentSpace J q))) t :=
      congrArg (fun V => covDerivAlong (g.prod h) (fun s => (γ s, q)) V t) hfields
    _ = (show TangentSpace (I.prod J) (γ t, q) from
        (covDerivAlong g γ (fun s => mfderiv 𝓘(ℝ, ℝ) I γ s (1 : ℝ)) t,
        covDerivAlong h (fun _ => q) (fun _ => (0 : TangentSpace J q)) t)) := hsplit
    _ = (show TangentSpace (I.prod J) (γ t, q) from
        (covariantAcceleration g γ t, (0 : TangentSpace J q))) := by
      rw [covDerivAlong_zero]
      rfl
    _ = _ := by
      rw [mfderiv_prod_left]
      rfl

end DifferentialGeometry.Geometry
