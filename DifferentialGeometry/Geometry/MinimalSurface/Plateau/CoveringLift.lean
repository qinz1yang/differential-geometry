import DifferentialGeometry.Geometry.MinimalSurface.Plateau.MorreyDisk
import DifferentialGeometry.Topology.Covering.SmoothLift

set_option autoImplicit false
noncomputable section

open Manifold
open DifferentialGeometry.Topology
open scoped Manifold ContDiff

namespace DifferentialGeometry.Geometry

private theorem immersed_parameter_of_smooth_lift
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {M N : Type*} [TopologicalSpace M] [ChartedSpace E M]
    [TopologicalSpace N] [ChartedSpace E N]
    {γ : freeLoop N} (hγ : IsSmoothEmbeddedLoop (E := E) γ)
    (p : M → N) (hp : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, E) ∞ p)
    (γLift : freeLoop M)
    (hsLift : ContMDiff 𝓘(ℝ, ℝ) 𝓘(ℝ, E) ∞
      (fun t : ℝ => γLift (t : loopCircle)))
    (hloop : ∀ θ, p (γLift θ) = γ θ) :
    ∀ t : ℝ,
      mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, E) (fun s : ℝ => γLift (s : loopCircle)) t 1 ≠ 0 := by
  have heq : p ∘ (fun s : ℝ => γLift (s : loopCircle)) =
      (fun s : ℝ => γ (s : loopCircle)) := funext fun s => hloop (s : loopCircle)
  intro t hzero
  apply hγ.immersed t
  have hc := mfderiv_comp t
    (hp.mdifferentiable (by decide) (γLift (t : loopCircle)))
    (hsLift.mdifferentiable (by decide) t)
  have hc1 := congrArg (fun L : ℝ →L[ℝ] E => L 1) hc
  have hprojDeriv := congrArg
    (fun f : ℝ → N => (mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, E) f t 1 : E)) heq
  apply hprojDeriv.symm.trans
  apply hc1.trans
  change mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) p (γLift (t : loopCircle))
    (mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, E) (fun s : ℝ => γLift (s : loopCircle)) t 1) = 0
  rw [hzero, map_zero]

variable {E M N : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace M] [ChartedSpace E M] [TopologicalSpace N] [ChartedSpace E N]

/-- A continuous lift through a local diffeomorphism preserves smoothness,
embeddedness, and the nonzero periodic parameter derivative of the same loop. -/
theorem IsSmoothEmbeddedLoop.of_lift_through_localDiffeomorph
    {γ : freeLoop M} (hγ : IsSmoothEmbeddedLoop (E := E) γ) {p : N → M}
    (hps : IsLocalDiffeomorph 𝓘(ℝ, E) 𝓘(ℝ, E) ∞ p)
    (γLift : freeLoop N) (hloop : ∀ θ, p (γLift θ) = γ θ) :
    IsSmoothEmbeddedLoop (E := E) γLift := by
  have hs : ContMDiff 𝓘(ℝ, ℝ) 𝓘(ℝ, E) ∞
      (fun t : ℝ => γLift (t : loopCircle)) :=
    contMDiff_of_lift_through_localDiffeomorph hps hγ.smooth
      (⟨fun t : ℝ => γLift (t : loopCircle),
        γLift.continuous.comp (AddCircle.continuous_mk' (1 : ℝ))⟩ : C(ℝ, N))
      (fun t => hloop (t : loopCircle))
  refine ⟨hs, ?_, immersed_parameter_of_smooth_lift hγ p hps.contMDiff γLift hs hloop⟩
  have hcomp : p ∘ γLift = γ := funext hloop
  apply _root_.Topology.IsEmbedding.of_comp γLift.continuous hps.contMDiff.continuous
  simpa only [hcomp] using hγ.embedding

end DifferentialGeometry.Geometry
