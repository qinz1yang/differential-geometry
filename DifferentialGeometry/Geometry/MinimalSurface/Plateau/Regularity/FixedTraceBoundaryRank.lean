import DifferentialGeometry.Geometry.MinimalSurface.Plateau.SmoothTraceLift
import DifferentialGeometry.Geometry.MinimalSurface.Plateau.AngleTrace
import DifferentialGeometry.Geometry.MinimalSurface.Plateau.DiskBoundaryMetric

set_option autoImplicit false

noncomputable section

open Manifold Set Metric
open DifferentialGeometry.Topology
open scoped Manifold ContDiff

namespace DifferentialGeometry.Geometry

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]

theorem SmoothDiskExtension.exists_regular_signed_trace_lift
    {γ : freeLoop M} {u : C(closedDisk, M)} {U : ℂ → M}
    (hU : SmoothDiskExtension (E := E) u U) (hγ : IsSmoothEmbeddedLoop (E := E) γ)
    {σ : C(loopCircle, loopCircle)} (hσ : IsWeaklyMonotoneOnce σ)
    (htrace : diskTrace u = γ.comp σ)
    (hrank : ∀ z ∈ sphere (0 : ℂ) 1,
      Function.Injective (mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, E) U z)) :
    ∃ ψ : ℝ → ℝ, ContDiff ℝ ∞ ψ ∧
      (∀ t : ℝ, (ψ t : loopCircle) = σ (t : loopCircle)) ∧
      ((Monotone ψ ∧ (∀ t, ψ (t + 1) = ψ t + 1) ∧ ∀ t, 0 < deriv ψ t) ∨
       (Antitone ψ ∧ (∀ t, ψ (t + 1) = ψ t - 1) ∧ ∀ t, deriv ψ t < 0)) := by
  obtain ⟨ψ, hψc, hlift, hsign⟩ := hσ
  have hψ : ContDiff ℝ ∞ ψ :=
    hγ.contDiff_weakTraceLift hU.smoothUpToBoundary htrace hψc hlift
  let φ : ℝ → ℝ := fun θ => ψ (θ / (2 * Real.pi))
  have hφ : ContDiff ℝ ∞ φ := hψ.comp (contDiff_id.div_const _)
  have hangle := hU.angle_trace htrace (fun θ => hlift (θ / (2 * Real.pi)))
  have hderne (t : ℝ) : deriv ψ t ≠ 0 := by
    intro hzero
    let θ : ℝ := 2 * Real.pi * t
    have hquot : θ / (2 * Real.pi) = t := by
      dsimp only [θ]
      field_simp
    have hfzero : fderiv ℝ ψ t = 0 := by
      ext
      simp [fderiv_eq_smul_deriv, hzero]
    have hφfzero : fderiv ℝ φ θ = 0 := by
      change fderiv ℝ (ψ ∘ (fun s : ℝ => s / (2 * Real.pi))) θ = 0
      have hscale : DifferentiableAt ℝ (fun s : ℝ => s / (2 * Real.pi)) θ :=
        differentiableAt_id.div_const (2 * Real.pi)
      rw [fderiv_comp θ (hψ.differentiable (by simp) _) hscale, hquot, hfzero]
      simp
    have hφzero : mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) φ θ (1 : ℝ) = 0 := by
      rw [mfderiv_eq_fderiv, hφfzero]
      rfl
    have hz : circleMap 0 1 θ ∈ sphere (0 : ℂ) 1 := by
      simp only [mem_sphere_zero_iff_norm, norm_circleMap_zero, abs_one]
    have hUd : MDifferentiableAt 𝓘(ℝ, ℂ) 𝓘(ℝ, E) U (circleMap 0 1 θ) := by
      obtain ⟨_, N, hN, hDN, hUs⟩ := hU
      exact (hUs.contMDiffAt (hN.mem_nhds (hDN (sphere_subset_closedBall hz)))).mdifferentiableAt
        (by simp)
    have hchain := mfderiv_comp (I := 𝓘(ℝ, ℝ)) (I' := 𝓘(ℝ, ℝ))
      (I'' := 𝓘(ℝ, E)) θ (hγ.smooth.mdifferentiable (by simp) (φ θ))
        (hφ.contMDiff.mdifferentiable (by simp) θ)
    have hvalue := congrArg (fun D : ℝ →L[ℝ] E => D 1) hchain
    change mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, E)
        ((fun s : ℝ => γ (s : loopCircle)) ∘ φ) θ (1 : ℝ) =
      mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, E) (fun s : ℝ => γ (s : loopCircle)) (φ θ)
        (mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) φ θ (1 : ℝ)) at hvalue
    rw [hφzero, map_zero, ← hangle, mfderiv_diskMapBoundary hUd] at hvalue
    have hv : Complex.I * circleMap 0 1 θ = (0 : ℂ) :=
      hrank _ hz (hvalue.trans (map_zero _).symm)
    exact (mul_ne_zero Complex.I_ne_zero (circleMap_ne_center one_ne_zero)) hv
  refine ⟨ψ, hψ, hlift, ?_⟩
  rcases hsign with ⟨hm, hp⟩ | ⟨hm, hp⟩
  · exact Or.inl ⟨hm, hp, fun t => lt_of_le_of_ne hm.deriv_nonneg (hderne t).symm⟩
  · exact Or.inr ⟨hm, hp, fun t => lt_of_le_of_ne hm.deriv_nonpos (hderne t)⟩

end DifferentialGeometry.Geometry
