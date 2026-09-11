import DifferentialGeometry.Geometry.MinimalSurface.Plateau.ImmersionTraceLift
import DifferentialGeometry.Geometry.MinimalSurface.Plateau.SmoothDiskTrace



noncomputable section

open Set Function Manifold ContinuousMap
open DifferentialGeometry.Topology
open scoped Topology ContDiff Manifold

namespace DifferentialGeometry.Geometry

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]

omit [FiniteDimensional ℝ E] in
theorem realContinuousLinearMap_injective_of_one_ne_zero (L : ℝ →L[ℝ] E)
    (h : L 1 ≠ 0) : Injective L := by
  intro a b hab
  have hz : (a - b) • L 1 = 0 := by
    rw [← map_smul, smul_eq_mul, mul_one, map_sub, hab, sub_self]
  exact sub_eq_zero.mp ((smul_eq_zero.mp hz).resolve_right h)




theorem IsSmoothEmbeddedLoop.contDiff_parameterLift {γ : freeLoop M}
    (hγ : IsSmoothEmbeddedLoop (E := E) γ) {ψ : ℝ → ℝ} (hψ : Continuous ψ)
    (hc : ContMDiff 𝓘(ℝ, ℝ) 𝓘(ℝ, E) ∞ (fun t => γ (ψ t : loopCircle))) :
    ContDiff ℝ ∞ ψ := by
  rw [contDiff_iff_contDiffAt]
  intro t
  exact contDiffAt_parameterLift_of_manifoldImmersion hγ.smooth
    (realContinuousLinearMap_injective_of_one_ne_zero _ (hγ.immersed (ψ t)))
    hψ.continuousAt (hc.contMDiffAt)



theorem IsSmoothEmbeddedLoop.contDiff_weakTraceLift {γ : freeLoop M}
    (hγ : IsSmoothEmbeddedLoop (E := E) γ) {u : C(closedDisk, M)}
    (hu : DiskSmoothUpToBoundary (E := E) u) {σ : C(loopCircle, loopCircle)}
    (htrace : diskTrace u = γ.comp σ) {ψ : ℝ → ℝ} (hψ : Continuous ψ)
    (hlift : ∀ t : ℝ, (ψ t : loopCircle) = σ (t : loopCircle)) : ContDiff ℝ ∞ ψ := by
  apply hγ.contDiff_parameterLift hψ
  apply hu.trace.congr
  intro t
  exact (congrArg γ (hlift t)).trans
    (congrArg (fun f : freeLoop M => f (t : loopCircle)) htrace).symm




theorem DiskWeakJordanTrace.exists_smooth_signed_lift {γ : freeLoop M}
    {u : C(closedDisk, M)} (h : DiskWeakJordanTrace γ u)
    (hγ : IsSmoothEmbeddedLoop (E := E) γ) (hu : DiskSmoothUpToBoundary (E := E) u) :
    ∃ (σ : C(loopCircle, loopCircle)) (ψ : ℝ → ℝ), ContDiff ℝ ∞ ψ ∧
      (∀ t : ℝ, (ψ t : loopCircle) = σ (t : loopCircle)) ∧ diskTrace u = γ.comp σ ∧
      ((Monotone ψ ∧ ∀ t, ψ (t + 1) = ψ t + 1) ∨
        (Antitone ψ ∧ ∀ t, ψ (t + 1) = ψ t - 1)) := by
  obtain ⟨σ, ⟨ψ, hc, hlift, hsign⟩, htrace⟩ := h
  exact ⟨σ, ψ, hγ.contDiff_weakTraceLift hu htrace hc hlift, hlift, htrace, hsign⟩

end DifferentialGeometry.Geometry
