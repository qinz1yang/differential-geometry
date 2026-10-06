/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Geometry.MinimalSurface.Plateau.Regularity.NoCollapsedBoundaryArc
import DifferentialGeometry.Geometry.MinimalSurface.Plateau.SmoothTraceLift

set_option autoImplicit false
noncomputable section

open Set Manifold
open DifferentialGeometry.Topology
open scoped Topology ContDiff Manifold

namespace DifferentialGeometry.Geometry

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M]
  [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M]

/-- The actual smooth signed trace lift of the same Morrey disk is strict:
equal lift values would collapse the boundary interval between them. The
original lift, circle map, trace identity and orientation are retained. -/
theorem IsMorreyDisk.exists_smooth_strict_signed_lift
    {g : SmoothRiemannianMetric 𝓘(ℝ, E) M} {γ : freeLoop M}
    {a : C(closedDisk, M)} (ha : IsMorreyDisk g γ a)
    (hγ : IsSmoothEmbeddedLoop (E := E) γ) {A : ℂ → M}
    (hA : SmoothDiskExtension (E := E) a A) :
    ∃ (σ : C(loopCircle, loopCircle)) (ψ : ℝ → ℝ), ContDiff ℝ ∞ ψ ∧
      (∀ t : ℝ, (ψ t : loopCircle) = σ (t : loopCircle)) ∧
      diskTrace a = γ.comp σ ∧
      ((StrictMono ψ ∧ ∀ t, ψ (t + 1) = ψ t + 1) ∨
        (StrictAnti ψ ∧ ∀ t, ψ (t + 1) = ψ t - 1)) := by
  obtain ⟨σ, ψ, hψ, hlift, htrace, hsign⟩ :=
    ha.trace.exists_smooth_signed_lift hγ hA.smoothUpToBoundary
  have htraceAt (u : ℝ) :
      diskTrace a (u : loopCircle) = γ (ψ u : loopCircle) := by
    have h := congrArg (fun f : freeLoop M => f (u : loopCircle)) htrace
    change diskTrace a (u : loopCircle) = γ (σ (u : loopCircle)) at h
    exact h.trans (congrArg γ (hlift u).symm)
  refine ⟨σ, ψ, hψ, hlift, htrace, ?_⟩
  rcases hsign with ⟨hm, hp⟩ | ⟨hm, hp⟩
  · refine Or.inl ⟨?_, hp⟩
    intro s t hst
    by_contra hnot
    have heq : ψ s = ψ t := le_antisymm (hm hst.le) (le_of_not_gt hnot)
    apply ha.not_constant_boundary_interval hγ hA hst (γ (ψ s : loopCircle))
    intro u hu
    have hueq : ψ u = ψ s := le_antisymm
      (by rw [heq]; exact hm hu.2.le) (hm hu.1.le)
    rw [htraceAt u, hueq]
  · refine Or.inr ⟨?_, hp⟩
    intro s t hst
    by_contra hnot
    have heq : ψ s = ψ t := le_antisymm (le_of_not_gt hnot) (hm hst.le)
    apply ha.not_constant_boundary_interval hγ hA hst (γ (ψ s : loopCircle))
    intro u hu
    have hueq : ψ u = ψ s := le_antisymm
      (hm hu.1.le) (by rw [heq]; exact hm hu.2.le)
    rw [htraceAt u, hueq]

end DifferentialGeometry.Geometry
