import DifferentialGeometry.Geometry.MinimalSurface.Plateau.Regularity.FixedTraceBoundaryRank
import DifferentialGeometry.Topology.LoopSpace.AffineLift
import Mathlib.Order.Hom.Set
import Mathlib.Topology.Order.MonotoneContinuity

set_option autoImplicit false

noncomputable section

open Set Metric
open DifferentialGeometry.Topology
open scoped Manifold ContDiff

namespace DifferentialGeometry.Geometry

private theorem injective_circleMap_of_strictMono_lift
    {σ : C(loopCircle, loopCircle)} {a : ℝ → ℝ}
    (ha : Continuous a) (hmono : StrictMono a)
    (hperiod : ∀ t, a (t + 1) = a t + 1)
    (hlift : ∀ t : ℝ, (a t : loopCircle) = σ (t : loopCircle)) :
    Function.Injective σ := by
  let f : CircleDeg1Lift :=
    { toFun := a
      monotone' := hmono.monotone
      map_add_one' := hperiod }
  have hsur : Function.Surjective a :=
    (CircleDeg1Lift.continuous_iff_surjective f).mp ha
  let F : ℝ ≃ₜ ℝ := (hmono.orderIsoOfSurjective a hsur).toHomeomorph
  let H : loopCircle ≃ₜ loopCircle := affineCircleHomeomorph F hperiod
  have hH (θ : loopCircle) : H θ = σ θ := by
    obtain ⟨t, rfl⟩ := QuotientAddGroup.mk_surjective θ
    change (a t : loopCircle) = σ (t : loopCircle)
    exact hlift t
  intro θ η h
  apply H.injective
  rw [hH, hH, h]

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]

/-- Boundary rank makes the original weakly monotone boundary phase injective.
No global injectivity of the disk is assumed. -/
theorem SmoothDiskExtension.injective_boundary_phase
    {γ : freeLoop M} {q : C(closedDisk, M)} {Q : ℂ → M}
    (hQ : SmoothDiskExtension (E := E) q Q)
    (hγ : IsSmoothEmbeddedLoop (E := E) γ)
    {σ : C(loopCircle, loopCircle)} (hσ : IsWeaklyMonotoneOnce σ)
    (htrace : diskTrace q = γ.comp σ)
    (hrank : ∀ z ∈ sphere (0 : ℂ) 1,
      Function.Injective (mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, E) Q z)) :
    Function.Injective σ := by
  obtain ⟨a, ha, hlift, hsign⟩ :=
    hQ.exists_regular_signed_trace_lift hγ hσ htrace hrank
  rcases hsign with ⟨_, hperiod, hder⟩ | ⟨_, hperiod, hder⟩
  · exact injective_circleMap_of_strictMono_lift ha.continuous
      (strictMono_of_deriv_pos hder) hperiod hlift
  · let τ : C(loopCircle, loopCircle) := ⟨fun θ => -σ θ, σ.continuous.neg⟩
    have hperiod' (t : ℝ) : -a (t + 1) = -a t + 1 := by
      rw [hperiod]
      ring
    have hlift' (t : ℝ) : ((-a t : ℝ) : loopCircle) = τ (t : loopCircle) := by
      change ((-a t : ℝ) : loopCircle) = -σ (t : loopCircle)
      rw [QuotientAddGroup.mk_neg, hlift]
    have hτ : Function.Injective τ := injective_circleMap_of_strictMono_lift
      ha.continuous.neg (strictAnti_of_deriv_neg hder).neg hperiod' hlift'
    intro θ η h
    apply hτ
    change -σ θ = -σ η
    exact congrArg Neg.neg h

/-- Every boundary value has a singleton fiber when boundary rank holds and
the interior misses the prescribed boundary curve. The disk and its phase
are the supplied ones, with either orientation. -/
theorem SmoothDiskExtension.boundary_fiber_eq
    {γ : freeLoop M} {q : C(closedDisk, M)} {Q : ℂ → M}
    (hQ : SmoothDiskExtension (E := E) q Q)
    (hγ : IsSmoothEmbeddedLoop (E := E) γ)
    {σ : C(loopCircle, loopCircle)} (hσ : IsWeaklyMonotoneOnce σ)
    (htrace : diskTrace q = γ.comp σ)
    (hrank : ∀ z ∈ sphere (0 : ℂ) 1,
      Function.Injective (mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, E) Q z))
    (hseparate : ∀ z : closedDisk, ‖(z : ℂ)‖ < 1 →
      ∀ θ : loopCircle, q z ≠ γ θ) :
    ∀ (θ : loopCircle) (z : closedDisk),
      q z = q (diskBoundary θ) → z = diskBoundary θ := by
  have hσinj := hQ.injective_boundary_phase hγ hσ htrace hrank
  have hboundary (θ : loopCircle) : q (diskBoundary θ) = γ (σ θ) :=
    congrArg (fun η : freeLoop M => η θ) htrace
  intro θ₀ z hz
  have hnorm : ‖(z : ℂ)‖ = 1 := by
    have hle : ‖(z : ℂ)‖ ≤ 1 := by
      simpa only [Metric.mem_closedBall, dist_zero_right] using z.property
    apply le_antisymm hle
    exact le_of_not_gt (fun hlt =>
      hseparate z hlt (σ θ₀) (hz.trans (hboundary θ₀)))
  let c : Circle := ⟨(z : ℂ), mem_sphere_zero_iff_norm.mpr hnorm⟩
  obtain ⟨θ, hθ⟩ := (AddCircle.homeomorphCircle (T := (1 : ℝ)) one_ne_zero).surjective c
  have hb : diskBoundary θ = z := by
    apply Subtype.ext
    have hc := congrArg (fun w : Circle => (w : ℂ)) hθ
    simpa only [AddCircle.homeomorphCircle_apply] using! hc
  have hθ₀ : θ = θ₀ := hσinj (hγ.embedding.injective ((hboundary θ).symm.trans
    ((congrArg q hb).trans (hz.trans (hboundary θ₀)))))
  exact hb.symm.trans (congrArg diskBoundary hθ₀)

end DifferentialGeometry.Geometry
