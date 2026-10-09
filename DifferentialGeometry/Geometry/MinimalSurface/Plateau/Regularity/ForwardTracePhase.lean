/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Geometry.MinimalSurface.Plateau.MorreyDiskExtension
import Mathlib.Dynamics.Circle.RotationNumber.TranslationNumber
import Mathlib.Order.Hom.Set
import Mathlib.Topology.Order.MonotoneContinuity
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

noncomputable section

open Set Manifold
open DifferentialGeometry.Topology
open scoped Topology ContDiff Manifold NNReal ENNReal

namespace DifferentialGeometry.Geometry

private theorem exists_homeomorph_eq_of_continuous_strictMono_period
    {f : ℝ → ℝ} (hc : Continuous f) (hm : StrictMono f)
    (hp : ∀ t : ℝ, f (t + 1) = f t + 1) :
    ∃ F : ℝ ≃ₜ ℝ, ∀ t : ℝ, F t = f t := by
  let fLift : CircleDeg1Lift := ⟨⟨f, hm.monotone⟩, hp⟩
  have hsurj : Function.Surjective f := fLift.continuous_iff_surjective.mp hc
  exact ⟨(StrictMono.orderIsoOfSurjective f hm hsurj).toHomeomorph, fun _ => rfl⟩

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {M : Type*} [TopologicalSpace M]
  [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]

/-- Keep the chosen signed lift and obtain a forward phase by reflecting the
original filling exactly in the negative branch. Area, range and the forward
metric Lipschitz constant are preserved; no inverse Lipschitz estimate or
positive derivative is required. -/
theorem exists_forward_phase_of_smooth_strict_signed_trace
    (G : SmoothRiemannianMetric 𝓘(ℝ, E) M)
    {γ : freeLoop M} (aOrig : C(closedDisk, M))
    (σ : C(loopCircle, loopCircle)) (ψ : ℝ → ℝ)
    (hψ : ContDiff ℝ ∞ ψ)
    (hlift : ∀ t : ℝ, (ψ t : loopCircle) = σ (t : loopCircle))
    (htrace : diskTrace aOrig = γ.comp σ)
    (hsign : (StrictMono ψ ∧ ∀ t, ψ (t + 1) = ψ t + 1) ∨
      (StrictAnti ψ ∧ ∀ t, ψ (t + 1) = ψ t - 1))
    {A : ℂ → M} (hA : SmoothDiskExtension (E := E) aOrig A)
    {La : ℝ≥0}
    (haLip : ∀ z w : closedDisk, riemannianEDistOf G (aOrig z) (aOrig w) ≤
      (La : ℝ≥0∞) * edist z w) :
    ∃ (aForward : C(closedDisk, M)) (φ : ℝ ≃ₜ ℝ),
      ((aForward = aOrig ∧ ∀ t : ℝ, φ t = ψ t) ∨
        (aForward = aOrig.comp ⟨diskReflection, diskReflection.continuous⟩ ∧
          ∀ t : ℝ, φ t = ψ (-t))) ∧
      ContDiff ℝ ∞ (fun t : ℝ => φ t) ∧ StrictMono φ ∧
      (∀ t : ℝ, φ (t + 1) = φ t + 1) ∧
      (∀ t : ℝ, diskTrace aForward (t : loopCircle) = γ (φ t : loopCircle)) ∧
      riemannianDiskArea G aForward = riemannianDiskArea G aOrig ∧
      Set.range aForward = Set.range aOrig ∧
      (∀ z w : closedDisk, riemannianEDistOf G (aForward z) (aForward w) ≤
        (La : ℝ≥0∞) * edist z w) := by
  have htraceAt (t : ℝ) :
      diskTrace aOrig (t : loopCircle) = γ (ψ t : loopCircle) := by
    have h := congrArg (fun f : freeLoop M => f (t : loopCircle)) htrace
    change diskTrace aOrig (t : loopCircle) = γ (σ (t : loopCircle)) at h
    exact h.trans (congrArg γ (hlift t).symm)
  rcases hsign with ⟨hm, hp⟩ | ⟨hm, hp⟩
  · obtain ⟨φ, hφeq⟩ :=
      exists_homeomorph_eq_of_continuous_strictMono_period hψ.continuous hm hp
    have hφfun : (φ : ℝ → ℝ) = ψ := funext hφeq
    refine ⟨aOrig, φ, Or.inl ⟨rfl, hφeq⟩, ?_, ?_, ?_, ?_, rfl, rfl, haLip⟩
    · exact hφfun.symm ▸ hψ
    · exact hφfun.symm ▸ hm
    · intro t
      simpa only [hφeq] using hp t
    · intro t
      simpa only [hφeq] using htraceAt t
  · let f : ℝ → ℝ := fun t => ψ (-t)
    have hf : ContDiff ℝ ∞ f := hψ.comp contDiff_neg
    have hfm : StrictMono f := fun _ _ hst => hm (neg_lt_neg hst)
    have hfp : ∀ t : ℝ, f (t + 1) = f t + 1 := by
      intro t
      change ψ (-(t + 1)) = ψ (-t) + 1
      have h := hp (-t - 1)
      rw [sub_add_cancel] at h
      rw [show -(t + 1) = -t - 1 by ring]
      linarith only [h]
    obtain ⟨φ, hφeq⟩ :=
      exists_homeomorph_eq_of_continuous_strictMono_period hf.continuous hfm hfp
    have hφfun : (φ : ℝ → ℝ) = f := funext hφeq
    let aForward := aOrig.comp ⟨diskReflection, diskReflection.continuous⟩
    refine ⟨aForward, φ, Or.inr ⟨rfl, hφeq⟩, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · exact hφfun.symm ▸ hf
    · exact hφfun.symm ▸ hfm
    · intro t
      simpa only [hφeq] using hfp t
    · intro t
      rw [hφeq]
      change aOrig (diskReflection (diskBoundary (t : loopCircle))) =
        γ (ψ (-t) : loopCircle)
      rw [diskReflection_diskBoundary]
      simpa only [diskTrace, ContinuousMap.comp_apply, AddCircle.coe_neg] using htraceAt (-t)
    · exact riemannianDiskArea_diskReflection_of_extension G hA
    · apply Set.Subset.antisymm
      · rintro y ⟨z, rfl⟩
        exact ⟨diskReflection z, rfl⟩
      · rintro y ⟨z, rfl⟩
        obtain ⟨w, hw⟩ := diskReflection.surjective z
        refine ⟨w, ?_⟩
        change aOrig (diskReflection w) = aOrig z
        exact congrArg aOrig hw
    · intro z w
      have hrefDist : edist (diskReflection z) (diskReflection w) = edist z w := by
        change edist (starRingEnd ℂ (z : ℂ)) (starRingEnd ℂ (w : ℂ)) =
          edist (z : ℂ) (w : ℂ)
        exact Complex.isometry_conj.edist_eq _ _
      change riemannianEDistOf G (aOrig (diskReflection z)) (aOrig (diskReflection w)) ≤
        (La : ℝ≥0∞) * edist z w
      simpa only [hrefDist] using haLip (diskReflection z) (diskReflection w)

end DifferentialGeometry.Geometry
