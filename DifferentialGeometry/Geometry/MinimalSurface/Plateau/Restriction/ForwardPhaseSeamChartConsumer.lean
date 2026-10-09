/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Geometry.MinimalSurface.Plateau.ForwardPhaseSeamChart
import DifferentialGeometry.Geometry.MinimalSurface.Plateau.MorreyDiskExtension

set_option autoImplicit false
noncomputable section

open Set Function Manifold DifferentialGeometry
open DifferentialGeometry.Topology DifferentialGeometry.Geometry DifferentialGeometry.Analysis
open DifferentialGeometry.Geometry.ImmersedDiskDivergence.Within
open DifferentialGeometry.Geometry.ImmersedDiskDivergence.HalfDisk
open scoped Topology ContDiff Manifold ComplexConjugate

namespace DifferentialGeometry.Geometry.IMS03ConsumerAudit

/-- Consume the once-chosen branch, phase and splice from
`IMS03Embeddedness.ConsumerAudit.actual_morrey_oriented_forward_phase_splice`.
The original Morrey records discharge all conformality and smooth-extension
requirements. In the reflected branch the original alternate map is still `A`,
with the explicit section `conj ∘ ψAlt`; no reflected Morrey record is needed. -/
theorem actual_morrey_regular_forward_phase_seam_chart
    {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [TopologicalSpace M] [ChartedSpace E M]
    [IsManifold 𝓘(ℝ, E) ∞ M]
    (G : SmoothRiemannianMetric 𝓘(ℝ, E) M)
    {γ : freeLoop M} {q : C(closedDisk, M)} (hq : IsMorreyDisk G γ q)
    (aOrig : C(closedDisk, M)) {r b : ℝ} (hr : 0 < r) (hrb : r < b) (hb : b < 1)
    (haOrig : IsMorreyDisk G (diskTrace (affineSubdisk q 0 r)) aOrig)
    (hΓ : IsSmoothEmbeddedLoop (E := E) (diskTrace (affineSubdisk q 0 r)))
    (QOriginal A : ℂ → M)
    (hQOriginal : SmoothDiskExtension (E := E) q QOriginal)
    (hA : SmoothDiskExtension (E := E) aOrig A)
    (ψ : ℝ → ℝ) (aForward : C(closedDisk, M)) (φ : ℝ ≃ₜ ℝ)
    (hφ : ContDiff ℝ ∞ (fun t : ℝ => φ t))
    (hp : ∀ t : ℝ, φ (t + 1) = φ t + 1)
    (hbranch : (aForward = aOrig ∧ ∀ t : ℝ, φ t = ψ t) ∨
      (aForward = aOrig.comp ⟨diskReflection, diskReflection.continuous⟩ ∧
        ∀ t : ℝ, φ t = ψ (-t)))
    (htrace : ∀ t : ℝ, diskTrace aForward (t : loopCircle) =
      diskTrace (affineSubdisk q 0 r) (φ t : loopCircle))
    (F : C(closedDisk, M))
    (hFinner : ∀ z : ℂ, ‖z‖ ≤ r →
      diskExtension F z = diskExtension aForward ((r⁻¹ : ℝ) • z))
    (hFmiddle : ∀ z : ℂ, r ≤ ‖z‖ → ‖z‖ ≤ b →
      diskExtension F z = diskExtension q (ForwardPhaseAnnulus.map r b hφ hp z)) :
    ∃ D : ℂ → ℂ,
      ((D = id ∧ aForward = aOrig ∧ ∀ t : ℝ, φ t = ψ t) ∨
        (D = conj ∧ aForward = aOrig.comp ⟨diskReflection, diskReflection.continuous⟩ ∧
          ∀ t : ℝ, φ t = ψ (-t))) ∧
      SmoothDiskExtension (E := E) aForward (A ∘ D) ∧
      (∀ z ∈ Metric.closedBall (0 : ℂ) 1, DiskMapConformalAt G (A ∘ D) z) ∧
      let H := ForwardPhaseAnnulus.map r b hφ hp
      ∃ (t₀ α : ℝ) (χ : PartialDiffeomorph 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) ℂ ℂ ∞),
        t₀ ∈ Ioo (0 : ℝ) 1 ∧ 0 < deriv φ t₀ ∧ 0 < α ∧
        (∀ z : ℂ, χ z = r • Complex.diskBoundaryChart
          (diskBoundary (t₀ : loopCircle) : ℂ) (by simp [diskBoundary]) (α • z)) ∧
        Metric.closedBall (0 : ℂ) 1 ⊆ χ.source ∧
        (∀ z ∈ Metric.closedBall (0 : ℂ) 1, r / 2 < ‖χ z‖ ∧ ‖χ z‖ < b) ∧
        χ '' Metric.closedBall (0 : ℂ) 1 ⊆ Metric.ball (0 : ℂ) 1 ∧
        let ψAlt : ℂ → ℂ := fun z => (r⁻¹ : ℝ) • χ z
        let ψOuter : ℂ → ℂ := H ∘ χ ∘ conj
        let UAlt : ℂ → M := A ∘ (D ∘ ψAlt)
        let UOuter : ℂ → M := QOriginal ∘ ψOuter
        χ 0 = r • (diskBoundary (t₀ : loopCircle) : ℂ) ∧
        ψAlt 0 = (diskBoundary (t₀ : loopCircle) : ℂ) ∧
        ψOuter 0 = r • (diskBoundary (φ t₀ : loopCircle) : ℂ) ∧
        ContDiffOn ℝ ∞ ψAlt (Metric.ball (0 : ℂ) 1) ∧
        ContDiffOn ℝ ∞ ψOuter (Metric.ball (0 : ℂ) 1) ∧
        (∀ z ∈ (openHalfDisk 0 (1 / 4) : Set ℂ), Bijective (fderiv ℝ ψAlt z)) ∧
        (∀ z ∈ (openHalfDisk 0 (1 / 4) : Set ℂ), Bijective (fderiv ℝ ψOuter z)) ∧
        MapsTo ψAlt (closedHalfDisk 0 (1 / 4)) (Metric.closedBall (0 : ℂ) 1) ∧
        MapsTo ψAlt (openHalfDisk 0 (1 / 4)) (Metric.ball (0 : ℂ) 1) ∧
        MapsTo ψOuter (closedHalfDisk 0 (1 / 4)) (Metric.ball (0 : ℂ) 1) ∧
        (∀ z ∈ (openHalfDisk 0 (1 / 4) : Set ℂ), r < ‖ψOuter z‖ ∧ ‖ψOuter z‖ < b) ∧
        ContMDiffOn 𝓘(ℝ, ℂ) 𝓘(ℝ, E) ∞ UAlt (Metric.ball (0 : ℂ) 1) ∧
        ContMDiffOn 𝓘(ℝ, ℂ) 𝓘(ℝ, E) ∞ UOuter (Metric.ball (0 : ℂ) 1) ∧
        (∀ z ∈ closedHalfDisk 0 (1 / 4), Injective
          (mfderivWithin 𝓘(ℝ, ℂ) 𝓘(ℝ, E) UAlt (closedHalfDisk 0 (1 / 4)) z)) ∧
        (∀ z ∈ closedHalfDisk 0 (1 / 4), Injective
          (mfderivWithin 𝓘(ℝ, ℂ) 𝓘(ℝ, E) UOuter (closedHalfDisk 0 (1 / 4)) z)) ∧
        EqOn (diskExtension F ∘ χ) UAlt (closedHalfDisk 0 (1 / 4)) ∧
        EqOn (diskExtension F ∘ χ ∘ conj) UOuter (closedHalfDisk 0 (1 / 4)) ∧
        (∀ s ∈ Icc (-(1 / 4) : ℝ) (1 / 4), UAlt (s : ℂ) = UOuter (s : ℂ)) := by
  have horiented : ∃ D : ℂ → ℂ,
      ((D = id ∧ aForward = aOrig ∧ ∀ t : ℝ, φ t = ψ t) ∨
        (D = conj ∧ aForward = aOrig.comp ⟨diskReflection, diskReflection.continuous⟩ ∧
          ∀ t : ℝ, φ t = ψ (-t))) ∧
      SmoothDiskExtension (E := E) aForward (A ∘ D) ∧
      (∀ z ∈ Metric.closedBall (0 : ℂ) 1, DiskMapConformalAt G (A ∘ D) z) := by
    rcases hbranch with ⟨ha, hphase⟩ | ⟨ha, hphase⟩
    · refine ⟨id, Or.inl ⟨rfl, ha, hphase⟩, ?_, ?_⟩
      · simpa only [Function.comp_id, ha] using hA
      · simpa only [Function.comp_id] using haOrig.conformal_of_extension_closedBall hA
    · refine ⟨conj, Or.inr ⟨rfl, ha, hphase⟩, ?_,
        haOrig.conformal_comp_diskReflection hA⟩
      simpa only [ha] using hA.comp_diskReflection
  obtain ⟨D, hD, hForward, hconfForward⟩ := horiented
  refine ⟨D, hD, hForward, hconfForward, ?_⟩
  exact exists_regular_forward_phase_seam_chart G q aForward F QOriginal (A ∘ D)
      hQOriginal hForward (hq.conformal_of_extension hQOriginal) hconfForward
      hr hrb hb hΓ φ hφ hp htrace hFinner hFmiddle

end DifferentialGeometry.Geometry.IMS03ConsumerAudit
