/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Geometry.MinimalSurface.Plateau.EqualAreaFoldArc
import DifferentialGeometry.Geometry.MinimalSurface.Plateau.ForwardPhaseSeamChart
import DifferentialGeometry.Geometry.MinimalSurface.Plateau.MorreyDiskExtension

noncomputable section

open Set Function Manifold DifferentialGeometry
open DifferentialGeometry.Topology DifferentialGeometry.Geometry DifferentialGeometry.Analysis
open DifferentialGeometry.Geometry.ImmersedDiskDivergence.Within
open DifferentialGeometry.Geometry.ImmersedDiskDivergence.HalfDisk
open scoped Topology ContDiff Manifold NNReal ENNReal ComplexConjugate

namespace DifferentialGeometry.Geometry.IMS03ConsumerAudit

/-- Extend the retained orientation, equal-area splice and seam tuple by
conormal cancellation. The branch and seam hypotheses are literal projections
of the preceding actual consumers; no new phase, filling or source chart is
chosen. The original alternate disk supplies the harmonic map `A`, even in the
reflected branch, where reflection remains in its source reparametrization. -/
theorem actual_morrey_forward_phase_conormal_cancellation
    {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [TopologicalSpace M] [ChartedSpace E M]
    [IsManifold 𝓘(ℝ, E) ∞ M] [T3Space M]
    (G : SmoothRiemannianMetric 𝓘(ℝ, E) M)
    {γ : freeLoop M} {q : C(closedDisk, M)} (hq : IsMorreyDisk G γ q)
    (aOrig : C(closedDisk, M)) {r b : ℝ}
    (haOrig : IsMorreyDisk G (diskTrace (affineSubdisk q 0 r)) aOrig)
    (QOriginal A : ℂ → M)
    (hQOriginal : SmoothDiskExtension (E := E) q QOriginal)
    (hA : SmoothDiskExtension (E := E) aOrig A)
    (ψ : ℝ → ℝ) (aForward : C(closedDisk, M)) (φ : ℝ ≃ₜ ℝ)
    (hφ : ContDiff ℝ ∞ (fun t : ℝ => φ t))
    (hp : ∀ t : ℝ, φ (t + 1) = φ t + 1)
    (D : ℂ → ℂ)
    (hbranch : (D = id ∧ aForward = aOrig ∧ ∀ t : ℝ, φ t = ψ t) ∨
      (D = conj ∧ aForward = aOrig.comp ⟨diskReflection, diskReflection.continuous⟩ ∧
        ∀ t : ℝ, φ t = ψ (-t)))
    (F : C(closedDisk, M)) {L : ℝ≥0}
    (hFLip : ∀ z w, riemannianEDistOf G (F z) (F w) ≤ (L : ℝ≥0∞) * edist z w)
    (hFtrace : diskTrace F = diskTrace q)
    (hFarea : riemannianDiskArea G F = riemannianDiskArea G q)
    (t₀ α : ℝ) (χ : PartialDiffeomorph 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) ℂ ℂ ∞)
    (hseam :
      t₀ ∈ Ioo (0 : ℝ) 1 ∧ 0 < deriv φ t₀ ∧ 0 < α ∧
      (∀ z : ℂ, χ z = r • Complex.diskBoundaryChart
        (diskBoundary (t₀ : loopCircle) : ℂ) (by simp [diskBoundary]) (α • z)) ∧
      Metric.closedBall (0 : ℂ) 1 ⊆ χ.source ∧
      (∀ z ∈ Metric.closedBall (0 : ℂ) 1, r / 2 < ‖χ z‖ ∧ ‖χ z‖ < b) ∧
      χ '' Metric.closedBall (0 : ℂ) 1 ⊆ Metric.ball (0 : ℂ) 1 ∧
      let H := ForwardPhaseAnnulus.map r b hφ hp
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
      (∀ s ∈ Icc (-(1 / 4) : ℝ) (1 / 4), UAlt (s : ℂ) = UOuter (s : ℂ))) :
    let H := ForwardPhaseAnnulus.map r b hφ hp
    let ψAlt : ℂ → ℂ := fun z => (r⁻¹ : ℝ) • χ z
    let UAlt : ℂ → M := A ∘ (D ∘ ψAlt)
    let UOuter : ℂ → M := QOriginal ∘ (H ∘ χ ∘ conj)
    ∀ x : ℝ, |x| < 1 / 16 → UAlt (x : ℂ) = UOuter (x : ℂ) ∧
      inwardConormalWithin G UAlt (closedHalfDisk 0 (1 / 4)) (x : ℂ) +
        tangentSpaceCast 𝓘(ℝ, E) (UOuter (x : ℂ)) (UAlt (x : ℂ))
          (inwardConormalWithin G UOuter (closedHalfDisk 0 (1 / 4)) (x : ℂ)) = 0 := by
  dsimp only at hseam ⊢
  rcases hseam with ⟨_, _, _, _, hχsrc, _, hχinside,
    _, _, _, hψAlt, hψOuter, hbijAlt, hbijOuter, _, hmapsAlt, hmapsOuter, _,
    hUAlt, hUOuter, hiAlt, hiOuter, heqAlt, heqOuter, _⟩
  let ψAlt : ℂ → ℂ := fun z => (r⁻¹ : ℝ) • χ z
  let ψOuter : ℂ → ℂ := ForwardPhaseAnnulus.map r b hφ hp ∘ χ ∘ conj
  have hopenClosed : (openHalfDisk 0 (1 / 4) : Set ℂ) ⊆ closedHalfDisk 0 (1 / 4) :=
    fun z hz => ⟨(show 0 < z.im from hz.1).le, Metric.ball_subset_closedBall hz.2⟩
  have hopenUnit : (openHalfDisk 0 (1 / 4) : Set ℂ) ⊆ Metric.ball (0 : ℂ) 1 := by
    intro z hz
    exact Metric.mem_ball.mpr ((Metric.mem_ball.mp hz.2).trans (by norm_num))
  have hsection :
      ContDiffOn ℝ ∞ (D ∘ ψAlt) (openHalfDisk 0 (1 / 4)) ∧
      MapsTo (D ∘ ψAlt) (openHalfDisk 0 (1 / 4)) (Metric.ball (0 : ℂ) 1) ∧
      ∀ z ∈ (openHalfDisk 0 (1 / 4) : Set ℂ), Bijective (fderiv ℝ (D ∘ ψAlt) z) := by
    rcases hbranch with ⟨rfl, _, _⟩ | ⟨rfl, _, _⟩
    · simpa only [Function.id_comp] using
        (show ContDiffOn ℝ ∞ ψAlt (openHalfDisk 0 (1 / 4)) ∧
          MapsTo ψAlt (openHalfDisk 0 (1 / 4)) (Metric.ball (0 : ℂ) 1) ∧
          ∀ z ∈ (openHalfDisk 0 (1 / 4) : Set ℂ), Bijective (fderiv ℝ ψAlt z) from
          ⟨hψAlt.mono hopenUnit, hmapsAlt, hbijAlt⟩)
    · refine ⟨Complex.conjCLE.contDiff.comp_contDiffOn (hψAlt.mono hopenUnit), ?_, ?_⟩
      · intro z hz
        simpa only [Function.comp_apply, Metric.mem_ball, dist_zero_right, Complex.norm_conj]
          using hmapsAlt hz
      · intro z hz
        have hdAlt : DifferentiableAt ℝ ψAlt z :=
          (hψAlt.contDiffAt (Metric.isOpen_ball.mem_nhds (hopenUnit hz))).differentiableAt
            (by simp)
        have hd : fderiv ℝ (conj ∘ ψAlt) z =
            (Complex.conjCLE : ℂ →L[ℝ] ℂ).comp (fderiv ℝ ψAlt z) :=
          (Complex.conjCLE.hasFDerivAt.comp z hdAlt.hasFDerivAt).fderiv
        rw [hd]
        exact Complex.conjCLE.bijective.comp (hbijAlt z hz)
  have hbijSection : ∀ z ∈ (openHalfDisk 0 (1 / 4) : Set ℂ), Bijective
      (mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) (D ∘ ψAlt) z) := by
    intro z hz
    rw [mfderiv_eq_fderiv]
    exact (NormedSpace.fromTangentSpace (𝕜 := ℝ) ((D ∘ ψAlt) z)).symm.bijective.comp
      ((hsection.2.2 z hz).comp (NormedSpace.fromTangentSpace (𝕜 := ℝ) z).bijective)
  have hbijOuterM : ∀ z ∈ (openHalfDisk 0 (1 / 4) : Set ℂ), Bijective
      (mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) ψOuter z) := by
    intro z hz
    rw [mfderiv_eq_fderiv]
    exact (NormedSpace.fromTangentSpace (𝕜 := ℝ) (ψOuter z)).symm.bijective.comp
      ((hbijOuter z hz).comp (NormedSpace.fromTangentSpace (𝕜 := ℝ) z).bijective)
  have hAsmooth : ContMDiffOn 𝓘(ℝ, ℂ) 𝓘(ℝ, E) ∞ A (Metric.ball (0 : ℂ) 1) := by
    obtain ⟨N, _, hN, hAN⟩ := hA.2
    exact hAN.mono (Metric.ball_subset_closedBall.trans hN)
  have hQsmooth : ContMDiffOn 𝓘(ℝ, ℂ) 𝓘(ℝ, E) ∞ QOriginal (Metric.ball (0 : ℂ) 1) := by
    obtain ⟨N, _, hN, hQN⟩ := hQOriginal.2
    exact hQN.mono (Metric.ball_subset_closedBall.trans hN)
  exact hq.equal_area_two_sheet_conormal_sum_eq_zero_on_arc F hFLip hFtrace hFarea
    χ hχsrc hχinside A QOriginal (D ∘ ψAlt) ψOuter
    hAsmooth (haOrig.conformal_of_extension hA) (haOrig.tension_eq_zero_of_extension hA)
    hQsmooth (hq.conformal_of_extension hQOriginal) (hq.tension_eq_zero_of_extension hQOriginal)
    hsection.1.contMDiffOn (hψOuter.mono hopenUnit).contMDiffOn
    hsection.2.1 (fun _ hz => hmapsOuter (hopenClosed hz)) hbijSection hbijOuterM
    hUAlt hUOuter hiAlt hiOuter heqAlt heqOuter

end DifferentialGeometry.Geometry.IMS03ConsumerAudit
