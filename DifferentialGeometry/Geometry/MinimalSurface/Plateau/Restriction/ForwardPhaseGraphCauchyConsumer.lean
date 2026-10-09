/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Geometry.MinimalSurface.Boundary.ConormalGraphCauchy
import DifferentialGeometry.Geometry.MinimalSurface.Plateau.Restriction.ForwardPhaseConormalCancellationConsumer
import DifferentialGeometry.Geometry.HarmonicMap.RegularLeadingPlane
import DifferentialGeometry.Analysis.Calculus.Inverse.CoordinateDerivativeEquiv

noncomputable section

open Set Filter Function Manifold DifferentialGeometry
open DifferentialGeometry.Topology DifferentialGeometry.Geometry DifferentialGeometry.Analysis
open DifferentialGeometry.Tensor.Coordinates
open DifferentialGeometry.Geometry.ImmersedDiskDivergence.Within
open DifferentialGeometry.Geometry.ImmersedDiskDivergence.HalfDisk
open scoped Topology ContDiff Manifold NNReal ENNReal ComplexConjugate

namespace DifferentialGeometry.Geometry.IMS03ConsumerAudit

private theorem graph_cauchy_halfdisk_uniqueMDiff :
    UniqueMDiffOn 𝓘(ℝ, ℂ) (closedHalfDisk 0 (1 / 4)) := by
  apply UniqueDiffOn.uniqueMDiffOn
  apply uniqueDiffOn_convex
    ((convex_halfSpace_im_ge 0).inter (convex_closedBall (0 : ℂ) (1 / 4)))
  have hinside : (openHalfDisk 0 (1 / 4) : Set ℂ) ⊆
      interior (closedHalfDisk 0 (1 / 4)) := by
    intro z hz
    apply mem_interior_iff_mem_nhds.mpr
    exact mem_of_superset ((openHalfDisk 0 (1 / 4)).isOpen.mem_nhds hz)
      (fun q hq => ⟨(show 0 < q.im from hq.1).le, Metric.ball_subset_closedBall hq.2⟩)
  refine ⟨(1 / 8 : ℂ) * Complex.I, hinside ?_⟩
  constructor
  · change 0 < ((1 / 8 : ℂ) * Complex.I).im
    norm_num
  · rw [Metric.mem_ball, dist_eq_norm, Complex.ofReal_zero, sub_zero]
    norm_num [norm_mul, norm_div]

/-- Normalize using the original conformal disk, then compose only its source
derivative with the supplied regular planar map. -/
private theorem original_projection_after_regular_source_map
    {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [TopologicalSpace M] [ChartedSpace E M]
    [IsManifold 𝓘(ℝ, E) ∞ M]
    {G : SmoothRiemannianMetric 𝓘(ℝ, E) M} {γ : freeLoop M}
    {q : C(closedDisk, M)} (hq : IsMorreyDisk G γ q)
    {Q : ℂ → M} (hQ : SmoothDiskExtension (E := E) q Q)
    (hd3 : Module.finrank ℝ E = 3) (ψ : ℂ → ℂ)
    (hdψ : DifferentiableAt ℝ ψ 0) (hbijψ : Bijective (fderiv ℝ ψ 0))
    (hinside : ψ 0 ∈ Metric.ball (0 : ℂ) 1)
    (hi : Injective (mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, E) (Q ∘ ψ) 0))
    (p : M) (hp : Q (ψ 0) ∈ (chartAt E p).source) :
    let B : Fin (Module.finrank ℝ E) → ℂ := fun i => chartComplexGradient p Q i (ψ 0)
    let Qg := chartGramBilin G p (Q (ψ 0))
    let P := chartLeadingPlaneProjection G p (Q (ψ 0)) B
    let lift : ℂ → E := fun w => (chartModelBasis E).equivFunL.symm
      (fun i => (2 : ℝ) * (w * B i).re)
    (P.comp (fderiv ℝ (fun z => extChartAt 𝓘(ℝ, E) p (Q (ψ z))) 0)).IsInvertible ∧
    ∃ N : E, Qg N N = 1 ∧ P N = 0 ∧
      ∀ v : E, v = lift (P v) + (Qg N v) • N := by
  intro B Qg P lift
  obtain ⟨V, _, hDV, hQV⟩ := hQ.2
  have hQB : ContMDiffOn 𝓘(ℝ, ℂ) 𝓘(ℝ, E) ∞ Q (Metric.ball (0 : ℂ) 1) :=
    hQV.mono (Metric.ball_subset_closedBall.trans hDV)
  have hdQ := (hQB.contMDiffAt (Metric.isOpen_ball.mem_nhds hinside)).mdifferentiableAt
    (by simp)
  have hdψM : MDifferentiableAt 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) ψ 0 :=
    mdifferentiableAt_iff_differentiableAt.mpr hdψ
  have hbijψM : Bijective (mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) ψ 0) := by
    rw [mfderiv_eq_fderiv]
    exact (NormedSpace.fromTangentSpace (𝕜 := ℝ) (ψ 0)).symm.bijective.comp
      (hbijψ.comp (NormedSpace.fromTangentSpace (𝕜 := ℝ) (0 : ℂ)).bijective)
  have hchain := mfderiv_comp (I := 𝓘(ℝ, ℂ)) (I' := 𝓘(ℝ, ℂ))
    (I'' := 𝓘(ℝ, E)) 0 hdQ hdψM
  have hiQ : Injective (mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, E) Q (ψ 0)) := by
    intro v w hvw
    obtain ⟨v0, hv0⟩ := hbijψM.surjective v
    obtain ⟨w0, hw0⟩ := hbijψM.surjective w
    have he : mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, E) (Q ∘ ψ) 0 v0 =
        mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, E) (Q ∘ ψ) 0 w0 := by
      rw [hchain]
      change mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, E) Q (ψ 0)
          (mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) ψ 0 v0) =
        mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, E) Q (ψ 0)
          (mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) ψ 0 w0)
      rwa [hv0, hw0]
    rw [← hv0, ← hw0, hi he]
  let s : Set ℂ := Metric.ball (0 : ℂ) 1 ∩ Q ⁻¹' (chartAt E p).source
  have hs : IsOpen s :=
    hQB.continuousOn.isOpen_inter_preimage Metric.isOpen_ball (chartAt E p).open_source
  obtain ⟨hnorm, N, hNN, hPN, hsplit⟩ :=
    chartLeadingPlaneProjection_regular_normalization_and_split G hd3 hs
      (hQB.mono inter_subset_left)
      (fun z hz => hq.conformal_of_extension hQ z hz.1) ⟨hinside, hp⟩
      (fun _ hz => hz.2) hiQ
  refine ⟨?_, N, hNN, hPN, hsplit⟩
  let X : ℂ → E := fun z => extChartAt 𝓘(ℝ, E) p (Q z)
  have hdX : DifferentiableAt ℝ X (ψ 0) :=
    (((contMDiffAt_extChartAt' (I := 𝓘(ℝ, E)) (n := ∞) hp).comp (ψ 0)
      (hQB.contMDiffAt (Metric.isOpen_ball.mem_nhds hinside))).contDiffAt).differentiableAt
      (by simp)
  have hDX : fderiv ℝ (fun z => extChartAt 𝓘(ℝ, E) p (Q (ψ z))) 0 =
      (fderiv ℝ X (ψ 0)).comp (fderiv ℝ ψ 0) :=
    (hdX.hasFDerivAt.comp 0 hdψ.hasFDerivAt).fderiv
  rw [hDX, ← ContinuousLinearMap.comp_assoc, hnorm, ContinuousLinearMap.id_comp]
  let L : ℂ ≃L[ℝ] ℂ :=
    (LinearEquiv.ofBijective (fderiv ℝ ψ 0).toLinearMap hbijψ).toContinuousLinearEquiv
  exact ⟨L, by ext v; rfl⟩

/-- The original minimum and the retained equal-area splice supply a cancelled
arc, then one original-metric graph chart and its actual one-sided Cauchy data.
The outer section retains H and lands in the proper original subdisk. -/
theorem actual_morrey_forward_phase_graph_cauchy_data
    {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [TopologicalSpace M] [ChartedSpace E M]
    [IsManifold 𝓘(ℝ, E) ∞ M] [T3Space M]
    (G : SmoothRiemannianMetric 𝓘(ℝ, E) M)
    {γ : freeLoop M} {q : C(closedDisk, M)} (hq : IsMorreyDisk G γ q)
    (aOrig : C(closedDisk, M)) {r b : ℝ}
    (hr : 0 < r) (hrb : r < b) (hb : b < 1)
    (hd3 : Module.finrank ℝ E = 3)
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
    let ψOuter : ℂ → ℂ := H ∘ χ ∘ conj
    let UAlt : ℂ → M := A ∘ (D ∘ ψAlt)
    let UOuter : ℂ → M := QOriginal ∘ ψOuter
    let aOriginal := ψOuter 0
    let p := QOriginal aOriginal
    let B : Fin (Module.finrank ℝ E) → ℂ := fun i =>
      chartComplexGradient p QOriginal i aOriginal
    let Qg := chartGramBilin G p (QOriginal aOriginal)
    let P := chartLeadingPlaneProjection G p (QOriginal aOriginal) B
    let lift : ℂ → E := fun w => (chartModelBasis E).equivFunL.symm
      (fun i => (2 : ℝ) * (w * B i).re)
    ∃ N : E, Qg N N = 1 ∧ P N = 0 ∧
      (∀ v : E, v = lift (P v) + (Qg N v) • N) ∧
      ∃ (eOuter eAlt : OpenPartialHomeomorph ℂ ℂ) (O : Set ℂ),
        (0 : ℂ) ∈ eOuter.source ∧ (0 : ℂ) ∈ eAlt.source ∧
        eOuter.source ⊆ Metric.ball (0 : ℂ) 1 ∧
        eAlt.source ⊆ Metric.ball (0 : ℂ) 1 ∧
        (eOuter : ℂ → ℂ) = (fun z => P (extChartAt 𝓘(ℝ, E) p (UOuter z))) ∧
        (eAlt : ℂ → ℂ) = (fun z => P (extChartAt 𝓘(ℝ, E) p (UAlt z))) ∧
        ContDiffOn ℝ ∞ eOuter.symm eOuter.target ∧
        ContDiffOn ℝ ∞ eAlt.symm eAlt.target ∧
        IsOpen O ∧ eOuter 0 ∈ O ∧ O ⊆ eOuter.target ∩ eAlt.target ∧
        let rOuter := ψOuter ∘ eOuter.symm
        let rAlt := D ∘ ψAlt ∘ eAlt.symm
        let hOuter : ℂ → ℝ := fun y => Qg N
          (extChartAt 𝓘(ℝ, E) p (QOriginal (rOuter y)) - extChartAt 𝓘(ℝ, E) p p)
        let hAlt : ℂ → ℝ := fun y => Qg N
          (extChartAt 𝓘(ℝ, E) p (A (rAlt y)) - extChartAt 𝓘(ℝ, E) p p)
        let S := O ∩ eAlt '' (eAlt.source ∩ {z : ℂ | 0 < z.im})
        ContDiffOn ℝ ∞ hOuter O ∧ ContDiffOn ℝ ∞ hAlt O ∧
        ContDiffOn ℝ ∞ rOuter O ∧ ContDiffOn ℝ ∞ rAlt O ∧
        (∀ y ∈ O, QOriginal (rOuter y) ∈ (chartAt E p).source) ∧
        (∀ y ∈ O, A (rAlt y) ∈ (chartAt E p).source) ∧
        (∀ y ∈ O, P (extChartAt 𝓘(ℝ, E) p (QOriginal (rOuter y))) = y) ∧
        (∀ y ∈ O, P (extChartAt 𝓘(ℝ, E) p (A (rAlt y))) = y) ∧
        (∀ y ∈ O, ∀ t ∈ Icc (0 : ℝ) 1,
          (1 - t) • extChartAt 𝓘(ℝ, E) p (A (rAlt y)) +
            t • extChartAt 𝓘(ℝ, E) p (QOriginal (rOuter y)) ∈
              (extChartAt 𝓘(ℝ, E) p).target) ∧
        IsOpen S ∧ S ⊆ O ∧ S.Nonempty ∧
        eOuter 0 ∈ closure S ∩ closure (interior Sᶜ) ∧
        O ∩ frontier S = {y | y ∈ O ∧ (eAlt.symm y).im = 0} ∧
        (∀ y ∈ O ∩ frontier S, ∃ t : ℝ, |t| < 1 / 16 ∧
          eAlt.symm y = (t : ℂ) ∧ eOuter.symm y = (t : ℂ)) ∧
        (∀ y ∈ O ∩ frontier S, hOuter y = hAlt y ∧
          fderiv ℝ hOuter y = fderiv ℝ hAlt y) ∧
        (∀ y ∈ O ∩ frontier S, ∃ (γ : ℝ → ℂ) (τ : ℂ),
          γ 0 = y ∧ HasDerivAt γ τ 0 ∧ τ ≠ 0 ∧
            ∀ᶠ t in 𝓝 0, γ t ∈ O ∩ frontier S) ∧
        MapsTo rAlt S (Metric.ball (0 : ℂ) 1) ∧
        MapsTo rOuter S (Metric.ball (0 : ℂ) r) ∧
        MapsTo rOuter S (Metric.ball (0 : ℂ) 1) ∧
        MapsTo (fun y => (r⁻¹ : ℝ) • rOuter y) S (Metric.ball (0 : ℂ) 1) := by
  intro H ψAlt ψOuter UAlt UOuter aOriginal p B Qg P lift
  have hcancel := actual_morrey_forward_phase_conormal_cancellation G hq aOrig haOrig
    QOriginal A hQOriginal hA ψ aForward φ hφ hp D hbranch F hFLip hFtrace hFarea
    t₀ α χ hseam
  change ∀ x : ℝ, |x| < 1 / 16 → UAlt (x : ℂ) = UOuter (x : ℂ) ∧
    inwardConormalWithin G UAlt (closedHalfDisk 0 (1 / 4)) (x : ℂ) +
      tangentSpaceCast 𝓘(ℝ, E) (UOuter (x : ℂ)) (UAlt (x : ℂ))
        (inwardConormalWithin G UOuter (closedHalfDisk 0 (1 / 4)) (x : ℂ)) = 0 at hcancel
  dsimp only at hseam
  rcases hseam with ⟨_, htpos, hα, hχformula, hχsrc, _, _, hχ0, _, _,
    hψAlt, hψOuter, _, _, _, hmapsAlt, hmapsOuter, _, hUAlt, hUOuter,
    hiAlt, hiOuter, _, _, _⟩
  have hzero : |(0 : ℝ)| < 1 / 16 := by norm_num
  have h0half : (0 : ℂ) ∈ closedHalfDisk 0 (1 / 4) := by
    exact ⟨by norm_num, Metric.mem_closedBall_self (by norm_num)⟩
  have h0ball : (0 : ℂ) ∈ Metric.ball (0 : ℂ) 1 := Metric.mem_ball_self zero_lt_one
  have hvalue : UAlt 0 = UOuter 0 := (hcancel 0 hzero).1
  have hinside : ψOuter 0 ∈ Metric.ball (0 : ℂ) 1 := hmapsOuter h0half
  have hdUOuter := (hUOuter.contMDiffAt
    (Metric.isOpen_ball.mem_nhds h0ball)).mdifferentiableAt (by simp)
  have hiUOuter : Injective (mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, E) UOuter 0) := by
    have h := hiOuter 0 h0half
    rwa [mfderivWithin_eq_mfderiv (graph_cauchy_halfdisk_uniqueMDiff _ h0half) hdUOuter] at h
  let κ := Complex.conjCLE.toDiffeomorph.toPartialDiffeomorph.trans χ
  have h0κ : (0 : ℂ) ∈ κ.source := by
    refine ⟨mem_univ _, ?_⟩
    change conj (0 : ℂ) ∈ χ.source
    simpa only [map_zero] using hχsrc (Metric.mem_closedBall_self zero_le_one)
  have hκ0 : κ 0 = χ 0 := by change χ (conj (0 : ℂ)) = χ 0; rw [map_zero]
  have hdκ : DifferentiableAt ℝ κ 0 :=
    (κ.contMDiffOn.contDiffOn.contDiffAt (κ.open_source.mem_nhds h0κ)).differentiableAt
      (by simp)
  have hbijκ := Analysis.bijective_fderiv_of_partialDiffeomorph κ h0κ
  have hχnorm : ‖χ 0‖ = r := by
    rw [hχ0, norm_smul, Real.norm_eq_abs, abs_of_pos hr]
    simp [diskBoundary]
  have hχne : χ 0 ≠ 0 := by
    intro h
    rw [h, norm_zero] at hχnorm
    exact hr.ne' hχnorm.symm
  have hdH : DifferentiableAt ℝ H (κ 0) := by
    rw [hκ0]
    exact (ForwardPhaseAnnulus.contDiffAt_map r b hφ hp hχne).differentiableAt (by simp)
  have hbijH : Bijective (fderiv ℝ H (κ 0)) := by
    rw [hκ0, hχ0]
    exact ForwardPhaseAnnulus.bijective_fderiv_map_at_inner hr hrb hφ hp htpos
  have hDψ : fderiv ℝ ψOuter 0 =
      (fderiv ℝ H (κ 0)).comp (fderiv ℝ κ 0) :=
    (hdH.hasFDerivAt.comp 0 hdκ.hasFDerivAt).fderiv
  have hbijψ : Bijective (fderiv ℝ ψOuter 0) := by
    rw [hDψ]
    exact hbijH.comp hbijκ
  have hdψ : DifferentiableAt ℝ ψOuter 0 :=
    (hψOuter.contDiffAt (Metric.isOpen_ball.mem_nhds h0ball)).differentiableAt (by simp)
  have hpChart : QOriginal (ψOuter 0) ∈ (chartAt E p).source := mem_chart_source E p
  obtain ⟨hP, N, hNN, hPN, hsplit⟩ := original_projection_after_regular_source_map
    hq hQOriginal hd3 ψOuter hdψ hbijψ hinside hiUOuter p hpChart
  let VOuter : Set ℂ := Metric.ball (0 : ℂ) 1 ∩ UOuter ⁻¹' (chartAt E p).source
  let VAlt : Set ℂ := Metric.ball (0 : ℂ) 1 ∩ UAlt ⁻¹' (chartAt E p).source
  have hVO : IsOpen VOuter := hUOuter.continuousOn.isOpen_inter_preimage
    Metric.isOpen_ball (chartAt E p).open_source
  have hVA : IsOpen VAlt := hUAlt.continuousOn.isOpen_inter_preimage
    Metric.isOpen_ball (chartAt E p).open_source
  have h0VO : (0 : ℂ) ∈ VOuter := ⟨h0ball, hpChart⟩
  have h0VA : (0 : ℂ) ∈ VAlt := ⟨h0ball, by
    change UAlt 0 ∈ (chartAt E p).source
    rw [hvalue]
    exact hpChart⟩
  have hrealHalf (t : ℝ) (ht : |t| < 1 / 16) :
      (t : ℂ) ∈ closedHalfDisk 0 (1 / 4) := by
    refine ⟨by simp, ?_⟩
    rw [Metric.mem_closedBall, dist_eq_norm, Complex.ofReal_zero, sub_zero,
      Complex.norm_real, Real.norm_eq_abs]
    linarith
  have hcancelOrder (t : ℝ) (ht : |t| < 1 / 16) :
      inwardConormalWithin G UOuter (closedHalfDisk 0 (1 / 4)) (t : ℂ) +
        tangentSpaceCast 𝓘(ℝ, E) (UAlt (t : ℂ)) (UOuter (t : ℂ))
          (inwardConormalWithin G UAlt (closedHalfDisk 0 (1 / 4)) (t : ℂ)) = 0 := by
    have h := (hcancel t ht).2
    change (show E from inwardConormalWithin G UAlt (closedHalfDisk 0 (1 / 4)) (t : ℂ)) +
      (show E from inwardConormalWithin G UOuter (closedHalfDisk 0 (1 / 4)) (t : ℂ)) = 0 at h
    change (show E from inwardConormalWithin G UOuter (closedHalfDisk 0 (1 / 4)) (t : ℂ)) +
      (show E from inwardConormalWithin G UAlt (closedHalfDisk 0 (1 / 4)) (t : ℂ)) = 0
    rwa [add_comm]
  obtain ⟨eOuter, eAlt, O, h0eOuter, h0eAlt, heOuterV, heAltV, heOuter, heAlt,
      hInvOuter, hInvAlt, hO, h0O, hOt, hsegment, hhOuter, hhAlt,
      hS, hSO, hSne, happroach, hfront, hcontrol, hside, hparameters, hjets, hcurve⟩ :=
    exists_fixed_graph_frontier_cauchy_data_of_conormal_cancellation G UOuter UAlt
      hVO hVA h0VO h0VA (hUOuter.mono inter_subset_left) (hUAlt.mono inter_subset_left)
      (fun t ht => hiOuter _ (hrealHalf t ht)) (fun t ht => hiAlt _ (hrealHalf t ht))
      (fun t ht => (hcancel t ht).1.symm) hcancelOrder p
      (fun _ hz => hz.2) (fun _ hz => hz.2) P (Qg N) (extChartAt 𝓘(ℝ, E) p p)
      hP isOpen_univ (mem_univ _)
  let rOuter : ℂ → ℂ := ψOuter ∘ eOuter.symm
  let rAlt : ℂ → ℂ := D ∘ ψAlt ∘ eAlt.symm
  let S : Set ℂ := O ∩ eAlt '' (eAlt.source ∩ {z : ℂ | 0 < z.im})
  have hDs : ContDiff ℝ ∞ D ∧ ∀ z : ℂ, ‖D z‖ = ‖z‖ := by
    rcases hbranch with ⟨hD, _, _⟩ | ⟨hD, _, _⟩
    · rw [hD]
      exact ⟨contDiff_id, fun _ => rfl⟩
    · rw [hD]
      exact ⟨Complex.conjCLE.contDiff, Complex.norm_conj⟩
  have hrOuter : ContDiffOn ℝ ∞ rOuter O :=
    (hψOuter.comp hInvOuter (fun y hy => (heOuterV (eOuter.map_target hy)).1)).mono
      (fun y hy => (hOt hy).2.1)
  have hrAlt : ContDiffOn ℝ ∞ rAlt O :=
    hDs.1.comp_contDiffOn
      ((hψAlt.comp hInvAlt (fun y hy => (heAltV (eAlt.map_target hy)).1)).mono
        (fun y hy => (hOt hy).2.2))
  have hProper : MapsTo rOuter S (Metric.ball (0 : ℂ) r) := by
    intro y hy
    have him : 0 < (α • conj (eOuter.symm y)).im := by
      have h := mul_pos hα (neg_pos.mpr (hside y hy))
      simpa only [Complex.real_smul, Complex.mul_im, Complex.ofReal_re,
        Complex.ofReal_im, zero_mul, add_zero, Complex.conj_im] using h
    let c := Complex.diskBoundaryChart
      (diskBoundary (t₀ : loopCircle) : ℂ) (by simp [diskBoundary])
    have hsrc : α • conj (eOuter.symm y) ∈ c.source := by
      change α • conj (eOuter.symm y) ≠ -Complex.I
      intro heq
      rw [heq] at him
      norm_num at him
    have hc : ‖c (α • conj (eOuter.symm y))‖ < 1 :=
      (Complex.norm_diskBoundaryChart_lt_one_iff _ _ hsrc).mpr him
    rw [Metric.mem_ball, dist_zero_right]
    change ‖H (χ (conj (eOuter.symm y)))‖ < r
    rw [ForwardPhaseAnnulus.norm_map, hχformula, norm_smul, Real.norm_eq_abs, abs_of_pos hr]
    simpa only [mul_one] using mul_lt_mul_of_pos_left hc hr
  have hInner : MapsTo rAlt S (Metric.ball (0 : ℂ) 1) := by
    intro y hy
    rcases hy.2 with ⟨z, ⟨hzsource, hzim⟩, hzy⟩
    have hinv : eAlt.symm y = z := by rw [← hzy]; exact eAlt.left_inv hzsource
    have hznorm : ‖z‖ < 1 / 16 := by simpa only [hinv] using (hcontrol y hy.1).1
    have hzhalf : z ∈ openHalfDisk 0 (1 / 4) := by
      refine ⟨hzim, ?_⟩
      rw [Metric.mem_ball, Complex.ofReal_zero, dist_zero_right]
      linarith
    have hi : ψAlt z ∈ Metric.ball (0 : ℂ) 1 := hmapsAlt hzhalf
    rw [Metric.mem_ball, dist_zero_right] at hi ⊢
    change ‖D (ψAlt (eAlt.symm y))‖ < 1
    rw [hinv, hDs.2]
    exact hi
  have hScaled : MapsTo (fun y => (r⁻¹ : ℝ) • rOuter y) S
      (Metric.ball (0 : ℂ) 1) := by
    intro y hy
    have hn : ‖rOuter y‖ < r := by
      simpa only [Metric.mem_ball, dist_zero_right] using hProper hy
    rw [Metric.mem_ball, dist_zero_right, norm_smul, Real.norm_eq_abs,
      abs_of_pos (inv_pos.mpr hr)]
    calc
      r⁻¹ * ‖rOuter y‖ < r⁻¹ * r := mul_lt_mul_of_pos_left hn (inv_pos.mpr hr)
      _ = 1 := inv_mul_cancel₀ hr.ne'
  have hUnit : MapsTo rOuter S (Metric.ball (0 : ℂ) 1) :=
    fun y hy => Metric.ball_subset_ball (hrb.trans hb).le (hProper hy)
  refine ⟨N, hNN, hPN, hsplit, eOuter, eAlt, O, h0eOuter, h0eAlt,
    fun z hz => (heOuterV hz).1, fun z hz => (heAltV hz).1,
    heOuter, heAlt, hInvOuter, hInvAlt, hO, h0O, fun y hy => (hOt hy).2,
    hhOuter, hhAlt, hrOuter, hrAlt, ?_, ?_, ?_, ?_, hsegment,
    hS, hSO, hSne, happroach, hfront, hparameters, hjets, hcurve,
    hInner, hProper, hUnit, hScaled⟩
  · intro y hy
    exact (heOuterV (eOuter.map_target (hOt hy).2.1)).2
  · intro y hy
    exact (heAltV (eAlt.map_target (hOt hy).2.2)).2
  · intro y hy
    change (fun z => P (extChartAt 𝓘(ℝ, E) p (UOuter z))) (eOuter.symm y) = y
    rw [← heOuter]
    exact eOuter.right_inv (hOt hy).2.1
  · intro y hy
    change (fun z => P (extChartAt 𝓘(ℝ, E) p (UAlt z))) (eAlt.symm y) = y
    rw [← heAlt]
    exact eAlt.right_inv (hOt hy).2.2

end DifferentialGeometry.Geometry.IMS03ConsumerAudit
