/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Analysis.Calculus.Interpolation.ForwardPhaseAnnulus
import DifferentialGeometry.Analysis.Complex.DiskBoundaryChart
import DifferentialGeometry.Geometry.HarmonicMap.ConformalRank
import DifferentialGeometry.Geometry.MinimalSurface.Plateau.Restriction
import DifferentialGeometry.Geometry.MinimalSurface.Plateau.SmoothDiskTrace
import DifferentialGeometry.Geometry.MinimalSurface.Plateau.SmoothExtension
import DifferentialGeometry.Geometry.MinimalSurface.Variation.ImmersedDiskDivergence
import DifferentialGeometry.Topology.Manifold.ImmersionCriterion
import DifferentialGeometry.Topology.Manifold.OpenSubtype
import DifferentialGeometry.Topology.Manifold.PartialDiffeomorph.Basic
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.ContDiff
import Mathlib.Analysis.Calculus.Deriv.MeanValue

set_option autoImplicit false
noncomputable section

open Set Filter Function Manifold DifferentialGeometry
open DifferentialGeometry.Topology DifferentialGeometry.Analysis
open DifferentialGeometry.Geometry.ImmersedDiskDivergence.Within
open DifferentialGeometry.Geometry.ImmersedDiskDivergence.HalfDisk
open scoped Topology ContDiff Manifold ComplexConjugate

namespace DifferentialGeometry.Geometry

private theorem forward_extension_eq
    {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [TopologicalSpace M] [ChartedSpace E M]
    {u : C(closedDisk, M)} {Q : ℂ → M}
    (hQ : SmoothDiskExtension (E := E) u Q) {z : ℂ}
    (hz : z ∈ Metric.closedBall (0 : ℂ) 1) : Q z = diskExtension u z :=
  (hQ.1 ⟨z, hz⟩).trans (diskExtension_coe u ⟨z, hz⟩).symm

private theorem forward_bijective_neighborhood
    {f : ℂ → ℂ} {V : Set ℂ} (hV : IsOpen V) (hf : ContDiffOn ℝ ∞ f V)
    {x : ℂ} (hx : x ∈ V) (hbij : Bijective (fderiv ℝ f x)) :
    ∃ N : Set ℂ, IsOpen N ∧ x ∈ N ∧ N ⊆ V ∧
      ∀ z ∈ N, Bijective (fderiv ℝ f z) := by
  let A : ℂ ≃L[ℝ] ℂ :=
    (LinearEquiv.ofBijective (fderiv ℝ f x).toLinearMap hbij).toContinuousLinearEquiv
  have hA : (A : ℂ →L[ℝ] ℂ) = fderiv ℝ f x := by ext z; rfl
  have hdf : ContinuousAt (fderiv ℝ f) x :=
    (hf.continuousOn_fderiv_of_isOpen hV (by simp)).continuousAt (hV.mem_nhds hx)
  have hnear : ∀ᶠ z in 𝓝 x, ∃ B : ℂ ≃L[ℝ] ℂ,
      (B : ℂ →L[ℝ] ℂ) = fderiv ℝ f z := by
    have hAn : {D : ℂ →L[ℝ] ℂ | ∃ B : ℂ ≃L[ℝ] ℂ, (B : ℂ →L[ℝ] ℂ) = D} ∈
        𝓝 (fderiv ℝ f x) := by
      rw [← hA]
      exact A.nhds
    exact hdf hAn
  obtain ⟨N, hNsub, hN, hxN⟩ :=
    mem_nhds_iff.mp (Filter.inter_mem (hV.mem_nhds hx) hnear)
  refine ⟨N, hN, hxN, fun z hz => (hNsub hz).1, ?_⟩
  intro z hz
  obtain ⟨B, hB⟩ := (hNsub hz).2
  rw [← hB]
  exact B.bijective

private theorem forward_halfdisk_uniqueMDiff :
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

section RankHelpers

variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace M] [ChartedSpace E M]
  [IsManifold 𝓘(ℝ, E) ∞ M]

omit [FiniteDimensional ℝ E] in
/-- A regular parametrized trace prevents the differential of the same conformal
map from vanishing. The source curve can be the unit circle lift or its radial
scaling; its derivative need not be computed explicitly. -/
private theorem injective_mfderiv_of_regular_curve_trace
    {g : SmoothRiemannianMetric 𝓘(ℝ, E) M} {Q : ℂ → M} {N : Set ℂ}
    (hN : IsOpen N) (hQ : ContMDiffOn 𝓘(ℝ, ℂ) 𝓘(ℝ, E) ∞ Q N)
    {β : ℝ → ℂ} (hβ : ContMDiff 𝓘(ℝ, ℝ) 𝓘(ℝ, ℂ) ∞ β)
    {γ : freeLoop M} (hγ : IsSmoothEmbeddedLoop (E := E) γ)
    {φ : ℝ → ℝ} (hφ : ContDiff ℝ ∞ φ)
    (htrace : ∀ t : ℝ, Q (β t) = γ (φ t : loopCircle))
    {t₀ : ℝ} (ht₀ : β t₀ ∈ N)
    (hconf : DiskMapConformalAt g Q (β t₀)) (hspeed : 0 < deriv φ t₀) :
    Function.Injective (mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, E) Q (β t₀)) := by
  apply hconf.injective_mfderiv_iff.mpr
  intro hzero
  have hQd : MDifferentiableAt 𝓘(ℝ, ℂ) 𝓘(ℝ, E) Q (β t₀) :=
    (hQ.contMDiffAt (hN.mem_nhds ht₀)).mdifferentiableAt (by simp)
  have hβd : MDifferentiableAt 𝓘(ℝ, ℝ) 𝓘(ℝ, ℂ) β t₀ :=
    hβ.mdifferentiable (by simp) t₀
  have heq : Q ∘ β = (fun s : ℝ => γ (s : loopCircle)) ∘ φ := funext htrace
  let DQ : ℂ →L[ℝ] E := mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, E) Q (β t₀)
  let Dβ : ℝ →L[ℝ] ℂ := mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, ℂ) β t₀
  let Dγ : ℝ →L[ℝ] E :=
    mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, E) (fun s : ℝ => γ (s : loopCircle)) (φ t₀)
  let Dφ : ℝ →L[ℝ] ℝ := mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) φ t₀
  let DL : ℝ →L[ℝ] E := mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, E) (Q ∘ β) t₀
  let DR : ℝ →L[ℝ] E :=
    mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, E) ((fun s : ℝ => γ (s : loopCircle)) ∘ φ) t₀
  have hDQ : DQ = 0 := hzero
  have hDL : DL = DQ.comp Dβ := by
    exact mfderiv_comp t₀ hQd hβd
  have hDR : DR = Dγ.comp Dφ := by
    exact mfderiv_comp (I := 𝓘(ℝ, ℝ)) (I' := 𝓘(ℝ, ℝ))
      (I'' := 𝓘(ℝ, E)) t₀ (hγ.smooth.mdifferentiable (by simp) (φ t₀))
        (hφ.contMDiff.mdifferentiable (by simp) t₀)
  have hLR : DL = DR := by
    exact congrArg
      (fun f : ℝ → M => (show ℝ →L[ℝ] E from mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, E) f t₀))
      heq
  have hDzero : Dγ (Dφ 1) = 0 := by
    calc
      Dγ (Dφ 1) = DR 1 := congrArg (fun A : ℝ →L[ℝ] E => A 1) hDR.symm
      _ = DL 1 := congrArg (fun A : ℝ →L[ℝ] E => A 1) hLR.symm
      _ = DQ (Dβ 1) := congrArg (fun A : ℝ →L[ℝ] E => A 1) hDL
      _ = 0 := congrArg (fun A : ℂ →L[ℝ] E => A (Dβ 1)) hDQ
  have hφvalue : Dφ 1 = deriv φ t₀ := by
    dsimp only [Dφ]
    rw [mfderiv_eq_fderiv]
    rfl
  have hDderiv : Dγ (deriv φ t₀) = 0 :=
    (congrArg Dγ hφvalue).symm.trans hDzero
  have hscale : Dγ (deriv φ t₀) = deriv φ t₀ • Dγ 1 := by
    simpa only [smul_eq_mul, mul_one] using Dγ.map_smul (deriv φ t₀) (1 : ℝ)
  have hγnonzero : Dγ 1 ≠ 0 := hγ.immersed (φ t₀)
  exact (smul_ne_zero (ne_of_gt hspeed) hγnonzero) (hscale.symm.trans hDderiv)

/-- Finite-dimensional rank persists on an open neighborhood within the actual
smooth domain. This is the open-subtype argument from ReplacementSeamChart,
with an arbitrary open domain in place of the original unit disk. -/
private theorem exists_open_rank_neighborhood
    {Q : ℂ → M} {N : Set ℂ} (hN : IsOpen N)
    (hQ : ContMDiffOn 𝓘(ℝ, ℂ) 𝓘(ℝ, E) ∞ Q N)
    {a : ℂ} (ha : a ∈ N)
    (hrank : Function.Injective (mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, E) Q a)) :
    ∃ V : Set ℂ, IsOpen V ∧ a ∈ V ∧ V ⊆ N ∧
      ContMDiffOn 𝓘(ℝ, ℂ) 𝓘(ℝ, E) ∞ Q V ∧
      ∀ z ∈ V, Function.Injective (mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, E) Q z) := by
  let S : TopologicalSpace.Opens ℂ := ⟨N, hN⟩
  let F : S → M := fun z => Q z
  let aS : S := ⟨a, ha⟩
  have hF : ContMDiff 𝓘(ℝ, ℂ) 𝓘(ℝ, E) ∞ F :=
    hQ.comp_contMDiff contMDiff_subtype_val (fun z => z.property)
  have hDF : Function.Injective (mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, E) F aS) := by
    change Function.Injective
      (mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, E) (fun z : S => Q z) aS : ℂ →L[ℝ] E)
    rw [DifferentialGeometry.mfderiv_restrict_open]
    exact hrank
  have hImm := DifferentialGeometry.Topology.Manifold.isImmersionAt_of_injective_mfderiv
    (by simp : (∞ : ℕ∞ω) ≠ 0) hF aS hDF
  let T : Set S := {z | IsImmersionAt 𝓘(ℝ, ℂ) 𝓘(ℝ, E) ∞ F z}
  have hT : IsOpen T := IsOpen.isImmersionAt
  have hVN : Subtype.val '' T ⊆ N := by
    rintro _ ⟨z, _, rfl⟩
    exact z.property
  refine ⟨Subtype.val '' T, hN.isOpenMap_subtype_val T hT,
    ⟨aS, hImm, rfl⟩, hVN, hQ.mono hVN, ?_⟩
  rintro _ ⟨z, hz, rfl⟩
  have hd := hz.mfderiv_injective (by simp : (∞ : ℕ∞ω) ≠ 0)
  change Function.Injective
    (mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, E) (fun z : S => Q z) z : ℂ →L[ℝ] E) at hd
  rw [DifferentialGeometry.mfderiv_restrict_open] at hd
  exact hd


end RankHelpers

/-- The literal forward-phase splice has one common regular seam chart at a
positive-speed point. Its outer sheet retains the supplied forward map. Rank
of the alternate sheet is derived from its trace and same-metric conformality. -/
theorem exists_regular_forward_phase_seam_chart
    {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [TopologicalSpace M] [ChartedSpace E M]
    [IsManifold 𝓘(ℝ, E) ∞ M]
    (G : SmoothRiemannianMetric 𝓘(ℝ, E) M)
    (q aForward F : C(closedDisk, M)) (QOriginal QForward : ℂ → M)
    (hQOriginal : SmoothDiskExtension (E := E) q QOriginal)
    (hQForward : SmoothDiskExtension (E := E) aForward QForward)
    (hconfOriginal : ∀ z ∈ Metric.ball (0 : ℂ) 1, DiskMapConformalAt G QOriginal z)
    (hconfForward : ∀ z ∈ Metric.closedBall (0 : ℂ) 1,
      DiskMapConformalAt G QForward z)
    {r b : ℝ} (hr : 0 < r) (hrb : r < b) (hb : b < 1)
    (hΓ : IsSmoothEmbeddedLoop (E := E) (diskTrace (affineSubdisk q 0 r)))
    (φ : ℝ → ℝ) (hφ : ContDiff ℝ ∞ φ) (hp : ∀ t, φ (t + 1) = φ t + 1)
    (htrace : ∀ t : ℝ, diskTrace aForward (t : loopCircle) =
      diskTrace (affineSubdisk q 0 r) (φ t : loopCircle))
    (hFinner : ∀ z : ℂ, ‖z‖ ≤ r →
      diskExtension F z = diskExtension aForward ((r⁻¹ : ℝ) • z))
    (hFmiddle : ∀ z : ℂ, r ≤ ‖z‖ → ‖z‖ ≤ b →
      diskExtension F z = diskExtension q (ForwardPhaseAnnulus.map r b hφ hp z)) :
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
      let UAlt : ℂ → M := QForward ∘ ψAlt
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
  intro H
  obtain ⟨t₀, ht₀, htderiv⟩ := exists_deriv_eq_slope φ zero_lt_one
    hφ.continuous.continuousOn (hφ.differentiable (by simp)).differentiableOn
  have htpos : 0 < deriv φ t₀ := by
    have hperiod : φ 1 = φ 0 + 1 := by simpa only [zero_add] using hp 0
    rw [hperiod] at htderiv
    linarith
  let B : ℝ → ℂ := fun t => diskBoundary (t : loopCircle)
  let p : ℂ := B t₀
  have hBnorm (t : ℝ) : ‖B t‖ = 1 := Circle.norm_coe _
  have hpnorm : ‖p‖ = 1 := hBnorm t₀
  have hBclosed (t : ℝ) : B t ∈ Metric.closedBall (0 : ℂ) 1 :=
    (diskBoundary (t : loopCircle)).property
  have hrunit : r < 1 := hrb.trans hb
  have hrB (t : ℝ) : r • B t ∈ Metric.ball (0 : ℂ) 1 := by
    rw [Metric.mem_ball, dist_zero_right, norm_smul, Real.norm_of_nonneg hr.le,
      hBnorm, mul_one]
    exact hrunit
  have hQOtrace (t : ℝ) : QOriginal (r • B t) =
      diskTrace (affineSubdisk q 0 r) (t : loopCircle) := by
    rw [forward_extension_eq hQOriginal (Metric.ball_subset_closedBall (hrB t))]
    change diskExtension q (r • B t) = diskExtension q (0 + r • B t)
    rw [zero_add]
  have hQFtrace (t : ℝ) : QForward (B t) =
      diskTrace (affineSubdisk q 0 r) (φ t : loopCircle) := by
    exact (hQForward.1 (diskBoundary (t : loopCircle))).trans (htrace t)
  obtain ⟨NO, hNO, hclosedNO, hQNO⟩ := hQOriginal.2
  obtain ⟨NA, hNA, hclosedNA, hQNA⟩ := hQForward.2
  have hBsmooth : ContMDiff 𝓘(ℝ, ℝ) 𝓘(ℝ, ℂ) ∞ B := diskBoundary_lift_contMDiff
  have hrBsmooth : ContMDiff 𝓘(ℝ, ℝ) 𝓘(ℝ, ℂ) ∞ (fun t => r • B t) := by
    exact ((hBsmooth.contDiff).const_smul r).contMDiff
  have hOrigRank : Injective
      (mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, E) QOriginal (r • B (φ t₀))) := by
    apply injective_mfderiv_of_regular_curve_trace hNO hQNO hrBsmooth hΓ contDiff_id
      hQOtrace (hclosedNO (Metric.ball_subset_closedBall (hrB (φ t₀))))
      (hconfOriginal _ (hrB (φ t₀)))
    simp
  have hAltRank : Injective (mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, E) QForward p) :=
    injective_mfderiv_of_regular_curve_trace hNA hQNA hBsmooth hΓ hφ hQFtrace
      (hclosedNA (hBclosed t₀)) (hconfForward _ (hBclosed t₀)) htpos
  obtain ⟨VO, hVO, hpVO, _, hQVO, hVOrank⟩ :=
    exists_open_rank_neighborhood hNO hQNO
      (hclosedNO (Metric.ball_subset_closedBall (hrB (φ t₀)))) hOrigRank
  obtain ⟨VA, hVA, hpVA, _, hQVA, hVArank⟩ :=
    exists_open_rank_neighborhood hNA hQNA (hclosedNA (hBclosed t₀)) hAltRank
  have hrpne : r • p ≠ 0 := by
    apply norm_pos_iff.mp
    rw [norm_smul, Real.norm_of_nonneg hr.le, hpnorm, mul_one]
    exact hr
  have hHsmooth : ContDiffOn ℝ ∞ H {z : ℂ | z ≠ 0} :=
    ForwardPhaseAnnulus.contDiffOn_map r b hφ hp
  have hHbij : Bijective (fderiv ℝ H (r • p)) :=
    ForwardPhaseAnnulus.bijective_fderiv_map_at_inner hr hrb hφ hp htpos
  obtain ⟨VH, hVH, hpVH, hVHne, hVHrank⟩ :=
    forward_bijective_neighborhood isOpen_ne_zero hHsmooth hrpne hHbij
  have hHpoint : H (r • p) = r • B (φ t₀) := by
    change ForwardPhaseAnnulus.map r b hφ hp
      (r • (AddCircle.toCircle (t₀ : loopCircle) : ℂ)) = _
    rw [ForwardPhaseAnnulus.map_pos_smul_toCircle r b hφ hp hr]
    simp only [ForwardPhaseAnnulus.phaseLift, ForwardPhaseAnnulus.cutoff_eq_one hrb le_rfl,
      sub_self, zero_mul, zero_add, one_mul]
    rfl
  let c := Complex.diskBoundaryChart p hpnorm
  let R : ℂ ≃ₘ[ℝ] ℂ :=
    (LinearEquiv.smulOfNeZero ℝ ℂ r hr.ne').toContinuousLinearEquiv.toDiffeomorph
  let κ := c.trans R.toPartialDiffeomorph
  have hc0 : (0 : ℂ) ∈ c.source := by
    change (0 : ℂ) ≠ -Complex.I
    exact (neg_ne_zero.mpr Complex.I_ne_zero).symm
  have hκ0 : (0 : ℂ) ∈ κ.source := ⟨hc0, mem_univ _⟩
  have hcpoint : c 0 = p := Complex.diskBoundaryChart_zero p hpnorm
  have hκpoint : κ 0 = r • p := by change r • c 0 = _; rw [hcpoint]
  have hcc : ContinuousAt c 0 :=
    c.contMDiffOn_toFun.continuousOn.continuousAt (c.open_source.mem_nhds hc0)
  have hκc : ContinuousAt κ 0 :=
    κ.contMDiffOn_toFun.continuousOn.continuousAt (κ.open_source.mem_nhds hκ0)
  have hκne : κ 0 ≠ 0 := by rw [hκpoint]; exact hrpne
  have hHκc : ContinuousAt (H ∘ κ) 0 :=
    (ForwardPhaseAnnulus.contDiffAt_map r b hφ hp hκne).continuousAt.comp hκc
  have hnear : ∀ᶠ z in 𝓝 (0 : ℂ), z ∈ κ.source ∧ c z ∈ VA ∧
      κ z ∈ VH ∧ H (κ z) ∈ VO ∧ r / 2 < ‖κ z‖ ∧ ‖κ z‖ < b := by
    have hcVA : c 0 ∈ VA := by rw [hcpoint]; exact hpVA
    have hκVH : κ 0 ∈ VH := by rw [hκpoint]; exact hpVH
    have hHκVO : (H ∘ κ) 0 ∈ VO := by
      change H (κ 0) ∈ VO
      rw [hκpoint, hHpoint]
      exact hpVO
    have hnormκ : ‖κ 0‖ = r := by
      rw [hκpoint, norm_smul, Real.norm_of_nonneg hr.le, hpnorm, mul_one]
    have hlo : r / 2 < ‖κ 0‖ := by rw [hnormκ]; linarith
    have hhi : ‖κ 0‖ < b := by rw [hnormκ]; exact hrb
    filter_upwards [κ.open_source.mem_nhds hκ0, hcc (hVA.mem_nhds hcVA),
      hκc (hVH.mem_nhds hκVH), hHκc (hVO.mem_nhds hHκVO),
      hκc.norm (Ioi_mem_nhds hlo), hκc.norm (Iio_mem_nhds hhi)] with z hz hza hzh hzo hzl hzu
    exact ⟨hz, hza, hzh, hzo, hzl, hzu⟩
  obtain ⟨ε, hε, hεsub⟩ := Metric.mem_nhds_iff.mp hnear
  let α : ℝ := ε / 4
  have hα : 0 < α := by dsimp only [α]; positivity
  let A : ℂ ≃ₘ[ℝ] ℂ :=
    (LinearEquiv.smulOfNeZero ℝ ℂ α hα.ne').toContinuousLinearEquiv.toDiffeomorph
  let η := A.toPartialDiffeomorph.trans c
  let χ := η.trans R.toPartialDiffeomorph
  let χr := Complex.conjCLE.toDiffeomorph.toPartialDiffeomorph.trans χ
  let ψAlt : ℂ → ℂ := fun z => (r⁻¹ : ℝ) • χ z
  let ψOuter : ℂ → ℂ := H ∘ χ ∘ conj
  let UAlt : ℂ → M := QForward ∘ ψAlt
  let UOuter : ℂ → M := QOriginal ∘ ψOuter
  have hbuffer {z : ℂ} (hz : z ∈ Metric.closedBall (0 : ℂ) 2) :
      α • z ∈ κ.source ∧ c (α • z) ∈ VA ∧ κ (α • z) ∈ VH ∧
        H (κ (α • z)) ∈ VO ∧ r / 2 < ‖κ (α • z)‖ ∧ ‖κ (α • z)‖ < b := by
    apply hεsub
    rw [Metric.mem_ball, dist_zero_right, norm_smul, Real.norm_of_nonneg hα.le]
    have hzNorm : ‖z‖ ≤ 2 := by simpa only [Metric.mem_closedBall, dist_zero_right] using hz
    dsimp only [α]
    nlinarith
  have hbar {z : ℂ} (hz : z ∈ Metric.closedBall (0 : ℂ) 2) :
      conj z ∈ Metric.closedBall (0 : ℂ) 2 := by
    simpa only [Metric.mem_closedBall, dist_zero_right, Complex.norm_conj] using hz
  have hχsource {z : ℂ} (hz : z ∈ Metric.closedBall (0 : ℂ) 2) : z ∈ χ.source :=
    ⟨⟨mem_univ _, (hbuffer hz).1.1⟩, mem_univ _⟩
  have hηsource {z : ℂ} (hz : z ∈ Metric.closedBall (0 : ℂ) 2) : z ∈ η.source :=
    ⟨mem_univ _, (hbuffer hz).1.1⟩
  have hχrsource {z : ℂ} (hz : z ∈ Metric.closedBall (0 : ℂ) 2) : z ∈ χr.source :=
    ⟨mem_univ _, hχsource (hbar hz)⟩
  have hAltEq : ψAlt = η := by
    funext z
    change r⁻¹ • (r • c (α • z)) = c (α • z)
    exact inv_smul_smul₀ hr.ne' _
  have hχvalue (z : ℂ) : χ z = r • c (α • z) := rfl
  have hAltvalue (z : ℂ) : ψAlt z = c (α • z) := by rw [hAltEq]; rfl
  have hOuterEq : ψOuter = H ∘ χr := rfl
  have hunitTwo : Metric.ball (0 : ℂ) 1 ⊆ Metric.closedBall (0 : ℂ) 2 :=
    Metric.ball_subset_closedBall.trans (Metric.closedBall_subset_closedBall (by norm_num))
  have hclosedTwo : Metric.closedBall (0 : ℂ) 1 ⊆ Metric.closedBall (0 : ℂ) 2 :=
    Metric.closedBall_subset_closedBall (by norm_num)
  have hHalfUnit : closedHalfDisk 0 (1 / 4) ⊆ Metric.ball (0 : ℂ) 1 := by
    intro z hz
    exact Metric.mem_ball.mpr ((Metric.mem_closedBall.mp hz.2).trans_lt (by norm_num))
  have hOpenClosed : (openHalfDisk 0 (1 / 4) : Set ℂ) ⊆ closedHalfDisk 0 (1 / 4) :=
    fun z hz => ⟨(show 0 < z.im from hz.1).le, Metric.ball_subset_closedBall hz.2⟩
  have hAltSmooth : ContDiffOn ℝ ∞ ψAlt (Metric.ball (0 : ℂ) 1) := by
    rw [hAltEq]
    exact (η.contMDiffOn_toFun.mono (fun z hz => hηsource (hunitTwo hz))).contDiffOn
  have hχrSmooth : ContDiffOn ℝ ∞ χr (Metric.ball (0 : ℂ) 1) :=
    (χr.contMDiffOn_toFun.mono (fun z hz => hχrsource (hunitTwo hz))).contDiffOn
  have hχrVH (z : ℂ) (hz : z ∈ Metric.ball (0 : ℂ) 1) : χr z ∈ VH :=
    (hbuffer (hbar (hunitTwo hz))).2.2.1
  have hAltVA (z : ℂ) (hz : z ∈ Metric.ball (0 : ℂ) 1) : ψAlt z ∈ VA := by
    rw [hAltvalue]
    exact (hbuffer (hunitTwo hz)).2.1
  have hOuterVO (z : ℂ) (hz : z ∈ Metric.ball (0 : ℂ) 1) : ψOuter z ∈ VO :=
    (hbuffer (hbar (hunitTwo hz))).2.2.2.1
  have hOuterSmooth : ContDiffOn ℝ ∞ ψOuter (Metric.ball (0 : ℂ) 1) :=
    (hHsmooth.mono hVHne).comp hχrSmooth hχrVH
  have hAltBij (z : ℂ) (hz : z ∈ Metric.ball (0 : ℂ) 1) :
      Bijective (fderiv ℝ ψAlt z) := by
    rw [hAltEq]
    have hbij : Bijective (mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) η z) :=
      ((η.isLocalDiffeomorphAt 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) ∞
        (hηsource (hunitTwo hz))).mfderivToContinuousLinearEquiv (by simp)).bijective
    rw [mfderiv_eq_fderiv] at hbij
    change Bijective ((NormedSpace.fromTangentSpace (𝕜 := ℝ) (η z)).symm ∘
      (fderiv ℝ η z) ∘ (NormedSpace.fromTangentSpace (𝕜 := ℝ) z)) at hbij
    exact (Bijective.of_comp_iff _ (NormedSpace.fromTangentSpace (𝕜 := ℝ) z).bijective).mp
      (((NormedSpace.fromTangentSpace (𝕜 := ℝ) (η z)).symm.bijective.of_comp_iff' _).mp hbij)
  have hOuterBij (z : ℂ) (hz : z ∈ Metric.ball (0 : ℂ) 1) :
      Bijective (fderiv ℝ ψOuter z) := by
    have hdH : DifferentiableAt ℝ H (χr z) :=
      ((hHsmooth.mono hVHne).contDiffAt (hVH.mem_nhds (hχrVH z hz))).differentiableAt
        (by simp)
    have hdχr : DifferentiableAt ℝ χr z :=
      (hχrSmooth.contDiffAt (Metric.isOpen_ball.mem_nhds hz)).differentiableAt (by simp)
    rw [hOuterEq, fderiv_comp z hdH hdχr]
    apply (hVHrank _ (hχrVH z hz)).comp
    have hbij : Bijective (mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) χr z) :=
      ((χr.isLocalDiffeomorphAt 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) ∞
        (hχrsource (hunitTwo hz))).mfderivToContinuousLinearEquiv (by simp)).bijective
    rw [mfderiv_eq_fderiv] at hbij
    change Bijective ((NormedSpace.fromTangentSpace (𝕜 := ℝ) (χr z)).symm ∘
      (fderiv ℝ χr z) ∘ (NormedSpace.fromTangentSpace (𝕜 := ℝ) z)) at hbij
    exact (Bijective.of_comp_iff _ (NormedSpace.fromTangentSpace (𝕜 := ℝ) z).bijective).mp
      (((NormedSpace.fromTangentSpace (𝕜 := ℝ) (χr z)).symm.bijective.of_comp_iff' _).mp hbij)
  have hAltClosed : MapsTo ψAlt (closedHalfDisk 0 (1 / 4))
      (Metric.closedBall (0 : ℂ) 1) := by
    intro z hz
    rw [hAltvalue, Metric.mem_closedBall, dist_zero_right]
    apply (Complex.norm_diskBoundaryChart_le_one_iff p hpnorm
      (hbuffer (hunitTwo (hHalfUnit hz))).1.1).mpr
    simpa only [Complex.smul_im, smul_eq_mul] using mul_nonneg hα.le (show 0 ≤ z.im from hz.1)
  have hAltOpen : MapsTo ψAlt (openHalfDisk 0 (1 / 4)) (Metric.ball (0 : ℂ) 1) := by
    intro z hz
    rw [hAltvalue, Metric.mem_ball, dist_zero_right]
    apply (Complex.norm_diskBoundaryChart_lt_one_iff p hpnorm
      (hbuffer (hunitTwo (hHalfUnit (hOpenClosed hz)))).1.1).mpr
    simpa only [Complex.smul_im, smul_eq_mul] using mul_pos hα (show 0 < z.im from hz.1)
  have hχlower (z : ℂ) (hz : z ∈ closedHalfDisk 0 (1 / 4)) : r ≤ ‖χ (conj z)‖ := by
    have hn : 1 ≤ ‖c (α • conj z)‖ := by
      apply le_of_not_gt
      intro hlt
      have him := (Complex.norm_diskBoundaryChart_lt_one_iff p hpnorm
        (hbuffer (hbar (hunitTwo (hHalfUnit hz)))).1.1).mp hlt
      change 0 < (α • conj z).im at him
      simp only [Complex.smul_im, smul_eq_mul, Complex.conj_im] at him
      have hzpos : 0 ≤ z.im := hz.1
      nlinarith
    rw [hχvalue, norm_smul, Real.norm_of_nonneg hr.le]
    simpa only [mul_one] using mul_le_mul_of_nonneg_left hn hr.le
  have hχlowerStrict (z : ℂ) (hz : z ∈ (openHalfDisk 0 (1 / 4) : Set ℂ)) :
      r < ‖χ (conj z)‖ := by
    have hn : 1 < ‖c (α • conj z)‖ := by
      apply lt_of_not_ge
      intro hle
      have him := (Complex.norm_diskBoundaryChart_le_one_iff p hpnorm
        (hbuffer (hbar (hunitTwo (hHalfUnit (hOpenClosed hz))))).1.1).mp hle
      change 0 ≤ (α • conj z).im at him
      simp only [Complex.smul_im, smul_eq_mul, Complex.conj_im] at him
      have hzpos : 0 < z.im := hz.1
      nlinarith
    rw [hχvalue, norm_smul, Real.norm_of_nonneg hr.le]
    simpa only [mul_one] using mul_lt_mul_of_pos_left hn hr
  have hOuterNorm (z : ℂ) : ‖ψOuter z‖ = ‖χ (conj z)‖ :=
    ForwardPhaseAnnulus.norm_map r b hφ hp _
  have hOuterUpper (z : ℂ) (hz : z ∈ closedHalfDisk 0 (1 / 4)) :
      ‖ψOuter z‖ < b := by
    rw [hOuterNorm]
    exact (hbuffer (hbar (hunitTwo (hHalfUnit hz)))).2.2.2.2.2
  have hOuterOpen : MapsTo ψOuter (closedHalfDisk 0 (1 / 4)) (Metric.ball (0 : ℂ) 1) := by
    intro z hz
    rw [Metric.mem_ball, dist_zero_right]
    exact (hOuterUpper z hz).trans hb
  have hUAlt : ContMDiffOn 𝓘(ℝ, ℂ) 𝓘(ℝ, E) ∞ UAlt (Metric.ball (0 : ℂ) 1) :=
    hQVA.comp hAltSmooth.contMDiffOn hAltVA
  have hUOuter : ContMDiffOn 𝓘(ℝ, ℂ) 𝓘(ℝ, E) ∞ UOuter (Metric.ball (0 : ℂ) 1) :=
    hQVO.comp hOuterSmooth.contMDiffOn hOuterVO
  have hiAlt (z : ℂ) (hz : z ∈ closedHalfDisk 0 (1 / 4)) : Injective
      (mfderivWithin 𝓘(ℝ, ℂ) 𝓘(ℝ, E) UAlt (closedHalfDisk 0 (1 / 4)) z) := by
    have hzu := hHalfUnit hz
    have hdQ := (hQVA.contMDiffAt (hVA.mem_nhds (hAltVA z hzu))).mdifferentiableAt (by simp)
    have hdψ := (hAltSmooth.contMDiffOn.contMDiffAt
      (Metric.isOpen_ball.mem_nhds hzu)).mdifferentiableAt (by simp)
    rw [mfderivWithin_eq_mfderiv (forward_halfdisk_uniqueMDiff z hz) (hdQ.comp z hdψ),
      mfderiv_comp z hdQ hdψ]
    apply (hVArank _ (hAltVA z hzu)).comp
    rw [mfderiv_eq_fderiv]
    change Injective ((NormedSpace.fromTangentSpace (𝕜 := ℝ) (ψAlt z)).symm ∘
      (fderiv ℝ ψAlt z) ∘ (NormedSpace.fromTangentSpace (𝕜 := ℝ) z))
    exact (NormedSpace.fromTangentSpace (𝕜 := ℝ) (ψAlt z)).symm.injective.comp
      ((hAltBij z hzu).injective.comp (NormedSpace.fromTangentSpace (𝕜 := ℝ) z).injective)
  have hiOuter (z : ℂ) (hz : z ∈ closedHalfDisk 0 (1 / 4)) : Injective
      (mfderivWithin 𝓘(ℝ, ℂ) 𝓘(ℝ, E) UOuter (closedHalfDisk 0 (1 / 4)) z) := by
    have hzu := hHalfUnit hz
    have hdQ := (hQVO.contMDiffAt (hVO.mem_nhds (hOuterVO z hzu))).mdifferentiableAt (by simp)
    have hdψ := (hOuterSmooth.contMDiffOn.contMDiffAt
      (Metric.isOpen_ball.mem_nhds hzu)).mdifferentiableAt (by simp)
    rw [mfderivWithin_eq_mfderiv (forward_halfdisk_uniqueMDiff z hz) (hdQ.comp z hdψ),
      mfderiv_comp z hdQ hdψ]
    apply (hVOrank _ (hOuterVO z hzu)).comp
    rw [mfderiv_eq_fderiv]
    change Injective ((NormedSpace.fromTangentSpace (𝕜 := ℝ) (ψOuter z)).symm ∘
      (fderiv ℝ ψOuter z) ∘ (NormedSpace.fromTangentSpace (𝕜 := ℝ) z))
    exact (NormedSpace.fromTangentSpace (𝕜 := ℝ) (ψOuter z)).symm.injective.comp
      ((hOuterBij z hzu).injective.comp (NormedSpace.fromTangentSpace (𝕜 := ℝ) z).injective)
  have heqAlt : EqOn (diskExtension F ∘ χ) UAlt (closedHalfDisk 0 (1 / 4)) := by
    intro z hz
    have hχsmall : ‖χ z‖ ≤ r := by
      have hn : ‖c (α • z)‖ ≤ 1 := by
        simpa only [hAltvalue, Metric.mem_closedBall, dist_zero_right] using hAltClosed hz
      rw [hχvalue, norm_smul, Real.norm_of_nonneg hr.le]
      simpa only [mul_one] using mul_le_mul_of_nonneg_left hn hr.le
    exact (hFinner (χ z) hχsmall).trans
      (forward_extension_eq hQForward (hAltClosed hz)).symm
  have heqOuter : EqOn (diskExtension F ∘ χ ∘ conj) UOuter
      (closedHalfDisk 0 (1 / 4)) := by
    intro z hz
    have hχupper : ‖χ (conj z)‖ ≤ b := by
      rw [← hOuterNorm]
      exact (hOuterUpper z hz).le
    exact (hFmiddle (χ (conj z)) (hχlower z hz) hχupper).trans
      (forward_extension_eq hQOriginal (Metric.ball_subset_closedBall (hOuterOpen hz))).symm
  refine ⟨t₀, α, χ, ht₀, htpos, hα, fun _ => rfl,
    fun z hz => hχsource (hclosedTwo hz), ?_, ?_, ?_⟩
  · intro z hz
    exact (hbuffer (hclosedTwo hz)).2.2.2.2
  · rintro _ ⟨z, hz, rfl⟩
    rw [Metric.mem_ball, dist_zero_right]
    exact (hbuffer (hclosedTwo hz)).2.2.2.2.2.trans hb
  · change χ 0 = r • p ∧ ψAlt 0 = p ∧ ψOuter 0 = r • B (φ t₀) ∧ _
    have hχzero : χ 0 = r • p := by rw [hχvalue, smul_zero, hcpoint]
    refine ⟨hχzero, ?_, ?_, hAltSmooth, hOuterSmooth,
      fun z hz => hAltBij z (hHalfUnit (hOpenClosed hz)),
      fun z hz => hOuterBij z (hHalfUnit (hOpenClosed hz)),
      hAltClosed, hAltOpen, hOuterOpen, ?_, hUAlt, hUOuter,
      hiAlt, hiOuter, heqAlt, heqOuter, ?_⟩
    · rw [hAltvalue, smul_zero, hcpoint]
    · change H (χ (conj 0)) = r • B (φ t₀)
      rw [map_zero, hχzero, hHpoint]
    · intro z hz
      exact ⟨by rw [hOuterNorm]; exact hχlowerStrict z hz,
        hOuterUpper z (hOpenClosed hz)⟩
    · intro s hs
      have hsH : (s : ℂ) ∈ closedHalfDisk 0 (1 / 4) := by
        refine ⟨(show 0 ≤ (s : ℂ).im from le_rfl), ?_⟩
        rw [Metric.mem_closedBall, Complex.isometry_ofReal.dist_eq, Real.dist_eq,
          sub_zero]
        exact abs_le.mpr hs
      have hc : conj (s : ℂ) = (s : ℂ) := Complex.conj_ofReal s
      exact (heqAlt hsH).symm.trans
        ((congrArg (diskExtension F ∘ χ) hc.symm).trans (heqOuter hsH))

end DifferentialGeometry.Geometry
