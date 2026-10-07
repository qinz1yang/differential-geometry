/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Geometry.MinimalSurface.Plateau.ChartFoldShortening
import DifferentialGeometry.Geometry.MinimalSurface.Plateau.MorreyDisk
import DifferentialGeometry.Geometry.MinimalSurface.Variation.NonzeroFoldFlow

noncomputable section

open Set Filter Bundle Manifold DifferentialGeometry
open DifferentialGeometry.Geometry DifferentialGeometry.Topology
open DifferentialGeometry.Geometry.ImmersedDiskDivergence.Within
open DifferentialGeometry.Geometry.ImmersedDiskDivergence.HalfDisk
open scoped Topology Manifold ContDiff NNReal ENNReal ComplexConjugate

namespace DifferentialGeometry.Geometry

private theorem equalAreaFold_uniqueDiffOn (p : ℝ) {r : ℝ} (hr : 0 < r) :
    UniqueDiffOn ℝ (closedHalfDisk p r) := by
  apply uniqueDiffOn_convex
    ((convex_halfSpace_im_ge 0).inter (convex_closedBall (p : ℂ) r))
  let q : ℂ := (p : ℂ) + (r / 2 : ℂ) * Complex.I
  have hq : q ∈ (openHalfDisk p r : Set ℂ) := by
    constructor
    · change 0 < q.im
      simp only [q, Complex.add_im, Complex.ofReal_im, Complex.mul_I_im,
        Complex.div_ofNat_re, Complex.ofReal_re, zero_add]
      positivity
    · rw [Metric.mem_ball, dist_eq_norm]
      simp only [q, add_sub_cancel_left, norm_mul, Complex.norm_I, mul_one,
        norm_div, Complex.norm_real, Real.norm_eq_abs, Complex.norm_ofNat]
      rw [abs_of_pos hr]
      linarith
  refine ⟨q, mem_interior_iff_mem_nhds.mpr ?_⟩
  exact mem_of_superset ((openHalfDisk p r).isOpen.mem_nhds hq)
    (fun z hz => ⟨(show 0 < z.im from hz.1).le, Metric.ball_subset_closedBall hz.2⟩)

variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace M] [ChartedSpace E M]
  [IsManifold 𝓘(ℝ, E) ∞ M] [T3Space M]

omit [FiniteDimensional ℝ E] [IsManifold 𝓘(ℝ, E) ∞ M] [T3Space M] in
private theorem equalAreaFold_mfderivWithin_congr {F V : ℂ → M} {K : Set ℂ}
    (heq : EqOn F V K) {z : ℂ} (hz : z ∈ K) :
    (show ℂ →L[ℝ] E from mfderivWithin 𝓘(ℝ, ℂ) 𝓘(ℝ, E) F K z) =
      (show ℂ →L[ℝ] E from mfderivWithin 𝓘(ℝ, ℂ) 𝓘(ℝ, E) V K z) := by
  have hd := mfderivWithin_congr_of_mem (I := 𝓘(ℝ, ℂ)) (I' := 𝓘(ℝ, E)) heq hz
  ext w
  simpa only [ContinuousLinearMap.comp_apply] using!
    congrArg (fun D : ℂ →L[ℝ] E => D w) hd

omit [FiniteDimensional ℝ E] [T3Space M] in
private theorem equalAreaFold_conormal_eq
    (G : SmoothRiemannianMetric 𝓘(ℝ, E) M) {F V : ℂ → M} {K S : Set ℂ} {z : ℂ}
    (hvalue : F z = V z)
    (hderiv : (show ℂ →L[ℝ] E from mfderivWithin 𝓘(ℝ, ℂ) 𝓘(ℝ, E) F K z) =
      (show ℂ →L[ℝ] E from mfderivWithin 𝓘(ℝ, ℂ) 𝓘(ℝ, E) V S z)) :
    (inwardConormalWithin G F K z : E) = (inwardConormalWithin G V S z : E) := by
  let Q : M → (ℂ →L[ℝ] E) → E := fun q D =>
    (Real.sqrt (G.inner q (D 1) (D 1)) *
      tangentTwoJacobian G (x := q) (D 1) (D Complex.I))⁻¹ •
      (G.inner q (D 1) (D 1) • D Complex.I - G.inner q (D 1) (D Complex.I) • D 1)
  have h := congrArg₂ Q hvalue hderiv
  simpa only [Q, inwardConormalWithin, gramWithin, densityWithin, partialWithin] using! h

/-- The two regular local sheets of an equal-area, equal-trace Lipschitz competitor
have opposite metric conormals on a nontrivial seam arc. Both sheets are actual
reparametrizations of the supplied harmonic conformal maps. Only the original
Morrey disk's minimum is used, for the same metric throughout. -/
theorem IsMorreyDisk.equal_area_two_sheet_conormal_sum_eq_zero_on_arc
    {G : SmoothRiemannianMetric 𝓘(ℝ, E) M} {γ : freeLoop M} {q : C(closedDisk, M)}
    (hq : IsMorreyDisk G γ q) (F : C(closedDisk, M)) {L : ℝ≥0}
    (hFLip : ∀ z w, riemannianEDistOf G (F z) (F w) ≤ (L : ℝ≥0∞) * edist z w)
    (hFtrace : diskTrace F = diskTrace q)
    (hFarea : riemannianDiskArea G F = riemannianDiskArea G q)
    (χ : PartialDiffeomorph 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) ℂ ℂ ∞)
    (hχsrc : Metric.closedBall (0 : ℂ) 1 ⊆ χ.source)
    (hχinside : χ '' Metric.closedBall (0 : ℂ) 1 ⊆ Metric.ball (0 : ℂ) 1)
    (U₁ U₂ : ℂ → M) (ψ₁ ψ₂ : ℂ → ℂ)
    (hU₁ : ContMDiffOn 𝓘(ℝ, ℂ) 𝓘(ℝ, E) ∞ U₁ (Metric.ball (0 : ℂ) 1))
    (hconf₁ : ∀ z ∈ Metric.ball (0 : ℂ) 1, DiskMapConformalAt G U₁ z)
    (htension₁ : ∀ z ∈ Metric.ball (0 : ℂ) 1, diskMapTension G U₁ z = 0)
    (hU₂ : ContMDiffOn 𝓘(ℝ, ℂ) 𝓘(ℝ, E) ∞ U₂ (Metric.ball (0 : ℂ) 1))
    (hconf₂ : ∀ z ∈ Metric.ball (0 : ℂ) 1, DiskMapConformalAt G U₂ z)
    (htension₂ : ∀ z ∈ Metric.ball (0 : ℂ) 1, diskMapTension G U₂ z = 0)
    (hψ₁ : ContMDiffOn 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) ∞ ψ₁ (openHalfDisk 0 (1 / 4)))
    (hψ₂ : ContMDiffOn 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) ∞ ψ₂ (openHalfDisk 0 (1 / 4)))
    (hmaps₁ : MapsTo ψ₁ (openHalfDisk 0 (1 / 4)) (Metric.ball (0 : ℂ) 1))
    (hmaps₂ : MapsTo ψ₂ (openHalfDisk 0 (1 / 4)) (Metric.ball (0 : ℂ) 1))
    (hbij₁ : ∀ z ∈ (openHalfDisk 0 (1 / 4) : Set ℂ), Function.Bijective
      (mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) ψ₁ z))
    (hbij₂ : ∀ z ∈ (openHalfDisk 0 (1 / 4) : Set ℂ), Function.Bijective
      (mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) ψ₂ z))
    (hV₁ : ContMDiffOn 𝓘(ℝ, ℂ) 𝓘(ℝ, E) ∞ (U₁ ∘ ψ₁) (Metric.ball (0 : ℂ) 1))
    (hV₂ : ContMDiffOn 𝓘(ℝ, ℂ) 𝓘(ℝ, E) ∞ (U₂ ∘ ψ₂) (Metric.ball (0 : ℂ) 1))
    (hi₁ : ∀ z ∈ closedHalfDisk 0 (1 / 4), Function.Injective
      (mfderivWithin 𝓘(ℝ, ℂ) 𝓘(ℝ, E) (U₁ ∘ ψ₁) (closedHalfDisk 0 (1 / 4)) z))
    (hi₂ : ∀ z ∈ closedHalfDisk 0 (1 / 4), Function.Injective
      (mfderivWithin 𝓘(ℝ, ℂ) 𝓘(ℝ, E) (U₂ ∘ ψ₂) (closedHalfDisk 0 (1 / 4)) z))
    (heq₁ : EqOn (diskExtension F ∘ χ) (U₁ ∘ ψ₁) (closedHalfDisk 0 (1 / 4)))
    (heq₂ : EqOn (diskExtension F ∘ χ ∘ conj) (U₂ ∘ ψ₂) (closedHalfDisk 0 (1 / 4))) :
    ∀ x : ℝ, |x| < 1 / 16 →
      (U₁ ∘ ψ₁) (x : ℂ) = (U₂ ∘ ψ₂) (x : ℂ) ∧
      inwardConormalWithin G (U₁ ∘ ψ₁) (closedHalfDisk 0 (1 / 4)) (x : ℂ) +
        tangentSpaceCast 𝓘(ℝ, E) ((U₂ ∘ ψ₂) (x : ℂ)) ((U₁ ∘ ψ₁) (x : ℂ))
          (inwardConormalWithin G (U₂ ∘ ψ₂) (closedHalfDisk 0 (1 / 4)) (x : ℂ)) = 0 := by
  intro x hx
  have hKball : closedHalfDisk 0 (1 / 4) ⊆ Metric.ball (0 : ℂ) 1 := by
    intro z hz
    exact Metric.mem_ball.mpr ((Metric.mem_closedBall.mp hz.2).trans_lt (by norm_num))
  have hKunit := hKball.trans Metric.ball_subset_closedBall
  have hxK : (x : ℂ) ∈ closedHalfDisk 0 (1 / 4) := by
    refine ⟨(show 0 ≤ (x : ℂ).im from le_rfl), ?_⟩
    simpa only [Metric.mem_closedBall, Complex.ofReal_zero, dist_zero_right,
      Complex.norm_real, Real.norm_eq_abs] using (show |x| ≤ 1 / 4 by linarith)
  refine ⟨?_, ?_⟩
  · refine (heq₁ hxK).symm.trans ?_
    simpa only [Function.comp_apply, Complex.conj_ofReal] using (heq₂ hxK)
  by_contra hnonzero
  let d := diskThroughSourceChart F χ hχsrc
  have hdvalue {z : ℂ} (hz : z ∈ Metric.closedBall (0 : ℂ) 1) :
      diskExtension d z = diskExtension F (χ z) := diskExtension_coe d ⟨z, hz⟩
  have hd₁ : EqOn (diskExtension d) (U₁ ∘ ψ₁) (closedHalfDisk 0 (1 / 4)) :=
    fun z hz => (hdvalue (hKunit hz)).trans (heq₁ hz)
  have hd₂ : EqOn (diskExtension d ∘ conj) (U₂ ∘ ψ₂) (closedHalfDisk 0 (1 / 4)) := by
    intro z hz
    have hzbar : conj z ∈ Metric.closedBall (0 : ℂ) 1 := by
      simpa only [Metric.mem_closedBall, dist_zero_right, Complex.norm_conj] using hKunit hz
    exact (hdvalue hzbar).trans (heq₂ hz)
  have hsmallBall {z : ℂ} (hz : z ∈ closedHalfDisk x (1 / 8)) :
      z ∈ Metric.ball (0 : ℂ) (1 / 4) := by
    have hdist : dist z (0 : ℂ) ≤ 1 / 8 + |x| := calc
      dist z 0 ≤ dist z (x : ℂ) + dist (x : ℂ) 0 := dist_triangle _ _ _
      _ ≤ 1 / 8 + |x| := add_le_add hz.2 (by simp [dist_zero_right])
    exact lt_of_le_of_lt hdist (by linarith)
  have hsub : closedHalfDisk x (1 / 8) ⊆ closedHalfDisk 0 (1 / 4) :=
    fun _ hz => ⟨hz.1, Metric.ball_subset_closedBall (hsmallBall hz)⟩
  have hopenClosed : (openHalfDisk x (1 / 8) : Set ℂ) ⊆ closedHalfDisk x (1 / 8) :=
    fun z hz => ⟨(show 0 < z.im from hz.1).le, Metric.ball_subset_closedBall hz.2⟩
  have hopenSub : (openHalfDisk x (1 / 8) : Set ℂ) ⊆ openHalfDisk 0 (1 / 4) :=
    fun _ hz => ⟨hz.1, hsmallBall (hopenClosed hz)⟩
  have hcenter : (x : ℂ) ∈ closedHalfDisk x (1 / 8) := by
    refine ⟨(show 0 ≤ (x : ℂ).im from le_rfl), ?_⟩
    simp only [Metric.mem_closedBall, dist_self]
    norm_num
  have hV₁K : ContMDiffOn 𝓘(ℝ, ℂ) 𝓘(ℝ, E) 1 (U₁ ∘ ψ₁)
      (closedHalfDisk 0 (1 / 4)) := (hV₁.mono hKball).of_le (by simp)
  have hV₂K : ContMDiffOn 𝓘(ℝ, ℂ) 𝓘(ℝ, E) 1 (U₂ ∘ ψ₂)
      (closedHalfDisk 0 (1 / 4)) := (hV₂.mono hKball).of_le (by simp)
  have hderiv₁ (z : ℂ) (hz : z ∈ closedHalfDisk x (1 / 8)) :
      (show ℂ →L[ℝ] E from mfderivWithin 𝓘(ℝ, ℂ) 𝓘(ℝ, E)
        (diskExtension d) (closedHalfDisk x (1 / 8)) z) =
      (show ℂ →L[ℝ] E from mfderivWithin 𝓘(ℝ, ℂ) 𝓘(ℝ, E)
        (U₁ ∘ ψ₁) (closedHalfDisk 0 (1 / 4)) z) := by
    exact (equalAreaFold_mfderivWithin_congr (hd₁.mono hsub) hz).trans
      (mfderivWithin_subset hsub
        ((equalAreaFold_uniqueDiffOn x (by norm_num : (0 : ℝ) < 1 / 8)).uniqueMDiffOn z hz)
        ((hV₁K z (hsub hz)).mdifferentiableWithinAt one_ne_zero))
  have hderiv₂ (z : ℂ) (hz : z ∈ closedHalfDisk x (1 / 8)) :
      (show ℂ →L[ℝ] E from mfderivWithin 𝓘(ℝ, ℂ) 𝓘(ℝ, E)
        (diskExtension d ∘ conj) (closedHalfDisk x (1 / 8)) z) =
      (show ℂ →L[ℝ] E from mfderivWithin 𝓘(ℝ, ℂ) 𝓘(ℝ, E)
        (U₂ ∘ ψ₂) (closedHalfDisk 0 (1 / 4)) z) := by
    exact (equalAreaFold_mfderivWithin_congr (hd₂.mono hsub) hz).trans
      (mfderivWithin_subset hsub
        ((equalAreaFold_uniqueDiffOn x (by norm_num : (0 : ℝ) < 1 / 8)).uniqueMDiffOn z hz)
        ((hV₂K z (hsub hz)).mdifferentiableWithinAt one_ne_zero))
  have hdi₁ : ∀ z ∈ closedHalfDisk x (1 / 8), Function.Injective
      (mfderivWithin 𝓘(ℝ, ℂ) 𝓘(ℝ, E) (diskExtension d) (closedHalfDisk x (1 / 8)) z) := by
    intro z hz a b hab
    apply hi₁ z (hsub hz)
    exact (congrArg (fun D : ℂ →L[ℝ] E => D a) (hderiv₁ z hz)).symm.trans
      (hab.trans (congrArg (fun D : ℂ →L[ℝ] E => D b) (hderiv₁ z hz)))
  have hdi₂ : ∀ z ∈ closedHalfDisk x (1 / 8), Function.Injective
      (mfderivWithin 𝓘(ℝ, ℂ) 𝓘(ℝ, E) (diskExtension d ∘ conj)
        (closedHalfDisk x (1 / 8)) z) := by
    intro z hz a b hab
    apply hi₂ z (hsub hz)
    exact (congrArg (fun D : ℂ →L[ℝ] E => D a) (hderiv₂ z hz)).symm.trans
      (hab.trans (congrArg (fun D : ℂ →L[ℝ] E => D b) (hderiv₂ z hz)))
  have hfold : inwardConormalWithin G (diskExtension d) (closedHalfDisk x (1 / 8)) (x : ℂ) +
      tangentSpaceCast 𝓘(ℝ, E) ((diskExtension d ∘ conj) (x : ℂ)) (diskExtension d (x : ℂ))
        (inwardConormalWithin G (diskExtension d ∘ conj) (closedHalfDisk x (1 / 8)) (x : ℂ)) ≠ 0 := by
    change (fun a b : E => a + b)
      (inwardConormalWithin G (diskExtension d) (closedHalfDisk x (1 / 8)) (x : ℂ))
      (inwardConormalWithin G (diskExtension d ∘ conj) (closedHalfDisk x (1 / 8)) (x : ℂ)) ≠ 0
    rw [equalAreaFold_conormal_eq G (hd₁ hxK) (hderiv₁ _ hcenter),
      equalAreaFold_conormal_eq G (hd₂ hxK) (hderiv₂ _ hcenter)]
    exact hnonzero
  have hdSmooth₁ : ContMDiffOn 𝓘(ℝ, ℂ) 𝓘(ℝ, E) ∞ (diskExtension d)
      (closedHalfDisk x (1 / 8)) :=
    (hV₁.mono (hsub.trans hKball)).congr (hd₁.mono hsub)
  have hdSmooth₂ : ContMDiffOn 𝓘(ℝ, ℂ) 𝓘(ℝ, E) ∞ (diskExtension d ∘ conj)
      (closedHalfDisk x (1 / 8)) :=
    (hV₂.mono (hsub.trans hKball)).congr (hd₂.mono hsub)
  obtain ⟨ρ, Y, Φ, _, hρR, hY, _, _, hΦ, hΦzero, hvelocity, hfix, hΦW, hnegative⟩ :=
    exists_supported_flow_of_nonzero_fold_of_two_reparametrizations G d U₁ U₂ ψ₁ ψ₂
      hU₁ hconf₁ htension₁ hU₂ hconf₂ htension₂ (W := Set.univ) (by norm_num : (0 : ℝ) < 1 / 8)
      (hdSmooth₁.of_le (by simp)) (hdSmooth₂.of_le (by simp)) hdi₁ hdi₂
      (hψ₁.mono hopenSub) (hψ₂.mono hopenSub)
      (fun _ hz => hmaps₁ (hopenSub hz)) (fun _ hz => hmaps₂ (hopenSub hz))
      (fun z hz => hbij₁ z (hopenSub hz)) (fun z hz => hbij₂ z (hopenSub hz))
      (hd₁.mono (hopenClosed.trans hsub)) (hd₂.mono (hopenClosed.trans hsub))
      (by simp) hfold
  have hopen : Metric.ball (x : ℂ) ρ ∩ {z : ℂ | 0 < z.im} ⊆ (openHalfDisk x (1 / 8) : Set ℂ) :=
    fun z hz => ⟨hz.2, (Metric.mem_ball.mp hz.1).trans_le hρR⟩
  have hclosedNhds (z : ℂ) (hz : z ∈ Metric.ball (x : ℂ) ρ ∩ {z : ℂ | 0 < z.im}) :
      closedHalfDisk x (1 / 8) ∈ 𝓝 z :=
    mem_of_superset ((openHalfDisk x (1 / 8)).isOpen.mem_nhds (hopen hz)) hopenClosed
  have hdi₁' : ∀ z ∈ Metric.ball (x : ℂ) ρ ∩ {z : ℂ | 0 < z.im},
      Function.Injective (mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, E) (diskExtension d) z) := by
    intro z hz
    rw [← mfderivWithin_of_mem_nhds (hclosedNhds z hz)]
    exact hdi₁ z (mem_of_mem_nhds (hclosedNhds z hz))
  have hdi₂' : ∀ z ∈ Metric.ball (x : ℂ) ρ ∩ {z : ℂ | 0 < z.im},
      Function.Injective (mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, E) (diskExtension d ∘ conj) z) := by
    intro z hz
    rw [← mfderivWithin_of_mem_nhds (hclosedNhds z hz)]
    exact hdi₂ z (mem_of_mem_nhds (hclosedNhds z hz))
  obtain ⟨w, K, hwLip, hwtrace, _, hwarea⟩ :=
    exists_disk_area_lt_of_chart_fold_divergence_neg G F hFLip χ (by simp) hχsrc hχinside
      (W := Set.univ) (Set.subset_univ _) Φ hΦ hΦzero Y hY hvelocity x ρ
      (by simpa only [Complex.norm_real, Real.norm_eq_abs] using
        (show |x| + ρ < 1 by linarith))
      hfix hΦW (hdSmooth₁.mono (hopen.trans hopenClosed))
      (hdSmooth₂.mono (hopen.trans hopenClosed)) hdi₁' hdi₂' hnegative
  have hwJordan : DiskWeakJordanTrace γ w := by
    obtain ⟨σ, hσ, hσtrace⟩ := hq.trace
    exact ⟨σ, hσ, hwtrace.trans (hFtrace.trans hσtrace)⟩
  exact (not_lt_of_ge (hq.minimizesLipschitz w hwJordan ⟨K, hwLip⟩))
    (hwarea.trans_eq hFarea)

end DifferentialGeometry.Geometry
