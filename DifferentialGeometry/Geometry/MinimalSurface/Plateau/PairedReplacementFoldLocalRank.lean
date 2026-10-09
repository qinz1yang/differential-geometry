/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Geometry.MinimalSurface.Plateau.PairedReplacementFold
import DifferentialGeometry.Topology.Manifold.ImmersionCriterion
import DifferentialGeometry.Topology.Manifold.OpenSubtype

set_option autoImplicit false
noncomputable section
open Set Filter Bundle Manifold DifferentialGeometry
open DifferentialGeometry.Geometry DifferentialGeometry.Topology
open DifferentialGeometry.Geometry.ImmersedDiskDivergence.Within
open DifferentialGeometry.Geometry.ImmersedDiskDivergence.HalfDisk
open scoped Topology Manifold ContDiff NNReal ENNReal ComplexConjugate

namespace DifferentialGeometry.Geometry

variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace M] [ChartedSpace E M]
  [IsManifold 𝓘(ℝ, E) ∞ M]


/-- Rank at the original seam point gives an open regular neighborhood, also
on the outside of the selected patch. -/
private theorem exists_open_original_rank_neighborhood
    {Q : ℂ → M} (hQ : ContMDiffOn 𝓘(ℝ, ℂ) 𝓘(ℝ, E) ∞ Q (Metric.ball 0 1))
    {a : ℂ} (ha : a ∈ Metric.ball (0 : ℂ) 1)
    (hrank : Function.Injective (mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, E) Q a)) :
    ∃ N : Set ℂ, IsOpen N ∧ a ∈ N ∧ N ⊆ Metric.ball (0 : ℂ) 1 ∧
      ∀ z ∈ N, Function.Injective (mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, E) Q z) := by
  let S : TopologicalSpace.Opens ℂ := ⟨Metric.ball 0 1, Metric.isOpen_ball⟩
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
  refine ⟨Subtype.val '' T, Metric.isOpen_ball.isOpenMap_subtype_val T hT,
    ⟨aS, hImm, rfl⟩, ?_, ?_⟩
  · rintro _ ⟨z, _, rfl⟩
    exact z.property
  · rintro _ ⟨z, hz, rfl⟩
    have hd := hz.mfderiv_injective (by simp : (∞ : ℕ∞ω) ≠ 0)
    change Function.Injective
      (mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, E) (fun z : S => Q z) z : ℂ →L[ℝ] E) at hd
    rw [DifferentialGeometry.mfderiv_restrict_open] at hd
    exact hd

variable [T3Space M]

private theorem exists_smooth_local_source_chart
    (e : PartialDiffeomorph 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) ℂ ℂ 1)
    {p : ℂ} (hp : p ∈ e.source) {V : Set ℂ} (hV : IsOpen V) (hpV : p ∈ V)
    (he : ContMDiffOn 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) ∞ e V) :
    ∃ f : PartialDiffeomorph 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) ℂ ℂ ∞,
      p ∈ f.source ∧ EqOn e f f.source := by
  have hlocal : IsLocalDiffeomorphOn 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) ∞ e (e.source ∩ V) :=
    (he.mono inter_subset_right).isLocalDiffeomorphOn_of_isInvertible_mfderiv
      (e.open_source.inter hV) (by simp)
      (fun z hz => (e.isLocalDiffeomorphAt 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) 1 hz.1).isInvertible_mfderiv one_ne_zero)
  exact hlocal ⟨p, hp, hpV⟩

private theorem paired_fold_uniqueMDiff {r : ℝ} (hr : 0 < r) :
    UniqueMDiffOn 𝓘(ℝ, ℂ) (closedHalfDisk 0 r) := by
  apply UniqueDiffOn.uniqueMDiffOn
  apply uniqueDiffOn_convex
    ((convex_halfSpace_im_ge 0).inter (convex_closedBall (0 : ℂ) r))
  have hinside : (openHalfDisk 0 r : Set ℂ) ⊆ interior (closedHalfDisk 0 r) := by
    intro z hz
    apply mem_interior_iff_mem_nhds.mpr
    exact mem_of_superset ((openHalfDisk 0 r).isOpen.mem_nhds hz)
      (fun q hq => ⟨(show 0 < q.im from hq.1).le, Metric.ball_subset_closedBall hq.2⟩)
  refine ⟨(r / 2 : ℂ) * Complex.I, hinside ?_⟩
  constructor
  · change 0 < ((r / 2 : ℂ) * Complex.I).im
    simp only [Complex.mul_I_im, Complex.div_ofNat_re, Complex.ofReal_re]
    positivity
  · rw [Metric.mem_ball, dist_eq_norm, Complex.ofReal_zero, sub_zero]
    simp only [norm_mul, Complex.norm_I, mul_one, norm_div,
      Complex.norm_real, Real.norm_eq_abs, Complex.norm_ofNat]
    rw [abs_of_pos hr]
    linarith

omit [FiniteDimensional ℝ E] [IsManifold 𝓘(ℝ, E) ∞ M] [T3Space M] in
private theorem paired_fold_mfderivWithin_congr {F G : ℂ → M} {H : Set ℂ}
    (heq : EqOn F G H) {z : ℂ} (hz : z ∈ H) :
    (show ℂ →L[ℝ] E from mfderivWithin 𝓘(ℝ, ℂ) 𝓘(ℝ, E) F H z) =
      (show ℂ →L[ℝ] E from mfderivWithin 𝓘(ℝ, ℂ) 𝓘(ℝ, E) G H z) := by
  have hd := mfderivWithin_congr_of_mem (I := 𝓘(ℝ, ℂ)) (I' := 𝓘(ℝ, E)) heq hz
  ext w
  simpa only [ContinuousLinearMap.comp_apply] using!
    congrArg (fun D : ℂ →L[ℝ] E => D w) hd

omit [FiniteDimensional ℝ E] [T3Space M] in
private theorem paired_fold_conormal_congr
    (g : SmoothRiemannianMetric 𝓘(ℝ, E) M) {F G : ℂ → M} {H : Set ℂ}
    (heq : EqOn F G H) {z : ℂ} (hz : z ∈ H) :
    (inwardConormalWithin g F H z : E) = (inwardConormalWithin g G H z : E) := by
  let Q : M → (ℂ →L[ℝ] E) → E := fun q D =>
    (Real.sqrt (g.inner q (D 1) (D 1)) *
      tangentTwoJacobian g (x := q) (D 1) (D Complex.I))⁻¹ •
      (g.inner q (D 1) (D 1) • D Complex.I - g.inner q (D 1) (D Complex.I) • D 1)
  have h := congrArg₂ Q (heq hz) (paired_fold_mfderivWithin_congr heq hz)
  simpa only [Q, inwardConormalWithin, gramWithin, densityWithin, partialWithin] using! h

private theorem paired_fold_chart_fderiv_bijective
    (ψ : PartialDiffeomorph 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) ℂ ℂ ∞)
    {z : ℂ} (hz : z ∈ ψ.source) : Function.Bijective (fderiv ℝ ψ z) := by
  have h := ((ψ.isLocalDiffeomorphAt 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) ∞ hz).mfderivToContinuousLinearEquiv (by simp)).bijective
  change Function.Bijective (mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) ψ z) at h
  rw [mfderiv_eq_fderiv] at h
  simpa only [Function.comp_def, ContinuousLinearMap.comp_apply,
    ContinuousLinearEquiv.apply_symm_apply, ContinuousLinearEquiv.symm_apply_apply] using!
    (NormedSpace.fromTangentSpace (𝕜 := ℝ) (ψ z)).bijective.comp
      (h.comp (NormedSpace.fromTangentSpace (𝕜 := ℝ) z).symm.bijective)

omit [FiniteDimensional ℝ E] [IsManifold 𝓘(ℝ, E) ∞ M] [T3Space M] in
private theorem paired_fold_sheet_regular
    {U : ℂ → M} (hU : ContMDiffOn 𝓘(ℝ, ℂ) 𝓘(ℝ, E) ∞ U (Metric.ball 0 1))
    (ψ : PartialDiffeomorph 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) ℂ ℂ ∞)
    (hiU : ∀ z ∈ ψ.target,
      Function.Injective (mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, E) U z))
    {r : ℝ} (hr : 0 < r) (hsource : closedHalfDisk 0 r ⊆ ψ.source)
    (htarget : ψ.target ⊆ Metric.ball (0 : ℂ) 1) :
    ContMDiffOn 𝓘(ℝ, ℂ) 𝓘(ℝ, E) ∞ (U ∘ ψ) (closedHalfDisk 0 r) ∧
      ∀ z ∈ closedHalfDisk 0 r, Function.Injective
        (mfderivWithin 𝓘(ℝ, ℂ) 𝓘(ℝ, E) (U ∘ ψ) (closedHalfDisk 0 r) z) := by
  refine ⟨hU.comp (ψ.contMDiffOn_toFun.mono hsource)
    (fun z hz => htarget (ψ.map_source' (hsource hz))), ?_⟩
  intro z hz
  have hdψ := ψ.mdifferentiableAt (by simp) (hsource hz)
  have hdU := (hU.contMDiffAt
    (Metric.isOpen_ball.mem_nhds (htarget (ψ.map_source' (hsource hz))))).mdifferentiableAt
      (by simp)
  rw [mfderivWithin_eq_mfderiv (paired_fold_uniqueMDiff hr z hz) (hdU.comp z hdψ),
    mfderiv_comp z hdU hdψ]
  exact (hiU (ψ z) (ψ.map_source' (hsource hz))).comp
    ((ψ.isLocalDiffeomorphAt 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) ∞ (hsource hz)).mfderivToContinuousLinearEquiv (by simp)).injective


/-- On the same Morrey minimizer, the genuine paired source disks cannot be
transverse at their matched marked point if the original disk derivative is
injective at just those two source points. The full C¹ paired disks and their
whole boundary matching remain fixed; only the smooth Cayley buffer shrinks
inside the two open regular neighborhoods. -/
theorem IsMorreyDisk.not_transverse_of_paired_source_disks_smooth_near_of_injective_at
    {g : SmoothRiemannianMetric 𝓘(ℝ, E) M} {γ : freeLoop M} {u : C(closedDisk, M)}
    (hu : IsMorreyDisk g γ u) {Uext : ℂ → M} (hUext : SmoothDiskExtension (E := E) u Uext)
    (e₁ e₂ : PartialDiffeomorph 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) ℂ ℂ 1)
    (hsrc₁ : Metric.closedBall (0 : ℂ) 1 ⊆ e₁.source)
    (hsrc₂ : Metric.closedBall (0 : ℂ) 1 ⊆ e₂.source)
    (hinside₁ : e₁ '' Metric.closedBall (0 : ℂ) 1 ⊆ Metric.ball (0 : ℂ) 1)
    (hinside₂ : e₂ '' Metric.closedBall (0 : ℂ) 1 ⊆ Metric.ball (0 : ℂ) 1)
    (hboundary : ∀ z ∈ Metric.sphere (0 : ℂ) 1,
      diskExtension u (e₁ z) = diskExtension u (e₂ z))
    (hdim : Module.finrank ℝ E = 3)
    {W : Set M} (huW : Set.range u ⊆ W) (p : ℂ) (hp : ‖p‖ = 1)
    (hiU₁ : Function.Injective
      (mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, E) (diskExtension u) (e₁ p)))
    (hiU₂ : Function.Injective
      (mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, E) (diskExtension u) (e₂ p)))
    (V₁ V₂ : Set ℂ) (hV₁ : IsOpen V₁) (hV₂ : IsOpen V₂)
    (hpV₁ : p ∈ V₁) (hpV₂ : p ∈ V₂)
    (he₁ : ContMDiffOn 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) ∞ e₁ V₁)
    (he₂ : ContMDiffOn 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) ∞ e₂ V₂)
    (hpW : diskExtension u (e₁ p) ∈ interior W) :
    ¬ Function.Surjective
      ((show ℂ →L[ℝ] E from mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, E) (diskExtension u) (e₁ p)).coprod
        (-(show ℂ →L[ℝ] E from mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, E) (diskExtension u) (e₂ p)))) := by
  intro htrans
  have hpD : p ∈ Metric.closedBall (0 : ℂ) 1 := by simpa only [Metric.mem_closedBall, dist_zero_right] using hp.le
  obtain ⟨N₁, hN₁, hpN₁, _hN₁ball, hiN₁⟩ :=
    exists_open_original_rank_neighborhood hu.smoothInterior
      (hinside₁ ⟨p, hpD, rfl⟩) hiU₁
  obtain ⟨N₂, hN₂, hpN₂, _hN₂ball, hiN₂⟩ :=
    exists_open_original_rank_neighborhood hu.smoothInterior
      (hinside₂ ⟨p, hpD, rfl⟩) hiU₂
  obtain ⟨f₁, hpf₁, hef₁⟩ := exists_smooth_local_source_chart e₁ (hsrc₁ hpD) hV₁ hpV₁ he₁
  obtain ⟨f₂, hpf₂, hef₂⟩ := exists_smooth_local_source_chart e₂ (hsrc₂ hpD) hV₂ hpV₂ he₂
  obtain ⟨v, L, R₀, hR₀, hvLip, hvtrace, hvW, hvarea, _, hbuffer₀, heq₁₀, heq₂₀⟩ :=
    exists_paired_subdisk_replacement_with_cayley_sheets g u hUext e₁ e₂
      hsrc₁ hsrc₂ hinside₁ hinside₂ hboundary huW p hp
  have hpatch := hu.paired_subdisk_areas_eq hUext e₁ e₂
    hsrc₁ hsrc₂ hinside₁ hinside₂ hboundary
  have hvareaeq : riemannianDiskArea g v = riemannianDiskArea g u := by
    rw [hpatch] at hvarea
    linarith
  let c := Complex.diskBoundaryChart p hp
  have hc₀ : (0 : ℂ) ∈ c.source := by
    change (0 : ℂ) ≠ -Complex.I
    exact (neg_ne_zero.mpr Complex.I_ne_zero).symm
  have hc := c.contMDiffOn_toFun.continuousOn.continuousAt (c.open_source.mem_nhds hc₀)
  have hcp₁ : c 0 ∈ f₁.source := by rw [Complex.diskBoundaryChart_zero]; exact hpf₁
  have hcp₂ : c 0 ∈ f₂.source := by rw [Complex.diskBoundaryChart_zero]; exact hpf₂
  have hf₁c : ContinuousAt (fun z : ℂ => f₁ (c z)) 0 :=
    (f₁.contMDiffOn_toFun.continuousOn.continuousAt
      (f₁.open_source.mem_nhds hcp₁)).comp hc
  have hf₂c : ContinuousAt (fun z : ℂ => f₂ (c z)) 0 :=
    (f₂.contMDiffOn_toFun.continuousOn.continuousAt
      (f₂.open_source.mem_nhds hcp₂)).comp hc
  have hf₁N : f₁ (c 0) ∈ N₁ := by
    rw [Complex.diskBoundaryChart_zero, ← hef₁ hpf₁]
    exact hpN₁
  have hf₂N : f₂ (c 0) ∈ N₂ := by
    rw [Complex.diskBoundaryChart_zero, ← hef₂ hpf₂]
    exact hpN₂
  have hnear : ∀ᶠ z in 𝓝 (0 : ℂ), c z ∈ f₁.source ∧ c z ∈ f₂.source ∧
      f₁ (c z) ∈ N₁ ∧ f₂ (c z) ∈ N₂ := by
    filter_upwards [hc (f₁.open_source.mem_nhds hcp₁), hc (f₂.open_source.mem_nhds hcp₂),
      hf₁c (hN₁.mem_nhds hf₁N), hf₂c (hN₂.mem_nhds hf₂N)]
      with z hz₁ hz₂ hNz₁ hNz₂
    exact ⟨hz₁, hz₂, hNz₁, hNz₂⟩
  obtain ⟨ε, hε, hεsub⟩ := Metric.mem_nhds_iff.mp hnear
  let R := min R₀ (ε / 4)
  have hR : 0 < R := lt_min hR₀ (by positivity)
  have hRR₀ : R ≤ R₀ := min_le_left _ _
  have hRε : R ≤ ε / 4 := min_le_right _ _
  have hfsource {z : ℂ} (hz : z ∈ Metric.closedBall (0 : ℂ) (2 * R)) :
      c z ∈ f₁.source ∧ c z ∈ f₂.source := by
    have h := hεsub (Metric.closedBall_subset_ball (by linarith) hz)
    exact ⟨h.1, h.2.1⟩
  have hRankBuffer (z : ℂ) (hz : z ∈ Metric.closedBall (0 : ℂ) (2 * R)) :
      Function.Injective (mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, E) (diskExtension u) (f₁ (c z))) ∧
      Function.Injective (mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, E) (diskExtension u) (f₂ (c z))) := by
    have h := hεsub (Metric.closedBall_subset_ball (by linarith) hz)
    exact ⟨hiN₁ _ h.2.2.1, hiN₂ _ h.2.2.2⟩
  have hbuffer (z : ℂ) (hz : z ∈ Metric.closedBall (0 : ℂ) (2 * R)) :
      z ∈ c.source ∧ c z ∈ f₁.source ∧ c z ∈ f₂.source ∧
      f₁ (c z) ∈ Metric.ball (0 : ℂ) 1 ∧ f₂ (c z) ∈ Metric.ball (0 : ℂ) 1 := by
    have h := hbuffer₀ z (Metric.closedBall_subset_closedBall
      (mul_le_mul_of_nonneg_left hRR₀ (by norm_num)) hz)
    obtain ⟨hf₁, hf₂⟩ := hfsource hz
    refine ⟨h.1, hf₁, hf₂, ?_, ?_⟩
    · rw [← hef₁ hf₁]; exact h.2.2.2.1
    · rw [← hef₂ hf₂]; exact h.2.2.2.2
  have hsmall : closedHalfDisk 0 R ⊆ closedHalfDisk 0 R₀ :=
    fun z hz => ⟨hz.1, Metric.closedBall_subset_closedBall hRR₀ hz.2⟩
  have heq₁ : EqOn (diskExtension v ∘ f₂ ∘ c) (diskExtension u ∘ f₁ ∘ c)
      (closedHalfDisk 0 R) := by
    intro z hz
    have hf := hfsource (Metric.closedBall_subset_closedBall (by linarith : R ≤ 2 * R) hz.2)
    change diskExtension v (f₂ (c z)) = diskExtension u (f₁ (c z))
    rw [← hef₂ hf.2, ← hef₁ hf.1]
    exact heq₁₀ (hsmall hz)
  have heq₂ : EqOn ((diskExtension v ∘ f₂ ∘ c) ∘ conj)
      ((diskExtension u ∘ f₂ ∘ c) ∘ conj) (closedHalfDisk 0 R) := by
    intro z hz
    have hzbar : conj z ∈ Metric.closedBall (0 : ℂ) (2 * R) := by
      simpa only [Metric.mem_closedBall, Complex.ofReal_zero, dist_zero_right, Complex.norm_conj] using
        Metric.closedBall_subset_closedBall (by linarith : R ≤ 2 * R) hz.2
    have hf := (hfsource hzbar).2
    change diskExtension v (f₂ (c (conj z))) = diskExtension u (f₂ (c (conj z)))
    rw [← hef₂ hf]
    exact heq₂₀ (hsmall hz)
  let a : ℝ := R / 2
  have ha : 0 < a := half_pos hR
  let D : Diffeomorph 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) ℂ ℂ ∞ :=
    (LinearEquiv.smulOfNeZero ℝ ℂ a ha.ne').toContinuousLinearEquiv.toDiffeomorph
  let κ₁ := (D.toPartialDiffeomorph.trans c).trans f₁
  let χ := (D.toPartialDiffeomorph.trans c).trans f₂
  let κ₂ := Complex.conjCLE.toDiffeomorph.toPartialDiffeomorph.trans χ
  let ψ₁ := DifferentialGeometry.Topology.PartialDiffeomorph.restrict κ₁
    (Metric.ball (0 : ℂ) 2) Metric.isOpen_ball
  let ψ₂ := DifferentialGeometry.Topology.PartialDiffeomorph.restrict κ₂
    (Metric.ball (0 : ℂ) 2) Metric.isOpen_ball
  have hscale {s : ℝ} {z : ℂ} (hz : z ∈ Metric.closedBall (0 : ℂ) s) :
      a • z ∈ Metric.closedBall (0 : ℂ) (a * s) := by
    rw [Metric.mem_closedBall, dist_zero_right, norm_smul, Real.norm_of_nonneg ha.le]
    exact mul_le_mul_of_nonneg_left (show ‖z‖ ≤ s by simpa only [Metric.mem_closedBall, dist_zero_right] using hz) ha.le
  have hscaledBuffer {z : ℂ} (hz : z ∈ Metric.closedBall (0 : ℂ) 2) :
      a • z ∈ Metric.closedBall (0 : ℂ) (2 * R) :=
    Metric.closedBall_subset_closedBall (by dsimp only [a]; linarith) (hscale hz)
  have hbar {s : ℝ} {z : ℂ} (hz : z ∈ Metric.closedBall (0 : ℂ) s) :
      conj z ∈ Metric.closedBall (0 : ℂ) s := by
    simpa only [Metric.mem_closedBall, Complex.ofReal_zero, dist_zero_right, Complex.norm_conj] using hz
  have hκsources {z : ℂ} (hz : z ∈ Metric.closedBall (0 : ℂ) 2) :
      z ∈ κ₁.source ∧ z ∈ χ.source ∧ z ∈ κ₂.source := by
    have h₁ := hbuffer (a • z) (hscaledBuffer hz)
    have h₂ := hbuffer (a • conj z) (hscaledBuffer (hbar hz))
    exact ⟨⟨⟨mem_univ _, h₁.1⟩, h₁.2.1⟩,
      ⟨⟨mem_univ _, h₁.1⟩, h₁.2.2.1⟩,
      ⟨mem_univ _, ⟨⟨mem_univ _, h₂.1⟩, h₂.2.2.1⟩⟩⟩
  have hχsrc : Metric.closedBall (0 : ℂ) 1 ⊆ χ.source := by
    intro z hz
    exact (hκsources (Metric.closedBall_subset_closedBall (by norm_num) hz)).2.1
  have hχinside : χ '' Metric.closedBall (0 : ℂ) 1 ⊆ Metric.ball (0 : ℂ) 1 := by
    rintro _ ⟨z, hz, rfl⟩
    exact (hbuffer (a • z) (hscaledBuffer
      (Metric.closedBall_subset_closedBall (by norm_num) hz))).2.2.2.2
  let d := diskThroughSourceChart v χ hχsrc
  have hdvalue {z : ℂ} (hz : z ∈ Metric.closedBall (0 : ℂ) 1) :
      diskExtension d z = diskExtension v (f₂ (c (a • z))) :=
    diskExtension_coe d ⟨z, hz⟩
  have hB (z : ℂ) (hz : z ∈ Metric.closedBall (0 : ℂ) (2 * (1 / 4 : ℝ))) :
      z ∈ ψ₁.source ∧ z ∈ ψ₂.source := by
    have hz₂ : z ∈ Metric.closedBall (0 : ℂ) 2 :=
      Metric.closedBall_subset_closedBall (by norm_num) hz
    have hzball : z ∈ Metric.ball (0 : ℂ) 2 := Metric.closedBall_subset_ball (by norm_num) hz
    exact ⟨⟨(hκsources hz₂).1, hzball⟩, ⟨(hκsources hz₂).2.2, hzball⟩⟩
  have htarget₁ : ψ₁.target ⊆ Metric.ball (0 : ℂ) 1 := by
    rintro z ⟨hzκ, hzB⟩
    have h := (hbuffer (a • κ₁.symm z)
      (hscaledBuffer (Metric.ball_subset_closedBall hzB))).2.2.2.1
    change κ₁.toPartialEquiv (κ₁.toPartialEquiv.symm z) ∈ Metric.ball (0 : ℂ) 1 at h
    simpa only [κ₁.toPartialEquiv.right_inv hzκ] using h
  have htarget₂ : ψ₂.target ⊆ Metric.ball (0 : ℂ) 1 := by
    rintro z ⟨hzκ, hzB⟩
    have h := (hbuffer (a • conj (κ₂.symm z))
      (hscaledBuffer (hbar (Metric.ball_subset_closedBall hzB)))).2.2.2.2
    change κ₂.toPartialEquiv (κ₂.toPartialEquiv.symm z) ∈ Metric.ball (0 : ℂ) 1 at h
    simpa only [κ₂.toPartialEquiv.right_inv hzκ] using h
  have htargetRank₁ : ∀ z ∈ ψ₁.target,
      Function.Injective (mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, E) (diskExtension u) z) := by
    rintro z ⟨hzκ, hzB⟩
    have h := (hRankBuffer (a • κ₁.symm z)
      (hscaledBuffer (Metric.ball_subset_closedBall hzB))).1
    change Function.Injective (mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, E) (diskExtension u)
      (κ₁.toPartialEquiv (κ₁.toPartialEquiv.symm z))) at h
    exact Eq.mp (congrArg (fun w : ℂ => Function.Injective
      (mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, E) (diskExtension u) w))
      (κ₁.toPartialEquiv.right_inv hzκ)) h
  have htargetRank₂ : ∀ z ∈ ψ₂.target,
      Function.Injective (mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, E) (diskExtension u) z) := by
    rintro z ⟨hzκ, hzB⟩
    have h := (hRankBuffer (a • conj (κ₂.symm z))
      (hscaledBuffer (hbar (Metric.ball_subset_closedBall hzB)))).2
    change Function.Injective (mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, E) (diskExtension u)
      (κ₂.toPartialEquiv (κ₂.toPartialEquiv.symm z))) at h
    exact Eq.mp (congrArg (fun w : ℂ => Function.Injective
      (mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, E) (diskExtension u) w))
      (κ₂.toPartialEquiv.right_inv hzκ)) h
  have hcenter₁ : ψ₁ 0 = e₁ p := by
    change f₁ (c (a • (0 : ℂ))) = e₁ p
    rw [smul_zero, Complex.diskBoundaryChart_zero]
    exact (hef₁ hpf₁).symm
  have hcenter₂ : ψ₂ 0 = e₂ p := by
    change f₂ (c (a • conj (0 : ℂ))) = e₂ p
    rw [map_zero, smul_zero, Complex.diskBoundaryChart_zero]
    exact (hef₂ hpf₂).symm
  have hscaledHalf {z : ℂ} (hz : z ∈ closedHalfDisk 0 (1 / 4)) :
      a • z ∈ closedHalfDisk 0 R := by
    refine ⟨?_, Metric.closedBall_subset_closedBall (by dsimp only [a]; linarith) (hscale hz.2)⟩
    change 0 ≤ (a • z).im
    simpa only [Complex.real_smul, Complex.mul_im, Complex.ofReal_re,
      Complex.ofReal_im, zero_mul, add_zero] using mul_nonneg ha.le (show 0 ≤ z.im from hz.1)
  have hHunit : closedHalfDisk 0 (1 / 4) ⊆ Metric.closedBall (0 : ℂ) 1 :=
    fun _ hz => Metric.closedBall_subset_closedBall (by norm_num) hz.2
  have hF₁ : EqOn (diskExtension d) (diskExtension u ∘ ψ₁) (closedHalfDisk 0 (1 / 4)) := by
    intro z hz
    rw [hdvalue (hHunit hz)]
    exact heq₁ (hscaledHalf hz)
  have hF₂ : EqOn (diskExtension d ∘ conj) (diskExtension u ∘ ψ₂)
      (closedHalfDisk 0 (1 / 4)) := by
    intro z hz
    change diskExtension d (conj z) = diskExtension u (f₂ (c (a • conj z)))
    rw [hdvalue (hbar (hHunit hz))]
    simpa only [Function.comp_apply, Complex.real_smul, map_mul, Complex.conj_ofReal]
      using heq₂ (hscaledHalf hz)
  have hseam (t : ℝ) (ht : t ∈ Icc (-2 * (1 / 4 : ℝ)) (2 * (1 / 4 : ℝ))) :
      diskExtension u (ψ₁ (t : ℂ)) = diskExtension u (ψ₂ (t : ℂ)) := by
    change diskExtension u (f₁ (c (a • (t : ℂ)))) =
      diskExtension u (f₂ (c (a • conj (t : ℂ))))
    rw [Complex.conj_ofReal]
    have htB : (t : ℂ) ∈ Metric.closedBall (0 : ℂ) 2 := by
      rw [Metric.mem_closedBall, dist_zero_right, Complex.norm_real, Real.norm_eq_abs, abs_le]
      constructor <;> linarith [ht.1, ht.2]
    have hf := hfsource (hscaledBuffer htB)
    rw [← hef₁ hf.1, ← hef₂ hf.2]
    apply hboundary
    rw [Metric.mem_sphere, dist_zero_right]
    apply (Complex.norm_diskBoundaryChart_eq_one_iff p hp ?_).mpr (by simp)
    change a • (t : ℂ) ≠ -Complex.I
    intro heq
    have him := congrArg Complex.im heq
    simp only [Complex.real_smul, Complex.mul_im, Complex.ofReal_re,
      Complex.ofReal_im, zero_mul, mul_zero, add_zero, Complex.neg_im, Complex.I_im] at him
    norm_num at him
  have hpS : p ∈ Metric.sphere (0 : ℂ) 1 := by simpa only [Metric.mem_sphere, dist_zero_right] using hp
  have hquarter : (0 : ℝ) < 1 / 4 := by norm_num
  obtain ⟨_, _, _, _, _, _, hnonzero, _⟩ :=
    paired_halfdisk_inward_conormals_ne_zero_of_transverse g Metric.isOpen_ball hu.smoothInterior
      (hboundary p hpS) hiU₁ hiU₂ htrans hdim hquarter
      ψ₁.toOpenPartialHomeomorph ψ₂.toOpenPartialHomeomorph
      hcenter₁ hcenter₂ hB htarget₁ htarget₂
      (contMDiffOn_iff_contDiffOn.mp ψ₁.contMDiffOn_toFun)
      (contMDiffOn_iff_contDiffOn.mp ψ₂.contMDiffOn_toFun)
      (fun _ hz => paired_fold_chart_fderiv_bijective ψ₁ hz)
      (fun _ hz => paired_fold_chart_fderiv_bijective ψ₂ hz) hseam
  have hHsrc : closedHalfDisk 0 (1 / 4) ⊆ ψ₁.source ∩ ψ₂.source := by
    intro z hz
    exact hB z (Metric.closedBall_subset_closedBall (by norm_num) hz.2)
  obtain ⟨hreg₁, hrank₁⟩ := paired_fold_sheet_regular hu.smoothInterior ψ₁ htargetRank₁ hquarter
    (fun _ hz => (hHsrc hz).1) htarget₁
  obtain ⟨hreg₂, hrank₂⟩ := paired_fold_sheet_regular hu.smoothInterior ψ₂ htargetRank₂ hquarter
    (fun _ hz => (hHsrc hz).2) htarget₂
  have hd₁ : ContMDiffOn 𝓘(ℝ, ℂ) 𝓘(ℝ, E) ∞ (diskExtension d)
      (closedHalfDisk 0 (1 / 4)) := hreg₁.congr hF₁
  have hd₂ : ContMDiffOn 𝓘(ℝ, ℂ) 𝓘(ℝ, E) ∞ (diskExtension d ∘ conj)
      (closedHalfDisk 0 (1 / 4)) := hreg₂.congr hF₂
  have hdi₁ : ∀ z ∈ closedHalfDisk 0 (1 / 4), Function.Injective
      (mfderivWithin 𝓘(ℝ, ℂ) 𝓘(ℝ, E) (diskExtension d) (closedHalfDisk 0 (1 / 4)) z) := by
    intro z hz
    have hD := paired_fold_mfderivWithin_congr (E := E) hF₁ hz
    intro v w hvw
    apply hrank₁ z hz
    exact (congrArg (fun L : ℂ →L[ℝ] E => L v) hD).symm.trans
      (hvw.trans (congrArg (fun L : ℂ →L[ℝ] E => L w) hD))
  have hdi₂ : ∀ z ∈ closedHalfDisk 0 (1 / 4), Function.Injective
      (mfderivWithin 𝓘(ℝ, ℂ) 𝓘(ℝ, E) (diskExtension d ∘ conj)
        (closedHalfDisk 0 (1 / 4)) z) := by
    intro z hz
    have hD := paired_fold_mfderivWithin_congr (E := E) hF₂ hz
    intro v w hvw
    apply hrank₂ z hz
    exact (congrArg (fun L : ℂ →L[ℝ] E => L v) hD).symm.trans
      (hvw.trans (congrArg (fun L : ℂ →L[ℝ] E => L w) hD))
  have hzero : (0 : ℂ) ∈ closedHalfDisk 0 (1 / 4) := by
    refine ⟨(show 0 ≤ (0 : ℂ).im from le_rfl), ?_⟩
    simpa only [Metric.mem_closedBall, Complex.ofReal_zero, dist_self] using hquarter.le
  have hdfold : (inwardConormalWithin g (diskExtension d) (closedHalfDisk 0 (1 / 4)) 0 : E) +
      (tangentSpaceCast 𝓘(ℝ, E) ((diskExtension d ∘ conj) 0) (diskExtension d 0)
        (inwardConormalWithin g (diskExtension d ∘ conj) (closedHalfDisk 0 (1 / 4)) 0) : E) ≠ 0 := by
    change (fun a b : E => a + b)
      (inwardConormalWithin g (diskExtension d) (closedHalfDisk 0 (1 / 4)) 0)
      (inwardConormalWithin g (diskExtension d ∘ conj) (closedHalfDisk 0 (1 / 4)) 0) ≠ 0
    rw [paired_fold_conormal_congr g hF₁ hzero, paired_fold_conormal_congr g hF₂ hzero]
    exact hnonzero
  have hdcenter : diskExtension d 0 ∈ interior W := by
    rw [hF₁ hzero, Function.comp_apply, hcenter₁]
    exact hpW
  have hopenClosed : (openHalfDisk 0 (1 / 4) : Set ℂ) ⊆ closedHalfDisk 0 (1 / 4) :=
    fun z hz => ⟨(show 0 < z.im from hz.1).le, Metric.ball_subset_closedBall hz.2⟩
  have hψsrc : (openHalfDisk 0 (1 / 4) : Set ℂ) ⊆ ψ₁.source ∩ ψ₂.source :=
    hopenClosed.trans hHsrc
  obtain ⟨r, Y, Φ, _, hrsmall, hY, _, _, hΦ, hΦzero, hvelocity, hfix, hΦW, hnegative⟩ :=
    exists_supported_flow_of_reparametrized_nonzero_fold g d (diskExtension u) ψ₁ ψ₂
      hu.smoothInterior hu.conformal hu.harmonic hquarter
      (hd₁.of_le (by simp)) (hd₂.of_le (by simp)) hdi₁ hdi₂
      (ψ₁.contMDiffOn_toFun.mono (fun _ hz => (hψsrc hz).1))
      (ψ₂.contMDiffOn_toFun.mono (fun _ hz => (hψsrc hz).2))
      (fun _ hz => htarget₁ (ψ₁.map_source' (hψsrc hz).1))
      (fun _ hz => htarget₂ (ψ₂.map_source' (hψsrc hz).2))
      (fun _ hz => ((ψ₁.isLocalDiffeomorphAt 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) ∞ (hψsrc hz).1).mfderivToContinuousLinearEquiv
        (by simp)).bijective)
      (fun _ hz => ((ψ₂.isLocalDiffeomorphAt 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) ∞ (hψsrc hz).2).mfderivToContinuousLinearEquiv
        (by simp)).bijective)
      (hF₁.mono hopenClosed) (hF₂.mono hopenClosed) hdcenter hdfold
  have hopen : Metric.ball (0 : ℂ) r ∩ {z : ℂ | 0 < z.im} ⊆
      (openHalfDisk 0 (1 / 4) : Set ℂ) :=
    fun z hz => ⟨hz.2, (Metric.mem_ball.mp hz.1).trans_le hrsmall⟩
  have hclosedNhds (z : ℂ) (hz : z ∈ Metric.ball (0 : ℂ) r ∩ {z : ℂ | 0 < z.im}) :
      closedHalfDisk 0 (1 / 4) ∈ 𝓝 z :=
    mem_of_superset ((openHalfDisk 0 (1 / 4)).isOpen.mem_nhds (hopen hz)) hopenClosed
  have hi₁ : ∀ z ∈ Metric.ball (0 : ℂ) r ∩ {z : ℂ | 0 < z.im},
      Function.Injective (mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, E) (diskExtension d) z) := by
    intro z hz
    rw [← mfderivWithin_of_mem_nhds (hclosedNhds z hz)]
    exact hdi₁ z (mem_of_mem_nhds (hclosedNhds z hz))
  have hi₂ : ∀ z ∈ Metric.ball (0 : ℂ) r ∩ {z : ℂ | 0 < z.im},
      Function.Injective (mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, E) (diskExtension d ∘ conj) z) := by
    intro z hz
    rw [← mfderivWithin_of_mem_nhds (hclosedNhds z hz)]
    exact hdi₂ z (mem_of_mem_nhds (hclosedNhds z hz))
  obtain ⟨w, K, hwLip, hwtrace, _, hwarea⟩ :=
    exists_disk_area_lt_of_chart_fold_divergence_neg g v hvLip χ (by simp) hχsrc hχinside
      hvW Φ hΦ hΦzero Y hY hvelocity 0 r
      (by simp only [Complex.ofReal_zero, norm_zero, zero_add]; linarith)
      hfix hΦW (hd₁.mono (hopen.trans hopenClosed)) (hd₂.mono (hopen.trans hopenClosed))
      hi₁ hi₂ hnegative
  have hwJordan : DiskWeakJordanTrace γ w := by
    obtain ⟨σ, hσ, hσtrace⟩ := hu.trace
    exact ⟨σ, hσ, hwtrace.trans (hvtrace.trans hσtrace)⟩
  have hmin := hu.minimizesLipschitz w hwJordan ⟨K, hwLip⟩
  exact (not_lt_of_ge hmin) (hwarea.trans_eq hvareaeq)

end DifferentialGeometry.Geometry
