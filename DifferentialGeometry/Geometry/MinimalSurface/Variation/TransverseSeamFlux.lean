import DifferentialGeometry.Geometry.Metric.PointwiseInner.Bounds
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Topology.Algebra.Indicator
import DifferentialGeometry.Geometry.MinimalSurface.Variation.TransverseConormal
import DifferentialGeometry.Topology.Manifold.CompactCutoff
import DifferentialGeometry.Bundle.Section
import DifferentialGeometry.Bundle.TangentMap

set_option autoImplicit false
noncomputable section
open Set Filter MeasureTheory Bundle _root_.Manifold DifferentialGeometry
open DifferentialGeometry.Geometry
open DifferentialGeometry.Geometry.ImmersedDiskDivergence.Within
open DifferentialGeometry.Geometry.ImmersedDiskDivergence.HalfDisk
open scoped Topology ContDiff _root_.Manifold

namespace DifferentialGeometry.Geometry

private theorem continuous_compact_indicator_Icc
    {l r : ℝ} (hlr : l ≤ r) {f : ℝ → ℝ}
    (hf : ContinuousOn f (Icc l r)) (hl : f l = 0) (hr : f r = 0) :
    Continuous ((Icc l r).indicator f) ∧
      HasCompactSupport ((Icc l r).indicator f) := by
  classical
  constructor
  · apply continuous_indicator
    · intro s hs
      rw [frontier_Icc hlr] at hs
      rcases hs with rfl | hs
      · exact hl
      · have hsr : s = r := mem_singleton_iff.mp hs
        simpa only [hsr] using hr
    · simpa only [isClosed_Icc.closure_eq] using hf
  · change IsCompact (tsupport ((Icc l r).indicator f))
    apply (isCompact_Icc : IsCompact (Icc l r)).of_isClosed_subset (isClosed_tsupport _)
    change closure (Function.support ((Icc l r).indicator f)) ⊆ Icc l r
    apply closure_minimal ?_ isClosed_Icc
    intro s hs
    by_contra hnot
    exact hs (indicator_of_notMem hnot f)

variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]

/-- Choose the source seam patch using the uncut local field first. Every later
nonnegative target cutoff with positive center and vanishing patch endpoints
then gives strictly negative total outward flux. The factor `sqrt (g(T,T))`
is the actual seam-speed measure, shared by both inward conormals.

The indicator is source localization: target compact support does not imply
that its preimage under a possibly returning seam is compact. No individual
half-sheet sign, derivative at the seam, or strict area-decrease law is assumed. -/
theorem exists_patch_for_strict_negative_outward_seam_flux
    (g : SmoothRiemannianMetric 𝓘(ℝ, E) M) (γ : ℝ → M)
    (T Y νPlus νMinus : ∀ s, TangentSpace 𝓘(ℝ, E) (γ s))
    {s₀ R : ℝ} (hR : 0 < R)
    (hplus : ContinuousOn (fun s => g.inner (γ s) (Y s) (νPlus s))
      (Icc (s₀ - R) (s₀ + R)))
    (hminus : ContinuousOn (fun s => g.inner (γ s) (Y s) (νMinus s))
      (Icc (s₀ - R) (s₀ + R)))
    (hspeed : ContinuousOn (fun s => g.inner (γ s) (T s) (T s))
      (Icc (s₀ - R) (s₀ + R)))
    (hY : Y s₀ = νPlus s₀ + νMinus s₀)
    (hfold : νPlus s₀ + νMinus s₀ ≠ 0) (hT : T s₀ ≠ 0) :
    ∃ δ : ℝ, 0 < δ ∧ δ ≤ R ∧
      (∀ s ∈ Icc (s₀ - δ) (s₀ + δ),
        0 < g.inner (γ s) (Y s) (νPlus s + νMinus s)) ∧
      ∀ (r : ℝ), 0 < r → r ≤ δ → ∀ (b : M → ℝ),
        ContinuousOn (fun s => b (γ s)) (Icc (s₀ - r) (s₀ + r)) →
        (∀ s ∈ Icc (s₀ - r) (s₀ + r), 0 ≤ b (γ s)) →
        0 < b (γ s₀) → b (γ (s₀ - r)) = 0 → b (γ (s₀ + r)) = 0 →
        -(∫ s : ℝ, (Icc (s₀ - r) (s₀ + r)).indicator
          (fun q => Real.sqrt (g.inner (γ q) (T q) (T q)) *
            g.inner (γ q) (b (γ q) • Y q) (νPlus q)) s) -
          (∫ s : ℝ, (Icc (s₀ - r) (s₀ + r)).indicator
            (fun q => Real.sqrt (g.inner (γ q) (T q) (T q)) *
              g.inner (γ q) (b (γ q) • Y q) (νMinus q)) s) < 0 := by
  classical
  let P : ℝ → ℝ := fun s => g.inner (γ s) (Y s) (νPlus s + νMinus s)
  have hP : ContinuousOn P (Icc (s₀ - R) (s₀ + R)) := by
    have heq : P = (fun s => g.inner (γ s) (Y s) (νPlus s)) +
        (fun s => g.inner (γ s) (Y s) (νMinus s)) := by
      funext s
      change g.inner (γ s) (Y s) (νPlus s + νMinus s) =
        g.inner (γ s) (Y s) (νPlus s) + g.inner (γ s) (Y s) (νMinus s)
      exact map_add (g.inner (γ s) (Y s)) _ _
    rw [heq]
    exact hplus.add hminus
  have hP₀ : 0 < P s₀ := by
    dsimp only [P]
    rw [hY]
    exact g.pos (γ s₀) _ hfold
  have hPat : ContinuousAt P s₀ := hP.continuousAt
    (Icc_mem_nhds (by linarith : s₀ - R < s₀) (by linarith : s₀ < s₀ + R))
  obtain ⟨ε, hε, hεP⟩ := Metric.mem_nhds_iff.mp
    (hPat.preimage_mem_nhds (Ioi_mem_nhds hP₀))
  let δ : ℝ := min (R / 2) (ε / 2)
  have hδ : 0 < δ := lt_min (half_pos hR) (half_pos hε)
  have hδR : δ ≤ R := (min_le_left _ _).trans (half_le_self hR.le)
  have hδP (s : ℝ) (hs : s ∈ Icc (s₀ - δ) (s₀ + δ)) : 0 < P s := by
    apply hεP
    rw [Metric.mem_ball, Real.dist_eq]
    have hdist : |s - s₀| ≤ δ := abs_le.mpr ⟨by linarith [hs.1], by linarith [hs.2]⟩
    exact hdist.trans_lt ((min_le_right _ _).trans_lt (half_lt_self hε))
  refine ⟨δ, hδ, hδR, hδP, ?_⟩
  intro r hr hrδ b hb hbn hb₀ hbl hbr
  let S : Set ℝ := Icc (s₀ - r) (s₀ + r)
  have hSδ : S ⊆ Icc (s₀ - δ) (s₀ + δ) :=
    Icc_subset_Icc (by linarith) (by linarith)
  have hSR : S ⊆ Icc (s₀ - R) (s₀ + R) :=
    hSδ.trans (Icc_subset_Icc (by linarith) (by linarith))
  let ρ : ℝ → ℝ := fun s => Real.sqrt (g.inner (γ s) (T s) (T s))
  let FPlus : ℝ → ℝ := fun s => b (γ s) * ρ s * g.inner (γ s) (Y s) (νPlus s)
  let FMinus : ℝ → ℝ := fun s => b (γ s) * ρ s * g.inner (γ s) (Y s) (νMinus s)
  have hρ : ContinuousOn ρ S := Real.continuous_sqrt.comp_continuousOn (hspeed.mono hSR)
  have hFPlus : ContinuousOn FPlus S := (hb.mul hρ).mul (hplus.mono hSR)
  have hFMinus : ContinuousOn FMinus S := (hb.mul hρ).mul (hminus.mono hSR)
  obtain ⟨hcPlus, hkPlus⟩ := continuous_compact_indicator_Icc
    (by linarith : s₀ - r ≤ s₀ + r) hFPlus
    (by simp only [FPlus, hbl, zero_mul]) (by simp only [FPlus, hbr, zero_mul])
  obtain ⟨hcMinus, hkMinus⟩ := continuous_compact_indicator_Icc
    (by linarith : s₀ - r ≤ s₀ + r) hFMinus
    (by simp only [FMinus, hbl, zero_mul]) (by simp only [FMinus, hbr, zero_mul])
  have hiPlus : Integrable (S.indicator FPlus) := hcPlus.integrable_of_hasCompactSupport hkPlus
  have hiMinus : Integrable (S.indicator FMinus) := hcMinus.integrable_of_hasCompactSupport hkMinus
  have hsum (s : ℝ) : FPlus s + FMinus s = b (γ s) * ρ s * P s := by
    dsimp only [FPlus, FMinus, P]
    rw [map_add]
    ring
  have hsumpos : 0 < ∫ s : ℝ, S.indicator FPlus s + S.indicator FMinus s := by
    apply integral_pos_of_integrable_nonneg_nonzero (x := s₀)
      (hcPlus.add hcMinus) (hiPlus.add hiMinus)
    · intro s
      change 0 ≤ S.indicator FPlus s + S.indicator FMinus s
      by_cases hs : s ∈ S
      · rw [indicator_of_mem hs, indicator_of_mem hs, hsum]
        exact mul_nonneg (mul_nonneg (hbn s hs) (Real.sqrt_nonneg _)) (hδP s (hSδ hs)).le
      · rw [indicator_of_notMem hs, indicator_of_notMem hs]
        exact add_nonneg le_rfl le_rfl
    · change S.indicator FPlus s₀ + S.indicator FMinus s₀ ≠ 0
      have hs₀ : s₀ ∈ S := ⟨by linarith, by linarith⟩
      rw [indicator_of_mem hs₀, indicator_of_mem hs₀, hsum]
      exact ne_of_gt (mul_pos (mul_pos hb₀ (Real.sqrt_pos.mpr (g.pos (γ s₀) _ hT))) hP₀)
  have heqPlus : (fun s => S.indicator
      (fun q => Real.sqrt (g.inner (γ q) (T q) (T q)) *
        g.inner (γ q) (b (γ q) • Y q) (νPlus q)) s) = S.indicator FPlus := by
    apply congrArg (fun f : ℝ → ℝ => S.indicator f)
    funext s
    simp only [FPlus, ρ, map_smul, smul_apply, smul_eq_mul]
    ring
  have heqMinus : (fun s => S.indicator
      (fun q => Real.sqrt (g.inner (γ q) (T q) (T q)) *
        g.inner (γ q) (b (γ q) • Y q) (νMinus q)) s) = S.indicator FMinus := by
    apply congrArg (fun f : ℝ → ℝ => S.indicator f)
    funext s
    simp only [FMinus, ρ, map_smul, smul_apply, smul_eq_mul]
    ring
  change -(∫ s : ℝ, S.indicator _ s) - (∫ s : ℝ, S.indicator _ s) < 0
  rw [heqPlus, heqMinus, sub_eq_add_neg, ← neg_add, ← integral_add hiPlus hiMinus]
  exact neg_lt_zero.mpr hsumpos


private theorem uniqueDiffOn_seam_halfdisk {r : ℝ} (hr : 0 < r) :
    UniqueDiffOn ℝ (closedHalfDisk 0 r) := by
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

private theorem real_mem_seam_halfdisk {r s : ℝ} (hs : s ∈ Icc (-r) r) :
    (s : ℂ) ∈ closedHalfDisk 0 r := by
  refine ⟨?_, ?_⟩
  · exact (le_rfl : (0 : ℝ) ≤ 0)
  · simpa only [Metric.mem_closedBall, Complex.ofReal_zero, dist_zero_right,
      Complex.norm_real, Real.norm_eq_abs] using abs_le.mpr hs

private theorem seam_halfdisk_subset_buffer {r : ℝ} (hr : 0 < r) :
    closedHalfDisk 0 r ⊆ Metric.ball (0 : ℂ) (2 * r) := by
  intro z hz
  exact lt_of_le_of_lt (show dist z (0 : ℂ) ≤ r from hz.2) (by linarith)

private theorem inner_cast_seam
    (g : SmoothRiemannianMetric 𝓘(ℝ, E) M) {x y : M} (h : x = y)
    (v w : TangentSpace 𝓘(ℝ, E) y) :
    g.inner x (tangentSpaceCast 𝓘(ℝ, E) y x v)
      (tangentSpaceCast 𝓘(ℝ, E) y x w) = g.inner y v w := by
  subst y
  rfl

private theorem inner_section_cast_seam
    (g : SmoothRiemannianMetric 𝓘(ℝ, E) M) {x y : M} (h : x = y)
    (Y : ∀ p : M, TangentSpace 𝓘(ℝ, E) p) (w : TangentSpace 𝓘(ℝ, E) y) :
    g.inner x (Y x) (tangentSpaceCast 𝓘(ℝ, E) y x w) = g.inner y (Y y) w := by
  subst y
  rfl

private theorem continuousOn_seam_gram
    (g : SmoothRiemannianMetric 𝓘(ℝ, E) M) {F : ℂ → M} {H : Set ℂ}
    (hH : UniqueDiffOn ℝ H) (hF : ContMDiffOn 𝓘(ℝ, ℂ) 𝓘(ℝ, E) 1 F H) :
    ContinuousOn (fun z => gramWithin g F H z 1 1) H := by
  have hT := contMDiffOn_source_partialWithin hH hF (m := 0) (by simp) (1 : ℂ)
  have hc : ContDiffOn ℝ 0 (fun z => gramWithin g F H z 1 1) H := by
    intro z hz
    have h : ContMDiffWithinAt 𝓘(ℝ, ℂ) (𝓘(ℝ, E).prod 𝓘(ℝ, ℝ)) 0
        (fun q => TotalSpace.mk' ℝ (E := Bundle.Trivial M ℝ) (F q)
          (gramWithin g F H q 1 1)) H z := by
      apply ContMDiffWithinAt.clm_bundle_apply₂ (F₁ := E) (F₂ := E)
      · exact (g.contMDiff.contMDiffAt.of_le (by simp)).comp_contMDiffWithinAt z
          ((hF.of_le (by simp)) z hz)
      · exact hT z hz
      · exact hT z hz
    exact (contMDiffWithinAt_totalSpace.mp h).2.contDiffWithinAt
  exact hc.continuousOn

private theorem paired_seam_tangent_speed
    (g : SmoothRiemannianMetric 𝓘(ℝ, E) M) {F₁ F₂ : ℂ → M} {r : ℝ}
    (hr : 0 < r)
    (hF₁ : ContMDiffOn 𝓘(ℝ, ℂ) 𝓘(ℝ, E) ∞ F₁ (Metric.ball (0 : ℂ) (2 * r)))
    (hF₂ : ContMDiffOn 𝓘(ℝ, ℂ) 𝓘(ℝ, E) ∞ F₂ (Metric.ball (0 : ℂ) (2 * r)))
    (hseam : ∀ t ∈ Icc (-2 * r) (2 * r), F₁ (t : ℂ) = F₂ (t : ℂ)) :
    ∀ s ∈ Icc (-r) r,
      F₁ (s : ℂ) = F₂ (s : ℂ) ∧
      partialWithin F₁ (closedHalfDisk 0 r) (s : ℂ) (1 : ℂ) =
        tangentSpaceCast 𝓘(ℝ, E) (F₂ (s : ℂ)) (F₁ (s : ℂ))
          (partialWithin F₂ (closedHalfDisk 0 r) (s : ℂ) (1 : ℂ)) ∧
      Real.sqrt (gramWithin g F₁ (closedHalfDisk 0 r) (s : ℂ) 1 1) =
        Real.sqrt (gramWithin g F₂ (closedHalfDisk 0 r) (s : ℂ) 1 1) := by
  intro s hs
  let H : Set ℂ := closedHalfDisk 0 r
  have hsH : (s : ℂ) ∈ H := real_mem_seam_halfdisk hs
  have hsB := seam_halfdisk_subset_buffer hr hsH
  have hbase : F₁ (s : ℂ) = F₂ (s : ℂ) :=
    hseam s ⟨by linarith [hs.1], by linarith [hs.2]⟩
  have hdF₁ := (hF₁.contMDiffAt (Metric.isOpen_ball.mem_nhds hsB)).mdifferentiableAt
    (by simp : (∞ : WithTop ℕ∞) ≠ 0)
  have hdF₂ := (hF₂.contMDiffAt (Metric.isOpen_ball.mem_nhds hsB)).mdifferentiableAt
    (by simp : (∞ : WithTop ℕ∞) ≠ 0)
  have huniq := (uniqueDiffOn_seam_halfdisk hr).uniqueMDiffOn (s : ℂ) hsH
  have hwithin₁ : (show ℂ →L[ℝ] E from
      mfderivWithin 𝓘(ℝ, ℂ) 𝓘(ℝ, E) F₁ H (s : ℂ)) =
      (show ℂ →L[ℝ] E from mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, E) F₁ (s : ℂ)) :=
    mfderivWithin_eq_mfderiv huniq hdF₁
  have hwithin₂ : (show ℂ →L[ℝ] E from
      mfderivWithin 𝓘(ℝ, ℂ) 𝓘(ℝ, E) F₂ H (s : ℂ)) =
      (show ℂ →L[ℝ] E from mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, E) F₂ (s : ℂ)) :=
    mfderivWithin_eq_mfderiv huniq hdF₂
  have hevent : (fun t : ℝ => F₁ (t : ℂ)) =ᶠ[𝓝 s]
      (fun t : ℝ => F₂ (t : ℂ)) := by
    filter_upwards [Icc_mem_nhds (by linarith [hs.1] : -2 * r < s)
      (by linarith [hs.2] : s < 2 * r)] with t ht
    exact hseam t ht
  have hline : HasFDerivAt (fun t : ℝ => (t : ℂ)) Complex.ofRealCLM s :=
    Complex.ofRealCLM.hasFDerivAt
  have hdl := hline.hasMFDerivAt
  have he := hevent.mfderiv_eq (I := 𝓘(ℝ, ℝ)) (I' := 𝓘(ℝ, E))
  have hc₁ : HasMFDerivAt 𝓘(ℝ, ℝ) 𝓘(ℝ, E) (fun t : ℝ => F₁ (t : ℂ)) s
      ((mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, E) F₁ (s : ℂ)).comp Complex.ofRealCLM) :=
    HasMFDerivAt.comp (f := fun t : ℝ => (t : ℂ)) (g := F₁)
      s hdF₁.hasMFDerivAt hdl
  have hc₂ : HasMFDerivAt 𝓘(ℝ, ℝ) 𝓘(ℝ, E) (fun t : ℝ => F₂ (t : ℂ)) s
      ((mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, E) F₂ (s : ℂ)).comp Complex.ofRealCLM) :=
    HasMFDerivAt.comp (f := fun t : ℝ => (t : ℂ)) (g := F₂)
      s hdF₂.hasMFDerivAt hdl
  have hv := congrArg (fun L : ℝ →L[ℝ] E => L 1) he
  change (mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, E) (fun t : ℝ => F₁ (t : ℂ)) s) 1 =
    (mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, E) (fun t : ℝ => F₂ (t : ℂ)) s) 1 at hv
  have hv₁ := congrArg (fun L : ℝ →L[ℝ] E => L 1) hc₁.mfderiv
  have hv₂ := congrArg (fun L : ℝ →L[ℝ] E => L 1) hc₂.mfderiv
  change (mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, E) (fun t : ℝ => F₁ (t : ℂ)) s) 1 =
    (mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, E) F₁ (s : ℂ)) (1 : ℂ) at hv₁
  change (mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, E) (fun t : ℝ => F₂ (t : ℂ)) s) 1 =
    (mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, E) F₂ (s : ℂ)) (1 : ℂ) at hv₂
  have hfull := hv₁.symm.trans (hv.trans hv₂)
  change @Eq E
    ((show ℂ →L[ℝ] E from mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, E) F₁ (s : ℂ)) (1 : ℂ))
    ((show ℂ →L[ℝ] E from mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, E) F₂ (s : ℂ)) (1 : ℂ)) at hfull
  have ht : partialWithin F₁ H (s : ℂ) (1 : ℂ) =
      tangentSpaceCast 𝓘(ℝ, E) (F₂ (s : ℂ)) (F₁ (s : ℂ))
        (partialWithin F₂ H (s : ℂ) (1 : ℂ)) := by
    change @Eq E
      ((show ℂ →L[ℝ] E from mfderivWithin 𝓘(ℝ, ℂ) 𝓘(ℝ, E) F₁ H (s : ℂ)) (1 : ℂ))
      ((show ℂ →L[ℝ] E from mfderivWithin 𝓘(ℝ, ℂ) 𝓘(ℝ, E) F₂ H (s : ℂ)) (1 : ℂ))
    exact (congrArg (fun L : ℂ →L[ℝ] E => L (1 : ℂ)) hwithin₁).trans
      (hfull.trans (congrArg (fun L : ℂ →L[ℝ] E => L (1 : ℂ)) hwithin₂).symm)
  refine ⟨hbase, ht, congrArg Real.sqrt ?_⟩
  change g.inner (F₁ (s : ℂ)) (partialWithin F₁ H (s : ℂ) (1 : ℂ))
    (partialWithin F₁ H (s : ℂ) (1 : ℂ)) =
      g.inner (F₂ (s : ℂ)) (partialWithin F₂ H (s : ℂ) (1 : ℂ))
        (partialWithin F₂ H (s : ℂ) (1 : ℂ))
  rw [ht]
  exact inner_cast_seam g hbase _ _

variable [FiniteDimensional ℝ E] [T2Space M]

/-- One compactly supported ambient field realizes the PLUS conormal sum and
has strictly negative total outward flux on the original paired half-disks.
The literal seam parameter, both endpoint tangents and both speeds are retained. -/
theorem exists_compactSupport_vectorField_negative_paired_seam_flux
    (g : SmoothRiemannianMetric 𝓘(ℝ, E) M)
    {U : ℂ → M} {S : Set ℂ} {a b : ℂ}
    (hS : IsOpen S)
    (hU : ContMDiffOn 𝓘(ℝ, ℂ) 𝓘(ℝ, E) ∞ U S)
    (heq : U a = U b)
    (hia : Function.Injective (mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, E) U a))
    (hib : Function.Injective (mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, E) U b))
    (htrans : Function.Surjective
      ((show ℂ →L[ℝ] E from mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, E) U a).coprod
        (-(show ℂ →L[ℝ] E from mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, E) U b))))
    (hdim : Module.finrank ℝ E = 3)
    {r : ℝ} (hr : 0 < r) (ψ₁ ψ₂ : OpenPartialHomeomorph ℂ ℂ)
    (hcenter₁ : ψ₁ 0 = a) (hcenter₂ : ψ₂ 0 = b)
    (hbuffer : Metric.closedBall (0 : ℂ) (2 * r) ⊆ ψ₁.source ∩ ψ₂.source)
    (htarget₁ : ψ₁.target ⊆ S) (htarget₂ : ψ₂.target ⊆ S)
    (hψ₁sm : ContDiffOn ℝ ∞ ψ₁ ψ₁.source)
    (hψ₂sm : ContDiffOn ℝ ∞ ψ₂ ψ₂.source)
    (hψ₁bij : ∀ z ∈ ψ₁.source, Function.Bijective (fderiv ℝ ψ₁ z))
    (hψ₂bij : ∀ z ∈ ψ₂.source, Function.Bijective (fderiv ℝ ψ₂ z))
    (hseam : ∀ t ∈ Icc (-2 * r) (2 * r), U (ψ₁ (t : ℂ)) = U (ψ₂ (t : ℂ)))
    (hinj₁ : Set.InjOn (U ∘ ψ₁) (closedHalfDisk 0 r))
    (hinj₂ : Set.InjOn (U ∘ ψ₂) (closedHalfDisk 0 r))
    (himm₁ : ∀ z ∈ closedHalfDisk 0 r, Function.Injective
      (mfderivWithin 𝓘(ℝ, ℂ) 𝓘(ℝ, E) (U ∘ ψ₁) (closedHalfDisk 0 r) z))
    (himm₂ : ∀ z ∈ closedHalfDisk 0 r, Function.Injective
      (mfderivWithin 𝓘(ℝ, ℂ) 𝓘(ℝ, E) (U ∘ ψ₂) (closedHalfDisk 0 r) z)) :
    let F₁ : ℂ → M := U ∘ ψ₁
    let F₂ : ℂ → M := U ∘ ψ₂
    let H : Set ℂ := closedHalfDisk 0 r
    (∀ s ∈ Icc (-r) r,
      F₁ (s : ℂ) = F₂ (s : ℂ) ∧
      partialWithin F₁ H (s : ℂ) (1 : ℂ) =
        tangentSpaceCast 𝓘(ℝ, E) (F₂ (s : ℂ)) (F₁ (s : ℂ))
          (partialWithin F₂ H (s : ℂ) (1 : ℂ)) ∧
      Real.sqrt (gramWithin g F₁ H (s : ℂ) 1 1) =
        Real.sqrt (gramWithin g F₂ H (s : ℂ) 1 1)) ∧
    ∃ Y : ∀ x : M, TangentSpace 𝓘(ℝ, E) x,
      ContMDiff 𝓘(ℝ, E) (𝓘(ℝ, E).prod 𝓘(ℝ, E)) ∞
        (fun x => TotalSpace.mk' E x (Y x)) ∧
      HasCompactSupport Y ∧
      Y (F₁ 0) = inwardConormalWithin g F₁ H 0 +
        tangentSpaceCast 𝓘(ℝ, E) (F₂ 0) (F₁ 0) (inwardConormalWithin g F₂ H 0) ∧
      (∀ q ∈ upperClosed ∩ Metric.sphere (0 : ℂ) r, F₁ q ∉ tsupport Y) ∧
      (∀ q ∈ upperClosed ∩ Metric.sphere (0 : ℂ) r, F₂ q ∉ tsupport Y) ∧
      ((∫ s : ℝ, (Icc (-r) r).indicator
          (fun s => Real.sqrt (gramWithin g F₁ H (s : ℂ) 1 1) *
            g.inner (F₁ (s : ℂ)) (Y (F₁ (s : ℂ)))
              (-inwardConormalWithin g F₁ H (s : ℂ))) s) +
        (∫ s : ℝ, (Icc (-r) r).indicator
          (fun s => Real.sqrt (gramWithin g F₂ H (s : ℂ) 1 1) *
            g.inner (F₂ (s : ℂ)) (Y (F₂ (s : ℂ)))
              (-inwardConormalWithin g F₂ H (s : ℂ))) s)) < 0 := by
  classical
  have : FiniteDimensional ℝ ℂ := Complex.basisOneI.finiteDimensional_of_finite
  let F₁ : ℂ → M := U ∘ ψ₁
  let F₂ : ℂ → M := U ∘ ψ₂
  let H : Set ℂ := closedHalfDisk 0 r
  let J : Set ℝ := Icc (-r) r
  have hF₁ : ContMDiffOn 𝓘(ℝ, ℂ) 𝓘(ℝ, E) ∞ F₁
      (Metric.ball (0 : ℂ) (2 * r)) :=
    (hU.comp hψ₁sm.contMDiffOn (fun z hz => htarget₁ (ψ₁.map_source hz))).mono
      (fun _ hz => (hbuffer (Metric.ball_subset_closedBall hz)).1)
  have hF₂ : ContMDiffOn 𝓘(ℝ, ℂ) 𝓘(ℝ, E) ∞ F₂
      (Metric.ball (0 : ℂ) (2 * r)) :=
    (hU.comp hψ₂sm.contMDiffOn (fun z hz => htarget₂ (ψ₂.map_source hz))).mono
      (fun _ hz => (hbuffer (Metric.ball_subset_closedBall hz)).2)
  have hFH₁ : ContMDiffOn 𝓘(ℝ, ℂ) 𝓘(ℝ, E) 1 F₁ H :=
    (hF₁.mono (seam_halfdisk_subset_buffer hr)).of_le (by simp)
  have hFH₂ : ContMDiffOn 𝓘(ℝ, ℂ) 𝓘(ℝ, E) 1 F₂ H :=
    (hF₂.mono (seam_halfdisk_subset_buffer hr)).of_le (by simp)
  have hreal : MapsTo (fun s : ℝ => (s : ℂ)) J H :=
    fun _ hs => real_mem_seam_halfdisk hs
  have hzeroJ : (0 : ℝ) ∈ J := ⟨by linarith, hr.le⟩
  have hzeroH : (0 : ℂ) ∈ H := by
    simpa only [Complex.ofReal_zero] using hreal hzeroJ
  have huniq : UniqueDiffOn ℝ H := uniqueDiffOn_seam_halfdisk hr
  have hall := paired_seam_tangent_speed g hr hF₁ hF₂ hseam
  obtain ⟨hbase, _, hT₀, _, _, _, hfold, _⟩ :=
    paired_halfdisk_inward_conormals_ne_zero_of_transverse g hS hU heq hia hib
      htrans hdim hr ψ₁ ψ₂ hcenter₁ hcenter₂ hbuffer htarget₁ htarget₂
      hψ₁sm hψ₂sm hψ₁bij hψ₂bij hseam
  -- The uncut field is chosen before the smaller scalar positivity interval.
  obtain ⟨Y₀, hY₀center⟩ :=
    ContMDiffSection.exists_eq_at (I := 𝓘(ℝ, E)) (F := E)
      (V := TangentSpace 𝓘(ℝ, E)) (n := (⊤ : ℕ∞)) (F₁ 0)
      (inwardConormalWithin g F₁ H 0 +
        tangentSpaceCast 𝓘(ℝ, E) (F₂ 0) (F₁ 0) (inwardConormalWithin g F₂ H 0))
  have hY₀ : ContMDiff 𝓘(ℝ, E) (𝓘(ℝ, E).prod 𝓘(ℝ, E)) ∞
      (fun x => TotalSpace.mk' E x (Y₀ x)) := Y₀.contMDiff
  let γ₀ : ℝ → M := fun s => F₁ (s : ℂ)
  let T : ∀ s, TangentSpace 𝓘(ℝ, E) (γ₀ s) :=
    fun s => partialWithin F₁ H (s : ℂ) (1 : ℂ)
  let νPlus : ∀ s, TangentSpace 𝓘(ℝ, E) (γ₀ s) :=
    fun s => inwardConormalWithin g F₁ H (s : ℂ)
  let νMinus : ∀ s, TangentSpace 𝓘(ℝ, E) (γ₀ s) := fun s =>
    if s ∈ J then tangentSpaceCast 𝓘(ℝ, E) (F₂ (s : ℂ)) (F₁ (s : ℂ))
      (inwardConormalWithin g F₂ H (s : ℂ)) else 0
  have hplus : ContinuousOn (fun s => g.inner (γ₀ s) (Y₀ (γ₀ s)) (νPlus s)) J :=
    (continuousOn_inner_inwardConormalWithin g F₁ huniq.uniqueMDiffOn hFH₁ himm₁
      (fun x => Y₀ x) hY₀).comp Complex.continuous_ofReal.continuousOn hreal
  have hminus : ContinuousOn (fun s => g.inner (γ₀ s) (Y₀ (γ₀ s)) (νMinus s)) J := by
    apply ((continuousOn_inner_inwardConormalWithin g F₂ huniq.uniqueMDiffOn hFH₂ himm₂
      (fun x => Y₀ x) hY₀).comp Complex.continuous_ofReal.continuousOn hreal).congr
    intro s hs
    change g.inner (F₁ (s : ℂ)) (Y₀ (F₁ (s : ℂ))) (νMinus s) =
      g.inner (F₂ (s : ℂ)) (Y₀ (F₂ (s : ℂ))) (inwardConormalWithin g F₂ H (s : ℂ))
    rw [show νMinus s = tangentSpaceCast 𝓘(ℝ, E) (F₂ (s : ℂ)) (F₁ (s : ℂ))
      (inwardConormalWithin g F₂ H (s : ℂ)) from ite_eq_left hs]
    exact inner_section_cast_seam g (hall s hs).1 (fun x => Y₀ x) _
  have hspeed : ContinuousOn (fun s => g.inner (γ₀ s) (T s) (T s)) J :=
    (continuousOn_seam_gram g huniq hFH₁).comp Complex.continuous_ofReal.continuousOn hreal
  have hcenter : Y₀ (γ₀ 0) = νPlus 0 + νMinus 0 := by
    simpa only [γ₀, νPlus, νMinus, ite_eq_left hzeroJ, Complex.ofReal_zero] using hY₀center
  have hfold₀ : νPlus 0 + νMinus 0 ≠ 0 := by
    simpa only [νPlus, νMinus, ite_eq_left hzeroJ, Complex.ofReal_zero] using hfold
  have hT : T 0 ≠ 0 := by
    change @Ne E
      ((show ℂ →L[ℝ] E from mfderivWithin 𝓘(ℝ, ℂ) 𝓘(ℝ, E) F₁ H 0) (1 : ℂ))
      (0 : E)
    exact hT₀
  obtain ⟨δ, hδ, hδr, _, hsmall⟩ :=
    exists_patch_for_strict_negative_outward_seam_flux g γ₀ T (fun s => Y₀ (γ₀ s))
      νPlus νMinus (s₀ := 0) hr
      (by simpa only [zero_sub, zero_add] using hplus)
      (by simpa only [zero_sub, zero_add] using hminus)
      (by simpa only [zero_sub, zero_add] using hspeed) hcenter hfold₀ hT
  let ρ : ℝ := δ / 2
  have hρ : 0 < ρ := half_pos hδ
  have hρδ : ρ ≤ δ := half_le_self hδ.le
  have hρr : ρ ≤ r := hρδ.trans hδr
  let K : Set ℝ := Icc (-ρ) ρ
  have hKJ : K ⊆ J := Icc_subset_Icc (neg_le_neg hρr) hρr
  -- Both curved edges and every remaining real-seam point are excluded.
  let A : Set ℂ := (upperClosed ∩ Metric.sphere (0 : ℂ) r) ∪
    (fun s : ℝ => (s : ℂ)) '' (Icc (-r) (-ρ) ∪ Icc ρ r)
  have hAc : IsCompact A :=
    ((isCompact_sphere (0 : ℂ) r).inter_left
      (isClosed_le continuous_const Complex.continuous_im)).union
      ((isCompact_Icc.union isCompact_Icc).image Complex.continuous_ofReal)
  have hAH : A ⊆ H := by
    intro z hz
    rcases hz with hz | ⟨s, hs, rfl⟩
    · exact ⟨hz.1, (show dist z (0 : ℂ) = r from hz.2).le⟩
    · apply real_mem_seam_halfdisk
      rcases hs with hs | hs
      · exact ⟨hs.1, hs.2.trans (by linarith)⟩
      · exact ⟨(by linarith : -r ≤ ρ).trans hs.1, hs.2⟩
  have hzeroA : (0 : ℂ) ∉ A := by
    intro hz
    rcases hz with hz | ⟨s, hs, hs0⟩
    · have he : (0 : ℝ) = r := by simpa only [Metric.mem_sphere, dist_self] using hz.2
      linarith
    · have hs0r : s = 0 := Complex.ofReal_injective (by simpa only [Complex.ofReal_zero] using hs0)
      subst s
      rcases hs with hs | hs <;> linarith [hs.1, hs.2]
  let B : Set M := F₁ '' A ∪ F₂ '' A
  have hBc : IsCompact B :=
    (hAc.image_of_continuousOn (hFH₁.continuousOn.mono hAH)).union
      (hAc.image_of_continuousOn (hFH₂.continuousOn.mono hAH))
  have hpB : F₁ 0 ∉ B := by
    intro hp
    rcases hp with ⟨z, hz, he⟩ | ⟨z, hz, he⟩
    · exact hzeroA ((hinj₁ (hAH hz) hzeroH he) ▸ hz)
    · exact hzeroA ((hinj₂ (hAH hz) hzeroH (he.trans hbase)) ▸ hz)
  let O : Set M := Bᶜ
  have hO : IsOpen O := hBc.isClosed.isOpen_compl
  have hpO : ({F₁ 0} : Set M) ⊆ O := by
    intro p hp
    rcases Set.mem_singleton_iff.mp hp with rfl
    exact hpB
  obtain ⟨β, hβ, hβc, hβO, hβrange, hβone⟩ :=
    DifferentialGeometry.Topology.exists_contMDiff_cutoff_of_isCompact
      (I := 𝓘(ℝ, E)) isCompact_singleton hO hpO
  have hβp : β (F₁ 0) = 1 := by
    have he : β =ᶠ[𝓝 (F₁ 0)] (1 : M → ℝ) := by
      simpa only [nhdsSet_singleton] using hβone
    exact he.self_of_nhds
  have hβzero : ∀ p ∈ B, β p = 0 := by
    intro p hp
    exact image_eq_zero_of_notMem_tsupport (fun hpt => (hβO hpt) hp)
  let Y : ∀ x : M, TangentSpace 𝓘(ℝ, E) x := fun x => β x • Y₀ x
  have hY : ContMDiff 𝓘(ℝ, E) (𝓘(ℝ, E).prod 𝓘(ℝ, E)) ∞
      (fun x => TotalSpace.mk' E x (Y x)) := hβ.smul_section hY₀
  have hYs : tsupport Y ⊆ tsupport β := tsupport_smul_subset_left β (fun x => Y₀ x)
  have hYc : HasCompactSupport Y := hβc.of_isClosed_subset (isClosed_tsupport Y) hYs
  have hYcenter : Y (F₁ 0) = inwardConormalWithin g F₁ H 0 +
      tangentSpaceCast 𝓘(ℝ, E) (F₂ 0) (F₁ 0) (inwardConormalWithin g F₂ H 0) := by
    change β (F₁ 0) • Y₀ (F₁ 0) = _
    rw [hβp, one_smul]
    exact hY₀center
  have havoid₁ : ∀ q ∈ upperClosed ∩ Metric.sphere (0 : ℂ) r, F₁ q ∉ tsupport Y := by
    intro q hq hqY
    exact (hβO (hYs hqY)) (Or.inl ⟨q, Or.inl hq, rfl⟩)
  have havoid₂ : ∀ q ∈ upperClosed ∩ Metric.sphere (0 : ℂ) r, F₂ q ∉ tsupport Y := by
    intro q hq hqY
    exact (hβO (hYs hqY)) (Or.inr ⟨q, Or.inl hq, rfl⟩)
  have houter₁ : ∀ s ∈ Icc (-r) (-ρ) ∪ Icc ρ r, β (F₁ (s : ℂ)) = 0 := by
    intro s hs
    exact hβzero _ (Or.inl ⟨(s : ℂ), Or.inr ⟨s, hs, rfl⟩, rfl⟩)
  have houter₂ : ∀ s ∈ Icc (-r) (-ρ) ∪ Icc ρ r, β (F₂ (s : ℂ)) = 0 := by
    intro s hs
    exact hβzero _ (Or.inr ⟨(s : ℂ), Or.inr ⟨s, hs, rfl⟩, rfl⟩)
  have hγc : ContinuousOn γ₀ J :=
    hFH₁.continuousOn.comp Complex.continuous_ofReal.continuousOn hreal
  have hβK : ContinuousOn (fun s => β (γ₀ s)) K :=
    hβ.continuous.comp_continuousOn (hγc.mono hKJ)
  have hβleft : β (γ₀ (-ρ)) = 0 :=
    houter₁ _ (Or.inl ⟨neg_le_neg hρr, le_rfl⟩)
  have hβright : β (γ₀ ρ) = 0 := houter₁ _ (Or.inr ⟨le_rfl, hρr⟩)
  have hnegative := hsmall ρ hρ hρδ β
    (by simpa only [zero_sub, zero_add] using hβK)
    (fun s _ => (hβrange (γ₀ s)).1)
    (by simpa only [γ₀, Complex.ofReal_zero, hβp] using (zero_lt_one : (0 : ℝ) < 1))
    (by simpa only [zero_sub] using hβleft)
    (by simpa only [zero_add] using hβright)
  let PPlus : ℝ → ℝ := fun s => Real.sqrt (g.inner (γ₀ s) (T s) (T s)) *
    g.inner (γ₀ s) (β (γ₀ s) • Y₀ (γ₀ s)) (νPlus s)
  let PMinus : ℝ → ℝ := fun s => Real.sqrt (g.inner (γ₀ s) (T s) (T s)) *
    g.inner (γ₀ s) (β (γ₀ s) • Y₀ (γ₀ s)) (νMinus s)
  have hnegative' : -(∫ s : ℝ, K.indicator PPlus s) -
      (∫ s : ℝ, K.indicator PMinus s) < 0 := by
    simpa only [zero_sub, zero_add] using hnegative
  have houter (s : ℝ) (hs : s ∈ J) (hn : s ∉ K) :
      s ∈ Icc (-r) (-ρ) ∪ Icc ρ r := by
    by_cases hleft : s < -ρ
    · exact Or.inl ⟨hs.1, hleft.le⟩
    · exact Or.inr ⟨le_of_lt (lt_of_not_ge (fun h => hn ⟨le_of_not_gt hleft, h⟩)), hs.2⟩
  have hflux₁ : (fun s : ℝ => J.indicator
      (fun s => Real.sqrt (gramWithin g F₁ H (s : ℂ) 1 1) *
        g.inner (F₁ (s : ℂ)) (Y (F₁ (s : ℂ)))
          (-inwardConormalWithin g F₁ H (s : ℂ))) s) =
      fun s => -(K.indicator PPlus s) := by
    funext s
    by_cases hs : s ∈ K
    · rw [indicator_of_mem (hKJ hs), indicator_of_mem hs]
      simp only [PPlus, γ₀, T, νPlus, Y, gramWithin, map_neg, mul_neg]
    · rw [indicator_of_notMem hs, neg_zero]
      by_cases hsJ : s ∈ J
      · rw [indicator_of_mem hsJ]
        have hz : Y (F₁ (s : ℂ)) = 0 := by
          change β (F₁ (s : ℂ)) • Y₀ (F₁ (s : ℂ)) = 0
          rw [houter₁ s (houter s hsJ hs), zero_smul]
        rw [hz, map_zero]
        exact mul_zero _
      · exact indicator_of_notMem hsJ _
  have hflux₂ : (fun s : ℝ => J.indicator
      (fun s => Real.sqrt (gramWithin g F₂ H (s : ℂ) 1 1) *
        g.inner (F₂ (s : ℂ)) (Y (F₂ (s : ℂ)))
          (-inwardConormalWithin g F₂ H (s : ℂ))) s) =
      fun s => -(K.indicator PMinus s) := by
    funext s
    by_cases hs : s ∈ K
    · have hsJ := hKJ hs
      rw [indicator_of_mem hsJ, indicator_of_mem hs]
      have hpair : g.inner (γ₀ s) (Y (γ₀ s)) (νMinus s) =
          g.inner (F₂ (s : ℂ)) (Y (F₂ (s : ℂ)))
            (inwardConormalWithin g F₂ H (s : ℂ)) := by
        change g.inner (F₁ (s : ℂ)) (Y (F₁ (s : ℂ))) (νMinus s) = _
        rw [show νMinus s = tangentSpaceCast 𝓘(ℝ, E) (F₂ (s : ℂ)) (F₁ (s : ℂ))
          (inwardConormalWithin g F₂ H (s : ℂ)) from ite_eq_left hsJ]
        exact inner_section_cast_seam g (hall s hsJ).1 Y _
      change Real.sqrt (gramWithin g F₂ H (s : ℂ) 1 1) *
        g.inner (F₂ (s : ℂ)) (Y (F₂ (s : ℂ)))
          (-inwardConormalWithin g F₂ H (s : ℂ)) = -PMinus s
      have hpm : PMinus s = Real.sqrt (gramWithin g F₁ H (s : ℂ) 1 1) *
          g.inner (F₂ (s : ℂ)) (Y (F₂ (s : ℂ)))
            (inwardConormalWithin g F₂ H (s : ℂ)) :=
        congrArg (fun t : ℝ => Real.sqrt (gramWithin g F₁ H (s : ℂ) 1 1) * t) hpair
      rw [hpm, (hall s hsJ).2.2, map_neg, mul_neg]
    · rw [indicator_of_notMem hs, neg_zero]
      by_cases hsJ : s ∈ J
      · rw [indicator_of_mem hsJ]
        have hz : Y (F₂ (s : ℂ)) = 0 := by
          change β (F₂ (s : ℂ)) • Y₀ (F₂ (s : ℂ)) = 0
          rw [houter₂ s (houter s hsJ hs), zero_smul]
        rw [hz, map_zero]
        exact mul_zero _
      · exact indicator_of_notMem hsJ _
  refine ⟨hall, Y, hY, hYc, hYcenter, havoid₁, havoid₂, ?_⟩
  change (∫ s : ℝ, J.indicator _ s) + (∫ s : ℝ, J.indicator _ s) < 0
  rw [hflux₁, hflux₂, integral_neg, integral_neg]
  simpa only [sub_eq_add_neg] using hnegative'

end DifferentialGeometry.Geometry
