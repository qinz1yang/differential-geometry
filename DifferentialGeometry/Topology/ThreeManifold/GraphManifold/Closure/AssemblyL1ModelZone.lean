import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.AssemblyL1ModelSphere

/-!
# Chapter-14 assembly, item L1, group G3a: the handle zone map of the model cycle

The `k`-th handle of the model and its two necks are restrictions of one map
`zoneChartMap ε c = zoneMap ε c ∘ zoneLift` of `ℝ² × ℝ` (`c = 4k`):
`zoneLift (z, t) = (z, zoneHeight ‖z‖ t)` lifts the handle parameter `t` to the height, and
`zoneMap ε c (z, u) = (zoneRatio ε ‖z‖ u • z, c + u)` is fibrewise radial. On the zone domain
`{‖z‖ < 13/10, -1/4 < t < 5/4}` it is smooth, injective, with injective differential; near `t = 0`
it is the neck of the lower end (`zoneChartMap_neck`), near `t = 1` the flipped neck of the upper end
(`zoneChartMap_neck_flip`).
-/

set_option autoImplicit false

noncomputable section

open Set Function
open scoped ContDiff Topology Manifold

namespace GC.GraphManifold.Assembly

variable {ε : ℝ}

/-- The zone domain. -/
def zoneDomain : Set ModelSpace := {y | ‖y.1‖ < 13 / 10 ∧ -1 / 4 < y.2 ∧ y.2 < 5 / 4}

theorem isOpen_zoneDomain : IsOpen zoneDomain :=
  (isOpen_lt (continuous_norm.comp continuous_fst) continuous_const).inter
    ((isOpen_lt continuous_const continuous_snd).inter (isOpen_lt continuous_snd continuous_const))

/-- The lift of the handle parameter to the height. -/
def zoneLift : ModelSpace → ModelSpace := modelGraphMap fun y => zoneHeightSq (‖y.1‖ ^ 2) y.2

/-- The fibrewise radial part of the zone map. -/
def zoneMap (ε c : ℝ) : ModelSpace → ModelSpace :=
  modelRadialMap (fun y => zoneRatioSq ε (‖y.1‖ ^ 2) y.2) c 1

/-- **The zone map.** -/
def zoneChartMap (ε c : ℝ) (y : ModelSpace) : ModelSpace := zoneMap ε c (zoneLift y)

theorem zoneLift_apply (y : ModelSpace) : zoneLift y = (y.1, zoneHeight ‖y.1‖ y.2) := rfl

theorem zoneChartMap_apply (ε c : ℝ) (y : ModelSpace) :
    zoneChartMap ε c y = (zoneRatio ε ‖y.1‖ (zoneHeight ‖y.1‖ y.2) • y.1,
      c + zoneHeight ‖y.1‖ y.2) := by
  simp only [zoneChartMap, zoneMap, modelRadialMap, zoneLift, modelGraphMap, one_mul]
  rw [zoneRatioSq_sq (norm_nonneg _), zoneHeightSq_sq]

theorem capCos_gt_of_lt {s : ℝ} (hs : 0 ≤ s) (hs' : s < 13 / 10) : 2 / 5 < capCos s := by
  have h := capCos_lt_capCos hs hs'
  have h2 : capCos (13 / 10) = 231 / 569 := by norm_num [capCos]
  rw [h2] at h
  linarith

theorem zoneHeight_mem {s t : ℝ} (hs : 0 ≤ s) (hs' : s < 13 / 10) (ht : -1 / 4 < t)
    (ht' : t < 5 / 4) : 3 / 10 < zoneHeight s t ∧ zoneHeight s t < 37 / 10 := by
  have hq := capCos_gt_of_lt hs hs'
  have hq1 := capCos_le_one s
  have habs : |s| < 2 := by rw [abs_of_nonneg hs]; linarith
  have h1 := zoneHeight_lt habs ht
  have h2 := zoneHeight_lt habs ht'
  rw [zoneHeight_of_le (s := s) (t := -1 / 4) (by norm_num)] at h1
  rw [zoneHeight_of_ge (s := s) (t := 5 / 4) (by norm_num)] at h2
  constructor <;> nlinarith

theorem zoneRatio_pos (hε : 0 < ε) (hε' : ε ≤ 1 / 8) {s u : ℝ} (hs : 0 ≤ s) (hs' : s < 13 / 10)
    (hu : 3 / 10 < u) (hu' : u < 37 / 10) : 0 < zoneRatio ε s u := by
  have hq := capCos_gt_of_lt hs hs'
  have hq1 := capCos_le_one s
  have hq0 : 0 < capCos s := by linarith
  have h1 : 1 / 4 ≤ 1 + (u / capCos s - 1) := by
    rw [add_sub_cancel, le_div_iff₀ hq0]
    nlinarith
  have h2 : 1 / 4 ≤ 1 + ((4 - u) / capCos s - 1) := by
    rw [add_sub_cancel, le_div_iff₀ hq0]
    nlinarith
  exact mul_pos (neckRatio_pos hε hε' h1) (neckRatio_pos hε hε' h2)

theorem norm_zoneChartMap_fst (hε : 0 < ε) (hε' : ε ≤ 1 / 8) (c : ℝ) {y : ModelSpace}
    (hy : y ∈ zoneDomain) :
    ‖(zoneChartMap ε c y).1‖ = zoneRadius ε ‖y.1‖ (zoneHeight ‖y.1‖ y.2) := by
  obtain ⟨h1, h2, h3⟩ := hy
  have hU := zoneHeight_mem (norm_nonneg y.1) h1 h2 h3
  rw [zoneChartMap_apply, norm_smul, Real.norm_of_nonneg
    (zoneRatio_pos hε hε' (norm_nonneg _) h1 hU.1 hU.2).le, zoneRadius, mul_comm]

/-! ## Injectivity -/

theorem zoneChartMap_injOn (hε : 0 < ε) (hε' : ε ≤ 1 / 8) (c : ℝ) :
    InjOn (zoneChartMap ε c) zoneDomain := by
  intro y hy y' hy' h
  have hU := zoneHeight_mem (norm_nonneg y.1) hy.1 hy.2.1 hy.2.2
  have hU' := zoneHeight_mem (norm_nonneg y'.1) hy'.1 hy'.2.1 hy'.2.2
  rw [zoneChartMap_apply, zoneChartMap_apply, Prod.mk.injEq] at h
  obtain ⟨hw, hv⟩ := h
  have hu : zoneHeight ‖y.1‖ y.2 = zoneHeight ‖y'.1‖ y'.2 := by linarith
  -- equal radii
  have hrad : zoneRadius ε ‖y.1‖ (zoneHeight ‖y.1‖ y.2) =
      zoneRadius ε ‖y'.1‖ (zoneHeight ‖y.1‖ y.2) := by
    have := congrArg norm hw
    rw [norm_smul, norm_smul, Real.norm_of_nonneg
      (zoneRatio_pos hε hε' (norm_nonneg _) hy.1 hU.1 hU.2).le, Real.norm_of_nonneg
      (zoneRatio_pos hε hε' (norm_nonneg _) hy'.1 hU'.1 hU'.2).le, ← hu] at this
    rw [zoneRadius, zoneRadius, mul_comm, this, mul_comm]
  have hs : ‖y.1‖ = ‖y'.1‖ := by
    rcases lt_trichotomy ‖y.1‖ ‖y'.1‖ with hlt | heq | hgt
    · exact absurd hrad (zoneRadius_lt hε hε' (norm_nonneg _) hlt (by linarith [hy'.1])
        (by linarith [hU.1]) (by linarith [hU.2])).ne
    · exact heq
    · exact absurd hrad (zoneRadius_lt hε hε' (norm_nonneg _) hgt (by linarith [hy.1])
        (by linarith [hU.1]) (by linarith [hU.2])).ne'
  rw [← hu, ← hs] at hw
  have hz : y.1 = y'.1 :=
    smul_right_injective _ (zoneRatio_pos hε hε' (norm_nonneg _) hy.1 hU.1 hU.2).ne' hw
  rw [hs] at hu
  have ht : y.2 = y'.2 :=
    (zoneHeight_strictMono (s := ‖y'.1‖) (by rw [abs_of_nonneg (norm_nonneg _)]; linarith [hy'.1])
      ).injective hu
  exact Prod.ext hz ht

/-! ## Smoothness -/

theorem contDiff_zoneLift : ContDiff ℝ ∞ zoneLift := by
  have hφ : ContDiff ℝ ∞ (fun y : ModelSpace => zoneHeightSq (‖y.1‖ ^ 2) y.2) := by
    rw [contDiff_iff_contDiffAt]
    intro y
    have hσ : ‖y.1‖ ^ 2 ≠ -4 := by
      have := sq_nonneg ‖y.1‖
      intro h
      linarith
    have hin : ContDiffAt ℝ ∞ (fun y : ModelSpace => (‖y.1‖ ^ 2, y.2)) y :=
      (((contDiff_norm_sq ℝ).comp contDiff_fst).prodMk contDiff_snd).contDiffAt
    exact (contDiffAt_zoneHeightSq hσ).comp y hin
  exact contDiff_fst.prodMk hφ

theorem contDiffAt_zoneRatioSq (hε : 0 < ε) (hε' : ε ≤ 1 / 8) {σ u : ℝ} (hσ : 0 ≤ σ)
    (hσ' : σ < 4) (hu : 3 / 10 < u) (hu' : u < 37 / 10) :
    ContDiffAt ℝ ∞ (fun p : ℝ × ℝ => zoneRatioSq ε p.1 p.2) (σ, u) := by
  have hq0 : 0 < capCosSq σ := div_pos (by linarith) (by linarith)
  have hq1 : capCosSq σ ≤ 1 := by
    rw [capCosSq, div_le_one (by linarith)]
    linarith
  have hσ4 : σ ≠ -4 := by intro h; linarith
  have hq : ContDiffAt ℝ ∞ (fun p : ℝ × ℝ => capCosSq p.1) (σ, u) :=
    ContDiffAt.comp (g := capCosSq) (σ, u) (contDiffAt_capCosSq hσ4) contDiffAt_fst
  have hτ1 : ε / 4 < 1 + (u / capCosSq σ - 1) := by
    rw [add_sub_cancel]
    have : u ≤ u / capCosSq σ := by
      rw [le_div_iff₀ hq0]
      nlinarith
    linarith
  have hτ2 : ε / 4 < 1 + ((4 - u) / capCosSq σ - 1) := by
    rw [add_sub_cancel]
    have : 4 - u ≤ (4 - u) / capCosSq σ := by
      rw [le_div_iff₀ hq0]
      nlinarith
    linarith
  have hin1 : ContDiffAt ℝ ∞ (fun p : ℝ × ℝ => (p.1, p.2 / capCosSq p.1 - 1)) (σ, u) :=
    contDiffAt_fst.prodMk ((contDiffAt_snd.fun_div hq hq0.ne').sub contDiffAt_const)
  have hin2 : ContDiffAt ℝ ∞ (fun p : ℝ × ℝ => (p.1, (4 - p.2) / capCosSq p.1 - 1)) (σ, u) :=
    contDiffAt_fst.prodMk (((contDiffAt_const.sub contDiffAt_snd).fun_div hq hq0.ne').sub
      contDiffAt_const)
  have hout1 := contDiffAt_neckRatioSq (σ := σ) hε hτ1
  have hout2 := contDiffAt_neckRatioSq (σ := σ) hε hτ2
  have h1 : ContDiffAt ℝ ∞ (fun p : ℝ × ℝ => neckRatioSq ε p.1 (p.2 / capCosSq p.1 - 1)) (σ, u) :=
    ContDiffAt.comp (g := fun p : ℝ × ℝ => neckRatioSq ε p.1 p.2)
      (f := fun p : ℝ × ℝ => (p.1, p.2 / capCosSq p.1 - 1)) (σ, u) hout1 hin1
  have h2 : ContDiffAt ℝ ∞ (fun p : ℝ × ℝ => neckRatioSq ε p.1 ((4 - p.2) / capCosSq p.1 - 1))
      (σ, u) :=
    ContDiffAt.comp (g := fun p : ℝ × ℝ => neckRatioSq ε p.1 p.2)
      (f := fun p : ℝ × ℝ => (p.1, (4 - p.2) / capCosSq p.1 - 1)) (σ, u) hout2 hin2
  have hfun : (fun p : ℝ × ℝ => zoneRatioSq ε p.1 p.2) = fun p : ℝ × ℝ =>
      neckRatioSq ε p.1 (p.2 / capCosSq p.1 - 1) * neckRatioSq ε p.1 ((4 - p.2) / capCosSq p.1 - 1) :=
    rfl
  rw [hfun]
  exact h1.mul h2

theorem contDiffAt_zoneMap (hε : 0 < ε) (hε' : ε ≤ 1 / 8) (c : ℝ) {p : ModelSpace}
    (hp : ‖p.1‖ < 13 / 10) (hu : 3 / 10 < p.2) (hu' : p.2 < 37 / 10) :
    ContDiffAt ℝ ∞ (zoneMap ε c) p := by
  have hσ' : ‖p.1‖ ^ 2 < 4 := by
    have := norm_nonneg p.1
    nlinarith
  have hm : ContDiffAt ℝ ∞ (fun y : ModelSpace => zoneRatioSq ε (‖y.1‖ ^ 2) y.2) p :=
    ContDiffAt.comp (g := fun q : ℝ × ℝ => zoneRatioSq ε q.1 q.2)
      (f := fun y : ModelSpace => (‖y.1‖ ^ 2, y.2)) p
      (contDiffAt_zoneRatioSq hε hε' (sq_nonneg _) hσ' hu hu')
      ((((contDiff_norm_sq ℝ).comp contDiff_fst).prodMk contDiff_snd).contDiffAt)
  exact (hm.smul contDiffAt_fst).prodMk (contDiffAt_const.add (contDiffAt_const.mul contDiffAt_snd))

theorem contDiffOn_zoneChartMap (hε : 0 < ε) (hε' : ε ≤ 1 / 8) (c : ℝ) :
    ContDiffOn ℝ ∞ (zoneChartMap ε c) zoneDomain := by
  intro y hy
  have hU := zoneHeight_mem (norm_nonneg y.1) hy.1 hy.2.1 hy.2.2
  have h := (contDiffAt_zoneMap hε hε' c (p := zoneLift y) hy.1 hU.1 hU.2).comp y
    contDiff_zoneLift.contDiffAt
  exact h.contDiffWithinAt

/-! ## The differential -/

theorem injective_fderiv_zoneLift (y : ModelSpace) (hy : ‖y.1‖ < 2) :
    Injective (fderiv ℝ zoneLift y) := by
  have hφd : DifferentiableAt ℝ (fun y : ModelSpace => zoneHeightSq (‖y.1‖ ^ 2) y.2) y :=
    ((contDiff_zoneLift.snd).differentiable (by simp)) y
  apply injective_fderiv_modelGraphMap hφd.hasFDerivAt
  have hline : HasDerivAt (fun t : ℝ => ((y.1, t) : ModelSpace)) ((0, 1) : ModelSpace) y.2 :=
    (hasDerivAt_const y.2 y.1).prodMk (hasDerivAt_id y.2)
  have hcomp := hφd.hasFDerivAt.comp_hasDerivAt y.2 hline
  have h2 : HasDerivAt (fun t : ℝ => zoneHeightSq (‖y.1‖ ^ 2) t)
      (capCos ‖y.1‖ + deriv zoneBlend y.2 * (4 - 3 * capCos ‖y.1‖)) y.2 := by
    have := hasDerivAt_zoneHeight ‖y.1‖ y.2
    exact this
  have heq := hcomp.unique h2
  rw [heq]
  exact (deriv_zoneHeight_pos (by rw [abs_of_nonneg (norm_nonneg _)]; exact hy)).ne'

/-- The radial derivative of the zone map is positive. -/
theorem exists_hasDerivAt_zoneRatio (hε : 0 < ε) (hε' : ε ≤ 1 / 8) {z : ModelPlane} (hz : z ≠ 0)
    (hz' : ‖z‖ < 13 / 10) {u : ℝ} (hu : 3 / 10 < u) (hu' : u < 37 / 10) :
    ∃ d, d ≠ 0 ∧ HasDerivAt (fun t : ℝ => t * zoneRatioSq ε (‖t • z‖ ^ 2) u) d 1 := by
  set s := ‖z‖ with hs
  have hspos : 0 < s := norm_pos_iff.mpr hz
  have hevgen : ∀ (g : ℝ → ℝ), (∀ s' : ℝ, 0 < s' → s' ≤ 3 / 2 → zoneRadius ε s' u = g s') →
      (fun t : ℝ => t * zoneRatioSq ε (‖t • z‖ ^ 2) u) =ᶠ[𝓝 1] fun t => g (t * s) / s := by
    intro g hg
    filter_upwards [Ioo_mem_nhds (show (1 / 2 : ℝ) < 1 by norm_num)
      (show (1 : ℝ) < 15 / 13 by norm_num)] with t ht
    have ht0 : 0 < t := by linarith [ht.1]
    have hts : 0 < t * s := mul_pos ht0 hspos
    rw [norm_smul, Real.norm_of_nonneg ht0.le, ← hs, mul_pow, ← mul_pow,
      zoneRatioSq_sq hts.le, ← hg (t * s) hts (by nlinarith [ht.2]), zoneRadius]
    field_simp
  have hline : HasDerivAt (fun t : ℝ => t * s) s 1 := by
    simpa using (hasDerivAt_id (1 : ℝ)).mul_const s
  rcases le_total u 2 with h2 | h2
  · obtain ⟨d, hd, hder⟩ := hasDerivAt_neckRadius_capCos (ε := ε) hspos (by linarith)
      (show 0 < u by linarith)
    have hder' : HasDerivAt (fun t : ℝ => neckRadius ε (t * s) (u / capCos (t * s) - 1)) (d * s) 1 := by
      have hder1 : HasDerivAt (fun s => neckRadius ε s (u / capCos s - 1)) d (1 * s) := by
        rw [one_mul]
        exact hder
      exact hder1.comp (1 : ℝ) hline
    have hev := hevgen (fun s' => neckRadius ε s' (u / capCos s' - 1))
      (fun s' hs' hs'' => zoneRadius_eq_lower hε hε' hs'.le hs'' h2 (by linarith))
    refine ⟨d, hd.ne', ?_⟩
    have := (hder'.div_const s).congr_of_eventuallyEq hev
    simpa [hspos.ne'] using this
  · obtain ⟨d, hd, hder⟩ := hasDerivAt_neckRadius_capCos (ε := ε) hspos (by linarith)
      (show 0 < 4 - u by linarith)
    have hder' : HasDerivAt (fun t : ℝ => neckRadius ε (t * s) ((4 - u) / capCos (t * s) - 1))
        (d * s) 1 := by
      have hder1 : HasDerivAt (fun s => neckRadius ε s ((4 - u) / capCos s - 1)) d (1 * s) := by
        rw [one_mul]
        exact hder
      exact hder1.comp (1 : ℝ) hline
    have hev := hevgen (fun s' => neckRadius ε s' ((4 - u) / capCos s' - 1))
      (fun s' hs' hs'' => zoneRadius_eq_upper hε hε' hs'.le hs'' h2 (by linarith))
    refine ⟨d, hd.ne', ?_⟩
    have := (hder'.div_const s).congr_of_eventuallyEq hev
    simpa [hspos.ne'] using this

theorem injective_fderiv_zoneMap (hε : 0 < ε) (hε' : ε ≤ 1 / 8) (c : ℝ) {p : ModelSpace}
    (hp : ‖p.1‖ < 13 / 10) (hu : 3 / 10 < p.2) (hu' : p.2 < 37 / 10) :
    Injective (fderiv ℝ (zoneMap ε c) p) := by
  have hσ' : ‖p.1‖ ^ 2 < 4 := by
    have := norm_nonneg p.1
    nlinarith
  have hm : ContDiffAt ℝ ∞ (fun y : ModelSpace => zoneRatioSq ε (‖y.1‖ ^ 2) y.2) p :=
    ContDiffAt.comp (g := fun q : ℝ × ℝ => zoneRatioSq ε q.1 q.2)
      (f := fun y : ModelSpace => (‖y.1‖ ^ 2, y.2)) p
      (contDiffAt_zoneRatioSq hε hε' (sq_nonneg _) hσ' hu hu')
      ((((contDiff_norm_sq ℝ).comp contDiff_fst).prodMk contDiff_snd).contDiffAt)
  apply injective_fderiv_modelRadialMap (hm.differentiableAt (by simp)).hasFDerivAt
  · intro y y' hn h2
    simp only [hn, h2]
  · rw [zoneRatioSq_sq (norm_nonneg _)]
    exact (zoneRatio_pos hε hε' (norm_nonneg _) hp hu hu').ne'
  · exact one_ne_zero
  · intro hz
    exact exists_hasDerivAt_zoneRatio hε hε' hz hp hu hu'

theorem injective_fderiv_zoneChartMap (hε : 0 < ε) (hε' : ε ≤ 1 / 8) (c : ℝ) {y : ModelSpace}
    (hy : y ∈ zoneDomain) : Injective (fderiv ℝ (zoneChartMap ε c) y) := by
  have hU := zoneHeight_mem (norm_nonneg y.1) hy.1 hy.2.1 hy.2.2
  have hmap := contDiffAt_zoneMap hε hε' c (p := zoneLift y) hy.1 hU.1 hU.2
  have hcomp : zoneChartMap ε c = zoneMap ε c ∘ zoneLift := rfl
  rw [hcomp, fderiv_comp y (hmap.differentiableAt (by simp))
    ((contDiff_zoneLift.differentiable (by simp)) y)]
  exact (injective_fderiv_zoneMap hε hε' c (p := zoneLift y) hy.1 hU.1 hU.2).comp
    (injective_fderiv_zoneLift y (by linarith [hy.1]))

theorem isLocalDiffeomorphOn_zoneChartMap (hε : 0 < ε) (hε' : ε ≤ 1 / 8) (c : ℝ) :
    IsLocalDiffeomorphOn 𝓘(ℝ, ModelSpace) 𝓘(ℝ, ModelSpace) ∞ (zoneChartMap ε c) zoneDomain :=
  isLocalDiffeomorphOn_of_injective_fderiv isOpen_zoneDomain (contDiffOn_zoneChartMap hε hε' c)
    (fun _ hy => injective_fderiv_zoneChartMap hε hε' c hy)

/-! ## The necks inside the zone map -/

theorem zoneChartMap_neck (hε : 0 < ε) (hε' : ε ≤ 1 / 8) (c : ℝ) {z : ModelPlane} {τ : ℝ}
    (hz : ‖z‖ < 13 / 10) (hτ : -1 / 4 < τ) (hτ' : τ ≤ 1 / 3) :
    zoneChartMap ε c (z, τ) = (neckRatio ε ‖z‖ τ • z, c + (1 + τ) * capCos ‖z‖) := by
  have hq := capCos_gt_of_lt (norm_nonneg z) hz
  have hq1 := capCos_le_one ‖z‖
  rw [zoneChartMap_apply]
  simp only
  rw [zoneHeight_of_le hτ']
  have hu2 : (1 + τ) * capCos ‖z‖ ≤ 2 := by nlinarith
  rw [zoneRatio_eq_lower hε hε' (by rw [abs_of_nonneg (norm_nonneg _)]; linarith) hu2,
    mul_div_cancel_right₀ _ (by linarith : capCos ‖z‖ ≠ 0), add_sub_cancel_left]

theorem zoneChartMap_neck_flip (hε : 0 < ε) (hε' : ε ≤ 1 / 8) (c : ℝ) {z : ModelPlane} {τ : ℝ}
    (hz : ‖z‖ < 13 / 10) (hτ : -1 / 4 < τ) (hτ' : τ ≤ 1 / 3) :
    zoneChartMap ε c (z, 1 - τ) = (neckRatio ε ‖z‖ τ • z, c + 4 - (1 + τ) * capCos ‖z‖) := by
  have hq := capCos_gt_of_lt (norm_nonneg z) hz
  have hq1 := capCos_le_one ‖z‖
  rw [zoneChartMap_apply]
  simp only
  rw [zoneHeight_of_ge (by linarith), sub_sub_cancel]
  have hu2 : 2 ≤ 4 - (1 + τ) * capCos ‖z‖ := by nlinarith
  rw [zoneRatio_eq_upper hε hε' (by rw [abs_of_nonneg (norm_nonneg _)]; linarith) hu2,
    sub_sub_cancel, mul_div_cancel_right₀ _ (by linarith : capCos ‖z‖ ≠ 0), add_sub_cancel_left,
    add_sub_assoc]

end GC.GraphManifold.Assembly
