import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.AssemblyL1NecksCharts
import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.AssemblyL1NecksCollarDomain
import DifferentialGeometry.Topology.Embedding.Extension
import DifferentialGeometry.Analysis.Calculus.SmoothExtension.Closed

/-!
# Chapter-14 assembly, item L1, G3b / T1′: the ball-side collar of a rim (E2a)

Lane ASM-L1e3, group C1. Near the end disk `b` of a handle `H`, inside a ball chart `Bh` of the
ball containing that end disk, the handle read in product coordinates
`(z, s) ↦ Bh⁻¹ (H (handleDiskMap A P z, endCoord b (σ s)))` (`s ≥ 0`) extends across `s = 0` to a
local diffeomorphism `G` of a thin slab `collarDomain η` into the chart, with values in the open
unit ball for `s < 0` (the ball side) and equal to the rim chart read in polar coordinates near the
rim (`‖z‖ ≥ 59/64`).

* `contMDiffAt_diskClamp`: `diskClamp` is smooth inside the open unit disk.
* `EdgeHandle.exists_endExtension`: the handle near an end disk, read in `Bh`, extends to a smooth
  map of `ℝ² × ℝ` (Seeley extension
  `IsSmoothEmbedding.exists_contDiff_extension_prod_halfspace_of_isClosed_image` on
  `ℝ² × [0, 1]`), with bijective derivative along the end.
* `inner_fderiv_pos_of_sphere`, `norm_lt_one_of_inner_fderiv_pos`: the inward direction (`dG` onto
  and `‖G (·, 0)‖ ≡ 1` force `⟪G, ∂ₛ G⟫ ≠ 0`; the handle side `s > 0` lies outside the ball, so the
  sign is positive; monotonicity puts `s < 0` inside the ball).
* `collarWeight`, `collarBlend`: the blend of the handle read with the rim read.
* `exists_ballSideCollar` (E2a, frozen statement of `build-logs/scratch/ASM-L1e2/Targets.lean`;
  `collarDomain` from `AssemblyL1NecksCollarDomain`).
-/

set_option autoImplicit false

noncomputable section

open Set Function Filter Manifold
open DifferentialGeometry DifferentialGeometry.Topology GC.Endpoint GC.GraphManifold
open scoped Manifold ContDiff Topology

universe u

namespace GC.GraphManifold.Assembly

local instance diskCharts_ASML1e3 : ChartedSpace (EuclideanHalfSpace 2) (ClosedCell 2) :=
  DifferentialGeometry.Topology.Handle.closedCellChartedSpaceSucc 1

local instance diskSmooth_ASML1e3 : IsManifold (𝓡∂ 2) ∞ (ClosedCell 2) :=
  DifferentialGeometry.Topology.Handle.closedCellIsManifold 1

local instance diskChartsSucc_ASML1e3 :
    ChartedSpace (EuclideanHalfSpace (1 + 1)) (ClosedCell (1 + 1)) :=
  DifferentialGeometry.Topology.Handle.closedCellChartedSpaceSucc 1

local instance diskSmoothSucc_ASML1e3 : IsManifold (𝓡∂ (1 + 1)) ∞ (ClosedCell (1 + 1)) :=
  DifferentialGeometry.Topology.Handle.closedCellIsManifold 1

local instance iccCharts_ASML1e3 : ChartedSpace (EuclideanHalfSpace (0 + 1)) (Icc (0 : ℝ) 1) :=
  inferInstanceAs (ChartedSpace (EuclideanHalfSpace 1) (Icc (0 : ℝ) 1))

theorem diskClamp_coe (w : ClosedCell 2) : diskClamp (w : EuclideanSpace ℝ (Fin 2)) = w :=
  Subtype.ext (diskClamp_val w.2)

/-- `diskClamp` is smooth inside the open unit disk. -/
theorem contMDiffAt_diskClamp {w : EuclideanSpace ℝ (Fin 2)} (hw : ‖w‖ < 1) :
    ContMDiffAt 𝓘(ℝ, EuclideanSpace ℝ (Fin 2)) (𝓡∂ 2) ∞ diskClamp w := by
  have hev : (fun v => (diskClamp v : EuclideanSpace ℝ (Fin 2))) =ᶠ[𝓝 w] id := by
    filter_upwards [(isOpen_lt continuous_norm continuous_const).mem_nhds hw] with v hv
    exact diskClamp_val (le_of_lt hv)
  have hi := (DifferentialGeometry.Topology.Manifold.isSmoothEmbedding_closedCell_inclusion
    1).isImmersion.isImmersionAt (diskClamp w)
  refine (ContMDiffAt.iff_comp_isImmersionAt hi).mpr ⟨?_, ?_⟩
  · exact Topology.IsInducing.subtypeVal.continuousAt_iff.mpr
      (continuousAt_id.congr hev.symm)
  · exact contMDiffAt_id.congr_of_eventuallyEq hev

variable {W : CompactCarrier.{u}}

/-- **The handle near an end disk, extended across the end.** Read in a chart `Bh` whose target
contains the end disk, the handle `(w, t) ↦ Bh⁻¹ (H (w, t))` extends, near `‖w‖ ≤ R < 1` and
`t` near the end, to a smooth map of `ℝ² × ℝ` with bijective derivative along the end. -/
theorem EdgeHandle.exists_endExtension (H : EdgeHandle W) (b : Bool)
    (Bh : PartialDiffeomorph (𝓡 3) W.model (EuclideanSpace ℝ (Fin 3)) W.Carrier ∞)
    (hdisk : H.endDisk b ⊆ Bh.target) {R : ℝ} (hR0 : 0 ≤ R) (hR : R < 1) :
    ∃ δ : ℝ, 0 < δ ∧ ∃ Gt : EuclideanSpace ℝ (Fin 2) × ℝ → EuclideanSpace ℝ (Fin 3),
      ContDiff ℝ ∞ Gt ∧
      (∀ (w : ClosedCell 2) (t : Icc (0 : ℝ) 1), ‖(w : EuclideanSpace ℝ (Fin 2))‖ ≤ R →
        |(t : ℝ) - (iccEnd b : ℝ)| < δ →
        H.map (w, t) ∈ Bh.target ∧
          Gt ((w : EuclideanSpace ℝ (Fin 2)), (t : ℝ)) = Bh.symm (H.map (w, t))) ∧
      ∀ w : EuclideanSpace ℝ (Fin 2), ‖w‖ ≤ R →
        Bijective (fderiv ℝ Gt (w, (iccEnd b : ℝ))) := by
  set r₁ : ℝ := (2 * R + 1) / 3 with hr₁def
  set r₂ : ℝ := (R + 2) / 3 with hr₂def
  have hr₁ : R < r₁ := by rw [hr₁def]; linarith
  have hr₁₂ : r₁ < r₂ := by rw [hr₁def, hr₂def]; linarith
  have hr₂ : r₂ < 1 := by rw [hr₂def]; linarith
  have hr₁0 : 0 < r₁ := by rw [hr₁def]; linarith
  let Φ : EuclideanSpace ℝ (Fin 2) × Icc (0 : ℝ) 1 → W.Carrier := fun p => H.map (diskClamp p.1, p.2)
  have hΦc : ContinuousOn Φ {p | ‖p.1‖ < 1} := by
    intro p hp
    apply ContinuousAt.continuousWithinAt
    exact H.smooth.continuous.continuousAt.comp
      ((((contMDiffAt_diskClamp hp).continuousAt).comp continuousAt_fst).prodMk continuousAt_snd)
  let O : Set (EuclideanSpace ℝ (Fin 2) × Icc (0 : ℝ) 1) := {p | ‖p.1‖ < 1} ∩ Φ ⁻¹' Bh.target
  have hO : IsOpen O := hΦc.isOpen_inter_preimage
    (isOpen_lt (continuous_norm.comp continuous_fst) continuous_const) Bh.open_target
  let K : Set (EuclideanSpace ℝ (Fin 2) × Icc (0 : ℝ) 1) := Metric.closedBall 0 r₂ ×ˢ {iccEnd b}
  have hK : IsCompact K := (isCompact_closedBall 0 r₂).prod isCompact_singleton
  have hKO : K ⊆ O := by
    rintro ⟨w, t⟩ ⟨hw, ht⟩
    rw [mem_singleton_iff] at ht
    subst ht
    exact ⟨lt_of_le_of_lt (mem_closedBall_zero_iff.mp hw) hr₂, hdisk ⟨diskClamp w, rfl⟩⟩
  obtain ⟨ε, hε, hεO⟩ := hK.exists_cthickening_subset_open hO hKO
  have hnear : ∀ (w : EuclideanSpace ℝ (Fin 2)) (t : Icc (0 : ℝ) 1), ‖w‖ ≤ r₂ →
      |(t : ℝ) - (iccEnd b : ℝ)| ≤ ε → (w, t) ∈ O := by
    intro w t hw ht
    apply hεO
    apply Metric.mem_cthickening_of_dist_le (w, t) (w, iccEnd b) ε K
      ⟨mem_closedBall_zero_iff.mpr hw, rfl⟩
    rw [Prod.dist_eq, dist_self, Subtype.dist_eq, Real.dist_eq]
    exact max_le hε.le ht
  let μ₁ : ContDiffBump (0 : EuclideanSpace ℝ (Fin 2)) := ⟨r₁, r₂, hr₁0, hr₁₂⟩
  let μ₂ : ContDiffBump ((iccEnd b : ℝ)) := ⟨ε / 2, ε, half_pos hε, half_lt_self hε⟩
  let g : EuclideanSpace ℝ (Fin 2) × Icc (0 : ℝ) 1 → EuclideanSpace ℝ (Fin 3) :=
    fun p => (μ₁ p.1 * μ₂ (p.2 : ℝ)) • Bh.symm (Φ p)
  have hgsupp : tsupport g ⊆ {p | ‖p.1‖ ≤ r₂ ∧ |(p.2 : ℝ) - (iccEnd b : ℝ)| ≤ ε} := by
    apply closure_minimal
    · intro p hp
      have hp' : μ₁ p.1 * μ₂ (p.2 : ℝ) ≠ 0 := left_ne_zero_of_smul hp
      have h1 : p.1 ∈ Function.support μ₁ := left_ne_zero_of_mul hp'
      have h2 : (p.2 : ℝ) ∈ Function.support μ₂ := right_ne_zero_of_mul hp'
      rw [μ₁.support_eq, mem_ball_zero_iff] at h1
      rw [μ₂.support_eq, Metric.mem_ball, Real.dist_eq] at h2
      exact ⟨h1.le, h2.le⟩
    · exact (isClosed_le (continuous_norm.comp continuous_fst) continuous_const).inter
        (isClosed_le (continuous_abs.comp ((continuous_subtype_val.comp continuous_snd).sub
          continuous_const)) continuous_const)
  have hg : ContMDiff (𝓘(ℝ, EuclideanSpace ℝ (Fin 2)).prod (𝓡∂ 1)) (𝓡 3) ∞ g := by
    apply contMDiff_of_tsupport
    intro p hp
    obtain ⟨hp1, hp2⟩ := hgsupp hp
    have hpO : p ∈ O := hnear p.1 p.2 hp1 hp2
    have hcl : ContMDiffAt (𝓘(ℝ, EuclideanSpace ℝ (Fin 2)).prod (𝓡∂ 1)) 𝓘(ℝ, ℝ) ∞
        (fun p : EuclideanSpace ℝ (Fin 2) × Icc (0 : ℝ) 1 => μ₁ p.1 * μ₂ (p.2 : ℝ)) p :=
      ((μ₁.contDiff.contMDiff.comp contMDiff_fst).mul
        (μ₂.contDiff.contMDiff.comp (contMDiff_subtypeVal_Icc.comp contMDiff_snd))).contMDiffAt
    have hΦ : ContMDiffAt (𝓘(ℝ, EuclideanSpace ℝ (Fin 2)).prod (𝓡∂ 1)) W.model ∞ Φ p :=
      H.smooth.contMDiffAt.comp p
        (((contMDiffAt_diskClamp hpO.1).comp p contMDiffAt_fst).prodMk contMDiffAt_snd)
    have hB : ContMDiffAt W.model (𝓡 3) ∞ Bh.symm (Φ p) :=
      Bh.symm.contMDiffOn.contMDiffAt (Bh.open_target.mem_nhds hpO.2)
    exact hcl.smul (hB.comp p hΦ)
  have hf : IsSmoothEmbedding (𝓘(ℝ, EuclideanSpace ℝ (Fin 2)).prod (𝓡∂ 1))
      𝓘(ℝ, EuclideanSpace ℝ (Fin 2) × ℝ) ∞
      (Prod.map (id : EuclideanSpace ℝ (Fin 2) → EuclideanSpace ℝ (Fin 2))
        (Subtype.val : Icc (0 : ℝ) 1 → ℝ)) := by
    rw [modelWithCornersSelf_prod, ← chartedSpaceSelf_prod]
    exact IsSmoothEmbedding.id.prodMap isSmoothEmbedding_subtypeVal_Icc
  have himg : IsClosed ((Prod.map (id : EuclideanSpace ℝ (Fin 2) → EuclideanSpace ℝ (Fin 2))
      (Subtype.val : Icc (0 : ℝ) 1 → ℝ)) '' univ) := by
    rw [image_univ, range_prodMap, range_id, Subtype.range_coe]
    exact isClosed_univ.prod isClosed_Icc
  obtain ⟨Gt, hGt, hGtf⟩ :=
    hf.exists_contDiff_extension_prod_halfspace_of_isClosed_image (d := 0) hg himg
  have hval : ∀ (w : EuclideanSpace ℝ (Fin 2)) (t : Icc (0 : ℝ) 1), ‖w‖ ≤ r₁ →
      |(t : ℝ) - (iccEnd b : ℝ)| ≤ ε / 2 → Gt (w, (t : ℝ)) = Bh.symm (Φ (w, t)) := by
    intro w t hw ht
    have h1 : Gt (w, (t : ℝ)) = g (w, t) := hGtf (mem_univ (w, t))
    have hμ1 : μ₁ w = 1 := μ₁.one_of_mem_closedBall (mem_closedBall_zero_iff.mpr hw)
    have hμ2 : μ₂ (t : ℝ) = 1 :=
      μ₂.one_of_mem_closedBall (by rw [Metric.mem_closedBall, Real.dist_eq]; exact ht)
    rw [h1]
    change (μ₁ w * μ₂ (t : ℝ)) • Bh.symm (Φ (w, t)) = Bh.symm (Φ (w, t))
    rw [hμ1, hμ2, mul_one, one_smul]
  refine ⟨ε / 2, half_pos hε, Gt, hGt, ?_, ?_⟩
  · intro w t hw ht
    have hΦw : Φ ((w : EuclideanSpace ℝ (Fin 2)), t) = H.map (w, t) := by
      change H.map (diskClamp (w : EuclideanSpace ℝ (Fin 2)), t) = H.map (w, t)
      rw [diskClamp_coe]
    have hwO := hnear w t (hw.trans (hr₁.le.trans hr₁₂.le))
      (ht.le.trans (half_le_self hε.le))
    refine ⟨hΦw ▸ hwO.2, ?_⟩
    rw [hval w t (hw.trans hr₁.le) ht.le, hΦw]
  · intro w hw
    have hwc : ‖w‖ ≤ 1 := by linarith
    let x₀ : ClosedCell 2 × Icc (0 : ℝ) 1 := (diskClamp w, iccEnd b)
    let ι : ClosedCell 2 × Icc (0 : ℝ) 1 → EuclideanSpace ℝ (Fin 2) × ℝ :=
      Prod.map Subtype.val Subtype.val
    have hι : IsSmoothEmbedding ((𝓡∂ 2).prod (𝓡∂ 1)) 𝓘(ℝ, EuclideanSpace ℝ (Fin 2) × ℝ) ∞ ι := by
      rw [modelWithCornersSelf_prod, ← chartedSpaceSelf_prod]
      exact (DifferentialGeometry.Topology.Manifold.isSmoothEmbedding_closedCell_inclusion
        1).prodMap (isSmoothEmbedding_subtypeVal_Icc (x := (0 : ℝ)) (y := 1))
    have hιb : Bijective (mfderiv ((𝓡∂ 2).prod (𝓡∂ 1))
        𝓘(ℝ, EuclideanSpace ℝ (Fin 2) × ℝ) ι x₀) :=
      DifferentialGeometry.Topology.Manifold.bijective_mfderiv_of_isImmersionAt _ _ ι x₀
        (hι.isImmersion.isImmersionAt x₀) (by simp)
    have hι0 : ι x₀ = (w, (iccEnd b : ℝ)) := by
      change ((diskClamp w : EuclideanSpace ℝ (Fin 2)), (iccEnd b : ℝ)) = (w, (iccEnd b : ℝ))
      rw [diskClamp_val hwc]
    have hev : (Gt ∘ ι) =ᶠ[𝓝 x₀] (Bh.symm ∘ H.map) := by
      have hc : ContinuousAt (fun x : ClosedCell 2 × Icc (0 : ℝ) 1 =>
          (‖(x.1 : EuclideanSpace ℝ (Fin 2))‖, |(x.2 : ℝ) - (iccEnd b : ℝ)|)) x₀ := by
        fun_prop
      have hlt : (‖(x₀.1 : EuclideanSpace ℝ (Fin 2))‖, |(x₀.2 : ℝ) - (iccEnd b : ℝ)|) ∈
          Iio r₁ ×ˢ Iio (ε / 2) := by
        refine ⟨?_, ?_⟩
        · change ‖((diskClamp w : ClosedCell 2) : EuclideanSpace ℝ (Fin 2))‖ < r₁
          rw [diskClamp_val hwc]
          exact lt_of_le_of_lt hw hr₁
        · change |(iccEnd b : ℝ) - (iccEnd b : ℝ)| < ε / 2
          rw [sub_self, abs_zero]
          exact half_pos hε
      filter_upwards [hc.preimage_mem_nhds ((isOpen_Iio.prod isOpen_Iio).mem_nhds hlt)] with x hx
      have h := hval (x.1 : EuclideanSpace ℝ (Fin 2)) x.2 hx.1.le hx.2.le
      change Gt ((x.1 : EuclideanSpace ℝ (Fin 2)), (x.2 : ℝ)) = Bh.symm (H.map x)
      rw [h]
      change Bh.symm (H.map (diskClamp (x.1 : EuclideanSpace ℝ (Fin 2)), x.2)) = Bh.symm (H.map x)
      rw [diskClamp_coe]
    have hx0 : H.map x₀ ∈ Bh.target := hdisk ⟨diskClamp w, rfl⟩
    have hBd : MDifferentiableAt W.model (𝓡 3) Bh.symm (H.map x₀) :=
      Bh.symm.mdifferentiableAt (by simp) hx0
    have hHd : MDifferentiableAt ((𝓡∂ 2).prod (𝓡∂ 1)) W.model H.map x₀ :=
      H.smooth.mdifferentiableAt (by simp)
    have hBb : Bijective (mfderiv W.model (𝓡 3) Bh.symm (H.map x₀)) :=
      ((Bh.symm.isLocalDiffeomorphAt W.model (𝓡 3) ∞ hx0).mfderivToContinuousLinearEquiv (by simp)).bijective
    have hGd : MDifferentiableAt 𝓘(ℝ, EuclideanSpace ℝ (Fin 2) × ℝ) (𝓡 3) Gt (ι x₀) :=
      (hGt.differentiable (by simp) (ι x₀)).mdifferentiableAt
    have hιd : MDifferentiableAt ((𝓡∂ 2).prod (𝓡∂ 1)) 𝓘(ℝ, EuclideanSpace ℝ (Fin 2) × ℝ) ι x₀ :=
      hι.isImmersion.contMDiff.mdifferentiableAt (by simp)
    have hall : Bijective (mfderiv ((𝓡∂ 2).prod (𝓡∂ 1)) (𝓡 3) (Gt ∘ ι) x₀) := by
      rw [hev.mfderiv_eq, mfderiv_comp x₀ hBd hHd]
      exact hBb.comp (H.mfderiv_bijective x₀)
    rw [mfderiv_comp x₀ hGd hιd, mfderiv_eq_fderiv] at hall
    rw [← hι0]
    exact (Function.Bijective.of_comp_iff _ hιb).mp hall

/-! ## The end coordinate -/

theorem endCoord_zero (b : Bool) : endCoord b 0 = (iccEnd b : ℝ) := by
  cases b <;> simp [endCoord, iccEnd]

theorem abs_endCoord_sub_iccEnd (b : Bool) (x : ℝ) :
    |endCoord b x - (iccEnd b : ℝ)| = |x| := by
  cases b
  · simp [endCoord, iccEnd]
  · simp [endCoord, iccEnd, abs_neg]

theorem endCoord_mem_Icc_of_mem (b : Bool) {x : ℝ} (hx : x ∈ Icc (0 : ℝ) 1) :
    endCoord b x ∈ Icc (0 : ℝ) 1 := by
  obtain ⟨h0, h1⟩ := hx
  cases b
  · simp only [endCoord, Bool.false_eq_true, ite_false]
    exact ⟨h0, h1⟩
  · simp only [endCoord, ite_true]
    constructor <;> linarith

theorem endCoord_mem_Ioo_of_mem (b : Bool) {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    endCoord b x ∈ Ioo (0 : ℝ) 1 := by
  obtain ⟨h0, h1⟩ := hx
  cases b
  · simp only [endCoord, Bool.false_eq_true, ite_false]
    exact ⟨h0, h1⟩
  · simp only [endCoord, ite_true]
    constructor <;> linarith

theorem hasDerivAt_endCoord (b : Bool) (x : ℝ) :
    HasDerivAt (endCoord b) (if b then -1 else 1) x := by
  cases b
  · have h : endCoord false = id := funext fun t => by simp [endCoord]
    rw [h]
    simpa using hasDerivAt_id x
  · have h : endCoord true = fun t => 1 - t := funext fun t => by simp [endCoord]
    rw [h]
    simpa using (hasDerivAt_id x).const_sub 1

theorem contDiff_endCoord (b : Bool) : ContDiff ℝ ∞ (endCoord b) := by
  cases b
  · have h : endCoord false = id := funext fun t => by simp [endCoord]
    rw [h]
    exact contDiff_id
  · have h : endCoord true = fun t => 1 - t := funext fun t => by simp [endCoord]
    rw [h]
    exact contDiff_const.sub contDiff_id

/-- A nonzero real multiple is a linear bijection of `ℝ`. -/
theorem bijective_smulRight_one {c : ℝ} (hc : c ≠ 0) :
    Bijective ((1 : ℝ →L[ℝ] ℝ).smulRight c) := by
  refine ⟨fun v w hvw => ?_, fun w => ⟨w / c, ?_⟩⟩
  · have h1 : v * c = w * c := by simpa using hvw
    exact mul_right_cancel₀ hc h1
  · have h2 : w / c * c = w := div_mul_cancel₀ w hc
    simpa using h2

/-! ## Calculus of the inward direction -/

/-- **The inward derivative is positive.** If `‖G (·, 0)‖ ≡ 1` near `z`, `‖G (z, s)‖ > 1` for
small `s > 0` and `dG (z, 0)` is onto, then `⟪G (z, 0), ∂ₛ G (z, 0)⟫ > 0`. -/
theorem inner_fderiv_pos_of_sphere
    {G : EuclideanSpace ℝ (Fin 2) × ℝ → EuclideanSpace ℝ (Fin 3)}
    {z : EuclideanSpace ℝ (Fin 2)} (hG : DifferentiableAt ℝ G (z, 0))
    (hsph : ∀ᶠ z' in 𝓝 z, ‖G (z', 0)‖ = 1)
    (hout : ∀ᶠ s in 𝓝[>] (0 : ℝ), 1 < ‖G (z, s)‖)
    (hsurj : Surjective (fderiv ℝ G (z, 0))) :
    0 < inner ℝ (G (z, 0)) (fderiv ℝ G (z, 0) (0, 1)) := by
  set p := G (z, 0) with hp
  set L := fderiv ℝ G (z, 0) with hL
  have hGL : HasFDerivAt G L (z, 0) := hG.hasFDerivAt
  have hp1 : ‖p‖ = 1 := hsph.self_of_nhds
  -- the horizontal derivative of `‖G‖²` vanishes
  have hhor : ∀ v : EuclideanSpace ℝ (Fin 2), inner ℝ p (L (v, 0)) = 0 := by
    have h1 : HasFDerivAt (fun z' : EuclideanSpace ℝ (Fin 2) => ‖G (z', 0)‖ ^ 2)
        (2 • (innerSL ℝ p).comp (L.comp (ContinuousLinearMap.inl ℝ _ ℝ))) z :=
      (hGL.comp z (hasFDerivAt_prodMk_left z (0 : ℝ))).norm_sq
    have h2 : HasFDerivAt (fun z' : EuclideanSpace ℝ (Fin 2) => ‖G (z', 0)‖ ^ 2)
        (0 : EuclideanSpace ℝ (Fin 2) →L[ℝ] ℝ) z := by
      apply (hasFDerivAt_const (1 : ℝ) z).congr_of_eventuallyEq
      filter_upwards [hsph] with z' hz'
      rw [hz', one_pow]
    intro v
    have h3 := congrArg (fun D : EuclideanSpace ℝ (Fin 2) →L[ℝ] ℝ => D v) (h1.unique h2)
    have h4 : (2 : ℕ) • inner ℝ p (L (v, 0)) = 0 := h3
    rw [two_nsmul] at h4
    linarith
  set c := inner ℝ p (L (0, 1)) with hc
  -- `c ≠ 0`, else `dG` maps into `p^⊥`
  have hc0 : c ≠ 0 := by
    intro hc0
    obtain ⟨q, hq⟩ := hsurj p
    have hdec : q = (q.1, 0) + q.2 • ((0 : EuclideanSpace ℝ (Fin 2)), (1 : ℝ)) := by
      ext <;> simp
    have h1 : inner ℝ p (L q) = 0 := by
      rw [hdec, map_add, map_smul, inner_add_right, inner_smul_right, hhor q.1, ← hc, hc0,
        mul_zero, add_zero]
    rw [hq, real_inner_self_eq_norm_sq, hp1] at h1
    norm_num at h1
  -- `c ≥ 0`, since `‖G (z, s)‖ > 1 = ‖G (z, 0)‖` for small `s > 0`
  have hφ : HasDerivAt (fun s : ℝ => ‖G (z, s)‖ ^ 2) (2 * c) 0 := by
    have h1 : HasFDerivAt (fun s : ℝ => ‖G (z, s)‖ ^ 2)
        (2 • (innerSL ℝ p).comp (L.comp (ContinuousLinearMap.inr ℝ _ ℝ))) 0 :=
      (hGL.comp (0 : ℝ) (hasFDerivAt_prodMk_right z (0 : ℝ))).norm_sq
    have h2 := h1.hasDerivAt
    have h3 : (2 • (innerSL ℝ p).comp (L.comp (ContinuousLinearMap.inr ℝ
        (EuclideanSpace ℝ (Fin 2)) ℝ))) (1 : ℝ) = 2 * c := by
      change (2 : ℕ) • inner ℝ p (L (0, 1)) = 2 * c
      rw [two_nsmul, ← hc]
      ring
    rwa [h3] at h2
  rcases lt_or_gt_of_ne hc0 with hneg | hpos
  · exfalso
    have hT := (hasDerivAt_iff_tendsto_slope.mp hφ).mono_left
      (nhdsWithin_mono (0 : ℝ) (fun s (hs : s ∈ Ioi (0 : ℝ)) => ne_of_gt hs))
    have hev : ∀ᶠ s in 𝓝[>] (0 : ℝ), slope (fun s : ℝ => ‖G (z, s)‖ ^ 2) 0 s < 0 :=
      hT.eventually (eventually_lt_nhds (by linarith))
    obtain ⟨s, hs1, hs2, hs3⟩ := (hev.and (hout.and self_mem_nhdsWithin)).exists
    rw [slope_def_field, sub_zero] at hs1
    have hs3' : (0 : ℝ) < s := hs3
    have h4 : ‖G (z, s)‖ ^ 2 - ‖G (z, 0)‖ ^ 2 < 0 := by
      by_contra hcon
      push Not at hcon
      have := div_nonneg hcon hs3'.le
      linarith
    rw [← hp, hp1] at h4
    nlinarith [norm_nonneg (G (z, s))]
  · exact hpos

/-- **Monotonicity in the inward direction.** -/
theorem norm_lt_one_of_inner_fderiv_pos
    {G : EuclideanSpace ℝ (Fin 2) × ℝ → EuclideanSpace ℝ (Fin 3)}
    {z : EuclideanSpace ℝ (Fin 2)} {η : ℝ}
    (hd : ∀ s ∈ Ioo (-η) η, DifferentiableAt ℝ G (z, s))
    (hpos : ∀ s ∈ Ioo (-η) η, 0 < inner ℝ (G (z, s)) (fderiv ℝ G (z, s) (0, 1)))
    (h0 : ‖G (z, 0)‖ = 1) {s : ℝ} (hs : s ∈ Ioo (-η) 0) : ‖G (z, s)‖ < 1 := by
  have hη : 0 < η := by linarith [hs.1, hs.2]
  have hder : ∀ x ∈ Ioo (-η) η, HasDerivAt (fun s : ℝ => ‖G (z, s)‖ ^ 2)
      (2 * inner ℝ (G (z, x)) (fderiv ℝ G (z, x) (0, 1))) x := by
    intro x hx
    have h1 : HasFDerivAt (fun s : ℝ => ‖G (z, s)‖ ^ 2)
        (2 • (innerSL ℝ (G (z, x))).comp ((fderiv ℝ G (z, x)).comp
          (ContinuousLinearMap.inr ℝ (EuclideanSpace ℝ (Fin 2)) ℝ))) x :=
      ((hd x hx).hasFDerivAt.comp x (hasFDerivAt_prodMk_right z x)).norm_sq
    have h2 := h1.hasDerivAt
    have h3 : (2 • (innerSL ℝ (G (z, x))).comp ((fderiv ℝ G (z, x)).comp
        (ContinuousLinearMap.inr ℝ (EuclideanSpace ℝ (Fin 2)) ℝ))) (1 : ℝ) =
        2 * inner ℝ (G (z, x)) (fderiv ℝ G (z, x) (0, 1)) := by
      change (2 : ℕ) • inner ℝ (G (z, x)) (fderiv ℝ G (z, x) (0, 1)) = _
      rw [two_nsmul]
      ring
    rwa [h3] at h2
  have hmono : StrictMonoOn (fun s : ℝ => ‖G (z, s)‖ ^ 2) (Ioo (-η) η) := by
    apply strictMonoOn_of_deriv_pos (convex_Ioo (-η) η)
    · exact fun x hx => (hder x hx).continuousAt.continuousWithinAt
    · intro x hx
      rw [interior_Ioo] at hx
      rw [(hder x hx).deriv]
      exact mul_pos two_pos (hpos x hx)
  have hlt := hmono ⟨hs.1, by linarith [hs.2]⟩ ⟨by linarith, hη⟩ hs.2
  simp only [h0, one_pow] at hlt
  have := norm_nonneg (G (z, s))
  nlinarith

/-! ## Compactness -/

/-- A slab around a compact set of the plane inside an open set. -/
theorem exists_slab_subset {K : Set (EuclideanSpace ℝ (Fin 2))} (hK : IsCompact K)
    {V : Set (EuclideanSpace ℝ (Fin 2) × ℝ)} (hV : IsOpen V)
    (hKV : ∀ z ∈ K, (z, (0 : ℝ)) ∈ V) :
    ∃ η : ℝ, 0 < η ∧ ∀ z ∈ K, ∀ s : ℝ, |s| < η → (z, s) ∈ V := by
  have hK' : IsCompact (K ×ˢ ({0} : Set ℝ)) := hK.prod isCompact_singleton
  have hKV' : K ×ˢ ({0} : Set ℝ) ⊆ V := by
    rintro ⟨z, s⟩ ⟨hz, hs⟩
    rw [mem_singleton_iff] at hs
    subst hs
    exact hKV z hz
  obtain ⟨ε, hε, hεV⟩ := hK'.exists_cthickening_subset_open hV hKV'
  refine ⟨ε, hε, fun z hz s hs => hεV ?_⟩
  apply Metric.mem_cthickening_of_dist_le (z, s) (z, 0) ε (K ×ˢ ({0} : Set ℝ)) ⟨hz, rfl⟩
  rw [Prod.dist_eq, dist_self, Real.dist_eq, sub_zero]
  exact max_le hε.le hs.le

/-- The set where `dG` is bijective and the inward derivative is positive is open. -/
theorem isOpen_bijective_inner_pos
    {G : EuclideanSpace ℝ (Fin 2) × ℝ → EuclideanSpace ℝ (Fin 3)}
    {D : Set (EuclideanSpace ℝ (Fin 2) × ℝ)} (hD : IsOpen D) (hG : ContDiffOn ℝ ∞ G D) :
    IsOpen {q | q ∈ D ∧ fderiv ℝ G q ∈ range ((↑) : ((EuclideanSpace ℝ (Fin 2) × ℝ) ≃L[ℝ]
      EuclideanSpace ℝ (Fin 3)) → (EuclideanSpace ℝ (Fin 2) × ℝ) →L[ℝ] EuclideanSpace ℝ (Fin 3)) ∧
        0 < inner ℝ (G q) (fderiv ℝ G q (0, 1))} := by
  have hF : ContinuousOn (fun q => (G q, fderiv ℝ G q)) D :=
    hG.continuousOn.prodMk (hG.continuousOn_fderiv_of_isOpen hD (by simp))
  have hT1 : IsOpen {x : EuclideanSpace ℝ (Fin 3) × ((EuclideanSpace ℝ (Fin 2) × ℝ) →L[ℝ]
      EuclideanSpace ℝ (Fin 3)) | x.2 ∈ range ((↑) : ((EuclideanSpace ℝ (Fin 2) × ℝ) ≃L[ℝ]
        EuclideanSpace ℝ (Fin 3)) → (EuclideanSpace ℝ (Fin 2) × ℝ) →L[ℝ]
          EuclideanSpace ℝ (Fin 3))} :=
    ContinuousLinearEquiv.isOpen.preimage continuous_snd
  have hT2 : IsOpen {x : EuclideanSpace ℝ (Fin 3) × ((EuclideanSpace ℝ (Fin 2) × ℝ) →L[ℝ]
      EuclideanSpace ℝ (Fin 3)) | 0 < inner ℝ x.1 (x.2 (0, 1))} :=
    isOpen_lt continuous_const
      (continuous_fst.inner (continuous_snd.clm_apply continuous_const))
  exact hF.isOpen_inter_preimage hD (hT1.inter hT2)

theorem bijective_of_mem_range_coe {L : (EuclideanSpace ℝ (Fin 2) × ℝ) →L[ℝ]
    EuclideanSpace ℝ (Fin 3)}
    (h : L ∈ range ((↑) : ((EuclideanSpace ℝ (Fin 2) × ℝ) ≃L[ℝ] EuclideanSpace ℝ (Fin 3)) →
      (EuclideanSpace ℝ (Fin 2) × ℝ) →L[ℝ] EuclideanSpace ℝ (Fin 3))) : Bijective L := by
  obtain ⟨e, rfl⟩ := h
  exact e.bijective

theorem mem_range_coe_of_bijective {L : (EuclideanSpace ℝ (Fin 2) × ℝ) →L[ℝ]
    EuclideanSpace ℝ (Fin 3)} (h : Bijective L) :
    L ∈ range ((↑) : ((EuclideanSpace ℝ (Fin 2) × ℝ) ≃L[ℝ] EuclideanSpace ℝ (Fin 3)) →
      (EuclideanSpace ℝ (Fin 2) × ℝ) →L[ℝ] EuclideanSpace ℝ (Fin 3)) :=
  ⟨(LinearEquiv.ofBijective L.toLinearMap h).toContinuousLinearEquiv, rfl⟩

/-! ## The blending weight -/

/-- The blending weight of the collar: `0` for `‖z‖ ≤ 235/256`, `1` for `‖z‖ ≥ 59/64`. -/
def collarWeight (z : EuclideanSpace ℝ (Fin 2)) : ℝ :=
  Real.smoothTransition ((‖z‖ ^ 2 - (235 / 256) ^ 2) / ((59 / 64) ^ 2 - (235 / 256) ^ 2))

theorem contDiff_collarWeight : ContDiff ℝ ∞ collarWeight :=
  Real.smoothTransition.contDiff.comp
    (((contDiff_norm_sq ℝ).sub contDiff_const).div_const _)

theorem collarWeight_eq_zero {z : EuclideanSpace ℝ (Fin 2)} (hz : ‖z‖ ≤ 235 / 256) :
    collarWeight z = 0 := by
  apply Real.smoothTransition.zero_of_nonpos
  apply div_nonpos_of_nonpos_of_nonneg _ (by norm_num)
  have := norm_nonneg z
  nlinarith

theorem collarWeight_eq_one {z : EuclideanSpace ℝ (Fin 2)} (hz : 59 / 64 ≤ ‖z‖) :
    collarWeight z = 1 := by
  apply Real.smoothTransition.one_of_one_le
  rw [le_div_iff₀ (by norm_num)]
  nlinarith

/-- The blend of the handle read `Γ` and the rim read `Ψ`. -/
def collarBlend (Γ Ψ : EuclideanSpace ℝ (Fin 2) × ℝ → EuclideanSpace ℝ (Fin 3))
    (q : EuclideanSpace ℝ (Fin 2) × ℝ) : EuclideanSpace ℝ (Fin 3) :=
  Γ q + collarWeight q.1 • (Ψ q - Γ q)

theorem collarBlend_of_eq {Γ Ψ : EuclideanSpace ℝ (Fin 2) × ℝ → EuclideanSpace ℝ (Fin 3)}
    {q : EuclideanSpace ℝ (Fin 2) × ℝ} (h : Ψ q = Γ q) : collarBlend Γ Ψ q = Γ q := by
  rw [collarBlend, h, sub_self, smul_zero, add_zero]

theorem collarBlend_of_le {Γ Ψ : EuclideanSpace ℝ (Fin 2) × ℝ → EuclideanSpace ℝ (Fin 3)}
    {q : EuclideanSpace ℝ (Fin 2) × ℝ} (h : ‖q.1‖ ≤ 235 / 256) : collarBlend Γ Ψ q = Γ q := by
  rw [collarBlend, collarWeight_eq_zero h, zero_smul, add_zero]

theorem collarBlend_of_ge {Γ Ψ : EuclideanSpace ℝ (Fin 2) × ℝ → EuclideanSpace ℝ (Fin 3)}
    {q : EuclideanSpace ℝ (Fin 2) × ℝ} (h : 59 / 64 ≤ ‖q.1‖) : collarBlend Γ Ψ q = Ψ q := by
  rw [collarBlend, collarWeight_eq_one h, one_smul, add_sub_cancel]

/-! ## The handle near the rim, read in the rim chart -/

theorem handleDiskMap_eq_rim (A : EuclideanSpace ℝ (Fin 2) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin 2))
    {P ρ : ℝ → ℝ} (hPρ : ∀ r, 1 - 11 / 128 ≤ r → r ≤ 1 → r * P (r ^ 2) = ρ (8 * (r - 1)))
    {z : EuclideanSpace ℝ (Fin 2)} (hz1 : 1 - 11 / 128 ≤ ‖z‖) (hz2 : ‖z‖ ≤ 1) :
    handleDiskMap A P z = ρ (8 * (‖z‖ - 1)) • A (planeOfCircle (planeUnit z)) := by
  have hz0 : z ≠ 0 := by
    intro h
    rw [h, norm_zero] at hz1
    norm_num at hz1
  rw [handleDiskMap_eq_of_mul A hz0 (hPρ _ hz1 hz2), planeOfCircle_planeUnit hz0, map_smul,
    smul_smul, div_eq_mul_inv]

/-! ## E2a: the ball-side collar -/

/-- **E2a (ball-side collar; self-contained).** In a ball chart `Bh` (the ball is
`Bh '' closedBall 0 1`) of the ball containing the end disk `b` of a handle `H`, the handle read
in product coordinates `(handleDiskMap A P z, endCoord b (σ s))` extends across `s = 0` to a
local diffeomorphism `G` into the chart, with values in the open unit ball for `s < 0`, equal to
the rim chart read in polar coordinates near the rim. -/
theorem exists_ballSideCollar (H : EdgeHandle W) (b : Bool)
    (χ : PartialDiffeomorph ((𝓡 1).prod 𝓘(ℝ, ℝ × ℝ)) W.model (Circle × (ℝ × ℝ)) W.Carrier ∞)
    (hχsrc : ∀ {p : Circle × (ℝ × ℝ)}, p ∈ χ.source ↔ p.2 ∈ rimBox 2)
    (Bh : PartialDiffeomorph (𝓡 3) W.model (EuclideanSpace ℝ (Fin 3)) W.Carrier ∞)
    (hBhsrc : Metric.closedBall 0 1 ⊆ Bh.source)
    (hsphere : ∀ {y}, y ∈ Bh.source → Bh y ∈ H.endDisk b → ‖y‖ = 1)
    (hdisk : H.endDisk b ⊆ Bh '' Metric.closedBall 0 1)
    (hHB : ∀ (w : ClosedCell 2) (t : Icc (0 : ℝ) 1),
      H.map (w, t) ∈ Bh '' Metric.closedBall 0 1 → (t : ℝ) = 0 ∨ (t : ℝ) = 1)
    {a : ℝ} (ha : 3 / 4 < a) (A : EuclideanSpace ℝ (Fin 2) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin 2))
    {ρ σ : ℝ → ℝ} (hσ : ContDiff ℝ ∞ σ) (hσ0 : σ 0 = 0) (hσd : ∀ y ∈ Ico 0 a, 0 < deriv σ y)
    (heq : ∀ (θ : Circle) (x y : ℝ) (w : ClosedCell 2) (t : Icc (0 : ℝ) 1),
      -a < x → x ≤ 0 → 0 ≤ y → y < a →
      (w : EuclideanSpace ℝ (Fin 2)) = ρ x • A (planeOfCircle θ) →
      (t : ℝ) = endCoord b (σ y) → χ (θ, (x, y)) = H.map (w, t))
    {P : ℝ → ℝ} (hP : ContDiff ℝ ∞ P) (hP1 : P 1 = 1) (hPpos : ∀ s, 0 ≤ s → s ≤ 1 → 0 < P s)
    (hPmono : ∀ r, 0 ≤ r → r ≤ 1 → 0 < deriv (fun r : ℝ => r * P (r ^ 2)) r)
    (hPρ : ∀ r, 1 - 11 / 128 ≤ r → r ≤ 1 → r * P (r ^ 2) = ρ (8 * (r - 1))) :
    ∃ η : ℝ, 0 < η ∧ ∃ G : EuclideanSpace ℝ (Fin 2) × ℝ → EuclideanSpace ℝ (Fin 3),
      ContDiffOn ℝ ∞ G (collarDomain η) ∧
      (∀ q ∈ collarDomain η, G q ∈ Bh.source) ∧
      (∀ q ∈ collarDomain η, Bijective (fderiv ℝ G q)) ∧
      (∀ q ∈ collarDomain η, 0 ≤ q.2 → ∀ (w : ClosedCell 2) (t : Icc (0 : ℝ) 1),
        (w : EuclideanSpace ℝ (Fin 2)) = handleDiskMap A P q.1 →
        (t : ℝ) = endCoord b (σ q.2) → Bh (G q) = H.map (w, t)) ∧
      (∀ q ∈ collarDomain η, 59 / 64 ≤ ‖q.1‖ →
        Bh (G q) = χ (planeUnit q.1, (8 * (‖q.1‖ - 1), q.2))) ∧
      (∀ q ∈ collarDomain η, q.2 < 0 → ‖G q‖ < 1) := by
  /- (0) the end disk lies in the chart target -/
  have hBt : H.endDisk b ⊆ Bh.target := by
    intro y hy
    obtain ⟨x, hx, rfl⟩ := hdisk hy
    exact Bh.map_source (hBhsrc hx)
  /- (1) a bound for the handle disk map on `‖z‖ ≤ 61/64` -/
  have hmono := strictMonoOn_handleRadius hP hPmono
  have hRh1 : 61 / 64 * P ((61 / 64) ^ 2) < 1 := by
    have := hmono ⟨by norm_num, by norm_num⟩ ⟨zero_le_one, le_rfl⟩ (show (61 / 64 : ℝ) < 1 by
      norm_num)
    simpa [hP1] using this
  have hRh0 : 0 ≤ 61 / 64 * P ((61 / 64) ^ 2) :=
    mul_nonneg (by norm_num) (hPpos _ (by positivity) (by norm_num)).le
  have hDMR : ∀ z : EuclideanSpace ℝ (Fin 2), ‖z‖ ≤ 61 / 64 →
      ‖handleDiskMap A P z‖ ≤ 61 / 64 * P ((61 / 64) ^ 2) := by
    intro z hz
    rw [norm_handleDiskMap A hPpos (hz.trans (by norm_num))]
    exact hmono.monotoneOn ⟨norm_nonneg z, hz.trans (by norm_num)⟩ ⟨by norm_num, by norm_num⟩ hz
  have hDM1 : ∀ z : EuclideanSpace ℝ (Fin 2), ‖z‖ ≤ 61 / 64 → ‖handleDiskMap A P z‖ ≤ 1 :=
    fun z hz => (hDMR z hz).trans hRh1.le
  /- (2) the handle extended across its end -/
  obtain ⟨δ, hδ, Gt, hGt, hGtv, hGtb⟩ := H.exists_endExtension b Bh hBt hRh0 hRh1
  /- (3) heights -/
  have hσmono : StrictMonoOn σ (Ico 0 a) := by
    apply strictMonoOn_of_deriv_pos (convex_Ico 0 a) hσ.continuous.continuousOn
    intro x hx
    rw [interior_Ico] at hx
    exact hσd x ⟨hx.1.le, hx.2⟩
  obtain ⟨η₀, hη₀, hη₀σ⟩ := Metric.continuousAt_iff.mp (hσ.continuous.continuousAt (x := 0))
    (min δ (1 / 2)) (lt_min hδ (by norm_num))
  set η₁ : ℝ := min η₀ (3 / 4) with hη₁def
  have hη₁ : 0 < η₁ := lt_min hη₀ (by norm_num)
  have hη₁a : η₁ < a := lt_of_le_of_lt (min_le_right _ _) ha
  have hσsmall : ∀ s, 0 ≤ s → s < η₁ → 0 ≤ σ s ∧ σ s < δ ∧ σ s < 1 / 2 := by
    intro s hs0 hs1
    have h1 : dist (σ s) (σ 0) < min δ (1 / 2) := by
      apply hη₀σ
      rw [Real.dist_eq, sub_zero, abs_of_nonneg hs0]
      exact lt_of_lt_of_le hs1 (min_le_left _ _)
    rw [hσ0, Real.dist_eq, sub_zero] at h1
    have h0 : 0 ≤ σ s := by
      rcases eq_or_lt_of_le hs0 with h | h
      · rw [← h, hσ0]
      · have := hσmono ⟨le_rfl, by linarith⟩ ⟨hs0, by linarith⟩ h
        rw [hσ0] at this
        exact this.le
    rw [abs_of_nonneg h0] at h1
    exact ⟨h0, lt_of_lt_of_le h1 (min_le_left _ _), lt_of_lt_of_le h1 (min_le_right _ _)⟩
  have hσpos : ∀ s, 0 < s → s < η₁ → 0 < σ s := by
    intro s hs0 hs1
    have := hσmono ⟨le_rfl, by linarith⟩ ⟨hs0.le, by linarith⟩ hs0
    rwa [hσ0] at this
  /- (4) the handle read `Γ` -/
  let T : ℝ → Icc (0 : ℝ) 1 := fun s => Set.projIcc 0 1 zero_le_one (endCoord b (σ s))
  have hT : ∀ s, 0 ≤ s → s < η₁ → (T s : ℝ) = endCoord b (σ s) := by
    intro s hs0 hs1
    have hmem : endCoord b (σ s) ∈ Icc (0 : ℝ) 1 :=
      endCoord_mem_Icc_of_mem b ⟨(hσsmall s hs0 hs1).1, by linarith [(hσsmall s hs0 hs1).2.2]⟩
    change ((Set.projIcc 0 1 zero_le_one (endCoord b (σ s)) : Icc (0 : ℝ) 1) : ℝ) = _
    rw [Set.projIcc_of_mem _ hmem]
  have hT0 : T 0 = iccEnd b := by
    apply Subtype.ext
    rw [hT 0 le_rfl hη₁, hσ0, endCoord_zero]
  let Γ : EuclideanSpace ℝ (Fin 2) × ℝ → EuclideanSpace ℝ (Fin 3) :=
    fun q => Gt (handleDiskMap A P q.1, endCoord b (σ q.2))
  have hΓ : ContDiff ℝ ∞ Γ :=
    hGt.comp (((contDiff_handleDiskMap A hP).comp contDiff_fst).prodMk
      ((contDiff_endCoord b).comp (hσ.comp contDiff_snd)))
  have hΓv : ∀ q : EuclideanSpace ℝ (Fin 2) × ℝ, ‖q.1‖ ≤ 61 / 64 → 0 ≤ q.2 → q.2 < η₁ →
      H.map (diskClamp (handleDiskMap A P q.1), T q.2) ∈ Bh.target ∧
      Γ q = Bh.symm (H.map (diskClamp (handleDiskMap A P q.1), T q.2)) := by
    intro q hq hs0 hs1
    have h := hGtv (diskClamp (handleDiskMap A P q.1)) (T q.2)
      (by rw [diskClamp_val (hDM1 q.1 hq)]; exact hDMR q.1 hq)
      (by
        rw [hT q.2 hs0 hs1, abs_endCoord_sub_iccEnd, abs_of_nonneg (hσsmall q.2 hs0 hs1).1]
        exact (hσsmall q.2 hs0 hs1).2.1)
    rw [diskClamp_val (hDM1 q.1 hq), hT q.2 hs0 hs1] at h
    exact h
  /- (5) the rim read `Ψ` -/
  let κ : EuclideanSpace ℝ (Fin 2) × ℝ → Circle × (ℝ × ℝ) :=
    fun q => (planeUnit q.1, (8 * (‖q.1‖ - 1), q.2))
  let Ψ : EuclideanSpace ℝ (Fin 2) × ℝ → EuclideanSpace ℝ (Fin 3) := fun q => Bh.symm (χ (κ q))
  have hrim : ∀ q : EuclideanSpace ℝ (Fin 2) × ℝ, 1 - 11 / 128 ≤ ‖q.1‖ → ‖q.1‖ ≤ 61 / 64 →
      0 ≤ q.2 → q.2 < η₁ → χ (κ q) = H.map (diskClamp (handleDiskMap A P q.1), T q.2) := by
    intro q h1 h2 hs0 hs1
    exact heq (planeUnit q.1) (8 * (‖q.1‖ - 1)) q.2 _ _ (by linarith) (by linarith) hs0
      (by linarith)
      (by rw [diskClamp_val (hDM1 q.1 h2), handleDiskMap_eq_rim A hPρ h1 (by linarith)])
      (hT q.2 hs0 hs1)
  have hΓΨ : ∀ q : EuclideanSpace ℝ (Fin 2) × ℝ, 1 - 11 / 128 ≤ ‖q.1‖ → ‖q.1‖ ≤ 61 / 64 →
      0 ≤ q.2 → q.2 < η₁ → Ψ q = Γ q := by
    intro q h1 h2 hs0 hs1
    change Bh.symm (χ (κ q)) = Γ q
    rw [hrim q h1 h2 hs0 hs1, (hΓv q h2 hs0 hs1).2]
  let A₀ : Set (EuclideanSpace ℝ (Fin 2) × ℝ) := {q | 233 / 256 < ‖q.1‖ ∧ ‖q.1‖ < 1 ∧ |q.2| < 1}
  have hA₀ : IsOpen A₀ :=
    (isOpen_lt continuous_const (continuous_norm.comp continuous_fst)).inter
      ((isOpen_lt (continuous_norm.comp continuous_fst) continuous_const).inter
        (isOpen_lt (continuous_abs.comp continuous_snd) continuous_const))
  have hκ : ∀ q ∈ A₀, ContMDiffAt 𝓘(ℝ, EuclideanSpace ℝ (Fin 2) × ℝ) ((𝓡 1).prod 𝓘(ℝ, ℝ × ℝ)) ∞
      κ q ∧ κ q ∈ χ.source := by
    intro q hq
    obtain ⟨h1, h2, h3⟩ := hq
    have hz : q.1 ≠ 0 := norm_pos_iff.mp (by linarith)
    refine ⟨?_, hχsrc.mpr ⟨?_, ?_⟩⟩
    · exact ((contMDiffOn_planeUnit.contMDiffAt (isOpen_ne.mem_nhds hz)).comp q
        contDiff_fst.contMDiff.contMDiffAt).prodMk ((contDiffAt_const.mul (((contDiffAt_norm ℝ hz).comp q
          contDiffAt_fst).sub contDiffAt_const)).prodMk contDiffAt_snd).contMDiffAt
    · change |8 * (‖q.1‖ - 1)| < 2
      rw [abs_lt]
      constructor <;> linarith
    · change |q.2| < 2
      linarith
  let UΨ : Set (EuclideanSpace ℝ (Fin 2) × ℝ) := A₀ ∩ (fun q => χ (κ q)) ⁻¹' Bh.target
  have hUΨ : IsOpen UΨ := by
    apply ContinuousOn.isOpen_inter_preimage _ hA₀ Bh.open_target
    intro q hq
    exact ((χ.contMDiffOn.contMDiffAt (χ.open_source.mem_nhds (hκ q hq).2)).comp q
      (hκ q hq).1).continuousAt.continuousWithinAt
  have hΨ : ∀ q ∈ UΨ, ContDiffAt ℝ ∞ Ψ q := by
    intro q hq
    exact contMDiffAt_iff_contDiffAt.mp
      ((Bh.symm.contMDiffOn.contMDiffAt (Bh.open_target.mem_nhds hq.2)).comp q
        ((χ.contMDiffOn.contMDiffAt (χ.open_source.mem_nhds (hκ q hq.1).2)).comp q
          (hκ q hq.1).1))
  let KΨ : Set (EuclideanSpace ℝ (Fin 2)) := {z | 1 - 11 / 128 ≤ ‖z‖ ∧ ‖z‖ ≤ 61 / 64}
  have hKΨ : IsCompact KΨ :=
    (isCompact_closedBall (0 : EuclideanSpace ℝ (Fin 2)) (61 / 64)).of_isClosed_subset
      ((isClosed_le continuous_const continuous_norm).inter
        (isClosed_le continuous_norm continuous_const))
      (fun z hz => mem_closedBall_zero_iff.mpr hz.2)
  have hKΨU : ∀ z ∈ KΨ, (z, (0 : ℝ)) ∈ UΨ := by
    intro z hz
    refine ⟨⟨by linarith [hz.1], by linarith [hz.2], by simp⟩, ?_⟩
    change χ (κ (z, 0)) ∈ Bh.target
    rw [hrim (z, 0) hz.1 hz.2 le_rfl hη₁, hT0]
    exact hBt ⟨_, rfl⟩
  obtain ⟨ηΨ, hηΨ, hηΨU⟩ := exists_slab_subset hKΨ hUΨ hKΨU
  /- (6) the blend `G` on the slab `D` -/
  set η₃ : ℝ := min η₁ ηΨ with hη₃def
  have hη₃ : 0 < η₃ := lt_min hη₁ hηΨ
  let G := collarBlend Γ Ψ
  let D : Set (EuclideanSpace ℝ (Fin 2) × ℝ) := {q | ‖q.1‖ < 61 / 64 ∧ |q.2| < η₃}
  have hD : IsOpen D :=
    (isOpen_lt (continuous_norm.comp continuous_fst) continuous_const).inter
      (isOpen_lt (continuous_abs.comp continuous_snd) continuous_const)
  have hDη₁ : ∀ q ∈ D, |q.2| < η₁ := fun q hq => lt_of_lt_of_le hq.2 (min_le_left _ _)
  have hDΨ : ∀ q ∈ D, 1 - 11 / 128 ≤ ‖q.1‖ → q ∈ UΨ := by
    intro q hq h1
    exact hηΨU q.1 ⟨h1, hq.1.le⟩ q.2 (lt_of_lt_of_le hq.2 (min_le_right _ _))
  have hGs : ContDiffOn ℝ ∞ G D := by
    intro q hq
    apply ContDiffAt.contDiffWithinAt
    by_cases hq0 : ‖q.1‖ < 235 / 256
    · have hev : G =ᶠ[𝓝 q] Γ := by
        filter_upwards [(isOpen_lt (continuous_norm.comp continuous_fst)
          continuous_const).mem_nhds hq0] with q' hq'
        exact collarBlend_of_le (le_of_lt hq')
      exact hΓ.contDiffAt.congr_of_eventuallyEq hev
    · have hU := hDΨ q hq (by linarith)
      exact hΓ.contDiffAt.add ((contDiff_collarWeight.contDiffAt.comp q contDiffAt_fst).smul
        ((hΨ q hU).sub hΓ.contDiffAt))
  have hGΓ : ∀ q ∈ D, 0 ≤ q.2 → G q = Γ q := by
    intro q hq hs0
    have hs1 : q.2 < η₁ := lt_of_le_of_lt (le_abs_self q.2) (hDη₁ q hq)
    by_cases h : ‖q.1‖ ≤ 235 / 256
    · exact collarBlend_of_le h
    · exact collarBlend_of_eq (hΓΨ q (by linarith) hq.1.le hs0 hs1)
  /- (7) the differential along `s = 0` -/
  have hΓb : ∀ z : EuclideanSpace ℝ (Fin 2), ‖z‖ ≤ 61 / 64 → Bijective (fderiv ℝ Γ (z, 0)) := by
    intro z hz
    have hφ : HasDerivAt (endCoord b ∘ σ) ((if b then -1 else 1) * deriv σ 0) 0 :=
      (hasDerivAt_endCoord b (σ 0)).comp 0 ((hσ.differentiable (by simp)) 0).hasDerivAt
    have hk : HasFDerivAt (Prod.map (handleDiskMap A P) (endCoord b ∘ σ))
        ((fderiv ℝ (handleDiskMap A P) z).prodMap
          ((1 : ℝ →L[ℝ] ℝ).smulRight ((if b then -1 else 1) * deriv σ 0))) (z, 0) :=
      HasFDerivAt.prodMap (z, 0)
        (((contDiff_handleDiskMap A hP).differentiable (by simp)) z).hasFDerivAt
        hφ.hasFDerivAt
    have hk0 : Prod.map (handleDiskMap A P) (endCoord b ∘ σ) (z, 0) =
        (handleDiskMap A P z, (iccEnd b : ℝ)) := by
      change (handleDiskMap A P z, endCoord b (σ 0)) = _
      rw [hσ0, endCoord_zero]
    have hGtd : HasFDerivAt Gt (fderiv ℝ Gt (handleDiskMap A P z, (iccEnd b : ℝ)))
        (Prod.map (handleDiskMap A P) (endCoord b ∘ σ) (z, 0)) := by
      rw [hk0]
      exact ((hGt.differentiable (by simp)) _).hasFDerivAt
    have hΓd := hGtd.comp (z, 0) hk
    have hΓeq : fderiv ℝ Γ (z, 0) = _ := hΓd.fderiv
    rw [hΓeq]
    have hc : (if b then -1 else 1) * deriv σ 0 ≠ 0 :=
      mul_ne_zero (by cases b <;> norm_num) (hσd 0 ⟨le_rfl, by linarith⟩).ne'
    exact (hGtb _ (hDMR z hz)).comp ((Prod.map_bijective).mpr
      ⟨bijective_fderiv_handleDiskMap A hP hPpos hPmono (hz.trans (by norm_num)),
        bijective_smulRight_one hc⟩)
  have hGd0 : ∀ z : EuclideanSpace ℝ (Fin 2), ‖z‖ < 61 / 64 →
      fderiv ℝ G (z, 0) = fderiv ℝ Γ (z, 0) := by
    intro z hz
    have hzD : (z, (0 : ℝ)) ∈ D := ⟨hz, by simpa using hη₃⟩
    have hcl : (z, (0 : ℝ)) ∈ closure (interior {q | q ∈ D ∧ 0 ≤ q.2}) := by
      have hsub : D ∩ {q | 0 < q.2} ⊆ interior {q | q ∈ D ∧ 0 ≤ q.2} :=
        interior_maximal (fun q hq => ⟨hq.1, hq.2.le⟩)
          (hD.inter (isOpen_lt continuous_const continuous_snd))
      apply closure_mono hsub
      have h0 : (0 : ℝ) ∈ closure (Ioo 0 η₃) := by
        rw [closure_Ioo hη₃.ne]
        exact ⟨le_rfl, hη₃.le⟩
      apply map_mem_closure (Continuous.prodMk_right z) h0
      intro s hs
      refine ⟨⟨hz, ?_⟩, hs.1⟩
      rw [abs_of_pos hs.1]
      exact hs.2
    exact Set.EqOn.fderiv_eq_of_mem_closure_interior (fun q hq => hGΓ q hq.1 hq.2) hcl
      ((hGs.contDiffAt (hD.mem_nhds hzD)).of_le (by simp)) (hΓ.contDiffAt.of_le (by simp))
  have hGb0 : ∀ z : EuclideanSpace ℝ (Fin 2), ‖z‖ < 61 / 64 → Bijective (fderiv ℝ G (z, 0)) :=
    fun z hz => (hGd0 z hz).symm ▸ hΓb z hz.le
  /- (8) the inward direction along `s = 0` -/
  have hsph : ∀ z : EuclideanSpace ℝ (Fin 2), ‖z‖ < 61 / 64 → ‖G (z, 0)‖ = 1 := by
    intro z hz
    have hzD : (z, (0 : ℝ)) ∈ D := ⟨hz, by simpa using hη₃⟩
    obtain ⟨hy, hΓy⟩ := hΓv (z, 0) hz.le le_rfl hη₁
    rw [hGΓ _ hzD le_rfl, hΓy]
    apply hsphere (Bh.map_target hy)
    rw [Bh.right_inv hy]
    change H.map (diskClamp (handleDiskMap A P z), T 0) ∈ H.endDisk b
    rw [hT0]
    exact ⟨_, rfl⟩
  have hout : ∀ z : EuclideanSpace ℝ (Fin 2), ‖z‖ < 61 / 64 → ∀ s ∈ Ioo 0 η₃,
      1 < ‖G (z, s)‖ := by
    intro z hz s hs
    have hs1 : s < η₁ := lt_of_lt_of_le hs.2 (min_le_left _ _)
    have hzD : (z, s) ∈ D := ⟨hz, by rw [abs_of_pos hs.1]; exact hs.2⟩
    obtain ⟨hy, hΓy⟩ := hΓv (z, s) hz.le hs.1.le hs1
    rw [hGΓ _ hzD hs.1.le, hΓy]
    by_contra hcon
    push Not at hcon
    have hmem : H.map (diskClamp (handleDiskMap A P z), T s) ∈ Bh '' Metric.closedBall 0 1 :=
      ⟨_, mem_closedBall_zero_iff.mpr hcon, Bh.right_inv hy⟩
    have hTs : (T s : ℝ) ∈ Ioo (0 : ℝ) 1 := by
      rw [hT s hs.1.le hs1]
      exact endCoord_mem_Ioo_of_mem b ⟨hσpos s hs.1 hs1, by linarith [(hσsmall s hs.1.le hs1).2.2]⟩
    rcases hHB _ _ hmem with h | h
    · rw [h] at hTs
      exact lt_irrefl _ hTs.1
    · rw [h] at hTs
      exact lt_irrefl _ hTs.2
  have hinner0 : ∀ z : EuclideanSpace ℝ (Fin 2), ‖z‖ < 61 / 64 →
      0 < inner ℝ (G (z, 0)) (fderiv ℝ G (z, 0) (0, 1)) := by
    intro z hz
    have hzD : (z, (0 : ℝ)) ∈ D := ⟨hz, by simpa using hη₃⟩
    apply inner_fderiv_pos_of_sphere
      ((hGs.contDiffAt (hD.mem_nhds hzD)).differentiableAt (by simp))
    · filter_upwards [(isOpen_lt continuous_norm continuous_const).mem_nhds hz] with z' hz'
      exact hsph z' hz'
    · filter_upwards [Ioo_mem_nhdsGT hη₃] with s hs
      exact hout z hz s hs
    · exact (hGb0 z hz).2
  /- (9) the good slab -/
  let V : Set (EuclideanSpace ℝ (Fin 2) × ℝ) := {q | q ∈ D ∧
    fderiv ℝ G q ∈ range ((↑) : ((EuclideanSpace ℝ (Fin 2) × ℝ) ≃L[ℝ]
      EuclideanSpace ℝ (Fin 3)) → (EuclideanSpace ℝ (Fin 2) × ℝ) →L[ℝ] EuclideanSpace ℝ (Fin 3)) ∧
        0 < inner ℝ (G q) (fderiv ℝ G q (0, 1))}
  have hV : IsOpen V := isOpen_bijective_inner_pos hD hGs
  have hKV : ∀ z ∈ Metric.closedBall (0 : EuclideanSpace ℝ (Fin 2)) (15 / 16), (z, (0 : ℝ)) ∈ V := by
    intro z hz
    have hz' : ‖z‖ < 61 / 64 := lt_of_le_of_lt (mem_closedBall_zero_iff.mp hz) (by norm_num)
    exact ⟨⟨hz', by simpa using hη₃⟩, mem_range_coe_of_bijective (hGb0 z hz'), hinner0 z hz'⟩
  obtain ⟨η, hη, hηV⟩ := exists_slab_subset (isCompact_closedBall _ _) hV hKV
  have hCV : ∀ q ∈ collarDomain η, q ∈ V := by
    intro q hq
    exact hηV q.1 (mem_closedBall_zero_iff.mpr hq.1.le) q.2 hq.2
  /- (10) the conclusions -/
  have hneg : ∀ q ∈ collarDomain η, q.2 < 0 → ‖G q‖ < 1 := by
    intro q hq hs
    have hz : ‖q.1‖ < 61 / 64 := lt_of_lt_of_le hq.1 (by norm_num)
    have hmem : ∀ s ∈ Ioo (-η) η, (q.1, s) ∈ V := fun s hs' =>
      hηV q.1 (mem_closedBall_zero_iff.mpr hq.1.le) s (abs_lt.mpr hs')
    exact norm_lt_one_of_inner_fderiv_pos
      (fun s hs' => (hGs.contDiffAt (hD.mem_nhds (hmem s hs').1)).differentiableAt (by simp))
      (fun s hs' => (hmem s hs').2.2) (hsph q.1 hz) ⟨(abs_lt.mp hq.2).1, hs⟩
  refine ⟨η, hη, G, hGs.mono (fun q hq => (hCV q hq).1), ?_,
    fun q hq => bijective_of_mem_range_coe (hCV q hq).2.1, ?_, ?_, hneg⟩
  · intro q hq
    rcases le_or_gt 0 q.2 with hs | hs
    · have hqD := (hCV q hq).1
      obtain ⟨hy, hΓy⟩ := hΓv q hqD.1.le hs (lt_of_le_of_lt (le_abs_self q.2) (hDη₁ q hqD))
      rw [hGΓ q hqD hs, hΓy]
      exact Bh.map_target hy
    · exact hBhsrc (mem_closedBall_zero_iff.mpr (hneg q hq hs).le)
  · intro q hq hs w t hw ht
    have hqD := (hCV q hq).1
    have hs1 : q.2 < η₁ := lt_of_le_of_lt (le_abs_self q.2) (hDη₁ q hqD)
    obtain ⟨hy, hΓy⟩ := hΓv q hqD.1.le hs hs1
    have hw' : w = diskClamp (handleDiskMap A P q.1) :=
      Subtype.ext (hw.trans (diskClamp_val (hDM1 q.1 hqD.1.le)).symm)
    have ht' : t = T q.2 := Subtype.ext (ht.trans (hT q.2 hs hs1).symm)
    rw [hGΓ q hqD hs, hΓy, hw', ht']
    exact Bh.right_inv hy
  · intro q hq h59
    have hqD := (hCV q hq).1
    have hU := hDΨ q hqD (by linarith)
    have hGq : G q = Ψ q := collarBlend_of_ge h59
    rw [hGq]
    exact Bh.right_inv hU.2


end GC.GraphManifold.Assembly
