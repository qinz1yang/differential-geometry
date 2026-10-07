/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Geometry.MinimalSurface.Boundary.ConormalGraphSide
import DifferentialGeometry.Geometry.HarmonicMap.TwoMapGraphContact

import Mathlib.Analysis.Complex.ReImTopology
import Mathlib.Analysis.Complex.RealDeriv
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Topology.OpenPartialHomeomorph.IsImage
import Mathlib.Topology.Constructions

noncomputable section

open Set Filter Metric Manifold DifferentialGeometry
open DifferentialGeometry.Geometry.ImmersedDiskDivergence.Within
open DifferentialGeometry.Geometry.ImmersedDiskDivergence.HalfDisk
open scoped Topology ContDiff Manifold

namespace DifferentialGeometry.Geometry

private theorem cauchy_halfdisk_uniqueMDiff :
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

private theorem cauchy_real_mem_halfdisk {t : ℝ} (ht : |t| < 1 / 16) :
    (t : ℂ) ∈ closedHalfDisk 0 (1 / 4) := by
  refine ⟨by simp, ?_⟩
  rw [Metric.mem_closedBall, dist_eq_norm, Complex.ofReal_zero, sub_zero,
    Complex.norm_real, Real.norm_eq_abs]
  linarith

/-- The actual positive source side of one fixed smooth planar inverse chart has
the real source seam as its relative frontier, with a regular parametrization. -/
private theorem planar_graph_half_domain
    (e : OpenPartialHomeomorph ℂ ℂ)
    (he : ContDiffOn ℝ ∞ e e.source)
    (heInv : ContDiffOn ℝ ∞ e.symm e.target)
    {O : Set ℂ} (hO : IsOpen O) (hOt : O ⊆ e.target)
    (h0 : (0 : ℂ) ∈ e.source) (he0 : e 0 ∈ O) :
    let S := O ∩ e '' (e.source ∩ {z : ℂ | 0 < z.im})
    IsOpen S ∧ S ⊆ O ∧ S.Nonempty ∧
      e 0 ∈ closure S ∩ closure (interior Sᶜ) ∧
      O ∩ frontier S = {y | y ∈ O ∧ (e.symm y).im = 0} ∧
      ∀ y ∈ O ∩ frontier S, ∃ τ : ℂ,
        HasDerivAt (fun t : ℝ => e (((e.symm y).re + t : ℝ) : ℂ)) τ 0 ∧
        τ ≠ 0 ∧ e (((e.symm y).re : ℝ) : ℂ) = y ∧
        ∀ᶠ t in 𝓝 0,
          e (((e.symm y).re + t : ℝ) : ℂ) ∈ O ∩ frontier S := by
  let U : Set ℂ := {z | 0 < z.im}
  let V : Set ℂ := {z | z.im < 0}
  let T : Set ℂ := e '' (e.source ∩ U)
  let N : Set ℂ := e '' (e.source ∩ V)
  let S : Set ℂ := O ∩ T
  have himage (W : Set ℂ) : e.IsImage W (e '' (e.source ∩ W)) := by
    intro z hz
    rw [e.image_source_inter_eq']
    simp only [mem_inter_iff, mem_preimage, e.map_source hz, e.left_inv hz, true_and]
  have hTimage : e.IsImage U T := himage U
  have hNimage : e.IsImage V N := himage V
  have hT : IsOpen T :=
    e.isOpen_image_source_inter (isOpen_lt continuous_const Complex.continuous_im)
  have hN : IsOpen N :=
    e.isOpen_image_source_inter (isOpen_lt Complex.continuous_im continuous_const)
  have hS : IsOpen S := hO.inter hT
  have h0U : (0 : ℂ) ∈ closure U := by
    simp only [U, Complex.closure_setOfPred_lt_im, mem_ofPred_eq, Complex.zero_im,
      le_refl]
  have h0V : (0 : ℂ) ∈ closure V := by
    simp only [V, Complex.closure_setOfPred_im_lt, mem_ofPred_eq, Complex.zero_im,
      le_refl]
  have h0T : e 0 ∈ closure T := (hTimage.closure.apply_mem_iff h0).mpr h0U
  have h0N : e 0 ∈ closure N := (hNimage.closure.apply_mem_iff h0).mpr h0V
  have h0S : e 0 ∈ closure S := hO.inter_closure ⟨he0, h0T⟩
  have hNc : N ⊆ Sᶜ := by
    rintro y ⟨z, ⟨hz, hzV⟩, rfl⟩ hyS
    have hzU : z ∈ U := (hTimage.apply_mem_iff hz).mp hyS.2
    change z.im < 0 at hzV
    change 0 < z.im at hzU
    exact lt_asymm hzV hzU
  have h0Other : e 0 ∈ closure (interior Sᶜ) :=
    closure_mono (interior_maximal hNc hN) h0N
  have hST : O ∩ frontier S = O ∩ frontier T := by
    simpa only [S, inter_comm] using (frontier_inter_open_inter (s := T) hO)
  have hfront : O ∩ frontier S = {y | y ∈ O ∧ (e.symm y).im = 0} := by
    rw [hST]
    ext y
    by_cases hy : y ∈ O
    · simp only [mem_inter_iff, mem_ofPred_eq, hy, true_and]
      simpa only [U, Complex.frontier_setOfPred_lt_im, mem_ofPred_eq] using
        (hTimage.frontier.symm_apply_mem_iff (hOt hy)).symm
    · simp only [mem_inter_iff, mem_ofPred_eq, hy, false_and]
  refine ⟨hS, inter_subset_left, closure_nonempty_iff.mp ⟨e 0, h0S⟩,
    ⟨h0S, h0Other⟩, hfront, ?_⟩
  intro y hy
  have hyO : y ∈ O := hy.1
  have hyim : (e.symm y).im = 0 := by
    have hy' := hy
    rw [hfront] at hy'
    exact hy'.2
  have hxreal : ((e.symm y).re : ℂ) = e.symm y := by
    apply Complex.ext
    · rfl
    · exact hyim.symm
  let l : ℝ → ℂ := fun t => (((e.symm y).re + t : ℝ) : ℂ)
  let γ : ℝ → ℂ := fun t => e (l t)
  have hl : HasDerivAt l (1 : ℂ) 0 :=
    ((hasDerivAt_id (0 : ℝ)).const_add (e.symm y).re).ofReal_comp
  have hl0 : l 0 = e.symm y := by
    simpa only [l, add_zero] using hxreal
  have hlsource : l 0 ∈ e.source := by
    rw [hl0]
    exact e.map_target (hOt hyO)
  have hdE : DifferentiableAt ℝ e (l 0) :=
    (he.contDiffAt (e.open_source.mem_nhds hlsource)).differentiableAt (by simp)
  let τ : ℂ := fderiv ℝ e (l 0) 1
  have hγ : HasDerivAt γ τ 0 := hdE.hasFDerivAt.comp_hasDerivAt 0 hl
  have hγ0 : γ 0 = y := by
    change e (l 0) = y
    rw [hl0, e.right_inv (hOt hyO)]
  have hdInv : DifferentiableAt ℝ e.symm y :=
    (heInv.contDiffAt (e.open_target.mem_nhds (hOt hyO))).differentiableAt (by simp)
  have hback : HasDerivAt (e.symm ∘ γ) (fderiv ℝ e.symm y τ) 0 :=
    hdInv.hasFDerivAt.comp_hasDerivAt_of_eq 0 hγ hγ0.symm
  have hls : ∀ᶠ t in 𝓝 0, l t ∈ e.source :=
    hl.continuousAt.eventually (e.open_source.mem_nhds hlsource)
  have hbackEq : l =ᶠ[𝓝 0] e.symm ∘ γ := by
    filter_upwards [hls] with t ht
    exact (e.left_inv ht).symm
  have hleft : HasDerivAt l (fderiv ℝ e.symm y τ) 0 :=
    hback.congr_of_eventuallyEq hbackEq
  have hτ : τ ≠ 0 := by
    intro hτ0
    have hderiv := hleft.unique hl
    rw [hτ0, map_zero] at hderiv
    exact zero_ne_one hderiv
  have hγO : ∀ᶠ t in 𝓝 0, γ t ∈ O :=
    hγ.continuousAt.eventually (by rw [hγ0]; exact hO.mem_nhds hyO)
  refine ⟨τ, hγ, hτ, ?_, ?_⟩
  · simpa only [γ, l, add_zero] using hγ0
  · filter_upwards [hls, hγO] with t ht htO
    rw [hfront]
    refine ⟨htO, ?_⟩
    change (e.symm (e (l t))).im = 0
    rw [e.left_inv ht]
    exact Complex.ofReal_im _

/-- A cancelled regular arc gives Cauchy data along the frontier of one fixed
projected side. The graph inverses are retained throughout; equality concerns
their height functions, not the raw source-coordinate differentials. -/
private theorem fixed_graph_frontier_cauchy_data_of_conormal_cancellation
    {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
    (g : SmoothRiemannianMetric 𝓘(ℝ, E) M)
    (UOuter UAlt : ℂ → M) {VOuter VAlt : Set ℂ}
    (hVOuter : IsOpen VOuter) (hVAlt : IsOpen VAlt)
    (h0Outer : (0 : ℂ) ∈ VOuter) (h0Alt : (0 : ℂ) ∈ VAlt)
    (hUOuter : ContMDiffOn 𝓘(ℝ, ℂ) 𝓘(ℝ, E) ∞ UOuter VOuter)
    (hUAlt : ContMDiffOn 𝓘(ℝ, ℂ) 𝓘(ℝ, E) ∞ UAlt VAlt)
    (hiOuter : ∀ t : ℝ, |t| < 1 / 16 → Function.Injective
      (mfderivWithin 𝓘(ℝ, ℂ) 𝓘(ℝ, E) UOuter (closedHalfDisk 0 (1 / 4)) (t : ℂ)))
    (hiAlt : ∀ t : ℝ, |t| < 1 / 16 → Function.Injective
      (mfderivWithin 𝓘(ℝ, ℂ) 𝓘(ℝ, E) UAlt (closedHalfDisk 0 (1 / 4)) (t : ℂ)))
    (htrace : ∀ t : ℝ, |t| < 1 / 16 → UOuter (t : ℂ) = UAlt (t : ℂ))
    (hcancel : ∀ t : ℝ, |t| < 1 / 16 →
      inwardConormalWithin g UOuter (closedHalfDisk 0 (1 / 4)) (t : ℂ) +
        tangentSpaceCast 𝓘(ℝ, E) (UAlt (t : ℂ)) (UOuter (t : ℂ))
          (inwardConormalWithin g UAlt (closedHalfDisk 0 (1 / 4)) (t : ℂ)) = 0)
    (p : M)
    (hchartOuter : ∀ z ∈ VOuter, UOuter z ∈ (chartAt E p).source)
    (hchartAlt : ∀ z ∈ VAlt, UAlt z ∈ (chartAt E p).source)
    (P : E →L[ℝ] ℂ) (height : E →L[ℝ] ℝ) (x0 : E)
    (hP : (P.comp (fderiv ℝ (fun z => extChartAt 𝓘(ℝ, E) p (UOuter z)) 0)).IsInvertible)
    (eOuter eAlt : OpenPartialHomeomorph ℂ ℂ)
    (heOuter : (eOuter : ℂ → ℂ) = fun z => P (extChartAt 𝓘(ℝ, E) p (UOuter z)))
    (heAlt : (eAlt : ℂ → ℂ) = fun z => P (extChartAt 𝓘(ℝ, E) p (UAlt z)))
    (h0eOuter : (0 : ℂ) ∈ eOuter.source) (h0eAlt : (0 : ℂ) ∈ eAlt.source)
    (heOuterV : eOuter.source ⊆ VOuter) (heAltV : eAlt.source ⊆ VAlt)
    (hInvOuter : ContDiffOn ℝ ∞ eOuter.symm eOuter.target)
    (hInvAlt : ContDiffOn ℝ ∞ eAlt.symm eAlt.target)
    {O0 : Set ℂ} (hO0 : IsOpen O0) (hy0 : eOuter 0 ∈ O0) :
    let hOuter : ℂ → ℝ := fun y => height
      (extChartAt 𝓘(ℝ, E) p (UOuter (eOuter.symm y)) - x0)
    let hAlt : ℂ → ℝ := fun y => height
      (extChartAt 𝓘(ℝ, E) p (UAlt (eAlt.symm y)) - x0)
    ∃ O : Set ℂ, IsOpen O ∧ eOuter 0 ∈ O ∧
      O ⊆ O0 ∩ (eOuter.target ∩ eAlt.target) ∧
      ContDiffOn ℝ ∞ hOuter O ∧ ContDiffOn ℝ ∞ hAlt O ∧
      let S := O ∩ eAlt '' (eAlt.source ∩ {z : ℂ | 0 < z.im})
      IsOpen S ∧ S ⊆ O ∧ S.Nonempty ∧
      eOuter 0 ∈ closure S ∩ closure (interior Sᶜ) ∧
      O ∩ frontier S = {y | y ∈ O ∧ (eAlt.symm y).im = 0} ∧
      (∀ y ∈ O, ‖eAlt.symm y‖ < 1 / 16 ∧ eAlt.symm y ∈ eOuter.source) ∧
      (∀ y ∈ S, (eOuter.symm y).im < 0) ∧
      (∀ y ∈ O ∩ frontier S, ∃ t : ℝ, |t| < 1 / 16 ∧
        eAlt.symm y = (t : ℂ) ∧ eOuter.symm y = (t : ℂ)) ∧
      (∀ y ∈ O ∩ frontier S, hOuter y = hAlt y ∧
        fderiv ℝ hOuter y = fderiv ℝ hAlt y) ∧
      (∀ y ∈ O ∩ frontier S, ∃ (γ : ℝ → ℂ) (τ : ℂ),
        γ 0 = y ∧ HasDerivAt γ τ 0 ∧ τ ≠ 0 ∧
          ∀ᶠ t in 𝓝 0, γ t ∈ O ∩ frontier S) := by
  intro hOuter hAlt
  have hzero : |(0 : ℝ)| < 1 / 16 := by norm_num
  have hvalue : UOuter 0 = UAlt 0 := htrace 0 hzero
  have hmarked : eOuter 0 = eAlt 0 := by
    rw [heOuter, heAlt]
    change P (extChartAt 𝓘(ℝ, E) p (UOuter 0)) =
      P (extChartAt 𝓘(ℝ, E) p (UAlt 0))
    rw [hvalue]
  have htraceNear (t : ℝ) (ht : |t| < 1 / 16) :
      (fun s : ℝ => UOuter (s : ℂ)) =ᶠ[𝓝 t] (fun s : ℝ => UAlt (s : ℂ)) := by
    have hs : {s : ℝ | |s| < 1 / 16} ∈ 𝓝 t :=
      (isOpen_lt continuous_abs continuous_const).mem_nhds ht
    filter_upwards [hs] with s hst
    exact htrace s hst
  have hXOuter : ContDiffOn ℝ ∞
      (fun z => extChartAt 𝓘(ℝ, E) p (UOuter z)) VOuter := by
    intro z hz
    exact (((contMDiffAt_extChartAt' (I := 𝓘(ℝ, E)) (n := ∞)
      (hchartOuter z hz)).comp z
      (hUOuter.contMDiffAt (hVOuter.mem_nhds hz))).contDiffAt).contDiffWithinAt
  have hXAlt : ContDiffOn ℝ ∞
      (fun z => extChartAt 𝓘(ℝ, E) p (UAlt z)) VAlt := by
    intro z hz
    exact (((contMDiffAt_extChartAt' (I := 𝓘(ℝ, E)) (n := ∞)
      (hchartAlt z hz)).comp z
      (hUAlt.contMDiffAt (hVAlt.mem_nhds hz))).contDiffAt).contDiffWithinAt
  have heAltSmooth : ContDiffOn ℝ ∞ eAlt eAlt.source := by
    rw [heAlt]
    exact P.contDiff.comp_contDiffOn (hXAlt.mono heAltV)
  let V : Set ℂ := eOuter.source ∩ Metric.ball (0 : ℂ) (1 / 16)
  have hV : IsOpen V := eOuter.open_source.inter Metric.isOpen_ball
  let O1 : Set ℂ := O0 ∩ (eAlt.target ∩ eAlt.symm ⁻¹' V)
  have hO1 : IsOpen O1 := hO0.inter
    (hInvAlt.continuousOn.isOpen_inter_preimage eAlt.open_target hV)
  have hInv0 : eAlt.symm (eOuter 0) = 0 := by
    rw [hmarked]
    exact eAlt.left_inv h0eAlt
  have h01 : eOuter 0 ∈ O1 := by
    refine ⟨hy0, ?_, ?_⟩
    · rw [hmarked]; exact eAlt.map_source h0eAlt
    · change eAlt.symm (eOuter 0) ∈ V
      rw [hInv0]
      exact ⟨h0eOuter, Metric.mem_ball_self (by norm_num)⟩
  obtain ⟨_, O, hO, h0O, hOO, hside⟩ :=
    exists_graph_side_reversal_of_trace_conormal_cancellation g
      (cauchy_real_mem_halfdisk hzero)
      (cauchy_halfdisk_uniqueMDiff _ (cauchy_real_mem_halfdisk hzero))
      (fun _ _ => rfl) (fun _ _ => rfl) hVOuter hVAlt h0Outer h0Alt
      hUOuter hUAlt (hiOuter 0 hzero) (hiAlt 0 hzero) (htraceNear 0 hzero)
      (hcancel 0 hzero) p hchartOuter hchartAlt P hP eOuter eAlt heOuter heAlt
      h0eOuter h0eAlt heOuterV heAltV hInvOuter hInvAlt hO1 h01
  have hOt : O ⊆ eAlt.target := fun y hy => (hOO hy).2.2
  have hOtOuter : O ⊆ eOuter.target := fun y hy => (hOO hy).2.1
  have h0AltO : eAlt 0 ∈ O := hmarked ▸ h0O
  obtain ⟨hS, hSO, hSne, happroach, hfront, hcurve⟩ :=
    planar_graph_half_domain eAlt heAltSmooth hInvAlt hO hOt h0eAlt h0AltO
  let S : Set ℂ := O ∩ eAlt '' (eAlt.source ∩ {z : ℂ | 0 < z.im})
  have hcontrol (y : ℂ) (hy : y ∈ O) :
      ‖eAlt.symm y‖ < 1 / 16 ∧ eAlt.symm y ∈ eOuter.source := by
    have hv : eAlt.symm y ∈ V := (hOO hy).1.2.2
    have hn : ‖eAlt.symm y‖ < 1 / 16 := by
      simpa only [Metric.mem_ball, dist_zero_right] using hv.2
    exact ⟨hn, hv.1⟩
  have hparameters (y : ℂ) (hy : y ∈ O ∩ frontier S) :
      ∃ t : ℝ, |t| < 1 / 16 ∧ eAlt.symm y = (t : ℂ) ∧
        eOuter.symm y = (t : ℂ) := by
    have him : (eAlt.symm y).im = 0 := by rw [hfront] at hy; exact hy.2
    let t := (eAlt.symm y).re
    have hreal : eAlt.symm y = (t : ℂ) := by
      apply Complex.ext
      · rfl
      · simpa only [Complex.ofReal_im] using him
    have ht : |t| < 1 / 16 := by
      have hn := (hcontrol y hy.1).1
      rw [hreal, Complex.norm_real, Real.norm_eq_abs] at hn
      exact hn
    have htOuter : (t : ℂ) ∈ eOuter.source := hreal ▸ (hcontrol y hy.1).2
    have hAltY : eAlt (t : ℂ) = y := by
      rw [← hreal]
      exact eAlt.right_inv (hOt hy.1)
    have heq : eOuter (t : ℂ) = eAlt (t : ℂ) := by
      rw [heOuter, heAlt]
      change P (extChartAt 𝓘(ℝ, E) p (UOuter (t : ℂ))) =
        P (extChartAt 𝓘(ℝ, E) p (UAlt (t : ℂ)))
      rw [htrace t ht]
    refine ⟨t, ht, hreal, ?_⟩
    rw [← hAltY, ← heq]
    exact eOuter.left_inv htOuter
  have hhOuter : ContDiffOn ℝ ∞ hOuter O := by
    exact height.contDiff.comp_contDiffOn
      (((hXOuter.comp hInvOuter (fun y hy => heOuterV (eOuter.map_target hy))).sub
        contDiffOn_const).mono hOtOuter)
  have hhAlt : ContDiffOn ℝ ∞ hAlt O := by
    exact height.contDiff.comp_contDiffOn
      (((hXAlt.comp hInvAlt (fun y hy => heAltV (eAlt.map_target hy))).sub
        contDiffOn_const).mono hOt)
  refine ⟨O, hO, h0O, fun y hy => ⟨(hOO hy).1.1, (hOO hy).2⟩,
    hhOuter, hhAlt, hS, hSO, hSne, ?_, hfront, hcontrol, hside, hparameters, ?_, ?_⟩
  · simpa only [hmarked] using happroach
  · intro y hy
    obtain ⟨t, ht, hAltT, hOuterT⟩ := hparameters y hy
    have htAlt : (t : ℂ) ∈ eAlt.source := hAltT ▸ eAlt.map_target (hOt hy.1)
    have htOuter : (t : ℂ) ∈ eOuter.source := hOuterT ▸ eOuter.map_target (hOtOuter hy.1)
    have hdOuter := (hUOuter.contMDiffAt
      (hVOuter.mem_nhds (heOuterV htOuter))).mdifferentiableAt (by simp)
    have hdAlt := (hUAlt.contMDiffAt
      (hVAlt.mem_nhds (heAltV htAlt))).mdifferentiableAt (by simp)
    have hrange := (mfderiv_range_eq_of_trace_conormal_cancellation g
      (cauchy_real_mem_halfdisk ht)
      (cauchy_halfdisk_uniqueMDiff _ (cauchy_real_mem_halfdisk ht))
      (fun _ _ => rfl) (fun _ _ => rfl) hdOuter hdAlt
      (hiOuter t ht) (hiAlt t ht) (htraceNear t ht) (hcancel t ht)).2.2
    have hpyOuter : P (extChartAt 𝓘(ℝ, E) p (UOuter (t : ℂ))) = y := by
      change (fun z => P (extChartAt 𝓘(ℝ, E) p (UOuter z))) (t : ℂ) = y
      rw [← heOuter, ← hOuterT]
      exact eOuter.right_inv (hOtOuter hy.1)
    have hpyAlt : P (extChartAt 𝓘(ℝ, E) p (UAlt (t : ℂ))) = y := by
      rw [← htrace t ht]
      exact hpyOuter
    have hdiOuter : DifferentiableAt ℝ eOuter.symm
        (P (extChartAt 𝓘(ℝ, E) p (UOuter (t : ℂ)))) := by
      rw [hpyOuter]
      exact (hInvOuter.contDiffAt (eOuter.open_target.mem_nhds (hOtOuter hy.1))).differentiableAt
        (by simp)
    have hdiAlt : DifferentiableAt ℝ eAlt.symm
        (P (extChartAt 𝓘(ℝ, E) p (UAlt (t : ℂ)))) := by
      rw [hpyAlt]
      exact (hInvAlt.contDiffAt (eAlt.open_target.mem_nhds (hOt hy.1))).differentiableAt
        (by simp)
    have hjets := chart_height_value_fderiv_eq_of_tangent_range_le p P height
      eOuter eAlt heOuter heAlt htOuter htAlt hdOuter hdAlt
      (hchartOuter _ (heOuterV htOuter)) hdiOuter hdiAlt (htrace t ht) hrange.ge x0
    change hOuter (P (extChartAt 𝓘(ℝ, E) p (UOuter (t : ℂ)))) =
        hAlt (P (extChartAt 𝓘(ℝ, E) p (UOuter (t : ℂ)))) ∧
      fderiv ℝ hOuter (P (extChartAt 𝓘(ℝ, E) p (UOuter (t : ℂ)))) =
        fderiv ℝ hAlt (P (extChartAt 𝓘(ℝ, E) p (UOuter (t : ℂ)))) at hjets
    simpa only [hpyOuter] using hjets
  · intro y hy
    obtain ⟨τ, hτ, hτne, hyvalue, hnear⟩ := hcurve y hy
    exact ⟨fun t : ℝ => eAlt (((eAlt.symm y).re + t : ℝ) : ℂ), τ,
      by simpa only [add_zero] using hyvalue, hτ, hτne, hnear⟩

/-- Choose graph inverses once, then retain them in the side, its frontier and
the Cauchy data of a cancelled regular arc. The original chart also contains
every interpolation segment between the two literal graph maps. -/
theorem exists_fixed_graph_frontier_cauchy_data_of_conormal_cancellation
    {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
    (g : SmoothRiemannianMetric 𝓘(ℝ, E) M)
    (UOuter UAlt : ℂ → M) {VOuter VAlt : Set ℂ}
    (hVOuter : IsOpen VOuter) (hVAlt : IsOpen VAlt)
    (h0Outer : (0 : ℂ) ∈ VOuter) (h0Alt : (0 : ℂ) ∈ VAlt)
    (hUOuter : ContMDiffOn 𝓘(ℝ, ℂ) 𝓘(ℝ, E) ∞ UOuter VOuter)
    (hUAlt : ContMDiffOn 𝓘(ℝ, ℂ) 𝓘(ℝ, E) ∞ UAlt VAlt)
    (hiOuter : ∀ t : ℝ, |t| < 1 / 16 → Function.Injective
      (mfderivWithin 𝓘(ℝ, ℂ) 𝓘(ℝ, E) UOuter (closedHalfDisk 0 (1 / 4)) (t : ℂ)))
    (hiAlt : ∀ t : ℝ, |t| < 1 / 16 → Function.Injective
      (mfderivWithin 𝓘(ℝ, ℂ) 𝓘(ℝ, E) UAlt (closedHalfDisk 0 (1 / 4)) (t : ℂ)))
    (htrace : ∀ t : ℝ, |t| < 1 / 16 → UOuter (t : ℂ) = UAlt (t : ℂ))
    (hcancel : ∀ t : ℝ, |t| < 1 / 16 →
      inwardConormalWithin g UOuter (closedHalfDisk 0 (1 / 4)) (t : ℂ) +
        tangentSpaceCast 𝓘(ℝ, E) (UAlt (t : ℂ)) (UOuter (t : ℂ))
          (inwardConormalWithin g UAlt (closedHalfDisk 0 (1 / 4)) (t : ℂ)) = 0)
    (p : M)
    (hchartOuter : ∀ z ∈ VOuter, UOuter z ∈ (chartAt E p).source)
    (hchartAlt : ∀ z ∈ VAlt, UAlt z ∈ (chartAt E p).source)
    (P : E →L[ℝ] ℂ) (height : E →L[ℝ] ℝ) (x0 : E)
    (hP : (P.comp (fderiv ℝ (fun z => extChartAt 𝓘(ℝ, E) p (UOuter z)) 0)).IsInvertible)
    {O0 : Set ℂ} (hO0 : IsOpen O0)
    (hy0 : P (extChartAt 𝓘(ℝ, E) p (UOuter 0)) ∈ O0) :
    ∃ (eOuter eAlt : OpenPartialHomeomorph ℂ ℂ) (O : Set ℂ),
      (0 : ℂ) ∈ eOuter.source ∧ (0 : ℂ) ∈ eAlt.source ∧
      eOuter.source ⊆ VOuter ∧ eAlt.source ⊆ VAlt ∧
      (eOuter : ℂ → ℂ) = (fun z => P (extChartAt 𝓘(ℝ, E) p (UOuter z))) ∧
      (eAlt : ℂ → ℂ) = (fun z => P (extChartAt 𝓘(ℝ, E) p (UAlt z))) ∧
      ContDiffOn ℝ ∞ eOuter.symm eOuter.target ∧
      ContDiffOn ℝ ∞ eAlt.symm eAlt.target ∧
      IsOpen O ∧ eOuter 0 ∈ O ∧ O ⊆ O0 ∩ (eOuter.target ∩ eAlt.target) ∧
      (∀ y ∈ O, ∀ t ∈ Icc (0 : ℝ) 1,
        (1 - t) • extChartAt 𝓘(ℝ, E) p (UAlt (eAlt.symm y)) +
          t • extChartAt 𝓘(ℝ, E) p (UOuter (eOuter.symm y)) ∈
            (extChartAt 𝓘(ℝ, E) p).target) ∧
      let hOuter : ℂ → ℝ := fun y => height
        (extChartAt 𝓘(ℝ, E) p (UOuter (eOuter.symm y)) - x0)
      let hAlt : ℂ → ℝ := fun y => height
        (extChartAt 𝓘(ℝ, E) p (UAlt (eAlt.symm y)) - x0)
      ContDiffOn ℝ ∞ hOuter O ∧ ContDiffOn ℝ ∞ hAlt O ∧
      let S := O ∩ eAlt '' (eAlt.source ∩ {z : ℂ | 0 < z.im})
      IsOpen S ∧ S ⊆ O ∧ S.Nonempty ∧
      eOuter 0 ∈ closure S ∩ closure (interior Sᶜ) ∧
      O ∩ frontier S = {y | y ∈ O ∧ (eAlt.symm y).im = 0} ∧
      (∀ y ∈ O, ‖eAlt.symm y‖ < 1 / 16 ∧ eAlt.symm y ∈ eOuter.source) ∧
      (∀ y ∈ S, (eOuter.symm y).im < 0) ∧
      (∀ y ∈ O ∩ frontier S, ∃ t : ℝ, |t| < 1 / 16 ∧
        eAlt.symm y = (t : ℂ) ∧ eOuter.symm y = (t : ℂ)) ∧
      (∀ y ∈ O ∩ frontier S, hOuter y = hAlt y ∧
        fderiv ℝ hOuter y = fderiv ℝ hAlt y) ∧
      (∀ y ∈ O ∩ frontier S, ∃ (γ : ℝ → ℂ) (τ : ℂ),
        γ 0 = y ∧ HasDerivAt γ τ 0 ∧ τ ≠ 0 ∧
          ∀ᶠ t in 𝓝 0, γ t ∈ O ∩ frontier S) := by
  have hz : |(0 : ℝ)| < 1 / 16 := by norm_num
  have hnear : (fun t : ℝ => UOuter (t : ℂ)) =ᶠ[𝓝 0]
      (fun t : ℝ => UAlt (t : ℂ)) := by
    have hs : {t : ℝ | |t| < 1 / 16} ∈ 𝓝 0 :=
      (isOpen_lt continuous_abs continuous_const).mem_nhds hz
    filter_upwards [hs] with t ht
    exact htrace t ht
  obtain ⟨eOuter, eAlt, O1, h0eOuter, h0eAlt, heOuterV, heAltV,
      heOuter, heAlt, hInvOuter, hInvAlt, hO1, hy1, _, hsegment⟩ :=
    exists_chart_graph_germs_of_trace_conormal_cancellation g
      (cauchy_real_mem_halfdisk hz)
      (cauchy_halfdisk_uniqueMDiff _ (cauchy_real_mem_halfdisk hz))
      (fun _ _ => rfl) (fun _ _ => rfl) hVOuter hVAlt h0Outer h0Alt
      hUOuter hUAlt (hiOuter 0 hz) (hiAlt 0 hz) hnear (hcancel 0 hz)
      p hchartOuter hchartAlt P hP
  have hmark : eOuter 0 = P (extChartAt 𝓘(ℝ, E) p (UOuter 0)) := congrFun heOuter 0
  obtain ⟨O, hO, h0O, hOO, hhOuter, hhAlt, hrest⟩ :=
    fixed_graph_frontier_cauchy_data_of_conormal_cancellation g UOuter UAlt
      hVOuter hVAlt h0Outer h0Alt hUOuter hUAlt hiOuter hiAlt htrace hcancel
      p hchartOuter hchartAlt P height x0 hP eOuter eAlt heOuter heAlt
      h0eOuter h0eAlt heOuterV heAltV hInvOuter hInvAlt (hO0.inter hO1)
      (by rw [hmark]; exact ⟨hy0, hy1⟩)
  refine ⟨eOuter, eAlt, O, h0eOuter, h0eAlt, heOuterV, heAltV,
    heOuter, heAlt, hInvOuter, hInvAlt, hO, h0O,
    fun y hy => ⟨(hOO hy).1.1, (hOO hy).2⟩,
    fun y hy t ht => hsegment y (hOO hy).1.2 t ht, hhOuter, hhAlt, hrest⟩

end DifferentialGeometry.Geometry
