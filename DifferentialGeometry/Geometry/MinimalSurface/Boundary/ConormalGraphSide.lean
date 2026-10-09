/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Geometry.MinimalSurface.Boundary.ConormalTangentPlane
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Analysis.Calculus.Deriv.MeanValue

set_option autoImplicit false
noncomputable section

open Set Filter Metric Manifold DifferentialGeometry
open DifferentialGeometry.Geometry.ImmersedDiskDivergence.Within
open DifferentialGeometry.Geometry.ImmersedDiskDivergence.HalfDisk
open scoped Topology ContDiff Manifold

namespace DifferentialGeometry.Geometry

private theorem side_mfderivWithin_congr
    {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [TopologicalSpace M] [ChartedSpace E M]
    {F U : ℂ → M} {H : Set ℂ} (heq : EqOn F U H) {z : ℂ} (hz : z ∈ H) :
    (show ℂ →L[ℝ] E from mfderivWithin 𝓘(ℝ, ℂ) 𝓘(ℝ, E) F H z) =
      (show ℂ →L[ℝ] E from mfderivWithin 𝓘(ℝ, ℂ) 𝓘(ℝ, E) U H z) := by
  have h := mfderivWithin_congr_of_mem (I := 𝓘(ℝ, ℂ)) (I' := 𝓘(ℝ, E)) heq hz
  ext v
  simpa only [ContinuousLinearMap.comp_apply] using!
    congrArg (fun D : ℂ →L[ℝ] E => D v) h

private theorem transition_im_neg_of_opposite_conormals
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (B : E →L[ℝ] E →L[ℝ] ℝ) (DOuter DAlt : ℂ →L[ℝ] E)
    (L : ℂ →L[ℝ] ℂ) (νOuter νAlt : E)
    (hfactor : DOuter.comp L = DAlt)
    (horth : B νOuter (DOuter 1) = 0)
    (hposOuter : 0 < B νOuter (DOuter Complex.I))
    (hposAlt : 0 < B νAlt (DAlt Complex.I))
    (hcancel : νOuter + νAlt = 0) :
    (L Complex.I).im < 0 := by
  have hν : νAlt = -νOuter := by
    calc
      νAlt = νOuter + νAlt - νOuter := (add_sub_cancel_left νOuter νAlt).symm
      _ = -νOuter := by rw [hcancel, zero_sub]
  have hnegative : B νOuter (DAlt Complex.I) < 0 := by
    rw [hν, map_neg] at hposAlt
    change 0 < -(B νOuter (DAlt Complex.I)) at hposAlt
    linarith
  have hLI : L Complex.I = (L Complex.I).re • (1 : ℂ) +
      (L Complex.I).im • Complex.I := by
    simpa only [Complex.real_smul, mul_one] using (Complex.re_add_im (L Complex.I)).symm
  have happly : DAlt Complex.I = DOuter (L Complex.I) :=
    (congrArg (fun D : ℂ →L[ℝ] E => D Complex.I) hfactor).symm
  have hmul : B νOuter (DAlt Complex.I) =
      (L Complex.I).im * B νOuter (DOuter Complex.I) := by
    rw [happly]
    conv_lhs => rw [hLI]
    simp only [map_add, map_smul, smul_eq_mul, horth, mul_zero, zero_add]
  rw [hmul] at hnegative
  by_contra hn
  have hnonneg := mul_nonneg (le_of_not_gt hn) hposOuter.le
  exact (not_lt_of_ge hnonneg) hnegative

private theorem exists_pos_radius_im_neg_of_real_trace
    {V : Set ℂ} (hV : IsOpen V) (h0V : (0 : ℂ) ∈ V)
    {K : ℂ → ℂ} (hK : ContDiffOn ℝ 1 K V)
    (htrace : (fun t : ℝ => (K (t : ℂ)).im) =ᶠ[𝓝 0] (fun _ => 0))
    (hneg : (fderiv ℝ K 0 Complex.I).im < 0) :
    ∃ r : ℝ, 0 < r ∧ ball (0 : ℂ) r ⊆ V ∧
      ∀ z ∈ ball (0 : ℂ) r, 0 < z.im → (K z).im < 0 := by
  have hDK : ContinuousAt (fderiv ℝ K) (0 : ℂ) :=
    (hK.continuousOn_fderiv_of_isOpen hV le_rfl).continuousAt (hV.mem_nhds h0V)
  have hd : ContinuousAt (fun z : ℂ => (fderiv ℝ K z Complex.I).im) 0 :=
    Complex.continuous_im.continuousAt.comp (hDK.clm_apply continuousAt_const)
  have hnegative : ∀ᶠ z in 𝓝 (0 : ℂ), (fderiv ℝ K z Complex.I).im < 0 :=
    hd (Iio_mem_nhds hneg)
  have hreal : ∀ᶠ z in 𝓝 (0 : ℂ), (K (z.re : ℂ)).im = 0 :=
    (Complex.continuous_re.tendsto (0 : ℂ)).eventually htrace
  have hcontrol : ∀ᶠ z in 𝓝 (0 : ℂ),
      z ∈ V ∧ (fderiv ℝ K z Complex.I).im < 0 ∧ (K (z.re : ℂ)).im = 0 := by
    filter_upwards [hV.mem_nhds h0V, hnegative, hreal] with z hz hdz htz
    exact ⟨hz, hdz, htz⟩
  obtain ⟨r, hr, hball⟩ := Metric.mem_nhds_iff.mp hcontrol
  refine ⟨r, hr, fun z hz => (hball hz).1, ?_⟩
  intro z hz hzim
  let x : ℂ := (z.re : ℂ)
  have hx : x ∈ ball (0 : ℂ) r := by
    rw [Metric.mem_ball, dist_zero_right] at hz ⊢
    calc
      ‖x‖ = |z.re| := by simp only [x, Complex.norm_real, Real.norm_eq_abs]
      _ ≤ ‖z‖ := Complex.abs_re_le_norm z
      _ < r := hz
  let η := ContinuousAffineMap.lineMap (R := ℝ) x z
  have hηball : MapsTo η (Icc (0 : ℝ) 1) (ball (0 : ℂ) r) :=
    (convex_ball (0 : ℂ) r).mapsTo_lineMap hx hz
  have hηV : MapsTo η (Icc (0 : ℝ) 1) V :=
    fun t ht => (hball (hηball ht)).1
  have hderiv (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) :
      HasDerivAt (fun s : ℝ => (K (η s)).im)
        (fderiv ℝ K (η t) (z - x)).im t := by
    have hηd : HasDerivAt η (z - x) t := AffineMap.hasDerivAt_lineMap
    have hKd : DifferentiableAt ℝ K (η t) :=
      (hK.contDiffAt (hV.mem_nhds (hηV ht))).differentiableAt one_ne_zero
    exact Complex.imCLM.hasFDerivAt.comp_hasDerivAt t
      (hKd.hasFDerivAt.comp_hasDerivAt t hηd)
  have hdelta : z - x = z.im • Complex.I := by
    apply Complex.ext <;> simp [x, Complex.real_smul]
  have hanti : StrictAntiOn (fun t : ℝ => (K (η t)).im) (Icc (0 : ℝ) 1) := by
    apply strictAntiOn_of_deriv_neg (convex_Icc (0 : ℝ) 1)
    · exact fun t ht => (hderiv t ht).continuousAt.continuousWithinAt
    · intro t ht
      have ht' : t ∈ Icc (0 : ℝ) 1 := interior_subset ht
      rw [(hderiv t ht').deriv]
      have heval : (fderiv ℝ K (η t) (z - x)).im =
          z.im * (fderiv ℝ K (η t) Complex.I).im := by
        rw [hdelta, map_smul]
        change Complex.imCLM (z.im • fderiv ℝ K (η t) Complex.I) = _
        rw [map_smul]
        rfl
      rw [heval]
      exact mul_neg_of_pos_of_neg hzim (hball (hηball ht')).2.1
  have hzero : (K x).im = 0 := (hball hz).2.2
  have hlt := hanti (show (0 : ℝ) ∈ Icc 0 1 from ⟨le_rfl, zero_le_one⟩)
    (show (1 : ℝ) ∈ Icc 0 1 from ⟨zero_le_one, le_rfl⟩) zero_lt_one
  simpa only [η, ContinuousAffineMap.coe_lineMap_eq, AffineMap.lineMap_apply_one,
    AffineMap.lineMap_apply_zero, hzero] using hlt

/-- Opposite actual inward conormals reverse the transverse side in the fixed
common graph coordinates. The same graph inverses are retained, and the common
target can be shrunk inside any prescribed open neighborhood. This is a local
geometric implication of the supplied no-fold output, not an immersion or
coincidence theorem for an alternate disk. -/
theorem exists_graph_side_reversal_of_trace_conormal_cancellation
    {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [TopologicalSpace M] [ChartedSpace E M]
    [IsManifold 𝓘(ℝ, E) ∞ M]
    (g : SmoothRiemannianMetric 𝓘(ℝ, E) M)
    {FOuter FAlt UOuter UAlt : ℂ → M} {H VOuter VAlt : Set ℂ}
    (h0H : (0 : ℂ) ∈ H) (huniq : UniqueMDiffWithinAt 𝓘(ℝ, ℂ) H 0)
    (heqOuter : EqOn FOuter UOuter H) (heqAlt : EqOn FAlt UAlt H)
    (hVOuter : IsOpen VOuter) (hVAlt : IsOpen VAlt)
    (h0Outer : (0 : ℂ) ∈ VOuter) (h0Alt : (0 : ℂ) ∈ VAlt)
    (hUOuter : ContMDiffOn 𝓘(ℝ, ℂ) 𝓘(ℝ, E) ∞ UOuter VOuter)
    (hUAlt : ContMDiffOn 𝓘(ℝ, ℂ) 𝓘(ℝ, E) ∞ UAlt VAlt)
    (hiOuter : Function.Injective (mfderivWithin 𝓘(ℝ, ℂ) 𝓘(ℝ, E) FOuter H 0))
    (hiAlt : Function.Injective (mfderivWithin 𝓘(ℝ, ℂ) 𝓘(ℝ, E) FAlt H 0))
    (htrace : (fun t : ℝ => UOuter (t : ℂ)) =ᶠ[𝓝 0]
      (fun t : ℝ => UAlt (t : ℂ)))
    (hcancel : inwardConormalWithin g FOuter H 0 +
      tangentSpaceCast 𝓘(ℝ, E) (FAlt 0) (FOuter 0)
        (inwardConormalWithin g FAlt H 0) = 0)
    (p : M)
    (hchartOuter : ∀ z ∈ VOuter, UOuter z ∈ (chartAt E p).source)
    (hchartAlt : ∀ z ∈ VAlt, UAlt z ∈ (chartAt E p).source)
    (P : E →L[ℝ] ℂ)
    (hP : (P.comp (fderiv ℝ (fun z => extChartAt 𝓘(ℝ, E) p (UOuter z)) 0)).IsInvertible)
    (eOuter eAlt : OpenPartialHomeomorph ℂ ℂ)
    (heOuter : (eOuter : ℂ → ℂ) = fun z => P (extChartAt 𝓘(ℝ, E) p (UOuter z)))
    (heAlt : (eAlt : ℂ → ℂ) = fun z => P (extChartAt 𝓘(ℝ, E) p (UAlt z)))
    (h0eOuter : (0 : ℂ) ∈ eOuter.source) (h0eAlt : (0 : ℂ) ∈ eAlt.source)
    (heOuterV : eOuter.source ⊆ VOuter) (heAltV : eAlt.source ⊆ VAlt)
    (hInvOuter : ContDiffOn ℝ ∞ eOuter.symm eOuter.target)
    (hInvAlt : ContDiffOn ℝ ∞ eAlt.symm eAlt.target)
    {O0 : Set ℂ} (hO0 : IsOpen O0) (hy0 : eOuter 0 ∈ O0) :
    (fderiv ℝ (eOuter.symm ∘ eAlt) 0 Complex.I).im < 0 ∧
    ∃ O : Set ℂ, IsOpen O ∧ eOuter 0 ∈ O ∧
      O ⊆ O0 ∩ (eOuter.target ∩ eAlt.target) ∧
      ∀ y ∈ O ∩ eAlt '' (eAlt.source ∩ {z : ℂ | 0 < z.im}),
        (eOuter.symm y).im < 0 := by
  let XOuter : ℂ → E := fun z => extChartAt 𝓘(ℝ, E) p (UOuter z)
  let XAlt : ℂ → E := fun z => extChartAt 𝓘(ℝ, E) p (UAlt z)
  let DOuter : ℂ →L[ℝ] E := mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, E) UOuter 0
  let DAlt : ℂ →L[ℝ] E := mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, E) UAlt 0
  let K : ℂ → ℂ := eOuter.symm ∘ eAlt
  let L : ℂ →L[ℝ] ℂ := fderiv ℝ K 0
  have hdOuter := (hUOuter.contMDiffAt (hVOuter.mem_nhds h0Outer)).mdifferentiableAt
    (by simp)
  have hdAlt := (hUAlt.contMDiffAt (hVAlt.mem_nhds h0Alt)).mdifferentiableAt
    (by simp)
  have hvalue : UOuter 0 = UAlt 0 := htrace.eq_of_nhds
  have hmarked : eOuter 0 = eAlt 0 := by
    rw [heOuter, heAlt]
    change P (extChartAt 𝓘(ℝ, E) p (UOuter 0)) =
      P (extChartAt 𝓘(ℝ, E) p (UAlt 0))
    rw [hvalue]
  have hK0 : K 0 = 0 := by
    change eOuter.symm (eAlt 0) = 0
    rw [← hmarked]
    exact eOuter.left_inv h0eOuter
  have hXOuter : ContDiffOn ℝ ∞ XOuter VOuter := by
    intro z hz
    exact (((contMDiffAt_extChartAt' (I := 𝓘(ℝ, E)) (n := ∞)
      (hchartOuter z hz)).comp z
      (hUOuter.contMDiffAt (hVOuter.mem_nhds hz))).contDiffAt).contDiffWithinAt
  have hXAlt : ContDiffOn ℝ ∞ XAlt VAlt := by
    intro z hz
    exact (((contMDiffAt_extChartAt' (I := 𝓘(ℝ, E)) (n := ∞)
      (hchartAlt z hz)).comp z
      (hUAlt.contMDiffAt (hVAlt.mem_nhds hz))).contDiffAt).contDiffWithinAt
  have heOuterSmooth : ContDiffOn ℝ ∞ eOuter eOuter.source := by
    rw [heOuter]
    exact P.contDiff.comp_contDiffOn (hXOuter.mono heOuterV)
  have heAltSmooth : ContDiffOn ℝ ∞ eAlt eAlt.source := by
    rw [heAlt]
    exact P.contDiff.comp_contDiffOn (hXAlt.mono heAltV)
  let V : Set ℂ := eAlt.source ∩ eAlt ⁻¹' eOuter.target
  have hV : IsOpen V :=
    heAltSmooth.continuousOn.isOpen_inter_preimage eAlt.open_source eOuter.open_target
  have h0V : (0 : ℂ) ∈ V := by
    refine ⟨h0eAlt, ?_⟩
    change eAlt 0 ∈ eOuter.target
    rw [← hmarked]
    exact eOuter.map_source h0eOuter
  have hK : ContDiffOn ℝ ∞ K V :=
    hInvOuter.comp (heAltSmooth.mono inter_subset_left) (fun _ hz => hz.2)
  have hdK : DifferentiableAt ℝ K 0 :=
    (hK.contDiffAt (hV.mem_nhds h0V)).differentiableAt (by simp)
  have hdEOuter : DifferentiableAt ℝ eOuter 0 :=
    (heOuterSmooth.contDiffAt (eOuter.open_source.mem_nhds h0eOuter)).differentiableAt
      (by simp)
  have hright : (eOuter ∘ K) =ᶠ[𝓝 0] eAlt := by
    filter_upwards [hV.mem_nhds h0V] with z hz
    exact eOuter.right_inv hz.2
  have hDXOuter : DifferentiableAt ℝ XOuter 0 :=
    (hXOuter.contDiffAt (hVOuter.mem_nhds h0Outer)).differentiableAt (by simp)
  have hDXAlt : DifferentiableAt ℝ XAlt 0 :=
    (hXAlt.contDiffAt (hVAlt.mem_nhds h0Alt)).differentiableAt (by simp)
  have hEOuter : fderiv ℝ eOuter 0 = P.comp (fderiv ℝ XOuter 0) := by
    rw [heOuter]
    exact (P.hasFDerivAt.comp 0 hDXOuter.hasFDerivAt).fderiv
  have hEAlt : fderiv ℝ eAlt 0 = P.comp (fderiv ℝ XAlt 0) := by
    rw [heAlt]
    exact (P.hasFDerivAt.comp 0 hDXAlt.hasFDerivAt).fderiv
  have hprojected : (P.comp (fderiv ℝ XOuter 0)).comp L =
      P.comp (fderiv ℝ XAlt 0) := by
    rw [← hEOuter, ← hEAlt]
    have hdOuterK : DifferentiableAt ℝ eOuter (K 0) := by rw [hK0]; exact hdEOuter
    have hchain := fderiv_comp 0 hdOuterK hdK
    rw [hK0] at hchain
    exact hchain.symm.trans hright.fderiv_eq
  have hrange : LinearMap.range DOuter.toLinearMap = LinearMap.range DAlt.toLinearMap :=
    (mfderiv_range_eq_of_trace_conormal_cancellation g h0H huniq heqOuter heqAlt
      hdOuter hdAlt hiOuter hiAlt htrace hcancel).2.2
  let C (x : M) : E →L[ℝ] E :=
    mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) (extChartAt 𝓘(ℝ, E) p) x
  have hchartDOuter : fderiv ℝ XOuter 0 = (C (UOuter 0)).comp DOuter := by
    have hc := contMDiffAt_extChartAt' (I := 𝓘(ℝ, E)) (n := ∞) (hchartOuter 0 h0Outer)
    exact mfderiv_eq_fderiv.symm.trans
      (mfderiv_comp 0 (hc.mdifferentiableAt (by simp)) hdOuter)
  have hchartDAlt : fderiv ℝ XAlt 0 = (C (UAlt 0)).comp DAlt := by
    have hc := contMDiffAt_extChartAt' (I := 𝓘(ℝ, E)) (n := ∞) (hchartAlt 0 h0Alt)
    exact mfderiv_eq_fderiv.symm.trans
      (mfderiv_comp 0 (hc.mdifferentiableAt (by simp)) hdAlt)
  have hfactor : DOuter.comp L = DAlt := by
    ext v
    obtain ⟨w, hw⟩ := hrange.ge (LinearMap.mem_range_self DAlt.toLinearMap v)
    change DOuter w = DAlt v at hw
    have hcoords : fderiv ℝ XOuter 0 w = fderiv ℝ XAlt 0 v := by
      rw [hchartDOuter, hchartDAlt]
      change C (UOuter 0) (DOuter w) = C (UAlt 0) (DAlt v)
      rw [hw, hvalue]
    have hLw : L v = w := by
      apply hP.injective
      change P (fderiv ℝ XOuter 0 (L v)) = P (fderiv ℝ XOuter 0 w)
      exact (congrArg (fun D : ℂ →L[ℝ] ℂ => D v) hprojected).trans
        (congrArg P hcoords).symm
    change DOuter (L v) = DAlt v
    rw [hLw, hw]
  have hWithinOuter : (show ℂ →L[ℝ] E from
      mfderivWithin 𝓘(ℝ, ℂ) 𝓘(ℝ, E) FOuter H 0) = DOuter :=
    (side_mfderivWithin_congr heqOuter h0H).trans (mfderivWithin_eq_mfderiv huniq hdOuter)
  have hWithinAlt : (show ℂ →L[ℝ] E from
      mfderivWithin 𝓘(ℝ, ℂ) 𝓘(ℝ, E) FAlt H 0) = DAlt :=
    (side_mfderivWithin_congr heqAlt h0H).trans (mfderivWithin_eq_mfderiv huniq hdAlt)
  let νOuter : E := inwardConormalWithin g FOuter H 0
  let νAlt : E := inwardConormalWithin g FAlt H 0
  let B : E →L[ℝ] E →L[ℝ] ℝ := g.inner (FOuter 0)
  have hbase : FOuter 0 = FAlt 0 :=
    (heqOuter h0H).trans (hvalue.trans (heqAlt h0H).symm)
  have hgeomOuter := inwardConormalWithin_geometry g hiOuter
  have hgeomAlt := inwardConormalWithin_geometry g hiAlt
  have horth : B νOuter (DOuter 1) = 0 := by
    have h := hgeomOuter.2.1
    change B νOuter ((show ℂ →L[ℝ] E from
      mfderivWithin 𝓘(ℝ, ℂ) 𝓘(ℝ, E) FOuter H 0) 1) = 0 at h
    rw [hWithinOuter] at h
    exact h
  have hposOuter : 0 < B νOuter (DOuter Complex.I) := by
    have h := hgeomOuter.2.2
    change 0 < B νOuter ((show ℂ →L[ℝ] E from
      mfderivWithin 𝓘(ℝ, ℂ) 𝓘(ℝ, E) FOuter H 0) Complex.I) at h
    rw [hWithinOuter] at h
    exact h
  have hposAlt : 0 < B νAlt (DAlt Complex.I) := by
    have h := hgeomAlt.2.2
    change 0 < g.inner (FAlt 0) νAlt ((show ℂ →L[ℝ] E from
      mfderivWithin 𝓘(ℝ, ℂ) 𝓘(ℝ, E) FAlt H 0) Complex.I) at h
    rw [hWithinAlt, ← hbase] at h
    exact h
  have hcancelE : νOuter + νAlt = 0 := hcancel
  have hsign : (L Complex.I).im < 0 :=
    transition_im_neg_of_opposite_conormals B DOuter DAlt L νOuter νAlt
      hfactor horth hposOuter hposAlt hcancelE
  have hrealSource : ∀ᶠ t : ℝ in 𝓝 0, (t : ℂ) ∈ eOuter.source :=
    (Complex.continuous_ofReal.continuousAt : ContinuousAt (fun t : ℝ => (t : ℂ)) 0)
      (eOuter.open_source.mem_nhds h0eOuter)
  have hrealK : (fun t : ℝ => (K (t : ℂ)).im) =ᶠ[𝓝 0] fun _ => 0 := by
    filter_upwards [htrace, hrealSource] with t ht hts
    have he : eAlt (t : ℂ) = eOuter (t : ℂ) := by
      rw [heAlt, heOuter]
      change P (extChartAt 𝓘(ℝ, E) p (UAlt (t : ℂ))) =
        P (extChartAt 𝓘(ℝ, E) p (UOuter (t : ℂ)))
      rw [ht]
    change (eOuter.symm (eAlt (t : ℂ))).im = 0
    simp only [he, eOuter.left_inv hts, Complex.ofReal_im]
  obtain ⟨r, hr, _, hside⟩ := exists_pos_radius_im_neg_of_real_trace hV h0V
    (hK.of_le (by simp)) hrealK hsign
  let O : Set ℂ := (O0 ∩ eOuter.target) ∩
    (eAlt.target ∩ eAlt.symm ⁻¹' Metric.ball (0 : ℂ) r)
  have hO : IsOpen O :=
    (hO0.inter eOuter.open_target).inter
      (hInvAlt.continuousOn.isOpen_inter_preimage eAlt.open_target Metric.isOpen_ball)
  have hyAlt : eOuter 0 ∈ eAlt.target := by
    rw [hmarked]
    exact eAlt.map_source h0eAlt
  have hInvAlt0 : eAlt.symm (eOuter 0) = 0 := by
    rw [hmarked]
    exact eAlt.left_inv h0eAlt
  have h0O : eOuter 0 ∈ O := by
    refine ⟨⟨hy0, eOuter.map_source h0eOuter⟩, hyAlt, ?_⟩
    change eAlt.symm (eOuter 0) ∈ Metric.ball (0 : ℂ) r
    rw [hInvAlt0]
    exact Metric.mem_ball_self hr
  refine ⟨hsign, O, hO, h0O, fun y hy => ⟨hy.1.1, hy.1.2, hy.2.1⟩, ?_⟩
  rintro y ⟨hyO, z, ⟨hzSource, hzIm⟩, hzy⟩
  have hInvY : eAlt.symm y = z := by rw [← hzy]; exact eAlt.left_inv hzSource
  have hzBall : z ∈ Metric.ball (0 : ℂ) r := by
    have hyBall : eAlt.symm y ∈ Metric.ball (0 : ℂ) r := hyO.2.2
    rw [hInvY] at hyBall
    exact hyBall
  have hzSide := hside z hzBall hzIm
  change (eOuter.symm (eAlt z)).im < 0 at hzSide
  rwa [hzy] at hzSide

end DifferentialGeometry.Geometry
