import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Seifert.ConeFoldCoreTopology
import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Seifert.ConeFoldSpec
import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Seifert.PantsFoldCore
import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Seifert.ConeFoldBijective

/-!
# The one-cone fold with its Jordan core replaced

Lane A4b2 (design `docs/geometrization/handoffs/20261004-design-a4-cone-fold.md`, §7 and
erratum 7). In the disc chart `coreMap` of the core, the assembled fold `E = foldE p` composed with
`coreInv` is smooth, has nonzero Jacobian and is injective on the annulus
`85/1000 < ‖w‖ < 89/1000` (outside the inner core the local forms of `foldE_local` apply; the
annulus lies in the open triangle; `foldE` is injective on the triangle). For `hout` take
`w₀ = 88/1000` and `S = E(coreOut) ∪ ray`, where `coreOut` (the triangle outside the closed chart
disc of radius `87/1000`) is preconnected and the outward ray starts at the image of a point
high in the cusp `∞`, whose modulus `outerProfile y` exceeds the maximum of `‖E‖` on the core
circle. K16f's `exists_core_replacement` then gives a plane diffeomorphism `Q` equal to
`E ∘ coreInv` near the circle; `foldCore` is `Q ∘ coreMap` on the open chart disc of radius
`87/1000` and `E` elsewhere (`exists_foldCore`). Every point outside the open target is on an
unbounded preconnected set missing the open target (rays, as in K16f's `foldMap_outside_ray`), so
`Q` maps the core disc into the open target; the core circle is mapped into the open target
because `E` is a local diffeomorphism there.
-/

set_option autoImplicit false

noncomputable section

open Complex Filter Set Metric
open scoped ComplexConjugate ContDiff Topology

namespace GC.Seifert

open ConeLayout

theorem det_fderiv_comp {f g : ℂ → ℂ} {x : ℂ} (hf : DifferentiableAt ℝ f (g x))
    (hg : DifferentiableAt ℝ g x) :
    (fderiv ℝ (f ∘ g) x).det = (fderiv ℝ f (g x)).det * (fderiv ℝ g x).det := by
  rw [fderiv_comp x hf hg]
  change LinearMap.det ((fderiv ℝ f (g x) : ℂ →ₗ[ℝ] ℂ) ∘ₗ (fderiv ℝ g x : ℂ →ₗ[ℝ] ℂ)) = _
  rw [LinearMap.det_comp]

theorem im_pos_of_nhds {u : ℂ} (h : {v : ℂ | 0 ≤ v.im} ∈ 𝓝 u) : 0 < u.im := by
  obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.1 h
  by_contra hle
  push Not at hle
  have hmem : u - ((ε / 2 : ℝ) : ℂ) * I ∈ ball u ε := by
    rw [mem_ball, dist_eq_norm, sub_sub_cancel_left, norm_neg, norm_mul, Complex.norm_I, mul_one,
      Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by positivity)]
    linarith
  have := hball hmem
  change 0 ≤ (u - ((ε / 2 : ℝ) : ℂ) * I).im at this
  simp only [sub_im, mul_im, ofReal_re, I_im, mul_one, ofReal_im, I_re, mul_zero,
    add_zero] at this
  linarith

def openTargetBefore : Set ℂ := {u | ‖u‖ < 3 ∧ 0 < u.im ∧ 1 / 2 < ‖u - 3 / 2‖}

theorem outside_ray {u : ℂ} (hu : u ∉ openTargetBefore) :
    ∃ S : Set ℂ, IsPreconnected S ∧ u ∈ S ∧ Disjoint S openTargetBefore ∧
      ¬ Bornology.IsBounded S := by
  have hdown : IsPreconnected ((fun t : ℝ => u - (t : ℂ) * I) '' Ici 0) :=
    isPreconnected_Ici.image _ (by fun_prop)
  have hdownb : ¬ Bornology.IsBounded ((fun t : ℝ => u - (t : ℂ) * I) '' Ici 0) := by
    rw [isBounded_iff_forall_norm_le]
    rintro ⟨C, hC⟩
    set t : ℝ := |C| + ‖u‖ + 1
    have ht := hC (u - (t : ℂ) * I) ⟨t, mem_Ici.2 (by positivity), rfl⟩
    have h1 := norm_sub_norm_le ((t : ℂ) * I) u
    rw [norm_sub_rev] at h1
    rw [norm_mul, Complex.norm_I, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos (by positivity), mul_one] at h1
    linarith [le_abs_self C]
  have hu0 : u ∈ (fun t : ℝ => u - (t : ℂ) * I) '' Ici 0 := ⟨0, mem_Ici.2 le_rfl, by simp⟩
  by_cases him : u.im ≤ 0
  · refine ⟨_, hdown, hu0, disjoint_left.2 ?_, hdownb⟩
    rintro v ⟨t, ht, rfl⟩ hv
    have := hv.2.1
    simp only [sub_im, mul_im, ofReal_re, ofReal_im, I_re, I_im, mul_one, zero_mul,
      add_zero] at this
    linarith [mem_Ici.1 ht]
  push Not at him
  by_cases h3 : 3 ≤ ‖u‖
  · have hu00 : u ≠ 0 := by
      intro h0; rw [h0, norm_zero] at h3; linarith
    refine ⟨_, isPreconnected_ray u, ⟨1, mem_Ici.2 le_rfl, by simp⟩, disjoint_left.2 ?_,
      not_isBounded_ray hu00⟩
    intro v hv hvp
    have := norm_ray_ge hv
    linarith [hvp.1]
  · push Not at h3
    have hhole : ‖u - 3 / 2‖ ≤ 1 / 2 := by
      by_contra hc
      push Not at hc
      exact hu ⟨h3, him, hc⟩
    refine ⟨_, hdown, hu0, disjoint_left.2 ?_, hdownb⟩
    rintro v ⟨t, ht, rfl⟩ hv
    have ht0 := mem_Ici.1 ht
    have hvim := hv.2.1
    simp only [sub_im, mul_im, ofReal_re, ofReal_im, I_re, I_im, mul_one, zero_mul,
      add_zero] at hvim
    have hv2 := hv.2.2
    have e1 : ‖u - (t : ℂ) * I - 3 / 2‖ ^ 2 = (u.re - 3 / 2) ^ 2 + (u.im - t) ^ 2 := by
      rw [Complex.sq_norm, normSq_apply]; simp; ring
    have e2 : ‖u - 3 / 2‖ ^ 2 = (u.re - 3 / 2) ^ 2 + u.im ^ 2 := by
      rw [Complex.sq_norm, normSq_apply]; simp; ring
    have : ‖u - (t : ℂ) * I - 3 / 2‖ ^ 2 ≤ ‖u - 3 / 2‖ ^ 2 := by
      rw [e1, e2]; nlinarith
    have := (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).1 this
    linarith

namespace ConeShape

variable (σ : ConeShape)

theorem chartScale_le_two : σ.chartScale ≤ 2 := by
  have h1 := σ.sqrt_constK_le_half
  have h2 := σ.cos_θ₁_nonneg
  have h3 := σ.sqrt_constK_pos
  unfold chartScale
  rw [div_le_iff₀ (by linarith)]
  nlinarith

theorem im_lt_two_of_coreMap_le {z : ℂ} (hz : 0 < z.im) (h : ‖σ.coreMap z‖ ≤ 89 / 1000) :
    z.im < 2 := by
  have hc := σ.outer_core_of_coreMap_le hz h
  rw [normSq_sub_coreCentre, coreOuter] at hc
  have hY : 813 / 1000 ≤ (σ.fermiChart z).im := by
    nlinarith [sq_nonneg (-(σ.fermiChart z).re - 201 / 1000)]
  rw [σ.fermiChart_im] at hY
  have hN := σ.normSq_sub_rightFoot_pos hz
  have hNy : z.im ^ 2 ≤ normSq (z - σ.rightFoot) := by
    rw [normSq_apply]; simp; nlinarith [sq_nonneg (z.re - σ.rightFoot)]
  have hk := σ.chartScale_le_two
  have hk0 := σ.chartScale_pos
  rw [le_div_iff₀ (by positivity)] at hY
  nlinarith

section Core

variable (hθ : σ.θ₂ = 0) (h₁ : Real.cos σ.θ₁ = 0 ∨ 1 / 2 ≤ Real.cos σ.θ₁)

include hθ h₁ in
theorem foldE_eventually_apex {p : ℕ} :
    σ.foldE p =ᶠ[𝓝 σ.vertexOne] σ.apexBefore p := by
  have h₂ := σ.adm_two_of_cusp hθ
  have hv := σ.vertexOne_im_pos
  have h1 : σ.etaOne σ.vertexOne < σ.foldA₁ := by
    rw [σ.etaOne_vertexOne]; exact σ.vertexOne_im_lt_foldA₁ h₁ h₂
  have hAB := σ.foldA₁_lt_foldB₁ h₁ h₂
  have hBH := σ.foldB₁_lt_foldH h₁ h₂
  have h0 : σ.foldH < cuspZeroHeight σ.vertexOne :=
    σ.foldH_lt_cuspZeroHeight_of_etaOne_le hθ hv (by linarith)
  filter_upwards [continuousAt_const.eventually_lt (continuousAt_cuspZeroHeight hv) h0,
    (σ.continuousAt_etaOne hv).eventually_lt continuousAt_const h1] with w hw0 hw1
  simp only [foldE, not_lt.2 hw0.le, hw1, ↓reduceIte]

include hθ h₁ in
theorem foldE_good {p : ℕ} (hp : 1 ≤ p) {z : ℂ} (hz : z ∈ σ.triangle)
    (hcore : ConeLayout.coreInner ^ 2 ≤ normSq (σ.fermiChart z - ConeLayout.coreCentre)) :
    ∀ᶠ w in 𝓝 z, 0 < w.im ∧ ContDiffAt ℝ ∞ (σ.foldE p) w ∧
      (w ≠ σ.vertexOne → (fderiv ℝ (σ.foldE p) w).det ≠ 0) := by
  have hup := isOpen_upper.mem_nhds hz.1
  by_cases hzv : z = σ.vertexOne
  · subst hzv
    have ha := σ.foldE_eventually_apex hθ h₁ (p := p)
    filter_upwards [hup, ha.eventuallyEq_nhds] with w hw hwe
    refine ⟨hw, (σ.contDiffAt_apexBefore p hw).congr_of_eventuallyEq hwe, fun hwv => ?_⟩
    rw [hwe.fderiv_eq]
    exact σ.det_fderiv_apexBefore_ne_zero (by omega) hw hwv
  · obtain ⟨g, D, hD, hzD, hg, hEg, hdet⟩ := σ.foldE_local hθ h₁ hp hz hcore
    filter_upwards [hup, hD.mem_nhds hzD, hEg.eventuallyEq_nhds,
      eventually_det_ne_zero hD hg hzD (hdet hzv)] with w hw hwD hwe hwdet
    refine ⟨hw, (hg.contDiffAt (hD.mem_nhds hwD)).congr_of_eventuallyEq hwe, fun _ => ?_⟩
    rw [hwe.fderiv_eq]
    exact hwdet

include hθ h₁ in
theorem foldE_mem_openTarget {p : ℕ} (hp : 1 ≤ p) (hpθ : σ.θ₁ * p = Real.pi) {z : ℂ}
    (hz : z ∈ σ.triangle) (hint : ∀ i, 0 < σ.wallSide i z)
    (hcore : ConeLayout.coreInner ^ 2 ≤ normSq (σ.fermiChart z - ConeLayout.coreCentre)) :
    σ.foldE p z ∈ openTargetBefore := by
  obtain ⟨h3, -, hh⟩ := σ.foldE_mem_target hθ h₁ hp hpθ hz
  refine ⟨h3, ?_, hh⟩
  have hzv : z ≠ σ.vertexOne := by
    intro h; have := hint 1; rw [h] at this; simp [wallSide, vertexOne_re] at this
  obtain ⟨g, D, hD, hzD, hg, hEg, hdet⟩ := σ.foldE_local hθ h₁ hp hz hcore
  have hT : σ.triangle ∈ 𝓝 z := σ.interior_mem_of_wallSide_pos hz hint
  have hN : σ.triangle ∩ {w | σ.foldE p w = g w} ∈ 𝓝 z := inter_mem hT hEg
  have himg := image_mem_nhds_of_det_ne_zero hN (hg.contDiffAt (hD.mem_nhds hzD)) (hdet hzv)
  have hsub : g '' (σ.triangle ∩ {w | σ.foldE p w = g w}) ⊆ {v : ℂ | 0 ≤ v.im} := by
    rintro _ ⟨w, ⟨hwT, hwe⟩, rfl⟩
    change 0 ≤ (g w).im
    rw [← hwe]
    exact (σ.foldE_mem_target hθ h₁ hp hpθ hwT).2.1
  have := im_pos_of_nhds (Filter.mem_of_superset himg hsub)
  rwa [← hEg.self_of_nhds] at this

include hθ h₁ in
theorem exists_foldCore {p : ℕ} (hp : 1 ≤ p) (hpθ : σ.θ₁ * p = Real.pi) :
    ∃ F : ℂ → ℂ, (∀ z, ¬ (0 < z.im ∧ ‖σ.coreMap z‖ < 87 / 1000) → F z = σ.foldE p z) ∧
      (∀ z ∈ σ.triangle, ∀ᶠ w in 𝓝 z, 0 < w.im ∧ ContDiffAt ℝ ∞ F w ∧
        (w ≠ σ.vertexOne → (fderiv ℝ F w).det ≠ 0)) ∧
      Set.InjOn F σ.triangle ∧
      (∀ z ∈ σ.triangle, ‖F z‖ < 3 ∧ 0 ≤ (F z).im ∧ 1 / 2 < ‖F z - 3 / 2‖) := by
  have h₂ := σ.adm_two_of_cusp hθ
  set E := σ.foldE p with hEdef
  set Ew : ℂ → ℂ := fun w => E (σ.coreInv w) with hEw
  have hdisc : ∀ w : ℂ, ‖w‖ ≤ 89 / 1000 → ‖w‖ < 1 ∧ σ.coreInv w ∈ σ.triangle ∧
      (∀ i, 0 < σ.wallSide i (σ.coreInv w)) ∧ σ.coreMap (σ.coreInv w) = w := by
    intro w hw
    have h1 : ‖w‖ < 1 := by linarith
    have hz := σ.coreInv_im_pos h1
    have hm := σ.coreMap_coreInv h1
    obtain ⟨hT, hw0, hw1, hw2⟩ := σ.mem_triangle_of_coreMap_le h₁ h₂ hz (by rw [hm]; exact hw)
    refine ⟨h1, hT, fun i => ?_, hm⟩
    fin_cases i
    · exact hw0
    · exact hw1
    · exact hw2
  have hout_core : ∀ z : ℂ, 0 < z.im → 17 / 200 ≤ ‖σ.coreMap z‖ →
      ConeLayout.coreInner ^ 2 ≤ normSq (σ.fermiChart z - ConeLayout.coreCentre) :=
    fun z hz h => σ.inner_core_of_coreMap hz h
  have hann : ∀ w : ℂ, 87 / 1000 - 1 / 500 < ‖w - 0‖ → ‖w - 0‖ < 87 / 1000 + 1 / 500 →
      ‖w‖ < 1 ∧ σ.coreInv w ∈ σ.triangle ∧ (∀ i, 0 < σ.wallSide i (σ.coreInv w)) ∧
      σ.coreMap (σ.coreInv w) = w ∧ 17 / 200 ≤ ‖w‖ := by
    intro w h1 h2
    rw [sub_zero] at h1 h2
    obtain ⟨a, b, c, d⟩ := hdisc w (by linarith)
    exact ⟨a, b, c, d, by linarith⟩
  have hgoodE : ∀ w : ℂ, 87 / 1000 - 1 / 500 < ‖w - 0‖ → ‖w - 0‖ < 87 / 1000 + 1 / 500 →
      ContDiffAt ℝ ∞ Ew w ∧ (fderiv ℝ Ew w).det ≠ 0 := by
    intro w h1 h2
    obtain ⟨hw1, hT, hint, hm, hr⟩ := hann w h1 h2
    have hzv : σ.coreInv w ≠ σ.vertexOne := by
      intro h; have := hint 1; rw [h] at this; simp [wallSide, vertexOne_re] at this
    obtain ⟨-, hc, hd⟩ :=
      (σ.foldE_good hθ h₁ hp hT (hout_core _ hT.1 (by rw [hm]; exact hr))).self_of_nhds
    have hcw := σ.contDiffAt_coreInv hw1
    have hcomp : ContDiffAt ℝ ∞ Ew w := hc.comp w hcw
    refine ⟨hcomp, ?_⟩
    change (fderiv ℝ (E ∘ σ.coreInv) w).det ≠ 0
    rw [det_fderiv_comp (hc.differentiableAt (by simp)) (hcw.differentiableAt (by simp))]
    exact mul_ne_zero (hd hzv) (σ.det_fderiv_coreInv_pos hw1).ne'
  have hE : ContDiffOn ℝ ∞ Ew {w | 87 / 1000 - 1 / 500 < ‖w - 0‖ ∧ ‖w - 0‖ < 87 / 1000 + 1 / 500} :=
    fun w hw => (hgoodE w hw.1 hw.2).1.contDiffWithinAt
  have hdet : ∀ w, 87 / 1000 - 1 / 500 < ‖w - 0‖ → ‖w - 0‖ < 87 / 1000 + 1 / 500 →
      (fderiv ℝ Ew w).det ≠ 0 := fun w h1 h2 => (hgoodE w h1 h2).2
  have hinjT := σ.foldE_injOn hθ h₁ hp hpθ
  have hinj : InjOn Ew {w | 87 / 1000 - 1 / 500 < ‖w - 0‖ ∧ ‖w - 0‖ < 87 / 1000 + 1 / 500} := by
    intro w hw w' hw' h
    obtain ⟨hw1, hT, -, -, -⟩ := hann w hw.1 hw.2
    obtain ⟨hw1', hT', -, -, -⟩ := hann w' hw'.1 hw'.2
    exact σ.coreInv_injOn (by simpa using hw1) (by simpa using hw1') (hinjT hT hT' h)
  have hsph : ∀ q ∈ sphere (0 : ℂ) (87 / 1000), ‖q‖ = 87 / 1000 ∧
      ContinuousAt Ew q ∧ σ.coreInv q ∈ σ.triangle ∧ σ.coreMap (σ.coreInv q) = q ∧
      Ew q ∈ openTargetBefore := by
    intro q hq
    have hq' : ‖q‖ = 87 / 1000 := by simpa using hq
    obtain ⟨hw1, hT, hint, hm, hr⟩ := hann q (by rw [sub_zero]; linarith)
      (by rw [sub_zero]; linarith)
    refine ⟨hq',
      (hgoodE q (by rw [sub_zero]; linarith) (by rw [sub_zero]; linarith)).1.continuousAt,
      hT, hm, ?_⟩
    exact σ.foldE_mem_openTarget hθ h₁ hp hpθ hT hint (hout_core _ hT.1 (by rw [hm]; exact hr))
  obtain ⟨qmax, hqmax, hmax⟩ := (isCompact_sphere (0 : ℂ) (87 / 1000)).exists_isMaxOn
    (NormedSpace.sphere_nonempty.2 (by norm_num))
    (fun q hq => (hsph q hq).2.1.norm.continuousWithinAt)
  set M := ‖Ew qmax‖ with hM
  have hM3 : M < 3 := (hsph qmax hqmax).2.2.2.2.1
  obtain ⟨Y, hY⟩ := exists_outerProfile_gt σ.constK_pos σ.foldY₁_lt_foldY₂ (sub_pos.2 hM3)
  set yt : ℝ := max Y 2 + 1 with hyt
  have hyt2 : 3 ≤ yt := by rw [hyt]; linarith [le_max_right Y 2]
  set zt : ℂ := ⟨σ.width / 2, yt⟩ with hzt
  have hW := σ.width_pos
  have hztT : zt ∈ σ.triangle := by
    refine ⟨by simp [hzt]; linarith, fun i => ?_⟩
    fin_cases i
    · change 0 ≤ zt.re; simp [hzt]; linarith
    · change 0 ≤ σ.width - zt.re; simp [hzt]; linarith
    · change 0 ≤ (zt.re - σ.centre) ^ 2 + zt.im ^ 2 - 1 / 16
      simp [hzt]; nlinarith [sq_nonneg (σ.width / 2 - σ.centre)]
  have hzt_out : zt ∈ σ.coreOut := by
    refine ⟨hztT, ?_⟩
    by_contra hle
    push Not at hle
    have := σ.im_lt_two_of_coreMap_le hztT.1 (by linarith)
    simp [hzt] at this
    linarith
  have hztE : M < ‖E zt‖ := by
    have hH := σ.foldH_pos
    have hHh := σ.foldH_lt_half
    have hzt1 : zt ∈ σ.domOne := σ.mem_domOne_of_re_ne hztT.1 (by simp [hzt]; linarith)
    have h0 : σ.foldH ≤ cuspZeroHeight zt := by
      linarith [im_le_cuspZeroHeight hztT.1, show zt.im = yt by simp [hzt]]
    have h1 : σ.foldH ≤ σ.etaOne zt := by
      linarith [σ.im_le_etaOne hzt1, show zt.im = yt by simp [hzt]]
    have hL : 1 / 10 ≤ |σ.sinhN zt| := by
      have hs : 1 / 10 ≤ σ.sinhN zt := by
        unfold sinhN
        rw [le_div_iff₀ hztT.1]
        simp only [wallSide, hzt]
        nlinarith [sq_nonneg (σ.width / 2 - σ.centre)]
      exact le_trans hs (le_abs_self _)
    obtain ⟨e, -⟩ := σ.foldE_image_inf hθ h₁ (p := p) hztT h0 h1 hL
    rw [hEdef, e]
    have := hY yt (by rw [hyt]; linarith [le_max_left Y 2])
    have hy : zt.im = yt := by simp [hzt]
    rw [hy]
    linarith
  set u₀ := E zt with hu₀
  have hu0 : u₀ ≠ 0 := by
    intro h; rw [h, norm_zero] at hztE; linarith [norm_nonneg (Ew qmax)]
  set S := E '' σ.coreOut ∪ (fun t : ℝ => (t : ℂ) * u₀) '' Ici 1 with hSdef
  have hEcont : ContinuousOn E σ.coreOut := fun z hz =>
    (σ.foldE_good hθ h₁ hp hz.1 (hout_core z hz.1.1 (by linarith [hz.2]))).self_of_nhds.2.1
      |>.continuousAt.continuousWithinAt
  have hSc : IsPreconnected S :=
    ((σ.isPreconnected_coreOut h₁ h₂).image E hEcont).union u₀ ⟨zt, hzt_out, rfl⟩
      ⟨1, mem_Ici.2 le_rfl, by simp⟩ (isPreconnected_ray u₀)
  have hSb : ¬ Bornology.IsBounded S := fun hb =>
    not_isBounded_ray hu0 (hb.subset subset_union_right)
  have hSd : Disjoint S (Ew '' sphere (0 : ℂ) (87 / 1000)) := by
    rw [disjoint_left]
    rintro v (⟨x, hx, hxv⟩ | hv) ⟨q, hq, hqv⟩
    · obtain ⟨hq', -, hqT, hqm, -⟩ := hsph q hq
      have := hinjT hx.1 hqT (hxv.trans hqv.symm)
      have h2 := hx.2
      rw [← this] at hqm
      rw [hqm, hq'] at h2
      exact lt_irrefl _ h2
    · have h1 := norm_ray_ge hv
      have h2 : ‖Ew q‖ ≤ M := hmax hq
      rw [hqv] at h2
      linarith
  have hw₀ : ‖((88 / 1000 : ℝ) : ℂ) - 0‖ = 88 / 1000 := by
    rw [sub_zero, Complex.norm_real, Real.norm_eq_abs]; norm_num
  have hout : ∃ z₀, 87 / 1000 < ‖z₀ - 0‖ ∧ ‖z₀ - 0‖ < 87 / 1000 + 1 / 500 ∧ ∃ S : Set ℂ,
      IsPreconnected S ∧ Ew z₀ ∈ S ∧ Disjoint S (Ew '' sphere (0 : ℂ) (87 / 1000)) ∧
        ¬ Bornology.IsBounded S := by
    refine ⟨((88 / 1000 : ℝ) : ℂ), by rw [hw₀]; norm_num, by rw [hw₀]; norm_num, S, hSc, ?_,
      hSd, hSb⟩
    obtain ⟨-, hT, -, hm⟩ := hdisc ((88 / 1000 : ℝ) : ℂ) (by
      rw [Complex.norm_real, Real.norm_eq_abs]; norm_num)
    refine Or.inl ⟨σ.coreInv ((88 / 1000 : ℝ) : ℂ), ⟨hT, ?_⟩, rfl⟩
    rw [hm, Complex.norm_real, Real.norm_eq_abs]; norm_num
  obtain ⟨Q, hQs, hQi, hQd, ⟨V, hVo, hsV, hQV⟩, hQc⟩ :=
    exists_core_replacement (by norm_num : (0 : ℝ) < 1 / 500) (by norm_num) hE hdet hinj hout
  have hQball : Q '' ball (0 : ℂ) (87 / 1000) ⊆ openTargetBefore := by
    rintro _ ⟨w, hw, rfl⟩
    by_contra hc
    obtain ⟨S₀, hS₀, huS, hS₀d, hS₀b⟩ := outside_ray hc
    have hΓ : Disjoint S₀ (Ew '' sphere (0 : ℂ) (87 / 1000)) := by
      refine disjoint_left.2 fun v hv ⟨q, hq, hqv⟩ => disjoint_left.1 hS₀d hv ?_
      rw [← hqv]
      exact (hsph q hq).2.2.2.2
    exact disjoint_left.1 (hQc S₀ hS₀ hS₀b hΓ) huS ⟨w, hw, rfl⟩
  classical
  set F : ℂ → ℂ := fun z => if 0 < z.im ∧ ‖σ.coreMap z‖ < 87 / 1000 then Q (σ.coreMap z)
    else E z with hFdef
  have hF1 : ∀ z, ¬ (0 < z.im ∧ ‖σ.coreMap z‖ < 87 / 1000) → F z = E z := fun z hz => by
    simp only [hFdef, hz, ↓reduceIte]
  have hFQ : ∀ z, 0 < z.im → (σ.coreMap z ∈ V ∨ ‖σ.coreMap z‖ < 87 / 1000) →
      F z = Q (σ.coreMap z) := by
    intro z hz h
    by_cases hb : ‖σ.coreMap z‖ < 87 / 1000
    · simp only [hFdef, hz, hb, and_self, ↓reduceIte]
    · rw [hF1 z (fun h' => hb h'.2)]
      rcases h with hV | hb'
      · rw [hQV hV]
        change E z = E (σ.coreInv (σ.coreMap z))
        rw [σ.coreInv_coreMap hz]
      · exact absurd hb' hb
  have hcontMap : ∀ z : ℂ, 0 < z.im → ContinuousAt σ.coreMap z := fun z hz =>
    (σ.contDiffAt_coreMap hz).continuousAt
  have hOQ : ∀ z, 0 < z.im → (σ.coreMap z ∈ V ∨ ‖σ.coreMap z‖ < 87 / 1000) →
      ∀ᶠ w in 𝓝 z, 0 < w.im ∧ (σ.coreMap w ∈ V ∨ ‖σ.coreMap w‖ < 87 / 1000) := by
    intro z hz h
    have hup := isOpen_upper.mem_nhds hz
    rcases h with hV | hb
    · filter_upwards [hup, (hcontMap z hz).preimage_mem_nhds (hVo.mem_nhds hV)] with w hw hwV
      exact ⟨hw, Or.inl hwV⟩
    · filter_upwards [hup, (hcontMap z hz).norm.eventually_lt continuousAt_const hb] with w hw hwb
      exact ⟨hw, Or.inr hwb⟩
  have hgoodQ : ∀ z, 0 < z.im → (σ.coreMap z ∈ V ∨ ‖σ.coreMap z‖ < 87 / 1000) →
      ∀ᶠ w in 𝓝 z, 0 < w.im ∧ ContDiffAt ℝ ∞ F w ∧ (fderiv ℝ F w).det ≠ 0 := by
    intro z hz h
    filter_upwards [hOQ z hz h] with w ⟨hw, hwh⟩
    have hev : F =ᶠ[𝓝 w] Q ∘ σ.coreMap := by
      filter_upwards [hOQ w hw hwh] with v ⟨hv, hvh⟩
      exact hFQ v hv hvh
    have hc : ContDiffAt ℝ ∞ (Q ∘ σ.coreMap) w := hQs.contDiffAt.comp w (σ.contDiffAt_coreMap hw)
    refine ⟨hw, hc.congr_of_eventuallyEq hev, ?_⟩
    rw [hev.fderiv_eq, det_fderiv_comp (hQs.contDiffAt.differentiableAt (by simp))
      ((σ.contDiffAt_coreMap hw).differentiableAt (by simp))]
    exact mul_ne_zero (hQd _) (σ.det_fderiv_coreMap_pos hw).ne'
  refine ⟨F, hF1, ?_, ?_, ?_⟩
  · intro z hz
    by_cases h : σ.coreMap z ∈ V ∨ ‖σ.coreMap z‖ < 87 / 1000
    · filter_upwards [hgoodQ z hz.1 h] with w ⟨hw, hc, hd⟩
      exact ⟨hw, hc, fun _ => hd⟩
    · push Not at h
      have hgt : 87 / 1000 < ‖σ.coreMap z‖ := by
        rcases h.2.lt_or_eq with hlt | heq
        · exact hlt
        · exact absurd (hsV (by simpa using heq.symm)) h.1
      have hE' : F =ᶠ[𝓝 z] E := by
        filter_upwards [continuousAt_const.eventually_lt (hcontMap z hz.1).norm hgt] with w hw
        exact hF1 w fun h' => by linarith [h'.2]
      filter_upwards [σ.foldE_good hθ h₁ hp hz (hout_core z hz.1 (by linarith)),
        hE'.eventuallyEq_nhds] with w ⟨hw, hc, hd⟩ hwe
      refine ⟨hw, hc.congr_of_eventuallyEq hwe, fun hwv => ?_⟩
      rw [hwe.fderiv_eq]
      exact hd hwv
  · have key : ∀ a b : ℂ, a ∈ σ.triangle → b ∈ σ.triangle → ‖σ.coreMap a‖ < 87 / 1000 →
        87 / 1000 ≤ ‖σ.coreMap b‖ → F a = F b → False := by
      intro a b ha hb hna hnb hab
      have hFa : F a = Q (σ.coreMap a) := hFQ a ha.1 (Or.inr hna)
      rcases hnb.lt_or_eq with hlt | heq
      · have hFb : F b = E b := hF1 b fun h' => by linarith [h'.2]
        have hbS : E b ∈ S := Or.inl ⟨b, ⟨hb, hlt⟩, rfl⟩
        rw [← hFb, ← hab, hFa] at hbS
        exact disjoint_left.1 (hQc S hSc hSb hSd) hbS
          ⟨σ.coreMap a, by simpa using hna, rfl⟩
      · have hbV : σ.coreMap b ∈ V := hsV (by simpa using heq.symm)
        rw [hFa, hFQ b hb.1 (Or.inl hbV)] at hab
        have := hQi hab
        rw [this] at hna
        linarith
    intro z hz z' hz' heq
    by_cases h1 : ‖σ.coreMap z‖ < 87 / 1000 <;> by_cases h2 : ‖σ.coreMap z'‖ < 87 / 1000
    · rw [hFQ z hz.1 (Or.inr h1), hFQ z' hz'.1 (Or.inr h2)] at heq
      exact σ.coreMap_injOn hz.1 hz'.1 (hQi heq)
    · exact (key z z' hz hz' h1 (not_lt.1 h2) heq).elim
    · exact (key z' z hz' hz h2 (not_lt.1 h1) heq.symm).elim
    · rw [hF1 z (fun h' => h1 h'.2), hF1 z' (fun h' => h2 h'.2)] at heq
      exact hinjT hz hz' heq
  · intro z hz
    by_cases h : ‖σ.coreMap z‖ < 87 / 1000
    · rw [hFQ z hz.1 (Or.inr h)]
      have := hQball ⟨σ.coreMap z, by simpa using h, rfl⟩
      exact ⟨this.1, this.2.1.le, this.2.2⟩
    · rw [hF1 z (fun h' => h h'.2)]
      exact σ.foldE_mem_target hθ h₁ hp hpθ hz

end Core

end ConeShape

end GC.Seifert
