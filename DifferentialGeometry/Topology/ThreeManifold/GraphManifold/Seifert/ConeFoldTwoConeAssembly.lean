import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Seifert.ConeFoldTwoConeCornerInf

/-!
# The assembled cone fold `E` of the two-cone shapes

Lane A4b3 (design `docs/geometrization/handoffs/20261004-design-a4-cone-fold.md`, §6 and the
errata after review 15, two-cone shapes `(p₁, p₂, ⊤)`). Before the final mirror `u ↦ -ū` the fold
`foldE₂ hθ p₁ p₂` is
* the corner at `v₂`, `regionTwoC` (the swap of the cone region), on `R₂ = {η₂ < h}`,
* the cone region `coneRegion p₁` (apex model and corner at `v₁`) on `R₁ = {η₁ < h}`,
* the two-cone wall-2 bridge `bridgeTwoC` on the lens `|sinh n| < 1/10` outside `R₁ ∪ R₂`,
* the corner at `∞`, `cornerInfC blendWeight`, elsewhere.
The layout of `SF/ConeFoldLayout.lean` applies with both uniform parameters `t₁, t₂ ≤ 2/3`: in
the Fermi chart `R₂` is `regionTwo t₂ < 0` (`regionTwo_nonneg_iffC`), and the lens arc and both
switch windows lie in the inner core (`inner_core_of_lensC`, `inner_core_of_windowTwoC`). At every
point of the triangle outside the inner core `foldE₂` agrees near the point with a map smooth on
an open neighbourhood with nonzero Jacobian off the vertices (`foldE₂_local`): on `∂R₂` and `∂R₁`
the corners equal the adjacent bridges (J1/J2), on the lens `bridgeTwoC` equals the corner
`cornerConeC` at `v₁` (`foldPhiB_lt_of_lens`), and near the vertices the map is the apex model
(`foldE₂_eventually_apexOne`, `foldE₂_eventually_apexTwo`).
-/

set_option autoImplicit false

noncomputable section

open Complex Filter Set
open scoped ComplexConjugate ContDiff Topology

namespace GC.Seifert

namespace ConeShape

variable (σ : ConeShape)

def foldE₂ (hθ : 0 < σ.θ₂) (p q : ℕ) (z : ℂ) : ℂ :=
  if σ.etaTwoC z < σ.foldH then σ.regionTwoC hθ q z
  else if σ.etaOne z < σ.foldH then σ.coneRegion p z
  else if |σ.sinhN z| < 1 / 10 then σ.bridgeTwoC z
  else σ.cornerInfC σ.blendWeight σ.foldY₁ σ.foldY₂ z

/-! ### The layout at the second cone -/

section Layout

variable (hθ : 0 < σ.θ₂) (h₁ : Real.cos σ.θ₁ = 0 ∨ 1 / 2 ≤ Real.cos σ.θ₁)
  (h₂ : Real.cos σ.θ₂ = 0 ∨ 1 / 2 ≤ Real.cos σ.θ₂)

include h₁ h₂ in
theorem tTwo_le : σ.tTwo ≤ 2 / 3 := by
  have hc2 := σ.cos_θ₂_nonneg
  have hc1 := σ.cos_θ₁_nonneg
  have hsum := σ.cos_add_cos_pos
  have h1pos := σ.one_add_cos_θ₁_pos
  rw [tTwo, div_le_iff₀ h1pos]
  rcases h₁ with h | h
  · rcases h₂ with h2 | h2
    · rw [h, h2] at hsum
      linarith
    · rw [h]
      linarith
  · rcases h₂ with h2 | h2
    · rw [h2]; linarith
    · linarith

include hθ in
theorem regionTwo_mulC {z : ℂ} (hz : 0 < z.im) :
    Real.sqrt σ.constK * σ.etaTwoC z * ConeLayout.regionTwo σ.tTwo (σ.fermiChart z) =
      (σ.fermiChart z).im * (σ.etaTwoC z - σ.foldH) *
        (σ.etaTwoC z - 21 / 20 * σ.tTwo * Real.sqrt σ.constK) := by
  have hid := σ.sqrt_constK_mul_coneHeight_two hθ hz
  have hv := σ.vertexTwo_im_sq
  have hK : Real.sqrt σ.constK ^ 2 = σ.constK := Real.sq_sqrt σ.constK_pos.le
  rw [ConeLayout.regionTwo, foldH]
  change Real.sqrt σ.constK * σ.etaTwoC z * (normSq (σ.fermiChart z) + σ.tTwo) =
    (σ.fermiChart z).im * (σ.etaTwoC z ^ 2 + σ.vertexTwo.im ^ 2) at hid
  rw [hv] at hid
  linear_combination hid - (σ.fermiChart z).im * σ.tTwo * hK

include hθ h₁ h₂ in
theorem etaTwoC_sub_pos {z : ℂ} (hz : 0 < z.im) :
    0 < σ.etaTwoC z - 21 / 20 * σ.tTwo * Real.sqrt σ.constK := by
  have hw := (ConeLayout.window_before_wallTwo σ hθ h₁ h₂).1
  have hv0 := σ.vertexTwo_im_pos hθ
  have hge : σ.vertexTwo.im ≤ σ.etaTwoC z := coneHeight_ge hv0 hz
  have hv := σ.vertexTwo_im_sq
  have ht := σ.tTwo_nonneg
  have hs := σ.sqrt_constK_pos
  have hK : Real.sqrt σ.constK ^ 2 = σ.constK := Real.sq_sqrt σ.constK_pos.le
  have hlt : 21 / 20 * σ.tTwo * Real.sqrt σ.constK < σ.vertexTwo.im := by
    have hsq : (21 / 20 * σ.tTwo * Real.sqrt σ.constK) ^ 2 < σ.vertexTwo.im ^ 2 := by
      rw [hv]
      have e : (21 / 20 * σ.tTwo * Real.sqrt σ.constK) ^ 2 =
          (21 / 20) ^ 2 * σ.tTwo * (σ.tTwo * σ.constK) := by rw [mul_pow, mul_pow, hK]; ring
      rw [e]
      have hK0 := σ.constK_pos
      have ht0 : 0 < σ.tTwo := by
        have : 0 < σ.tTwo * σ.constK := by rw [← hv]; positivity
        exact pos_of_mul_pos_left this hK0.le
      nlinarith [mul_pos (by linarith : (0 : ℝ) < 1 - (21 / 20) ^ 2 * σ.tTwo) (mul_pos ht0 hK0)]
    exact lt_of_pow_lt_pow_left₀ 2 hv0.le hsq
  linarith

include hθ h₁ h₂ in
theorem regionTwo_nonneg_iffC {z : ℂ} (hz : 0 < z.im) :
    0 ≤ ConeLayout.regionTwo σ.tTwo (σ.fermiChart z) ↔ σ.foldH ≤ σ.etaTwoC z := by
  have h := σ.regionTwo_mulC hθ hz
  have hp := σ.etaTwoC_sub_pos hθ h₁ h₂ hz
  have hY := σ.fermiChart_im_pos hz
  have hE := σ.etaTwoC_pos hθ hz
  have hs := σ.sqrt_constK_pos
  have hsE : 0 < Real.sqrt σ.constK * σ.etaTwoC z := mul_pos hs hE
  constructor
  · intro hR
    by_contra hlt
    push Not at hlt
    have : (σ.fermiChart z).im * (σ.etaTwoC z - σ.foldH) *
        (σ.etaTwoC z - 21 / 20 * σ.tTwo * Real.sqrt σ.constK) < 0 :=
      mul_neg_of_neg_of_pos (mul_neg_of_pos_of_neg hY (by linarith)) hp
    nlinarith
  · intro hle
    have : 0 ≤ (σ.fermiChart z).im * (σ.etaTwoC z - σ.foldH) *
        (σ.etaTwoC z - 21 / 20 * σ.tTwo * Real.sqrt σ.constK) :=
      mul_nonneg (mul_nonneg hY.le (by linarith)) hp.le
    rw [← h, mul_comm] at this
    exact nonneg_of_mul_nonneg_left this hsE

include hθ in
theorem regionTwo_eq_zero_ofC {z : ℂ} (hz : 0 < z.im) (he : σ.etaTwoC z = σ.foldH) :
    ConeLayout.regionTwo σ.tTwo (σ.fermiChart z) = 0 := by
  have h := σ.regionTwo_mulC hθ hz
  rw [he, sub_self, mul_zero, zero_mul] at h
  have hsE : 0 < Real.sqrt σ.constK * σ.foldH := mul_pos σ.sqrt_constK_pos σ.foldH_pos
  rcases mul_eq_zero.1 h with h' | h'
  · linarith
  · exact h'

include hθ h₁ h₂ in
theorem inner_core_of_lensC {z : ℂ} (hz : z ∈ σ.triangle) (h0 : σ.foldH ≤ σ.etaTwoC z)
    (h1 : σ.foldH ≤ σ.etaOne z) (hL : σ.sinhN z = 1 / 10) :
    normSq (σ.fermiChart z - ConeLayout.coreCentre) < ConeLayout.coreInner ^ 2 := by
  refine ConeLayout.lens_mem_core σ.tOne_pos.le (σ.tOne_le h₁ h₂) (σ.tTwo_le h₁ h₂)
    (σ.fermiChart_im_pos hz.1) ?_ (σ.tOne_mul_normSq_fermiChart_le hz)
    (σ.tTwo_le_normSq_fermiChart hz) ((σ.regionOne_nonneg_iff h₁ h₂ hz.1).2 h1)
    ((σ.regionTwo_nonneg_iffC hθ h₁ h₂ hz.1).2 h0)
  rw [σ.chart_neg_re hz.1, hL, ConeLayout.lensWidth]

include hθ h₁ h₂ in
theorem inner_core_of_windowTwoC {z : ℂ} (hz : z ∈ σ.triangle) (he : σ.etaTwoC z = σ.foldH)
    (hw1 : 1 / 10 ≤ σ.sinhN z) (hw2 : σ.sinhN z ≤ 7 / 50) :
    normSq (σ.fermiChart z - ConeLayout.coreCentre) < ConeLayout.coreInner ^ 2 := by
  have hY := σ.fermiChart_im_pos hz.1
  refine ConeLayout.windowTwo_mem_core (σ.tTwo_le h₁ h₂) hY ?_ ?_
    (σ.regionTwo_eq_zero_ofC hθ hz.1 he) (σ.tTwo_le_normSq_fermiChart hz)
  · rw [σ.chart_neg_re hz.1, ConeLayout.lensWidth]
    exact mul_le_mul_of_nonneg_right hw1 hY.le
  · rw [σ.chart_neg_re hz.1, ConeLayout.windowEnd]
    exact mul_le_mul_of_nonneg_right hw2 hY.le

include h₁ h₂ in
theorem foldPhiB_lt_of_lens {z : ℂ} (hz : z ∈ σ.domOne) (h1 : σ.foldH ≤ σ.etaOne z)
    (hφ : 0 ≤ discAngle (σ.discOne z) ∧ discAngle (σ.discOne z) ≤ σ.θ₁)
    (hs : σ.sinhN z < 1 / 10) : σ.foldPhiB < discAngle (σ.discOne z) := by
  have hD := σ.foldSD_pos h₁ h₂
  have hH := σ.foldH_pos
  have hmono := σ.sinhRad_le_sinhRad hH h1
  have hθ := σ.θ₁_le
  have hsin0 : 0 ≤ Real.sin (σ.θ₁ - discAngle (σ.discOne z)) :=
    Real.sin_nonneg_of_nonneg_of_le_pi (by linarith) (by linarith [hφ.1, Real.pi_pos])
  rw [σ.sinhN_eq_sinhRad hz] at hs
  have h2 : σ.foldSD * Real.sin (σ.θ₁ - discAngle (σ.discOne z)) < 1 / 10 :=
    lt_of_le_of_lt (mul_le_mul_of_nonneg_right hmono hsin0) hs
  have h3 : Real.sin (σ.θ₁ - discAngle (σ.discOne z)) < Real.sin (σ.θ₁ - σ.foldPhiB) := by
    rw [σ.sin_sub_foldPhiB h₁ h₂, lt_div_iff₀ hD]
    linarith [mul_comm σ.foldSD (Real.sin (σ.θ₁ - discAngle (σ.discOne z)))]
  have hb := σ.foldPhiB_pos h₁ h₂
  have hb' := σ.foldPhiB_lt h₁ h₂
  by_contra hle
  push Not at hle
  have : Real.sin (σ.θ₁ - σ.foldPhiB) ≤ Real.sin (σ.θ₁ - discAngle (σ.discOne z)) :=
    Real.sin_le_sin_of_le_of_le_pi_div_two (by linarith [Real.pi_pos]) (by linarith) (by linarith)
  linarith

include hθ in
theorem im_le_etaTwoC {z : ℂ} (hz : z ∈ σ.domZeroC) : z.im ≤ σ.etaTwoC z := by
  have h := σ.etaTwoC_sub_im hθ hz
  have := σ.cofZeroC_pos hθ hz
  nlinarith [sq_nonneg (σ.wallZeroC z)]

end Layout

/-! ### Branches and local forms -/

section Local

variable (hθ : 0 < σ.θ₂) (h₁ : Real.cos σ.θ₁ = 0 ∨ 1 / 2 ≤ Real.cos σ.θ₁)
  (h₂ : Real.cos σ.θ₂ = 0 ∨ 1 / 2 ≤ Real.cos σ.θ₂)

theorem foldE₂_of_two {p q : ℕ} {z : ℂ} (h2 : σ.etaTwoC z < σ.foldH) :
    σ.foldE₂ hθ p q z = σ.regionTwoC hθ q z := by
  simp only [foldE₂, h2, ↓reduceIte]

theorem foldE₂_of_one {p q : ℕ} {z : ℂ} (h2 : σ.foldH ≤ σ.etaTwoC z)
    (h1 : σ.etaOne z < σ.foldH) : σ.foldE₂ hθ p q z = σ.coneRegion p z := by
  simp only [foldE₂, not_lt.2 h2, h1, ↓reduceIte]

theorem foldE₂_of_lens {p q : ℕ} {z : ℂ} (h2 : σ.foldH ≤ σ.etaTwoC z)
    (h1 : σ.foldH ≤ σ.etaOne z) (hL : |σ.sinhN z| < 1 / 10) :
    σ.foldE₂ hθ p q z = σ.bridgeTwoC z := by
  simp only [foldE₂, not_lt.2 h2, not_lt.2 h1, hL, ↓reduceIte]

theorem foldE₂_of_inf {p q : ℕ} {z : ℂ} (h2 : σ.foldH ≤ σ.etaTwoC z)
    (h1 : σ.foldH ≤ σ.etaOne z) (hL : 1 / 10 ≤ |σ.sinhN z|) :
    σ.foldE₂ hθ p q z = σ.cornerInfC σ.blendWeight σ.foldY₁ σ.foldY₂ z := by
  simp only [foldE₂, not_lt.2 h2, not_lt.2 h1, not_lt.2 hL, ↓reduceIte]

def LocalForm (F : ℂ → ℂ) (z : ℂ) : Prop :=
  ∃ g : ℂ → ℂ, ∃ D : Set ℂ, IsOpen D ∧ z ∈ D ∧ ContDiffOn ℝ ∞ g D ∧ F =ᶠ[𝓝 z] g ∧
    (z ≠ σ.vertexOne → z ≠ σ.vertexTwo → (fderiv ℝ g z).det ≠ 0)

theorem localForm_of_eventuallyEq {F G : ℂ → ℂ} {z : ℂ} (h : F =ᶠ[𝓝 z] G)
    (hG : σ.LocalForm G z) : σ.LocalForm F z := by
  obtain ⟨g, D, hD, hzD, hg, hGg, hdet⟩ := hG
  exact ⟨g, D, hD, hzD, hg, h.trans hGg, hdet⟩

include hθ h₁ h₂ in
theorem foldE₂_local_two {p q : ℕ} (hq : 1 ≤ q) {z : ℂ} (hz : z ∈ σ.triangle)
    (h2 : σ.etaTwoC z < σ.foldH) : σ.LocalForm (σ.foldE₂ hθ p q) z := by
  obtain ⟨g, D, hD, hzD, hg, hEg, hdet⟩ := σ.regionTwoC_local hθ h₁ h₂ hq hz h2.le
  refine σ.localForm_of_eventuallyEq ?_ ⟨g, D, hD, hzD, hg, hEg, fun _ h => hdet h⟩
  filter_upwards [(σ.continuousAt_etaTwoC hθ hz.1).eventually_lt continuousAt_const h2] with w hw
  exact σ.foldE₂_of_two hθ hw

include hθ h₁ h₂ in
theorem foldE₂_local_one {p q : ℕ} (hp : 1 ≤ p) {z : ℂ} (hz : z ∈ σ.triangle)
    (h2 : σ.foldH < σ.etaTwoC z) (h1 : σ.etaOne z < σ.foldH) :
    σ.LocalForm (σ.foldE₂ hθ p q) z := by
  obtain ⟨g, D, hD, hzD, hg, hEg, hdet⟩ := σ.coneRegion_local hθ h₁ h₂ hp hz h1.le
  refine σ.localForm_of_eventuallyEq ?_ ⟨g, D, hD, hzD, hg, hEg, fun h _ => hdet h⟩
  filter_upwards [continuousAt_const.eventually_lt (σ.continuousAt_etaTwoC hθ hz.1) h2,
    (σ.continuousAt_etaOne hz.1).eventually_lt continuousAt_const h1] with w hw2 hw1
  exact σ.foldE₂_of_one hθ hw2.le hw1

include hθ h₁ h₂ in
theorem foldE₂_local_J1 {p q : ℕ} (hq : 1 ≤ q) {z : ℂ} (hz : z ∈ σ.triangle)
    (he : σ.etaTwoC z = σ.foldH) (hs : σ.sinhN z < 1 / 10 ∨ 7 / 50 < σ.sinhN z) :
    σ.LocalForm (σ.foldE₂ hθ p q) z := by
  obtain ⟨g, D, hD, hzD, hg, hEg, hdet⟩ := σ.regionTwoC_local hθ h₁ h₂ hq hz he.le
  refine σ.localForm_of_eventuallyEq ?_ ⟨g, D, hD, hzD, hg, hEg, fun _ h => hdet h⟩
  obtain ⟨hv1, hv2⟩ := σ.ne_vertices_of_etaTwoC_eq hθ h₁ h₂ hz.1 he
  have h1 : σ.foldH < σ.etaOne z := σ.foldH_lt_etaOne_of_etaTwoC_le hθ hz.1 he.le
  have hsn := σ.sinhN_nonneg_of_mem_triangle hz
  have h1e := continuousAt_const.eventually_lt (σ.continuousAt_etaOne hz.1) h1
  rcases hs with hs | hs
  · have hb := σ.regionTwoC_eventually_bridgeTwoC hθ h₁ h₂ (q := q) hz he hs
    have hs' : |σ.sinhN z| < 1 / 10 := by rwa [abs_of_nonneg hsn]
    filter_upwards [hb, h1e, (continuous_abs.continuousAt.comp
      (σ.continuousAt_sinhN hz.1)).eventually_lt continuousAt_const hs'] with w hwb hw1 hwL
    by_cases hw2 : σ.etaTwoC w < σ.foldH
    · rw [σ.foldE₂_of_two hθ hw2, hwb]
    · rw [σ.foldE₂_of_lens hθ (not_lt.1 hw2) hw1.le hwL, hwb]
  · have hb := σ.regionTwoC_eventually_bridgeZeroC hθ h₁ h₂ (q := q) hz he hs
    have hs' : 1 / 10 < |σ.sinhN z| := by rw [abs_of_nonneg hsn]; linarith
    have hd0 := σ.mem_domZeroC_of_mem_triangle hθ hz hv2
    have hbl : σ.blendFn z < -1 / 2 := by
      have := σ.blendFn_le_of_etaTwo_le hz.1 (σ.re_le_width_of_mem_triangle hz)
        (by rw [σ.etaTwo_eq_of_cone hθ, he, foldH_eq])
      linarith
    have hy : z.im < σ.foldY₁ :=
      lt_of_le_of_lt (le_trans (σ.im_le_etaTwoC hθ hd0) he.le) σ.foldH_lt_foldY₁
    filter_upwards [hb, h1e, continuousAt_const.eventually_lt
      (continuous_abs.continuousAt.comp (σ.continuousAt_sinhN hz.1)) hs',
      (σ.continuousAt_blendFnC hθ hz.1).eventually_lt continuousAt_const hbl,
      continuous_im.continuousAt.eventually_lt continuousAt_const hy,
      (σ.isOpen_domZeroC hθ).mem_nhds hd0] with w hwb hw1 hwL hwbl hwy hwd
    by_cases hw2 : σ.etaTwoC w < σ.foldH
    · rw [σ.foldE₂_of_two hθ hw2, hwb]
    · rw [σ.foldE₂_of_inf hθ (not_lt.1 hw2) hw1.le hwL.le, hwb]
      exact σ.cornerInfC_eq_bridgeZeroC hθ σ.foldY₁_lt_foldY₂ hwd
        (σ.blendWeight_eq_zero hwbl.le) hwy.le

include hθ h₁ h₂ in
theorem foldE₂_local_J2 {p q : ℕ} (hp : 1 ≤ p) {z : ℂ} (hz : z ∈ σ.triangle)
    (h2 : σ.foldH < σ.etaTwoC z) (he : σ.etaOne z = σ.foldH)
    (hs : σ.sinhN z < 1 / 10 ∨ 7 / 50 < σ.sinhN z) : σ.LocalForm (σ.foldE₂ hθ p q) z := by
  obtain ⟨g, D, hD, hzD, hg, hEg, hdet⟩ := σ.coneRegion_local hθ h₁ h₂ hp hz he.le
  refine σ.localForm_of_eventuallyEq ?_ ⟨g, D, hD, hzD, hg, hEg, fun h _ => hdet h⟩
  have hsn := σ.sinhN_nonneg_of_mem_triangle hz
  have h2e := continuousAt_const.eventually_lt (σ.continuousAt_etaTwoC hθ hz.1) h2
  have hAB := σ.foldA₁_lt_foldB₁ h₁ h₂
  have hBH := σ.foldB₁_lt_foldH h₁ h₂
  have hzv := σ.ne_vertexOne_of_foldA₁_le h₁ h₂ (by rw [he]; linarith)
  rcases hs with hs | hs
  · have hb := σ.coneRegion_eventually_bridgeTwoC hθ h₁ h₂ (p := p) hz he hs
    have hs' : |σ.sinhN z| < 1 / 10 := by rwa [abs_of_nonneg hsn]
    filter_upwards [hb, h2e, (continuous_abs.continuousAt.comp
      (σ.continuousAt_sinhN hz.1)).eventually_lt continuousAt_const hs'] with w hwb hw2 hwL
    by_cases hw1 : σ.etaOne w < σ.foldH
    · rw [σ.foldE₂_of_one hθ hw2.le hw1, hwb]
    · rw [σ.foldE₂_of_lens hθ hw2.le (not_lt.1 hw1) hwL, hwb]
  · have hb := σ.coneRegion_eventually_bridgeOne h₁ h₂ (p := p) hz he hs
    have hs' : 1 / 10 < |σ.sinhN z| := by rw [abs_of_nonneg hsn]; linarith
    have hd1 := σ.mem_domOne_of_mem_triangle hz hzv
    have hbl : 1 / 2 < σ.blendFn z := by
      have := σ.one_le_blendFn_of_etaOne_le hz.1 (σ.re_nonneg_of_triangle hz)
        (by change σ.etaOne z ≤ _; rw [he, foldH_eq])
      linarith
    have hy : z.im < σ.foldY₁ :=
      lt_of_le_of_lt (le_trans (σ.im_le_etaOne hd1) he.le) σ.foldH_lt_foldY₁
    filter_upwards [hb, h2e, continuousAt_const.eventually_lt
      (continuous_abs.continuousAt.comp (σ.continuousAt_sinhN hz.1)) hs',
      continuousAt_const.eventually_lt (σ.continuousAt_blendFnC hθ hz.1) hbl,
      continuous_im.continuousAt.eventually_lt continuousAt_const hy,
      σ.isOpen_domOne.mem_nhds hd1] with w hwb hw2 hwL hwbl hwy hwd
    by_cases hw1 : σ.etaOne w < σ.foldH
    · rw [σ.foldE₂_of_one hθ hw2.le hw1, hwb]
    · rw [σ.foldE₂_of_inf hθ hw2.le (not_lt.1 hw1) hwL.le, hwb]
      exact σ.cornerInfC_eq_bridgeOne σ.foldY₁_lt_foldY₂ hwd (σ.blendWeight_eq_one hwbl.le)
        hwy.le

include hθ h₁ h₂ in
theorem foldE₂_local_lens {p q : ℕ} (hp : 1 ≤ p) {z : ℂ} (hz : z ∈ σ.triangle)
    (h2 : σ.foldH < σ.etaTwoC z) (h1 : σ.foldH < σ.etaOne z) (hL : |σ.sinhN z| < 1 / 10) :
    σ.LocalForm (σ.foldE₂ hθ p q) z := by
  have hAB := σ.foldA₁_lt_foldB₁ h₁ h₂
  have hBH := σ.foldB₁_lt_foldH h₁ h₂
  have hφ := σ.foldPhiA_lt_foldPhiB h₁ h₂
  have hzv := σ.ne_vertexOne_of_foldA₁_le h₁ h₂ (by linarith)
  have hzv2 : z ≠ σ.vertexTwo := by
    rintro rfl
    have h0 : σ.etaTwoC σ.vertexTwo = σ.vertexTwo.im := by
      simp [etaTwoC, coneHeight, coneDisc_self]
    have := σ.vertexTwo_im_lt_foldH hθ h₁ h₂
    linarith
  have hz1 := σ.mem_domOne_of_mem_triangle hz hzv
  have hz2 := σ.mem_domTwoC_of_mem_triangle hθ hz hzv hzv2
  have hφb := σ.foldPhiB_lt_of_lens h₁ h₂ hz1 h1.le (σ.discAngle_mem_of_mem_triangle hz hzv)
    (lt_of_le_of_lt (le_abs_self _) hL)
  have hb : σ.foldB₁ < σ.etaOne z := by linarith
  have hcc : σ.cornerConeC p σ.foldA₁ σ.foldB₁ σ.foldPhiA σ.foldPhiB =ᶠ[𝓝 z] σ.bridgeTwoC := by
    filter_upwards [(σ.isOpen_domTwoC hθ).mem_nhds hz2,
      continuousAt_const.eventually_lt (σ.continuousAt_etaOne hz.1) hb,
      continuousAt_const.eventually_lt (σ.continuousAt_discAngle hz1) hφb] with w hw2 hwb hwφ
    exact σ.cornerConeC_eq_bridgeTwoC hθ p hAB hφ hw2 hwb.le hwφ.le
  refine ⟨σ.cornerConeC p σ.foldA₁ σ.foldB₁ σ.foldPhiA σ.foldPhiB, σ.domOne ∩ σ.domTwoC,
    σ.isOpen_domOne.inter (σ.isOpen_domTwoC hθ), ⟨hz1, hz2⟩,
    fun w hw => (σ.contDiffAt_cornerConeC hθ p _ _ _ _ hw.1 hw.2).contDiffWithinAt, ?_,
    fun _ _ => ?_⟩
  · filter_upwards [hcc, continuousAt_const.eventually_lt (σ.continuousAt_etaTwoC hθ hz.1) h2,
      continuousAt_const.eventually_lt (σ.continuousAt_etaOne hz.1) h1,
      (continuous_abs.continuousAt.comp (σ.continuousAt_sinhN hz.1)).eventually_lt
        continuousAt_const hL] with w hcw hw2 hw1 hwL
    rw [σ.foldE₂_of_lens hθ hw2.le hw1.le hwL, hcw]
  · exact σ.det_fderiv_cornerConeC_ne_zero hθ hp hAB hφ hz1 hz2
      (σ.angleTwoConeC_le_angleOneCone hθ hz1 hz2 (σ.wallOne_nonneg_of_mem_triangle hz)
        (σ.wallTwo_nonneg_of_mem_triangle hz))

include hθ h₁ h₂ in
theorem foldE₂_local_inf {p q : ℕ} {z : ℂ} (hz : z ∈ σ.triangle)
    (h2 : σ.foldH < σ.etaTwoC z) (h1 : σ.foldH < σ.etaOne z) (hL : 1 / 10 < |σ.sinhN z|) :
    σ.LocalForm (σ.foldE₂ hθ p q) z := by
  have hAB := σ.foldA₁_lt_foldB₁ h₁ h₂
  have hBH := σ.foldB₁_lt_foldH h₁ h₂
  have hzv := σ.ne_vertexOne_of_foldA₁_le h₁ h₂ (by linarith)
  have hzv2 : z ≠ σ.vertexTwo := by
    rintro rfl
    have h0 : σ.etaTwoC σ.vertexTwo = σ.vertexTwo.im := by
      simp [etaTwoC, coneHeight, coneDisc_self]
    have := σ.vertexTwo_im_lt_foldH hθ h₁ h₂
    linarith
  have hz1 := σ.mem_domOne_of_mem_triangle hz hzv
  have hz0 := σ.mem_domZeroC_of_mem_triangle hθ hz hzv2
  have hne2 : ∀ w ∈ σ.domZeroC, w ≠ σ.vertexTwo := by
    rintro w hw rfl
    have := hw.2
    rw [discTwo, coneDisc_self, norm_zero, zero_re, add_zero] at this
    exact lt_irrefl _ this
  refine ⟨σ.cornerInfC σ.blendWeight σ.foldY₁ σ.foldY₂, σ.domOne ∩ σ.domZeroC,
    σ.isOpen_domOne.inter (σ.isOpen_domZeroC hθ), ⟨hz1, hz0⟩,
    fun w hw => (σ.contDiffAt_cornerInfC hθ _ _ hw.1 hw.2 (σ.contDiffAt_blendWeightC hθ hw.1.1
      (σ.vertexOne_ne_of_domOne hw.1) (hne2 w hw.2))).contDiffWithinAt, ?_, fun _ _ => ?_⟩
  · filter_upwards [continuousAt_const.eventually_lt (σ.continuousAt_etaTwoC hθ hz.1) h2,
      continuousAt_const.eventually_lt (σ.continuousAt_etaOne hz.1) h1,
      continuousAt_const.eventually_lt
        (continuous_abs.continuousAt.comp (σ.continuousAt_sinhN hz.1)) hL] with w hw2 hw1 hwL
    exact σ.foldE₂_of_inf hθ hw2.le hw1.le hwL.le
  · obtain ⟨d, hd, hdd⟩ := σ.exists_hasDerivAt_blendWeight hz.1 hzv (fun _ => hzv2)
      (σ.re_nonneg_of_triangle hz) (σ.re_le_width_of_mem_triangle hz)
    exact σ.det_fderiv_cornerInfC_ne_zero hθ σ.foldY₁_pos.le σ.foldY₁_lt_foldY₂ σ.foldY₂_lt_sqrt
      σ.sqrt_constK_le_half hz1 hz0 (σ.contDiffAt_blendWeightC hθ hz.1 hzv hzv2) hdd hd
      (σ.blendWeight_nonneg z) (σ.blendWeight_le_one z)

include hθ h₁ h₂ in
theorem foldE₂_local {p q : ℕ} (hp : 1 ≤ p) (hq : 1 ≤ q) {z : ℂ} (hz : z ∈ σ.triangle)
    (hcore : ConeLayout.coreInner ^ 2 ≤ normSq (σ.fermiChart z - ConeLayout.coreCentre)) :
    σ.LocalForm (σ.foldE₂ hθ p q) z := by
  have hc : ¬ normSq (σ.fermiChart z - ConeLayout.coreCentre) < ConeLayout.coreInner ^ 2 :=
    not_lt.2 hcore
  have hsn := σ.sinhN_nonneg_of_mem_triangle hz
  rcases lt_trichotomy (σ.etaTwoC z) σ.foldH with h2 | h2 | h2
  · exact σ.foldE₂_local_two hθ h₁ h₂ hq hz h2
  · rcases lt_or_ge (σ.sinhN z) (1 / 10) with hs | hs
    · exact σ.foldE₂_local_J1 hθ h₁ h₂ hq hz h2 (Or.inl hs)
    rcases lt_or_ge (7 / 50) (σ.sinhN z) with hs' | hs'
    · exact σ.foldE₂_local_J1 hθ h₁ h₂ hq hz h2 (Or.inr hs')
    · exact absurd (σ.inner_core_of_windowTwoC hθ h₁ h₂ hz h2 hs hs') hc
  · rcases lt_trichotomy (σ.etaOne z) σ.foldH with h1 | h1 | h1
    · exact σ.foldE₂_local_one hθ h₁ h₂ hp hz h2 h1
    · rcases lt_or_ge (σ.sinhN z) (1 / 10) with hs | hs
      · exact σ.foldE₂_local_J2 hθ h₁ h₂ hp hz h2 h1 (Or.inl hs)
      rcases lt_or_ge (7 / 50) (σ.sinhN z) with hs' | hs'
      · exact σ.foldE₂_local_J2 hθ h₁ h₂ hp hz h2 h1 (Or.inr hs')
      · exact absurd (σ.inner_core_of_windowOne h₁ h₂ hz h1 hs hs') hc
    · rcases lt_trichotomy |σ.sinhN z| (1 / 10) with hL | hL | hL
      · exact σ.foldE₂_local_lens hθ h₁ h₂ hp hz h2 h1 hL
      · rw [abs_of_nonneg hsn] at hL
        exact absurd (σ.inner_core_of_lensC hθ h₁ h₂ hz h2.le h1.le hL) hc
      · exact σ.foldE₂_local_inf hθ h₁ h₂ hz h2 h1 hL

include hθ h₁ h₂ in
theorem foldE₂_eventually_apexOne {p q : ℕ} :
    σ.foldE₂ hθ p q =ᶠ[𝓝 σ.vertexOne] σ.apexBefore p := by
  have hv := σ.vertexOne_im_pos
  have h1 : σ.etaOne σ.vertexOne < σ.foldH := by
    rw [σ.etaOne_vertexOne]; exact σ.vertexOne_im_lt_foldH h₁ h₂
  have h2 : σ.foldH < σ.etaTwoC σ.vertexOne := σ.foldH_lt_etaTwoC_of_etaOne_le hθ hv h1.le
  filter_upwards [continuousAt_const.eventually_lt (σ.continuousAt_etaTwoC hθ hv) h2,
    (σ.continuousAt_etaOne hv).eventually_lt continuousAt_const h1,
    σ.coneRegion_eventually_apex h₁ h₂ (p := p)] with w hw2 hw1 hwa
  rw [σ.foldE₂_of_one hθ hw2.le hw1, hwa]

include hθ h₁ h₂ in
theorem foldE₂_eventually_apexTwo {p q : ℕ} :
    σ.foldE₂ hθ p q =ᶠ[𝓝 σ.vertexTwo] σ.apexTwoBefore q := by
  have hv := σ.vertexTwo_im_pos hθ
  have h2 : σ.etaTwoC σ.vertexTwo < σ.foldH := by
    have h0 : σ.etaTwoC σ.vertexTwo = σ.vertexTwo.im := by
      simp [etaTwoC, coneHeight, coneDisc_self]
    rw [h0]; exact σ.vertexTwo_im_lt_foldH hθ h₁ h₂
  filter_upwards [(σ.continuousAt_etaTwoC hθ hv).eventually_lt continuousAt_const h2,
    σ.regionTwoC_eventually_apex hθ h₁ h₂ (q := q)] with w hw2 hwa
  rw [σ.foldE₂_of_two hθ hw2, hwa]

include hθ in
theorem det_fderiv_apexTwoBefore_ne_zero {q : ℕ} (hq : q ≠ 0) {z : ℂ} (hz : 0 < z.im)
    (hzv : z ≠ σ.vertexTwo) : (fderiv ℝ (σ.apexTwoBefore q) z).det ≠ 0 := by
  have he : σ.apexTwoBefore q = fun w => -conj ((σ.swap hθ).apexBefore q (σ.swapPt w)) :=
    funext fun w => (σ.swap_apexBefore hθ q w).symm
  have hs : 0 < (σ.swapPt z).im := by simpa using hz
  rw [he, σ.det_fderiv_mirror ((((σ.swap hθ).contDiffAt_apexBefore q hs)).differentiableAt
    (by simp))]
  exact (σ.swap hθ).det_fderiv_apexBefore_ne_zero hq hs ((σ.swapPt_ne_vertexOne_iff hθ).2 hzv)

include hθ h₁ h₂ in
theorem foldE₂_good {p q : ℕ} (hp : 1 ≤ p) (hq : 1 ≤ q) {z : ℂ} (hz : z ∈ σ.triangle)
    (hcore : ConeLayout.coreInner ^ 2 ≤ normSq (σ.fermiChart z - ConeLayout.coreCentre)) :
    ∀ᶠ w in 𝓝 z, 0 < w.im ∧ ContDiffAt ℝ ∞ (σ.foldE₂ hθ p q) w ∧
      (w ≠ σ.vertexOne → w ≠ σ.vertexTwo → (fderiv ℝ (σ.foldE₂ hθ p q) w).det ≠ 0) := by
  have hup := isOpen_upper.mem_nhds hz.1
  by_cases hzv : z = σ.vertexOne
  · subst hzv
    have ha := σ.foldE₂_eventually_apexOne hθ h₁ h₂ (p := p) (q := q)
    filter_upwards [hup, ha.eventuallyEq_nhds] with w hw hwe
    refine ⟨hw, (σ.contDiffAt_apexBefore p hw).congr_of_eventuallyEq hwe, fun hwv _ => ?_⟩
    rw [hwe.fderiv_eq]
    exact σ.det_fderiv_apexBefore_ne_zero (by omega) hw hwv
  by_cases hzv2 : z = σ.vertexTwo
  · subst hzv2
    have ha := σ.foldE₂_eventually_apexTwo hθ h₁ h₂ (p := p) (q := q)
    filter_upwards [hup, ha.eventuallyEq_nhds] with w hw hwe
    refine ⟨hw, (σ.contDiffAt_apexTwoBefore hθ q hw).congr_of_eventuallyEq hwe,
      fun _ hwv => ?_⟩
    rw [hwe.fderiv_eq]
    exact σ.det_fderiv_apexTwoBefore_ne_zero hθ (by omega) hw hwv
  obtain ⟨g, D, hD, hzD, hg, hEg, hdet⟩ := σ.foldE₂_local hθ h₁ h₂ hp hq hz hcore
  filter_upwards [hup, hD.mem_nhds hzD, hEg.eventuallyEq_nhds,
    eventually_det_ne_zero hD hg hzD (hdet hzv hzv2)] with w hw hwD hwe hwdet
  refine ⟨hw, (hg.contDiffAt (hD.mem_nhds hwD)).congr_of_eventuallyEq hwe, fun _ _ => ?_⟩
  rw [hwe.fderiv_eq]
  exact hwdet

end Local

end ConeShape

end GC.Seifert
