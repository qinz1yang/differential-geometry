import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Seifert.ConeFoldTwoConeCore

/-!
# Wall identities and wall values of the assembled two-cone fold

Lane A4b3 (design `docs/geometrization/handoffs/20261004-design-a4-cone-fold.md`, §5–§6, J5 and
erratum 2, two-cone shapes). For each wall `i` an open set containing the wall of the triangle on
which `foldE₂` is equivariant for the wall reflection:
* wall 1: `wallSetOneC`, outside `R₂`, the apex zone at `v₁`, or `|φ₁| < foldPhiA` with either
  `η₁ < h` (cone region) or `sinh n > 1/10` and blend weight `1` (corner at `∞`)
  (`foldE₂_refl_one`);
* wall 0: `wallSetZeroC = swapPt⁻¹ (wallSetOneC of the swap)`, the same conditions at `v₂` with
  blend weight `0` (`swap_blendFn`: the swap negates the blend function) (`foldE₂_refl_zero`);
* wall 2: `wallSetTwoC`, the band `|sinh n| < 1/80` with `cos(θᵢ - φᵢ) > 0` outside both apex zones,
  where both cone regions are pure in the angle and the lens branch is the globally equivariant
  bridge `bridgeTwoC` (`foldE₂_refl_two`).
The walls of the triangle lie in these sets (`foldWall_subset_wallSetC`), and the wall values are
the one-sided segments required by `bijOn_of_local'` before the mirror (`foldE₂_wall_zero_re`,
`foldE₂_wall_one_re`, `foldE₂_wall_two_re`).
-/

set_option autoImplicit false

noncomputable section

open Complex Filter Set Metric
open scoped ComplexConjugate ContDiff Topology

namespace GC.Seifert

namespace ConeShape

variable (σ : ConeShape)

def wallSetOneC : Set ℂ :=
  {z | 0 < z.im ∧ σ.foldH < σ.etaTwoC z ∧ (σ.etaOne z < σ.foldA₁ ∨ (z ∈ σ.domOne ∧
    |discAngle (σ.discOne z)| < σ.foldPhiA ∧
      (σ.etaOne z < σ.foldH ∨ (1 / 10 < σ.sinhN z ∧ 1 / 2 < σ.blendFn z))))}

def wallSetZeroC (hθ : 0 < σ.θ₂) : Set ℂ := σ.swapPt ⁻¹' (σ.swap hθ).wallSetOneC

def conePartTwo : Set ℂ :=
  {w | 0 < w.im ∧ (σ.etaOne w < σ.foldA₁ ∨
    (w ∈ σ.domOne ∧ 0 < (exp (-(σ.θ₁ * I)) * σ.discOne w).re))}

def wallSetTwoC (hθ : 0 < σ.θ₂) : Set ℂ :=
  {z | |σ.sinhN z| < 1 / 80} ∩ σ.conePartTwo ∩ σ.swapPt ⁻¹' (σ.swap hθ).conePartTwo

def wallSetC (hθ : 0 < σ.θ₂) : Fin 3 → Set ℂ
  | 0 => σ.wallSetZeroC hθ
  | 1 => σ.wallSetOneC
  | 2 => σ.wallSetTwoC hθ

theorem etaTwoC_refl_zero (z : ℂ) : σ.etaTwoC (σ.refl 0 z) = σ.etaTwoC z := by
  simp only [etaTwoC, coneHeight]
  rw [← discTwo, ← discTwo, σ.discTwo_refl_zero, Complex.norm_conj]

theorem swap_blendFn (hθ : 0 < σ.θ₂) (z : ℂ) :
    (σ.swap hθ).blendFn (σ.swapPt z) = -σ.blendFn z := by
  have hW := σ.width_pos
  have h1 := σ.etaOne_pos (z := z)
  have e1 : (σ.swap hθ).etaTwo (σ.swapPt z) = σ.etaOne z := by
    rw [(σ.swap hθ).etaTwo_eq_of_cone σ.θ₁_pos, σ.swap_etaTwoC hθ]
  have e2 : coneHeight (σ.swap hθ).vertexOne (σ.swapPt z) = σ.etaTwoC z := σ.swap_etaOne hθ z
  have e3 : σ.etaTwo z = σ.etaTwoC z := by rw [σ.etaTwo_eq_of_cone hθ]
  have e4 : coneHeight σ.vertexOne z = σ.etaOne z := rfl
  rw [blendFn, blendFn, e1, e2, e3, e4, σ.swap_width hθ, swapPt_re]
  by_cases hs : σ.etaTwoC z + σ.etaOne z = 0
  · have hs' : σ.etaOne z + σ.etaTwoC z = 0 := by linarith
    rw [hs, hs', div_zero, div_zero]
    field_simp
    ring
  · have hs' : σ.etaOne z + σ.etaTwoC z ≠ 0 := by intro h; apply hs; linarith
    field_simp
    ring

theorem continuousAt_discAngle' {z : ℂ} (hz : z ∈ σ.domOne) :
    ContinuousAt (fun u => discAngle (σ.discOne u)) z := σ.continuousAt_discAngle hz

theorem isOpen_wallSetOneC (hθ : 0 < σ.θ₂) : IsOpen σ.wallSetOneC := by
  rw [isOpen_iff_mem_nhds]
  rintro z ⟨hz0, h2, hz1⟩
  have hup := isOpen_upper.mem_nhds hz0
  have h2e := continuousAt_const.eventually_lt (σ.continuousAt_etaTwoC hθ hz0) h2
  change σ.wallSetOneC ∈ 𝓝 z
  rcases hz1 with h | ⟨hd, hφ, h'⟩
  · filter_upwards [hup, h2e, (σ.continuousAt_etaOne hz0).eventually_lt continuousAt_const h]
      with w hw hw2 hw1
    exact ⟨hw, hw2, Or.inl hw1⟩
  · have hφe : ∀ᶠ w in 𝓝 z, |discAngle (σ.discOne w)| < σ.foldPhiA :=
      (continuous_abs.continuousAt.comp (σ.continuousAt_discAngle hd)).eventually_lt
        continuousAt_const hφ
    have hde := σ.isOpen_domOne.mem_nhds hd
    rcases h' with h1 | ⟨hs, hb⟩
    · filter_upwards [hup, h2e, hφe, hde,
        (σ.continuousAt_etaOne hz0).eventually_lt continuousAt_const h1] with w hw hw2 hwφ hwd hw1
      exact ⟨hw, hw2, Or.inr ⟨hwd, hwφ, Or.inl hw1⟩⟩
    · filter_upwards [hup, h2e, hφe, hde,
        continuousAt_const.eventually_lt (σ.continuousAt_sinhN hz0) hs,
        continuousAt_const.eventually_lt (σ.continuousAt_blendFnC hθ hz0) hb]
        with w hw hw2 hwφ hwd hws hwb
      exact ⟨hw, hw2, Or.inr ⟨hwd, hwφ, Or.inr ⟨hws, hwb⟩⟩⟩

theorem isOpen_wallSetZeroC (hθ : 0 < σ.θ₂) : IsOpen (σ.wallSetZeroC hθ) :=
  ((σ.swap hθ).isOpen_wallSetOneC σ.θ₁_pos).preimage σ.continuous_swapPt

theorem isOpen_conePartTwo : IsOpen σ.conePartTwo := by
  rw [isOpen_iff_mem_nhds]
  rintro z ⟨hz0, h⟩
  have hup := isOpen_upper.mem_nhds hz0
  change σ.conePartTwo ∈ 𝓝 z
  rcases h with h | ⟨hd, hc⟩
  · filter_upwards [hup, (σ.continuousAt_etaOne hz0).eventually_lt continuousAt_const h]
      with w hw hw1
    exact ⟨hw, Or.inl hw1⟩
  · filter_upwards [hup, σ.isOpen_domOne.mem_nhds hd,
      continuousAt_const.eventually_lt (σ.continuousAt_rotRe hz0) hc] with w hw hwd hwc
    exact ⟨hw, Or.inr ⟨hwd, hwc⟩⟩

theorem isOpen_wallSetTwoC (hθ : 0 < σ.θ₂) : IsOpen (σ.wallSetTwoC hθ) := by
  rw [isOpen_iff_mem_nhds]
  rintro z ⟨⟨hs, hc⟩, hc'⟩
  have hz0 := hc.1
  have h1 := σ.isOpen_conePartTwo.mem_nhds hc
  have h2 := ((σ.swap hθ).isOpen_conePartTwo.preimage σ.continuous_swapPt).mem_nhds hc'
  have h3 : ∀ᶠ w in 𝓝 z, |σ.sinhN w| < 1 / 80 :=
    (continuous_abs.continuousAt.comp (σ.continuousAt_sinhN hz0)).eventually_lt
      continuousAt_const hs
  filter_upwards [h1, h2, h3] with w hw1 hw2 hw3
  exact ⟨⟨hw3, hw1⟩, hw2⟩

theorem isOpen_wallSetC (hθ : 0 < σ.θ₂) (i : Fin 3) : IsOpen (σ.wallSetC hθ i) := by
  fin_cases i
  · exact σ.isOpen_wallSetZeroC hθ
  · exact σ.isOpen_wallSetOneC hθ
  · exact σ.isOpen_wallSetTwoC hθ

section Identities

variable (hθ : 0 < σ.θ₂) (h₁ : Real.cos σ.θ₁ = 0 ∨ 1 / 2 ≤ Real.cos σ.θ₁)
  (h₂ : Real.cos σ.θ₂ = 0 ∨ 1 / 2 ≤ Real.cos σ.θ₂)

include hθ h₁ h₂ in
theorem foldE₂_refl_one {p q : ℕ} {z : ℂ} (hz : z ∈ σ.wallSetOneC)
    (hz' : σ.refl 1 z ∈ σ.wallSetOneC) :
    σ.foldE₂ hθ p q (σ.refl 1 z) = conj (σ.foldE₂ hθ p q z) := by
  have hAB := σ.foldA₁_lt_foldB₁ h₁ h₂
  have hBH := σ.foldB₁_lt_foldH h₁ h₂
  have e1 := σ.etaOne_refl_one z
  obtain ⟨hz0, h2, hz1⟩ := hz
  obtain ⟨hz0', h2', hz1'⟩ := hz'
  by_cases h1 : σ.etaOne z < σ.foldH
  · have h1' : σ.etaOne (σ.refl 1 z) < σ.foldH := by rw [e1]; exact h1
    rw [σ.foldE₂_of_one hθ h2.le h1, σ.foldE₂_of_one hθ h2'.le h1']
    refine σ.coneRegion_refl_one h₁ h₂ z ?_
    rcases hz1 with h | ⟨-, hφ, -⟩
    · exact Or.inl h
    · exact Or.inr hφ
  · push Not at h1
    have ha : ¬ σ.etaOne z < σ.foldA₁ := not_lt.2 (by linarith)
    obtain ⟨-, -, hrest⟩ := hz1.resolve_left ha
    obtain ⟨-, -, hrest'⟩ := hz1'.resolve_left (by rw [e1]; exact ha)
    obtain ⟨hs, hb⟩ := hrest.resolve_left (not_lt.2 h1)
    obtain ⟨hs', hb'⟩ := hrest'.resolve_left (by rw [e1]; exact not_lt.2 h1)
    rw [σ.foldE₂_of_inf hθ h2.le h1 (le_trans hs.le (le_abs_self _)),
      σ.foldE₂_of_inf hθ h2'.le (by rw [e1]; exact h1) (le_trans hs'.le (le_abs_self _))]
    exact σ.cornerInfC_refl_one _ _ (σ.blendWeight_eq_one hb.le) (σ.blendWeight_eq_one hb'.le)

include hθ h₁ h₂ in
theorem foldE₂_refl_zero {p q : ℕ} {z : ℂ} (hz : z ∈ σ.wallSetZeroC hθ)
    (hz' : σ.refl 0 z ∈ σ.wallSetZeroC hθ) :
    σ.foldE₂ hθ p q (σ.refl 0 z) = conj (σ.foldE₂ hθ p q z) := by
  have hAB := (σ.swap hθ).foldA₁_lt_foldB₁ h₂ h₁
  have hBH := (σ.swap hθ).foldB₁_lt_foldH h₂ h₁
  rw [σ.swap_foldH hθ] at hBH
  have e2 := σ.etaTwoC_refl_zero z
  obtain ⟨hz0, h1, hz1⟩ := hz
  obtain ⟨hz0', h1', hz1'⟩ := hz'
  rw [σ.swap_etaTwoC hθ, σ.swap_foldH hθ] at h1 h1'
  rw [σ.swap_etaOne hθ, σ.swap_foldH hθ, σ.swap_sinhN hθ, σ.swap_blendFn hθ] at hz1 hz1'
  by_cases h2 : σ.etaTwoC z < σ.foldH
  · have h2' : σ.etaTwoC (σ.refl 0 z) < σ.foldH := by rw [e2]; exact h2
    rw [σ.foldE₂_of_two hθ h2, σ.foldE₂_of_two hθ h2']
    refine σ.regionTwoC_refl_zero hθ h₁ h₂ z ?_
    rcases hz1 with h | ⟨-, hφ, -⟩
    · exact Or.inl h
    · rw [σ.swap_discAngle hθ, abs_neg] at hφ
      exact Or.inr hφ
  · push Not at h2
    have ha : ¬ σ.etaTwoC z < (σ.swap hθ).foldA₁ := not_lt.2 (by linarith)
    obtain ⟨-, -, hrest⟩ := hz1.resolve_left ha
    obtain ⟨-, -, hrest'⟩ := hz1'.resolve_left (by rw [e2]; exact ha)
    obtain ⟨hs, hb⟩ := hrest.resolve_left (not_lt.2 h2)
    obtain ⟨hs', hb'⟩ := hrest'.resolve_left (by rw [e2]; exact not_lt.2 h2)
    rw [σ.foldE₂_of_inf hθ h2 h1.le (le_trans hs.le (le_abs_self _)),
      σ.foldE₂_of_inf hθ (by rw [e2]; exact h2) h1'.le (le_trans hs'.le (le_abs_self _))]
    exact σ.cornerInfC_refl_zero _ _ (σ.blendWeight_eq_zero (by linarith))
      (σ.blendWeight_eq_zero (by linarith))

include hθ h₁ h₂ in
theorem foldE₂_refl_two {p q : ℕ} (hpθ : σ.θ₁ * p = Real.pi) (hqθ : σ.θ₂ * q = Real.pi) {z : ℂ}
    (hz : z ∈ σ.wallSetTwoC hθ) : σ.foldE₂ hθ p q (σ.refl 2 z) = conj (σ.foldE₂ hθ p q z) := by
  obtain ⟨⟨hs0, hz0, h1d⟩, ⟨-, h2d⟩⟩ := hz
  have hs : |σ.sinhN z| < 1 / 80 := hs0
  have e1 := σ.etaOne_refl_two hz0
  have e2 := σ.etaTwoC_refl_two hz0
  have es := σ.sinhN_refl_two hz0
  by_cases h2 : σ.etaTwoC z < σ.foldH
  · have h2' : σ.etaTwoC (σ.refl 2 z) < σ.foldH := by rw [e2]; exact h2
    rw [σ.foldE₂_of_two hθ h2, σ.foldE₂_of_two hθ h2']
    refine σ.regionTwoC_refl_two hθ h₁ h₂ hqθ hz0 ?_
    rw [σ.swap_etaOne hθ] at h2d
    rcases h2d with h | ⟨hd, hc⟩
    · exact Or.inl h
    · by_cases ha : σ.etaTwoC z < (σ.swap hθ).foldA₁
      · exact Or.inl ha
      push Not at ha
      have hs' : |(σ.swap hθ).sinhN (σ.swapPt z)| < 1 / 80 := by rw [σ.swap_sinhN hθ]; exact hs
      obtain ⟨hb1, hb2⟩ := (σ.swap hθ).foldPhiB_lt_of_band h₂ h₁ hd
        (by rw [σ.swap_etaOne hθ]; exact ha) hc hs'
      exact Or.inr ⟨hd, hb1.le, hb2.le⟩
  push Not at h2
  have h2' : σ.foldH ≤ σ.etaTwoC (σ.refl 2 z) := by rw [e2]; exact h2
  by_cases h1 : σ.etaOne z < σ.foldH
  · have h1' : σ.etaOne (σ.refl 2 z) < σ.foldH := by rw [e1]; exact h1
    rw [σ.foldE₂_of_one hθ h2 h1, σ.foldE₂_of_one hθ h2' h1']
    refine σ.coneRegion_refl_two h₁ h₂ hpθ hz0 ?_
    rcases h1d with h | ⟨hd, hc⟩
    · exact Or.inl h
    · by_cases ha : σ.etaOne z < σ.foldA₁
      · exact Or.inl ha
      push Not at ha
      obtain ⟨hb1, hb2⟩ := σ.foldPhiB_lt_of_band h₁ h₂ hd ha hc hs
      exact Or.inr ⟨hd, hb1.le, hb2.le⟩
  · push Not at h1
    have hL : |σ.sinhN z| < 1 / 10 := by linarith
    have hL' : |σ.sinhN (σ.refl 2 z)| < 1 / 10 := by rw [es, abs_neg]; exact hL
    rw [σ.foldE₂_of_lens hθ h2 h1 hL, σ.foldE₂_of_lens hθ h2' (by rw [e1]; exact h1) hL']
    exact σ.bridgeTwoC_refl_two hz0

end Identities

/-! ### The walls lie in the wall sets -/

section WallSets

variable (hθ : 0 < σ.θ₂) (h₁ : Real.cos σ.θ₁ = 0 ∨ 1 / 2 ≤ Real.cos σ.θ₁)
  (h₂ : Real.cos σ.θ₂ = 0 ∨ 1 / 2 ≤ Real.cos σ.θ₂)

include h₁ h₂ in
theorem sinhN_wallOne_gtC {z : ℂ} (hx : z.re = σ.width) (hz : 0 < z.im) (h1 : σ.foldH ≤ z.im) :
    7 / 50 < σ.sinhN z := by
  have hH := σ.foldH_pos
  rw [σ.sinhN_of_wallOne hx]
  have hw' := σ.window_lt_foldSD_mul h₁ h₂
  have hvy : σ.vertexOne.im = Real.sin σ.θ₁ / 4 := σ.vertexOne_im
  have hSD : σ.foldSD * Real.sin σ.θ₁ = 2 * (σ.foldH ^ 2 - σ.vertexOne.im ^ 2) / σ.foldH := by
    have hs0 := σ.sin_θ₁_pos.ne'
    unfold foldSD sinhRad
    rw [hvy]
    field_simp
    ring
  have hmono : 2 * (σ.foldH ^ 2 - σ.vertexOne.im ^ 2) / σ.foldH ≤
      2 * (z.im ^ 2 - σ.vertexOne.im ^ 2) / z.im := by
    rw [div_le_div_iff₀ hH hz]
    nlinarith [mul_nonneg (sub_nonneg.2 h1) (mul_nonneg hz.le hH.le),
      mul_nonneg (sub_nonneg.2 h1) (sq_nonneg σ.vertexOne.im)]
  linarith

include hθ in
theorem foldH_lt_etaTwoC_of_wallOne {z : ℂ} (hz : z ∈ σ.triangle) (hx : z.re = σ.width) :
    σ.foldH < σ.etaTwoC z := by
  have hy := σ.vertexOne_im_le_of_wallOne hz hx
  have he := σ.etaOne_of_wallOne hx hy
  rcases le_or_gt (σ.etaOne z) σ.foldH with h | h
  · exact σ.foldH_lt_etaTwoC_of_etaOne_le hθ hz.1 h
  · have hd0 : z ∈ σ.domZeroC := σ.mem_domZeroC_of_re_ne hθ hz.1 (by
      rw [hx]; exact σ.width_pos.ne')
    have := σ.im_le_etaTwoC hθ hd0
    linarith

include hθ h₁ h₂ in
theorem mem_wallSetOneC_of_wall {z : ℂ} (hz : z ∈ σ.triangle) (hx : z.re = σ.width) :
    z ∈ σ.wallSetOneC := by
  have hAB := σ.foldA₁_lt_foldB₁ h₁ h₂
  have hBH := σ.foldB₁_lt_foldH h₁ h₂
  have hy := σ.vertexOne_im_le_of_wallOne hz hx
  have he := σ.etaOne_of_wallOne hx hy
  refine ⟨hz.1, σ.foldH_lt_etaTwoC_of_wallOne hθ hz hx, ?_⟩
  by_cases ha : σ.etaOne z < σ.foldA₁
  · exact Or.inl ha
  push Not at ha
  have hzv := σ.ne_vertexOne_of_foldA₁_le h₁ h₂ ha
  have hd := σ.mem_domOne_of_mem_triangle hz hzv
  refine Or.inr ⟨hd, ?_, ?_⟩
  · rw [σ.discOne_of_wallOne hx hz.1]
    simp only [discAngle, ofReal_im, halfArg_zero, abs_zero]
    exact σ.foldPhiA_pos h₁ h₂
  · by_cases h1 : σ.etaOne z < σ.foldH
    · exact Or.inl h1
    push Not at h1
    refine Or.inr ⟨?_, ?_⟩
    · have := σ.sinhN_wallOne_gtC h₁ h₂ hx hz.1 (by rw [← he]; exact h1)
      linarith
    · have hd0 : z ∈ σ.domZeroC := σ.mem_domZeroC_of_re_ne hθ hz.1 (by
        rw [hx]; exact σ.width_pos.ne')
      have := σ.one_le_blendFn_of_wallOne hz.1 hx.ge (by
        rw [σ.etaTwo_eq_of_cone hθ]
        change σ.etaOne z ≤ σ.etaTwoC z
        rw [he]; exact σ.im_le_etaTwoC hθ hd0)
      linarith

include h₁ h₂ in
theorem mem_conePartTwo_of_wall {z : ℂ} (hz : z ∈ σ.triangle) (hw : σ.wallSide 2 z = 0) :
    z ∈ σ.conePartTwo := by
  refine ⟨hz.1, ?_⟩
  by_cases ha : σ.etaOne z < σ.foldA₁
  · exact Or.inl ha
  push Not at ha
  have hzv := σ.ne_vertexOne_of_foldA₁_le h₁ h₂ ha
  have hd := σ.mem_domOne_of_mem_triangle hz hzv
  refine Or.inr ⟨hd, ?_⟩
  have hr : 0 < ‖σ.discOne z‖ := norm_pos_iff.2 (σ.discOne_ne_zero hd)
  rw [σ.rotRe_eq_polar hd, σ.discAngle_of_wallTwo hz hw hzv, sub_self, Real.cos_zero, mul_one]
  exact hr

include hθ h₁ h₂ in
theorem foldWall_subset_wallSetC (i : Fin 3) : σ.foldWall i ⊆ σ.wallSetC hθ i := by
  intro z ⟨hz, hw⟩
  fin_cases i
  · change z.re = 0 at hw
    change σ.swapPt z ∈ (σ.swap hθ).wallSetOneC
    refine (σ.swap hθ).mem_wallSetOneC_of_wall σ.θ₁_pos h₂ h₁ ((σ.swapPt_mem_triangle hθ).2 hz) ?_
    rw [swapPt_re, hw, sub_zero, σ.swap_width hθ]
  · change σ.width - z.re = 0 at hw
    exact σ.mem_wallSetOneC_of_wall hθ h₁ h₂ hz (by linarith)
  · change σ.wallSide 2 z = 0 at hw
    have hs0 : σ.sinhN z = 0 := by rw [sinhN, hw]; simp
    refine ⟨⟨by change |σ.sinhN z| < 1 / 80; rw [hs0]; norm_num,
      σ.mem_conePartTwo_of_wall h₁ h₂ hz hw⟩, ?_⟩
    exact (σ.swap hθ).mem_conePartTwo_of_wall h₂ h₁ ((σ.swapPt_mem_triangle hθ).2 hz)
      (by rw [σ.swap_wallSide_two hθ]; exact hw)

end WallSets

/-! ### Values of `foldE₂` on the walls -/

section Values

variable (hθ : 0 < σ.θ₂) (h₁ : Real.cos σ.θ₁ = 0 ∨ 1 / 2 ≤ Real.cos σ.θ₁)
  (h₂ : Real.cos σ.θ₂ = 0 ∨ 1 / 2 ≤ Real.cos σ.θ₂)

include hθ in
theorem bridgeZeroC_im_of_wallZero {z : ℂ} (hz : 0 < z.im) (hx : z.re = 0) :
    (σ.bridgeZeroC z).im = 0 := by
  have hv2 := σ.vertexTwo_im_pos hθ
  have h1 := σ.im_coneDisc_vertexTwo_mul z
  have hN := normSq_sub_conj_pos hv2 hz
  have hw : σ.wallZeroC z = 0 := by
    have : (coneDisc σ.vertexTwo z).im * normSq (z - conj σ.vertexTwo) = 0 := by
      rw [h1]; simp [wallSide, hx]
    have := (mul_eq_zero.1 this).resolve_right hN.ne'
    rw [wallZeroC, discTwo, this, neg_zero]
  rw [bridgeZeroC, outerBridge, hw]
  exact twoCircle_im_eq_zero _ _ _ _ _

include hθ h₁ h₂ in
theorem foldE₂_wall_one_re {p q : ℕ} (hp : 1 ≤ p) {z : ℂ} (hz : z ∈ σ.triangle)
    (hx : z.re = σ.width) : (σ.foldE₂ hθ p q z).re ≤ -(3 / 2) := by
  have hK := σ.constK_pos
  have h2 := σ.foldH_lt_etaTwoC_of_wallOne hθ hz hx
  have hy := σ.vertexOne_im_le_of_wallOne hz hx
  have he := σ.etaOne_of_wallOne hx hy
  by_cases h1 : σ.etaOne z < σ.foldH
  · rw [σ.foldE₂_of_one hθ h2.le h1]
    exact σ.coneRegion_wall_one h₁ h₂ hp hz hx h1
  push Not at h1
  have hwall : σ.wallOne z = 0 := by rw [wallOne, σ.discOne_of_wallOne hx hz.1, ofReal_im]
  have hL : 1 / 10 ≤ |σ.sinhN z| := by
    have := σ.sinhN_wallOne_gtC h₁ h₂ hx hz.1 (by rw [← he]; exact h1)
    exact le_trans (by linarith) (le_abs_self _)
  have hb : 1 / 2 ≤ σ.blendFn z := by
    have hd0 : z ∈ σ.domZeroC := σ.mem_domZeroC_of_re_ne hθ hz.1 (by
      rw [hx]; exact σ.width_pos.ne')
    have := σ.one_le_blendFn_of_wallOne hz.1 hx.ge (by
      rw [σ.etaTwo_eq_of_cone hθ]
      change σ.etaOne z ≤ σ.etaTwoC z
      rw [he]; exact σ.im_le_etaTwoC hθ hd0)
    linarith
  rw [σ.foldE₂_of_inf hθ h2.le h1 hL, cornerInfC, angleInfC, σ.blendWeight_eq_one hb,
    angleOneInf, σ.bridgeOne_im_of_wallOne hwall, negHalfArg_zero]
  simp only [sub_self, zero_mul, one_mul, zero_add, Complex.exp_pi_mul_I, mul_neg, mul_one,
    neg_re, ofReal_re]
  linarith [two_lt_outerProfile hK σ.sqrt_constK_le_half
    (lt_trans σ.foldY₁_pos σ.foldY₁_lt_foldY₂) σ.foldY₂_lt_sqrt hz.1 (Y₁ := σ.foldY₁)]

include hθ h₁ h₂ in
theorem foldE₂_wall_zero_re {p q : ℕ} (hq : 1 ≤ q) {z : ℂ} (hz : z ∈ σ.triangle)
    (hx : z.re = 0) : 3 / 2 ≤ (σ.foldE₂ hθ p q z).re := by
  have hK := σ.constK_pos
  have hzT := (σ.swapPt_mem_triangle hθ).2 hz
  have hx' : (σ.swapPt z).re = (σ.swap hθ).width := by
    rw [swapPt_re, hx, sub_zero, σ.swap_width hθ]
  have h1 : σ.foldH < σ.etaOne z := by
    have := (σ.swap hθ).foldH_lt_etaTwoC_of_wallOne σ.θ₁_pos hzT hx'
    rwa [σ.swap_etaTwoC hθ, σ.swap_foldH hθ] at this
  by_cases h2 : σ.etaTwoC z < σ.foldH
  · rw [σ.foldE₂_of_two hθ h2]
    exact σ.regionTwoC_wall_zero hθ h₁ h₂ hq hz hx h2
  push Not at h2
  have hy := (σ.swap hθ).vertexOne_im_le_of_wallOne hzT hx'
  have he := (σ.swap hθ).etaOne_of_wallOne hx' hy
  rw [σ.swap_etaOne hθ, swapPt_im] at he
  have hL : 1 / 10 ≤ |σ.sinhN z| := by
    have := (σ.swap hθ).sinhN_wallOne_gtC h₂ h₁ hx' hzT.1 (by
      rw [σ.swap_foldH hθ, swapPt_im, ← he]; exact h2)
    rw [σ.swap_sinhN hθ] at this
    exact le_trans (by linarith) (le_abs_self _)
  have hb : σ.blendFn z ≤ -1 / 2 := by
    have hd1 : z ∈ σ.domOne := σ.mem_domOne_of_re_ne hz.1 (by rw [hx]; exact σ.width_pos.ne)
    have := σ.blendFn_le_of_wallZero hz.1 hx.le (by
      rw [σ.etaTwo_eq_of_cone hθ, he]; exact σ.im_le_etaOne hd1)
    linarith
  rw [σ.foldE₂_of_inf hθ h2 h1.le hL, cornerInfC, angleInfC, σ.blendWeight_eq_zero hb,
    angleZeroInfC, σ.bridgeZeroC_im_of_wallZero hθ hz.1 hx, halfArg_zero]
  simp only [sub_zero, one_mul, zero_mul, add_zero, ofReal_zero, Complex.exp_zero, mul_one,
    ofReal_re]
  linarith [two_lt_outerProfile hK σ.sqrt_constK_le_half
    (lt_trans σ.foldY₁_pos σ.foldY₁_lt_foldY₂) σ.foldY₂_lt_sqrt hz.1 (Y₁ := σ.foldY₁)]

include hθ in
theorem re_bound_of_bridgeTwoC_real {z : ℂ} (hz : z ∈ σ.domTwoC)
    (him : (σ.bridgeTwoC z).im = 0) : -1 < (σ.bridgeTwoC z).re ∧ (σ.bridgeTwoC z).re < 1 := by
  have hK := σ.constK_pos
  have e1 := σ.norm_bridgeTwoC_sub hθ hz
  have e2 := σ.norm_bridgeTwoC_add hθ hz
  have g1 := coneProfile_lt hK (σ.etaTwoC z)
  have g2 := coneProfile_lt hK (σ.etaOne z)
  have hr1 : ‖σ.bridgeTwoC z - 3 / 2‖ = |(σ.bridgeTwoC z).re - 3 / 2| := by
    rw [Complex.norm_def, normSq_apply]
    simp [him, Real.sqrt_mul_self_eq_abs]
  have hr2 : ‖σ.bridgeTwoC z + 3 / 2‖ = |(σ.bridgeTwoC z).re + 3 / 2| := by
    rw [Complex.norm_def, normSq_apply]
    simp [him, Real.sqrt_mul_self_eq_abs]
  rw [hr1] at e1
  rw [hr2] at e2
  constructor
  · have := neg_abs_le ((σ.bridgeTwoC z).re - 3 / 2); linarith
  · have := le_abs_self ((σ.bridgeTwoC z).re + 3 / 2); linarith

include hθ h₁ h₂ in
theorem foldE₂_wall_two_re {p q : ℕ} (hp : 1 ≤ p) (hq : 1 ≤ q) (hpθ : σ.θ₁ * p = Real.pi)
    (hqθ : σ.θ₂ * q = Real.pi) {z : ℂ} (hz : z ∈ σ.triangle) (hw : σ.wallSide 2 z = 0) :
    -(3 / 2) ≤ (σ.foldE₂ hθ p q z).re ∧ (σ.foldE₂ hθ p q z).re ≤ 3 / 2 := by
  have hAH : σ.foldA₁ < σ.foldH :=
    lt_trans (σ.foldA₁_lt_foldB₁ h₁ h₂) (σ.foldB₁_lt_foldH h₁ h₂)
  have hs0 : σ.sinhN z = 0 := by rw [sinhN, hw]; simp
  by_cases h2 : σ.etaTwoC z < σ.foldH
  · rw [σ.foldE₂_of_two hθ h2]
    exact σ.regionTwoC_wall_two hθ h₁ h₂ hq hqθ hz hw h2
  push Not at h2
  by_cases h1 : σ.etaOne z < σ.foldH
  · rw [σ.foldE₂_of_one hθ h2 h1]
    exact σ.coneRegion_wall_two h₁ h₂ hp hpθ hz hw h1
  push Not at h1
  have hzv := σ.ne_vertexOne_of_foldA₁_le h₁ h₂ (le_trans hAH.le h1)
  have hzv2 := σ.ne_vertexTwo_of_foldH_le hθ h₁ h₂ h2
  have hd := σ.mem_domTwoC_of_mem_triangle hθ hz hzv hzv2
  rw [σ.foldE₂_of_lens hθ h2 h1 (by rw [hs0, abs_zero]; norm_num)]
  have := σ.re_bound_of_bridgeTwoC_real hθ hd
    (σ.bridgeTwoC_im_of_wallTwo (σ.wallTwo_eq_zero_of hz.1 hw))
  constructor <;> linarith

end Values

end ConeShape

end GC.Seifert
