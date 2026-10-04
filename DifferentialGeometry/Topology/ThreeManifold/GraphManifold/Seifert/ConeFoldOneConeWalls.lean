import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Seifert.ConeFoldOneConeCore

/-!
# Wall identities and wall values of the assembled one-cone fold

Lane A4b2 (design `docs/geometrization/handoffs/20261004-design-a4-cone-fold.md`, §5–§6, J5 and
erratum 2). For each wall `i` an open set `wallSet i` containing the wall of the triangle on which
`foldE p` is equivariant for the wall reflection, in the form
`foldE (refl i z) = conj (foldE z)` whenever `z` and `refl i z` lie in `wallSet i`
(`foldE_refl_zero`, `foldE_refl_one`, `foldE_refl_two`):
* wall 0: the horocyclic band `|horoX| < -foldB₀` with the blend weight `0` and `η₁ > h`
  (`cornerZero` and `cornerInfW` with odd angles);
* wall 1: the apex zone, or `|φ| < foldPhiA` outside `R₂` with either `η₁ < h` (cone corner) or
  `sinh n > 1/10` and weight `1` (corner at `∞`);
* wall 2: the band `|sinh n| < 1/80` with `|horoX + 1/2| < foldA₀ + 1/2` inside `R₂` and
  `cos(θ₁ - φ) > 0` outside the apex zone (erratum 2: the cone corner is the pure wall-2 bridge
  there).
The values of `foldE` on the walls (`foldE_wall_zero_re`, `foldE_wall_one_re`,
`foldE_wall_two_re`) are the one-sided wall images required by `bijOn_of_local'` before the
mirror.
-/

set_option autoImplicit false

noncomputable section

open Complex Filter Set Metric
open scoped ComplexConjugate ContDiff Topology

namespace GC.Seifert

namespace ConeShape

variable (σ : ConeShape)

/-! ### Behaviour of the coordinates under the reflections -/

theorem cuspZeroHeight_refl_zero (z : ℂ) : cuspZeroHeight (σ.refl 0 z) = cuspZeroHeight z := by
  simp [cuspZeroHeight, refl, normSq_apply]

theorem horoX_refl_zero (z : ℂ) : horoX (σ.refl 0 z) = -horoX z := by
  rw [horoX_eq, horoX_eq]
  simp [refl, normSq_apply]
  ring

theorem sinhN_refl_two {z : ℂ} (hz : 0 < z.im) : σ.sinhN (σ.refl 2 z) = -σ.sinhN z := by
  have hn : 0 < normSq (z - σ.centre) := normSq_pos.2 (σ.centre_ne hz)
  rw [sinhN, sinhN, σ.wallSide_refl_two hz, σ.refl_two_im hz]
  field_simp

theorem horoX_refl_two (hθ : σ.θ₂ = 0) {z : ℂ} (hz : 0 < z.im) :
    horoX (σ.refl 2 z) + 1 / 2 = -(horoX z + 1 / 2) := by
  have h1 := σ.sinhN_eq_horoX hθ hz
  have h2 := σ.sinhN_eq_horoX hθ (σ.refl_im_pos hz 2)
  rw [σ.sinhN_refl_two hz, σ.cuspZeroHeight_refl_two hθ hz, h1] at h2
  have hc := cuspZeroHeight_pos hz
  have : 4 * cuspZeroHeight z * (horoX (σ.refl 2 z) + 1 / 2 + (horoX z + 1 / 2)) = 0 := by
    linear_combination -h2
  rcases mul_eq_zero.1 this with h | h
  · linarith
  · linarith

theorem continuousAt_refl (i : Fin 3) {z : ℂ} (hz : 0 < z.im) : ContinuousAt (σ.refl i) z := by
  fin_cases i
  · exact (continuous_conj.neg).continuousAt
  · exact (continuous_const.sub continuous_conj).continuousAt
  · change ContinuousAt (fun z : ℂ => (σ.centre : ℂ) + 1 / 16 / (conj z - σ.centre)) z
    exact continuousAt_const.add (continuousAt_const.div
      (continuous_conj.continuousAt.sub continuousAt_const) (σ.conj_centre_ne hz))

/-! ### The wall sets -/

def wallSetZero : Set ℂ :=
  {z | 0 < z.im ∧ |horoX z| < -σ.foldB₀ ∧ σ.blendFn z < -1 / 2 ∧ σ.foldH < σ.etaOne z}

def wallSetOne : Set ℂ :=
  {z | 0 < z.im ∧ (σ.etaOne z < σ.foldA₁ ∨ (z ∈ σ.domOne ∧
    |discAngle (σ.discOne z)| < σ.foldPhiA ∧ σ.foldH < cuspZeroHeight z ∧
      (σ.etaOne z < σ.foldH ∨ (1 / 10 < σ.sinhN z ∧ 1 / 2 < σ.blendFn z))))}

def wallSetTwo : Set ℂ :=
  {z | 0 < z.im ∧ |σ.sinhN z| < 1 / 80 ∧
    (σ.foldH < cuspZeroHeight z ∨ |horoX z + 1 / 2| < σ.foldA₀ + 1 / 2) ∧
    (σ.etaOne z < σ.foldA₁ ∨ (z ∈ σ.domOne ∧ 0 < (exp (-(σ.θ₁ * I)) * σ.discOne z).re))}

def wallSet : Fin 3 → Set ℂ
  | 0 => σ.wallSetZero
  | 1 => σ.wallSetOne
  | 2 => σ.wallSetTwo

theorem continuousAt_rotRe {z : ℂ} (hz : 0 < z.im) :
    ContinuousAt (fun u => (exp (-(σ.θ₁ * I)) * σ.discOne u).re) z :=
  (continuous_re.continuousAt).comp (continuousAt_const.mul (σ.contDiffAt_discOne hz).continuousAt)

theorem isOpen_wallSet (hθ : σ.θ₂ = 0) (i : Fin 3) : IsOpen (σ.wallSet i) := by
  rw [isOpen_iff_mem_nhds]
  intro z hz
  fin_cases i
  · change z ∈ σ.wallSetZero at hz
    change σ.wallSetZero ∈ 𝓝 z
    have hup := isOpen_upper.mem_nhds hz.1
    obtain ⟨hz0, hX, hb, h1⟩ := hz
    filter_upwards [hup,
      (continuous_abs.continuousAt.comp (contDiffAt_horoX hz0).continuousAt).eventually_lt
        continuousAt_const hX,
      (σ.continuousAt_blendFn hθ hz0).eventually_lt continuousAt_const hb,
      continuousAt_const.eventually_lt (σ.continuousAt_etaOne hz0) h1] with w hw hwX hwb hw1
    exact ⟨hw, hwX, hwb, hw1⟩
  · change z ∈ σ.wallSetOne at hz
    change σ.wallSetOne ∈ 𝓝 z
    have hup := isOpen_upper.mem_nhds hz.1
    obtain ⟨hz0, h | ⟨hd, hφ, h0, h'⟩⟩ := hz
    · filter_upwards [hup, (σ.continuousAt_etaOne hz0).eventually_lt continuousAt_const h]
        with w hw hw1
      exact ⟨hw, Or.inl hw1⟩
    · have hφe : ∀ᶠ w in 𝓝 z, |discAngle (σ.discOne w)| < σ.foldPhiA :=
        (continuous_abs.continuousAt.comp (σ.continuousAt_discAngle hd)).eventually_lt
          continuousAt_const hφ
      have hde := σ.isOpen_domOne.mem_nhds hd
      have h0e := continuousAt_const.eventually_lt (continuousAt_cuspZeroHeight hz0) h0
      rcases h' with h1 | ⟨hs, hb⟩
      · filter_upwards [hup, hφe, hde, h0e,
          (σ.continuousAt_etaOne hz0).eventually_lt continuousAt_const h1] with w hw hwφ hwd hw0 hw1
        exact ⟨hw, Or.inr ⟨hwd, hwφ, hw0, Or.inl hw1⟩⟩
      · filter_upwards [hup, hφe, hde, h0e,
          continuousAt_const.eventually_lt (σ.continuousAt_sinhN hz0) hs,
          continuousAt_const.eventually_lt (σ.continuousAt_blendFn hθ hz0) hb]
          with w hw hwφ hwd hw0 hws hwb
        exact ⟨hw, Or.inr ⟨hwd, hwφ, hw0, Or.inr ⟨hws, hwb⟩⟩⟩
  · change z ∈ σ.wallSetTwo at hz
    change σ.wallSetTwo ∈ 𝓝 z
    have hup := isOpen_upper.mem_nhds hz.1
    obtain ⟨hz0, hs, h0, h1⟩ := hz
    have hse := (continuous_abs.continuousAt.comp (σ.continuousAt_sinhN hz0)).eventually_lt
      continuousAt_const hs
    have h0e : ∀ᶠ w in 𝓝 z, σ.foldH < cuspZeroHeight w ∨ |horoX w + 1 / 2| < σ.foldA₀ + 1 / 2 := by
      rcases h0 with h | h
      · filter_upwards [continuousAt_const.eventually_lt (continuousAt_cuspZeroHeight hz0) h]
          with w hw
        exact Or.inl hw
      · filter_upwards [(continuous_abs.continuousAt.comp
          ((contDiffAt_horoX hz0).continuousAt.add continuousAt_const)).eventually_lt
            continuousAt_const h] with w hw
        exact Or.inr hw
    have h1e : ∀ᶠ w in 𝓝 z, σ.etaOne w < σ.foldA₁ ∨
        (w ∈ σ.domOne ∧ 0 < (exp (-(σ.θ₁ * I)) * σ.discOne w).re) := by
      rcases h1 with h | ⟨hd, hc⟩
      · filter_upwards [(σ.continuousAt_etaOne hz0).eventually_lt continuousAt_const h] with w hw
        exact Or.inl hw
      · filter_upwards [σ.isOpen_domOne.mem_nhds hd,
          continuousAt_const.eventually_lt (σ.continuousAt_rotRe hz0) hc] with w hwd hwc
        exact Or.inr ⟨hwd, hwc⟩
    filter_upwards [hup, hse, h0e, h1e] with w hw hws hw0 hw1
    exact ⟨hw, hws, hw0, hw1⟩

/-! ### Wall identities of `foldE` -/

section Identities

variable (hθ : σ.θ₂ = 0) (h₁ : Real.cos σ.θ₁ = 0 ∨ 1 / 2 ≤ Real.cos σ.θ₁)

include hθ h₁ in
theorem foldE_refl_zero {p : ℕ} {z : ℂ} (hz : z ∈ σ.wallSetZero)
    (hz' : σ.refl 0 z ∈ σ.wallSetZero) : σ.foldE p (σ.refl 0 z) = conj (σ.foldE p z) := by
  have h₂ := σ.adm_two_of_cusp hθ
  have hAH : σ.foldA₁ < σ.foldH :=
    lt_trans (σ.foldA₁_lt_foldB₁ h₁ h₂) (σ.foldB₁_lt_foldH h₁ h₂)
  obtain ⟨hz0, hX, hb, h1⟩ := hz
  obtain ⟨hz0', hX', hb', h1'⟩ := hz'
  have e0 := σ.cuspZeroHeight_refl_zero z
  by_cases h0 : cuspZeroHeight z < σ.foldH
  · rw [σ.foldE_of_zero h0, σ.foldE_of_zero (by rw [e0]; exact h0)]
    exact σ.cornerZero_refl_zero σ.foldA₀_lt_foldB₀ (by linarith [neg_abs_le (horoX z)])
      (by linarith [neg_abs_le (horoX (σ.refl 0 z))])
  · push Not at h0
    have hH := σ.foldH_pos
    have hL : ∀ w : ℂ, 0 < w.im → σ.foldH ≤ cuspZeroHeight w → |horoX w| < -σ.foldB₀ →
        1 / 10 ≤ |σ.sinhN w| := by
      intro w hw hw0 hwX
      have hs := σ.sinhN_eq_horoX hθ hw
      have hb0 : -σ.foldB₀ = 1 / 2 - 7 / 50 / (4 * σ.foldH) := by unfold foldB₀; ring
      have hpos : 7 / 50 / (4 * σ.foldH) < horoX w + 1 / 2 := by
        rw [hb0] at hwX; linarith [neg_abs_le (horoX w)]
      have : 7 / 50 ≤ σ.sinhN w := by
        rw [hs]
        have h7 : 7 / 50 = 4 * σ.foldH * (7 / 50 / (4 * σ.foldH)) := by field_simp
        rw [h7]
        apply mul_le_mul (by linarith) hpos.le (by positivity) (by linarith)
      exact le_trans (by linarith) (le_abs_self _)
    rw [σ.foldE_of_inf hθ h₁ h0 h1.le (hL z hz0 h0 hX),
      σ.foldE_of_inf hθ h₁ (by rw [e0]; exact h0) h1'.le (hL _ hz0' (by rw [e0]; exact h0) hX')]
    exact σ.cornerInfW_refl_zero _ _ (σ.blendWeight_eq_zero hb.le) (σ.blendWeight_eq_zero hb'.le)

include hθ h₁ in
theorem foldE_refl_one {p : ℕ} {z : ℂ} (hz : z ∈ σ.wallSetOne)
    (hz' : σ.refl 1 z ∈ σ.wallSetOne) : σ.foldE p (σ.refl 1 z) = conj (σ.foldE p z) := by
  have h₂ := σ.adm_two_of_cusp hθ
  have hAB := σ.foldA₁_lt_foldB₁ h₁ h₂
  have hBH := σ.foldB₁_lt_foldH h₁ h₂
  have hφ := σ.foldPhiA_lt_foldPhiB h₁ h₂
  have e1 := σ.etaOne_refl_one z
  obtain ⟨hz0, hz1⟩ := hz
  obtain ⟨hz0', hz1'⟩ := hz'
  by_cases ha : σ.etaOne z < σ.foldA₁
  · have h0 := σ.foldH_lt_cuspZeroHeight_of_etaOne_le hθ hz0 (by linarith)
    have h0' := σ.foldH_lt_cuspZeroHeight_of_etaOne_le hθ hz0' (by rw [e1]; linarith)
    have ha' : σ.etaOne (σ.refl 1 z) < σ.foldA₁ := by rw [e1]; exact ha
    simp only [foldE, not_lt.2 h0.le, not_lt.2 h0'.le, ha, ha', ↓reduceIte]
    exact σ.apexBefore_refl_one p z
  obtain ⟨hd, hφz, h0, hrest⟩ := hz1.resolve_left ha
  obtain ⟨hd', hφz', h0', hrest'⟩ := hz1'.resolve_left (by rw [e1]; exact ha)
  push Not at ha
  by_cases h1 : σ.etaOne z < σ.foldH
  · have h1' : σ.etaOne (σ.refl 1 z) < σ.foldH := by rw [e1]; exact h1
    have ha' : ¬ σ.etaOne (σ.refl 1 z) < σ.foldA₁ := by rw [e1]; exact not_lt.2 ha
    simp only [foldE, not_lt.2 h0.le, not_lt.2 h0'.le, not_lt.2 ha, ha', h1, h1', ↓reduceIte]
    exact σ.cornerCone_refl_one p hφ z hφz.le
  · push Not at h1
    obtain ⟨hs, hb⟩ := hrest.resolve_left (not_lt.2 h1)
    obtain ⟨hs', hb'⟩ := hrest'.resolve_left (by rw [e1]; exact not_lt.2 h1)
    rw [σ.foldE_of_inf hθ h₁ h0.le h1 (le_trans hs.le (le_abs_self _)),
      σ.foldE_of_inf hθ h₁ h0'.le (by rw [e1]; exact h1) (le_trans hs'.le (le_abs_self _))]
    exact σ.cornerInfW_refl_one _ _ (σ.blendWeight_eq_one hb.le) (σ.blendWeight_eq_one hb'.le)

include hθ h₁ in
theorem foldE_refl_two {p : ℕ} (hpθ : σ.θ₁ * p = Real.pi) {z : ℂ} (hz : z ∈ σ.wallSetTwo) :
    σ.foldE p (σ.refl 2 z) = conj (σ.foldE p z) := by
  have h₂ := σ.adm_two_of_cusp hθ
  have hAB := σ.foldA₁_lt_foldB₁ h₁ h₂
  have hBH := σ.foldB₁_lt_foldH h₁ h₂
  have hφ := σ.foldPhiA_lt_foldPhiB h₁ h₂
  obtain ⟨hz0, hs, h0d, h1d⟩ := hz
  have e0 := σ.cuspZeroHeight_refl_two hθ hz0
  have e1 := σ.etaOne_refl_two hz0
  have es := σ.sinhN_refl_two hz0
  have eX := σ.horoX_refl_two hθ hz0
  by_cases h0 : cuspZeroHeight z < σ.foldH
  · have hX := h0d.resolve_left (not_lt.2 h0.le)
    rw [σ.foldE_of_zero h0, σ.foldE_of_zero (by rw [e0]; exact h0)]
    refine σ.cornerZero_refl_two hθ σ.foldA₀_lt_foldB₀ hz0 ?_ ?_
    · linarith [le_abs_self (horoX z + 1 / 2)]
    · linarith [neg_abs_le (horoX z + 1 / 2)]
  push Not at h0
  have h0' : σ.foldH ≤ cuspZeroHeight (σ.refl 2 z) := by rw [e0]; exact h0
  by_cases ha : σ.etaOne z < σ.foldA₁
  · have hA : σ.foldA₁ < σ.foldH := lt_trans hAB hBH
    have ha' : σ.etaOne (σ.refl 2 z) < σ.foldA₁ := by rw [e1]; exact ha
    simp only [foldE, not_lt.2 h0, not_lt.2 h0', ha, ha', ↓reduceIte]
    exact σ.apexBefore_refl_two hpθ hz0
  push Not at ha
  have ha' : ¬ σ.etaOne (σ.refl 2 z) < σ.foldA₁ := by rw [e1]; exact not_lt.2 ha
  by_cases h1 : σ.etaOne z < σ.foldH
  · have h1' : σ.etaOne (σ.refl 2 z) < σ.foldH := by rw [e1]; exact h1
    obtain ⟨hd, hc⟩ := h1d.resolve_left (not_lt.2 ha)
    obtain ⟨hb1, hb2⟩ := σ.foldPhiB_lt_of_band h₁ h₂ hd ha hc (by linarith)
    simp only [foldE, not_lt.2 h0, not_lt.2 h0', not_lt.2 ha, ha', h1, h1', ↓reduceIte]
    exact σ.cornerCone_refl_two hθ hpθ hφ (σ.foldPhiB_pos h₁ h₂) hd hb1.le hb2.le
  · push Not at h1
    have hL : |σ.sinhN z| < 1 / 10 := by linarith
    have hL' : |σ.sinhN (σ.refl 2 z)| < 1 / 10 := by rw [es, abs_neg]; exact hL
    rw [σ.foldE_of_lens hθ h₁ h0 h1 hL, σ.foldE_of_lens hθ h₁ h0' (by rw [e1]; exact h1) hL']
    exact σ.bridgeTwo_refl_two hθ hz0

end Identities

/-! ### Coordinates on the walls -/

theorem discOne_of_wallOne {z : ℂ} (hx : z.re = σ.width) (hz : 0 < z.im) :
    σ.discOne z = (((z.im - σ.vertexOne.im) / (z.im + σ.vertexOne.im) : ℝ) : ℂ) := by
  have hv := σ.vertexOne_im_pos
  have hpos : (z.im : ℂ) + σ.vertexOne.im ≠ 0 := by
    rw [← Complex.ofReal_add]; exact Complex.ofReal_ne_zero.2 (by linarith)
  have e1 : z - σ.vertexOne = ((z.im - σ.vertexOne.im : ℝ) : ℂ) * I :=
    Complex.ext (by simp [hx, vertexOne_re]) (by simp)
  have e2 : z - conj σ.vertexOne = ((z.im + σ.vertexOne.im : ℝ) : ℂ) * I :=
    Complex.ext (by simp [hx, vertexOne_re]) (by simp)
  rw [discOne, coneDisc, e1, e2, mul_div_mul_right _ _ I_ne_zero]
  push_cast
  rfl

theorem etaOne_of_wallOne {z : ℂ} (hx : z.re = σ.width) (hy : σ.vertexOne.im ≤ z.im) :
    σ.etaOne z = z.im := by
  have hv := σ.vertexOne_im_pos
  have hz : 0 < z.im := lt_of_lt_of_le hv hy
  have hn : ‖σ.discOne z‖ = (z.im - σ.vertexOne.im) / (z.im + σ.vertexOne.im) := by
    rw [σ.discOne_of_wallOne hx hz, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (div_nonneg (by linarith) (by linarith))]
  unfold etaOne coneHeight
  rw [← discOne, hn]
  have h1 : z.im + σ.vertexOne.im ≠ 0 := by linarith
  have hr1 : 1 - (z.im - σ.vertexOne.im) / (z.im + σ.vertexOne.im) ≠ 0 := by
    rw [one_sub_div h1]
    exact div_ne_zero (by linarith) h1
  rw [div_eq_iff hr1]
  field_simp
  ring

theorem cuspZeroHeight_of_wallZero {z : ℂ} (hx : z.re = 0) (hz : 0 < z.im) :
    cuspZeroHeight z = z.im := by
  rw [cuspZeroHeight, normSq_apply, hx]
  field_simp
  ring

theorem two_width_le_cuspZeroHeight_of_wallOne {z : ℂ} (hx : z.re = σ.width) (hz : 0 < z.im) :
    2 * σ.width ≤ cuspZeroHeight z := by
  rw [cuspZeroHeight, normSq_apply, hx, le_div_iff₀ hz]
  nlinarith [sq_nonneg (σ.width - z.im)]

theorem sinhN_of_wallOne {z : ℂ} (hx : z.re = σ.width) :
    σ.sinhN z = 2 * (z.im ^ 2 - σ.vertexOne.im ^ 2) / z.im := by
  have hW : σ.width - σ.centre = Real.cos σ.θ₁ / 4 := by unfold width centre; ring
  unfold sinhN
  simp only [wallSide]
  rw [hx, vertexOne_im, hW]
  have hs := Real.sin_sq_add_cos_sq σ.θ₁
  congr 1
  linear_combination ((1 : ℝ) / 8) * hs

theorem wallTwo_eq_zero_of {z : ℂ} (hz : 0 < z.im) (hw : σ.wallSide 2 z = 0) :
    σ.wallTwo z = 0 := by
  have hN := normSq_sub_conj_pos σ.vertexOne_im_pos hz
  have h := σ.im_rot_coneDisc_vertexOne_mul z
  rw [hw, mul_zero, neg_zero] at h
  have := (mul_eq_zero.1 h).resolve_right hN.ne'
  rw [wallTwo, discOne, this, neg_zero]

theorem discAngle_of_wallTwo {z : ℂ} (hz : z ∈ σ.triangle) (hw : σ.wallSide 2 z = 0)
    (hzv : z ≠ σ.vertexOne) : discAngle (σ.discOne z) = σ.θ₁ := by
  have hd := σ.mem_domOne_of_mem_triangle hz hzv
  have hr : 0 < ‖σ.discOne z‖ := norm_pos_iff.2 (σ.discOne_ne_zero hd)
  have h0 := σ.wallTwo_eq_zero_of hz.1 hw
  rw [σ.wallTwo_eq_polar hd] at h0
  have hs := (mul_eq_zero.1 h0).resolve_left hr.ne'
  have hm := σ.discAngle_mem_of_mem_triangle hz hzv
  by_contra hne
  have hlt : 0 < σ.θ₁ - discAngle (σ.discOne z) := by
    rcases lt_or_gt_of_ne hne with h | h
    · linarith
    · linarith [hm.2]
  have := Real.sin_pos_of_pos_of_lt_pi hlt (by linarith [hm.1, σ.θ₁_le, Real.pi_pos])
  linarith

theorem re_bound_of_bridgeTwo_real (hθ : σ.θ₂ = 0) {z : ℂ} (hz : z ∈ σ.domTwo)
    (him : (σ.bridgeTwo z).im = 0) : -1 < (σ.bridgeTwo z).re ∧ (σ.bridgeTwo z).re < 1 := by
  have hK := σ.constK_pos
  have e1 := σ.norm_bridgeTwo_sub hθ hz
  have e2 := σ.norm_bridgeTwo_add hθ hz
  have g1 := coneProfile_lt hK (cuspZeroHeight z)
  have g2 := coneProfile_lt hK (σ.etaOne z)
  have hr1 : ‖σ.bridgeTwo z - 3 / 2‖ = |(σ.bridgeTwo z).re - 3 / 2| := by
    rw [Complex.norm_def, normSq_apply]
    simp [him, Real.sqrt_mul_self_eq_abs]
  have hr2 : ‖σ.bridgeTwo z + 3 / 2‖ = |(σ.bridgeTwo z).re + 3 / 2| := by
    rw [Complex.norm_def, normSq_apply]
    simp [him, Real.sqrt_mul_self_eq_abs]
  rw [hr1] at e1
  rw [hr2] at e2
  constructor
  · have := neg_abs_le ((σ.bridgeTwo z).re - 3 / 2); linarith
  · have := le_abs_self ((σ.bridgeTwo z).re + 3 / 2); linarith

/-! ### The walls lie in the wall sets -/

section WallSets

variable (hθ : σ.θ₂ = 0) (h₁ : Real.cos σ.θ₁ = 0 ∨ 1 / 2 ≤ Real.cos σ.θ₁)

include hθ h₁ in
theorem foldWall_subset_wallSet (i : Fin 3) : σ.foldWall i ⊆ σ.wallSet i := by
  have h₂ := σ.adm_two_of_cusp hθ
  have hH := σ.foldH_pos
  have hAB := σ.foldA₁_lt_foldB₁ h₁ h₂
  have hBH := σ.foldB₁_lt_foldH h₁ h₂
  intro z ⟨hz, hw⟩
  fin_cases i
  · change z.re = 0 at hw
    change z ∈ σ.wallSetZero
    have hd : z ∈ σ.domOne := σ.mem_domOne_of_re_ne hz.1 (by rw [hw]; exact σ.width_pos.ne)
    have h0 := cuspZeroHeight_of_wallZero hw hz.1
    have hle := σ.im_le_etaOne hd
    refine ⟨hz.1, ?_, ?_, ?_⟩
    · rw [horoX_eq, hw]
      simp only [neg_zero, zero_div, abs_zero]
      linarith [σ.foldB₀_neg]
    · have := σ.blendFn_le_of_wallZero hz.1 hw.le (by
        rw [σ.etaTwo_eq_of_cusp hθ, h0]; exact hle)
      linarith
    · rcases le_or_gt (cuspZeroHeight z) σ.foldH with h | h
      · exact σ.foldH_lt_etaOne_of_cuspZeroHeight_le hθ hz.1 h
      · rw [h0] at h; linarith
  · change σ.width - z.re = 0 at hw
    have hx : z.re = σ.width := by linarith
    change z ∈ σ.wallSetOne
    refine ⟨hz.1, ?_⟩
    by_cases ha : σ.etaOne z < σ.foldA₁
    · exact Or.inl ha
    push Not at ha
    have hzv := σ.ne_vertexOne_of_foldA₁_le h₁ h₂ ha
    have hd := σ.mem_domOne_of_mem_triangle hz hzv
    have hy : σ.vertexOne.im ≤ z.im := by
      have := coneHeight_ge σ.vertexOne_im_pos hz.1
      have h' := σ.im_le_etaOne hd
      have hw2 := hz.2 2
      simp only [wallSide] at hw2
      rw [hx] at hw2
      have hW : σ.width - σ.centre = Real.cos σ.θ₁ / 4 := by unfold width centre; ring
      rw [hW] at hw2
      have hs := Real.sin_sq_add_cos_sq σ.θ₁
      have hsq : σ.vertexOne.im ^ 2 ≤ z.im ^ 2 := by rw [vertexOne_im]; nlinarith
      exact (pow_le_pow_iff_left₀ σ.vertexOne_im_pos.le hz.1.le two_ne_zero).1 hsq
    have he := σ.etaOne_of_wallOne hx hy
    refine Or.inr ⟨hd, ?_, ?_, ?_⟩
    · rw [σ.discOne_of_wallOne hx hz.1]
      simp only [discAngle, ofReal_im, halfArg_zero, abs_zero]
      exact σ.foldPhiA_pos h₁ h₂
    · linarith [σ.two_width_le_cuspZeroHeight_of_wallOne hx hz.1, σ.two_width_gt_foldH hθ]
    · by_cases h1 : σ.etaOne z < σ.foldH
      · exact Or.inl h1
      push Not at h1
      refine Or.inr ⟨?_, ?_⟩
      · rw [he] at h1
        rw [σ.sinhN_of_wallOne hx]
        have hw' := σ.window_lt_foldSD_mul h₁ h₂
        have hv := σ.vertexOne_im_pos
        have hvy : σ.vertexOne.im = Real.sin σ.θ₁ / 4 := σ.vertexOne_im
        have hvH := σ.vertexOne_im_lt_foldH h₁ h₂
        have hSD : σ.foldSD * Real.sin σ.θ₁ = 2 * (σ.foldH ^ 2 - σ.vertexOne.im ^ 2) / σ.foldH := by
          have hs0 := σ.sin_θ₁_pos.ne'
          unfold foldSD sinhRad
          rw [hvy]
          field_simp
          ring
        have hmono : 2 * (σ.foldH ^ 2 - σ.vertexOne.im ^ 2) / σ.foldH ≤
            2 * (z.im ^ 2 - σ.vertexOne.im ^ 2) / z.im := by
          rw [div_le_div_iff₀ hH hz.1]
          nlinarith [mul_nonneg (sub_nonneg.2 h1) (mul_nonneg hz.1.le hH.le),
            mul_nonneg (sub_nonneg.2 h1) (sq_nonneg σ.vertexOne.im)]
        linarith
      · have := σ.one_le_blendFn_of_wallOne hz.1 hx.ge (by
          rw [σ.etaTwo_eq_of_cusp hθ]
          change σ.etaOne z ≤ cuspZeroHeight z
          rw [he]; exact im_le_cuspZeroHeight hz.1)
        linarith
  · change σ.wallSide 2 z = 0 at hw
    change z ∈ σ.wallSetTwo
    have hs0 : σ.sinhN z = 0 := by rw [sinhN, hw]; simp
    refine ⟨hz.1, by rw [hs0]; norm_num, Or.inr ?_, ?_⟩
    · have h1 := σ.sinhN_eq_horoX hθ hz.1
      rw [hs0] at h1
      have hc := cuspZeroHeight_pos hz.1
      have : horoX z + 1 / 2 = 0 := by
        rcases mul_eq_zero.1 h1.symm with h | h
        · linarith
        · exact h
      rw [this, abs_zero]
      linarith [σ.neg_half_lt_foldA₀]
    · by_cases ha : σ.etaOne z < σ.foldA₁
      · exact Or.inl ha
      push Not at ha
      have hzv := σ.ne_vertexOne_of_foldA₁_le h₁ h₂ ha
      have hd := σ.mem_domOne_of_mem_triangle hz hzv
      refine Or.inr ⟨hd, ?_⟩
      have hr : 0 < ‖σ.discOne z‖ := norm_pos_iff.2 (σ.discOne_ne_zero hd)
      rw [σ.rotRe_eq_polar hd, σ.discAngle_of_wallTwo hz hw hzv, sub_self, Real.cos_zero, mul_one]
      exact hr

end WallSets

/-! ### Values of `foldE` on the walls -/

theorem bridgeZero_im_of_wallZero {z : ℂ} (hx : z.re = 0) : (σ.bridgeZero z).im = 0 := by
  rw [bridgeZero, outerBridge, hx]
  exact twoCircle_im_eq_zero _ _ _ _ _

theorem bridgeOne_im_of_wallOne {z : ℂ} (hw : σ.wallOne z = 0) : (σ.bridgeOne z).im = 0 := by
  rw [bridgeOne, outerBridge, hw]
  exact twoCircle_im_eq_zero _ _ _ _ _

theorem bridgeTwo_im_of_wallTwo {z : ℂ} (hw : σ.wallTwo z = 0) : (σ.bridgeTwo z).im = 0 := by
  rw [bridgeTwo, innerBridge, hw]
  exact twoCircle_im_eq_zero _ _ _ _ _

theorem vertexOne_im_le_of_wallOne {z : ℂ} (hz : z ∈ σ.triangle) (hx : z.re = σ.width) :
    σ.vertexOne.im ≤ z.im := by
  have hw2 := hz.2 2
  simp only [wallSide] at hw2
  rw [hx] at hw2
  have hW : σ.width - σ.centre = Real.cos σ.θ₁ / 4 := by unfold width centre; ring
  rw [hW] at hw2
  have hs := Real.sin_sq_add_cos_sq σ.θ₁
  have hsq : σ.vertexOne.im ^ 2 ≤ z.im ^ 2 := by rw [vertexOne_im]; nlinarith
  exact (pow_le_pow_iff_left₀ σ.vertexOne_im_pos.le hz.1.le two_ne_zero).1 hsq

theorem sinhN_of_wallZero (hθ : σ.θ₂ = 0) {z : ℂ} (hx : z.re = 0) (hz : 0 < z.im) :
    σ.sinhN z = 2 * z.im := by
  unfold sinhN
  simp only [wallSide]
  rw [hx, σ.cusp_centre hθ]
  field_simp
  ring

section Values

variable (hθ : σ.θ₂ = 0) (h₁ : Real.cos σ.θ₁ = 0 ∨ 1 / 2 ≤ Real.cos σ.θ₁)

include hθ h₁ in
theorem sinhN_wallOne_gt {z : ℂ} (hx : z.re = σ.width) (hz : 0 < z.im) (h1 : σ.foldH ≤ z.im) :
    7 / 50 < σ.sinhN z := by
  have h₂ := σ.adm_two_of_cusp hθ
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

include hθ h₁ in
theorem foldE_wall_zero_re {p : ℕ} {z : ℂ} (hz : z ∈ σ.triangle) (hx : z.re = 0) :
    3 / 2 ≤ (σ.foldE p z).re := by
  have hK := σ.constK_pos
  have hH := σ.foldH_pos
  have h0 := cuspZeroHeight_of_wallZero hx hz.1
  have hbz := σ.bridgeZero_im_of_wallZero hx
  have hd : z ∈ σ.domOne := σ.mem_domOne_of_re_ne hz.1 (by rw [hx]; exact σ.width_pos.ne)
  rcases lt_or_ge (cuspZeroHeight z) σ.foldH with h | h
  · rw [σ.foldE_of_zero h, cornerZero, angleHole,
      coneStep_eq_one σ.foldA₀_lt_foldB₀ (by rw [horoX_eq, hx]; simp; linarith [σ.foldB₀_neg]),
      angleZeroHole, hbz, halfArg_zero]
    simp only [one_mul, sub_self, zero_mul, add_zero, ofReal_zero, Complex.exp_zero, mul_one]
    rw [add_re, ofReal_re]
    norm_num
    linarith [half_le_coneProfile hK (cuspZeroHeight z)]
  · have hle := σ.im_le_etaOne hd
    have h1 : σ.foldH ≤ σ.etaOne z := by rw [h0] at h; linarith
    have hL : 1 / 10 ≤ |σ.sinhN z| := by
      rw [σ.sinhN_of_wallZero hθ hx hz.1, abs_of_pos (by linarith [hz.1])]
      rw [h0] at h; linarith [σ.five_twentyoneths_le_foldH]
    have hb : σ.blendFn z ≤ -1 / 2 := by
      have := σ.blendFn_le_of_wallZero hz.1 hx.le (by rw [σ.etaTwo_eq_of_cusp hθ, h0]; exact hle)
      linarith
    rw [σ.foldE_of_inf hθ h₁ h h1 hL, cornerInfW, angleInfW, σ.blendWeight_eq_zero hb,
      angleZeroInf, hbz, halfArg_zero]
    simp only [sub_zero, one_mul, zero_mul, add_zero, ofReal_zero, Complex.exp_zero, mul_one,
      ofReal_re]
    linarith [two_lt_outerProfile hK σ.sqrt_constK_le_half
      (lt_trans σ.foldY₁_pos σ.foldY₁_lt_foldY₂) σ.foldY₂_lt_sqrt hz.1 (Y₁ := σ.foldY₁)]

include hθ h₁ in
theorem foldE_wall_one_re {p : ℕ} (hp : 1 ≤ p) {z : ℂ} (hz : z ∈ σ.triangle)
    (hx : z.re = σ.width) : (σ.foldE p z).re ≤ -(3 / 2) := by
  have h₂ := σ.adm_two_of_cusp hθ
  have hK := σ.constK_pos
  have hH := σ.foldH_pos
  have hAB := σ.foldA₁_lt_foldB₁ h₁ h₂
  have hBH := σ.foldB₁_lt_foldH h₁ h₂
  have hφ := σ.foldPhiA_lt_foldPhiB h₁ h₂
  have hy := σ.vertexOne_im_le_of_wallOne hz hx
  have he := σ.etaOne_of_wallOne hx hy
  have hv := σ.vertexOne_im_pos
  have h0 : σ.foldH < cuspZeroHeight z := by
    linarith [σ.two_width_le_cuspZeroHeight_of_wallOne hx hz.1, σ.two_width_gt_foldH hθ]
  have hdisc := σ.discOne_of_wallOne hx hz.1
  set r := (z.im - σ.vertexOne.im) / (z.im + σ.vertexOne.im) with hr
  have hr0 : 0 ≤ r := div_nonneg (by linarith) (by linarith)
  have hwall : σ.wallOne z = 0 := by rw [wallOne, hdisc, ofReal_im]
  have hangle : discAngle (σ.discOne z) = 0 := by
    rw [hdisc]; simp [discAngle, halfArg_zero]
  by_cases ha : σ.etaOne z < σ.foldA₁
  · simp only [foldE, not_lt.2 h0.le, ha, ↓reduceIte]
    rw [apexBefore, hdisc, conj_ofReal]
    have := pow_nonneg hr0 p
    have hre : ((r : ℂ) ^ p).re = r ^ p := by rw [← ofReal_pow, ofReal_re]
    norm_num
    linarith
  push Not at ha
  by_cases h1 : σ.etaOne z < σ.foldH
  · simp only [foldE, not_lt.2 h0.le, not_lt.2 ha, h1, ↓reduceIte]
    have hS : 0 ≤ coneRadial p σ.foldA₁ σ.foldB₁ σ.vertexOne.im σ.constK (σ.etaOne z) :=
      (σ.coneRadial_lt_foldH hp (coneHeight_ge hv hz.1) h1).1
    have hΘ : σ.angleCone p σ.foldA₁ σ.foldB₁ σ.foldPhiA σ.foldPhiB z = Real.pi := by
      rw [angleCone, angleConeBlend, coneLambda, hangle,
        coneStep_eq_zero hφ (σ.foldPhiA_pos h₁ h₂).le, angleOneCone,
        σ.bridgeOne_im_of_wallOne hwall, negHalfArg_zero]
      ring
    rw [cornerCone, hΘ, Complex.exp_pi_mul_I]
    simp only [mul_neg, mul_one, add_re, neg_re, ofReal_re]
    norm_num
    linarith
  · push Not at h1
    have hL : 1 / 10 ≤ |σ.sinhN z| := by
      have := σ.sinhN_wallOne_gt hθ h₁ hx hz.1 (by rw [← he]; exact h1)
      exact le_trans (by linarith) (le_abs_self _)
    have hb : 1 / 2 ≤ σ.blendFn z := by
      have := σ.one_le_blendFn_of_wallOne hz.1 hx.ge (by
        rw [σ.etaTwo_eq_of_cusp hθ]
        change σ.etaOne z ≤ cuspZeroHeight z
        rw [he]; exact im_le_cuspZeroHeight hz.1)
      linarith
    rw [σ.foldE_of_inf hθ h₁ h0.le h1 hL, cornerInfW, angleInfW, σ.blendWeight_eq_one hb,
      angleOneInf, σ.bridgeOne_im_of_wallOne hwall, negHalfArg_zero]
    simp only [sub_self, zero_mul, one_mul, zero_add, Complex.exp_pi_mul_I, mul_neg, mul_one,
      neg_re, ofReal_re]
    linarith [two_lt_outerProfile hK σ.sqrt_constK_le_half
      (lt_trans σ.foldY₁_pos σ.foldY₁_lt_foldY₂) σ.foldY₂_lt_sqrt hz.1 (Y₁ := σ.foldY₁)]

include hθ h₁ in
theorem foldE_wall_two_re {p : ℕ} (hp : 1 ≤ p) (hpθ : σ.θ₁ * p = Real.pi) {z : ℂ}
    (hz : z ∈ σ.triangle) (hw : σ.wallSide 2 z = 0) :
    -(3 / 2) ≤ (σ.foldE p z).re ∧ (σ.foldE p z).re ≤ 3 / 2 := by
  have h₂ := σ.adm_two_of_cusp hθ
  have hK := σ.constK_pos
  have hH := σ.foldH_pos
  have hAB := σ.foldA₁_lt_foldB₁ h₁ h₂
  have hBH := σ.foldB₁_lt_foldH h₁ h₂
  have hφ := σ.foldPhiA_lt_foldPhiB h₁ h₂
  have hv := σ.vertexOne_im_pos
  have hs0 : σ.sinhN z = 0 := by rw [sinhN, hw]; simp
  have hw2 := σ.wallTwo_eq_zero_of hz.1 hw
  have hbt := σ.bridgeTwo_im_of_wallTwo hw2
  have hGh := σ.coneProfile_foldH_lt
  by_cases hzv : z = σ.vertexOne
  · subst hzv
    have heq := (σ.foldE_eventually_apex hθ h₁ (p := p)).self_of_nhds
    rw [heq, apexBefore, show σ.discOne σ.vertexOne = 0 from coneDisc_self _, map_zero,
      zero_pow (by omega)]
    norm_num
  have hz2 := σ.mem_domTwo_of_mem_triangle hz hzv
  have hz1 := σ.mem_domOne_of_mem_triangle hz hzv
  rcases lt_or_ge (cuspZeroHeight z) σ.foldH with h0 | h0
  · have hX : horoX z ≤ σ.foldA₀ := by
      have h1 := σ.sinhN_eq_horoX hθ hz.1
      rw [hs0] at h1
      have hc := cuspZeroHeight_pos hz.1
      have : horoX z + 1 / 2 = 0 := by
        rcases mul_eq_zero.1 h1.symm with h | h
        · linarith
        · exact h
      linarith [σ.neg_half_lt_foldA₀]
    rw [σ.foldE_of_zero h0, σ.cornerZero_eq_bridgeTwo hθ σ.foldA₀_lt_foldB₀ hz2 hX]
    have := σ.re_bound_of_bridgeTwo_real hθ hz2 hbt
    constructor <;> linarith
  have hφθ := σ.discAngle_of_wallTwo hz hw hzv
  by_cases ha : σ.etaOne z < σ.foldA₁
  · simp only [foldE, not_lt.2 h0, ha, ↓reduceIte]
    have hpol := σ.discOne_polar hz1
    rw [hφθ] at hpol
    set r := ‖σ.discOne z‖ with hr
    have hr0 : 0 ≤ r := norm_nonneg _
    have hr1 : r < 1 := norm_coneDisc_lt_one hv hz.1
    have hc : conj (σ.discOne z) ^ p = -((r ^ p : ℝ) : ℂ) := by
      rw [hpol, map_mul, conj_ofReal, ← Complex.exp_conj, mul_pow, ← Complex.exp_nat_mul]
      have e : (p : ℂ) * conj ((σ.θ₁ : ℂ) * I) = -(Real.pi : ℂ) * I := by
        rw [show conj ((σ.θ₁ : ℂ) * I) = -((σ.θ₁ : ℂ) * I) by simp, ← hpθ]
        push_cast; ring
      rw [e, show -(Real.pi : ℂ) * I = -((Real.pi : ℂ) * I) by ring, Complex.exp_neg,
        Complex.exp_pi_mul_I]
      push_cast; ring
    rw [apexBefore, hc]
    have hpow : r ^ p ≤ 1 := pow_le_one₀ hr0 hr1.le
    have hpow0 : 0 ≤ r ^ p := pow_nonneg hr0 p
    simp only [neg_div, sub_neg_eq_add, add_re, neg_re, div_ofNat_re, ofReal_re]
    norm_num
    constructor <;> linarith
  push Not at ha
  by_cases h1 : σ.etaOne z < σ.foldH
  · simp only [foldE, not_lt.2 h0, not_lt.2 ha, h1, ↓reduceIte]
    have hS := σ.coneRadial_lt_foldH hp (coneHeight_ge hv hz.1) h1
    have hS0 : 0 ≤ coneRadial p σ.foldA₁ σ.foldB₁ σ.vertexOne.im σ.constK (σ.etaOne z) := hS.1
    have hS1 : coneRadial p σ.foldA₁ σ.foldB₁ σ.vertexOne.im σ.constK (σ.etaOne z) <
      coneProfile σ.constK σ.foldH := hS.2
    have hΘ : σ.angleCone p σ.foldA₁ σ.foldB₁ σ.foldPhiA σ.foldPhiB z = 0 := by
      rw [angleCone, angleConeBlend, coneLambda, hφθ,
        coneStep_eq_one hφ (σ.foldPhiB_lt h₁ h₂).le, angleTwoCone, hbt, halfArg_zero]
      have : Real.pi - (p : ℝ) * σ.θ₁ = 0 := by rw [mul_comm, hpθ]; ring
      rw [this]
      ring
    rw [cornerCone, hΘ]
    simp only [ofReal_zero, zero_mul, Complex.exp_zero, mul_one, add_re, neg_re, ofReal_re]
    norm_num
    constructor <;> linarith
  · push Not at h1
    rw [σ.foldE_of_lens hθ h₁ h0 h1 (by rw [hs0, abs_zero]; norm_num)]
    have := σ.re_bound_of_bridgeTwo_real hθ hz2 hbt
    constructor <;> linarith

end Values

end ConeShape

end GC.Seifert
