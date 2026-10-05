import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.AssemblyL1Standard
import DifferentialGeometry.Analysis.Calculus.SmoothTransition

/-!
# Chapter-14 assembly, item L1, group G3a: the profile functions of the model cycle

The explicit model normal form of the solid torus (G3a) is rotationally symmetric about the core
circle; its pieces are described by functions of two real variables, collected here.

* `capCos s = (4 - s²) / (4 + s²)`: the cosine of the polar angle of the point of the unit sphere
  with stereographic coordinate of norm `s` (seen from the antipodal pole);
* `neckRadius ε s τ = roundedMin (ε / 4) s (1 + τ)`: the radius of the model neck at the neck
  coordinates `(s, τ)`; `1 + ε * neckRounding ε q = neckRadius ε ‖q.1‖ q.2`, so the rounded union
  is `{neckRadius ≤ 1}` (`one_add_mul_neckRounding`);
* `neckRatio ε s τ = neckRadius ε s τ / s` (`1` near the axis);
* `ballCut R`: a smoothed `max R (3/10)` (it keeps the ball profile smooth at the centre).

Every profile is monotone in each variable; the neck radius moves along the diagonal with slope
one (`neckRadius_add_diag`), which gives the strict monotonicity used for injectivity without
derivatives (`neckRadius_lt_of_lt`).
-/

set_option autoImplicit false

noncomputable section

open Set Function
open DifferentialGeometry.Topology.Manifold.CornerRounding
open scoped ContDiff Topology

namespace GC.GraphManifold.Assembly

/-! ## The polar-angle profile -/

/-- The cosine of the polar angle at stereographic radius `s`. -/
def capCos (s : ℝ) : ℝ := (4 - s ^ 2) / (4 + s ^ 2)

/-- The same profile as a function of the squared radius. -/
def capCosSq (σ : ℝ) : ℝ := (4 - σ) / (4 + σ)

theorem capCos_eq_capCosSq (s : ℝ) : capCos s = capCosSq (s ^ 2) := rfl

theorem capCos_zero : capCos 0 = 1 := by norm_num [capCos]

theorem capCos_one : capCos 1 = 3 / 5 := by norm_num [capCos]

theorem capCos_le_one (s : ℝ) : capCos s ≤ 1 := by
  rw [capCos, div_le_one (by positivity)]
  nlinarith [sq_nonneg s]

theorem capCos_pos {s : ℝ} (hs : |s| < 2) : 0 < capCos s := by
  have h : s ^ 2 < 4 := by
    have h1 := abs_lt.mp hs
    nlinarith
  exact div_pos (by linarith) (by positivity)

theorem capCos_neg (s : ℝ) : capCos (-s) = capCos s := by simp [capCos]

/-- `capCos` is strictly decreasing on `[0, ∞)`. -/
theorem capCos_lt_capCos {s s' : ℝ} (hs : 0 ≤ s) (hss' : s < s') : capCos s' < capCos s := by
  rw [capCos, capCos, div_lt_div_iff₀ (by positivity) (by positivity)]
  have h : s ^ 2 < s' ^ 2 := by nlinarith
  nlinarith

theorem capCos_le_capCos {s s' : ℝ} (hs : 0 ≤ s) (hss' : s ≤ s') : capCos s' ≤ capCos s := by
  rcases eq_or_lt_of_le hss' with h | h
  · rw [h]
  · exact (capCos_lt_capCos hs h).le

theorem capCos_lt_capCos_iff {s s' : ℝ} (hs : 0 ≤ s) (hs' : 0 ≤ s') :
    capCos s' < capCos s ↔ s < s' := by
  constructor
  · intro h
    by_contra hle
    exact absurd h (not_lt.mpr (capCos_le_capCos hs' (not_lt.mp hle)))
  · exact capCos_lt_capCos hs

theorem capCos_injOn {s s' : ℝ} (hs : 0 ≤ s) (hs' : 0 ≤ s') (h : capCos s = capCos s') :
    s = s' := by
  rcases lt_trichotomy s s' with h1 | h1 | h1
  · exact absurd h (capCos_lt_capCos hs h1).ne'
  · exact h1
  · exact absurd h (capCos_lt_capCos hs' h1).ne

theorem hasDerivAt_capCos (s : ℝ) :
    HasDerivAt capCos (-(16 * s) / (4 + s ^ 2) ^ 2) s := by
  have h1 : HasDerivAt (fun s : ℝ => 4 - s ^ 2) (-(2 * s)) s := by
    simpa using ((hasDerivAt_pow 2 s).const_sub 4)
  have h2 : HasDerivAt (fun s : ℝ => 4 + s ^ 2) (2 * s) s := by
    simpa using ((hasDerivAt_pow 2 s).const_add 4)
  have h := h1.fun_div h2 (by positivity : (4 : ℝ) + s ^ 2 ≠ 0)
  exact h.congr_deriv (by field_simp; ring)

theorem contDiff_capCos : ContDiff ℝ ∞ capCos := by
  unfold capCos
  exact ((contDiff_const.sub (contDiff_id.pow 2)).div (contDiff_const.add (contDiff_id.pow 2))
    (fun s => by positivity))

theorem contDiffAt_capCosSq {σ : ℝ} (hσ : σ ≠ -4) : ContDiffAt ℝ ∞ capCosSq σ := by
  unfold capCosSq
  exact (contDiffAt_const.sub contDiffAt_id).div (contDiffAt_const.add contDiffAt_id)
    (by intro h; apply hσ; linarith)

/-- The stereographic radius of the polar angle with cosine `u`. -/
def capRadius (u : ℝ) : ℝ := 2 * Real.sqrt ((1 - u) / (1 + u))

theorem capRadius_nonneg (u : ℝ) : 0 ≤ capRadius u := by
  unfold capRadius
  positivity

theorem capCos_capRadius {u : ℝ} (hu : -1 < u) (hu' : u ≤ 1) : capCos (capRadius u) = u := by
  have hq : 0 ≤ (1 - u) / (1 + u) := div_nonneg (by linarith) (by linarith)
  have hsq : capRadius u ^ 2 = 4 * ((1 - u) / (1 + u)) := by
    rw [capRadius, mul_pow, Real.sq_sqrt hq]
    norm_num
  rw [capCos, hsq]
  have h1 : (1 + u) ≠ 0 := by linarith
  field_simp
  ring

/-- The polar cosine of a point `(ρ, h)` of the meridian half plane, seen from the south pole: at
radius `R = √(ρ² + h²)`, the stereographic radius `2ρ / (R - h)` has polar cosine `-h / R`. -/
theorem mul_capCos_south {ρ h R : ℝ} (hR : R ^ 2 = ρ ^ 2 + h ^ 2) (hR0 : 0 ≤ R)
    (hRh : 0 < R - h) : R * capCos (2 * ρ / (R - h)) = -h := by
  have hsq : (2 * ρ / (R - h)) ^ 2 = 4 * ((R + h) / (R - h)) := by
    rw [div_pow]
    have hρ2 : ρ ^ 2 = (R - h) * (R + h) := by nlinarith
    rw [mul_pow, hρ2]
    field_simp
    ring
  rw [capCos, hsq]
  have hne : R - h ≠ 0 := hRh.ne'
  have hden : 4 + 4 * ((R + h) / (R - h)) = 8 * R / (R - h) := by
    field_simp
    ring
  have hnum : 4 - 4 * ((R + h) / (R - h)) = -8 * h / (R - h) := by
    field_simp
    ring
  rw [hden, hnum]
  rcases eq_or_lt_of_le hR0 with h0 | h0
  · subst h0
    have : h = 0 := by nlinarith [sq_nonneg ρ, sq_nonneg h]
    simp [this]
  · field_simp

/-! ## The neck radius -/

/-- The radius of the model neck at the neck coordinates `(s, τ)`. -/
def neckRadius (ε s τ : ℝ) : ℝ := roundedMin (ε / 4) s (1 + τ)

theorem neckRadius_def (ε s τ : ℝ) :
    neckRadius ε s τ = (s + (1 + τ) - Real.smoothAbs (ε / 4) (s - (1 + τ))) / 2 := rfl

/-- The rounded union of a neck is the unit sublevel of the neck radius. -/
theorem one_add_mul_neckRounding {ε : ℝ} (hε : 0 < ε) (q : EuclideanSpace ℝ (Fin 2) × ℝ) :
    1 + ε * neckRounding ε q = neckRadius ε ‖q.1‖ q.2 := by
  have hscale := Real.smoothAbs.mul_left ε (1 / 4) ((‖q.1‖ - 1 - q.2) / ε)
  rw [show ε * (1 / 4) = ε / 4 by ring, mul_div_cancel₀ _ hε.ne'] at hscale
  rw [neckRounding, standardRimRounding, roundedMin, neckRadius_def, rimRoundingWidth]
  simp only
  rw [show (‖q.1‖ - 1) / ε - q.2 / ε = (‖q.1‖ - 1 - q.2) / ε by ring,
    show ‖q.1‖ - (1 + q.2) = ‖q.1‖ - 1 - q.2 by ring, hscale]
  field_simp
  ring

theorem neckRounding_nonpos_iff {ε : ℝ} (hε : 0 < ε) {q : EuclideanSpace ℝ (Fin 2) × ℝ} :
    neckRounding ε q ≤ 0 ↔ neckRadius ε ‖q.1‖ q.2 ≤ 1 := by
  rw [← one_add_mul_neckRounding hε q]
  constructor
  · intro h
    nlinarith
  · intro h
    by_contra hpos
    have : 0 < ε * neckRounding ε q := mul_pos hε (not_le.mp hpos)
    linarith

variable {ε : ℝ}

theorem neckRadius_le_left (hε : 0 < ε) (s τ : ℝ) : neckRadius ε s τ ≤ s :=
  (roundedMin_le_min (by positivity) s (1 + τ)).trans (min_le_left _ _)

theorem neckRadius_le_right (hε : 0 < ε) (s τ : ℝ) : neckRadius ε s τ ≤ 1 + τ :=
  (roundedMin_le_min (by positivity) s (1 + τ)).trans (min_le_right _ _)

theorem min_sub_le_neckRadius (hε : 0 < ε) (s τ : ℝ) :
    min s (1 + τ) - ε / 4 ≤ neckRadius ε s τ :=
  min_sub_le_roundedMin (by positivity) s (1 + τ)

/-- Near the axis the neck radius is the radius. -/
theorem neckRadius_eq_left (hε : 0 < ε) {s τ : ℝ} (h : s ≤ 1 + τ - ε / 4) :
    neckRadius ε s τ = s := by
  rw [neckRadius, roundedMin_eq_min (by positivity)
    (by rw [abs_sub_comm, abs_of_nonneg (by linarith)]; linarith)]
  exact min_eq_left (by linarith)

/-- Far from the axis the neck radius is `1 + τ`. -/
theorem neckRadius_eq_right (hε : 0 < ε) {s τ : ℝ} (h : 1 + τ + ε / 4 ≤ s) :
    neckRadius ε s τ = 1 + τ := by
  rw [neckRadius, roundedMin_eq_min (by positivity)
    (by rw [abs_of_nonneg (by linarith)]; linarith)]
  exact min_eq_right (by linarith)

theorem neckRadius_add_diag (ε s τ d : ℝ) :
    neckRadius ε (s + d) (τ + d) = neckRadius ε s τ + d := by
  rw [neckRadius_def, neckRadius_def, show s + d - (1 + (τ + d)) = s - (1 + τ) by ring]
  ring

theorem neckRadius_mono_left (ε : ℝ) {s s' : ℝ} (τ : ℝ) (h : s ≤ s') :
    neckRadius ε s τ ≤ neckRadius ε s' τ := by
  rw [neckRadius_def, neckRadius_def]
  have hl := (Real.smoothAbs.lipschitzWith (ε / 4)).dist_le_mul (s' - (1 + τ)) (s - (1 + τ))
  rw [Real.dist_eq, Real.dist_eq, NNReal.coe_one, one_mul,
    show s' - (1 + τ) - (s - (1 + τ)) = s' - s by ring] at hl
  have h2 : |s' - s| = s' - s := abs_of_nonneg (by linarith)
  rw [h2] at hl
  have := (abs_le.mp hl).2
  linarith

theorem neckRadius_mono_right (ε s : ℝ) {τ τ' : ℝ} (h : τ ≤ τ') :
    neckRadius ε s τ ≤ neckRadius ε s τ' := by
  rw [neckRadius_def, neckRadius_def]
  have hl := (Real.smoothAbs.lipschitzWith (ε / 4)).dist_le_mul (s - (1 + τ)) (s - (1 + τ'))
  rw [Real.dist_eq, Real.dist_eq, NNReal.coe_one, one_mul,
    show s - (1 + τ) - (s - (1 + τ')) = τ' - τ by ring] at hl
  have h2 : |τ' - τ| = τ' - τ := abs_of_nonneg (by linarith)
  rw [h2] at hl
  have := (abs_le.mp hl).1
  linarith

theorem neckRadius_mono (ε : ℝ) {s s' τ τ' : ℝ} (hs : s ≤ s') (hτ : τ ≤ τ') :
    neckRadius ε s τ ≤ neckRadius ε s' τ' :=
  (neckRadius_mono_left ε τ hs).trans (neckRadius_mono_right ε s' hτ)

/-- Strict monotonicity along a direction increasing both variables strictly. -/
theorem neckRadius_lt_of_lt (ε : ℝ) {s s' τ τ' : ℝ} (hs : s < s') (hτ : τ < τ') :
    neckRadius ε s τ < neckRadius ε s' τ' := by
  set d := min (s' - s) (τ' - τ)
  have hd : 0 < d := lt_min (by linarith) (by linarith)
  have h1 : neckRadius ε (s + d) (τ + d) ≤ neckRadius ε s' τ' :=
    neckRadius_mono ε (by linarith [min_le_left (s' - s) (τ' - τ)])
      (by linarith [min_le_right (s' - s) (τ' - τ)])
  rw [neckRadius_add_diag] at h1
  linarith

theorem contDiff_neckRadius (ε : ℝ) :
    ContDiff ℝ ∞ (fun p : ℝ × ℝ => neckRadius ε p.1 p.2) := by
  unfold neckRadius
  exact (contDiff_roundedMin (ε / 4)).comp (contDiff_fst.prodMk (contDiff_const.add contDiff_snd))

theorem continuous_neckRadius (ε : ℝ) : Continuous (fun p : ℝ × ℝ => neckRadius ε p.1 p.2) :=
  (contDiff_neckRadius ε).continuous

/-- The derivative of the neck radius along a curve `t ↦ (a t, b t)`. -/
theorem HasDerivAt.neckRadius {a b : ℝ → ℝ} {a' b' t : ℝ} (ha : HasDerivAt a a' t)
    (hb : HasDerivAt b b' t) :
    HasDerivAt (fun t => neckRadius ε (a t) (b t))
      ((a' + b' - deriv (Real.smoothAbs (ε / 4)) (a t - (1 + b t)) * (a' - b')) / 2) t := by
  have habs : HasDerivAt (Real.smoothAbs (ε / 4)) (deriv (Real.smoothAbs (ε / 4))
      (a t - (1 + b t))) (a t - (1 + b t)) :=
    ((Real.smoothAbs.contDiff (ε / 4)).differentiable (by simp) _).hasDerivAt
  have hin : HasDerivAt (fun t => a t - (1 + b t)) (a' - b') t :=
    (ha.fun_sub (hb.const_add 1)).congr_deriv (by ring)
  have h := ((ha.fun_add (hb.const_add 1)).fun_sub (habs.comp t hin)).div_const 2
  simp only [neckRadius_def]
  exact h.congr_deriv (by ring)

theorem abs_deriv_smoothAbs_le (w x : ℝ) : |deriv (Real.smoothAbs w) x| ≤ 1 :=
  Real.smoothAbs.abs_deriv_le_one w x

/-- The derivative of `smoothAbs` is below one strictly to the left of the width. -/
theorem deriv_smoothAbs_lt_one {w x : ℝ} (hw : 0 < w) (hx : x < w) :
    deriv (Real.smoothAbs w) x < 1 := by
  rw [Real.smoothAbs.deriv]
  have : 0 < Real.smoothTransition ((w - x) / (2 * w)) :=
    Real.smoothTransition.pos_of_pos (div_pos (by linarith) (by positivity))
  linarith

/-- The derivative of `smoothAbs` is above minus one strictly to the right of minus the width. -/
theorem neg_one_lt_deriv_smoothAbs {w x : ℝ} (hw : 0 < w) (hx : -w < x) :
    -1 < deriv (Real.smoothAbs w) x := by
  rw [Real.smoothAbs.deriv]
  have : Real.smoothTransition ((w - x) / (2 * w)) < 1 :=
    Real.smoothTransition.lt_one_of_lt_one (by rw [div_lt_one (by positivity)]; linarith)
  linarith

/-! ## The neck ratio -/

/-- The neck radius divided by the radius (`1` near the axis). -/
def neckRatio (ε s τ : ℝ) : ℝ := 1 + (neckRadius ε s τ - s) / s

theorem neckRatio_mul {s : ℝ} (hs : s ≠ 0) (τ : ℝ) : neckRatio ε s τ * s = neckRadius ε s τ := by
  rw [neckRatio]
  field_simp
  ring

theorem neckRatio_eq_one (hε : 0 < ε) {s τ : ℝ} (h : s ≤ 1 + τ - ε / 4) : neckRatio ε s τ = 1 := by
  rw [neckRatio, neckRadius_eq_left hε h, sub_self, zero_div, add_zero]

theorem neckRatio_pos (hε : 0 < ε) (hε' : ε ≤ 1 / 8) {s τ : ℝ} (hτ : 1 / 4 ≤ 1 + τ) :
    0 < neckRatio ε s τ := by
  by_cases hle : s ≤ 1 + τ - ε / 4
  · rw [neckRatio_eq_one hε hle]
    exact one_pos
  · have hs0 : 0 < s := by linarith
    have hpos : 0 < neckRadius ε s τ := by
      have := min_sub_le_neckRadius hε s τ
      have hmin : 1 / 4 - ε / 4 ≤ min s (1 + τ) := le_min (by linarith) (by linarith)
      linarith
    rw [← mul_lt_mul_iff_of_pos_right hs0, zero_mul, neckRatio_mul hs0.ne']
    exact hpos

/-- The neck ratio as a function of the squared radius. -/
def neckRatioSq (ε σ τ : ℝ) : ℝ := neckRatio ε (Real.sqrt σ) τ

/-- Near the axis the squared-radius neck ratio is one. -/
theorem neckRatioSq_eq_one (hε : 0 < ε) {σ τ : ℝ} (hτ : ε / 4 < 1 + τ)
    (hσ : σ < (1 + τ - ε / 4) ^ 2) : neckRatioSq ε σ τ = 1 := by
  apply neckRatio_eq_one hε
  rcases le_or_gt σ 0 with h0 | h0
  · rw [Real.sqrt_eq_zero'.mpr h0]
    linarith
  · have : Real.sqrt σ < 1 + τ - ε / 4 := by
      rw [Real.sqrt_lt' (by linarith)]
      exact hσ
    exact this.le

theorem contDiffAt_neckRatioSq (hε : 0 < ε) {σ τ : ℝ} (hτ : ε / 4 < 1 + τ) :
    ContDiffAt ℝ ∞ (fun p : ℝ × ℝ => neckRatioSq ε p.1 p.2) (σ, τ) := by
  by_cases hσ : σ < (1 + τ - ε / 4) ^ 2
  · -- locally constant
    have hopen : IsOpen {p : ℝ × ℝ | ε / 4 < 1 + p.2 ∧ p.1 < (1 + p.2 - ε / 4) ^ 2} :=
      (isOpen_lt continuous_const (continuous_const.add continuous_snd)).inter
        (isOpen_lt continuous_fst
          (((continuous_const.add continuous_snd).sub continuous_const).pow 2))
    have hev : (fun p : ℝ × ℝ => neckRatioSq ε p.1 p.2) =ᶠ[𝓝 (σ, τ)] fun _ => (1 : ℝ) := by
      filter_upwards [hopen.mem_nhds ⟨hτ, hσ⟩] with p hp
      exact neckRatioSq_eq_one hε hp.1 hp.2
    exact contDiffAt_const.congr_of_eventuallyEq hev
  · have hpos : 0 < σ := by
      have h1 : 0 < (1 + τ - ε / 4) ^ 2 := by
        have : 0 < 1 + τ - ε / 4 := by linarith
        positivity
      linarith [not_lt.mp hσ]
    have hsq : ContDiffAt ℝ ∞ (fun p : ℝ × ℝ => Real.sqrt p.1) (σ, τ) :=
      (Real.contDiffAt_sqrt hpos.ne').comp _ contDiffAt_fst
    have hsq0 : Real.sqrt σ ≠ 0 := (Real.sqrt_pos.mpr hpos).ne'
    have hrad : ContDiffAt ℝ ∞ (fun p : ℝ × ℝ => neckRadius ε (Real.sqrt p.1) p.2) (σ, τ) :=
      (contDiff_neckRadius ε).contDiffAt.comp _ (hsq.prodMk contDiffAt_snd)
    unfold neckRatioSq neckRatio
    exact contDiffAt_const.add ((hrad.sub hsq).div hsq hsq0)

/-! ## The smoothed cut of the ball radius -/

/-- The centre value of the ball cut. -/
def ballCutCentre : ℝ := 3 / 10

/-- The width of the ball cut. -/
def ballCutWidth : ℝ := 13 / 50

/-- A smoothed `max R (3/10)`. -/
def ballCut (R : ℝ) : ℝ := (R + ballCutCentre + Real.smoothAbs ballCutWidth (R - ballCutCentre)) / 2

theorem ballCutWidth_pos : 0 < ballCutWidth := by norm_num [ballCutWidth]

theorem le_ballCut (R : ℝ) : max R ballCutCentre ≤ ballCut R := by
  have h := (Real.smoothAbs.sub_abs_mem_Icc ballCutWidth_pos (R - ballCutCentre)).1
  rw [ballCut]
  rcases le_total R ballCutCentre with h1 | h1
  · rw [max_eq_right h1, abs_of_nonpos (by linarith)] at *
    linarith
  · rw [max_eq_left h1, abs_of_nonneg (by linarith)] at *
    linarith

theorem ballCut_le (R : ℝ) : ballCut R ≤ max R ballCutCentre + ballCutWidth := by
  have h := (Real.smoothAbs.sub_abs_mem_Icc ballCutWidth_pos (R - ballCutCentre)).2
  rw [ballCut]
  rcases le_total R ballCutCentre with h1 | h1
  · rw [max_eq_right h1, abs_of_nonpos (by linarith)] at *
    linarith
  · rw [max_eq_left h1, abs_of_nonneg (by linarith)] at *
    linarith

theorem ballCut_eq_self {R : ℝ} (h : ballCutCentre + ballCutWidth ≤ R) : ballCut R = R := by
  rw [ballCut, Real.smoothAbs.eq_self_of_le ballCutWidth_pos (by linarith)]
  ring

theorem ballCut_eq_centre {R : ℝ} (h : R ≤ ballCutCentre - ballCutWidth) :
    ballCut R = ballCutCentre := by
  rw [ballCut, Real.smoothAbs.eq_neg_of_le ballCutWidth_pos (by linarith)]
  ring

theorem hasDerivAt_ballCut (R : ℝ) :
    HasDerivAt ballCut ((1 + deriv (Real.smoothAbs ballCutWidth) (R - ballCutCentre)) / 2) R := by
  have habs : HasDerivAt (Real.smoothAbs ballCutWidth)
      (deriv (Real.smoothAbs ballCutWidth) (R - ballCutCentre)) (R - ballCutCentre) :=
    ((Real.smoothAbs.contDiff ballCutWidth).differentiable (by simp) _).hasDerivAt
  have h := (((hasDerivAt_id R).add_const ballCutCentre).fun_add
    (habs.comp R ((hasDerivAt_id R).sub_const ballCutCentre))).div_const 2
  simp only [Function.comp_def, id] at h
  exact h.congr_deriv (by ring)

theorem contDiff_ballCut : ContDiff ℝ ∞ ballCut := by
  unfold ballCut
  exact ((contDiff_id.add contDiff_const).add
    ((Real.smoothAbs.contDiff ballCutWidth).comp (contDiff_id.sub contDiff_const))).div_const 2

theorem ballCut_mono {R R' : ℝ} (h : R ≤ R') : ballCut R ≤ ballCut R' := by
  rw [ballCut, ballCut]
  have hl := (Real.smoothAbs.lipschitzWith ballCutWidth).dist_le_mul (R' - ballCutCentre)
    (R - ballCutCentre)
  rw [Real.dist_eq, Real.dist_eq, NNReal.coe_one, one_mul,
    show R' - ballCutCentre - (R - ballCutCentre) = R' - R by ring] at hl
  have h2 : |R' - R| = R' - R := abs_of_nonneg (by linarith)
  rw [h2] at hl
  have := (abs_le.mp hl).1
  linarith

/-- The ball cut as a function of the squared radius: smooth everywhere. -/
def ballCutSq (x : ℝ) : ℝ := ballCut (Real.sqrt x)

theorem contDiff_ballCutSq : ContDiff ℝ ∞ ballCutSq := by
  rw [contDiff_iff_contDiffAt]
  intro x
  by_cases hx : x < (ballCutCentre - ballCutWidth) ^ 2
  · have hev : ballCutSq =ᶠ[𝓝 x] fun _ => ballCutCentre := by
      filter_upwards [(isOpen_gt' ((ballCutCentre - ballCutWidth) ^ 2)).mem_nhds hx] with y hy
      apply ballCut_eq_centre
      have hcw : 0 ≤ ballCutCentre - ballCutWidth := by norm_num [ballCutCentre, ballCutWidth]
      rcases le_or_gt y 0 with h0 | h0
      · rw [Real.sqrt_eq_zero'.mpr h0]
        exact hcw
      · exact ((Real.sqrt_lt' (by norm_num [ballCutCentre, ballCutWidth])).mpr hy).le
    exact contDiffAt_const.congr_of_eventuallyEq hev
  · have hpos : 0 < x := by
      have : 0 < (ballCutCentre - ballCutWidth) ^ 2 := by norm_num [ballCutCentre, ballCutWidth]
      linarith [not_lt.mp hx]
    exact contDiff_ballCut.contDiffAt.comp x (Real.contDiffAt_sqrt hpos.ne')

/-! ## The zone profiles (handles and necks) -/

/-- The blend between the two ends of a handle. -/
def zoneBlend (t : ℝ) : ℝ := Real.smoothTransition (3 * t - 1)

theorem zoneBlend_of_le {t : ℝ} (ht : t ≤ 1 / 3) : zoneBlend t = 0 :=
  Real.smoothTransition.zero_of_nonpos (by linarith)

theorem zoneBlend_of_ge {t : ℝ} (ht : 2 / 3 ≤ t) : zoneBlend t = 1 :=
  Real.smoothTransition.one_of_one_le (by linarith)

theorem zoneBlend_mono : Monotone zoneBlend := fun _ _ h =>
  Real.smoothTransition.monotone (by linarith)

theorem contDiff_zoneBlend : ContDiff ℝ ∞ zoneBlend :=
  (Real.smoothTransition.contDiff (n := ⊤)).comp ((contDiff_const.mul contDiff_id).sub contDiff_const)

/-- The height (relative to the zone base) of the point `(s, t)` of a handle. -/
def zoneHeight (s t : ℝ) : ℝ := (1 + t) * capCos s + zoneBlend t * (4 - 3 * capCos s)

theorem zoneHeight_of_le {s t : ℝ} (ht : t ≤ 1 / 3) : zoneHeight s t = (1 + t) * capCos s := by
  rw [zoneHeight, zoneBlend_of_le ht, zero_mul, add_zero]

theorem zoneHeight_of_ge {s t : ℝ} (ht : 2 / 3 ≤ t) :
    zoneHeight s t = 4 - (1 + (1 - t)) * capCos s := by
  rw [zoneHeight, zoneBlend_of_ge ht]
  ring

theorem zoneHeight_lt {s t t' : ℝ} (hs : |s| < 2) (htt' : t < t') :
    zoneHeight s t < zoneHeight s t' := by
  have hq := capCos_pos hs
  have hq1 := capCos_le_one s
  have hb := zoneBlend_mono htt'.le
  rw [zoneHeight, zoneHeight]
  nlinarith

theorem zoneHeight_strictMono {s : ℝ} (hs : |s| < 2) : StrictMono (zoneHeight s) :=
  fun _ _ h => zoneHeight_lt hs h

theorem contDiff_zoneHeight :
    ContDiff ℝ ∞ (fun p : ℝ × ℝ => zoneHeight p.1 p.2) := by
  unfold zoneHeight
  exact ((contDiff_const.add contDiff_snd).mul (contDiff_capCos.comp contDiff_fst)).add
    ((contDiff_zoneBlend.comp contDiff_snd).mul
      (contDiff_const.sub (contDiff_const.mul (contDiff_capCos.comp contDiff_fst))))

/-- The height of a handle point as a function of the squared radius. -/
def zoneHeightSq (σ t : ℝ) : ℝ := (1 + t) * capCosSq σ + zoneBlend t * (4 - 3 * capCosSq σ)

theorem zoneHeightSq_sq (s t : ℝ) : zoneHeightSq (s ^ 2) t = zoneHeight s t := rfl

theorem contDiffAt_zoneHeightSq {σ t : ℝ} (hσ : σ ≠ -4) :
    ContDiffAt ℝ ∞ (fun p : ℝ × ℝ => zoneHeightSq p.1 p.2) (σ, t) := by
  have hq : ContDiffAt ℝ ∞ (fun p : ℝ × ℝ => capCosSq p.1) (σ, t) :=
    ContDiffAt.comp (g := capCosSq) (σ, t) (contDiffAt_capCosSq hσ) contDiffAt_fst
  unfold zoneHeightSq
  exact ((contDiffAt_const.add contDiffAt_snd).mul hq).add
    ((contDiff_zoneBlend.contDiffAt.comp _ contDiffAt_snd).mul
      (contDiffAt_const.sub (contDiffAt_const.mul hq)))

theorem hasDerivAt_zoneHeight (s t : ℝ) :
    HasDerivAt (zoneHeight s) (capCos s + deriv zoneBlend t * (4 - 3 * capCos s)) t := by
  have hb : HasDerivAt zoneBlend (deriv zoneBlend t) t :=
    (contDiff_zoneBlend.differentiable (by simp) t).hasDerivAt
  have h := (((hasDerivAt_id t).const_add 1).mul_const (capCos s)).fun_add
    (hb.mul_const (4 - 3 * capCos s))
  exact h.congr_deriv (by simp)

theorem deriv_zoneBlend_nonneg (t : ℝ) : 0 ≤ deriv zoneBlend t :=
  zoneBlend_mono.deriv_nonneg

theorem deriv_zoneHeight_pos {s t : ℝ} (hs : |s| < 2) :
    0 < capCos s + deriv zoneBlend t * (4 - 3 * capCos s) := by
  have hq := capCos_pos hs
  have hq1 := capCos_le_one s
  have hd := deriv_zoneBlend_nonneg t
  nlinarith

/-- The radial ratio of the zone map at radius `s` and height `u`: the neck ratio of the lower
end for `u ≤ 2`, of the upper end for `u ≥ 2`. -/
def zoneRatio (ε s u : ℝ) : ℝ :=
  neckRatio ε s (u / capCos s - 1) * neckRatio ε s ((4 - u) / capCos s - 1)

/-- The same ratio as a function of the squared radius. -/
def zoneRatioSq (ε σ u : ℝ) : ℝ :=
  neckRatioSq ε σ (u / capCosSq σ - 1) * neckRatioSq ε σ ((4 - u) / capCosSq σ - 1)

theorem zoneRatioSq_sq {s : ℝ} (hs : 0 ≤ s) (u : ℝ) : zoneRatioSq ε (s ^ 2) u = zoneRatio ε s u := by
  rw [zoneRatioSq, zoneRatio, neckRatioSq, neckRatioSq, Real.sqrt_sq hs, ← capCos_eq_capCosSq]

/-- The radius of the zone map. -/
def zoneRadius (ε s u : ℝ) : ℝ := s * zoneRatio ε s u

theorem zoneRatio_eq_lower (hε : 0 < ε) (hε' : ε ≤ 1 / 8) {s u : ℝ} (hs : |s| ≤ 3 / 2)
    (hu : u ≤ 2) : zoneRatio ε s u = neckRatio ε s (u / capCos s - 1) := by
  have hq := capCos_pos (show |s| < 2 by linarith)
  have hq1 := capCos_le_one s
  have h2 : 1 ≤ (4 - u) / capCos s - 1 := by
    rw [le_sub_iff_add_le, le_div_iff₀ hq]
    nlinarith
  rw [zoneRatio, neckRatio_eq_one hε (show s ≤ 1 + ((4 - u) / capCos s - 1) - ε / 4 by
    have := le_abs_self s
    linarith), mul_one]

theorem zoneRatio_eq_upper (hε : 0 < ε) (hε' : ε ≤ 1 / 8) {s u : ℝ} (hs : |s| ≤ 3 / 2)
    (hu : 2 ≤ u) : zoneRatio ε s u = neckRatio ε s ((4 - u) / capCos s - 1) := by
  have hq := capCos_pos (show |s| < 2 by linarith)
  have hq1 := capCos_le_one s
  have h2 : 1 ≤ u / capCos s - 1 := by
    rw [le_sub_iff_add_le, le_div_iff₀ hq]
    nlinarith
  rw [zoneRatio, neckRatio_eq_one hε (show s ≤ 1 + (u / capCos s - 1) - ε / 4 by
    have := le_abs_self s
    linarith), one_mul]

theorem zoneRadius_eq_lower (hε : 0 < ε) (hε' : ε ≤ 1 / 8) {s u : ℝ} (hs : 0 ≤ s)
    (hs' : s ≤ 3 / 2) (hu : u ≤ 2) (hu' : 1 / 4 ≤ u) :
    zoneRadius ε s u = neckRadius ε s (u / capCos s - 1) := by
  rw [zoneRadius, zoneRatio_eq_lower hε hε' (by rw [abs_of_nonneg hs]; exact hs') hu]
  rcases eq_or_lt_of_le hs with h0 | h0
  · subst h0
    rw [zero_mul, neckRadius_eq_left hε (by rw [capCos_zero, div_one]; linarith)]
  · rw [mul_comm, neckRatio_mul h0.ne']

theorem zoneRadius_eq_upper (hε : 0 < ε) (hε' : ε ≤ 1 / 8) {s u : ℝ} (hs : 0 ≤ s)
    (hs' : s ≤ 3 / 2) (hu : 2 ≤ u) (hu' : u ≤ 4 - 1 / 4) :
    zoneRadius ε s u = neckRadius ε s ((4 - u) / capCos s - 1) := by
  rw [zoneRadius, zoneRatio_eq_upper hε hε' (by rw [abs_of_nonneg hs]; exact hs') hu]
  rcases eq_or_lt_of_le hs with h0 | h0
  · subst h0
    rw [zero_mul, neckRadius_eq_left hε (by rw [capCos_zero, div_one]; linarith)]
  · rw [mul_comm, neckRatio_mul h0.ne']

/-- The neck coordinate of the zone height is increasing in the radius. -/
theorem div_capCos_lt {s s' u : ℝ} (hs : 0 ≤ s) (hss' : s < s') (hs' : s' < 2) (hu : 0 < u) :
    u / capCos s < u / capCos s' := by
  have hq' := capCos_pos (show |s'| < 2 by rw [abs_of_nonneg (by linarith)]; exact hs')
  exact div_lt_div_of_pos_left hu hq' (capCos_lt_capCos hs hss')

/-- **Radial strict monotonicity of the zone map.** -/
theorem zoneRadius_lt (hε : 0 < ε) (hε' : ε ≤ 1 / 8) {s s' u : ℝ} (hs : 0 ≤ s) (hss' : s < s')
    (hs' : s' ≤ 3 / 2) (hu : 1 / 4 ≤ u) (hu' : u ≤ 4 - 1 / 4) :
    zoneRadius ε s u < zoneRadius ε s' u := by
  rcases le_total u 2 with h2 | h2
  · rw [zoneRadius_eq_lower hε hε' hs (by linarith) h2 hu,
      zoneRadius_eq_lower hε hε' (by linarith) hs' h2 hu]
    exact neckRadius_lt_of_lt ε hss' (by
      linarith [div_capCos_lt hs hss' (by linarith) (show 0 < u by linarith)])
  · rw [zoneRadius_eq_upper hε hε' hs (by linarith) h2 hu',
      zoneRadius_eq_upper hε hε' (by linarith) hs' h2 hu']
    exact neckRadius_lt_of_lt ε hss' (by
      linarith [div_capCos_lt hs hss' (by linarith) (show 0 < 4 - u by linarith)])

theorem zoneRadius_le (hε : 0 < ε) (hε' : ε ≤ 1 / 8) {s u : ℝ} (hs : 0 ≤ s) (hs' : s ≤ 3 / 2)
    (hu : 1 / 4 ≤ u) (hu' : u ≤ 4 - 1 / 4) : zoneRadius ε s u ≤ s := by
  rcases le_total u 2 with h2 | h2
  · rw [zoneRadius_eq_lower hε hε' hs hs' h2 hu]
    exact neckRadius_le_left hε _ _
  · rw [zoneRadius_eq_upper hε hε' hs hs' h2 hu']
    exact neckRadius_le_left hε _ _

/-- The derivative of the neck radius along `s ↦ (s, c / capCos s - 1)` is positive. -/
theorem hasDerivAt_neckRadius_capCos {s c : ℝ} (hs : 0 < s) (hs' : s < 2) (hc : 0 < c) :
    ∃ d, 0 < d ∧ HasDerivAt (fun s => neckRadius ε s (c / capCos s - 1)) d s := by
  have hq := capCos_pos (show |s| < 2 by rw [abs_of_pos hs]; exact hs')
  set b' : ℝ := c * (16 * s / (4 + s ^ 2) ^ 2) / capCos s ^ 2 with hb'
  have hb'pos : 0 < b' := by
    rw [hb']
    positivity
  have hbder : HasDerivAt (fun s => c / capCos s - 1) b' s := by
    have := ((hasDerivAt_const s c).fun_div (hasDerivAt_capCos s) hq.ne').sub_const 1
    exact this.congr_deriv (by rw [hb']; ring)
  have h := HasDerivAt.neckRadius (ε := ε) (hasDerivAt_id s) hbder
  refine ⟨_, ?_, h⟩
  simp only [id]
  have hσ := abs_le.mp (abs_deriv_smoothAbs_le (ε / 4) (s - (1 + (c / capCos s - 1))))
  rcases lt_or_eq_of_le hσ.2 with h1 | h1
  · nlinarith [mul_nonneg hb'pos.le (show 0 ≤ 1 + deriv (Real.smoothAbs (ε / 4))
      (s - (1 + (c / capCos s - 1))) by linarith)]
  · rw [h1]
    linarith

/-! ## The ball profile -/

/-- The smoothed `|h|` of the ball profile. -/
def ballHeightAbs (h : ℝ) : ℝ := Real.smoothAbs (1 / 4) h

theorem ballHeightAbs_pos (h : ℝ) : 0 < ballHeightAbs h := Real.smoothAbs.pos (by norm_num) h

theorem ballHeightAbs_eq {h : ℝ} (hh : 1 / 4 ≤ |h|) : ballHeightAbs h = |h| :=
  Real.smoothAbs.eq_abs_of_le (by norm_num) hh

theorem ballCutSq_ge (x : ℝ) : ballCutCentre ≤ ballCutSq x :=
  (le_max_right _ _).trans (le_ballCut _)

theorem sqrt_le_ballCutSq (x : ℝ) : Real.sqrt x ≤ ballCutSq x :=
  (le_max_left _ _).trans (le_ballCut _)

theorem ballCutCentre_pos : 0 < ballCutCentre := by norm_num [ballCutCentre]

/-- The denominator of the ball profile at squared radius `σ` and height `h`. -/
def ballDen (σ h : ℝ) : ℝ := ballCutSq (σ + h ^ 2) + ballHeightAbs h

theorem ballDen_pos (σ h : ℝ) : 0 < ballDen σ h :=
  add_pos (ballCutCentre_pos.trans_le (ballCutSq_ge _)) (ballHeightAbs_pos h)

/-- The radial ratio of the ball map at squared radius `σ` and height `h`. -/
def ballRatioSq (ε σ h : ℝ) : ℝ :=
  neckRatioSq ε (4 * σ / ballDen σ h ^ 2) (ballCutSq (σ + h ^ 2) - 1) * (2 / ballDen σ h)

/-- The radius of the ball map at radius `ρ` and height `h`. -/
def ballRadius (ε ρ h : ℝ) : ℝ := ρ * ballRatioSq ε (ρ ^ 2) h

theorem ballRadius_eq (hε : 0 < ε) (hε' : ε ≤ 1 / 8) {ρ : ℝ} (hρ : 0 ≤ ρ) (h : ℝ) :
    ballRadius ε ρ h = neckRadius ε (2 * ρ / ballDen (ρ ^ 2) h) (ballCutSq (ρ ^ 2 + h ^ 2) - 1) := by
  have hD := ballDen_pos (ρ ^ 2) h
  have hsq : Real.sqrt (4 * ρ ^ 2 / ballDen (ρ ^ 2) h ^ 2) = 2 * ρ / ballDen (ρ ^ 2) h := by
    rw [show 4 * ρ ^ 2 / ballDen (ρ ^ 2) h ^ 2 = (2 * ρ / ballDen (ρ ^ 2) h) ^ 2 by ring,
      Real.sqrt_sq (by positivity)]
  rw [ballRadius, ballRatioSq, neckRatioSq, hsq]
  rcases eq_or_lt_of_le hρ with h0 | h0
  · subst h0
    have hc := ballCutSq_ge ((0 : ℝ) ^ 2 + h ^ 2)
    rw [zero_mul, mul_zero, zero_div, neckRadius_eq_left hε (by
      norm_num [ballCutCentre] at hc ⊢
      linarith)]
  · have hne : 2 * ρ / ballDen (ρ ^ 2) h ≠ 0 := by positivity
    rw [← neckRatio_mul hne]
    field_simp

theorem contDiff_ballRatioSq (hε : 0 < ε) (hε' : ε ≤ 1 / 8) :
    ContDiff ℝ ∞ (fun p : ℝ × ℝ => ballRatioSq ε p.1 p.2) := by
  rw [contDiff_iff_contDiffAt]
  rintro ⟨σ, h⟩
  have hcut : ContDiff ℝ ∞ (fun p : ℝ × ℝ => ballCutSq (p.1 + p.2 ^ 2)) :=
    contDiff_ballCutSq.comp (contDiff_fst.add (contDiff_snd.pow 2))
  have hden : ContDiff ℝ ∞ (fun p : ℝ × ℝ => ballDen p.1 p.2) :=
    hcut.add ((Real.smoothAbs.contDiff (1 / 4)).comp contDiff_snd)
  have hden0 : ∀ p : ℝ × ℝ, ballDen p.1 p.2 ≠ 0 := fun p => (ballDen_pos p.1 p.2).ne'
  have harg : ContDiffAt ℝ ∞ (fun p : ℝ × ℝ =>
      (4 * p.1 / ballDen p.1 p.2 ^ 2, ballCutSq (p.1 + p.2 ^ 2) - 1)) (σ, h) :=
    (((contDiffAt_const.mul contDiffAt_fst).div (hden.contDiffAt.pow 2)
      (pow_ne_zero 2 (hden0 (σ, h))))).prodMk (hcut.contDiffAt.sub contDiffAt_const)
  have hτ : ε / 4 < 1 + (ballCutSq (σ + h ^ 2) - 1) := by
    have := ballCutSq_ge (σ + h ^ 2)
    norm_num [ballCutCentre] at this ⊢
    linarith
  have hratio := (contDiffAt_neckRatioSq hε hτ).comp (σ, h) harg
  unfold ballRatioSq
  exact hratio.mul (contDiffAt_const.div hden.contDiffAt (hden0 (σ, h)))

/-- **Radial derivative of the ball profile.** -/
theorem hasDerivAt_ballRadius (hε : 0 < ε) (hε' : ε ≤ 1 / 8) {ρ : ℝ} (hρ : 0 < ρ) (h : ℝ) :
    ∃ d, 0 < d ∧ HasDerivAt (fun ρ => ballRadius ε ρ h) d ρ := by
  set x := ρ ^ 2 + h ^ 2 with hx
  have hxpos : 0 < x := by positivity
  set R := Real.sqrt x with hR
  have hRpos : 0 < R := Real.sqrt_pos.mpr hxpos
  set bc := (1 + deriv (Real.smoothAbs ballCutWidth) (R - ballCutCentre)) / 2 with hbc
  have hcutd : HasDerivAt ballCutSq (bc * (1 / (2 * R))) x := by
    have h1 := (hasDerivAt_ballCut R).comp x (Real.hasDerivAt_sqrt hxpos.ne')
    exact h1
  set c₁ := bc * (1 / (2 * R)) * (2 * ρ) with hc₁
  have hRd : HasDerivAt (fun ρ => ballCutSq (ρ ^ 2 + h ^ 2)) c₁ ρ := by
    have h2 : HasDerivAt (fun ρ : ℝ => ρ ^ 2 + h ^ 2) (2 * ρ) ρ := by
      simpa using (hasDerivAt_pow 2 ρ).add_const (h ^ 2)
    have h3 := hcutd.comp ρ h2
    exact h3
  set Rt := ballCutSq x with hRt
  set D := Rt + ballHeightAbs h with hD
  have hDpos : 0 < D := ballDen_pos (ρ ^ 2) h
  have hDd : HasDerivAt (fun ρ => ballDen (ρ ^ 2) h) c₁ ρ :=
    hRd.add_const (ballHeightAbs h)
  set a' := (2 * D - 2 * ρ * c₁) / D ^ 2 with ha'
  have had : HasDerivAt (fun ρ => 2 * ρ / ballDen (ρ ^ 2) h) a' ρ := by
    have := ((hasDerivAt_id ρ).const_mul 2).fun_div hDd hDpos.ne'
    exact this.congr_deriv (by simp only [id, mul_one, ha']; rfl)
  have hbd : HasDerivAt (fun ρ => ballCutSq (ρ ^ 2 + h ^ 2) - 1) c₁ ρ := hRd.sub_const 1
  have hmain := HasDerivAt.neckRadius (ε := ε) had hbd
  have hev : (fun ρ => ballRadius ε ρ h) =ᶠ[𝓝 ρ] fun ρ => neckRadius ε (2 * ρ / ballDen (ρ ^ 2) h)
      (ballCutSq (ρ ^ 2 + h ^ 2) - 1) := by
    filter_upwards [lt_mem_nhds hρ] with y hy
    exact ballRadius_eq hε hε' hy.le h
  refine ⟨_, ?_, hmain.congr_of_eventuallyEq hev⟩
  -- positivity of the derivative
  have hbc0 : 0 ≤ bc := by
    have := (abs_le.mp (abs_deriv_smoothAbs_le ballCutWidth (R - ballCutCentre))).1
    rw [hbc]
    linarith
  have hbc1 : bc ≤ 1 := by
    have := (abs_le.mp (abs_deriv_smoothAbs_le ballCutWidth (R - ballCutCentre))).2
    rw [hbc]
    linarith
  have hc₁eq : c₁ = bc * ρ / R := by
    rw [hc₁]
    field_simp
  have hc₁0 : 0 ≤ c₁ := by rw [hc₁eq]; positivity
  have hρR : ρ ≤ R := by
    rw [hR, hx]
    exact Real.le_sqrt_of_sq_le (by nlinarith [sq_nonneg h])
  have hRRt : R ≤ Rt := sqrt_le_ballCutSq x
  have hρc : ρ * c₁ ≤ R := by
    rw [hc₁eq]
    have : ρ * (bc * ρ / R) = bc * (ρ ^ 2 / R) := by ring
    rw [this]
    have h1 : ρ ^ 2 / R ≤ R := by
      rw [div_le_iff₀ hRpos]
      nlinarith
    have h2 : 0 ≤ ρ ^ 2 / R := by positivity
    nlinarith
  have ha'pos : 0 < a' := by
    rw [ha']
    have : 0 < 2 * D - 2 * ρ * c₁ := by
      have := ballHeightAbs_pos h
      nlinarith
    positivity
  set X := deriv (Real.smoothAbs (ε / 4)) (2 * ρ / ballDen (ρ ^ 2) h -
    (1 + (ballCutSq (ρ ^ 2 + h ^ 2) - 1))) with hX
  have hXb := abs_le.mp (abs_deriv_smoothAbs_le (ε / 4) (2 * ρ / ballDen (ρ ^ 2) h -
    (1 + (ballCutSq (ρ ^ 2 + h ^ 2) - 1))))
  rw [← hX] at hXb
  rcases lt_or_eq_of_le hXb.2 with hX1 | hX1
  · nlinarith [mul_nonneg hc₁0 (show 0 ≤ 1 + X by linarith)]
  · -- exact zone: the cut radius moves
    have hzone : ε / 4 ≤ 2 * ρ / ballDen (ρ ^ 2) h - (1 + (ballCutSq (ρ ^ 2 + h ^ 2) - 1)) := by
      by_contra hlt
      have := deriv_smoothAbs_lt_one (show 0 < ε / 4 by positivity) (not_le.mp hlt)
      rw [← hX] at this
      linarith
    have hRtc : ballCutCentre ≤ Rt := ballCutSq_ge x
    have hDRt : Rt ≤ D := by
      have := ballHeightAbs_pos h
      linarith
    have h2ρ : Rt * D < 2 * ρ := by
      have hdiv : Rt < 2 * ρ / D := by
        have : ε / 4 > 0 := by positivity
        change ε / 4 ≤ 2 * ρ / D - (1 + (Rt - 1)) at hzone
        linarith
      rwa [lt_div_iff₀ hDpos] at hdiv
    have hρbig : 9 / 200 < ρ := by
      have : ballCutCentre * ballCutCentre ≤ Rt * D :=
        mul_le_mul hRtc (hRtc.trans hDRt) ballCutCentre_pos.le (hRtc.trans' ballCutCentre_pos.le)
      norm_num [ballCutCentre] at this
      linarith
    have hbcpos : 0 < bc := by
      have := neg_one_lt_deriv_smoothAbs ballCutWidth_pos (show -ballCutWidth < R - ballCutCentre by
        norm_num [ballCutWidth, ballCutCentre]
        linarith)
      rw [hbc]
      linarith
    have hc₁pos : 0 < c₁ := by rw [hc₁eq]; positivity
    rw [hX1]
    linarith

theorem ballRadius_strictMonoOn (hε : 0 < ε) (hε' : ε ≤ 1 / 8) (h : ℝ) :
    StrictMonoOn (fun ρ => ballRadius ε ρ h) (Ici 0) := by
  have hpair : Continuous (fun ρ : ℝ => (ρ ^ 2, h)) :=
    (continuous_pow 2).prodMk continuous_const
  have h0 := (contDiff_ballRatioSq hε hε').continuous.comp hpair
  have h1 : Continuous (fun ρ : ℝ => ballRatioSq ε (ρ ^ 2) h) := h0
  have hcont : Continuous (fun ρ => ballRadius ε ρ h) := by
    change Continuous (fun ρ : ℝ => ρ * ballRatioSq ε (ρ ^ 2) h)
    exact continuous_id.mul h1
  apply strictMonoOn_of_deriv_pos (convex_Ici 0) hcont.continuousOn
  intro ρ hρ
  rw [interior_Ici] at hρ
  obtain ⟨d, hd, hder⟩ := hasDerivAt_ballRadius hε hε' (show 0 < ρ from hρ) h
  rw [hder.deriv]
  exact hd

theorem ballRadius_zero (h : ℝ) : ballRadius ε 0 h = 0 := by
  rw [ballRadius, zero_mul]

theorem ballRadius_le_one (hε : 0 < ε) (hε' : ε ≤ 1 / 8) {ρ h : ℝ} (hρ : 0 ≤ ρ)
    (h1 : ρ ^ 2 + h ^ 2 ≤ 1) : ballRadius ε ρ h ≤ 1 := by
  rw [ballRadius_eq hε hε' hρ]
  refine (neckRadius_le_right hε _ _).trans ?_
  rw [add_sub_cancel]
  have hs : Real.sqrt (ρ ^ 2 + h ^ 2) ≤ 1 := by
    rw [Real.sqrt_le_one]
    exact h1
  rcases le_total (Real.sqrt (ρ ^ 2 + h ^ 2)) (ballCutCentre + ballCutWidth) with h2 | h2
  · have hm : max (Real.sqrt (ρ ^ 2 + h ^ 2)) ballCutCentre ≤ ballCutCentre + ballCutWidth :=
      max_le h2 (by norm_num [ballCutCentre, ballCutWidth])
    have := (ballCut_le (Real.sqrt (ρ ^ 2 + h ^ 2))).trans (add_le_add_left hm ballCutWidth)
    rw [ballCutSq]
    norm_num [ballCutCentre, ballCutWidth] at this ⊢
    linarith
  · rw [ballCutSq, ballCut_eq_self h2]
    exact hs

/-- In the cap regions the ball profile is the neck radius of the stereographic coordinates. -/
theorem ballRadius_eq_cap (hε : 0 < ε) (hε' : ε ≤ 1 / 8) {ρ h : ℝ} (hρ : 0 ≤ ρ)
    (hh : 1 / 4 ≤ |h|) (hR : ballCutCentre + ballCutWidth ≤ Real.sqrt (ρ ^ 2 + h ^ 2)) :
    ballRadius ε ρ h = neckRadius ε (2 * ρ / (Real.sqrt (ρ ^ 2 + h ^ 2) + |h|))
      (Real.sqrt (ρ ^ 2 + h ^ 2) - 1) := by
  rw [ballRadius_eq hε hε' hρ, ballDen, ballCutSq, ballCut_eq_self hR, ballHeightAbs_eq hh]

/-- Off the exact neck zone the ball profile is the radius. -/
theorem ballRadius_eq_radius (hε : 0 < ε) (hε' : ε ≤ 1 / 8) {ρ h : ℝ} (hρ : 0 ≤ ρ)
    (hR : ballCutCentre + ballCutWidth ≤ Real.sqrt (ρ ^ 2 + h ^ 2))
    (hz : Real.sqrt (ρ ^ 2 + h ^ 2) + ε / 4 ≤ 2 * ρ / ballDen (ρ ^ 2) h) :
    ballRadius ε ρ h = Real.sqrt (ρ ^ 2 + h ^ 2) := by
  rw [ballRadius_eq hε hε' hρ, ballCutSq, ballCut_eq_self hR, neckRadius_eq_right hε (by linarith)]
  ring

end GC.GraphManifold.Assembly
