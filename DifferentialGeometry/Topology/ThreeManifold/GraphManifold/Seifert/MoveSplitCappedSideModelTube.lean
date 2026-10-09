import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Seifert.MoveSplitCappedSideModelInj

/-!
# The tube inside the lift

Lane N2d, side model, step 4 (tube). On the polar part of the model the strip level of the point
`R u` (`R ≥ 2`) is `h` exactly when `u = exp (± hostTheta h)` (`eq_exp_of_level`,
`stripLevel_exp`); on the annulus part the model point is the strip point of its own level. Hence
every point of the tube at a level `|h| < 3` is the lift of a model point of level `h`
(`exists_liftMap_eq_tubeMap`), and conversely every model point of level `|h| < 3` lifts to a
point of the tube at level `h` (`exists_tubeMap_eq_liftMap`).
-/

set_option autoImplicit false

noncomputable section
open Set Function Metric Filter
open DifferentialGeometry DifferentialGeometry.Topology GC.Endpoint GC.GraphManifold
open scoped Manifold ContDiff Topology

universe u

local notation "S2" => Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1

namespace GC.Seifert.SplitTube

theorem circleSign_port_nonpos (l : Fin 3) (t : Bool) {w : ℂ} (hw : l.val ≠ 0 → w ≠ 0)
    (h : ‖w - (sideData l t).famC 3‖ ≤ (sideData l t).famR 3) :
    circleSign (sidePort l t) (hostChart l w) ≤ 0 := by
  rw [famC_three, famR_three] at h
  unfold sideData at h
  split_ifs at h with hl hp
  · simp only [zeroData] at h
    have hp0 : (sidePort l t).val ≠ 0 := by fin_cases l <;> cases t <;> simp_all [sidePort]
    have e : circleSign (sidePort l t) (hostChart l w) =
        ‖w - planarCenter 3 (sidePort l t)‖ - 1 / 2 := by
      simp only [circleSign, planarSign, planarRadius, hp0, ↓reduceIte, hostChart, hl, one_mul]
    rw [e]
    norm_num at h
    linarith
  · simp only [outerData] at h
    have hA2 : (planarCenter 3 (sidePort l t) - planarCenter 3 l) ^ 2 = 9 / 4 := by
      rw [← sq_abs, abs_sidePort_outer hl hp]; norm_num
    set A := planarCenter 3 (sidePort l t) - planarCenter 3 l with hAdef
    have hcl : planarCenter 3 l = -A := by
      rw [hAdef, planarCenter_zero hp]; ring
    have hw0 := hw hl
    have hA2c : (A : ℂ) ^ 2 = 9 / 4 := by
      have := congrArg (fun x : ℝ => (x : ℂ)) hA2
      push_cast at this
      exact this
    norm_num at h
    rw [hA2] at h
    norm_num at h
    try rw [hA2c] at h
    have hR : ‖w - ((-(4 / 27) * A : ℝ) : ℂ)‖ ≤ 4 / 9 := by
      convert (show ‖w - ((A / (9 / 4 - 9) : ℝ) : ℂ)‖ ≤ 4 / 9 by
        push_cast at h ⊢; linarith) using 4
      ring
    have hn : Complex.normSq (w - ((-(4 / 27) * A : ℝ) : ℂ)) ≤ (4 / 9) ^ 2 := by
      rw [← Complex.sq_norm]; exact pow_le_pow_left₀ (norm_nonneg _) hR 2
    rw [normSq_sub_ofReal] at hn
    have e : circleSign (sidePort l t) (hostChart l w) =
        3 - ‖((planarCenter 3 l : ℝ) : ℂ) + w⁻¹‖ := by
      simp only [circleSign, planarSign, planarRadius, hp, ↓reduceIte, hostChart, hl,
        planarCenter_zero hp, Complex.ofReal_zero, sub_zero]
      ring
    rw [e, hcl]
    have hns := Complex.normSq_nonneg w
    have := le_norm_add_inv_of (-A) 3 hw0 (by norm_num) (by rw [neg_sq, hA2]; nlinarith)
    push_cast at this ⊢
    linarith
  · simp only [innerData] at h
    have hA2 : (planarCenter 3 (sidePort l t) - planarCenter 3 l) ^ 2 = 9 := by
      rw [← sq_abs, abs_sidePort_inner hl hp]; norm_num
    set A := planarCenter 3 (sidePort l t) - planarCenter 3 l with hAdef
    have hw0 := hw hl
    have hA2c : (A : ℂ) ^ 2 = 9 := by
      have := congrArg (fun x : ℝ => (x : ℂ)) hA2
      push_cast at this
      exact this
    norm_num at h
    rw [hA2] at h
    norm_num at h
    try rw [hA2c] at h
    have hR : ‖w - (((4 / 35) * A : ℝ) : ℂ)‖ ≤ 2 / 35 := by
      convert (show ‖w - ((A / (9 - 1 / 4) : ℝ) : ℂ)‖ ≤ 2 / 35 by
        push_cast at h ⊢; linarith) using 4
      ring
    have hn : Complex.normSq (w - (((4 / 35) * A : ℝ) : ℂ)) ≤ (2 / 35) ^ 2 := by
      rw [← Complex.sq_norm]; exact pow_le_pow_left₀ (norm_nonneg _) hR 2
    rw [normSq_sub_ofReal] at hn
    have e : circleSign (sidePort l t) (hostChart l w) =
        ‖((-A : ℝ) : ℂ) + w⁻¹‖ - 1 / 2 := by
      simp only [circleSign, planarSign, planarRadius, hp, ↓reduceIte, hostChart, hl, one_mul]
      congr 2
      rw [hAdef]
      push_cast
      ring
    rw [e]
    have hns := Complex.normSq_nonneg w
    have := norm_add_inv_le_of (-A) (1 / 2) hw0 (by norm_num) (by rw [neg_sq, hA2]; nlinarith)
    linarith

theorem three_lt_of_inside_port (l : Fin 3) (t : Bool) {w : ℂ} (hw : l.val ≠ 0 → w ≠ 0)
    (h : ‖w - (sideData l t).famC 3‖ ≤ (sideData l t).famR 3) :
    3 < sgnR t * stripLevel l w := by
  have hz : hostChart l w ∈ outerCollarRegion (sidePort l t) := by
    change circleSign (sidePort l t) (hostChart l w) ≤ 1 / 8
    linarith [circleSign_port_nonpos l t hw h]
  have := (lt_sgnR_mul_stripLevel l t hz).2
  rwa [hostInv_hostChart] at this

theorem abs_stripCenter_le (l : Fin 3) : |stripCenter l| ≤ 1 / 4 := by
  unfold stripCenter
  split_ifs <;> norm_num

theorem stripLevel_of_one_le (l : Fin 3) {w : ℂ} (hw : 1 ≤ |w.im|) :
    stripLevel l w = -w.re / (tubeSlope * |w.im|) := by
  rw [stripLevel_eq, stripBump_of_one_le hw, stripWidth_of_one_le hw, mul_zero, zero_sub]

theorem strip_stripLevel (l : Fin 3) (w : ℂ) : strip l (w.im, stripLevel l w) = w :=
  (stripDiffeo l).right_inv w

theorem stripWidth_le_three_halves (Y : ℝ) (hY : |Y| ≤ 1) : stripWidth Y ≤ 3 / 2 := by
  have hB := stripBump_le_one Y
  have hY2 : Y ^ 2 ≤ 1 := by rw [← sq_abs]; nlinarith [abs_nonneg Y]
  rw [stripWidth]
  calc Real.sqrt (Y ^ 2 + stripBump Y) ≤ Real.sqrt ((3 / 2) ^ 2) :=
        Real.sqrt_le_sqrt (by linarith)
    _ = 3 / 2 := Real.sqrt_sq (by norm_num)

theorem abs_re_le_of_level {l : Fin 3} {w : ℂ} (hY : |w.im| ≤ 1) (hlev : |stripLevel l w| < 3) :
    |w.re| ≤ 1 / 4 + 9 / 2000 := by
  have hB0 := stripBump_nonneg w.im
  have hB1 := stripBump_le_one w.im
  have hW := stripWidth_pos w.im
  have hW2 := stripWidth_le_three_halves w.im hY
  have hden : 0 < tubeSlope * stripWidth w.im := mul_pos (by norm_num [tubeSlope]) hW
  rw [stripLevel_eq, abs_div, abs_of_pos hden, div_lt_iff₀ hden] at hlev
  have hc := abs_stripCenter_le l
  have hcB : |stripCenter l * stripBump w.im| ≤ 1 / 4 := by
    rw [abs_mul, abs_of_nonneg hB0]
    nlinarith [abs_nonneg (stripCenter l)]
  have hs : |w.re| ≤ |stripCenter l * stripBump w.im| +
      |stripCenter l * stripBump w.im - w.re| := by
    have := abs_sub (stripCenter l * stripBump w.im) (stripCenter l * stripBump w.im - w.re)
    simpa using this
  have ht : tubeSlope * stripWidth w.im ≤ 3 / 2000 := by
    rw [show tubeSlope = 1 / 1000 from rfl]
    linarith
  linarith

theorem one_le_abs_im_of_level {l : Fin 3} {w : ℂ} (hw : 2 ≤ ‖w‖)
    (hlev : |stripLevel l w| < 3) : 1 ≤ |w.im| := by
  by_contra hc
  push Not at hc
  have hX := abs_re_le_of_level hc.le hlev
  have h4 : 4 ≤ ‖w‖ ^ 2 := by nlinarith
  rw [Complex.sq_norm, Complex.normSq_apply] at h4
  have h1 := abs_lt.mp hc
  have h2 := abs_le.mp hX
  nlinarith

theorem angleScale_lt_two {h : ℝ} (hh : |h| < 3) : angleScale h < 2 := by
  have h1 := angleScale_sq h
  have h2 := angleScale_pos h
  have h3 : (tubeSlope * h) ^ 2 < 1 := by
    rw [show tubeSlope = 1 / 1000 from rfl, mul_pow, ← sq_abs h]
    nlinarith [abs_nonneg h]
  nlinarith

theorem eq_exp_of_level {l : Fin 3} {R : ℝ} (hR : 2 ≤ R) {u : Circle}
    (hlev : |stripLevel l ((R : ℂ) * (u : ℂ))| < 3) :
    u = Circle.exp (sgnR (decide (0 < (u : ℂ).im)) *
      hostTheta (stripLevel l ((R : ℂ) * (u : ℂ)))) := by
  set w : ℂ := (R : ℂ) * (u : ℂ) with hwdef
  set hl := stripLevel l w with hldef
  have hR0 : 0 < R := by linarith
  have hwn : ‖w‖ = R := by
    rw [hwdef, norm_mul, Circle.norm_coe, mul_one, Complex.norm_real,
      Real.norm_of_nonneg hR0.le]
  have hY := one_le_abs_im_of_level (l := l) (by rw [hwn]; exact hR) hlev
  have hre : w.re = R * (u : ℂ).re := by rw [hwdef, Complex.re_ofReal_mul]
  have him : w.im = R * (u : ℂ).im := by rw [hwdef, Complex.im_ofReal_mul]
  have hτ : (0 : ℝ) < tubeSlope := by norm_num [tubeSlope]
  have hYpos : 0 < |w.im| := by linarith
  have hlev' := stripLevel_of_one_le l hY
  rw [← hldef] at hlev'
  have hX : (u : ℂ).re = -(tubeSlope * hl) * |(u : ℂ).im| := by
    have e1 : w.re = -(hl * (tubeSlope * |w.im|)) := by
      rw [hlev']
      field_simp
    rw [hre, him, abs_mul, abs_of_pos hR0] at e1
    have : R * (u : ℂ).re = R * (-(tubeSlope * hl) * |(u : ℂ).im|) := by rw [e1]; ring
    exact mul_left_cancel₀ hR0.ne' this
  have hnorm : (u : ℂ).re ^ 2 + (u : ℂ).im ^ 2 = 1 := by
    have := Complex.normSq_apply (u : ℂ)
    rw [Circle.normSq_coe] at this
    nlinarith
  have hA2 := angleScale_sq hl
  have hA := angleScale_pos hl
  have hIm : |(u : ℂ).im| = 1 / angleScale hl := by
    rw [hX, mul_pow, sq_abs] at hnorm
    have e : (|(u : ℂ).im| * angleScale hl) ^ 2 = 1 := by
      rw [mul_pow, hA2, sq_abs]
      linear_combination hnorm
    have e2 : |(u : ℂ).im| * angleScale hl = 1 := by
      have hpos : 0 ≤ |(u : ℂ).im| * angleScale hl := mul_nonneg (abs_nonneg _) hA.le
      nlinarith [sq_nonneg (|(u : ℂ).im| * angleScale hl - 1)]
    field_simp
    linarith
  apply Circle.ext
  apply Complex.ext
  · rw [Circle.coe_exp, Complex.exp_ofReal_mul_I_re]
    have hc :
        Real.cos (sgnR (decide (0 < (u : ℂ).im)) * hostTheta hl) = Real.cos (hostTheta hl) := by
      rcases sgnR_eq (decide (0 < (u : ℂ).im)) with e | e <;> rw [e]
      · rw [one_mul]
      · rw [neg_one_mul, Real.cos_neg]
    rw [hc, cos_hostTheta, hX, hIm]
    ring
  · rw [Circle.coe_exp, Complex.exp_ofReal_mul_I_im]
    by_cases hpos : 0 < (u : ℂ).im
    · simp only [hpos, decide_true, sgnR, ↓reduceIte, one_mul]
      rw [sin_hostTheta, ← hIm, abs_of_pos hpos]
    · have hne : (u : ℂ).im ≠ 0 := by
        intro h0
        rw [h0, abs_zero] at hIm
        have : 0 < 1 / angleScale hl := by positivity
        linarith
      have hneg : (u : ℂ).im < 0 := lt_of_le_of_ne (not_lt.mp hpos) hne
      simp only [hpos, decide_false, sgnR, Bool.false_eq_true, ↓reduceIte, neg_one_mul,
        Real.sin_neg]
      rw [sin_hostTheta, ← hIm, abs_of_neg hneg, neg_neg]

theorem stripLevel_exp (l : Fin 3) {R : ℝ} (hR : 2 ≤ R) (s : Bool) {h : ℝ} (hh : |h| < 3) :
    stripLevel l ((R : ℂ) * (Circle.exp (sgnR s * hostTheta h) : ℂ)) = h ∧
      decide (0 < ((Circle.exp (sgnR s * hostTheta h) : Circle) : ℂ).im) = s := by
  have hA := angleScale_pos h
  have hA2 := angleScale_lt_two hh
  have hre : ((Circle.exp (sgnR s * hostTheta h) : Circle) : ℂ).re =
      -(tubeSlope * h) / angleScale h := by
    rw [Circle.coe_exp, Complex.exp_ofReal_mul_I_re, ← cos_hostTheta]
    rcases sgnR_eq s with e | e <;> rw [e]
    · rw [one_mul]
    · rw [neg_one_mul, Real.cos_neg]
  have him : ((Circle.exp (sgnR s * hostTheta h) : Circle) : ℂ).im = sgnR s / angleScale h := by
    rw [Circle.coe_exp, Complex.exp_ofReal_mul_I_im]
    rcases sgnR_eq s with e | e <;> rw [e]
    · rw [one_mul, sin_hostTheta]
    · rw [neg_one_mul, Real.sin_neg, sin_hostTheta]
      ring
  constructor
  · have hwim : ((R : ℂ) * (Circle.exp (sgnR s * hostTheta h) : ℂ)).im =
        R * (sgnR s / angleScale h) := by rw [Complex.im_ofReal_mul, him]
    have hwre : ((R : ℂ) * (Circle.exp (sgnR s * hostTheta h) : ℂ)).re =
        R * (-(tubeSlope * h) / angleScale h) := by rw [Complex.re_ofReal_mul, hre]
    have habs : |R * (sgnR s / angleScale h)| = R / angleScale h := by
      rw [abs_mul, abs_div, abs_of_pos hA, abs_of_pos (by linarith : (0 : ℝ) < R)]
      rcases sgnR_eq s with e | e <;> rw [e] <;> norm_num <;> rw [div_eq_mul_inv]
    have hY : 1 ≤ |((R : ℂ) * (Circle.exp (sgnR s * hostTheta h) : ℂ)).im| := by
      rw [hwim, habs, le_div_iff₀ hA]
      linarith
    rw [stripLevel_of_one_le l hY, hwim, hwre, habs]
    have hτ : tubeSlope ≠ 0 := by norm_num [tubeSlope]
    have hR0 : R ≠ 0 := by linarith
    field_simp
  · rw [him]
    rcases Bool.eq_false_or_eq_true s with e | e <;> subst e
    · simp only [sgnR, ↓reduceIte, decide_eq_true_eq]
      positivity
    · simp only [sgnR, Bool.false_eq_true, ↓reduceIte, decide_eq_false_iff_not, not_lt]
      rw [neg_div]
      exact neg_nonpos.mpr (by positivity)

theorem exp_zpow_eq_tubeFibre (e : ℤ) (s : Bool) (h : ℝ) :
    Circle.exp (sgnR s * hostTheta h) ^ e = tubeFibre e s h := by
  rw [circleExp_zpow, tubeFibre, sgnR]
  congr 1
  ring

theorem norm_eq_of_one_le_im (l : Fin 3) {w : ℂ} (hY : 1 ≤ |w.im|) :
    ‖w‖ = |w.im| * angleScale (stripLevel l w) := by
  have hlev := stripLevel_of_one_le l hY
  have hτ : tubeSlope ≠ 0 := by norm_num [tubeSlope]
  have hY0 : |w.im| ≠ 0 := by linarith
  have hre : w.re = -(tubeSlope * stripLevel l w) * |w.im| := by
    rw [hlev]
    field_simp
  have hA := angleScale_pos (stripLevel l w)
  have hA2 := angleScale_sq (stripLevel l w)
  have e : ‖w‖ ^ 2 = (|w.im| * angleScale (stripLevel l w)) ^ 2 := by
    rw [Complex.sq_norm, Complex.normSq_apply, mul_pow, hA2, hre]
    have h2 := sq_abs w.im
    linear_combination -h2
  exact (pow_left_inj₀ (norm_nonneg _) (by positivity) two_ne_zero).mp e

theorem two_le_hostRadius (l : ℕ) : 2 ≤ hostRadius l 0 := by
  unfold hostRadius
  split_ifs <;> norm_num

theorem norm_lt_of_level {l : Fin 3} {w : ℂ} (hlev : |stripLevel l w| < 3)
    (hY : 1 ≤ |w.im| → |w.im| * angleScale (stripLevel l w) < hostRadius l.val 0) :
    ‖w‖ < hostRadius l.val 0 := by
  by_cases h1 : 1 ≤ |w.im|
  · rw [norm_eq_of_one_le_im l h1]
    exact hY h1
  · push Not at h1
    have hX := abs_re_le_of_level h1.le hlev
    have h2 := two_le_hostRadius l.val
    have hn : ‖w‖ ^ 2 < 2 ^ 2 := by
      rw [Complex.sq_norm, Complex.normSq_apply]
      have a1 := abs_lt.mp h1
      have a2 := abs_le.mp hX
      nlinarith
    have := (pow_lt_pow_iff_left₀ (norm_nonneg w) (by norm_num) two_ne_zero).mp hn
    linarith

namespace SplitCharts

variable {M : Type*} [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
  (C : SplitCharts M)

theorem tubeMap_of_nonpos
    (hseam0 : ∀ τ : Torus, C.seam (τ, 0) = C.solid ((3 : ℝ) • (τ.1 : ℂ), τ.2))
    {p : S2} (h : ℝ) (hp : seamHeight (heightOf p) ≤ 0) :
    C.tubeMap (p, h) = C.solid ((6 : ℝ) • planeOf p, tubeFibre C.e₀ (side (p, h)) h) := by
  rcases hp.lt_or_eq with hneg | hzero
  · exact C.tubeMap_of_neg (q := (p, h)) hneg
  · rw [C.tubeMap_of_zero (q := (p, h)) hzero, seamModel_of_zero (q := (p, h)) hzero, hseam0]
    have hn : ‖planeOf p‖ = 1 / 2 := by
      have := latRadius_heightOf p
      rw [seamHeight] at hzero
      linarith
    congr 2
    change (3 : ℝ) • ((unitOf (planeOf p) : Circle) : ℂ) = (6 : ℝ) • planeOf p
    conv_rhs => rw [← norm_smul_unitOf (planeOf p), hn, smul_smul]
    norm_num

theorem tubeMap_of_pos' {p : S2} (h : ℝ) (hp : 0 < seamHeight (heightOf p)) :
    C.tubeMap (p, h) = C.hostMap (hostChart C.host (strip C.host
      (bandHeight C.host.val (heightOf p) / angleScale h, h)),
      unitOf (planeOf p) ^ C.e₁ * bandPhase C.e₀ C.d (heightOf p) h) :=
  C.tubeMap_of_pos (q := (p, h)) hp

end SplitCharts

end GC.Seifert.SplitTube

namespace GC.Seifert.ElementaryPresentation

open SplitTube

variable {Q : ConnectedClosedOrientedManifold.{u} 3} (E : ElementaryPresentation (NoCuts.carrier Q))
  {j : Fin E.toTorus.pairing.count} {b : Bool} (h : E.IsSplitSeam j b)

def sideLevel (t : Bool) (q : ℂ × Circle) : ℝ :=
  stripLevel (E.hostSide h) ((sideData (E.hostSide h) t).point (q.2, ‖q.1‖))

theorem sideDom_iff {t : Bool} {q : ℂ × Circle} :
    E.sideDom h t q ↔ ‖q.1‖ ≤ 3 ∧ -3 < sgnR t * E.sideLevel h t q :=
  Iff.rfl

theorem sideLevel_of_le (t : Bool) {q : ℂ × Circle} (h2 : ‖q.1‖ ≤ 2) :
    E.sideLevel h t q =
      stripLevel (E.hostSide h) ((vRadius (E.hostSide h) (2 * ‖q.1‖) : ℂ) * (q.2 : ℂ)) := by
  unfold sideLevel
  rw [(sideData (E.hostSide h) t).point_of_le_two (q := (q.2, ‖q.1‖)) h2]

theorem neg_three_lt_sgnR_mul {t : Bool} {x : ℝ} (hx : |x| < 3) : -3 < sgnR t * x := by
  have := abs_lt.mp hx
  rcases sgnR_eq t with e | e <;> rw [e] <;> linarith

theorem sgnR_mul_lt_three {t : Bool} {x : ℝ} (hx : |x| < 3) : sgnR t * x < 3 := by
  have := abs_lt.mp hx
  rcases sgnR_eq t with e | e <;> rw [e] <;> linarith

theorem sqrt_three_half_sq : (Real.sqrt 3 / 2) ^ 2 = 3 / 4 := by
  rw [div_pow, Real.sq_sqrt (by norm_num)]
  norm_num

theorem sqrt_three_half_lt_one : Real.sqrt 3 / 2 < 1 := by
  have h := sqrt_three_half_sq
  have h0 : 0 ≤ Real.sqrt 3 / 2 := by positivity
  nlinarith

theorem seamHeight_pos_of_lt {x : ℝ} (hx : |x| < Real.sqrt 3 / 2) : 0 < seamHeight x := by
  have h := sqrt_three_half_sq
  have hx2 : x ^ 2 < 3 / 4 := by
    rw [← h, ← sq_abs x]
    exact pow_lt_pow_left₀ hx (abs_nonneg x) two_ne_zero
  have hl : 1 / 2 < latRadius x := by
    rw [latRadius]
    exact (Real.lt_sqrt (by norm_num)).mpr (by linarith)
  unfold seamHeight
  linarith

theorem seamHeight_sqrt_three_half : seamHeight (Real.sqrt 3 / 2) = 0 := by
  have h := sqrt_three_half_sq
  have hl : latRadius (Real.sqrt 3 / 2) = 1 / 2 := by
    rw [latRadius, h, show (1 : ℝ) - 3 / 4 = (1 / 2) ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]
  rw [seamHeight, hl]
  norm_num

theorem seamHeight_neg_sqrt_three_half : seamHeight (-(Real.sqrt 3 / 2)) = 0 := by
  have h := sqrt_three_half_sq
  have hl : latRadius (-(Real.sqrt 3 / 2)) = 1 / 2 := by
    rw [latRadius, neg_sq, h, show (1 : ℝ) - 3 / 4 = (1 / 2) ^ 2 by norm_num,
      Real.sqrt_sq (by norm_num)]
  rw [seamHeight, hl]
  norm_num

theorem exists_bandHeight_eq (l : ℕ) {y : ℝ} (hy : |y| < hostRadius l 0) :
    ∃ x, |x| < Real.sqrt 3 / 2 ∧ bandHeight l x = y := by
  set r := Real.sqrt 3 / 2 with hr
  have hr1 := sqrt_three_half_lt_one
  have hr0 : 0 < r := by positivity
  have hc : ContinuousOn (bandHeight l) (Icc (-r) r) := fun x hx =>
    (contDiffAt_bandHeight l (abs_le.mpr ⟨by linarith [hx.1], by linarith [hx.2]⟩ |>.trans_lt
      hr1)).continuousAt.continuousWithinAt
  have hlo : bandHeight l (-r) = -hostRadius l 0 := by
    rw [bandHeight_of_le l (by linarith [show (1 / 2 : ℝ) < r by nlinarith [sqrt_three_half_sq]]),
      seamHeight_neg_sqrt_three_half]
  have hhi : bandHeight l r = hostRadius l 0 := by
    rw [bandHeight_of_ge l (by nlinarith [sqrt_three_half_sq]), seamHeight_sqrt_three_half]
  have hmem : y ∈ Ioo (bandHeight l (-r)) (bandHeight l r) := by
    rw [hlo, hhi]
    exact ⟨by linarith [(abs_lt.mp hy).1], (abs_lt.mp hy).2⟩
  obtain ⟨x, hx, hxe⟩ := intermediate_value_Ioo (by linarith) hc hmem
  exact ⟨x, abs_lt.mpr ⟨hx.1, hx.2⟩, hxe⟩

section Lift

variable (hlin : E.IsLinearSeam j)

theorem exists_tubeMap_eq_liftMap (t : Bool) {q : ℂ × Circle} (hq : E.sideDom h t q)
    (hlev : |E.sideLevel h t q| < 3) :
    ∃ p : S2, (E.splitCharts h hlin).tubeMap (p, E.sideLevel h t q) =
      (E.splitCharts h hlin).liftMap t q := by
  have he₁ := (E.splitCharts h hlin).he₁
  by_cases h32 : ‖q.1‖ ≤ 3 / 2
  · have hR : 2 ≤ vRadius (E.hostSide h) (2 * ‖q.1‖) :=
      two_le_vRadius _ (by positivity) (by linarith)
    rw [E.sideLevel_of_le h t (by linarith)] at hlev ⊢
    have hu := eq_exp_of_level hR hlev
    set s := decide (0 < ((q.2 : Circle) : ℂ).im)
    have hz : ‖(1 / 3 : ℝ) • q.1‖ < 1 := by
      rw [norm_smul, Real.norm_of_nonneg (by norm_num)]
      linarith
    refine ⟨capPoint s ((1 / 3 : ℝ) • q.1), ?_⟩
    have hsp : seamHeight (heightOf (capPoint s ((1 / 3 : ℝ) • q.1))) ≤ 0 := by
      rw [seamHeight, latRadius_heightOf, planeOf_capPoint s hz, norm_smul,
        Real.norm_of_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 3)]
      linarith
    rw [SplitCharts.tubeMap_of_nonpos _ (E.splitCharts_seam_zero h hlin) _ hsp,
      planeOf_capPoint s hz, SplitCharts.liftMap_of_le _ t h32]
    have hside : SplitCharts.side (capPoint s ((1 / 3 : ℝ) • q.1),
        stripLevel (E.hostSide h) ((vRadius (E.hostSide h) (2 * ‖q.1‖) : ℂ) * (q.2 : ℂ))) = s := by
      apply SplitCharts.side_eq_of_sgnR
      rw [heightOf_capPoint s hz, ← mul_assoc, sgnR_mul_self, one_mul]
      exact Real.sqrt_pos.mpr (by nlinarith [norm_nonneg ((1 / 3 : ℝ) • q.1)])
    rw [hside, ← exp_zpow_eq_tubeFibre, ← hu, smul_smul]
    unfold SplitCharts.liftV
    norm_num
  · push Not at h32
    set l := E.hostSide h with hl
    have hwn : ‖(sideData l t).point (q.2, ‖q.1‖)‖ < hostRadius l.val 0 :=
      (norm_point_le l t (q := (q.2, ‖q.1‖)) h32.le hq.1).2 h32
    have hY : |((sideData l t).point (q.2, ‖q.1‖)).im| * angleScale (E.sideLevel h t q) <
        hostRadius l.val 0 := by
      by_cases h1 : 1 ≤ |((sideData l t).point (q.2, ‖q.1‖)).im|
      · exact (norm_eq_of_one_le_im l h1).symm.trans_lt hwn
      · push Not at h1
        have hA := angleScale_lt_two hlev
        have h2 := two_le_hostRadius l.val
        nlinarith [abs_nonneg ((sideData l t).point (q.2, ‖q.1‖)).im, angleScale_pos
          (E.sideLevel h t q)]
    obtain ⟨x, hx, hxe⟩ := exists_bandHeight_eq l.val (y := ((sideData l t).point
      (q.2, ‖q.1‖)).im * angleScale (E.sideLevel h t q)) (by
        rw [abs_mul, abs_of_pos (angleScale_pos _)]
        exact hY)
    have hx1 : |x| < 1 := hx.trans sqrt_three_half_lt_one
    have hpos := seamHeight_pos_of_lt hx
    set φ : Circle := (E.liftFib h hlin q *
      (bandPhase (E.splitCharts h hlin).e₀ (E.splitCharts h hlin).d x
        (E.sideLevel h t q))⁻¹) ^ (E.splitCharts h hlin).e₁ with hφ
    refine ⟨bandPoint (x, φ), ?_⟩
    rw [SplitCharts.tubeMap_of_pos' _ _ (by rwa [heightOf_bandPoint hx1]),
      heightOf_bandPoint hx1, planeOf_bandPoint hx1, unitOf_smul (latRadius_pos hx1),
      hφ, zpow_zpow_unit he₁, inv_mul_cancel_right, SplitCharts.liftMap_of_gt _ t h32]
    change (E.splitCharts h hlin).hostMap (hostChart l (strip l (bandHeight l.val x /
      angleScale (E.sideLevel h t q), E.sideLevel h t q)), E.liftFib h hlin q) = _
    rw [hxe, mul_div_cancel_right₀ _ (angleScale_pos _).ne']
    unfold sideLevel
    rw [strip_stripLevel]
    rfl

theorem exists_liftMap_eq_tubeMap (t : Bool) (p : S2) {lv : ℝ} (hlv : |lv| < 3) :
    ∃ q : ℂ × Circle, E.sideDom h t q ∧ ‖q.1‖ < 3 ∧ E.sideLevel h t q = lv ∧
      (E.splitCharts h hlin).liftMap t q = (E.splitCharts h hlin).tubeMap (p, lv) := by
  have he₁ := (E.splitCharts h hlin).he₁
  have hε := neg_three_lt_sgnR_mul (t := t) hlv
  set l := E.hostSide h with hl
  by_cases hsp : seamHeight (heightOf p) ≤ 0
  · set s := SplitCharts.side (p, lv)
    have hpl : ‖planeOf p‖ ≤ 1 / 2 := by
      have := latRadius_heightOf p
      rw [seamHeight] at hsp
      linarith
    set ζ : ℂ := (3 : ℝ) • planeOf p with hζ
    have hζn : ‖ζ‖ ≤ 3 / 2 := by
      rw [hζ, norm_smul, Real.norm_of_nonneg (by norm_num : (0 : ℝ) ≤ 3)]
      linarith
    have hR : 2 ≤ vRadius l (2 * ‖ζ‖) := two_le_vRadius _ (by positivity) (by linarith)
    obtain ⟨hL, -⟩ := stripLevel_exp l hR s hlv
    have hlev : E.sideLevel h t (ζ, Circle.exp (sgnR s * hostTheta lv)) = lv := by
      rw [E.sideLevel_of_le h t (by dsimp only; linarith)]
      exact hL
    refine ⟨(ζ, Circle.exp (sgnR s * hostTheta lv)), ⟨by dsimp only; linarith, ?_⟩,
      by dsimp only; linarith, hlev, ?_⟩
    · change -3 < sgnR t * E.sideLevel h t _
      rw [hlev]
      exact hε
    · rw [SplitCharts.liftMap_of_le _ t hζn,
        SplitCharts.tubeMap_of_nonpos _ (E.splitCharts_seam_zero h hlin) lv hsp]
      unfold SplitCharts.liftV
      rw [exp_zpow_eq_tubeFibre, hζ, smul_smul]
      norm_num
      rfl
  · push Not at hsp
    have hx1 := abs_heightOf_lt_of_seamHeight_pos hsp
    obtain ⟨hmem, hne⟩ := hostChart_strip_mem l hx1 hsp hlv
    set w := strip l (bandHeight l.val (heightOf p) / angleScale lv, lv) with hw
    have hwl : stripLevel l w = lv := stripLevel_strip l _
    have hwn : ‖w‖ < hostRadius l.val 0 := by
      refine norm_lt_of_level (by rw [hwl]; exact hlv) fun _ => ?_
      rw [hwl]
      change |bandHeight l.val (heightOf p) / angleScale lv| * angleScale lv < _
      rw [abs_div, abs_of_pos (angleScale_pos lv), div_mul_cancel₀ _ (angleScale_pos lv).ne']
      exact abs_bandHeight_lt l.val hx1 hsp
    have hout : (sideData l t).famR 3 < ‖w - (sideData l t).famC 3‖ := by
      by_contra hc
      push Not at hc
      have := three_lt_of_inside_port l t hne hc
      rw [hwl] at this
      linarith [sgnR_mul_lt_three (t := t) hlv]
    have hv3 : vRadius l 3 = hostRadius l.val 0 := by
      rw [vRadius_of_two_le l (by norm_num)]
      norm_num
    have h0 : ‖w - (sideData l t).famC 0‖ ≤ (sideData l t).famR 0 := by
      rw [(sideData l t).famC_of_le (by norm_num), (sideData l t).famR_of_le (by norm_num),
        sub_zero, mul_zero]
      have := (strictAntiOn_vRadius l).antitoneOn (mem_Ici.mpr le_rfl)
        (mem_Ici.mpr (by norm_num : (0 : ℝ) ≤ 3)) (by norm_num : (0 : ℝ) ≤ 3)
      linarith
    obtain ⟨⟨u, ρ⟩, hρ, hpt⟩ := exists_nestedPoint_eq (μ := (sideData l t).famMu)
      (a := (sideData l t).famA) (sideData l t).continuousOn_famC
      (sideData l t).continuousOn_famR (fun _ hρ => (sideData l t).famR_pos hρ)
      (fun _ hρ => (sideData l t).famA_lt' hρ) h0 hout.le
    change (sideData l t).point (u, ρ) = w at hpt
    have hρ3 : ρ < 3 := by
      refine lt_of_le_of_ne hρ.2 fun he => ?_
      have := norm_nestedPoint_sub (c := (sideData l t).famC) (μ := (sideData l t).famMu)
        (a := (sideData l t).famA) (q := (u, ρ)) ((sideData l t).famR_pos hρ).le
      change ‖(sideData l t).point (u, ρ) - _‖ = _ at this
      rw [hpt] at this
      dsimp only at this
      rw [he] at this
      linarith
    have hρ32 : 3 / 2 < ρ := by
      by_contra hc
      push Not at hc
      have e := (sideData l t).point_of_le_two (q := (u, ρ)) (by dsimp only; linarith)
      rw [hpt] at e
      have hv : 2 ≤ vRadius l (2 * ρ) := two_le_vRadius l (by linarith [hρ.1]) (by linarith)
      have hn : ‖w‖ = vRadius l (2 * ρ) := by
        rw [e, norm_mul, Circle.norm_coe, mul_one, Complex.norm_real,
          Real.norm_of_nonneg (by linarith)]
      have := (strictAntiOn_vRadius l).antitoneOn (mem_Ici.mpr (by linarith [hρ.1]))
        (mem_Ici.mpr (by norm_num : (0 : ℝ) ≤ 3)) (by linarith : 2 * ρ ≤ 3)
      linarith
    have hρ0 : 0 < ρ := by linarith
    set X : Circle := unitOf (planeOf p) ^ (E.splitCharts h hlin).e₁ *
      bandPhase (E.splitCharts h hlin).e₀ (E.splitCharts h hlin).d (heightOf p) lv with hX
    set φ : Circle := (X * (u ^ ((E.splitCharts h hlin).e₀ * (E.splitCharts h hlin).d))⁻¹) ^
      (E.splitCharts h hlin).e₁ with hφ
    set ζ : ℂ := (ρ : ℝ) • (φ : ℂ) with hζ
    have hζn : ‖ζ‖ = ρ := by
      rw [hζ, norm_smul, Circle.norm_coe, mul_one, Real.norm_of_nonneg hρ0.le]
    have hζu : unitOf ζ = φ := unitOf_smul hρ0 φ
    have hpt' : (sideData l t).point (u, ‖ζ‖) = w := by rw [hζn]; exact hpt
    have hlev : E.sideLevel h t (ζ, u) = lv := by
      change stripLevel l ((sideData l t).point (u, ‖ζ‖)) = lv
      rw [hpt', hwl]
    refine ⟨(ζ, u), ⟨by dsimp only; linarith, ?_⟩, by dsimp only; linarith, hlev, ?_⟩
    · change -3 < sgnR t * E.sideLevel h t _
      rw [hlev]
      exact hε
    · rw [SplitCharts.liftMap_of_gt _ t (by dsimp only; linarith),
        SplitCharts.tubeMap_of_pos' _ lv hsp]
      unfold SplitCharts.liftH
      dsimp only
      change (E.splitCharts h hlin).hostMap (hostChart l ((sideData l t).point (u, ‖ζ‖)),
        u ^ ((E.splitCharts h hlin).e₀ * (E.splitCharts h hlin).d) * unitOf ζ ^
          (E.splitCharts h hlin).e₁) = (E.splitCharts h hlin).hostMap (hostChart l w, X)
      rw [hpt', hζu, hφ, zpow_zpow_unit he₁, mul_comm X, mul_inv_cancel_left]

end Lift

end GC.Seifert.ElementaryPresentation
