import
  DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Seifert.ClosedTriangleGeometryFlatScrews
import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Seifert.CompactFoldHypDisc

/-!
# The disc base chart of the hyperbolic connection models and their screws

Lane B3c (design `docs/geometrization/handoffs/20261004-design-b3c-hyperbolic-rows.md`, §1–2).
For the connection models `H² × ℝ` and `SL₂~` (`hyperbolicProfile l`, `l = 0, 1`) the plane
coordinates of `ModelCoordinates` are the projection of the hyperboloid; the base coordinate
`hb x = hypDisc (planeOf x)`, `hypDisc p = p/(1 + √(1 + |p|²))`, is the Poincaré disc of CF's
`ε = 1` chart, a smooth map onto the unit disc with inverse `hypDiscInv w = 2w/(1 - |w|²)`
(`hypDiscInv_hypDisc`, `hypDisc_hypDiscInv`) and injective derivative
(`det_fderiv_hypDisc_ne_zero`), commuting with `conj` and with rotations about the axis.
In upper half-plane coordinates `Z = X + i e^y` of `hyperboloidMap l (X, y, τ)` it is the Cayley
map `cay Z = (iZ + 1)/(Z + i)` (`hb_hyperboloidMap`), X14's recentring acts by `Z ↦ aZ + b`
with `a > 0` (`hb_recentre`), and for every such affine map the disc coordinate centred at the
image of `i` is a rotation, `disc (cay (b + ai)) (cay (aZ + b)) = u · cay Z`, `|u| = 1`
(`mob_cay_affine`, `norm_mobUnit`). Hence the unimodular rotation part of `recentre` cancels in
a screw: in the Möbius coordinate centred at `hb v` the screw `screwAt v p q ℓ` is the rotation
by `e^{-2πi/p}` (`mob_hb_screwAt`), for both hyperbolic models and every `v`. For `H² × ℝ` the
fibre coordinate drops by `ℓ q/p` (`screwAt_hyperbolicProduct_two`). The point
`hypVertex w = ofPlane (hypDiscInv w) 0` has base coordinate `w` (`hb_hypVertex`).
-/

set_option autoImplicit false

noncomputable section

open Complex
open scoped ComplexConjugate ContDiff

namespace GC.Seifert

namespace ClosedTriangle

namespace Hyp

open GC.Geometry

def hypDisc (p : ℂ) : ℂ := p / ((1 + Real.sqrt (1 + normSq p) : ℝ) : ℂ)

def cay (Z : ℂ) : ℂ := (I * Z + 1) / (Z + I)

def hb (x : ModelCoordinates) : ℂ := hypDisc (planeOf x)

theorem normSq_planeOf (x : ModelCoordinates) : normSq (planeOf x) = x 0 ^ 2 + x 1 ^ 2 := by
  rw [normSq_apply, planeOf_re, planeOf_im]
  ring

theorem cay_alg (X E E' : ℝ) (hEE : E * E' = 1) :
    ((X * E' : ℝ) + ((X ^ 2 * E' / 2 + (E - E') / 2 : ℝ) : ℂ) * I) * ((X : ℂ) + I * E + I) =
      (I * ((X : ℂ) + I * E) + 1) * ((1 + (X ^ 2 * E' / 2 + (E + E') / 2) : ℝ) : ℂ) := by
  apply Complex.ext <;>
    simp only [mul_re, mul_im, add_re, add_im, ofReal_re, ofReal_im, I_re, I_im, one_re,
      one_im] <;> ring_nf
  · linear_combination hEE
  · linear_combination X * hEE

theorem hb_hyperboloidMap (l : ℝ) (g : ModelCoordinates) :
    hb (hyperboloidMap l g) = cay ((g 0 : ℂ) + I * (Real.exp (g 1) : ℂ)) := by
  have hH := hyperboloidHeight_hyperboloidMap l g
  have hsq : Real.sqrt (1 + normSq (planeOf (hyperboloidMap l g))) =
      g 0 ^ 2 * Real.exp (-g 1) / 2 + (Real.exp (g 1) + Real.exp (-g 1)) / 2 := by
    rw [← hH, hyperboloidHeight, normSq_planeOf]
    congr 1
    ring
  have h0 : hyperboloidMap l g 0 = g 0 * Real.exp (-g 1) := by simp [hyperboloidMap]
  have h1 : hyperboloidMap l g 1 =
      g 0 ^ 2 * Real.exp (-g 1) / 2 + (Real.exp (g 1) - Real.exp (-g 1)) / 2 := by
    simp [hyperboloidMap]
  have hEE : Real.exp (g 1) * Real.exp (-g 1) = 1 := by
    rw [← Real.exp_add, add_neg_cancel, Real.exp_zero]
  have hE := Real.exp_pos (g 1)
  have hE' := Real.exp_pos (-g 1)
  unfold hb hypDisc cay
  rw [hsq]
  have hden : (g 0 : ℂ) + I * (Real.exp (g 1) : ℂ) + I ≠ 0 := by
    intro h
    have := congrArg Complex.im h
    simp only [add_im, ofReal_im, mul_im, I_re, I_im, ofReal_re, zero_mul, one_mul, zero_add,
      zero_im] at this
    linarith
  have hD : (((1 + (g 0 ^ 2 * Real.exp (-g 1) / 2 + (Real.exp (g 1) + Real.exp (-g 1)) / 2)) :
      ℝ) : ℂ) ≠ 0 := by
    have : 0 < 1 + (g 0 ^ 2 * Real.exp (-g 1) / 2 + (Real.exp (g 1) + Real.exp (-g 1)) / 2) := by
      positivity
    exact ofReal_ne_zero.mpr this.ne'
  rw [div_eq_div_iff hD hden]
  have hp : planeOf (hyperboloidMap l g) = ((g 0 * Real.exp (-g 1) : ℝ) : ℂ) +
      ((g 0 ^ 2 * Real.exp (-g 1) / 2 + (Real.exp (g 1) - Real.exp (-g 1)) / 2 : ℝ) : ℂ) *
        I := by
    rw [planeOf, h0, h1]
  rw [hp]
  exact cay_alg (g 0) (Real.exp (g 1)) (Real.exp (-g 1)) hEE

theorem ne_zero_of_im_pos {w : ℂ} (h : 0 < w.im) : w ≠ 0 := by
  intro h0; rw [h0, zero_im] at h; exact lt_irrefl _ h

theorem add_I_ne_zero {Z : ℂ} (hZ : 0 < Z.im) : Z + I ≠ 0 := by
  apply ne_zero_of_im_pos
  simp only [add_im, I_im]; linarith

theorem conj_sub_I_ne_zero {Z : ℂ} (hZ : 0 < Z.im) : conj Z - I ≠ 0 := by
  intro h
  have := congrArg Complex.im h
  simp only [sub_im, conj_im, I_im, zero_im] at this
  linarith

theorem conj_cay (V : ℂ) : conj (cay V) = (1 - I * conj V) / (conj V - I) := by
  unfold cay
  rw [map_div₀]
  congr 1
  · simp only [map_add, map_mul, conj_I, map_one]; ring
  · simp only [map_add, conj_I]; ring

theorem cay_sub_cay {V W : ℂ} (hV : V + I ≠ 0) (hW : W + I ≠ 0) :
    cay W - cay V = -2 * (W - V) / ((W + I) * (V + I)) := by
  unfold cay
  rw [div_sub_div _ _ hW hV]
  congr 1
  linear_combination (W - V) * I_sq

theorem one_sub_conj_cay_mul {V W : ℂ} (hV : conj V - I ≠ 0) (hW : W + I ≠ 0) :
    1 - conj (cay V) * cay W = -2 * I * (W - conj V) / ((conj V - I) * (W + I)) := by
  rw [conj_cay]
  unfold cay
  rw [div_mul_div_comm, one_sub_div (mul_ne_zero hV hW)]
  congr 1
  linear_combination (conj V * W - 1) * I_sq

theorem mob_cay_cay {V W : ℂ} (hV : V + I ≠ 0) (hV' : conj V - I ≠ 0) (hW : W + I ≠ 0)
    (hWV : W - conj V ≠ 0) :
    HypFold.mob (cay V) (cay W) = (W - V) * (conj V - I) / (I * (W - conj V) * (V + I)) := by
  unfold HypFold.mob
  rw [cay_sub_cay hV hW, one_sub_conj_cay_mul hV' hW, div_div_div_eq,
    div_eq_div_iff (mul_ne_zero (mul_ne_zero hW hV)
      (mul_ne_zero (mul_ne_zero (by norm_num) I_ne_zero) hWV))
      (mul_ne_zero (mul_ne_zero I_ne_zero hWV) hV)]
  ring

def mobUnit (V : ℂ) : ℂ := (conj V - I) / (-(V + I))

theorem mob_cay_affine {a : ℝ} (b : ℝ) (ha : 0 < a) {Z : ℂ} (hZ : 0 < Z.im) :
    HypFold.mob (cay (b + a * I)) (cay (a * Z + b)) = mobUnit (b + a * I) * cay Z := by
  set V : ℂ := b + a * I with hVdef
  have hVim : 0 < V.im := by simp [hVdef, ha]
  have hV := add_I_ne_zero hVim
  have hV' := conj_sub_I_ne_zero hVim
  have hWim : 0 < ((a : ℂ) * Z + b).im := by
    simp only [add_im, mul_im, ofReal_re, ofReal_im, zero_mul, add_zero]; positivity
  have hW := add_I_ne_zero hWim
  have hZI := add_I_ne_zero hZ
  have hcV : conj V = b - a * I := by simp [hVdef]; ring
  have hWV : (a : ℂ) * Z + b - conj V = a * (Z + I) := by rw [hcV]; ring
  have ha' : (a : ℂ) ≠ 0 := ofReal_ne_zero.mpr ha.ne'
  have hWV0 : (a : ℂ) * Z + b - conj V ≠ 0 := by rw [hWV]; exact mul_ne_zero ha' hZI
  rw [mob_cay_cay hV hV' hW hWV0, hWV]
  have hWV2 : (a : ℂ) * Z + b - V = a * (Z - I) := by rw [hVdef]; ring
  rw [hWV2]
  unfold mobUnit cay
  rw [div_mul_div_comm, div_eq_div_iff (mul_ne_zero (mul_ne_zero I_ne_zero
    (mul_ne_zero ha' hZI)) hV) (mul_ne_zero (neg_ne_zero.mpr hV) hZI)]
  linear_combination (-(a * (conj V - I) * (V + I) * (Z + I) * Z)) * I_sq

theorem norm_mobUnit {V : ℂ} (hV : V + I ≠ 0) : ‖mobUnit V‖ = 1 := by
  unfold mobUnit
  have h : conj V - I = conj (V + I) := by simp only [map_add, conj_I]; ring
  rw [norm_div, norm_neg, h, norm_conj, div_self (norm_ne_zero_iff.mpr hV)]

theorem hyperboloidInv_zero (l : ℝ) : hyperboloidInv l 0 = 0 := by
  ext i
  fin_cases i <;> simp [hyperboloidInv, hyperboloidHeight]

def uhp (x : ModelCoordinates) : ℂ :=
  (hyperboloidInv 0 x 0 : ℂ) + I * (Real.exp (hyperboloidInv 0 x 1) : ℂ)

theorem hyperboloidInv_base (l : ℝ) (x : ModelCoordinates) :
    hyperboloidInv l x 0 = hyperboloidInv 0 x 0 ∧
      hyperboloidInv l x 1 = hyperboloidInv 0 x 1 := by
  constructor <;> simp [hyperboloidInv]

theorem hb_eq_cay_uhp (l : ℝ) (x : ModelCoordinates) : hb x = cay (uhp x) := by
  conv_lhs => rw [← hyperboloidMap_hyperboloidInv l x]
  rw [hb_hyperboloidMap, uhp, (hyperboloidInv_base l x).1, (hyperboloidInv_base l x).2]

theorem uhp_im_pos (x : ModelCoordinates) : 0 < (uhp x).im := by
  simp only [uhp, add_im, ofReal_im, mul_im, I_re, I_im, ofReal_re, zero_mul, one_mul, zero_add]
  exact Real.exp_pos _

def hypShiftA (v : ModelCoordinates) : ℝ := Real.exp (hyperboloidInv 0 v 1)

def hypShiftB (v : ModelCoordinates) : ℝ := hyperboloidInv 0 v 0

theorem uhp_eq_shift (v : ModelCoordinates) : uhp v = hypShiftB v + hypShiftA v * I := by
  rw [uhp, hypShiftA, hypShiftB]
  push_cast
  ring

theorem hb_hyperboloidMap_shift (k : CoordinateModel)
    (hk : k = .hyperbolicProduct ∨ k = .universalSL2) (l : ℝ) (v x : ModelCoordinates) :
    hb (hyperboloidMap l (coordinateShift k (hyperboloidInv l 0) (hyperboloidInv l v)
      (hyperboloidInv l x))) = cay (hypShiftA v * uhp x + hypShiftB v) := by
  rw [hb_hyperboloidMap, hyperboloidInv_zero]
  congr 1
  have h0 := hyperboloidInv_base l v
  have h1 := hyperboloidInv_base l x
  rcases hk with rfl | rfl <;>
  · simp only [coordinateShift, coordinateShiftLinear, PiLp.add_apply, sub_zero]
    simp [h0.1, h0.2, h1.1, h1.2, uhp, hypShiftA, hypShiftB, Real.exp_add]
    ring

theorem recentre_hyperbolicProduct_apply
    (hm : ConnectionModel.hyperbolicProduct.baseCurvature ≤ 0) (v x : ModelCoordinates) :
    recentre .hyperbolicProduct hm v x = hyperboloidMap 0 (coordinateShift .hyperbolicProduct
      (hyperboloidInv 0 0) (hyperboloidInv 0 v) (hyperboloidInv 0 x)) := rfl

theorem recentre_universalSL2_apply (hm : ConnectionModel.universalSL2.baseCurvature ≤ 0)
    (v x : ModelCoordinates) :
    recentre .universalSL2 hm v x = hyperboloidMap 1 (coordinateShift .universalSL2
      (hyperboloidInv 1 0) (hyperboloidInv 1 v) (hyperboloidInv 1 x)) := rfl

theorem recentre_symm_hyperbolicProduct_apply
    (hm : ConnectionModel.hyperbolicProduct.baseCurvature ≤ 0) (v x : ModelCoordinates) :
    (recentre .hyperbolicProduct hm v).symm x = hyperboloidMap 0 (coordinateShift
      .hyperbolicProduct (hyperboloidInv 0 v) (hyperboloidInv 0 0) (hyperboloidInv 0 x)) := rfl

theorem hb_recentre (m : ConnectionModel) (hm : m.baseCurvature ≤ 0)
    (hmm : m = .hyperbolicProduct ∨ m = .universalSL2) (v x : ModelCoordinates) :
    hb (recentre m hm v x) = cay (hypShiftA v * uhp x + hypShiftB v) := by
  rcases hmm with rfl | rfl
  · rw [recentre_hyperbolicProduct_apply]
    exact hb_hyperboloidMap_shift _ (Or.inl rfl) 0 v x
  · rw [recentre_universalSL2_apply]
    exact hb_hyperboloidMap_shift _ (Or.inr rfl) 1 v x

theorem mob_hb_recentre (m : ConnectionModel) (hm : m.baseCurvature ≤ 0)
    (hmm : m = .hyperbolicProduct ∨ m = .universalSL2) (v x : ModelCoordinates) :
    HypFold.mob (hb v) (hb (recentre m hm v x)) = mobUnit (uhp v) * hb x := by
  rw [hb_recentre m hm hmm, hb_eq_cay_uhp 0 v, hb_eq_cay_uhp 0 x, uhp_eq_shift v]
  exact mob_cay_affine _ (Real.exp_pos _) (uhp_im_pos x)

theorem hypDisc_mul_circle (θ : ℝ) (p : ℂ) :
    hypDisc ((Circle.exp θ : ℂ) * p) = (Circle.exp θ : ℂ) * hypDisc p := by
  unfold hypDisc
  rw [normSq_mul, Complex.normSq_eq_norm_sq (Circle.exp θ : ℂ), Circle.norm_coe]
  rw [one_pow, one_mul, mul_div_assoc]

theorem hb_screwDiffeomorph (θ s : ℝ) (y : ModelCoordinates) :
    hb (screwDiffeomorph θ s y) = (Circle.exp θ : ℂ) * hb y := by
  rw [hb, screwDiffeomorph_apply', planeOf_add_fibreShift, planeOf_planeRotation,
    hypDisc_mul_circle]
  rfl

theorem mob_hb_screwAt (m : ConnectionModel) (hm : m.baseCurvature ≤ 0)
    (hmm : m = .hyperbolicProduct ∨ m = .universalSL2) (v : ModelCoordinates) (p : ℕ+) (q : ℤ)
    (ℓ : ℝ) (x : ModelCoordinates) :
    HypFold.mob (hb v) (hb (screwAt m hm v p q ℓ x)) =
      (Circle.exp (-2 * Real.pi / p) : ℂ) * HypFold.mob (hb v) (hb x) := by
  change HypFold.mob (hb v) (hb (recentre m hm v (screwDiffeomorph (-2 * Real.pi / p)
    (-ℓ * q / p) ((recentre m hm v).symm x)))) = _
  rw [mob_hb_recentre m hm hmm, hb_screwDiffeomorph]
  conv_rhs => rw [← (recentre m hm v).apply_symm_apply x]
  rw [mob_hb_recentre m hm hmm]
  ring

theorem screwAt_hyperbolicProduct_two (hm : ConnectionModel.hyperbolicProduct.baseCurvature ≤ 0)
    (v : ModelCoordinates) (p : ℕ+) (q : ℤ) (ℓ : ℝ) (x : ModelCoordinates) :
    screwAt .hyperbolicProduct hm v p q ℓ x 2 = x 2 - ℓ * q / p := by
  change recentre .hyperbolicProduct hm v (screwDiffeomorph (-2 * Real.pi / p)
    (-ℓ * q / p) ((recentre .hyperbolicProduct hm v).symm x)) 2 = _
  rw [recentre_hyperbolicProduct_apply, screwDiffeomorph_apply',
    recentre_symm_hyperbolicProduct_apply]
  simp [hyperboloidMap, hyperboloidInv, coordinateShift, coordinateShiftLinear, fibreShift]
  ring

def hypDiscInv (w : ℂ) : ℂ := 2 * w / ((1 - normSq w : ℝ) : ℂ)

theorem hypDisc_hypDiscInv {w : ℂ} (hw : ‖w‖ < 1) : hypDisc (hypDiscInv w) = w := by
  have hn : normSq w < 1 := by
    rw [normSq_eq_norm_sq]; nlinarith [norm_nonneg w]
  have h1 : 0 < 1 - normSq w := by linarith
  have h0 := normSq_nonneg w
  have hs : Real.sqrt (1 + normSq (hypDiscInv w)) = (1 + normSq w) / (1 - normSq w) := by
    rw [Real.sqrt_eq_iff_mul_self_eq (by linarith [normSq_nonneg (hypDiscInv w)])
      (div_nonneg (by linarith) h1.le)]
    unfold hypDiscInv
    rw [normSq_div, normSq_mul, normSq_ofReal]
    have : normSq (2 : ℂ) = 4 := by norm_num [normSq_apply]
    rw [this]
    field_simp
    ring
  have e : (1 + (1 + normSq w) / (1 - normSq w) : ℝ) = 2 / (1 - normSq w) := by
    field_simp
    ring
  unfold hypDisc
  rw [hs, e]
  unfold hypDiscInv
  have hne : (1 : ℂ) - (normSq w : ℂ) ≠ 0 := by
    have : ((1 - normSq w : ℝ) : ℂ) ≠ 0 := ofReal_ne_zero.mpr h1.ne'
    simpa using this
  push_cast
  field_simp

def hypVertex (w : ℂ) : ModelCoordinates := ofPlane (hypDiscInv w) 0

theorem hb_hypVertex {w : ℂ} (hw : ‖w‖ < 1) : hb (hypVertex w) = w := by
  rw [hb, hypVertex, planeOf_ofPlane, hypDisc_hypDiscInv hw]

theorem one_add_sqrt_pos (p : ℂ) : 0 < 1 + Real.sqrt (1 + normSq p) := by positivity

theorem hypDisc_eq_smul (p : ℂ) : hypDisc p = (1 + Real.sqrt (1 + normSq p))⁻¹ • p := by
  rw [hypDisc, Complex.real_smul, div_eq_inv_mul, ofReal_inv]

theorem norm_hypDisc_lt_one (p : ℂ) : ‖hypDisc p‖ < 1 := by
  have hs : ‖p‖ < Real.sqrt (1 + normSq p) := by
    rw [normSq_eq_norm_sq]
    exact Real.lt_sqrt_of_sq_lt (by linarith)
  rw [hypDisc, norm_div, norm_real, Real.norm_of_nonneg (one_add_sqrt_pos p).le,
    div_lt_one (one_add_sqrt_pos p)]
  linarith

theorem hypDisc_conj (p : ℂ) : hypDisc (conj p) = conj (hypDisc p) := by
  rw [hypDisc, hypDisc, map_div₀, conj_ofReal, normSq_conj]

theorem normSq_hypDisc (p : ℂ) :
    normSq (hypDisc p) = normSq p / (1 + Real.sqrt (1 + normSq p)) ^ 2 := by
  rw [hypDisc, normSq_div, normSq_ofReal, sq]

theorem hypDiscInv_hypDisc (p : ℂ) : hypDiscInv (hypDisc p) = p := by
  have hd := one_add_sqrt_pos p
  have hn := normSq_nonneg p
  have hs := Real.sq_sqrt (show 0 ≤ 1 + normSq p by linarith)
  have e : 1 - normSq (hypDisc p) = 2 / (1 + Real.sqrt (1 + normSq p)) := by
    rw [normSq_hypDisc]
    field_simp
    nlinarith [hs]
  unfold hypDiscInv
  rw [e, hypDisc]
  have hd' : ((1 + Real.sqrt (1 + normSq p) : ℝ) : ℂ) ≠ 0 := ofReal_ne_zero.mpr hd.ne'
  push_cast
  push_cast at hd'
  field_simp

theorem contDiff_normSq : ContDiff ℝ ∞ (fun u : ℂ => normSq u) := by
  have : (fun u : ℂ => normSq u) = fun u => u.re * u.re + u.im * u.im := by
    funext u; rw [normSq_apply]
  rw [this]
  exact (reCLM.contDiff.mul reCLM.contDiff).add (imCLM.contDiff.mul imCLM.contDiff)

theorem contDiff_hypDisc : ContDiff ℝ ∞ hypDisc := by
  have hf : ContDiff ℝ ∞ (fun p : ℂ => (1 + Real.sqrt (1 + normSq p))⁻¹) := by
    refine ContDiff.inv (contDiff_const.add (ContDiff.sqrt (contDiff_const.add contDiff_normSq)
      fun p => ?_)) fun p => (one_add_sqrt_pos p).ne'
    have := normSq_nonneg p
    positivity
  have : hypDisc = fun p => (1 + Real.sqrt (1 + normSq p))⁻¹ • p := funext hypDisc_eq_smul
  rw [this]
  exact hf.smul contDiff_id

theorem hypDiscInv_eq_smul (w : ℂ) : hypDiscInv w = (2 / (1 - normSq w)) • w := by
  rw [hypDiscInv, Complex.real_smul]
  push_cast
  ring

theorem contDiffAt_hypDiscInv {w : ℂ} (hw : normSq w ≠ 1) :
    ContDiffAt ℝ ∞ hypDiscInv w := by
  have : hypDiscInv = fun w => (2 / (1 - normSq w)) • w := funext hypDiscInv_eq_smul
  rw [this]
  exact (contDiffAt_const.div (contDiffAt_const.sub contDiff_normSq.contDiffAt)
    (sub_ne_zero.mpr (Ne.symm hw))).smul contDiffAt_id

theorem normSq_hypDisc_lt_one (p : ℂ) : normSq (hypDisc p) < 1 := by
  rw [normSq_eq_norm_sq]
  have := norm_hypDisc_lt_one p
  nlinarith [norm_nonneg (hypDisc p)]

theorem fderiv_hypDisc_injective (p : ℂ) : Function.Injective (fderiv ℝ hypDisc p) := by
  have h1 : HasFDerivAt hypDisc (fderiv ℝ hypDisc p) p :=
    (contDiff_hypDisc.differentiable (by simp)).differentiableAt.hasFDerivAt
  have h2 : HasFDerivAt hypDiscInv (fderiv ℝ hypDiscInv (hypDisc p)) (hypDisc p) :=
    ((contDiffAt_hypDiscInv (normSq_hypDisc_lt_one p).ne).differentiableAt
      (by simp)).hasFDerivAt
  have hc := h2.comp p h1
  have hid : (hypDiscInv ∘ hypDisc) = id := funext hypDiscInv_hypDisc
  rw [hid] at hc
  have heq := hc.unique (hasFDerivAt_id p)
  intro u v huv
  have := congrArg (fun L : ℂ →L[ℝ] ℂ => L u) heq
  have h' := congrArg (fun L : ℂ →L[ℝ] ℂ => L v) heq
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.id_apply] at this h'
  rw [← this, ← h', huv]

theorem det_fderiv_hypDisc_ne_zero (p : ℂ) : (fderiv ℝ hypDisc p).det ≠ 0 := by
  have hk : LinearMap.ker (fderiv ℝ hypDisc p : ℂ →ₗ[ℝ] ℂ) = ⊥ :=
    LinearMap.ker_eq_bot.2 (fderiv_hypDisc_injective p)
  have hu := (LinearMap.isUnit_iff_ker_eq_bot _).2 hk
  exact ((LinearMap.isUnit_iff_isUnit_det _).1 hu).ne_zero

end Hyp

end ClosedTriangle

end GC.Seifert
