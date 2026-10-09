import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Seifert.MobiusBlock

/-!
# The Möbius circle bundle as a Seifert block over `D²(2, 2)`

Packet RG02, part 3, item (c), continuing `Seifert/MobiusBlock.lean` on
`mobiusBundleCarrier ⊆ L(4, -1)`; `J` is the base map `mobiusBundleBase`, `c_j = ±3/2`.

Solid-torus charts. For `(w₁, w₂)` with `w₂ ≠ 0` the pair
`holeChartPoint = (w₁ / conj w₂ · √‖S‖, w₂⁴ / S)`, `S = holeSum = 27 + 18 J`, is invariant
under the deck group and descends to `holeChart`; `solidChart = (z, unitOf w)` is a smooth left
inverse of `solidFoldPlus` (`solidChart_solidSection`). Since `w₁ / conj w₂` and `unitOf (w₂⁴)`
determine a deck orbit off `w₂ = 0` (`exists_lensUnit_of_ratio`), it is also a right inverse on
`‖J - 3/2‖ ≤ 1/2` (`solidFoldPlus_chart`); the swap of `w₁, w₂` gives the same for
`solidFoldMinus` on `‖J + 3/2‖ ≤ 1/2`. So both folds are injective with bijective differential
(`mfderiv_solidFoldPlus_bijective`, `mfderiv_solidFoldMinus_bijective`) and their images are
the closed discs of radius `1/2` about `±3/2` in the base. The signed seam map is a partial
diffeomorphism `mobiusSeam j` from `signedCollarSource` onto `1/4 < ‖J - c_j‖ < 3/4`, with
inverse `(unitOf μ, unitOf μ ^ 2 / unitOf (J - c_j), 4 ‖J - c_j‖ - 2)`, `μ` the fibre.

Cut carrier. `MobiusCut = productSet 3 ⊕ (solidSet ⊕ solidSet)` folds onto the bundle by
`mobiusFold`, smooth with bijective differential, and is oriented by pullback. Seam `i : Fin 2`
glues solid torus `i` (left, `solidCollar 2`) to hole `i + 1` of the pants (right) by
`seamMatching`. The fold identifies exactly the glued points (`mobiusGluing_rel_of_fold_eq`) and
is onto, so it descends to `mobiusReconstruction`; both seams reverse the boundary orientation
(`mobiusReversing`); the interior of the cut carrier is identified with
`‖J‖ < 3, ‖J ∓ 3/2‖ ≠ 1/2` (`mobiusInteriorDiffeomorph`); the outer collar of the pants, carried
by `mobiusOuterLift`, is the free torus. This is `mobiusPresentation`, and `mobiusBlock` is a
`SeifertBlock` for `mobiusData` (cones `(2, -1), (2, -1)`, both meridians `-(2, -1)`).

Signed normalisation. `holeShear ζ = unitOf (ζ - 3/2) · exp (i χ (π - arg (3/2 - ζ)))`, with `χ`
a smooth cutoff equal to `1` on `‖ζ + 3/2‖ ≤ 3/4` and `0` on `‖ζ + 3/2‖ ≥ 1`, is
`unitOf (ζ - 3/2)` on the collar of the hole about `3/2` and `1` on the collar of the hole about
`-3/2`. Shearing the pants fibre by it (`pantsShear`) turns the right collar of seam `0` by
`(τ₁, τ₂) ↦ (τ₁, τ₂ τ₁⁻¹)` and fixes that of seam `1`; with matching `!![-2, 1; -1, 1]`
(meridian `-(2, 1)`) at seam `0` and a sheared free port, `twistPresentation` gives
`mobiusTwistedIBundle : TwistedIBundle mobiusBundleCarrier` for `twistedIBundleData` itself.
-/

set_option autoImplicit false

noncomputable section
open Set Metric Function Filter
open DifferentialGeometry DifferentialGeometry.Topology GC.Endpoint GC.GraphManifold
open scoped Manifold ContDiff Topology ComplexConjugate

universe u

namespace GC.Seifert

attribute [local instance] fact_finrank_euclideanSpace_four finrank_real_complex_fact'

theorem unitOf_one : unitOf (1 : ℂ) = 1 := by
  have h := unitOf_circle 1
  rwa [Circle.coe_one] at h

theorem unitOf_mul {a b : ℂ} (ha : a ≠ 0) (hb : b ≠ 0) :
    unitOf (a * b) = unitOf a * unitOf b := by
  have h : a * b = (‖a‖ * ‖b‖) • ((unitOf a * unitOf b : Circle) : ℂ) := by
    rw [Circle.coe_mul, ← smul_mul_smul_comm, norm_smul_unitOf, norm_smul_unitOf]
  rw [h, unitOf_smul (mul_pos (norm_pos_iff.mpr ha) (norm_pos_iff.mpr hb))]

theorem unitOf_pow {a : ℂ} (ha : a ≠ 0) (n : ℕ) : unitOf (a ^ n) = unitOf a ^ n := by
  induction n with
  | zero => rw [pow_zero, pow_zero, unitOf_one]
  | succ n ih => rw [pow_succ, unitOf_mul (pow_ne_zero n ha) ha, ih, pow_succ]

theorem unitOf_inv {a : ℂ} (ha : a ≠ 0) : unitOf a⁻¹ = (unitOf a)⁻¹ := by
  refine eq_inv_of_mul_eq_one_left ?_
  rw [← unitOf_mul (inv_ne_zero ha) ha, inv_mul_cancel₀ ha, unitOf_one]

theorem unitOf_div {a b : ℂ} (ha : a ≠ 0) (hb : b ≠ 0) :
    unitOf (a / b) = unitOf a * (unitOf b)⁻¹ := by
  rw [div_eq_mul_inv, unitOf_mul ha (inv_ne_zero hb), unitOf_inv hb]

theorem coe_norm_mul_unitOf (z : ℂ) : ((‖z‖ : ℝ) : ℂ) * (unitOf z : ℂ) = z := by
  rw [← Complex.real_smul]
  exact norm_smul_unitOf z

theorem sq_norm_eq_mul_conj (z : ℂ) : ((‖z‖ : ℝ) : ℂ) ^ 2 = z * conj z := by
  rw [Complex.mul_conj, Complex.normSq_eq_norm_sq]
  push_cast
  ring

def holeSum (p : ℂ × ℂ) : ℂ := 27 + 18 * bundleBasePoint p

def holeChartPoint (p : ℂ × ℂ) : ℂ × ℂ :=
  (p.1 / conj p.2 * ((√‖holeSum p‖ : ℝ) : ℂ), p.2 ^ 4 / holeSum p)

theorem holeSum_lensUnitAction {ε : Circle} (hε : ε ^ 4 = 1) (p : ℂ × ℂ) :
    holeSum (lensUnitAction ε p) = holeSum p := by
  rw [holeSum, holeSum, bundleBasePoint_lensUnitAction hε]

theorem holeChartPoint_lensUnitAction {ε : Circle} (hε : ε ^ 4 = 1) (p : ℂ × ℂ) :
    holeChartPoint (lensUnitAction ε p) = holeChartPoint p := by
  have h4 : (ε : ℂ) ^ 4 = 1 := by rw [← Circle.coe_pow, hε, Circle.coe_one]
  have hc : conj (((ε⁻¹ : Circle) : ℂ)) = (ε : ℂ) := by
    rw [Circle.coe_inv_eq_conj, Complex.conj_conj]
  have hε0 : (ε : ℂ) ≠ 0 := Circle.coe_ne_zero ε
  rw [holeChartPoint, holeChartPoint, holeSum_lensUnitAction hε]
  refine Prod.ext ?_ ?_
  · change (ε : ℂ) * p.1 / conj (((ε⁻¹ : Circle) : ℂ) * p.2) * _ = _
    rw [map_mul, hc, mul_div_mul_left _ _ hε0]
  · change (((ε⁻¹ : Circle) : ℂ) * p.2) ^ 4 / _ = _
    rw [mul_pow, Circle.coe_inv, inv_pow, h4, inv_one, one_mul]

theorem bundleBasePoint_swap (p : ℂ × ℂ) : bundleBasePoint p.swap = -bundleBasePoint p := by
  rw [bundleBasePoint, bundleBasePoint, Prod.fst_swap, Prod.snd_swap, ← neg_sub, div_neg,
    add_comm]

theorem lensUnitAction_swap (ε : Circle) (p : ℂ × ℂ) :
    (lensUnitAction ε p).swap = lensUnitAction ε⁻¹ p.swap := by
  change (((ε⁻¹ : Circle) : ℂ) * p.2, (ε : ℂ) * p.1) =
    (((ε⁻¹ : Circle) : ℂ) * p.2, (((ε⁻¹)⁻¹ : Circle) : ℂ) * p.1)
  rw [inv_inv]

theorem holeChartPoint_swap_lensUnitAction {ε : Circle} (hε : ε ^ 4 = 1) (p : ℂ × ℂ) :
    holeChartPoint (lensUnitAction ε p).swap = holeChartPoint p.swap := by
  rw [lensUnitAction_swap, holeChartPoint_lensUnitAction (by rw [inv_pow, hε, inv_one])]

def holeChart : mobiusLensGroup.Orbit → ℂ × ℂ :=
  lensDescend holeChartPoint fun _ hε p => holeChartPoint_lensUnitAction hε p

def holeNegChart : mobiusLensGroup.Orbit → ℂ × ℂ :=
  lensDescend (fun p => holeChartPoint p.swap) fun _ hε p =>
    holeChartPoint_swap_lensUnitAction hε p

def solidChart (y : mobiusLens.{u}.Carrier) : PlaneLift.{u} × Circle :=
  (ULift.up (holeChart (lensDown y)).1, unitOf (holeChart (lensDown y)).2)

def solidNegChart (y : mobiusLens.{u}.Carrier) : PlaneLift.{u} × Circle :=
  (ULift.up (holeNegChart (lensDown y)).1, unitOf (-(holeNegChart (lensDown y)).2))

theorem contDiffAt_holeChartPoint {p : ℂ × ℂ} (h2 : p.2 ≠ 0) (hab : p.1 ^ 2 - p.2 ^ 2 ≠ 0)
    (hS : holeSum p ≠ 0) : ContDiffAt ℝ ∞ holeChartPoint p := by
  have hJ : ContDiffAt ℝ ∞ holeSum p :=
    contDiffAt_const.add (contDiffAt_const.mul (contDiffAt_bundleBasePoint hab))
  have hc : ContDiffAt ℝ ∞ (fun q : ℂ × ℂ => conj q.2) p :=
    Complex.conjCLE.contDiff.contDiffAt.comp p contDiffAt_snd
  have hn : ContDiffAt ℝ ∞ (fun q : ℂ × ℂ => ‖holeSum q‖) p :=
    (contDiffAt_norm ℝ hS).comp p hJ
  have hr : ContDiffAt ℝ ∞ (fun q : ℂ × ℂ => ((√‖holeSum q‖ : ℝ) : ℂ)) p :=
    Complex.ofRealCLM.contDiff.contDiffAt.comp p
      (hn.sqrt (norm_pos_iff.mpr hS).ne')
  have h1 : ContDiffAt ℝ ∞ (fun q : ℂ × ℂ => q.1 / conj q.2 * ((√‖holeSum q‖ : ℝ) : ℂ)) p := by
    have he : (fun q : ℂ × ℂ => q.1 / conj q.2 * ((√‖holeSum q‖ : ℝ) : ℂ)) =
        fun q : ℂ × ℂ => q.1 * (conj q.2)⁻¹ * ((√‖holeSum q‖ : ℝ) : ℂ) :=
      funext fun q => by rw [div_eq_mul_inv]
    rw [he]
    exact (contDiffAt_fst.mul (hc.inv ((map_ne_zero _).mpr h2))).mul hr
  have h2' : ContDiffAt ℝ ∞ (fun q : ℂ × ℂ => q.2 ^ 4 / holeSum q) p := by
    have he : (fun q : ℂ × ℂ => q.2 ^ 4 / holeSum q) = fun q : ℂ × ℂ => q.2 ^ 4 * (holeSum q)⁻¹ :=
      funext fun q => div_eq_mul_inv _ _
    rw [he]
    exact (contDiffAt_snd.pow 4).mul (hJ.inv hS)
  exact h1.prodMk h2'

theorem coneFirstScaleP_mul_sqrt {q : ℂ × ℂ} (hq : coneSumP q ≠ 0) :
    coneFirstScaleP q * √‖coneSumP q‖ = coneSecondScaleP q := by
  have h0 := coneTauP_nonneg q
  have hT : 0 < ‖coneSumP q‖ := norm_pos_iff.mpr hq
  rw [coneFirstScaleP, coneSecondScaleP,
    ← Real.sqrt_mul (inv_nonneg.mpr (mul_nonneg (by linarith) hT.le))]
  congr 1
  rw [mul_inv, mul_assoc, inv_mul_cancel₀ hT.ne', mul_one]

theorem holeSum_solidPair {q : ℂ × ℂ} (hq : coneSumP q ≠ 0) (w κ : Circle)
    (hw : ((w⁻¹ : Circle) : ℂ) = q.2) (hκ : κ ^ 4 = w * unitOf (coneSumP q)) :
    holeSum ((coneFirstScaleP q : ℂ) * q.1 * ((κ⁻¹ : Circle) : ℂ),
      (coneSecondScaleP q : ℂ) * (κ : ℂ)) = coneSumP q := by
  rw [holeSum, bundleBasePoint_solidPair hq w κ hw hκ, coneSumP]
  ring

theorem holeChartPoint_solidPair {q : ℂ × ℂ} (hq : coneSumP q ≠ 0) (w κ : Circle)
    (hw : ((w⁻¹ : Circle) : ℂ) = q.2) (hκ : κ ^ 4 = w * unitOf (coneSumP q)) :
    holeChartPoint ((coneFirstScaleP q : ℂ) * q.1 * ((κ⁻¹ : Circle) : ℂ),
      (coneSecondScaleP q : ℂ) * (κ : ℂ)) =
      (q.1, ((coneSecondScaleP q ^ 4 / ‖coneSumP q‖ : ℝ) : ℂ) * (w : ℂ)) := by
  rw [holeChartPoint, holeSum_solidPair hq w κ hw hκ]
  have hB : (coneSecondScaleP q : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (coneSecondScaleP_pos q).ne'
  have hκ0 : ((κ⁻¹ : Circle) : ℂ) ≠ 0 := Circle.coe_ne_zero _
  have hT : ((‖coneSumP q‖ : ℝ) : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (norm_ne_zero_iff.mpr hq)
  refine Prod.ext ?_ ?_
  · dsimp only
    have hconj : conj ((coneSecondScaleP q : ℂ) * (κ : ℂ)) =
        (coneSecondScaleP q : ℂ) * ((κ⁻¹ : Circle) : ℂ) := by
      rw [map_mul, Complex.conj_ofReal, Circle.coe_inv_eq_conj]
    have hm := congrArg (fun r : ℝ => (r : ℂ)) (coneFirstScaleP_mul_sqrt hq)
    simp only [Complex.ofReal_mul] at hm
    rw [hconj, mul_div_mul_right _ _ hκ0, div_mul_eq_mul_div, div_eq_iff hB]
    linear_combination q.1 * hm
  · dsimp only
    have hκ' : (κ : ℂ) ^ 4 = (w : ℂ) * (unitOf (coneSumP q) : ℂ) := by
      have h := congrArg (fun c : Circle => (c : ℂ)) hκ
      simpa only [Circle.coe_pow, Circle.coe_mul] using h
    have hU := coe_norm_mul_unitOf (coneSumP q)
    rw [mul_pow, hκ']
    push_cast
    field_simp
    linear_combination hU

theorem holeChartPoint_fst (p : ℂ × ℂ) :
    (holeChartPoint p).1 = p.1 / conj p.2 * ((√‖holeSum p‖ : ℝ) : ℂ) := rfl

theorem holeChartPoint_snd (p : ℂ × ℂ) : (holeChartPoint p).2 = p.2 ^ 4 / holeSum p := rfl

theorem holeChartPoint_coneSum {p : ℂ × ℂ} (h2 : p.2 ≠ 0) (hab : p.1 ^ 2 - p.2 ^ 2 ≠ 0)
    (hS : holeSum p ≠ 0) :
    54 + (holeChartPoint p).1 ^ 2 * (((unitOf (holeChartPoint p).2)⁻¹ : Circle) : ℂ) =
      holeSum p := by
  have hc : (holeChartPoint p).2 ≠ 0 := div_ne_zero (pow_ne_zero 4 h2) hS
  have hcb : conj p.2 ≠ 0 := (map_ne_zero _).mpr h2
  have hu : (((unitOf (holeChartPoint p).2)⁻¹ : Circle) : ℂ) =
      ((‖(holeChartPoint p).2‖ : ℝ) : ℂ) / (holeChartPoint p).2 := by
    have hU' := coe_norm_mul_unitOf (holeChartPoint p).2
    have hU : (unitOf (holeChartPoint p).2 : ℂ) ≠ 0 := Circle.coe_ne_zero _
    rw [Circle.coe_inv, eq_div_iff hc]
    calc ((unitOf (holeChartPoint p).2 : ℂ))⁻¹ * (holeChartPoint p).2
        = ((unitOf (holeChartPoint p).2 : ℂ))⁻¹ * (((‖(holeChartPoint p).2‖ : ℝ) : ℂ) *
          (unitOf (holeChartPoint p).2 : ℂ)) := by rw [hU']
      _ = _ := by field_simp
  have hnc : ((‖(holeChartPoint p).2‖ : ℝ) : ℂ) =
      ((‖p.2‖ : ℝ) : ℂ) ^ 4 / ((‖holeSum p‖ : ℝ) : ℂ) := by
    rw [holeChartPoint_snd, norm_div, norm_pow]
    push_cast
    rfl
  have hs : ((√‖holeSum p‖ : ℝ) : ℂ) ^ 2 = ((‖holeSum p‖ : ℝ) : ℂ) := by
    rw [← Complex.ofReal_pow, Real.sq_sqrt (norm_nonneg _)]
  have hN := sq_norm_eq_mul_conj p.2
  have hJ : bundleBasePoint p * (p.1 ^ 2 - p.2 ^ 2) = -(3 / 2) * (p.1 ^ 2 + p.2 ^ 2) := by
    rw [bundleBasePoint, div_mul_cancel₀ _ hab]
  have hT : ((‖holeSum p‖ : ℝ) : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (norm_ne_zero_iff.mpr hS)
  have hN4 : ((‖p.2‖ : ℝ) : ℂ) ^ 4 = (p.2 * conj p.2) ^ 2 := by
    rw [← hN]
    ring
  have step : (holeChartPoint p).1 ^ 2 * (((‖p.2‖ : ℝ) : ℂ) ^ 4 / ((‖holeSum p‖ : ℝ) : ℂ) /
      (holeChartPoint p).2) = p.1 ^ 2 * holeSum p / p.2 ^ 2 := by
    rw [holeChartPoint_fst, holeChartPoint_snd, mul_pow, div_pow, hs, hN4]
    field_simp
  rw [hu, hnc, step]
  have hS' : holeSum p = 27 + 18 * bundleBasePoint p := rfl
  field_simp
  rw [hS']
  linear_combination 18 * hJ

theorem exists_lensUnit_of_ratio {p p' : ℂ × ℂ} (hn : ‖p.1‖ ^ 2 + ‖p.2‖ ^ 2 = 1)
    (hn' : ‖p'.1‖ ^ 2 + ‖p'.2‖ ^ 2 = 1) (h2 : p.2 ≠ 0) (h2' : p'.2 ≠ 0)
    (hr : p.1 / conj p.2 = p'.1 / conj p'.2) (hq : unitOf (p.2 ^ 4) = unitOf (p'.2 ^ 4)) :
    ∃ ε : Circle, ε ^ 4 = 1 ∧ p' = lensUnitAction ε p := by
  have hc : conj p.2 ≠ 0 := (map_ne_zero _).mpr h2
  have hc' : conj p'.2 ≠ 0 := (map_ne_zero _).mpr h2'
  have hnr : ‖p.1‖ / ‖p.2‖ = ‖p'.1‖ / ‖p'.2‖ := by
    have h := congrArg norm hr
    rwa [norm_div, norm_div, Complex.norm_conj, Complex.norm_conj] at h
  have hρ : ‖p.2‖ = ‖p'.2‖ := by
    set k := ‖p.1‖ / ‖p.2‖
    have h1 : ‖p.1‖ = k * ‖p.2‖ := by rw [div_mul_cancel₀ _ (norm_ne_zero_iff.mpr h2)]
    have h1' : ‖p'.1‖ = k * ‖p'.2‖ := by rw [hnr, div_mul_cancel₀ _ (norm_ne_zero_iff.mpr h2')]
    rw [h1] at hn
    rw [h1'] at hn'
    have hsq : ‖p.2‖ ^ 2 = ‖p'.2‖ ^ 2 := by
      have hk : 0 < k ^ 2 + 1 := by positivity
      have e1 : (k ^ 2 + 1) * ‖p.2‖ ^ 2 = 1 := by linear_combination hn
      have e2 : (k ^ 2 + 1) * ‖p'.2‖ ^ 2 = 1 := by linear_combination hn'
      exact mul_left_cancel₀ hk.ne' (e1.trans e2.symm)
    exact (pow_left_inj₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero).mp hsq
  set e : Circle := unitOf p'.2 * (unitOf p.2)⁻¹ with he
  have he' : (e : ℂ) * (unitOf p.2 : ℂ) = unitOf p'.2 := by
    rw [← Circle.coe_mul, he, inv_mul_cancel_right]
  have he2 : p'.2 = (e : ℂ) * p.2 := by
    calc p'.2 = ((‖p'.2‖ : ℝ) : ℂ) * (unitOf p'.2 : ℂ) := (coe_norm_mul_unitOf _).symm
      _ = (e : ℂ) * (((‖p.2‖ : ℝ) : ℂ) * (unitOf p.2 : ℂ)) := by rw [← he', hρ]; ring
      _ = (e : ℂ) * p.2 := by rw [coe_norm_mul_unitOf]
  have he4 : e ^ 4 = 1 := by
    rw [he, mul_pow, inv_pow, ← unitOf_pow h2', ← unitOf_pow h2, hq, mul_inv_cancel]
  have he1 : p'.1 = ((e⁻¹ : Circle) : ℂ) * p.1 := by
    have h : p'.1 = p.1 / conj p.2 * conj p'.2 := by rw [hr, div_mul_cancel₀ _ hc']
    rw [h, he2, map_mul, ← Circle.coe_inv_eq_conj]
    field_simp
  refine ⟨e⁻¹, by rw [inv_pow, he4, inv_one], Prod.ext he1 ?_⟩
  change p'.2 = (((e⁻¹)⁻¹ : Circle) : ℂ) * p.2
  rw [inv_inv]
  exact he2

theorem holeChartPoint_snd_ne_zero {p : ℂ × ℂ} (h2 : p.2 ≠ 0) (hS : holeSum p ≠ 0) :
    (holeChartPoint p).2 ≠ 0 :=
  div_ne_zero (pow_ne_zero 4 h2) hS

theorem exists_lensUnit_of_holeChartPoint {p p' : ℂ × ℂ} (hn : ‖p.1‖ ^ 2 + ‖p.2‖ ^ 2 = 1)
    (hn' : ‖p'.1‖ ^ 2 + ‖p'.2‖ ^ 2 = 1) (h2 : p.2 ≠ 0) (h2' : p'.2 ≠ 0) (hS : holeSum p ≠ 0)
    (hSS : holeSum p = holeSum p') (h1 : (holeChartPoint p).1 = (holeChartPoint p').1)
    (hw : unitOf (holeChartPoint p).2 = unitOf (holeChartPoint p').2) :
    ∃ ε : Circle, ε ^ 4 = 1 ∧ p' = lensUnitAction ε p := by
  have hS' : holeSum p' ≠ 0 := hSS ▸ hS
  refine exists_lensUnit_of_ratio hn hn' h2 h2' ?_ ?_
  · have hs : ((√‖holeSum p‖ : ℝ) : ℂ) ≠ 0 :=
      Complex.ofReal_ne_zero.mpr (Real.sqrt_pos.mpr (norm_pos_iff.mpr hS)).ne'
    rw [holeChartPoint_fst, holeChartPoint_fst, ← hSS] at h1
    exact mul_right_cancel₀ hs h1
  · have e1 : p.2 ^ 4 = (holeChartPoint p).2 * holeSum p := by
      rw [holeChartPoint_snd, div_mul_cancel₀ _ hS]
    have e2 : p'.2 ^ 4 = (holeChartPoint p').2 * holeSum p' := by
      rw [holeChartPoint_snd, div_mul_cancel₀ _ hS']
    rw [e1, e2, unitOf_mul (holeChartPoint_snd_ne_zero h2 hS) hS,
      unitOf_mul (holeChartPoint_snd_ne_zero h2' hS') hS', hw, hSS]

theorem holeChart_projection (x : sphere (0 : EuclideanSpace ℝ (Fin 4)) 1) :
    holeChart (mobiusLensGroup.projection x) = holeChartPoint (lensPair x) :=
  rfl

theorem holeNegChart_projection (x : sphere (0 : EuclideanSpace ℝ (Fin 4)) 1) :
    holeNegChart (mobiusLensGroup.projection x) = holeChartPoint (lensPair x).swap :=
  rfl

theorem unitOf_ofReal_mul {r : ℝ} (hr : 0 < r) (v : Circle) : unitOf ((r : ℂ) * (v : ℂ)) = v := by
  rw [← Complex.real_smul]
  exact unitOf_smul hr v

theorem coneScaleRatio_pos (q : ℂ × ℂ) (hq : coneSumP q ≠ 0) :
    0 < coneSecondScaleP q ^ 4 / ‖coneSumP q‖ :=
  div_pos (pow_pos (coneSecondScaleP_pos q) 4) (norm_pos_iff.mpr hq)

theorem holeChartPoint_solidSectionLift {y : PlaneLift.{u} × Circle} (hy : coneGood y) :
    holeChartPoint (lensPair (sphereDownPoint (solidSectionLift y) : EuclideanSpace ℝ (Fin 4))) =
      (y.1.down, ((coneSecondScaleP (conePair y) ^ 4 / ‖coneSumP (conePair y)‖ : ℝ) : ℂ) *
        (y.2 : ℂ)) := by
  rw [lensPair_solidSectionLift]
  exact holeChartPoint_solidPair hy y.2 _ rfl (circleRootOf_pow 4 _)

theorem solidChart_solidSection {y : PlaneLift.{u} × Circle} (hy : coneGood y) :
    solidChart (lensUp (solidSection y)) = y := by
  have h : holeChart (lensDown (lensUp.{u} (solidSection y))) =
      holeChartPoint (lensPair (sphereDownPoint (solidSectionLift y) :
        EuclideanSpace ℝ (Fin 4))) := rfl
  rw [holeChartPoint_solidSectionLift hy] at h
  rw [solidChart, h]
  exact Prod.ext rfl (unitOf_ofReal_mul (coneScaleRatio_pos _ hy) y.2)

theorem holeChartPoint_solidNegSectionLift {y : PlaneLift.{u} × Circle} (hy : coneNegGood y) :
    holeChartPoint (lensPair (sphereDownPoint (solidNegSectionLift y) :
      EuclideanSpace ℝ (Fin 4))).swap =
      (y.1.down, ((coneSecondScaleP (conePairNeg y) ^ 4 / ‖coneSumP (conePairNeg y)‖ : ℝ) : ℂ) *
        ((circleI ^ 2 * y.2 : Circle) : ℂ)) := by
  rw [lensPair_solidNegSectionLift, Prod.swap_prod_mk]
  have h := holeChartPoint_solidPair hy (circleI ^ 2 * y.2)
    (circleRootOf 4 (solidNegRootTarget y))⁻¹
    (conePairNeg_snd y) (solidNegRootTarget_root y)
  rw [inv_inv] at h
  exact h

theorem circleI_sq_coe : ((circleI ^ 2 : Circle) : ℂ) = -1 := by
  rw [Circle.coe_pow, coe_circleI, Complex.I_sq]

theorem solidNegChart_solidNegSection {y : PlaneLift.{u} × Circle} (hy : coneNegGood y) :
    solidNegChart (lensUp (solidNegSection y)) = y := by
  have h : holeNegChart (lensDown (lensUp.{u} (solidNegSection y))) =
      holeChartPoint (lensPair (sphereDownPoint (solidNegSectionLift y) :
        EuclideanSpace ℝ (Fin 4))).swap := rfl
  rw [holeChartPoint_solidNegSectionLift hy] at h
  rw [solidNegChart, h]
  refine Prod.ext rfl ?_
  dsimp only
  rw [Circle.coe_mul, circleI_sq_coe, show ∀ a b : ℂ, -(a * (-1 * b)) = a * b by intros; ring]
  exact unitOf_ofReal_mul (coneScaleRatio_pos _ hy) y.2

theorem contMDiffAt_solidChart {y : mobiusLens.{u}.Carrier}
    {x : sphere (0 : EuclideanSpace ℝ (Fin 4)) 1} (hx : lensDown y = mobiusLensGroup.projection x)
    (h2 : (lensPair x).2 ≠ 0) (hab : (lensPair x).1 ^ 2 - (lensPair x).2 ^ 2 ≠ 0)
    (hS : holeSum (lensPair x) ≠ 0) :
    ContMDiffAt (𝓡 3) PlaneCircleModel ∞ solidChart.{u} y := by
  have hc := contMDiffAt_lensDescend (fun _ hε p => holeChartPoint_lensUnitAction hε p) x
    (contDiffAt_holeChartPoint h2 hab hS)
  rw [← hx] at hc
  have hc' : ContMDiffAt (𝓡 3) 𝓘(ℝ, ℂ × ℂ) ∞ (fun y => holeChart (lensDown.{u} y)) y :=
    hc.comp y contMDiff_lensDown.contMDiffAt
  have h1 : ContMDiffAt (𝓡 3) 𝓘(ℝ, ℂ) ∞ (fun y => (holeChart (lensDown.{u} y)).1) y :=
    contDiff_fst.contMDiff.contMDiffAt.comp y hc'
  have h2' : ContMDiffAt (𝓡 3) 𝓘(ℝ, ℂ) ∞ (fun y => (holeChart (lensDown.{u} y)).2) y :=
    contDiff_snd.contMDiff.contMDiffAt.comp y hc'
  have hne : (holeChart (lensDown y)).2 ≠ 0 := by
    rw [hx, holeChart_projection]
    exact holeChartPoint_snd_ne_zero h2 hS
  exact (contMDiff_planeLift_up.contMDiffAt.comp y h1).prodMk
    ((contMDiffOn_unitOf.contMDiffAt (isOpen_ne.mem_nhds hne)).comp y h2')

theorem holeSum_swap (p : ℂ × ℂ) : holeSum p.swap = 27 - 18 * bundleBasePoint p := by
  rw [holeSum, bundleBasePoint_swap]
  ring

theorem contMDiffAt_solidNegChart {y : mobiusLens.{u}.Carrier}
    {x : sphere (0 : EuclideanSpace ℝ (Fin 4)) 1} (hx : lensDown y = mobiusLensGroup.projection x)
    (h1 : (lensPair x).1 ≠ 0) (hab : (lensPair x).1 ^ 2 - (lensPair x).2 ^ 2 ≠ 0)
    (hS : holeSum (lensPair x).swap ≠ 0) :
    ContMDiffAt (𝓡 3) PlaneCircleModel ∞ solidNegChart.{u} y := by
  have hab' : (lensPair x).swap.1 ^ 2 - (lensPair x).swap.2 ^ 2 ≠ 0 := by
    rw [Prod.fst_swap, Prod.snd_swap, ← neg_sub]
    exact neg_ne_zero.mpr hab
  have hc := contMDiffAt_lensDescend (fun _ hε p => holeChartPoint_swap_lensUnitAction hε p) x
    ((contDiffAt_holeChartPoint h1 hab' hS).comp _
      (contDiff_snd.prodMk contDiff_fst).contDiffAt)
  rw [← hx] at hc
  have hc' : ContMDiffAt (𝓡 3) 𝓘(ℝ, ℂ × ℂ) ∞ (fun y => holeNegChart (lensDown.{u} y)) y :=
    hc.comp y contMDiff_lensDown.contMDiffAt
  have e1 : ContMDiffAt (𝓡 3) 𝓘(ℝ, ℂ) ∞ (fun y => (holeNegChart (lensDown.{u} y)).1) y :=
    contDiff_fst.contMDiff.contMDiffAt.comp y hc'
  have e2 : ContMDiffAt (𝓡 3) 𝓘(ℝ, ℂ) ∞ (fun y => -(holeNegChart (lensDown.{u} y)).2) y :=
    (contDiff_snd.neg.contMDiff.contMDiffAt).comp y hc'
  have hne : -(holeNegChart (lensDown y)).2 ≠ 0 := by
    rw [hx, holeNegChart_projection]
    exact neg_ne_zero.mpr (holeChartPoint_snd_ne_zero h1 hS)
  exact (contMDiff_planeLift_up.contMDiffAt.comp y e1).prodMk
    ((contMDiffOn_unitOf.contMDiffAt (isOpen_ne.mem_nhds hne)).comp y e2)

theorem solidSection_solidChart {y : mobiusLens.{u}.Carrier}
    {x : sphere (0 : EuclideanSpace ℝ (Fin 4)) 1} (hx : lensDown y = mobiusLensGroup.projection x)
    (h2 : (lensPair x).2 ≠ 0) (hab : (lensPair x).1 ^ 2 - (lensPair x).2 ^ 2 ≠ 0)
    (hS : holeSum (lensPair x) ≠ 0) :
    coneGood (solidChart y) ∧ solidSection (solidChart y) = lensDown y := by
  have hY : solidChart y = (ULift.up (holeChartPoint (lensPair x)).1,
      unitOf (holeChartPoint (lensPair x)).2) := by
    rw [solidChart, hx]
    rfl
  have hq : coneSumP (conePair (solidChart y)) = holeSum (lensPair x) := by
    rw [hY]
    exact holeChartPoint_coneSum h2 hab hS
  have hg : coneGood (solidChart y) := by
    change coneSumP (conePair (solidChart y)) ≠ 0
    rw [hq]
    exact hS
  refine ⟨hg, ?_⟩
  rw [hx]
  change mobiusLensGroup.projection (sphereDownPoint (solidSectionLift (solidChart y))) = _
  refine (projection_eq_projection_iff _ _).mpr ?_
  have hP := holeChartPoint_solidSectionLift hg
  have hP2 : (lensPair (sphereDownPoint (solidSectionLift (solidChart y)) :
      EuclideanSpace ℝ (Fin 4))).2 ≠ 0 := by
    rw [lensPair_solidSectionLift]
    exact mul_ne_zero (Complex.ofReal_ne_zero.mpr (coneSecondScaleP_pos _).ne')
      (Circle.coe_ne_zero _)
  have hPS : holeSum (lensPair (sphereDownPoint (solidSectionLift (solidChart y)) :
      EuclideanSpace ℝ (Fin 4))) = holeSum (lensPair x) := by
    rw [lensPair_solidSectionLift, holeSum_solidPair hg (solidChart y).2
      (circleRootOf 4 (solidRootTarget (solidChart y))) rfl (circleRootOf_pow 4 _), hq]
  refine exists_lensUnit_of_holeChartPoint (norm_sq_lensPair_sphere _) (norm_sq_lensPair_sphere x)
    hP2 h2 (hPS ▸ hS) hPS ?_ ?_
  · rw [hP, hY]
  · rw [hP, unitOf_ofReal_mul (coneScaleRatio_pos _ hg), hY]

theorem unitOf_neg {c : ℂ} (hc : c ≠ 0) : unitOf (-c) = circleI ^ 2 * unitOf c := by
  have hm : unitOf (-1 : ℂ) = circleI ^ 2 := by
    have h := unitOf_circle (circleI ^ 2)
    rwa [circleI_sq_coe] at h
  rw [neg_eq_neg_one_mul, unitOf_mul (by norm_num) hc, hm]

theorem swap_eq_lensUnitAction {p p' : ℂ × ℂ} {ε : Circle}
    (h : p'.swap = lensUnitAction ε p.swap) : p' = lensUnitAction ε⁻¹ p := by
  have h' := congrArg Prod.swap h
  rw [Prod.swap_swap, lensUnitAction_swap, Prod.swap_swap] at h'
  exact h'

theorem solidNegSection_solidNegChart {y : mobiusLens.{u}.Carrier}
    {x : sphere (0 : EuclideanSpace ℝ (Fin 4)) 1} (hx : lensDown y = mobiusLensGroup.projection x)
    (h1 : (lensPair x).1 ≠ 0) (hab : (lensPair x).1 ^ 2 - (lensPair x).2 ^ 2 ≠ 0)
    (hS : holeSum (lensPair x).swap ≠ 0) :
    coneNegGood (solidNegChart y) ∧ solidNegSection (solidNegChart y) = lensDown y := by
  have hab' : (lensPair x).swap.1 ^ 2 - (lensPair x).swap.2 ^ 2 ≠ 0 := by
    rw [Prod.fst_swap, Prod.snd_swap, ← neg_sub]
    exact neg_ne_zero.mpr hab
  have hc := holeChartPoint_snd_ne_zero (p := (lensPair x).swap) h1 hS
  have hY : solidNegChart y = (ULift.up (holeChartPoint (lensPair x).swap).1,
      unitOf (-(holeChartPoint (lensPair x).swap).2)) := by
    rw [solidNegChart, hx]
    rfl
  have hinv : -((((unitOf (-(holeChartPoint (lensPair x).swap).2))⁻¹ : Circle)) : ℂ) =
      (((unitOf (holeChartPoint (lensPair x).swap).2)⁻¹ : Circle) : ℂ) := by
    rw [unitOf_neg hc, mul_inv, Circle.coe_mul, Circle.coe_inv (circleI ^ 2), circleI_sq_coe]
    ring
  have hq : coneSumP (conePairNeg (solidNegChart y)) = holeSum (lensPair x).swap := by
    rw [hY]
    change 54 + _ ^ 2 * -(_ : ℂ) = _
    rw [hinv]
    exact holeChartPoint_coneSum h1 hab' hS
  have hg : coneNegGood (solidNegChart y) := by
    change coneSumP (conePairNeg (solidNegChart y)) ≠ 0
    rw [hq]
    exact hS
  refine ⟨hg, ?_⟩
  rw [hx]
  change mobiusLensGroup.projection (sphereDownPoint (solidNegSectionLift (solidNegChart y))) = _
  refine (projection_eq_projection_iff _ _).mpr ?_
  have hP := holeChartPoint_solidNegSectionLift hg
  have hP2 : (lensPair (sphereDownPoint (solidNegSectionLift (solidNegChart y)) :
      EuclideanSpace ℝ (Fin 4))).swap.2 ≠ 0 := by
    rw [lensPair_solidNegSectionLift, Prod.snd_swap]
    exact mul_ne_zero (Complex.ofReal_ne_zero.mpr (coneSecondScaleP_pos _).ne')
      (Circle.coe_ne_zero _)
  have hPS : holeSum (lensPair (sphereDownPoint (solidNegSectionLift (solidNegChart y)) :
      EuclideanSpace ℝ (Fin 4))).swap = holeSum (lensPair x).swap := by
    have h := holeSum_solidPair hg (circleI ^ 2 * (solidNegChart y).2)
      (circleRootOf 4 (solidNegRootTarget (solidNegChart y)))⁻¹ (conePairNeg_snd _)
      (solidNegRootTarget_root _)
    rw [inv_inv] at h
    rw [lensPair_solidNegSectionLift, Prod.swap_prod_mk, h, hq]
  have hn : ∀ z : sphere (0 : EuclideanSpace ℝ (Fin 4)) 1,
      ‖(lensPair z).swap.1‖ ^ 2 + ‖(lensPair z).swap.2‖ ^ 2 = 1 := fun z => by
    rw [Prod.fst_swap, Prod.snd_swap, add_comm]
    exact norm_sq_lensPair_sphere z
  obtain ⟨ε, hε, h⟩ := exists_lensUnit_of_holeChartPoint (hn _) (hn x) hP2 h1 (hPS ▸ hS) hPS
    (by rw [hP, hY]) (by
      rw [hP, unitOf_ofReal_mul (coneScaleRatio_pos _ hg), hY]
      dsimp only
      rw [unitOf_neg hc, ← mul_assoc, ← pow_add, show 2 + 2 = 4 from rfl, circleI_pow_four,
        one_mul])
  exact ⟨ε⁻¹, by rw [inv_pow, hε, inv_one], swap_eq_lensUnitAction h⟩

theorem holeSum_eq_zero_iff (p : ℂ × ℂ) : holeSum p = 0 ↔ bundleBasePoint p = -(3 / 2) := by
  rw [holeSum]
  constructor
  · intro h
    linear_combination h / 18
  · intro h
    rw [h]
    norm_num

theorem holeSum_swap_eq_zero_iff (p : ℂ × ℂ) : holeSum p.swap = 0 ↔ bundleBasePoint p = 3 / 2 := by
  rw [holeSum_swap]
  constructor
  · intro h
    linear_combination -h / 18
  · intro h
    rw [h]
    norm_num

theorem exists_sphere_rep_snd (y : mobiusBundleSet.{u}) (hy : mobiusBundleBase y ≠ -(3 / 2)) :
    ∃ x : sphere (0 : EuclideanSpace ℝ (Fin 4)) 1, lensDown y.val = mobiusLensGroup.projection x ∧
      (lensPair x).2 ≠ 0 ∧ (lensPair x).1 ^ 2 - (lensPair x).2 ^ 2 ≠ 0 ∧
        holeSum (lensPair x) ≠ 0 ∧ mobiusBundleBase y = bundleBasePoint (lensPair x) := by
  obtain ⟨x, hx, hq⟩ := exists_sphere_rep y
  have hab := sq_sub_sq_ne_zero_of_bundleQuartic_nonpos (lensPair_ne_zero x) hq
  have hJ := mobiusBundleBase_eq hx
  refine ⟨x, hx, fun h => hy (hJ.trans ((bundleBasePoint_eq_iff_snd hab).mpr h)), hab,
    fun h => hy (hJ.trans ((holeSum_eq_zero_iff _).mp h)), hJ⟩

theorem exists_sphere_rep_fst (y : mobiusBundleSet.{u}) (hy : mobiusBundleBase y ≠ 3 / 2) :
    ∃ x : sphere (0 : EuclideanSpace ℝ (Fin 4)) 1, lensDown y.val = mobiusLensGroup.projection x ∧
      (lensPair x).1 ≠ 0 ∧ (lensPair x).1 ^ 2 - (lensPair x).2 ^ 2 ≠ 0 ∧
        holeSum (lensPair x).swap ≠ 0 ∧ mobiusBundleBase y = bundleBasePoint (lensPair x) := by
  obtain ⟨x, hx, hq⟩ := exists_sphere_rep y
  have hab := sq_sub_sq_ne_zero_of_bundleQuartic_nonpos (lensPair_ne_zero x) hq
  have hJ := mobiusBundleBase_eq hx
  refine ⟨x, hx, fun h => hy (hJ.trans ((bundleBasePoint_eq_iff_fst hab).mpr h)), hab,
    fun h => hy (hJ.trans ((holeSum_swap_eq_zero_iff _).mp h)), hJ⟩

theorem solidChart_solidFoldPlus (x : solidSet.{u}) : solidChart (solidFoldPlus x).val = x.val :=
  solidChart_solidSection (coneGood_of_mem_solidSet x)

theorem solidNegChart_solidFoldMinus (x : solidSet.{u}) :
    solidNegChart (solidFoldMinus x).val = x.val :=
  solidNegChart_solidNegSection (coneNegGood_of_mem_solidSet x)

theorem solidFoldPlus_injective : Injective solidFoldPlus.{u} := fun x x' h =>
  Subtype.ext ((solidChart_solidFoldPlus x).symm.trans
    ((congrArg (fun z => solidChart z.val) h).trans (solidChart_solidFoldPlus x')))

theorem solidFoldMinus_injective : Injective solidFoldMinus.{u} := fun x x' h =>
  Subtype.ext ((solidNegChart_solidFoldMinus x).symm.trans
    ((congrArg (fun z => solidNegChart z.val) h).trans (solidNegChart_solidFoldMinus x')))

theorem norm_solidChart_sq (y : mobiusBundleSet.{u}) (hy : mobiusBundleBase y ≠ -(3 / 2)) :
    ‖(solidChart y.val).1.down‖ ^ 2 = 18 * ‖mobiusBundleBase y - 3 / 2‖ := by
  obtain ⟨x, hx, h2, hab, hS, hJ⟩ := exists_sphere_rep_snd y hy
  have hY : solidChart y.val = (ULift.up (holeChartPoint (lensPair x)).1,
      unitOf (holeChartPoint (lensPair x)).2) := by
    rw [solidChart, hx]
    rfl
  have h := holeChartPoint_coneSum h2 hab hS
  have h' : (holeChartPoint (lensPair x)).1 ^ 2 *
      (((unitOf (holeChartPoint (lensPair x)).2)⁻¹ : Circle) : ℂ) =
      18 * (bundleBasePoint (lensPair x) - 3 / 2) := by
    rw [holeSum] at h
    linear_combination h
  have hn := congrArg norm h'
  rw [norm_mul, Circle.norm_coe, mul_one, norm_pow, norm_mul] at hn
  rw [hY, hJ]
  change ‖(holeChartPoint (lensPair x)).1‖ ^ 2 = _
  rw [hn]
  norm_num

theorem norm_solidNegChart_sq (y : mobiusBundleSet.{u}) (hy : mobiusBundleBase y ≠ 3 / 2) :
    ‖(solidNegChart y.val).1.down‖ ^ 2 = 18 * ‖mobiusBundleBase y + 3 / 2‖ := by
  obtain ⟨x, hx, h1, hab, hS, hJ⟩ := exists_sphere_rep_fst y hy
  have hab' : (lensPair x).swap.1 ^ 2 - (lensPair x).swap.2 ^ 2 ≠ 0 := by
    rw [Prod.fst_swap, Prod.snd_swap, ← neg_sub]
    exact neg_ne_zero.mpr hab
  have hY : solidNegChart y.val = (ULift.up (holeChartPoint (lensPair x).swap).1,
      unitOf (-(holeChartPoint (lensPair x).swap).2)) := by
    rw [solidNegChart, hx]
    rfl
  have h := holeChartPoint_coneSum (p := (lensPair x).swap) h1 hab' hS
  have h' : (holeChartPoint (lensPair x).swap).1 ^ 2 *
      (((unitOf (holeChartPoint (lensPair x).swap).2)⁻¹ : Circle) : ℂ) =
      -18 * (bundleBasePoint (lensPair x) + 3 / 2) := by
    rw [holeSum_swap] at h
    linear_combination h
  have hn := congrArg norm h'
  rw [norm_mul, Circle.norm_coe, mul_one, norm_pow, norm_mul] at hn
  rw [hY, hJ]
  change ‖(holeChartPoint (lensPair x).swap).1‖ ^ 2 = _
  rw [hn]
  norm_num

theorem solidChart_mem (y : mobiusBundleSet.{u}) (hy : ‖mobiusBundleBase y - 3 / 2‖ ≤ 1 / 2) :
    solidChart y.val ∈ solidSet.{u} := by
  have hne : mobiusBundleBase y ≠ -(3 / 2) := by
    intro h
    rw [h] at hy
    norm_num at hy
  rw [mem_solidSet_iff]
  have h := norm_solidChart_sq y hne
  nlinarith [norm_nonneg (solidChart y.val).1.down]

theorem solidNegChart_mem (y : mobiusBundleSet.{u}) (hy : ‖mobiusBundleBase y + 3 / 2‖ ≤ 1 / 2) :
    solidNegChart y.val ∈ solidSet.{u} := by
  have hne : mobiusBundleBase y ≠ 3 / 2 := by
    intro h
    rw [h] at hy
    norm_num at hy
  rw [mem_solidSet_iff]
  have h := norm_solidNegChart_sq y hne
  nlinarith [norm_nonneg (solidNegChart y.val).1.down]

theorem solidFoldPlus_chart (y : mobiusBundleSet.{u}) (hy : ‖mobiusBundleBase y - 3 / 2‖ ≤ 1 / 2) :
    solidFoldPlus ⟨solidChart y.val, solidChart_mem y hy⟩ = y := by
  have hne : mobiusBundleBase y ≠ -(3 / 2) := by
    intro h
    rw [h] at hy
    norm_num at hy
  obtain ⟨x, hx, h2, hab, hS, -⟩ := exists_sphere_rep_snd y hne
  apply Subtype.ext
  change lensUp (solidSection (solidChart y.val)) = y.val
  rw [(solidSection_solidChart hx h2 hab hS).2, lensUp_lensDown]

theorem solidFoldMinus_chart (y : mobiusBundleSet.{u})
    (hy : ‖mobiusBundleBase y + 3 / 2‖ ≤ 1 / 2) :
    solidFoldMinus ⟨solidNegChart y.val, solidNegChart_mem y hy⟩ = y := by
  have hne : mobiusBundleBase y ≠ 3 / 2 := by
    intro h
    rw [h] at hy
    norm_num at hy
  obtain ⟨x, hx, h1, hab, hS, -⟩ := exists_sphere_rep_fst y hne
  apply Subtype.ext
  change lensUp (solidNegSection (solidNegChart y.val)) = y.val
  rw [(solidNegSection_solidNegChart hx h1 hab hS).2, lensUp_lensDown]

theorem bijective_mfderiv_of_leftInverse {E H M F G N : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [TopologicalSpace M]
    [ChartedSpace H M] [NormedAddCommGroup F] [NormedSpace ℝ F] [TopologicalSpace G]
    {J : ModelWithCorners ℝ F G} [TopologicalSpace N] [ChartedSpace G N] [FiniteDimensional ℝ E]
    [FiniteDimensional ℝ F] {f : M → N} {g : N → M} {x : M} (hf : MDifferentiableAt I J f x)
    (hg : MDifferentiableAt J I g (f x)) (hgf : g ∘ f =ᶠ[𝓝 x] id)
    (hdim : Module.finrank ℝ E = Module.finrank ℝ F) : Bijective (mfderiv I J f x) := by
  have hcomp := mfderiv_comp x hg hf
  rw [hgf.mfderiv_eq, mfderiv_id] at hcomp
  have hinj : Injective (mfderiv I J f x) := by
    intro v w hvw
    have hv := congrArg (fun L => L v) hcomp
    have hw := congrArg (fun L => L w) hcomp
    simp only [ContinuousLinearMap.comp_apply] at hv hw
    change v = _ at hv
    change w = _ at hw
    rw [hv, hw, hvw]
  have hdim' : Module.finrank ℝ (TangentSpace I x) = Module.finrank ℝ (TangentSpace J (f x)) :=
    hdim
  have : FiniteDimensional ℝ (TangentSpace I x) := inferInstanceAs (FiniteDimensional ℝ E)
  have : FiniteDimensional ℝ (TangentSpace J (f x)) := inferInstanceAs (FiniteDimensional ℝ F)
  exact ⟨hinj, (LinearMap.injective_iff_surjective_of_finrank_eq_finrank hdim'
    (f := (mfderiv I J f x : TangentSpace I x →ₗ[ℝ] TangentSpace J (f x)))).mp hinj⟩

theorem finrank_planeCircle_eq :
    Module.finrank ℝ (ℂ × EuclideanSpace ℝ (Fin 1)) =
      Module.finrank ℝ (EuclideanSpace ℝ (Fin 3)) := by
  rw [finrank_planeCircleModel, finrank_euclideanSpace_fin]

theorem mfderiv_solidSection_bijective {y : PlaneLift.{u} × Circle} (hy : coneGood y) :
    Bijective (mfderiv PlaneCircleModel (𝓡 3) (fun y => lensUp.{u} (solidSection y)) y) := by
  have hf : MDifferentiableAt PlaneCircleModel (𝓡 3) (fun y => lensUp.{u} (solidSection y)) y :=
    (contMDiff_lensUp.contMDiffAt.comp y (contMDiffAt_solidSection hy)).mdifferentiableAt
      (by simp)
  have h2 : (lensPair (sphereDownPoint (solidSectionLift y) : EuclideanSpace ℝ (Fin 4))).2 ≠ 0 := by
    rw [lensPair_solidSectionLift]
    exact mul_ne_zero (Complex.ofReal_ne_zero.mpr (coneSecondScaleP_pos _).ne')
      (Circle.coe_ne_zero _)
  have hS : holeSum (lensPair (sphereDownPoint (solidSectionLift y) :
      EuclideanSpace ℝ (Fin 4))) ≠ 0 := by
    rw [lensPair_solidSectionLift, holeSum_solidPair hy y.2 (circleRootOf 4 (solidRootTarget y))
      rfl (circleRootOf_pow 4 _)]
    exact hy
  have hg : MDifferentiableAt (𝓡 3) PlaneCircleModel solidChart.{u} (lensUp (solidSection y)) :=
    (contMDiffAt_solidChart (x := sphereDownPoint (solidSectionLift y)) rfl h2
      (solidSectionLift_sq_sub_ne_zero hy) hS).mdifferentiableAt (by simp)
  refine bijective_mfderiv_of_leftInverse hf hg ?_ finrank_planeCircle_eq
  filter_upwards [isOpen_coneGood.mem_nhds hy] with y' hy'
  exact solidChart_solidSection hy'

theorem mfderiv_solidNegSection_bijective {y : PlaneLift.{u} × Circle} (hy : coneNegGood y) :
    Bijective (mfderiv PlaneCircleModel (𝓡 3) (fun y => lensUp.{u} (solidNegSection y)) y) := by
  have hf : MDifferentiableAt PlaneCircleModel (𝓡 3)
      (fun y => lensUp.{u} (solidNegSection y)) y :=
    (contMDiff_lensUp.contMDiffAt.comp y (contMDiffAt_solidNegSection hy)).mdifferentiableAt
      (by simp)
  have h1 : (lensPair (sphereDownPoint (solidNegSectionLift y) :
      EuclideanSpace ℝ (Fin 4))).1 ≠ 0 := by
    rw [lensPair_solidNegSectionLift]
    exact mul_ne_zero (Complex.ofReal_ne_zero.mpr (coneSecondScaleP_pos _).ne')
      (Circle.coe_ne_zero _)
  have hS : holeSum (lensPair (sphereDownPoint (solidNegSectionLift y) :
      EuclideanSpace ℝ (Fin 4))).swap ≠ 0 := by
    have h := holeSum_solidPair hy (circleI ^ 2 * y.2) (circleRootOf 4 (solidNegRootTarget y))⁻¹
      (conePairNeg_snd y) (solidNegRootTarget_root y)
    rw [inv_inv] at h
    rw [lensPair_solidNegSectionLift, Prod.swap_prod_mk, h]
    exact hy
  have hab : (lensPair (sphereDownPoint (solidNegSectionLift y) :
      EuclideanSpace ℝ (Fin 4))).1 ^ 2 - (lensPair (sphereDownPoint (solidNegSectionLift y) :
      EuclideanSpace ℝ (Fin 4))).2 ^ 2 ≠ 0 := by
    intro h
    exact solidNegSectionLift_sq_sub_ne_zero hy h
  have hg : MDifferentiableAt (𝓡 3) PlaneCircleModel solidNegChart.{u}
      (lensUp (solidNegSection y)) :=
    (contMDiffAt_solidNegChart (x := sphereDownPoint (solidNegSectionLift y)) rfl h1 hab
      hS).mdifferentiableAt (by simp)
  refine bijective_mfderiv_of_leftInverse hf hg ?_ finrank_planeCircle_eq
  filter_upwards [isOpen_coneNegGood.mem_nhds hy] with y' hy'
  exact solidNegChart_solidNegSection hy'

theorem mfderiv_solidFoldPlus_bijective (x : solidSet.{u}) :
    Bijective (mfderiv (𝓡∂ 3) (𝓡∂ 3) solidFoldPlus x) := by
  have hy := coneGood_of_mem_solidSet x
  refine ConeFilling.bijective_mfderiv_of_comp (g := Subtype.val) (K := 𝓡 3)
    (mobiusBundleAtlas.contMDiff_subtype_val.mdifferentiableAt (by simp))
    (contMDiff_solidFoldPlus.mdifferentiableAt (by simp))
    (mobiusBundleAtlas.mfderiv_subtypeVal_bijective _) ?_
  have hval : MDifferentiableAt (𝓡∂ 3) PlaneCircleModel (Subtype.val : solidSet.{u} → _) x :=
    solidAtlas.contMDiff_subtype_val.mdifferentiableAt (by simp)
  have hS : MDifferentiableAt PlaneCircleModel (𝓡 3) (fun y => lensUp.{u} (solidSection y))
      x.val :=
    (contMDiff_lensUp.contMDiffAt.comp _ (contMDiffAt_solidSection hy)).mdifferentiableAt
      (by simp)
  change Bijective (mfderiv (𝓡∂ 3) (𝓡 3)
    ((fun y => lensUp.{u} (solidSection y)) ∘ Subtype.val) x)
  rw [mfderiv_comp x hS hval, ContinuousLinearMap.coe_comp]
  exact (mfderiv_solidSection_bijective hy).comp (solidAtlas.mfderiv_subtypeVal_bijective x)

theorem mfderiv_solidFoldMinus_bijective (x : solidSet.{u}) :
    Bijective (mfderiv (𝓡∂ 3) (𝓡∂ 3) solidFoldMinus x) := by
  have hy := coneNegGood_of_mem_solidSet x
  refine ConeFilling.bijective_mfderiv_of_comp (g := Subtype.val) (K := 𝓡 3)
    (mobiusBundleAtlas.contMDiff_subtype_val.mdifferentiableAt (by simp))
    (contMDiff_solidFoldMinus.mdifferentiableAt (by simp))
    (mobiusBundleAtlas.mfderiv_subtypeVal_bijective _) ?_
  have hval : MDifferentiableAt (𝓡∂ 3) PlaneCircleModel (Subtype.val : solidSet.{u} → _) x :=
    solidAtlas.contMDiff_subtype_val.mdifferentiableAt (by simp)
  have hS : MDifferentiableAt PlaneCircleModel (𝓡 3) (fun y => lensUp.{u} (solidNegSection y))
      x.val :=
    (contMDiff_lensUp.contMDiffAt.comp _ (contMDiffAt_solidNegSection hy)).mdifferentiableAt
      (by simp)
  change Bijective (mfderiv (𝓡∂ 3) (𝓡 3)
    ((fun y => lensUp.{u} (solidNegSection y)) ∘ Subtype.val) x)
  rw [mfderiv_comp x hS hval, ContinuousLinearMap.coe_comp]
  exact (mfderiv_solidNegSection_bijective hy).comp (solidAtlas.mfderiv_subtypeVal_bijective x)

def pantsOfBundle (y : mobiusBundleSet.{u}) : PlaneLift.{u} × Circle :=
  (ULift.up (mobiusBundleBase y), unitOf (mobiusBundleFibre y))

theorem pantsOfBundle_mem {y : mobiusBundleSet.{u}} (hy : mobiusBundleBase y ∈ planarModel 3) :
    pantsOfBundle y ∈ productSet.{u} 3 :=
  (mem_planarSet_iff (Or.inr rfl) _).mpr hy

theorem pantsOfBundle_mobiusPantsFold (x : productSet.{u} 3) :
    pantsOfBundle (mobiusPantsFold x) = x.val := by
  rw [pantsOfBundle, mobiusBundleBase_mobiusPantsFold, mobiusBundleFibre_mobiusPantsFold,
    unitOf_circle]

theorem mobiusBundleFibre_eq_unitOf (y : mobiusBundleSet.{u}) (h1 : mobiusBundleBase y ≠ 3 / 2)
    (h2 : mobiusBundleBase y ≠ -(3 / 2)) :
    (unitOf (mobiusBundleFibre y) : ℂ) = mobiusBundleFibre y := by
  have hn := norm_mobiusBundleFibre y h1 h2
  have hne : mobiusBundleFibre y ≠ 0 := by
    intro h0
    rw [h0, norm_zero] at hn
    exact zero_ne_one hn
  rw [coe_unitOf hne, hn, inv_one, one_smul]

theorem mobiusPantsFold_ofBundle {y : mobiusBundleSet.{u}}
    (hy : mobiusBundleBase y ∈ planarModel 3) :
    mobiusPantsFold ⟨pantsOfBundle y, pantsOfBundle_mem hy⟩ = y := by
  obtain ⟨-, h1, h2⟩ := planarModel_three_ne hy
  refine eq_of_mobiusBundleBase_eq_of_fibre_eq _ _ ?_ ?_ ?_ ?_
  · rw [mobiusBundleBase_mobiusPantsFold]
    exact h1
  · rw [mobiusBundleBase_mobiusPantsFold]
    exact h2
  · rw [mobiusBundleBase_mobiusPantsFold]
    rfl
  · rw [mobiusBundleFibre_mobiusPantsFold]
    exact mobiusBundleFibre_eq_unitOf y h1 h2

theorem contMDiffAt_unitOf_fibre {y : mobiusBundleSet.{u}} (h1 : mobiusBundleBase y ≠ 3 / 2)
    (h2 : mobiusBundleBase y ≠ -(3 / 2)) :
    ContMDiffAt (𝓡∂ 3) (𝓡 1) ∞ (fun y => unitOf (mobiusBundleFibre y)) y := by
  have hn := norm_mobiusBundleFibre y h1 h2
  have hne : mobiusBundleFibre y ≠ 0 := by
    intro h0
    rw [h0, norm_zero] at hn
    exact zero_ne_one hn
  exact (contMDiffOn_unitOf.contMDiffAt (isOpen_ne.mem_nhds hne)).comp y
    (contMDiffAt_mobiusBundleFibre y h1 h2)

theorem contMDiffAt_pantsOfBundle {y : mobiusBundleSet.{u}} (h1 : mobiusBundleBase y ≠ 3 / 2)
    (h2 : mobiusBundleBase y ≠ -(3 / 2)) :
    ContMDiffAt (𝓡∂ 3) PlaneCircleModel ∞ pantsOfBundle.{u} y :=
  (contMDiff_planeLift_up.comp contMDiff_mobiusBundleBase).contMDiffAt.prodMk
    (contMDiffAt_unitOf_fibre h1 h2)

instance : Nonempty mobiusBundleSet.{u} := ⟨mobiusPantsFold (Classical.arbitrary _)⟩

theorem mobiusSeamPoint_mem (j : Fin 3) (hj : j.val ≠ 0) (t : Torus) {s : ℝ} (hs : -1 < s)
    (hs1 : s < 1) : mobiusSeamPoint.{u} j t s ∈ mobiusBundleSet.{u} := by
  obtain ⟨y, hy, -, -⟩ := exists_mobiusSeamPoint.{u} j hj t hs hs1
  exact hy ▸ y.2

open Classical in
def mobiusSeamMap (j : Fin 3) (hj : j.val ≠ 0) (y : Torus × ℝ) : mobiusBundleSet.{u} :=
  if h : -1 < y.2 ∧ y.2 < 1 then ⟨mobiusSeamPoint j y.1 y.2, mobiusSeamPoint_mem j hj y.1 h.1 h.2⟩
  else Classical.arbitrary _

def mobiusSeamInv (j : Fin 3) (y : mobiusBundleSet.{u}) : Torus × ℝ :=
  ((unitOf (mobiusBundleFibre y),
    unitOf (mobiusBundleFibre y) ^ 2 * (unitOf (mobiusBundleBase y - planarCenter 3 j))⁻¹),
    4 * ‖mobiusBundleBase y - planarCenter 3 j‖ - 2)

def mobiusSeamTarget (j : Fin 3) : Set mobiusBundleSet.{u} :=
  {y | -1 < 4 * ‖mobiusBundleBase y - planarCenter 3 j‖ - 2 ∧
    4 * ‖mobiusBundleBase y - planarCenter 3 j‖ - 2 < 1}

theorem mobiusSeamMap_val (j : Fin 3) (hj : j.val ≠ 0) {y : Torus × ℝ}
    (hy : y ∈ signedCollarSource) : (mobiusSeamMap.{u} j hj y).val = mobiusSeamPoint j y.1 y.2 := by
  rw [mobiusSeamMap, dite_eq_left (show -1 < y.2 ∧ y.2 < 1 from hy)]

theorem mobiusSeamMap_base_fibre (j : Fin 3) (hj : j.val ≠ 0) {y : Torus × ℝ}
    (hy : y ∈ signedCollarSource) :
    mobiusBundleBase (mobiusSeamMap.{u} j hj y) = seamBasePoint j y.1 y.2 ∧
      mobiusBundleFibre (mobiusSeamMap.{u} j hj y) = (y.1.1 : ℂ) := by
  obtain ⟨z, hz, hb, hf⟩ := exists_mobiusSeamPoint.{u} j hj y.1 hy.1 hy.2
  have h : mobiusSeamMap.{u} j hj y = z := Subtype.ext ((mobiusSeamMap_val j hj hy).trans hz.symm)
  rw [h]
  exact ⟨hb, hf⟩

theorem seamTarget_ne (j : Fin 3) (hj : j.val ≠ 0) {J : ℂ}
    (h1 : 1 / 4 < ‖J - planarCenter 3 j‖) (h2 : ‖J - planarCenter 3 j‖ < 3 / 4) :
    J ≠ 3 / 2 ∧ J ≠ -(3 / 2) ∧ J - planarCenter 3 j ≠ 0 := by
  have h0 : J - planarCenter 3 j ≠ 0 := by
    intro h
    rw [h, norm_zero] at h1
    norm_num at h1
  rcases planarCenter_hole j hj with hc | hc
  · rw [hc] at h1 h2
    refine ⟨fun h => ?_, fun h => ?_, h0⟩
    · rw [h] at h1
      norm_num at h1
    · rw [h] at h2
      norm_num at h2
  · rw [hc] at h1 h2
    refine ⟨fun h => ?_, fun h => ?_, h0⟩
    · rw [h] at h2
      norm_num at h2
    · rw [h] at h1
      norm_num at h1

theorem circle_sq_mul_inv_inv (a b : Circle) : a ^ 2 * (a ^ 2 * b⁻¹)⁻¹ = b := by
  rw [mul_inv_rev, inv_inv, mul_comm b, mul_inv_cancel_left]

theorem coe_seamTerm (t : Torus) :
    (t.1 : ℂ) ^ 2 * ((t.2⁻¹ : Circle) : ℂ) = ((t.1 ^ 2 * t.2⁻¹ : Circle) : ℂ) := by
  rw [Circle.coe_mul, Circle.coe_pow]

def mobiusSeam (j : Fin 3) (hj : j.val ≠ 0) :
    PartialDiffeomorph signedCollarModel (𝓡∂ 3) (Torus × ℝ) mobiusBundleSet.{u} ∞ where
  toFun := mobiusSeamMap j hj
  invFun := mobiusSeamInv j
  source := signedCollarSource
  target := mobiusSeamTarget j
  map_source' y hy := by
    obtain ⟨hb, -⟩ := mobiusSeamMap_base_fibre.{u} j hj hy
    change -1 < 4 * ‖mobiusBundleBase _ - planarCenter 3 j‖ - 2 ∧
      4 * ‖mobiusBundleBase _ - planarCenter 3 j‖ - 2 < 1
    rw [hb, norm_seamBasePoint_sub j y.1 (by linarith [hy.1])]
    exact ⟨by linarith [hy.1], by linarith [hy.2]⟩
  map_target' y hy := hy
  left_inv' y hy := by
    obtain ⟨hb, hf⟩ := mobiusSeamMap_base_fibre.{u} j hj hy
    have hsub : mobiusBundleBase (mobiusSeamMap.{u} j hj y) - planarCenter 3 j =
        ((1 / 2 + y.2 / 4 : ℝ) : ℂ) * ((y.1.1 ^ 2 * y.1.2⁻¹ : Circle) : ℂ) := by
      rw [hb, seamBasePoint, add_sub_cancel_left, coe_seamTerm]
    have hpos : (0 : ℝ) < 1 / 2 + y.2 / 4 := by linarith [hy.1]
    change ((unitOf (mobiusBundleFibre _), unitOf (mobiusBundleFibre _) ^ 2 *
      (unitOf (mobiusBundleBase _ - planarCenter 3 j))⁻¹),
      4 * ‖mobiusBundleBase _ - planarCenter 3 j‖ - 2) = y
    rw [hf, hsub, unitOf_circle, unitOf_ofReal_mul hpos, circle_sq_mul_inv_inv, norm_mul,
      Circle.norm_coe, mul_one, Complex.norm_real, Real.norm_of_nonneg hpos.le]
    exact Prod.ext rfl (by ring)
  right_inv' y hy := by
    have hy1 : 1 / 4 < ‖mobiusBundleBase y - planarCenter 3 j‖ := by linarith [hy.1]
    have hy2 : ‖mobiusBundleBase y - planarCenter 3 j‖ < 3 / 4 := by linarith [hy.2]
    obtain ⟨h1, h2, h0⟩ := seamTarget_ne j hj hy1 hy2
    apply Subtype.ext
    rw [mobiusSeamMap_val j hj hy]
    refine (eq_mobiusSeamPoint j hj _ hy.1 hy.2 y ?_ ?_).symm
    · change mobiusBundleBase y = (planarCenter 3 j : ℂ) +
        ((1 / 2 + (4 * ‖mobiusBundleBase y - planarCenter 3 j‖ - 2) / 4 : ℝ) : ℂ) *
          ((unitOf (mobiusBundleFibre y) : ℂ) ^ 2 * (((unitOf (mobiusBundleFibre y) ^ 2 *
            (unitOf (mobiusBundleBase y - planarCenter 3 j))⁻¹)⁻¹ : Circle) : ℂ))
      rw [← Circle.coe_pow, ← Circle.coe_mul, circle_sq_mul_inv_inv,
        show (1 / 2 + (4 * ‖mobiusBundleBase y - planarCenter 3 j‖ - 2) / 4 : ℝ) =
          ‖mobiusBundleBase y - planarCenter 3 j‖ by ring, coe_norm_mul_unitOf]
      ring
    · exact (mobiusBundleFibre_eq_unitOf y h1 h2).symm
  open_source := isOpen_signedCollarSource
  open_target := by
    have hn : Continuous fun y : mobiusBundleSet.{u} =>
        4 * ‖mobiusBundleBase y - planarCenter 3 j‖ - 2 :=
      (continuous_const.mul (continuous_norm.comp
        (contMDiff_mobiusBundleBase.continuous.sub continuous_const))).sub continuous_const
    exact (isOpen_lt continuous_const hn).inter (isOpen_lt hn continuous_const)
  contMDiffOn_toFun := by
    refine (mobiusBundleAtlas.contMDiffOn_iff_subtype_val _ _).mpr fun y hy => ?_
    exact ((contMDiffAt_mobiusSeamPoint j hj hy.1 hy.2).contMDiffWithinAt).congr
      (fun y' hy' => mobiusSeamMap_val j hj hy') (mobiusSeamMap_val j hj hy)
  contMDiffOn_invFun := by
    intro y hy
    have hy1 : 1 / 4 < ‖mobiusBundleBase y - planarCenter 3 j‖ := by linarith [hy.1]
    have hy2 : ‖mobiusBundleBase y - planarCenter 3 j‖ < 3 / 4 := by linarith [hy.2]
    obtain ⟨h1, h2, h0⟩ := seamTarget_ne j hj hy1 hy2
    have hJ : ContMDiffAt (𝓡∂ 3) 𝓘(ℝ, ℂ) ∞
        (fun y : mobiusBundleSet.{u} => mobiusBundleBase y - planarCenter 3 j) y :=
      contMDiff_mobiusBundleBase.contMDiffAt.sub contMDiffAt_const
    have hU : ContMDiffAt (𝓡∂ 3) (𝓡 1) ∞
        (fun y : mobiusBundleSet.{u} => unitOf (mobiusBundleBase y - planarCenter 3 j)) y :=
      (contMDiffOn_unitOf.contMDiffAt (isOpen_ne.mem_nhds h0)).comp y hJ
    have hF := contMDiffAt_unitOf_fibre h1 h2
    have hN : ContMDiffAt (𝓡∂ 3) 𝓘(ℝ, ℝ) ∞
        (fun y : mobiusBundleSet.{u} => 4 * ‖mobiusBundleBase y - planarCenter 3 j‖ - 2) y :=
      (contMDiffAt_const.mul ((contDiffAt_norm ℝ h0).contMDiffAt.comp y hJ)).sub
        contMDiffAt_const
    exact ((hF.prodMk (((contMDiff_pow 2).contMDiffAt.comp y hF).mul hU.inv)).prodMk
      hN).contMDiffWithinAt

theorem mobiusSeam_apply_val (j : Fin 3) (hj : j.val ≠ 0) {y : Torus × ℝ}
    (hy : y ∈ signedCollarSource) : (mobiusSeam.{u} j hj y).val = mobiusSeamPoint j y.1 y.2 :=
  mobiusSeamMap_val j hj hy

theorem mobiusSeam_base (j : Fin 3) (hj : j.val ≠ 0) {y : mobiusBundleSet.{u}}
    (hy : y ∈ (mobiusSeam.{u} j hj).target) :
    1 / 4 < ‖mobiusBundleBase y - planarCenter 3 j‖ ∧
      ‖mobiusBundleBase y - planarCenter 3 j‖ < 3 / 4 :=
  ⟨by linarith [hy.1], by linarith [hy.2]⟩

abbrev MobiusCut : Type u := productSet.{u} 3 ⊕ (solidSet.{u} ⊕ solidSet.{u})

def mobiusSolidFold : solidSet.{u} ⊕ solidSet.{u} → mobiusBundleSet.{u} :=
  Sum.elim solidFoldPlus solidFoldMinus

def mobiusFold : MobiusCut.{u} → mobiusBundleSet.{u} := Sum.elim mobiusPantsFold mobiusSolidFold

theorem contMDiff_mobiusSolidFold : ContMDiff (𝓡∂ 3) (𝓡∂ 3) ∞ mobiusSolidFold.{u} :=
  ContMDiff.sumElim contMDiff_solidFoldPlus contMDiff_solidFoldMinus

theorem contMDiff_mobiusFold : ContMDiff (𝓡∂ 3) (𝓡∂ 3) ∞ mobiusFold.{u} :=
  ContMDiff.sumElim contMDiff_mobiusPantsFold contMDiff_mobiusSolidFold

theorem bijective_mfderiv_sumElim {M M' N : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanHalfSpace 3) M] [TopologicalSpace M']
    [ChartedSpace (EuclideanHalfSpace 3) M'] [TopologicalSpace N]
    [ChartedSpace (EuclideanHalfSpace 3) N] {f : M → N} {g : M' → N}
    (hf : ContMDiff (𝓡∂ 3) (𝓡∂ 3) ∞ f) (hg : ContMDiff (𝓡∂ 3) (𝓡∂ 3) ∞ g)
    (hfb : ∀ x, Bijective (mfderiv (𝓡∂ 3) (𝓡∂ 3) f x))
    (hgb : ∀ x, Bijective (mfderiv (𝓡∂ 3) (𝓡∂ 3) g x)) (x : M ⊕ M') :
    Bijective (mfderiv (𝓡∂ 3) (𝓡∂ 3) (Sum.elim f g) x) := by
  have hF : MDifferentiableAt (𝓡∂ 3) (𝓡∂ 3) (Sum.elim f g) x :=
    (ContMDiff.sumElim hf hg).mdifferentiableAt (by simp)
  rcases x with a | b
  · have hi : MDifferentiableAt (𝓡∂ 3) (𝓡∂ 3) (Sum.inl : M → M ⊕ M') a :=
      (ContMDiff.inl : ContMDiff (𝓡∂ 3) (𝓡∂ 3) ∞ (Sum.inl : M → M ⊕ M')).mdifferentiableAt
        (by simp)
    have h := mfderiv_comp a hF hi
    rw [hasMFDerivAt_inl.mfderiv] at h
    have hb := hfb a
    change Bijective (mfderiv (𝓡∂ 3) (𝓡∂ 3) (Sum.elim f g ∘ (Sum.inl : M → M ⊕ M')) a) at hb
    rw [h] at hb
    exact hb
  · have hi : MDifferentiableAt (𝓡∂ 3) (𝓡∂ 3) (Sum.inr : M' → M ⊕ M') b :=
      (ContMDiff.inr : ContMDiff (𝓡∂ 3) (𝓡∂ 3) ∞ (Sum.inr : M' → M ⊕ M')).mdifferentiableAt
        (by simp)
    have h := mfderiv_comp b hF hi
    rw [hasMFDerivAt_inr.mfderiv] at h
    have hb := hgb b
    change Bijective (mfderiv (𝓡∂ 3) (𝓡∂ 3) (Sum.elim f g ∘ (Sum.inr : M' → M ⊕ M')) b) at hb
    rw [h] at hb
    exact hb

theorem mfderiv_mobiusFold_bijective (x : MobiusCut.{u}) :
    Bijective (mfderiv (𝓡∂ 3) (𝓡∂ 3) mobiusFold x) :=
  bijective_mfderiv_sumElim contMDiff_mobiusPantsFold contMDiff_mobiusSolidFold
    mfderiv_mobiusPantsFold_bijective
    (bijective_mfderiv_sumElim contMDiff_solidFoldPlus contMDiff_solidFoldMinus
      mfderiv_solidFoldPlus_bijective mfderiv_solidFoldMinus_bijective) x

def mobiusCutOrientation : ManifoldOrientation (𝓡∂ 3) MobiusCut.{u} 3 :=
  Manifold.manifoldOrientationPullback (𝓡∂ 3) (𝓡∂ 3) finrank_euclideanSpace_fin mobiusFold
    contMDiff_mobiusFold mfderiv_mobiusFold_bijective mobiusBundleCarrier.{u}.orientation

theorem orientation_map_mobiusCutOrientation (x : MobiusCut.{u}) :
    Orientation.map (Fin 3) (Manifold.differentialEquivOfBijective (𝓡∂ 3) (𝓡∂ 3) mobiusFold
      mfderiv_mobiusFold_bijective x).toLinearEquiv (mobiusCutOrientation.orientation x) =
      mobiusBundleCarrier.{u}.orientation.orientation (mobiusFold x) :=
  Manifold.orientation_map_manifoldOrientationPullback (𝓡∂ 3) (𝓡∂ 3) finrank_euclideanSpace_fin
    mobiusFold contMDiff_mobiusFold mfderiv_mobiusFold_bijective
    mobiusBundleCarrier.{u}.orientation x

abbrev mobiusCutCarrier : CompactCarrier.{u} where
  kind := .withBoundary
  Carrier := MobiusCut.{u}
  charts := (inferInstance : ChartedSpace (EuclideanHalfSpace 3) MobiusCut.{u})
  smooth := (inferInstance : IsManifold (𝓡∂ 3) ∞ MobiusCut.{u})
  orientation := mobiusCutOrientation

def holeOf (i : Fin 2) : Fin 3 := i.succ

theorem holeOf_ne (i : Fin 2) : (holeOf i).val ≠ 0 := Nat.succ_ne_zero _

theorem holeOf_injective : Injective holeOf := Fin.succ_injective 2

def solidInner :
    Fin 2 → PartialDiffeomorph (𝓡∂ 3) (𝓡∂ 3) solidSet.{u} (solidSet.{u} ⊕ solidSet.{u}) ∞ :=
  ![partialDiffeomorphSumInl, partialDiffeomorphSumInr]

def solidInto (i : Fin 2) : PartialDiffeomorph (𝓡∂ 3) (𝓡∂ 3) solidSet.{u} MobiusCut.{u} ∞ :=
  (solidInner i).trans partialDiffeomorphSumInr

def solidPick (i : Fin 2) (b : solidSet.{u}) : solidSet.{u} ⊕ solidSet.{u} :=
  ![Sum.inl b, Sum.inr b] i

theorem solidInto_apply (i : Fin 2) (b : solidSet.{u}) :
    solidInto i b = (Sum.inr (solidPick i b) : MobiusCut.{u}) := by
  fin_cases i <;> rfl

theorem solidInto_source (i : Fin 2) : (solidInto.{u} i).source = univ := by
  fin_cases i <;> exact eq_univ_of_forall fun _ => ⟨trivial, trivial⟩

def solidFoldAt (i : Fin 2) : solidSet.{u} → mobiusBundleSet.{u} :=
  ![solidFoldPlus, solidFoldMinus] i

theorem mobiusFold_solidInto (i : Fin 2) (b : solidSet.{u}) :
    mobiusFold (solidInto i b) = solidFoldAt i b := by
  fin_cases i <;> rfl

theorem solidFoldAt_injective (i : Fin 2) : Injective (solidFoldAt.{u} i) := by
  fin_cases i
  exacts [solidFoldPlus_injective, solidFoldMinus_injective]

theorem solidFoldAt_collar (i : Fin 2) (t : Torus) {σ : ℝ} (hσ : 0 ≤ σ) (hσ1 : σ < 1) :
    (solidFoldAt i (solidCollar.{u} 2 (t, halfPoint σ hσ))).val =
      mobiusSeamPoint (holeOf i) t (-σ) := by
  fin_cases i
  exacts [solidFoldPlus_collar_eq_seam t hσ hσ1, solidFoldMinus_collar_eq_seam t hσ hσ1]

theorem pantsFold_hole_eq (i : Fin 2) (t : Torus) :
    mobiusPantsFold (productCollar.{u} 3 (Or.inr rfl) (holeOf i) (seamMatching t, halfZero)) =
      solidFoldAt i (solidCollar.{u} 2 (t, halfZero)) := by
  fin_cases i
  exacts [mobiusPantsFold_hole_one_eq t, mobiusPantsFold_hole_two_eq t]

theorem planarCenter_holeOf (i : Fin 2) :
    (planarCenter 3 (holeOf i) : ℂ) = ![3 / 2, -(3 / 2)] i := by
  fin_cases i
  · change ((planarCenter 3 1 : ℝ) : ℂ) = 3 / 2
    rw [planarCenter_three_one]
    push_cast
    ring
  · change ((planarCenter 3 2 : ℝ) : ℂ) = -(3 / 2)
    rw [planarCenter_three_two]
    push_cast
    ring

theorem norm_base_solidFoldAt (i : Fin 2) (b : solidSet.{u}) :
    ‖mobiusBundleBase (solidFoldAt i b) - planarCenter 3 (holeOf i)‖ ≤ 1 / 2 := by
  rw [planarCenter_holeOf]
  fin_cases i
  · exact norm_mobiusBundleBase_solidFoldPlus_sub b
  · have h := norm_mobiusBundleBase_solidFoldMinus_add b
    change ‖mobiusBundleBase (solidFoldMinus b) - -(3 / 2)‖ ≤ 1 / 2
    rwa [sub_neg_eq_add]

def mobiusLeftCollar (i : Fin 2) :
    PartialDiffeomorph halfCollarModel (𝓡∂ 3) (Torus × EuclideanHalfSpace 1) MobiusCut.{u} ∞ :=
  (solidCollar 2).trans (solidInto i)

def mobiusRightCollar (i : Fin 2) :
    PartialDiffeomorph halfCollarModel (𝓡∂ 3) (Torus × EuclideanHalfSpace 1) MobiusCut.{u} ∞ :=
  (productCollar 3 (Or.inr rfl) (holeOf i)).trans partialDiffeomorphSumInl

theorem mobiusLeftCollar_source (i : Fin 2) :
    (mobiusLeftCollar.{u} i).source = halfCollarSource := by
  change (solidCollar.{u} 2).source ∩ _ ⁻¹' (solidInto.{u} i).source = _
  rw [solidInto_source, preimage_univ, inter_univ]
  rfl

theorem mobiusRightCollar_source (i : Fin 2) :
    (mobiusRightCollar.{u} i).source = halfCollarSource := by
  change (productCollar.{u} 3 (Or.inr rfl) (holeOf i)).source ∩ _ ⁻¹' univ = _
  rw [preimage_univ, inter_univ]
  rfl

def mobiusLeftTorus (i : Fin 2) (t : Torus) : MobiusCut.{u} := mobiusLeftCollar i (t, halfZero)

def mobiusRightTorus (i : Fin 2) (t : Torus) : MobiusCut.{u} := mobiusRightCollar i (t, halfZero)

theorem mobiusLeftTorus_eq (i : Fin 2) (t : Torus) :
    mobiusLeftTorus.{u} i t = solidInto i (solidCollar 2 (t, halfZero)) := rfl

theorem mobiusRightTorus_eq (i : Fin 2) (t : Torus) :
    mobiusRightTorus.{u} i t = Sum.inl (productCollar 3 (Or.inr rfl) (holeOf i) (t, halfZero)) :=
  rfl

theorem continuous_mobiusLeftTorus (i : Fin 2) : Continuous (mobiusLeftTorus.{u} i) :=
  ((mobiusLeftCollar i).contMDiffOn.comp_contMDiff (contMDiff_id.prodMk contMDiff_const)
    (fun t => mobiusLeftCollar_source i ▸ zero_mem_halfCollarSource t)).continuous

theorem continuous_mobiusRightTorus (i : Fin 2) : Continuous (mobiusRightTorus.{u} i) :=
  ((mobiusRightCollar i).contMDiffOn.comp_contMDiff (contMDiff_id.prodMk contMDiff_const)
    (fun t => mobiusRightCollar_source i ▸ zero_mem_halfCollarSource t)).continuous

theorem injective_mobiusLeftTorus (i : Fin 2) : Injective (mobiusLeftTorus.{u} i) := fun t s h =>
  congrArg Prod.fst ((mobiusLeftCollar i).toOpenPartialHomeomorph.injOn
    (mobiusLeftCollar_source i ▸ zero_mem_halfCollarSource t)
    (mobiusLeftCollar_source i ▸ zero_mem_halfCollarSource s) h)

theorem injective_mobiusRightTorus (i : Fin 2) : Injective (mobiusRightTorus.{u} i) :=
  fun t s h => congrArg Prod.fst ((mobiusRightCollar i).toOpenPartialHomeomorph.injOn
    (mobiusRightCollar_source i ▸ zero_mem_halfCollarSource t)
    (mobiusRightCollar_source i ▸ zero_mem_halfCollarSource s) h)

def mobiusLeftParam (i : Fin 2) : Torus ≃ₜ range (mobiusLeftTorus.{u} i) :=
  ((continuous_mobiusLeftTorus i).isClosedEmbedding
    (injective_mobiusLeftTorus i)).isEmbedding.toHomeomorph

def mobiusRightParam (i : Fin 2) : Torus ≃ₜ range (mobiusRightTorus.{u} i) :=
  ((continuous_mobiusRightTorus i).isClosedEmbedding
    (injective_mobiusRightTorus i)).isEmbedding.toHomeomorph

def mobiusAttaching (i : Fin 2) : range (mobiusLeftTorus.{u} i) ≃ₜ range (mobiusRightTorus.{u} i) :=
  (mobiusLeftParam i).symm.trans (seamMatching.toHomeomorph.trans (mobiusRightParam i))

theorem mobiusAttaching_leftParam (i : Fin 2) (t : Torus) :
    mobiusAttaching.{u} i (mobiusLeftParam i t) = mobiusRightParam i (seamMatching t) := by
  simp [mobiusAttaching]

theorem mobiusAttaching_val (i : Fin 2) (t : Torus) (h : mobiusLeftTorus.{u} i t ∈ range
    (mobiusLeftTorus i)) :
    (mobiusAttaching i ⟨mobiusLeftTorus i t, h⟩ : MobiusCut.{u}) =
      mobiusRightTorus i (seamMatching t) := by
  have hl : (⟨mobiusLeftTorus i t, h⟩ : range (mobiusLeftTorus.{u} i)) = mobiusLeftParam i t :=
    Subtype.ext rfl
  rw [hl, mobiusAttaching_leftParam]
  rfl

theorem mobiusAttaching_symm_val (i : Fin 2) (t : Torus)
    (h : mobiusRightTorus.{u} i t ∈ range (mobiusRightTorus i)) :
    ((mobiusAttaching i).symm ⟨mobiusRightTorus i t, h⟩ : MobiusCut.{u}) =
      mobiusLeftTorus i (seamMatching.symm t) := by
  have hr : (⟨mobiusRightTorus i t, h⟩ : range (mobiusRightTorus.{u} i)) =
      mobiusAttaching i (mobiusLeftParam i (seamMatching.symm t)) := by
    rw [mobiusAttaching_leftParam, Diffeomorph.apply_symm_apply]
    exact Subtype.ext rfl
  rw [hr, Homeomorph.symm_apply_apply]
  rfl

theorem solidPick_ne {i j : Fin 2} (hij : i ≠ j) (b b' : solidSet.{u}) :
    solidPick i b ≠ solidPick j b' := by
  fin_cases i <;> fin_cases j
  · exact absurd rfl hij
  · exact Sum.inl_ne_inr
  · exact Sum.inr_ne_inl
  · exact absurd rfl hij

def mobiusGluing : BoundaryGluing MobiusCut.{u} (Fin 2) where
  left i := range (mobiusLeftTorus i)
  right i := range (mobiusRightTorus i)
  attaching i := mobiusAttaching i
  isClosed_left i := isClosed_range_of_continuous_of_compactSpace (continuous_mobiusLeftTorus i)
  isClosed_right i := isClosed_range_of_continuous_of_compactSpace (continuous_mobiusRightTorus i)
  disjoint_left_right i := by
    rw [Set.disjoint_left]
    rintro _ ⟨t, rfl⟩ ⟨s, hs⟩
    rw [mobiusLeftTorus_eq, solidInto_apply, mobiusRightTorus_eq] at hs
    exact Sum.inl_ne_inr hs
  disjoint_blocks i j hij := by
    rw [Set.disjoint_left]
    rintro _ (⟨t, rfl⟩ | ⟨t, rfl⟩) (⟨s, hs⟩ | ⟨s, hs⟩)
    · rw [mobiusLeftTorus_eq, mobiusLeftTorus_eq, solidInto_apply, solidInto_apply] at hs
      exact solidPick_ne hij.symm _ _ (Sum.inr_injective hs)
    · rw [mobiusLeftTorus_eq, solidInto_apply, mobiusRightTorus_eq] at hs
      exact Sum.inl_ne_inr hs
    · rw [mobiusLeftTorus_eq, solidInto_apply, mobiusRightTorus_eq] at hs
      exact Sum.inr_ne_inl hs
    · rw [mobiusRightTorus_eq, mobiusRightTorus_eq] at hs
      exact ConeFilling.productCollar_ne (holeOf_injective.ne hij.symm) s t (Sum.inl_injective hs)

theorem mobiusFold_leftTorus (i : Fin 2) (t : Torus) :
    mobiusFold (mobiusLeftTorus.{u} i t) = solidFoldAt i (solidCollar 2 (t, halfZero)) :=
  mobiusFold_solidInto i _

theorem mobiusFold_rightTorus_matching (i : Fin 2) (t : Torus) :
    mobiusFold (mobiusRightTorus.{u} i (seamMatching t)) =
      solidFoldAt i (solidCollar 2 (t, halfZero)) :=
  pantsFold_hole_eq i t

theorem mobiusFold_rightTorus (i : Fin 2) (τ : Torus) :
    mobiusFold (mobiusRightTorus.{u} i τ) =
      mobiusFold (mobiusLeftTorus i (seamMatching.symm τ)) := by
  rw [mobiusFold_leftTorus, ← mobiusFold_rightTorus_matching, Diffeomorph.apply_symm_apply]

theorem mobiusGluing_rel_left_right (i : Fin 2) (t : Torus) :
    mobiusGluing.{u}.rel (mobiusLeftTorus i t) (mobiusRightTorus i (seamMatching t)) := by
  refine Or.inr ⟨i, Or.inl ⟨t, rfl⟩, ?_⟩
  rw [mobiusGluing.flip_of_mem_left ⟨t, rfl⟩]
  exact (mobiusAttaching_val i t _).symm

theorem mobiusFold_eq_of_rel {x y : MobiusCut.{u}} (h : mobiusGluing.rel x y) :
    mobiusFold x = mobiusFold y := by
  rcases h with rfl | ⟨i, hx, rfl⟩
  · rfl
  · rcases hx with hx | hx
    · obtain ⟨t, rfl⟩ := id hx
      rw [mobiusGluing.flip_of_mem_left hx]
      change mobiusFold (mobiusLeftTorus i t) =
        mobiusFold (mobiusAttaching i ⟨mobiusLeftTorus i t, hx⟩ : _)
      rw [mobiusAttaching_val i t hx, mobiusFold_leftTorus, mobiusFold_rightTorus_matching]
    · obtain ⟨τ, rfl⟩ := id hx
      rw [mobiusGluing.flip_of_mem_right hx]
      change mobiusFold (mobiusRightTorus i τ) =
        mobiusFold ((mobiusAttaching i).symm ⟨mobiusRightTorus i τ, hx⟩ : _)
      rw [mobiusAttaching_symm_val i τ hx, mobiusFold_rightTorus]

theorem planarSign_hole {j : Fin 3} (hj : j.val ≠ 0) : planarSign j = 1 := by
  simp [planarSign, hj]

theorem planarRadius_hole {j : Fin 3} (hj : j.val ≠ 0) : planarRadius j = 1 / 2 := by
  simp [planarRadius, hj]

theorem exists_productCollar_hole {j : Fin 3} (hj : j.val ≠ 0) {a : productSet.{u} 3}
    (ha : ‖a.val.1.down - planarCenter 3 j‖ = 1 / 2) :
    ∃ τ, productCollar.{u} 3 (Or.inr rfl) j (τ, halfZero) = a := by
  set P := productCollar.{u} 3 (Or.inr rfl) j
  have hmem : a ∈ P.target := by
    change planarSign j * (‖a.val.1.down - planarCenter 3 j‖ - planarRadius j) < 1 / 4
    rw [planarSign_hole hj, planarRadius_hole hj, ha]
    norm_num
  have h2 : P.symm a = ((P.symm a).1, halfZero) := by
    refine Prod.ext rfl ?_
    change Manifold.halfSpaceOneLift (4 * (planarSign j *
      (‖a.val.1.down - planarCenter 3 j‖ - planarRadius j))) = halfZero
    rw [planarSign_hole hj, planarRadius_hole hj, ha, sub_self, mul_zero, mul_zero,
      ← halfPoint_eq_halfSpaceOneLift 0 le_rfl]
    rfl
  exact ⟨(P.symm a).1, by rw [← h2]; exact P.right_inv hmem⟩

theorem mobiusGluing_rel_inl_solid {a : productSet.{u} 3} {i : Fin 2} {b : solidSet.{u}}
    (h : mobiusPantsFold a = solidFoldAt i b) :
    mobiusGluing.rel (Sum.inl a) (solidInto i b) := by
  have hb := norm_base_solidFoldAt i b
  rw [← h, mobiusBundleBase_mobiusPantsFold] at hb
  have hm : 1 / 2 ≤ ‖a.val.1.down - planarCenter 3 (holeOf i)‖ :=
    ((mem_planarSet_iff (Or.inr rfl) a.val.1).mp a.2).2 (holeOf i) (holeOf_ne i)
  obtain ⟨τ, hτ⟩ := exists_productCollar_hole (holeOf_ne i) (le_antisymm hb hm)
  have hb' : b = solidCollar 2 (seamMatching.symm τ, halfZero) := by
    apply solidFoldAt_injective i
    rw [← h, ← hτ, ← pantsFold_hole_eq, Diffeomorph.apply_symm_apply]
  have hl : solidInto i b = mobiusLeftTorus i (seamMatching.symm τ) := by
    rw [hb']
    rfl
  have hr : (Sum.inl a : MobiusCut.{u}) =
      mobiusRightTorus i (seamMatching (seamMatching.symm τ)) := by
    rw [Diffeomorph.apply_symm_apply, ← hτ]
    rfl
  rw [hl, hr]
  exact mobiusGluing.isEquivalence_rel.symm (mobiusGluing_rel_left_right i _)

theorem solidFoldAt_eq_index {i i' : Fin 2} {b b' : solidSet.{u}}
    (h : solidFoldAt i b = solidFoldAt i' b') : i = i' := by
  by_contra hne
  have h1 := norm_base_solidFoldAt i b
  have h2 := norm_base_solidFoldAt i' b'
  rw [h] at h1
  have key : ‖(planarCenter 3 (holeOf i) : ℂ) - planarCenter 3 (holeOf i')‖ ≤ 1 := by
    calc _ ≤ ‖(planarCenter 3 (holeOf i) : ℂ) - mobiusBundleBase (solidFoldAt i' b')‖ +
          ‖mobiusBundleBase (solidFoldAt i' b') - planarCenter 3 (holeOf i')‖ :=
          norm_sub_le_norm_sub_add_norm_sub _ _ _
      _ ≤ 1 := by
          rw [norm_sub_rev]
          linarith
  rw [planarCenter_holeOf, planarCenter_holeOf] at key
  fin_cases i <;> fin_cases i'
  · exact hne rfl
  · norm_num at key
  · norm_num at key
  · exact hne rfl

theorem mobiusCut_cases (x : MobiusCut.{u}) :
    (∃ a, x = Sum.inl a) ∨ ∃ i b, x = solidInto i b := by
  rcases x with a | b | b
  · exact Or.inl ⟨a, rfl⟩
  · exact Or.inr ⟨0, b, rfl⟩
  · exact Or.inr ⟨1, b, rfl⟩

theorem mobiusGluing_rel_of_fold_eq {x y : MobiusCut.{u}} (h : mobiusFold x = mobiusFold y) :
    mobiusGluing.rel x y := by
  rcases mobiusCut_cases x with ⟨a, rfl⟩ | ⟨i, b, rfl⟩ <;>
    rcases mobiusCut_cases y with ⟨a', rfl⟩ | ⟨i', b', rfl⟩
  · exact Or.inl (congrArg Sum.inl (mobiusPantsFold_injective h))
  · rw [mobiusFold_solidInto] at h
    exact mobiusGluing_rel_inl_solid h
  · rw [mobiusFold_solidInto] at h
    exact mobiusGluing.isEquivalence_rel.symm (mobiusGluing_rel_inl_solid h.symm)
  · rw [mobiusFold_solidInto, mobiusFold_solidInto] at h
    obtain rfl := solidFoldAt_eq_index h
    rw [solidFoldAt_injective i h]
    exact Or.inl rfl

theorem surjective_mobiusFold : Surjective mobiusFold.{u} := by
  intro y
  by_cases hJ : mobiusBundleBase y ∈ planarModel 3
  · exact ⟨Sum.inl ⟨pantsOfBundle y, pantsOfBundle_mem hJ⟩, mobiusPantsFold_ofBundle hJ⟩
  · have h3 := mobiusBundleBase_norm_le y
    rw [mem_planarModel_three] at hJ
    have e1 : ((3 / 2 : ℝ) : ℂ) = 3 / 2 := by push_cast; ring
    have e2 : ((-(3 / 2) : ℝ) : ℂ) = -(3 / 2) := by push_cast; ring
    rw [e1, e2] at hJ
    by_cases h1 : ‖mobiusBundleBase y - 3 / 2‖ < 1 / 2
    · exact ⟨solidInto 0 ⟨solidChart y.val, solidChart_mem y h1.le⟩,
        (mobiusFold_solidInto 0 _).trans (solidFoldPlus_chart y h1.le)⟩
    · have h2 : ‖mobiusBundleBase y + 3 / 2‖ < 1 / 2 := by
        by_contra h2
        exact hJ ⟨h3, not_lt.mp h1, by rw [sub_neg_eq_add]; exact not_lt.mp h2⟩
      exact ⟨solidInto 1 ⟨solidNegChart y.val, solidNegChart_mem y h2.le⟩,
        (mobiusFold_solidInto 1 _).trans (solidFoldMinus_chart y h2.le)⟩

def mobiusQuotientMap : Quotient mobiusGluing.{u}.setoid → mobiusBundleSet.{u} :=
  Quotient.lift mobiusFold (fun _ _ h => mobiusFold_eq_of_rel h)

theorem bijective_mobiusQuotientMap : Bijective mobiusQuotientMap.{u} := by
  constructor
  · intro q q' h
    induction q using Quotient.inductionOn with
    | h x =>
      induction q' using Quotient.inductionOn with
      | h y => exact Quotient.sound (mobiusGluing_rel_of_fold_eq h)
  · intro p
    obtain ⟨x, hx⟩ := surjective_mobiusFold p
    exact ⟨Quotient.mk _ x, hx⟩

def mobiusReconstruction : Quotient mobiusGluing.{u}.setoid ≃ₜ mobiusBundleSet.{u} :=
  Continuous.homeoOfEquivCompactToT2 (f := Equiv.ofBijective _ bijective_mobiusQuotientMap)
    (continuous_quot_lift _ contMDiff_mobiusFold.continuous)

theorem mobiusReconstruction_mk (x : MobiusCut.{u}) :
    mobiusReconstruction (Quotient.mk _ x) = mobiusFold x := rfl

theorem isInteriorPoint_inl_iff {M M' : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanHalfSpace 3) M] [TopologicalSpace M']
    [ChartedSpace (EuclideanHalfSpace 3) M'] (a : M) :
    (𝓡∂ 3).IsInteriorPoint (Sum.inl a : M ⊕ M') ↔ (𝓡∂ 3).IsInteriorPoint a :=
  ⟨fun h => ModelWithCorners.isInteriorPoint_disjointUnion_left h rfl,
    ModelWithCorners.interiorPoint_inl a⟩

theorem isInteriorPoint_inr_iff {M M' : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanHalfSpace 3) M] [TopologicalSpace M']
    [ChartedSpace (EuclideanHalfSpace 3) M'] (b : M') :
    (𝓡∂ 3).IsInteriorPoint (Sum.inr b : M ⊕ M') ↔ (𝓡∂ 3).IsInteriorPoint b :=
  ⟨fun h => ModelWithCorners.isInteriorPoint_disjointUnion_right h rfl,
    ModelWithCorners.interiorPoint_inr b⟩

theorem isInteriorPoint_solidInto_iff (i : Fin 2) (b : solidSet.{u}) :
    (𝓡∂ 3).IsInteriorPoint (solidInto i b) ↔ (𝓡∂ 3).IsInteriorPoint b := by
  rw [solidInto_apply, isInteriorPoint_inr_iff]
  fin_cases i
  · exact isInteriorPoint_inl_iff b
  · exact isInteriorPoint_inr_iff b

theorem isBoundaryPoint_inl_iff (a : productSet.{u} 3) :
    (𝓡∂ 3).IsBoundaryPoint (Sum.inl a : MobiusCut.{u}) ↔ (𝓡∂ 3).IsBoundaryPoint a := by
  rw [ModelWithCorners.isBoundaryPoint_iff_not_isInteriorPoint,
    ModelWithCorners.isBoundaryPoint_iff_not_isInteriorPoint, isInteriorPoint_inl_iff]

theorem isBoundaryPoint_solidInto_iff (i : Fin 2) (b : solidSet.{u}) :
    (𝓡∂ 3).IsBoundaryPoint (solidInto i b) ↔ (𝓡∂ 3).IsBoundaryPoint b := by
  rw [ModelWithCorners.isBoundaryPoint_iff_not_isInteriorPoint,
    ModelWithCorners.isBoundaryPoint_iff_not_isInteriorPoint, isInteriorPoint_solidInto_iff]

def mobiusCutExternal : BoundaryTori mobiusCutCarrier.{u} 1 where
  collar _ := (productCollar 3 (Or.inr rfl) 0).trans partialDiffeomorphSumInl
  source_eq _ := by
    change (productCollar.{u} 3 (Or.inr rfl) 0).source ∩ _ ⁻¹' univ = _
    rw [preimage_univ, inter_univ]
    rfl
  boundary_zero _ t := (isBoundaryPoint_inl_iff _).mpr
    ((productBoundaryTori.{u} 3 (Or.inr rfl)).boundary_zero 0 t)
  disjoint i j hij := (hij (Subsingleton.elim i j)).elim

theorem mobiusCutExternal_torusMap (k : Fin 1) (t : Torus) :
    mobiusCutExternal.{u}.torusMap k t =
      Sum.inl (productCollar 3 (Or.inr rfl) 0 (t, halfZero)) := rfl

theorem exists_holeOf {j : Fin 3} (hj : j ≠ 0) : ∃ i, holeOf i = j := by
  fin_cases j
  · exact absurd rfl hj
  · exact ⟨0, rfl⟩
  · exact ⟨1, rfl⟩

theorem holeOf_ne_zero (i : Fin 2) : holeOf i ≠ 0 := Fin.succ_ne_zero i

theorem mem_mobiusCutBoundary_iff (x : MobiusCut.{u}) :
    x ∈ (⋃ i, mobiusGluing.{u}.block i) ∪ mobiusCutExternal.image ↔
      (∃ i t, mobiusLeftTorus i t = x) ∨ (∃ i t, mobiusRightTorus i t = x) ∨
        ∃ t, Sum.inl (productCollar 3 (Or.inr rfl) 0 (t, halfZero)) = x := by
  simp only [mem_union, mem_iUnion, BoundaryTori.image, mem_range, mobiusCutExternal_torusMap]
  constructor
  · rintro (⟨i, ⟨t, ht⟩ | ⟨t, ht⟩⟩ | ⟨-, t, ht⟩)
    · exact Or.inl ⟨i, t, ht⟩
    · exact Or.inr (Or.inl ⟨i, t, ht⟩)
    · exact Or.inr (Or.inr ⟨t, ht⟩)
  · rintro (⟨i, t, ht⟩ | ⟨i, t, ht⟩ | ⟨t, ht⟩)
    · exact Or.inl ⟨i, Or.inl ⟨t, ht⟩⟩
    · exact Or.inl ⟨i, Or.inr ⟨t, ht⟩⟩
    · exact Or.inr ⟨0, t, ht⟩

theorem mobiusCut_boundary : (𝓡∂ 3).boundary MobiusCut.{u} =
    (⋃ i, mobiusGluing.block i) ∪ mobiusCutExternal.image := by
  ext x
  rw [mem_mobiusCutBoundary_iff]
  change (𝓡∂ 3).IsBoundaryPoint x ↔ _
  rcases mobiusCut_cases x with ⟨a, rfl⟩ | ⟨i, b, rfl⟩
  · rw [isBoundaryPoint_inl_iff, ConeFilling.productSet_isBoundaryPoint_iff']
    constructor
    · rintro ⟨j, t, rfl⟩
      by_cases hj : j = 0
      · subst hj
        exact Or.inr (Or.inr ⟨t, rfl⟩)
      · obtain ⟨i, rfl⟩ := exists_holeOf hj
        exact Or.inr (Or.inl ⟨i, t, rfl⟩)
    · rintro (⟨i, t, ht⟩ | ⟨i, t, ht⟩ | ⟨t, ht⟩)
      · rw [mobiusLeftTorus_eq, solidInto_apply] at ht
        exact absurd ht Sum.inr_ne_inl
      · exact ⟨holeOf i, t, Sum.inl_injective ht⟩
      · exact ⟨0, t, Sum.inl_injective ht⟩
  · rw [isBoundaryPoint_solidInto_iff]
    have h0 : (𝓡∂ 3).IsBoundaryPoint b ↔ b ∈ (𝓡∂ 3).boundary solidSet.{u} := Iff.rfl
    rw [h0, solidSet_boundary_eq 2, mem_range]
    constructor
    · rintro ⟨t, rfl⟩
      exact Or.inl ⟨i, t, rfl⟩
    · rintro (⟨i', t, ht⟩ | ⟨i', t, ht⟩ | ⟨t, ht⟩)
      · rw [mobiusLeftTorus_eq, solidInto_apply, solidInto_apply] at ht
        have hs := Sum.inr_injective ht
        by_cases hii : i' = i
        · subst hii
          refine ⟨t, ?_⟩
          fin_cases i'
          · exact Sum.inl_injective hs
          · exact Sum.inr_injective hs
        · exact absurd hs (solidPick_ne hii _ _)
      · rw [mobiusRightTorus_eq, solidInto_apply] at ht
        exact absurd ht Sum.inl_ne_inr
      · rw [solidInto_apply] at ht
        exact absurd ht Sum.inl_ne_inr

theorem mobiusCut_external_disjoint :
    Disjoint (⋃ i, mobiusGluing.{u}.block i) mobiusCutExternal.image := by
  rw [Set.disjoint_left]
  intro x hx hy
  simp only [BoundaryTori.image, mem_iUnion, mem_range, mobiusCutExternal_torusMap] at hy
  obtain ⟨-, s, rfl⟩ := hy
  obtain ⟨i, hi⟩ := mem_iUnion.mp hx
  rcases hi with ⟨t, ht⟩ | ⟨t, ht⟩
  · rw [mobiusLeftTorus_eq, solidInto_apply] at ht
    exact Sum.inr_ne_inl ht
  · rw [mobiusRightTorus_eq] at ht
    exact ConeFilling.productCollar_ne (holeOf_ne_zero i) t s (Sum.inl_injective ht)

theorem range_solidInto (i : Fin 2) : range (solidInto.{u} i) = (solidInto.{u} i).target := by
  ext y
  constructor
  · rintro ⟨b, rfl⟩
    exact (solidInto i).map_source' (by rw [solidInto_source]; trivial)
  · intro hy
    exact ⟨(solidInto i).invFun y, (solidInto i).right_inv' hy⟩

theorem isOpen_range_solidInto (i : Fin 2) : IsOpen (range (solidInto.{u} i)) := by
  rw [range_solidInto]
  exact (solidInto i).open_target

theorem contMDiff_solidInto (i : Fin 2) : ContMDiff (𝓡∂ 3) (𝓡∂ 3) ∞ (solidInto.{u} i) := by
  have h := (solidInto.{u} i).contMDiffOn
  rw [solidInto_source] at h
  exact contMDiffOn_univ.mp h

theorem solidInto_left_inv (i : Fin 2) (b : solidSet.{u}) :
    (solidInto i).invFun (solidInto i b) = b :=
  (solidInto i).left_inv' (by rw [solidInto_source]; trivial)

def solidPieceOpen (i : Fin 2) : TopologicalSpace.Opens MobiusCut.{u} :=
  ⟨range (solidInto i), isOpen_range_solidInto i⟩

def solidPieceDiffeomorph (i : Fin 2) :
    solidPieceOpen.{u} i ≃ₘ⟮𝓡∂ 3, 𝓡∂ 3⟯ solidSet.{u} where
  toFun y := (solidInto i).invFun y.val
  invFun b := ⟨solidInto i b, mem_range_self b⟩
  left_inv := by
    rintro ⟨_, b, rfl⟩
    exact Subtype.ext (by
      change solidInto i ((solidInto i).invFun (solidInto i b)) = solidInto i b
      rw [solidInto_left_inv])
  right_inv b := solidInto_left_inv i b
  contMDiff_toFun := (solidInto i).contMDiffOn_invFun.comp_contMDiff contMDiff_subtype_val
    (fun y => by
      obtain ⟨b, hb⟩ := y.2
      rw [← hb, ← range_solidInto]
      exact mem_range_self b)
  contMDiff_invFun := (ContMDiff.subtypeVal_comp_iff _ _).mp (contMDiff_solidInto i)

def pantsPieceOpen : TopologicalSpace.Opens MobiusCut.{u} := ⟨range Sum.inl, isOpen_range_inl⟩

def mobiusPieces (k : Fin 3) : TopologicalSpace.Opens MobiusCut.{u} :=
  Fin.cases pantsPieceOpen solidPieceOpen k

theorem mobiusPieces_succ (i : Fin 2) : mobiusPieces.{u} i.succ = solidPieceOpen i := rfl

theorem pieceInterior_pants :
    ((mobiusCutCarrier.{u}.pieceInterior pantsPieceOpen : Set MobiusCut.{u})) =
      Sum.inl '' (𝓡∂ 3).interior (productSet.{u} 3) := by
  ext x
  constructor
  · rintro ⟨⟨a, rfl⟩, hx⟩
    exact ⟨a, (isInteriorPoint_inl_iff a).mp hx, rfl⟩
  · rintro ⟨a, ha, rfl⟩
    exact ⟨⟨a, rfl⟩, (isInteriorPoint_inl_iff a).mpr ha⟩

theorem pieceInterior_solid (i : Fin 2) :
    ((mobiusCutCarrier.{u}.pieceInterior (solidPieceOpen i) : Set MobiusCut.{u})) =
      solidInto i '' (𝓡∂ 3).interior solidSet.{u} := by
  ext x
  constructor
  · rintro ⟨⟨b, rfl⟩, hx⟩
    exact ⟨b, (isInteriorPoint_solidInto_iff i b).mp hx, rfl⟩
  · rintro ⟨b, hb, rfl⟩
    exact ⟨⟨b, rfl⟩, (isInteriorPoint_solidInto_iff i b).mpr hb⟩

theorem disjoint_pants_solid (i : Fin 2) :
    Disjoint (pantsPieceOpen.{u} : Set MobiusCut.{u}) (solidPieceOpen i) := by
  rw [Set.disjoint_left]
  rintro _ ⟨a, rfl⟩ ⟨b, hb⟩
  rw [solidInto_apply] at hb
  exact Sum.inr_ne_inl hb

theorem disjoint_solid_solid {i j : Fin 2} (hij : i ≠ j) :
    Disjoint (solidPieceOpen.{u} i : Set MobiusCut.{u}) (solidPieceOpen j) := by
  rw [Set.disjoint_left]
  rintro _ ⟨b, rfl⟩ ⟨b', hb⟩
  rw [solidInto_apply, solidInto_apply] at hb
  exact solidPick_ne hij.symm _ _ (Sum.inr_injective hb)

abbrev mobiusComponents : mobiusCutCarrier.{u}.Components where
  count := 3
  count_pos := by decide
  piece := mobiusPieces
  closed i := by
    fin_cases i
    · exact isClosed_range_inl
    · exact (isCompact_range (contMDiff_solidInto 0).continuous).isClosed
    · exact (isCompact_range (contMDiff_solidInto 1).continuous).isClosed
  connected i := by
    have := connectedSpace_productSet.{u} (k := 3) (Or.inr rfl)
    fin_cases i
    · exact isConnected_iff_connectedSpace.mp (isConnected_range continuous_inl)
    · exact isConnected_iff_connectedSpace.mp
        (isConnected_range (contMDiff_solidInto 0).continuous)
    · exact isConnected_iff_connectedSpace.mp
        (isConnected_range (contMDiff_solidInto 1).continuous)
  disjoint i j h := by
    fin_cases i <;> fin_cases j
    · exact (h rfl).elim
    · exact disjoint_pants_solid 0
    · exact disjoint_pants_solid 1
    · exact (disjoint_pants_solid 0).symm
    · exact (h rfl).elim
    · exact disjoint_solid_solid (by decide)
    · exact (disjoint_pants_solid 1).symm
    · exact disjoint_solid_solid (by decide)
    · exact (h rfl).elim
  covers := by
    refine eq_univ_of_forall fun x => ?_
    rcases mobiusCut_cases x with ⟨a, rfl⟩ | ⟨i, b, rfl⟩
    · exact mem_iUnion.mpr ⟨0, a, rfl⟩
    · refine mem_iUnion.mpr ⟨i.succ, ?_⟩
      rw [mobiusPieces_succ]
      exact mem_range_self b
  interior_connected i := by
    have := connectedSpace_productSet.{u} (k := 3) (Or.inr rfl)
    fin_cases i
    · apply isConnected_iff_connectedSpace.mp
      change IsConnected (mobiusCutCarrier.{u}.pieceInterior pantsPieceOpen : Set MobiusCut.{u})
      rw [pieceInterior_pants]
      exact ConeFilling.isConnected_interior_of_connected.image _ continuous_inl.continuousOn
    · apply isConnected_iff_connectedSpace.mp
      change IsConnected (mobiusCutCarrier.{u}.pieceInterior (solidPieceOpen 0) :
        Set MobiusCut.{u})
      rw [pieceInterior_solid]
      exact ConeFilling.isConnected_interior_of_connected.image _
        (contMDiff_solidInto 0).continuous.continuousOn
    · apply isConnected_iff_connectedSpace.mp
      change IsConnected (mobiusCutCarrier.{u}.pieceInterior (solidPieceOpen 1) :
        Set MobiusCut.{u})
      rw [pieceInterior_solid]
      exact ConeFilling.isConnected_interior_of_connected.image _
        (contMDiff_solidInto 1).continuous.continuousOn

open Classical in
def pantsOf (y : mobiusBundleSet.{u}) : productSet.{u} 3 :=
  if h : mobiusBundleBase y ∈ planarModel 3 then ⟨pantsOfBundle y, pantsOfBundle_mem h⟩
  else Classical.arbitrary _

theorem pantsOf_val {y : mobiusBundleSet.{u}} (h : mobiusBundleBase y ∈ planarModel 3) :
    (pantsOf y).val = pantsOfBundle y := by
  rw [pantsOf, dite_eq_left h]

theorem mobiusPantsFold_pantsOf {y : mobiusBundleSet.{u}}
    (h : mobiusBundleBase y ∈ planarModel 3) : mobiusPantsFold (pantsOf y) = y := by
  have e : pantsOf y = ⟨pantsOfBundle y, pantsOfBundle_mem h⟩ := Subtype.ext (pantsOf_val h)
  rw [e]
  exact mobiusPantsFold_ofBundle h

theorem pantsOf_mobiusPantsFold (x : productSet.{u} 3) : pantsOf (mobiusPantsFold x) = x :=
  Subtype.ext ((pantsOf_val (mobiusPantsFold_mem_mobiusPants x)).trans
    (pantsOfBundle_mobiusPantsFold x))

theorem contMDiffAt_pantsOf {y : mobiusBundleSet.{u}} {U : Set mobiusBundleSet.{u}}
    (hU : IsOpen U) (hy : y ∈ U) (hUJ : ∀ z ∈ U, mobiusBundleBase z ∈ planarModel 3) :
    ContMDiffAt (𝓡∂ 3) (𝓡∂ 3) ∞ pantsOf y := by
  obtain ⟨-, h1, h2⟩ := planarModel_three_ne (hUJ y hy)
  have h : ContMDiffAt (𝓡∂ 3) PlaneCircleModel ∞ (Subtype.val ∘ pantsOf) y := by
    apply (contMDiffAt_pantsOfBundle h1 h2).congr_of_eventuallyEq
    filter_upwards [hU.mem_nhds hy] with z hz
    exact pantsOf_val (hUJ z hz)
  exact contMDiffWithinAt_univ.mp (((productAtlas.{u} 3).contMDiffWithinAt_iff_subtype_val
    pantsOf univ y).mpr h.contMDiffWithinAt)

open Classical in
def solidOf (y : mobiusBundleSet.{u}) : solidSet.{u} :=
  if h : solidChart y.val ∈ solidSet.{u} then ⟨solidChart y.val, h⟩ else Classical.arbitrary _

open Classical in
def solidNegOf (y : mobiusBundleSet.{u}) : solidSet.{u} :=
  if h : solidNegChart y.val ∈ solidSet.{u} then ⟨solidNegChart y.val, h⟩
  else Classical.arbitrary _

theorem solidOf_val {y : mobiusBundleSet.{u}} (h : solidChart y.val ∈ solidSet.{u}) :
    (solidOf y).val = solidChart y.val := by
  rw [solidOf, dite_eq_left h]

theorem solidNegOf_val {y : mobiusBundleSet.{u}} (h : solidNegChart y.val ∈ solidSet.{u}) :
    (solidNegOf y).val = solidNegChart y.val := by
  rw [solidNegOf, dite_eq_left h]

theorem solidFoldPlus_solidOf {y : mobiusBundleSet.{u}}
    (hy : ‖mobiusBundleBase y - 3 / 2‖ ≤ 1 / 2) : solidFoldPlus (solidOf y) = y := by
  have e : solidOf y = ⟨solidChart y.val, solidChart_mem y hy⟩ :=
    Subtype.ext (solidOf_val (solidChart_mem y hy))
  rw [e]
  exact solidFoldPlus_chart y hy

theorem solidFoldMinus_solidNegOf {y : mobiusBundleSet.{u}}
    (hy : ‖mobiusBundleBase y + 3 / 2‖ ≤ 1 / 2) : solidFoldMinus (solidNegOf y) = y := by
  have e : solidNegOf y = ⟨solidNegChart y.val, solidNegChart_mem y hy⟩ :=
    Subtype.ext (solidNegOf_val (solidNegChart_mem y hy))
  rw [e]
  exact solidFoldMinus_chart y hy

theorem solidOf_solidFoldPlus (x : solidSet.{u}) : solidOf (solidFoldPlus x) = x := by
  have h : solidChart (solidFoldPlus x).val ∈ solidSet.{u} := by
    rw [solidChart_solidFoldPlus]
    exact x.2
  exact Subtype.ext ((solidOf_val h).trans (solidChart_solidFoldPlus x))

theorem solidNegOf_solidFoldMinus (x : solidSet.{u}) : solidNegOf (solidFoldMinus x) = x := by
  have h : solidNegChart (solidFoldMinus x).val ∈ solidSet.{u} := by
    rw [solidNegChart_solidFoldMinus]
    exact x.2
  exact Subtype.ext ((solidNegOf_val h).trans (solidNegChart_solidFoldMinus x))

theorem continuous_baseNorm (c : ℂ) :
    Continuous fun y : mobiusBundleSet.{u} => ‖mobiusBundleBase y - c‖ :=
  continuous_norm.comp (contMDiff_mobiusBundleBase.continuous.sub continuous_const)

theorem contMDiffAt_solidOf {y : mobiusBundleSet.{u}}
    (hy : ‖mobiusBundleBase y - 3 / 2‖ < 1 / 2) :
    ContMDiffAt (𝓡∂ 3) (𝓡∂ 3) ∞ solidOf y := by
  have hne : mobiusBundleBase y ≠ -(3 / 2) := by
    intro h
    rw [h] at hy
    norm_num at hy
  obtain ⟨x, hx, h2, hab, hS, -⟩ := exists_sphere_rep_snd y hne
  have hU : IsOpen {z : mobiusBundleSet.{u} | ‖mobiusBundleBase z - 3 / 2‖ < 1 / 2} :=
    isOpen_lt (continuous_baseNorm _) continuous_const
  have h : ContMDiffAt (𝓡∂ 3) PlaneCircleModel ∞ (Subtype.val ∘ solidOf) y := by
    apply ((contMDiffAt_solidChart hx h2 hab hS).comp y
      (mobiusBundleAtlas.contMDiff_subtype_val y)).congr_of_eventuallyEq
    filter_upwards [hU.mem_nhds hy] with z hz
    exact solidOf_val (solidChart_mem z (le_of_lt hz))
  exact contMDiffWithinAt_univ.mp ((solidAtlas.contMDiffWithinAt_iff_subtype_val
    solidOf univ y).mpr h.contMDiffWithinAt)

theorem contMDiffAt_solidNegOf {y : mobiusBundleSet.{u}}
    (hy : ‖mobiusBundleBase y + 3 / 2‖ < 1 / 2) :
    ContMDiffAt (𝓡∂ 3) (𝓡∂ 3) ∞ solidNegOf y := by
  have hne : mobiusBundleBase y ≠ 3 / 2 := by
    intro h
    rw [h] at hy
    norm_num at hy
  obtain ⟨x, hx, h1, hab, hS, -⟩ := exists_sphere_rep_fst y hne
  have hU : IsOpen {z : mobiusBundleSet.{u} | ‖mobiusBundleBase z + 3 / 2‖ < 1 / 2} := by
    have e : (fun z : mobiusBundleSet.{u} => ‖mobiusBundleBase z + 3 / 2‖) =
        fun z => ‖mobiusBundleBase z - -(3 / 2)‖ := funext fun z => by rw [sub_neg_eq_add]
    exact isOpen_lt (by rw [e]; exact continuous_baseNorm _) continuous_const
  have h : ContMDiffAt (𝓡∂ 3) PlaneCircleModel ∞ (Subtype.val ∘ solidNegOf) y := by
    apply ((contMDiffAt_solidNegChart hx h1 hab hS).comp y
      (mobiusBundleAtlas.contMDiff_subtype_val y)).congr_of_eventuallyEq
    filter_upwards [hU.mem_nhds hy] with z hz
    exact solidNegOf_val (solidNegChart_mem z (le_of_lt hz))
  exact contMDiffWithinAt_univ.mp ((solidAtlas.contMDiffWithinAt_iff_subtype_val
    solidNegOf univ y).mpr h.contMDiffWithinAt)

theorem mem_planarModel_of_two_lt {z : ℂ} (hz : ‖z‖ ≤ 3) (h2 : 2 < ‖z‖) :
    z ∈ planarModel 3 := by
  rw [mem_planarModel_three]
  have b1 := (norm_sub_real_bounds z (3 / 2)).1
  have b2 := (norm_sub_real_bounds z (-(3 / 2))).1
  rw [abs_of_pos (by norm_num : (0 : ℝ) < 3 / 2)] at b1
  rw [abs_neg, abs_of_pos (by norm_num : (0 : ℝ) < 3 / 2)] at b2
  exact ⟨hz, by linarith, by linarith⟩

theorem mem_planarModel_of_outer {y : mobiusBundleSet.{u}} (h2 : 2 < ‖mobiusBundleBase y‖) :
    mobiusBundleBase y ∈ planarModel 3 :=
  mem_planarModel_of_two_lt (mobiusBundleBase_norm_le y) h2

def mobiusOuterLift :
    PartialDiffeomorph (𝓡∂ 3) (𝓡∂ 3) (productSet.{u} 3) mobiusBundleSet.{u} ∞ where
  toFun := mobiusPantsFold
  invFun := pantsOf
  source := {x | 2 < ‖x.val.1.down‖}
  target := {y | 2 < ‖mobiusBundleBase y‖}
  map_source' x hx := by
    change 2 < ‖mobiusBundleBase (mobiusPantsFold x)‖
    rw [mobiusBundleBase_mobiusPantsFold]
    exact hx
  map_target' y hy := by
    change 2 < ‖(pantsOf y).val.1.down‖
    rw [pantsOf_val (mem_planarModel_of_outer hy)]
    exact hy
  left_inv' x _ := pantsOf_mobiusPantsFold x
  right_inv' y hy := mobiusPantsFold_pantsOf (mem_planarModel_of_outer hy)
  open_source := isOpen_lt continuous_const (continuous_norm.comp (continuous_uliftDown.comp
    (continuous_fst.comp continuous_subtype_val)))
  open_target := isOpen_lt continuous_const
    (continuous_norm.comp contMDiff_mobiusBundleBase.continuous)
  contMDiffOn_toFun := contMDiff_mobiusPantsFold.contMDiffOn
  contMDiffOn_invFun y hy := (contMDiffAt_pantsOf (isOpen_lt continuous_const
    (continuous_norm.comp contMDiff_mobiusBundleBase.continuous)) hy
      (fun z hz => mem_planarModel_of_outer hz)).contMDiffWithinAt

theorem outer_far {x : productSet.{u} 3} (hx : x ∈ (productCollar 3 (Or.inr rfl) 0).target) :
    11 / 4 < ‖x.val.1.down‖ := by
  change planarSign (0 : Fin 3) * (‖x.val.1.down - planarCenter 3 0‖ - planarRadius (0 : Fin 3))
    < 1 / 4 at hx
  rw [show planarSign (0 : Fin 3) = -1 by simp [planarSign],
    show planarCenter 3 (0 : Fin 3) = 0 by simp [planarCenter],
    show planarRadius (0 : Fin 3) = 3 by simp [planarRadius], Complex.ofReal_zero, sub_zero] at hx
  linarith

theorem productCollar_zero_base (t : Torus) :
    ‖(productCollar.{u} 3 (Or.inr rfl) 0 (t, halfZero)).val.1.down‖ = 3 := by
  rw [show (productCollar.{u} 3 (Or.inr rfl) 0 (t, halfZero)).val.1.down =
    planarCircleMap 3 0 t.1 from planarCollar_zero_val.{u} (Or.inr rfl) 0 t.1]
  simp [planarCircleMap, planarCenter, planarRadius]

def mobiusExternalCollar :
    PartialDiffeomorph halfCollarModel (𝓡∂ 3) (Torus × EuclideanHalfSpace 1)
      mobiusBundleSet.{u} ∞ :=
  (productCollar 3 (Or.inr rfl) 0).trans mobiusOuterLift

theorem mobiusExternalCollar_source : mobiusExternalCollar.{u}.source = halfCollarSource := by
  ext p
  refine ⟨fun hp => hp.1, fun hp => ⟨hp, ?_⟩⟩
  change 2 < ‖(productCollar.{u} 3 (Or.inr rfl) 0 p).val.1.down‖
  linarith [outer_far ((productCollar.{u} 3 (Or.inr rfl) 0).map_source' hp)]

theorem mobiusExternalCollar_apply (p : Torus × EuclideanHalfSpace 1) :
    mobiusExternalCollar.{u} p = mobiusPantsFold (productCollar 3 (Or.inr rfl) 0 p) := rfl

def mobiusExternal : BoundaryTori mobiusBundleCarrier.{u} 1 where
  collar _ := mobiusExternalCollar
  source_eq _ := mobiusExternalCollar_source
  boundary_zero _ t := by
    change (𝓡∂ 3).IsBoundaryPoint (mobiusExternalCollar.{u} (t, halfZero))
    rw [mobiusBundleSet_isBoundaryPoint_iff_base, mobiusExternalCollar_apply,
      mobiusBundleBase_mobiusPantsFold, productCollar_zero_base]
  disjoint i j hij := (hij (Subsingleton.elim i j)).elim

theorem norm_planarCircleMap_hole_le (j : Fin 3) (hj : j ≠ 0) (t : Circle) :
    ‖planarCircleMap 3 j t‖ ≤ 2 := by
  have h := norm_planarCircleMap_sub 3 j t
  have hc : |planarCenter 3 j| = 3 / 2 := by
    fin_cases j
    · exact absurd rfl hj
    · simp [planarCenter]
      norm_num
    · simp [planarCenter]
      norm_num
  have hr : planarRadius j = 1 / 2 := planarRadius_hole (fun h0 => hj (Fin.ext h0))
  have hb := (norm_sub_real_bounds (planarCircleMap 3 j t) (planarCenter 3 j)).1
  rw [h, hc, hr] at hb
  linarith

theorem isBoundaryPoint_iff_external (y : mobiusBundleSet.{u}) :
    (𝓡∂ 3).IsBoundaryPoint y ↔ ∃ t, mobiusExternalCollar.{u} (t, halfZero) = y := by
  rw [mobiusBundleSet_isBoundaryPoint_iff_base]
  constructor
  · intro h3
    have hJ : mobiusBundleBase y ∈ planarModel 3 := mem_planarModel_of_outer (by rw [h3]; norm_num)
    have hx : (pantsOf y).val.1.down = mobiusBundleBase y := by
      rw [pantsOf_val hJ]
      rfl
    have hb : (𝓡∂ 3).IsBoundaryPoint (pantsOf y) := by
      rw [productSet_isBoundaryPoint_iff, planarFunction_three, hx, h3]
      ring
    obtain ⟨j, τ, hτ⟩ := (ConeFilling.productSet_isBoundaryPoint_iff' (pantsOf y)).mp hb
    have hj : j = 0 := by
      by_contra hj
      have h2 := norm_planarCircleMap_hole_le j hj τ.1
      rw [← planarCollar_zero_val.{u} (Or.inr rfl) j τ.1] at h2
      change ‖(productCollar.{u} 3 (Or.inr rfl) j (τ, halfZero)).val.1.down‖ ≤ 2 at h2
      rw [hτ, hx, h3] at h2
      norm_num at h2
    subst hj
    refine ⟨τ, ?_⟩
    rw [mobiusExternalCollar_apply, hτ]
    exact mobiusPantsFold_pantsOf hJ
  · rintro ⟨t, rfl⟩
    rw [mobiusExternalCollar_apply, mobiusBundleBase_mobiusPantsFold, productCollar_zero_base]

theorem cast_three_halves_sub (z : ℂ) : z - ((3 / 2 : ℝ) : ℂ) = z - 3 / 2 := by
  push_cast
  ring

theorem cast_neg_three_halves_sub (z : ℂ) : z - ((-(3 / 2) : ℝ) : ℂ) = z + 3 / 2 := by
  push_cast
  ring

theorem mem_planarModel_three' (z : ℂ) :
    z ∈ planarModel 3 ↔ ‖z‖ ≤ 3 ∧ 1 / 2 ≤ ‖z - 3 / 2‖ ∧ 1 / 2 ≤ ‖z + 3 / 2‖ := by
  rw [mem_planarModel_three, cast_three_halves_sub, cast_neg_three_halves_sub]

theorem planarFunction_three_neg_iff' (z : ℂ) :
    planarFunction 3 z < 0 ↔ ‖z‖ < 3 ∧ 1 / 2 < ‖z - 3 / 2‖ ∧ 1 / 2 < ‖z + 3 / 2‖ := by
  rw [ConeFilling.planarFunction_three_neg_iff, cast_three_halves_sub, cast_neg_three_halves_sub]

theorem far_of_near_plus {J : ℂ} (h : ‖J - 3 / 2‖ < 1 / 2) : ‖J‖ < 3 ∧ 5 / 2 < ‖J + 3 / 2‖ := by
  have h1 := norm_sub_norm_le J (3 / 2)
  have h2 := norm_sub_le (J + 3 / 2) (J - 3 / 2)
  rw [show J + 3 / 2 - (J - 3 / 2) = 3 by ring] at h2
  norm_num at h1 h2
  constructor <;> linarith

theorem far_of_near_minus {J : ℂ} (h : ‖J + 3 / 2‖ < 1 / 2) : ‖J‖ < 3 ∧ 5 / 2 < ‖J - 3 / 2‖ := by
  have h1 := norm_sub_norm_le J (-(3 / 2))
  have h2 := norm_sub_le (J + 3 / 2) (J - 3 / 2)
  rw [show J + 3 / 2 - (J - 3 / 2) = 3 by ring] at h2
  rw [sub_neg_eq_add] at h1
  norm_num at h1 h2
  constructor <;> linarith

theorem norm_base_sub_solidFoldPlus (b : solidSet.{u}) :
    ‖mobiusBundleBase (solidFoldPlus b) - 3 / 2‖ = ‖b.val.1.down‖ ^ 2 / 18 := by
  rw [mobiusBundleBase_solidFoldPlus, add_sub_cancel_left, norm_div, norm_mul, norm_pow,
    Circle.norm_coe, mul_one]
  norm_num

theorem norm_base_add_solidFoldMinus (b : solidSet.{u}) :
    ‖mobiusBundleBase (solidFoldMinus b) + 3 / 2‖ = ‖b.val.1.down‖ ^ 2 / 18 := by
  rw [mobiusBundleBase_solidFoldMinus, neg_add_cancel_comm, norm_div, norm_mul, norm_pow,
    Circle.norm_coe, mul_one]
  norm_num

theorem continuous_baseNormAdd (c : ℂ) :
    Continuous fun y : mobiusBundleSet.{u} => ‖mobiusBundleBase y + c‖ :=
  continuous_norm.comp (contMDiff_mobiusBundleBase.continuous.add continuous_const)

def mobiusInteriorImage : TopologicalSpace.Opens mobiusBundleSet.{u} :=
  ⟨{y | ‖mobiusBundleBase y‖ < 3 ∧ ‖mobiusBundleBase y - 3 / 2‖ ≠ 1 / 2 ∧
      ‖mobiusBundleBase y + 3 / 2‖ ≠ 1 / 2},
    (isOpen_lt (continuous_norm.comp contMDiff_mobiusBundleBase.continuous) continuous_const).inter
      ((isOpen_ne_fun (continuous_baseNorm _) continuous_const).inter
        (isOpen_ne_fun (continuous_baseNormAdd _) continuous_const))⟩

theorem mem_interiorImage_of_near_plus {y : mobiusBundleSet.{u}}
    (h : ‖mobiusBundleBase y - 3 / 2‖ < 1 / 2) : y ∈ mobiusInteriorImage.{u} := by
  obtain ⟨h0, h2⟩ := far_of_near_plus h
  exact ⟨h0, h.ne, by intro e; rw [e] at h2; norm_num at h2⟩

theorem mem_interiorImage_of_near_minus {y : mobiusBundleSet.{u}}
    (h : ‖mobiusBundleBase y + 3 / 2‖ < 1 / 2) : y ∈ mobiusInteriorImage.{u} := by
  obtain ⟨h0, h2⟩ := far_of_near_minus h
  exact ⟨h0, by intro e; rw [e] at h2; norm_num at h2, h.ne⟩

theorem mobiusFold_mem_interiorImage (x : mobiusCutCarrier.{u}.interior) :
    mobiusFold x.val ∈ mobiusInteriorImage.{u} := by
  obtain ⟨x, hx⟩ := x
  change (𝓡∂ 3).IsInteriorPoint x at hx
  rcases mobiusCut_cases x with ⟨a, rfl⟩ | ⟨i, b, rfl⟩
  · have ha := (ConeFilling.productSet_isInteriorPoint_iff a).mp ((isInteriorPoint_inl_iff a).mp hx)
    obtain ⟨h1, h2, h3⟩ := (planarFunction_three_neg_iff' _).mp ha
    change mobiusPantsFold a ∈ mobiusInteriorImage.{u}
    refine ⟨?_, ?_, ?_⟩ <;> rw [mobiusBundleBase_mobiusPantsFold]
    · exact h1
    · exact h2.ne'
    · exact h3.ne'
  · have hb := (solidSet_isInteriorPoint_iff b).mp ((isInteriorPoint_solidInto_iff i b).mp hx)
    have hb2 : ‖b.val.1.down‖ ^ 2 / 18 < 1 / 2 := by nlinarith [norm_nonneg b.val.1.down]
    change mobiusFold (solidInto i b) ∈ mobiusInteriorImage.{u}
    rw [mobiusFold_solidInto]
    fin_cases i
    · exact mem_interiorImage_of_near_plus (by
        change ‖mobiusBundleBase (solidFoldPlus b) - 3 / 2‖ < 1 / 2
        rw [norm_base_sub_solidFoldPlus]
        exact hb2)
    · exact mem_interiorImage_of_near_minus (by
        change ‖mobiusBundleBase (solidFoldMinus b) + 3 / 2‖ < 1 / 2
        rw [norm_base_add_solidFoldMinus]
        exact hb2)

theorem solidOf_interior {y : mobiusBundleSet.{u}} (h : ‖mobiusBundleBase y - 3 / 2‖ < 1 / 2) :
    (𝓡∂ 3).IsInteriorPoint (solidOf y) := by
  have hne : mobiusBundleBase y ≠ -(3 / 2) := by
    intro e
    rw [e] at h
    norm_num at h
  rw [solidSet_isInteriorPoint_iff, solidOf_val (solidChart_mem y h.le)]
  have hn := norm_solidChart_sq y hne
  nlinarith [norm_nonneg (solidChart y.val).1.down]

theorem solidNegOf_interior {y : mobiusBundleSet.{u}} (h : ‖mobiusBundleBase y + 3 / 2‖ < 1 / 2) :
    (𝓡∂ 3).IsInteriorPoint (solidNegOf y) := by
  have hne : mobiusBundleBase y ≠ 3 / 2 := by
    intro e
    rw [e] at h
    norm_num at h
  rw [solidSet_isInteriorPoint_iff, solidNegOf_val (solidNegChart_mem y h.le)]
  have hn := norm_solidNegChart_sq y hne
  nlinarith [norm_nonneg (solidNegChart y.val).1.down]

theorem mem_planarModel_of_far {y : mobiusBundleSet.{u}}
    (h1 : 1 / 2 < ‖mobiusBundleBase y - 3 / 2‖) (h2 : 1 / 2 < ‖mobiusBundleBase y + 3 / 2‖) :
    mobiusBundleBase y ∈ planarModel 3 :=
  (mem_planarModel_three' _).mpr ⟨mobiusBundleBase_norm_le y, h1.le, h2.le⟩

theorem pantsOf_interior {y : mobiusBundleSet.{u}} (h0 : ‖mobiusBundleBase y‖ < 3)
    (h1 : 1 / 2 < ‖mobiusBundleBase y - 3 / 2‖) (h2 : 1 / 2 < ‖mobiusBundleBase y + 3 / 2‖) :
    (𝓡∂ 3).IsInteriorPoint (pantsOf y) := by
  rw [ConeFilling.productSet_isInteriorPoint_iff, pantsOf_val (mem_planarModel_of_far h1 h2)]
  exact (planarFunction_three_neg_iff' _).mpr ⟨h0, h1, h2⟩

theorem far_of_interiorImage (y : mobiusInteriorImage.{u})
    (h1 : ¬ ‖mobiusBundleBase y.val - 3 / 2‖ < 1 / 2)
    (h2 : ¬ ‖mobiusBundleBase y.val + 3 / 2‖ < 1 / 2) :
    1 / 2 < ‖mobiusBundleBase y.val - 3 / 2‖ ∧ 1 / 2 < ‖mobiusBundleBase y.val + 3 / 2‖ :=
  ⟨lt_of_le_of_ne (not_lt.mp h1) (Ne.symm y.2.2.1),
    lt_of_le_of_ne (not_lt.mp h2) (Ne.symm y.2.2.2)⟩

open Classical in
def mobiusInteriorBackward (y : mobiusInteriorImage.{u}) : mobiusCutCarrier.{u}.interior :=
  if h1 : ‖mobiusBundleBase y.val - 3 / 2‖ < 1 / 2 then
    ⟨solidInto 0 (solidOf y.val), (isInteriorPoint_solidInto_iff 0 _).mpr (solidOf_interior h1)⟩
  else if h2 : ‖mobiusBundleBase y.val + 3 / 2‖ < 1 / 2 then
    ⟨solidInto 1 (solidNegOf y.val),
      (isInteriorPoint_solidInto_iff 1 _).mpr (solidNegOf_interior h2)⟩
  else
    ⟨Sum.inl (pantsOf y.val), (isInteriorPoint_inl_iff _).mpr (pantsOf_interior y.2.1
      (far_of_interiorImage y h1 h2).1 (far_of_interiorImage y h1 h2).2)⟩

theorem contMDiff_mobiusInteriorBackward_val :
    ContMDiff (𝓡∂ 3) (𝓡∂ 3) ∞
      (fun y : mobiusInteriorImage.{u} => (mobiusInteriorBackward y).val) := by
  intro y
  have hval : ContMDiffAt (𝓡∂ 3) (𝓡∂ 3) ∞ (Subtype.val : mobiusInteriorImage.{u} → _) y :=
    contMDiff_subtype_val y
  have c1 : Continuous fun z : mobiusInteriorImage.{u} => ‖mobiusBundleBase z.val - 3 / 2‖ :=
    (continuous_baseNorm _).comp continuous_subtype_val
  have c2 : Continuous fun z : mobiusInteriorImage.{u} => ‖mobiusBundleBase z.val + 3 / 2‖ :=
    (continuous_baseNormAdd _).comp continuous_subtype_val
  by_cases h1 : ‖mobiusBundleBase y.val - 3 / 2‖ < 1 / 2
  · have hs : ContMDiffAt (𝓡∂ 3) (𝓡∂ 3) ∞
        (fun z : mobiusInteriorImage.{u} => solidInto 0 (solidOf z.val)) y :=
      (contMDiff_solidInto 0).contMDiffAt.comp y ((contMDiffAt_solidOf h1).comp y hval)
    apply hs.congr_of_eventuallyEq
    filter_upwards [(isOpen_lt c1 continuous_const).mem_nhds h1] with z hz
    have hz' : ‖mobiusBundleBase z.val - 3 / 2‖ < 1 / 2 := hz
    change (mobiusInteriorBackward z).val = _
    rw [mobiusInteriorBackward, dite_eq_left hz']
  · by_cases h2 : ‖mobiusBundleBase y.val + 3 / 2‖ < 1 / 2
    · have hs : ContMDiffAt (𝓡∂ 3) (𝓡∂ 3) ∞
          (fun z : mobiusInteriorImage.{u} => solidInto 1 (solidNegOf z.val)) y :=
        (contMDiff_solidInto 1).contMDiffAt.comp y ((contMDiffAt_solidNegOf h2).comp y hval)
      apply hs.congr_of_eventuallyEq
      filter_upwards [(isOpen_lt c2 continuous_const).mem_nhds h2] with z hz
      have hz' : ‖mobiusBundleBase z.val + 3 / 2‖ < 1 / 2 := hz
      have hz1 : ¬ ‖mobiusBundleBase z.val - 3 / 2‖ < 1 / 2 := by
        have := (far_of_near_minus hz').2
        linarith
      change (mobiusInteriorBackward z).val = _
      rw [mobiusInteriorBackward, dite_eq_right hz1, dite_eq_left hz']
    · obtain ⟨g1, g2⟩ := far_of_interiorImage y h1 h2
      have hU : IsOpen {z : mobiusBundleSet.{u} | 1 / 2 < ‖mobiusBundleBase z - 3 / 2‖ ∧
          1 / 2 < ‖mobiusBundleBase z + 3 / 2‖} :=
        (isOpen_lt continuous_const (continuous_baseNorm _)).inter
          (isOpen_lt continuous_const (continuous_baseNormAdd _))
      have hs : ContMDiffAt (𝓡∂ 3) (𝓡∂ 3) ∞
          (fun z : mobiusInteriorImage.{u} => (Sum.inl (pantsOf z.val) : MobiusCut.{u})) y :=
        ContMDiff.inl.contMDiffAt.comp y ((contMDiffAt_pantsOf hU ⟨g1, g2⟩
          (fun z hz => mem_planarModel_of_far hz.1 hz.2)).comp y hval)
      apply hs.congr_of_eventuallyEq
      filter_upwards [(hU.preimage continuous_subtype_val).mem_nhds ⟨g1, g2⟩] with z hz
      have hz1 : ¬ ‖mobiusBundleBase z.val - 3 / 2‖ < 1 / 2 := not_lt.mpr hz.1.le
      have hz2 : ¬ ‖mobiusBundleBase z.val + 3 / 2‖ < 1 / 2 := not_lt.mpr hz.2.le
      change (mobiusInteriorBackward z).val = _
      rw [mobiusInteriorBackward, dite_eq_right hz1, dite_eq_right hz2]

def mobiusInteriorForward (x : mobiusCutCarrier.{u}.interior) : mobiusInteriorImage.{u} :=
  ⟨mobiusFold x.val, mobiusFold_mem_interiorImage x⟩

def mobiusInteriorDiffeomorph :
    mobiusCutCarrier.{u}.interior ≃ₘ⟮𝓡∂ 3, 𝓡∂ 3⟯ mobiusInteriorImage.{u} where
  toFun := mobiusInteriorForward
  invFun := mobiusInteriorBackward
  left_inv := by
    rintro ⟨x, hx⟩
    have hx' : (𝓡∂ 3).IsInteriorPoint x := hx
    apply Subtype.ext
    change (mobiusInteriorBackward (mobiusInteriorForward ⟨x, hx⟩)).val = x
    rcases mobiusCut_cases x with ⟨a, rfl⟩ | ⟨i, b, rfl⟩
    · have ha := (ConeFilling.productSet_isInteriorPoint_iff a).mp
        ((isInteriorPoint_inl_iff a).mp hx')
      obtain ⟨-, h2, h3⟩ := (planarFunction_three_neg_iff' _).mp ha
      have e : mobiusBundleBase (mobiusFold (Sum.inl a : MobiusCut.{u})) = a.val.1.down :=
        mobiusBundleBase_mobiusPantsFold a
      have n1 : ¬ ‖mobiusBundleBase (mobiusFold (Sum.inl a : MobiusCut.{u})) - 3 / 2‖ < 1 / 2 := by
        rw [e]
        exact not_lt.mpr h2.le
      have n2 : ¬ ‖mobiusBundleBase (mobiusFold (Sum.inl a : MobiusCut.{u})) + 3 / 2‖ < 1 / 2 := by
        rw [e]
        exact not_lt.mpr h3.le
      rw [mobiusInteriorBackward]
      split_ifs with h1 h2
      · exact absurd h1 n1
      · exact absurd h2 n2
      · exact congrArg Sum.inl (pantsOf_mobiusPantsFold a)
    · have hb := (solidSet_isInteriorPoint_iff b).mp ((isInteriorPoint_solidInto_iff i b).mp hx')
      have hb2 : ‖b.val.1.down‖ ^ 2 / 18 < 1 / 2 := by nlinarith [norm_nonneg b.val.1.down]
      rw [mobiusInteriorBackward]
      fin_cases i
      · have n1 : ‖mobiusBundleBase (solidFoldPlus b) - 3 / 2‖ < 1 / 2 := by
          rw [norm_base_sub_solidFoldPlus]
          exact hb2
        split_ifs with h1 h2
        · change solidInto 0 (solidOf (solidFoldPlus b)) = solidInto 0 b
          rw [solidOf_solidFoldPlus]
        · exact absurd n1 h1
        · exact absurd n1 h1
      · have n2 : ‖mobiusBundleBase (solidFoldMinus b) + 3 / 2‖ < 1 / 2 := by
          rw [norm_base_add_solidFoldMinus]
          exact hb2
        have n1 : ¬ ‖mobiusBundleBase (solidFoldMinus b) - 3 / 2‖ < 1 / 2 := by
          have := (far_of_near_minus n2).2
          linarith
        split_ifs with h1 h2
        · exact absurd h1 n1
        · change solidInto 1 (solidNegOf (solidFoldMinus b)) = solidInto 1 b
          rw [solidNegOf_solidFoldMinus]
        · exact absurd n2 h2
  right_inv := by
    intro y
    apply Subtype.ext
    change mobiusFold (mobiusInteriorBackward y).val = y.val
    rw [mobiusInteriorBackward]
    split_ifs with h1 h2
    · exact (mobiusFold_solidInto 0 _).trans (solidFoldPlus_solidOf h1.le)
    · exact (mobiusFold_solidInto 1 _).trans (solidFoldMinus_solidNegOf h2.le)
    · exact mobiusPantsFold_pantsOf (mem_planarModel_of_far (far_of_interiorImage y h1 h2).1
        (far_of_interiorImage y h1 h2).2)
  contMDiff_toFun := (ContMDiff.subtypeVal_comp_iff mobiusInteriorImage.{u} _).mp
    (contMDiff_mobiusFold.comp contMDiff_subtype_val)
  contMDiff_invFun := (ContMDiff.subtypeVal_comp_iff mobiusCutCarrier.{u}.interior _).mp
    contMDiff_mobiusInteriorBackward_val

abbrev mobiusSeamAt (i : Fin 2) :
    PartialDiffeomorph signedCollarModel (𝓡∂ 3) (Torus × ℝ) mobiusBundleSet.{u} ∞ :=
  mobiusSeam (holeOf i) (holeOf_ne i)

def mobiusRightCollarMatched (i : Fin 2) :
    PartialDiffeomorph halfCollarModel (𝓡∂ 3) (Torus × EuclideanHalfSpace 1) MobiusCut.{u} ∞ :=
  (seamMatching.prodCongr
    (Diffeomorph.refl (𝓡∂ 1) (EuclideanHalfSpace 1) ∞)).toPartialDiffeomorph.trans
      (mobiusRightCollar i)

theorem halfCollarHeight_mem_mobiusSeam_source (i : Fin 2) (t : Torus) :
    halfCollarHeight (t, halfZero) ∈ (mobiusSeamAt.{u} i).source := by
  change -1 < halfZero.val 0 ∧ halfZero.val 0 < 1
  rw [show halfZero.val 0 = 0 from rfl]
  norm_num

theorem mobiusFold_leftCollar_eventuallyEq (i : Fin 2) (t : Torus) :
    mobiusFold.{u} ∘ mobiusLeftCollar i =ᶠ[𝓝 (t, halfZero)]
      mobiusSeamAt i ∘ seamReflection ∘ halfCollarHeight := by
  filter_upwards [ConeFilling.isOpen_halfCollarSource.mem_nhds (zero_mem_halfCollarSource t)]
    with q hq
  have hq' : q.2.val 0 < 1 := hq
  have h0 : 0 ≤ q.2.val 0 := q.2.2
  apply Subtype.ext
  change (mobiusFold (solidInto i (solidCollar 2 q))).val = (mobiusSeamAt i (q.1, -q.2.val 0)).val
  rw [mobiusSeam_apply_val _ _ ⟨by linarith, by linarith⟩, mobiusFold_solidInto]
  have h := solidFoldAt_collar.{u} i q.1 h0 hq'
  rw [halfPoint_eq_self q.2 h0 rfl] at h
  exact h

theorem mobiusFold_rightCollarMatched_eventuallyEq (i : Fin 2) (t : Torus) :
    mobiusFold.{u} ∘ mobiusRightCollarMatched i =ᶠ[𝓝 (t, halfZero)]
      mobiusSeamAt i ∘ halfCollarHeight := by
  filter_upwards [ConeFilling.isOpen_halfCollarSource.mem_nhds (zero_mem_halfCollarSource t)]
    with q hq
  have hq' : q.2.val 0 < 1 := hq
  have h0 : 0 ≤ q.2.val 0 := q.2.2
  apply Subtype.ext
  change (mobiusPantsFold (productCollar.{u} 3 (Or.inr rfl) (holeOf i)
    (seamMatching q.1, q.2))).val =
    (mobiusSeamAt i (q.1, q.2.val 0)).val
  rw [mobiusSeam_apply_val _ _ ⟨by linarith, hq'⟩]
  have h := mobiusPantsFold_collar_eq_seam.{u} (holeOf i) (holeOf_ne i) q.1 h0 hq'
  rw [halfPoint_eq_self q.2 h0 rfl] at h
  exact h

theorem mfderiv_mobiusSeam_congr (i : Fin 2) (y₁ y₂ : Torus × ℝ) (h : y₁ = y₂)
    (w : TangentSpace signedCollarModel y₁) :
    mfderiv signedCollarModel (𝓡∂ 3) (mobiusSeamAt.{u} i) y₁ w =
      mfderiv signedCollarModel (𝓡∂ 3) (mobiusSeamAt.{u} i) y₂ w := by
  subst h
  rfl

theorem mfderiv_mobiusFold_leftCollar_apply (i : Fin 2) (t : Torus)
    (v : TangentSpace halfCollarModel ((t, halfZero) : Torus × EuclideanHalfSpace 1)) :
    mfderiv (𝓡∂ 3) (𝓡∂ 3) mobiusFold (mobiusLeftCollar.{u} i (t, halfZero))
      (mfderiv halfCollarModel (𝓡∂ 3) (mobiusLeftCollar.{u} i) (t, halfZero) v) =
      mfderiv signedCollarModel (𝓡∂ 3) (mobiusSeamAt.{u} i) (halfCollarHeight (t, halfZero))
        (mfderiv signedCollarModel signedCollarModel seamReflection (halfCollarHeight (t, halfZero))
          (mfderiv halfCollarModel signedCollarModel halfCollarHeight (t, halfZero) v)) := by
  have hq0 : ((t, halfZero) : Torus × EuclideanHalfSpace 1) ∈ (mobiusLeftCollar.{u} i).source := by
    rw [mobiusLeftCollar_source]
    exact zero_mem_halfCollarSource t
  have hy0 := halfCollarHeight_mem_mobiusSeam_source.{u} i t
  have hfold : MDifferentiableAt (𝓡∂ 3) (𝓡∂ 3) mobiusFold (mobiusLeftCollar.{u} i (t, halfZero)) :=
    contMDiff_mobiusFold.mdifferentiableAt (by simp)
  have hl : MDifferentiableAt halfCollarModel (𝓡∂ 3) (mobiusLeftCollar.{u} i) (t, halfZero) :=
    (mobiusLeftCollar i).mdifferentiableAt (by simp) hq0
  have hj : MDifferentiableAt halfCollarModel signedCollarModel halfCollarHeight (t, halfZero) :=
    contMDiff_halfCollarHeight.mdifferentiableAt (by simp)
  have hρ : MDifferentiableAt signedCollarModel signedCollarModel seamReflection
      (halfCollarHeight (t, halfZero)) :=
    contMDiff_seamReflection.mdifferentiableAt (by simp)
  have hS : MDifferentiableAt signedCollarModel (𝓡∂ 3) (mobiusSeamAt.{u} i)
      (seamReflection (halfCollarHeight (t, halfZero))) := by
    rw [seamReflection_halfCollarHeight_zero]
    exact (mobiusSeamAt i).mdifferentiableAt (by simp) hy0
  have e1 := DFunLike.congr_fun (mfderiv_comp (t, halfZero) hfold hl) v
  have e2 := DFunLike.congr_fun (mfderiv_comp (t, halfZero) hS (hρ.comp (t, halfZero) hj)) v
  have e3 := DFunLike.congr_fun (mfderiv_comp (t, halfZero) hρ hj) v
  have e4 := DFunLike.congr_fun (Filter.EventuallyEq.mfderiv_eq (I := halfCollarModel)
    (I' := 𝓡∂ 3) (mobiusFold_leftCollar_eventuallyEq.{u} i t)) v
  exact ((e1.symm.trans e4).trans e2).trans ((congrArg (mfderiv signedCollarModel (𝓡∂ 3)
    (mobiusSeamAt i) (seamReflection (halfCollarHeight (t, halfZero)))) e3).trans
      (mfderiv_mobiusSeam_congr i _ _ (seamReflection_halfCollarHeight_zero t) _))

theorem mfderiv_mobiusFold_rightCollar_apply (i : Fin 2) (t : Torus)
    (v : TangentSpace halfCollarModel ((t, halfZero) : Torus × EuclideanHalfSpace 1)) :
    mfderiv (𝓡∂ 3) (𝓡∂ 3) mobiusFold (mobiusRightCollarMatched.{u} i (t, halfZero))
      (mfderiv halfCollarModel (𝓡∂ 3) (mobiusRightCollarMatched.{u} i) (t, halfZero) v) =
      mfderiv signedCollarModel (𝓡∂ 3) (mobiusSeamAt.{u} i) (halfCollarHeight (t, halfZero))
        (mfderiv halfCollarModel signedCollarModel halfCollarHeight (t, halfZero) v) := by
  have hq0 : ((t, halfZero) : Torus × EuclideanHalfSpace 1) ∈
      (mobiusRightCollarMatched.{u} i).source := by
    refine ⟨mem_univ _, ?_⟩
    change (seamMatching t, halfZero) ∈ (mobiusRightCollar.{u} i).source
    rw [mobiusRightCollar_source]
    exact zero_mem_halfCollarSource _
  have hy0 := halfCollarHeight_mem_mobiusSeam_source.{u} i t
  have hfold : MDifferentiableAt (𝓡∂ 3) (𝓡∂ 3) mobiusFold
      (mobiusRightCollarMatched.{u} i (t, halfZero)) :=
    contMDiff_mobiusFold.mdifferentiableAt (by simp)
  have hr : MDifferentiableAt halfCollarModel (𝓡∂ 3) (mobiusRightCollarMatched.{u} i)
      (t, halfZero) :=
    (mobiusRightCollarMatched i).mdifferentiableAt (by simp) hq0
  have hj : MDifferentiableAt halfCollarModel signedCollarModel halfCollarHeight (t, halfZero) :=
    contMDiff_halfCollarHeight.mdifferentiableAt (by simp)
  have hS : MDifferentiableAt signedCollarModel (𝓡∂ 3) (mobiusSeamAt.{u} i)
      (halfCollarHeight (t, halfZero)) :=
    (mobiusSeamAt i).mdifferentiableAt (by simp) hy0
  have e1 := DFunLike.congr_fun (mfderiv_comp (t, halfZero) hfold hr) v
  have e2 := DFunLike.congr_fun (mfderiv_comp (t, halfZero) hS hj) v
  have e4 := DFunLike.congr_fun (Filter.EventuallyEq.mfderiv_eq (I := halfCollarModel)
    (I' := 𝓡∂ 3) (mobiusFold_rightCollarMatched_eventuallyEq.{u} i t)) v
  exact (e1.symm.trans e4).trans e2

theorem mobiusReversing (i : Fin 2) :
    ReversesBoundaryOrientation mobiusCutCarrier.{u} (mobiusLeftCollar i)
      (fun p => mobiusRightCollar i (seamMatching p.1, p.2)) := by
  intro t
  let q0 : Torus × EuclideanHalfSpace 1 := (t, halfZero)
  have hq0l : q0 ∈ (mobiusLeftCollar.{u} i).source := by
    rw [mobiusLeftCollar_source]
    exact zero_mem_halfCollarSource t
  have hq0r : q0 ∈ (mobiusRightCollarMatched.{u} i).source := by
    refine ⟨mem_univ _, ?_⟩
    change (seamMatching t, halfZero) ∈ (mobiusRightCollar.{u} i).source
    rw [mobiusRightCollar_source]
    exact zero_mem_halfCollarSource _
  have hl := (mobiusLeftCollar.{u} i).isLocalDiffeomorphAt halfCollarModel (𝓡∂ 3) ∞ hq0l
  have hr := (mobiusRightCollarMatched.{u} i).isLocalDiffeomorphAt halfCollarModel (𝓡∂ 3) ∞ hq0r
  let L := (hl.mfderivToContinuousLinearEquiv (by simp)).toLinearEquiv
  let R := (hr.mfderivToContinuousLinearEquiv (by simp)).toLinearEquiv
  refine ⟨L, R, fun v => rfl, fun v => rfl, ?_⟩
  let D : (x : MobiusCut.{u}) → EuclideanSpace ℝ (Fin 3) ≃ₗ[ℝ] EuclideanSpace ℝ (Fin 3) :=
    fun x => (Manifold.differentialEquivOfBijective (𝓡∂ 3) (𝓡∂ 3) mobiusFold
      mfderiv_mobiusFold_bijective x).toLinearEquiv
  have hO : ∀ x : MobiusCut.{u}, mobiusCutOrientation.orientation x =
      Orientation.map (Fin 3) (D x).symm
        (mobiusBundleCarrier.{u}.orientation.orientation (mobiusFold x)) := by
    intro x
    rw [← orientation_map_mobiusCutOrientation x]
    exact (Equiv.symm_apply_apply (Orientation.map (Fin 3) (D x)) _).symm
  let y0 : Torus × ℝ := halfCollarHeight q0
  have hS := (mobiusSeamAt.{u} i).isLocalDiffeomorphAt signedCollarModel (𝓡∂ 3) ∞
    (halfCollarHeight_mem_mobiusSeam_source.{u} i t)
  let dS := (hS.mfderivToContinuousLinearEquiv (by simp)).toLinearEquiv
  let A := L.trans (D (mobiusLeftCollar i q0))
  let B := R.trans (D (mobiusRightCollarMatched i q0))
  let J := B.trans dS.symm
  let P : (TangentSpace signedCollarModel y0) →ₗ[ℝ] (TangentSpace signedCollarModel y0) :=
    (LinearMap.id : (EuclideanSpace ℝ (Fin 1) × EuclideanSpace ℝ (Fin 1)) →ₗ[ℝ] _).prodMap
      (-LinearMap.id : ℝ →ₗ[ℝ] ℝ)
  have hJ : ∀ v, J v = mfderiv halfCollarModel signedCollarModel halfCollarHeight q0 v := by
    intro v
    apply dS.injective
    exact (dS.apply_symm_apply (B v)).trans (mfderiv_mobiusFold_rightCollar_apply i t v)
  have hdet : LinearMap.det ((A.trans B.symm : _ ≃ₗ[ℝ] _) :
      TangentSpace halfCollarModel q0 →ₗ[ℝ] TangentSpace halfCollarModel q0) < 0 := by
    let Sₗ : TangentSpace signedCollarModel y0 →ₗ[ℝ] EuclideanSpace ℝ (Fin 3) := dS.toLinearMap
    rw [det_trans_symm_eq_det A B J P Sₗ]
    · rw [show LinearMap.det P = -1 from
        det_prodMap_id_neg (EuclideanSpace ℝ (Fin 1) × EuclideanSpace ℝ (Fin 1))]
      norm_num
    · intro v
      change D (mobiusLeftCollar i q0) (L v) = Sₗ (P (J v))
      rw [hJ]
      exact (mfderiv_mobiusFold_leftCollar_apply i t v).trans
        (congrArg Sₗ (mfderiv_seamReflection_apply _ _))
    · intro v
      change D (mobiusRightCollarMatched i q0) (R v) = Sₗ (J v)
      rw [hJ]
      exact mfderiv_mobiusFold_rightCollar_apply i t v
  have hpt : mobiusFold (mobiusRightCollarMatched.{u} i q0) =
      mobiusFold (mobiusLeftCollar.{u} i q0) :=
    (mobiusFold_rightTorus_matching i t).trans (mobiusFold_leftTorus i t).symm
  have hOS : ∀ p₁ p₂ : mobiusBundleSet.{u}, p₁ = p₂ →
      mobiusBundleCarrier.{u}.orientation.orientation p₁ =
        mobiusBundleCarrier.{u}.orientation.orientation p₂ := by
    rintro _ _ rfl
    rfl
  change Orientation.map (Fin 3) L.symm
      (mobiusCutOrientation.orientation (mobiusLeftCollar i q0)) =
    -Orientation.map (Fin 3) R.symm
      (mobiusCutOrientation.orientation (mobiusRightCollarMatched i q0))
  rw [hO, hO, hOS _ _ hpt]
  let o := mobiusBundleCarrier.{u}.orientation.orientation (mobiusFold (mobiusLeftCollar.{u} i q0))
  have key := orientation_map_symm_eq_neg_of_det_neg (finrank_halfCollarTangent q0) A B o hdet
  have hA' : A.symm = (D (mobiusLeftCollar i q0)).symm.trans L.symm :=
    LinearEquiv.ext fun _ => rfl
  have hB' : B.symm = (D (mobiusRightCollarMatched i q0)).symm.trans R.symm :=
    LinearEquiv.ext fun _ => rfl
  rw [hA', hB'] at key
  exact (DifferentialGeometry.orientation_map_trans (D (mobiusLeftCollar i q0)).symm L.symm
    o).symm.trans (key.trans (congrArg Neg.neg (DifferentialGeometry.orientation_map_trans
      (D (mobiusRightCollarMatched i q0)).symm R.symm o)))

abbrev mobiusPairing : TorusPairing mobiusCutCarrier.{u} where
  count := 2
  gluing := mobiusGluing
  leftParam i := mobiusLeftParam i
  rightParam i := mobiusRightParam i
  matching _ := seamMatching
  matching_eq i t := mobiusAttaching_leftParam i t
  leftCollar i := mobiusLeftCollar i
  rightCollar i := mobiusRightCollar i
  left_source i := mobiusLeftCollar_source i
  right_source i := mobiusRightCollar_source i
  left_zero _ _ := rfl
  right_zero _ _ := rfl
  reversing i := mobiusReversing i

theorem norm_planarCenter_holeOf (i : Fin 2) : ‖(planarCenter 3 (holeOf i) : ℂ)‖ = 3 / 2 := by
  rw [planarCenter_holeOf]
  fin_cases i <;> norm_num

theorem norm_sub_planarCenter_holeOf {i j : Fin 2} (hij : i ≠ j) :
    ‖(planarCenter 3 (holeOf i) : ℂ) - planarCenter 3 (holeOf j)‖ = 3 := by
  rw [planarCenter_holeOf, planarCenter_holeOf]
  fin_cases i <;> fin_cases j
  · exact absurd rfl hij
  · norm_num
  · norm_num
  · exact absurd rfl hij

theorem mobiusSeamAt_target_base (i : Fin 2) {y : mobiusBundleSet.{u}}
    (hy : y ∈ (mobiusSeamAt.{u} i).target) :
    ‖mobiusBundleBase y - planarCenter 3 (holeOf i)‖ < 3 / 4 :=
  (mobiusSeam_base (holeOf i) (holeOf_ne i) hy).2

theorem norm_base_lt_of_seam (i : Fin 2) {y : mobiusBundleSet.{u}}
    (hy : y ∈ (mobiusSeamAt.{u} i).target) : ‖mobiusBundleBase y‖ < 9 / 4 := by
  have h1 := mobiusSeamAt_target_base i hy
  have h2 := norm_sub_norm_le (mobiusBundleBase y) (planarCenter 3 (holeOf i))
  rw [norm_planarCenter_holeOf] at h2
  linarith

abbrev mobiusPresentation : TorusPresentation mobiusBundleCarrier.{u} where
  cutCarrier := mobiusCutCarrier
  components := mobiusComponents
  pairing := mobiusPairing
  externalCount := 1
  external := mobiusExternal
  cutExternal := mobiusCutExternal
  external_exhausted := by
    ext y
    rw [BoundaryTori.image, mem_iUnion]
    obtain ⟨z, rfl⟩ : ∃ z : mobiusBundleSet.{u}, z = y := ⟨y, rfl⟩
    change (𝓡∂ 3).IsBoundaryPoint z ↔ ∃ i, ∃ t, mobiusExternalCollar.{u} (t, halfZero) = z
    rw [isBoundaryPoint_iff_external]
    exact ⟨fun ⟨t, ht⟩ => ⟨0, t, ht⟩, fun ⟨_, t, ht⟩ => ⟨t, ht⟩⟩
  cut_boundary_exhausted := mobiusCut_boundary
  external_disjoint := mobiusCut_external_disjoint
  reconstruction := mobiusReconstruction
  quotient_smooth := contMDiff_mobiusFold
  quotient_oriented x := ⟨(Manifold.differentialEquivOfBijective (𝓡∂ 3) (𝓡∂ 3) mobiusFold
    mfderiv_mobiusFold_bijective x).toLinearEquiv, fun _ => rfl,
      orientation_map_mobiusCutOrientation x⟩
  interiorImage := mobiusInteriorImage
  interiorDiffeomorph := mobiusInteriorDiffeomorph
  interior_map _ := rfl
  seam i := mobiusSeamAt i
  seam_source _ := rfl
  seam_zero i t := by
    apply Subtype.ext
    rw [mobiusSeam_apply_val _ _ (by constructor <;> norm_num)]
    change mobiusSeamPoint (holeOf i) t 0 = (mobiusFold (mobiusLeftTorus i t)).val
    rw [mobiusFold_leftTorus]
    have h := solidFoldAt_collar.{u} i t (le_refl 0) (by norm_num)
    rw [neg_zero] at h
    exact h.symm
  seam_positive i t s hs hs1 := by
    apply Subtype.ext
    rw [mobiusSeam_apply_val _ _ ⟨by linarith, hs1⟩]
    exact (mobiusPantsFold_collar_eq_seam (holeOf i) (holeOf_ne i) t hs hs1).symm
  seam_negative i t s hs hs1 := by
    apply Subtype.ext
    rw [mobiusSeam_apply_val _ _ ⟨hs1, by linarith⟩]
    change _ = (mobiusFold (solidInto i
      (solidCollar 2 (t, halfPoint (-s) (neg_nonneg.mpr hs))))).val
    rw [mobiusFold_solidInto, solidFoldAt_collar i t _ (by linarith), neg_neg]
  seam_interior i := by
    intro y hy
    obtain ⟨z, rfl⟩ : ∃ z : mobiusBundleSet.{u}, z = y := ⟨y, rfl⟩
    change (𝓡∂ 3).IsInteriorPoint z
    rw [ModelWithCorners.isInteriorPoint_iff_not_isBoundaryPoint,
      mobiusBundleSet_isBoundaryPoint_iff_base]
    have := norm_base_lt_of_seam i hy
    intro h
    rw [h] at this
    norm_num at this
  seam_disjoint i j h := Set.disjoint_left.mpr fun y hi hj => by
    have h1 := mobiusSeamAt_target_base i hi
    have h2 := mobiusSeamAt_target_base j hj
    have h3 := norm_sub_le_norm_sub_add_norm_sub (planarCenter 3 (holeOf i) : ℂ)
      (mobiusBundleBase y) (planarCenter 3 (holeOf j))
    rw [norm_sub_planarCenter_holeOf h, norm_sub_rev] at h3
    linarith
  marked_collar _ _ _ := rfl
  external_seam_disjoint _ j := by
    rw [Set.disjoint_left]
    rintro y ⟨hy1, hy2⟩ hys
    have hJ := mem_planarModel_of_outer hy1
    have hfar := outer_far hy2
    change 11 / 4 < ‖(pantsOf y).val.1.down‖ at hfar
    rw [pantsOf_val hJ] at hfar
    have := norm_base_lt_of_seam j hys
    change 11 / 4 < ‖mobiusBundleBase y‖ at hfar
    linarith
  leftPiece i := i.succ
  rightPiece _ := 0
  left_owned i := by
    rintro _ ⟨t, rfl⟩
    exact ⟨_, rfl⟩
  right_owned _ := by
    rintro _ ⟨t, rfl⟩
    exact ⟨_, rfl⟩
  externalPiece _ := 0
  external_owned _ := by
    rintro _ ⟨t, rfl⟩
    exact ⟨_, rfl⟩

abbrev mobiusData : SeifertData :=
  ⟨3, 1, [(2, -1), (2, -1)], [], by norm_num, le_rfl, by decide, by decide, rfl⟩

theorem mobiusData_eq_retwist : mobiusData = SeifertData.retwist
    ⟨3, 1, [(2, 1), (2, 1)], [], by norm_num, le_rfl, by decide, by decide, rfl⟩ ![1, 1] := by
  simp [mobiusData, SeifertData.retwist, List.ofFn_succ]

def mobiusProductPortFun (j : Fin 3) : mobiusPresentation.{u}.OwnedSide 0 :=
  Fin.cases ⟨.inr (.inr 0), rfl⟩ (fun m => ⟨.inr (.inl m), rfl⟩) j

def mobiusProductPortInv : mobiusPresentation.{u}.OwnedSide 0 → Fin 3
  | ⟨.inl m, _⟩ => m.succ
  | ⟨.inr (.inl m), _⟩ => m.succ
  | ⟨.inr (.inr _), _⟩ => 0

def mobiusProductPort : Fin 3 ≃ mobiusPresentation.{u}.OwnedSide 0 where
  toFun := mobiusProductPortFun
  invFun := mobiusProductPortInv
  left_inv j := by
    fin_cases j <;> rfl
  right_inv s := by
    rcases s with ⟨m | m | e, h⟩
    · exact absurd h (Fin.succ_ne_zero m)
    · rfl
    · obtain rfl : e = 0 := Subsingleton.elim e 0
      rfl

def mobiusProductPiece : ProductFibredPiece mobiusPresentation.{u} 0 3 where
  base := pantsPlanarBase
  port := mobiusProductPort
  trivialization := (productDiffeomorph 3).trans (sumInlRangeDiffeomorph (I := 𝓡∂ 3)).symm
  collar_eq j p hp := by
    apply Subtype.ext
    rw [TorusPresentation.pieceCollar_apply _ _ _ hp]
    fin_cases j <;> rfl

def mobiusSolidPort (m : Fin 2) : Fin 1 ≃ mobiusPresentation.{u}.OwnedSide m.succ where
  toFun _ := ⟨.inl m, rfl⟩
  invFun _ := 0
  left_inv j := Subsingleton.elim _ _
  right_inv s := by
    rcases s with ⟨m' | m' | e, h⟩
    · obtain rfl : m' = m := Fin.succ_injective 2 h
      rfl
    · exact absurd h.symm (Fin.succ_ne_zero m)
    · exact absurd h.symm (Fin.succ_ne_zero m)

def mobiusSolidPiece (m : Fin 2) : SolidTorusPiece mobiusPresentation.{u} m.succ where
  base := discPlanarBase 2
  port := mobiusSolidPort m
  trivialization := solidDiffeomorph.trans (solidPieceDiffeomorph m).symm
  collar_eq j p hp := by
    apply Subtype.ext
    rw [TorusPresentation.pieceCollar_apply _ _ _ hp, Subsingleton.elim j 0]
    rfl

def mobiusPieceEquiv :
    Option (Fin mobiusData.fillingCount) ≃ Fin mobiusPresentation.{u}.components.count where
  toFun o := o.elim 0 Fin.succ
  invFun k := Fin.cases none some k
  left_inv o := by
    rcases o with _ | m <;> rfl
  right_inv k := by
    fin_cases k <;> rfl

def mobiusPortEquiv : Fin mobiusData.ports ⊕ Fin mobiusData.fillingCount ≃ Fin mobiusData.k where
  toFun := Sum.elim (fun _ => 0) Fin.succ
  invFun k := Fin.cases (.inl 0) .inr k
  left_inv o := by
    rcases o with r | m
    · obtain rfl : r = 0 := Subsingleton.elim r 0
      rfl
    · rfl
  right_inv k := by
    fin_cases k <;> rfl

theorem fillingSlope_mobiusData (m : Fin mobiusData.fillingCount) :
    mobiusData.fillingSlope m = (2, -1) := by
  fin_cases m <;> rfl

def mobiusBlock : SeifertBlock mobiusBundleCarrier.{u} mobiusData where
  presentation := mobiusPresentation
  piece := mobiusPieceEquiv.{u}
  product := mobiusProductPiece
  solid m := mobiusSolidPiece m
  port := mobiusPortEquiv
  seam := Equiv.refl _
  free := Equiv.refl _
  free_port r := by
    obtain rfl : r = 0 := Subsingleton.elim r 0
    rfl
  filled_port _ := rfl
  solid_port _ := rfl
  slope m := by
    have h : PrimitiveSlope.mk (mobiusData.fillingSlope m) (mobiusData.isPrimitive_fillingSlope m) =
        PrimitiveSlope.mk (2, -1) (by decide) := by
      congr 1
      exact fillingSlope_mobiusData m
    rw [h]
    exact seamMatching_meridian

def holeCutoff (ζ : ℂ) : ℝ := Real.smoothTransition (16 / 7 * (1 - ‖ζ + 3 / 2‖ ^ 2))

theorem contDiff_holeCutoff : ContDiff ℝ ∞ holeCutoff :=
  Real.smoothTransition.contDiff.comp (contDiff_const.mul (contDiff_const.sub
    ((contDiff_norm_sq ℝ).comp (contDiff_id.add contDiff_const))))

theorem holeCutoff_eq_zero {ζ : ℂ} (h : 1 ≤ ‖ζ + 3 / 2‖) : holeCutoff ζ = 0 :=
  Real.smoothTransition.zero_of_nonpos (by nlinarith)

theorem holeCutoff_eq_one {ζ : ℂ} (h : ‖ζ + 3 / 2‖ ≤ 3 / 4) : holeCutoff ζ = 1 :=
  Real.smoothTransition.one_of_one_le (by nlinarith [norm_nonneg (ζ + 3 / 2)])

def holeAngle (ζ : ℂ) : ℝ := holeCutoff ζ * (Real.pi - Complex.arg (3 / 2 - ζ))

theorem contDiff_holeAngle : ContDiff ℝ ∞ holeAngle := by
  rw [contDiff_iff_contDiffAt]
  intro ζ
  by_cases h : ‖ζ + 3 / 2‖ < 2
  · have hre : |(ζ + 3 / 2).re| ≤ ‖ζ + 3 / 2‖ := Complex.abs_re_le_norm _
    have hs : (3 / 2 - ζ) ∈ Complex.slitPlane := by
      refine Complex.mem_slitPlane_iff.mpr (Or.inl ?_)
      have e1 : (3 / 2 - ζ).re = 3 - (ζ + 3 / 2).re := by
        simp only [Complex.sub_re, Complex.add_re]
        norm_num
        ring
      rw [e1]
      have := le_abs_self (ζ + 3 / 2).re
      linarith
    have he : (fun z : ℂ => Complex.arg (3 / 2 - z)) =
        fun z : ℂ => Complex.imCLM (Complex.log (3 / 2 - z)) :=
      funext fun z => by rw [Complex.imCLM_apply, Complex.log_im]
    have harg : ContDiffAt ℝ ∞ (fun z : ℂ => Complex.arg (3 / 2 - z)) ζ := by
      rw [he]
      exact Complex.imCLM.contDiff.contDiffAt.comp ζ
        (((Complex.contDiffAt_log hs).restrict_scalars ℝ).comp ζ
          (contDiffAt_const.sub contDiffAt_id))
    exact contDiff_holeCutoff.contDiffAt.mul (contDiffAt_const.sub harg)
  · have hev : holeAngle =ᶠ[𝓝 ζ] fun _ => 0 := by
      have ho : IsOpen {z : ℂ | 1 < ‖z + 3 / 2‖} :=
        isOpen_lt continuous_const (continuous_norm.comp (continuous_id.add continuous_const))
      filter_upwards [ho.mem_nhds (show 1 < ‖ζ + 3 / 2‖ by linarith [not_lt.mp h])] with z hz
      rw [holeAngle, holeCutoff_eq_zero (le_of_lt hz), zero_mul]
    exact contDiffAt_const.congr_of_eventuallyEq hev

def holeShear (ζ : ℂ) : Circle := unitOf (ζ - 3 / 2) * Circle.exp (holeAngle ζ)

theorem contMDiffAt_holeShear {ζ : ℂ} (h : ζ ≠ 3 / 2) :
    ContMDiffAt 𝓘(ℝ, ℂ) (𝓡 1) ∞ holeShear ζ := by
  have h1 : ContMDiffAt 𝓘(ℝ, ℂ) (𝓡 1) ∞ (fun z : ℂ => unitOf (z - 3 / 2)) ζ :=
    (contMDiffOn_unitOf.contMDiffAt (isOpen_ne.mem_nhds (sub_ne_zero.mpr h))).comp ζ
      ((contDiffAt_id.sub contDiffAt_const).contMDiffAt)
  have h2 : ContMDiffAt 𝓘(ℝ, ℂ) (𝓡 1) ∞ (fun z : ℂ => Circle.exp (holeAngle z)) ζ :=
    contMDiff_circleExp.contMDiffAt.comp ζ contDiff_holeAngle.contMDiff.contMDiffAt
  exact h1.mul h2

theorem holeShear_of_near_one {ζ : ℂ} (h : ‖ζ - 3 / 2‖ ≤ 3 / 4) :
    holeShear ζ = unitOf (ζ - 3 / 2) := by
  have h3 := norm_sub_le (ζ + 3 / 2) (ζ - 3 / 2)
  rw [show ζ + 3 / 2 - (ζ - 3 / 2) = 3 by ring] at h3
  norm_num at h3
  rw [holeShear, holeAngle, holeCutoff_eq_zero (by linarith), zero_mul, Circle.exp_zero, mul_one]

theorem unitOf_eq_exp_arg {w : ℂ} (hw : w ≠ 0) : unitOf w = Circle.exp (Complex.arg w) := by
  have h := Complex.norm_mul_exp_arg_mul_I w
  conv_lhs => rw [← h]
  rw [← Circle.coe_exp]
  exact unitOf_ofReal_mul (norm_pos_iff.mpr hw) _

theorem holeShear_of_near_two {ζ : ℂ} (h : ‖ζ + 3 / 2‖ ≤ 3 / 4) : holeShear ζ = 1 := by
  have h3 := norm_sub_le (3 / 2 - ζ) (-(ζ + 3 / 2))
  rw [show 3 / 2 - ζ - -(ζ + 3 / 2) = 3 by ring, norm_neg] at h3
  norm_num at h3
  have hw : (3 / 2 - ζ) ≠ 0 := by
    intro h0
    rw [h0, norm_zero] at h3
    linarith
  have hpi : circleI ^ 2 = Circle.exp Real.pi :=
    Circle.ext (by rw [circleI_sq_coe, Circle.coe_exp, Complex.exp_pi_mul_I])
  rw [holeShear, holeAngle, holeCutoff_eq_one h, one_mul,
    show ζ - 3 / 2 = -(3 / 2 - ζ) by ring, unitOf_neg hw, unitOf_eq_exp_arg hw, hpi,
    ← Circle.exp_add, ← Circle.exp_add]
  convert Circle.exp_two_pi using 2
  ring

theorem planarCollarFormula_hole (j : Fin 3) (hj : j.val ≠ 0) (t : Circle) (m : ℝ) :
    planarCollarFormula 3 j ((t : ℂ), m) =
      planarCenter 3 j + ((1 / 2 + m / 4 : ℝ) : ℂ) * ((t⁻¹ : Circle) : ℂ) := by
  simp only [planarCollarFormula, planarRadius, planarSign, planarTwist, hj, ite_false,
    Complex.real_smul, Circle.coe_inv_eq_conj]
  push_cast
  ring

theorem holeShear_collar_one (t : Circle) {m : ℝ} (h0 : 0 ≤ m) (h1 : m ≤ 1) :
    holeShear (planarCollarFormula 3 1 ((t : ℂ), m)) = t⁻¹ := by
  have e : planarCollarFormula 3 1 ((t : ℂ), m) - 3 / 2 =
      ((1 / 2 + m / 4 : ℝ) : ℂ) * ((t⁻¹ : Circle) : ℂ) := by
    rw [planarCollarFormula_hole 1 (by decide), planarCenter_three_one]
    push_cast
    ring
  have hpos : (0 : ℝ) < 1 / 2 + m / 4 := by linarith
  have hn : ‖planarCollarFormula 3 1 ((t : ℂ), m) - 3 / 2‖ ≤ 3 / 4 := by
    rw [e, norm_mul, Circle.norm_coe, mul_one, Complex.norm_real, Real.norm_of_nonneg hpos.le]
    linarith
  rw [holeShear_of_near_one hn, e, unitOf_ofReal_mul hpos]

theorem holeShear_collar_two (t : Circle) {m : ℝ} (h0 : 0 ≤ m) (h1 : m ≤ 1) :
    holeShear (planarCollarFormula 3 2 ((t : ℂ), m)) = 1 := by
  have e : planarCollarFormula 3 2 ((t : ℂ), m) + 3 / 2 =
      ((1 / 2 + m / 4 : ℝ) : ℂ) * ((t⁻¹ : Circle) : ℂ) := by
    rw [planarCollarFormula_hole 2 (by decide), planarCenter_three_two]
    push_cast
    ring
  have hpos : (0 : ℝ) < 1 / 2 + m / 4 := by linarith
  apply holeShear_of_near_two
  rw [e, norm_mul, Circle.norm_coe, mul_one, Complex.norm_real, Real.norm_of_nonneg hpos.le]
  linarith

def pantsShearBy (g : ℂ → Circle) (x : productSet.{u} 3) : productSet.{u} 3 :=
  ⟨(x.val.1, x.val.2 * g x.val.1.down), x.2⟩

theorem contMDiff_pantsShearBy {g : ℂ → Circle}
    (hg : ∀ ζ, ζ ≠ 3 / 2 → ContMDiffAt 𝓘(ℝ, ℂ) (𝓡 1) ∞ g ζ) :
    ContMDiff (𝓡∂ 3) (𝓡∂ 3) ∞ (pantsShearBy.{u} g) := by
  refine ((productAtlas.{u} 3).contMDiff_iff_subtype_val _).mpr fun x => ?_
  have hv := (productAtlas.{u} 3).contMDiff_subtype_val x
  have hz : ContMDiffAt (𝓡∂ 3) 𝓘(ℝ, ℂ) ∞ (fun x : productSet.{u} 3 => x.val.1.down) x :=
    (contMDiff_planeLift_down.comp contMDiff_fst).contMDiffAt.comp x hv
  exact (contMDiff_fst.contMDiffAt.comp x hv).prodMk ((contMDiff_snd.contMDiffAt.comp x hv).mul
    ((hg _ (pantsGood_of_mem_productSet x).1).comp x hz))

def pantsShear : productSet.{u} 3 ≃ₘ⟮𝓡∂ 3, 𝓡∂ 3⟯ productSet.{u} 3 where
  toFun := pantsShearBy holeShear
  invFun := pantsShearBy fun ζ => (holeShear ζ)⁻¹
  left_inv x := Subtype.ext (Prod.ext rfl (by
    change x.val.2 * holeShear x.val.1.down * (holeShear x.val.1.down)⁻¹ = x.val.2
    rw [mul_inv_cancel_right]))
  right_inv x := Subtype.ext (Prod.ext rfl (by
    change x.val.2 * (holeShear x.val.1.down)⁻¹ * holeShear x.val.1.down = x.val.2
    rw [inv_mul_cancel_right]))
  contMDiff_toFun := contMDiff_pantsShearBy fun _ h => contMDiffAt_holeShear h
  contMDiff_invFun := contMDiff_pantsShearBy fun _ h => (contMDiffAt_holeShear h).inv

theorem pantsShear_apply_val (x : productSet.{u} 3) :
    (pantsShear x).val = (x.val.1, x.val.2 * holeShear x.val.1.down) := rfl

theorem pantsShear_productCollar (j : Fin 3) (p : Torus × EuclideanHalfSpace 1) :
    pantsShear (productCollar.{u} 3 (Or.inr rfl) j p) = productCollar.{u} 3 (Or.inr rfl) j
      ((p.1.1, p.1.2 * holeShear (planarCollarFormula 3 j ((p.1.1 : ℂ), min (p.2.val 0) 1))),
        p.2) :=
  rfl

theorem min_mem_unit (h : EuclideanHalfSpace 1) : 0 ≤ min (h.val 0) 1 ∧ min (h.val 0) 1 ≤ 1 :=
  ⟨le_min h.2 zero_le_one, min_le_right _ _⟩

theorem pantsShear_productCollar_one (p : Torus × EuclideanHalfSpace 1) :
    pantsShear (productCollar.{u} 3 (Or.inr rfl) 1 p) =
      productCollar.{u} 3 (Or.inr rfl) 1 ((p.1.1, p.1.2 * p.1.1⁻¹), p.2) := by
  rw [pantsShear_productCollar, holeShear_collar_one _ (min_mem_unit p.2).1 (min_mem_unit p.2).2]

theorem pantsShear_productCollar_two (p : Torus × EuclideanHalfSpace 1) :
    pantsShear (productCollar.{u} 3 (Or.inr rfl) 2 p) = productCollar.{u} 3 (Or.inr rfl) 2 p := by
  rw [pantsShear_productCollar, holeShear_collar_two _ (min_mem_unit p.2).1 (min_mem_unit p.2).2,
    mul_one]

def twistHomeo : Torus ≃ₜ Torus where
  toFun τ := (τ.1, τ.2 * τ.1⁻¹)
  invFun τ := (τ.1, τ.2 * τ.1)
  left_inv τ := Prod.ext rfl (inv_mul_cancel_right τ.2 τ.1)
  right_inv τ := Prod.ext rfl (mul_inv_cancel_right τ.2 τ.1)
  continuous_toFun := continuous_fst.prodMk (continuous_snd.mul continuous_fst.inv)
  continuous_invFun := continuous_fst.prodMk (continuous_snd.mul continuous_fst)

def holeTwist (i : Fin 2) : Torus ≃ₜ Torus :=
  Fin.cases twistHomeo (fun _ => Homeomorph.refl Torus) i

def twistedMatrix : Matrix (Fin 2) (Fin 2) ℤ := !![-2, 1; -1, 1]

theorem det_twistedMatrix : twistedMatrix.det = -1 := by
  simp [twistedMatrix, Matrix.det_fin_two]

def twistedUnit : GL (Fin 2) ℤ := PrimitiveSlope.unitOfDet twistedMatrix (Or.inr det_twistedMatrix)

def twistedMatching : Torus ≃ₘ⟮torusModel, torusModel⟯ Torus := linearTorusDiffeomorph twistedUnit

theorem twistedMatching_apply (t : Torus) :
    twistedMatching t = (t.1 ^ (-2 : ℤ) * t.2, t.1⁻¹ * t.2) := by
  change linearTorusMap twistedMatrix t = _
  simp [linearTorusMap, twistedMatrix]

theorem torusMatrix_twistedMatching : torusMatrix twistedMatching = twistedMatrix :=
  torusMatrix_linearTorusDiffeomorph twistedUnit

theorem twistedMatching_meridian :
    torusUnit twistedMatching • meridianSlope = PrimitiveSlope.mk (2, 1) (by decide) := by
  rw [meridianSlope, PrimitiveSlope.smul_mk, PrimitiveSlope.mk_eq_mk_iff]
  right
  change ((2 : ℤ), (1 : ℤ)) = -smulVec (torusMatrix twistedMatching) (1, 0)
  rw [torusMatrix_twistedMatching]
  simp [smulVec, twistedMatrix]

def holeMatching (i : Fin 2) : Torus ≃ₘ⟮torusModel, torusModel⟯ Torus :=
  Fin.cases twistedMatching (fun _ => seamMatching) i

theorem holeTwist_holeMatching (i : Fin 2) (t : Torus) :
    holeTwist i (holeMatching i t) = seamMatching t := by
  fin_cases i
  · change twistHomeo (twistedMatching t) = seamMatching t
    rw [twistedMatching_apply, seamMatching_apply]
    refine Prod.ext rfl ?_
    change t.1⁻¹ * t.2 * (t.1 ^ (-2 : ℤ) * t.2)⁻¹ = t.1
    group
  · rfl

def twistRightCollar (i : Fin 2) :
    PartialDiffeomorph halfCollarModel (𝓡∂ 3) (Torus × EuclideanHalfSpace 1) MobiusCut.{u} ∞ :=
  (productCollar 3 (Or.inr rfl) (holeOf i)).trans
    (pantsShear.toPartialDiffeomorph.trans partialDiffeomorphSumInl)

theorem twistRightCollar_apply (i : Fin 2) (p : Torus × EuclideanHalfSpace 1) :
    twistRightCollar.{u} i p = mobiusRightCollar i (holeTwist i p.1, p.2) := by
  fin_cases i
  · change (Sum.inl (pantsShear (productCollar.{u} 3 (Or.inr rfl) 1 p)) : MobiusCut.{u}) =
      Sum.inl (productCollar.{u} 3 (Or.inr rfl) 1 ((p.1.1, p.1.2 * p.1.1⁻¹), p.2))
    rw [pantsShear_productCollar_one]
  · change (Sum.inl (pantsShear (productCollar.{u} 3 (Or.inr rfl) 2 p)) : MobiusCut.{u}) =
      Sum.inl (productCollar.{u} 3 (Or.inr rfl) 2 p)
    rw [pantsShear_productCollar_two]

theorem twistRightCollar_source (i : Fin 2) :
    (twistRightCollar.{u} i).source = halfCollarSource := by
  ext p
  exact ⟨fun h => h.1, fun h => ⟨h, trivial, trivial⟩⟩

def twistRightParam (i : Fin 2) : Torus ≃ₜ range (mobiusRightTorus.{u} i) :=
  (holeTwist i).trans (mobiusRightParam i)

abbrev twistPairing : TorusPairing mobiusCutCarrier.{u} where
  count := 2
  gluing := mobiusGluing
  leftParam i := mobiusLeftParam i
  rightParam i := twistRightParam i
  matching i := holeMatching i
  matching_eq i t := by
    change mobiusAttaching i (mobiusLeftParam i t) =
      mobiusRightParam i (holeTwist i (holeMatching i t))
    rw [mobiusAttaching_leftParam, holeTwist_holeMatching]
  leftCollar i := mobiusLeftCollar i
  rightCollar i := twistRightCollar i
  left_source i := mobiusLeftCollar_source i
  right_source i := twistRightCollar_source i
  left_zero _ _ := rfl
  right_zero i t := by
    rw [twistRightCollar_apply]
    rfl
  reversing i := (congrArg (ReversesBoundaryOrientation mobiusCutCarrier.{u} (mobiusLeftCollar i))
    (funext fun p => by
      change twistRightCollar i (holeMatching i p.1, p.2) =
        mobiusRightCollar i (seamMatching p.1, p.2)
      rw [twistRightCollar_apply, holeTwist_holeMatching])).mpr (mobiusReversing i)

def twistCutExternal : BoundaryTori mobiusCutCarrier.{u} 1 where
  collar _ := (productCollar 3 (Or.inr rfl) 0).trans
    (pantsShear.toPartialDiffeomorph.trans partialDiffeomorphSumInl)
  source_eq _ := by
    ext p
    exact ⟨fun h => h.1, fun h => ⟨h, trivial, trivial⟩⟩
  boundary_zero _ t := by
    change (𝓡∂ 3).IsBoundaryPoint
      (Sum.inl (pantsShear (productCollar.{u} 3 (Or.inr rfl) 0 (t, halfZero))) : MobiusCut.{u})
    rw [isBoundaryPoint_inl_iff, pantsShear_productCollar]
    exact (productBoundaryTori.{u} 3 (Or.inr rfl)).boundary_zero 0 _
  disjoint i j hij := (hij (Subsingleton.elim i j)).elim

def outerShearAt (τ : Circle) : Circle :=
  holeShear (planarCollarFormula 3 0 ((τ : ℂ), min (halfZero.val 0) 1))

theorem pantsShear_outer (τ : Torus) :
    pantsShear (productCollar.{u} 3 (Or.inr rfl) 0 ((τ.1, τ.2 * (outerShearAt τ.1)⁻¹), halfZero)) =
      productCollar.{u} 3 (Or.inr rfl) 0 (τ, halfZero) := by
  rw [pantsShear_productCollar]
  change productCollar.{u} 3 (Or.inr rfl) 0
    ((τ.1, τ.2 * (outerShearAt τ.1)⁻¹ * outerShearAt τ.1), halfZero) = _
  rw [inv_mul_cancel_right]

theorem twistCutExternal_image :
    twistCutExternal.{u}.image = mobiusCutExternal.{u}.image := by
  ext x
  simp only [BoundaryTori.image, mem_iUnion, mem_range]
  constructor
  · rintro ⟨k, t, rfl⟩
    refine ⟨k, (t.1, t.2 * outerShearAt t.1), ?_⟩
    change (Sum.inl (productCollar.{u} 3 (Or.inr rfl) 0 ((t.1, t.2 * outerShearAt t.1),
      halfZero)) : MobiusCut.{u}) = Sum.inl (pantsShear (productCollar.{u} 3 (Or.inr rfl) 0
        (t, halfZero)))
    rw [pantsShear_productCollar]
    rfl
  · rintro ⟨k, τ, rfl⟩
    refine ⟨k, (τ.1, τ.2 * (outerShearAt τ.1)⁻¹), ?_⟩
    change (Sum.inl (pantsShear (productCollar.{u} 3 (Or.inr rfl) 0
      ((τ.1, τ.2 * (outerShearAt τ.1)⁻¹), halfZero))) : MobiusCut.{u}) =
        Sum.inl (productCollar.{u} 3 (Or.inr rfl) 0 (τ, halfZero))
    rw [pantsShear_outer]

def twistExternalCollar :
    PartialDiffeomorph halfCollarModel (𝓡∂ 3) (Torus × EuclideanHalfSpace 1)
      mobiusBundleSet.{u} ∞ :=
  (productCollar 3 (Or.inr rfl) 0).trans (pantsShear.toPartialDiffeomorph.trans mobiusOuterLift)

theorem twistExternalCollar_source : twistExternalCollar.{u}.source = halfCollarSource := by
  ext p
  refine ⟨fun hp => hp.1, fun hp => ⟨hp, trivial, ?_⟩⟩
  change 2 < ‖(productCollar.{u} 3 (Or.inr rfl) 0 p).val.1.down‖
  linarith [outer_far ((productCollar.{u} 3 (Or.inr rfl) 0).map_source' hp)]

theorem twistExternalCollar_apply (p : Torus × EuclideanHalfSpace 1) :
    twistExternalCollar.{u} p = mobiusPantsFold (pantsShear (productCollar 3 (Or.inr rfl) 0 p)) :=
  rfl

def twistExternal : BoundaryTori mobiusBundleCarrier.{u} 1 where
  collar _ := twistExternalCollar
  source_eq _ := twistExternalCollar_source
  boundary_zero _ t := by
    change (𝓡∂ 3).IsBoundaryPoint (twistExternalCollar.{u} (t, halfZero))
    rw [mobiusBundleSet_isBoundaryPoint_iff_base, twistExternalCollar_apply,
      mobiusBundleBase_mobiusPantsFold]
    exact productCollar_zero_base.{u} t
  disjoint i j hij := (hij (Subsingleton.elim i j)).elim

theorem isBoundaryPoint_iff_twistExternal (y : mobiusBundleSet.{u}) :
    (𝓡∂ 3).IsBoundaryPoint y ↔ ∃ t, twistExternalCollar.{u} (t, halfZero) = y := by
  rw [isBoundaryPoint_iff_external]
  constructor
  · rintro ⟨τ, rfl⟩
    refine ⟨(τ.1, τ.2 * (outerShearAt τ.1)⁻¹), ?_⟩
    rw [twistExternalCollar_apply, mobiusExternalCollar_apply, pantsShear_outer]
  · rintro ⟨t, rfl⟩
    refine ⟨(t.1, t.2 * outerShearAt t.1), ?_⟩
    rw [twistExternalCollar_apply, mobiusExternalCollar_apply, pantsShear_productCollar]
    rfl

abbrev twistPresentation : TorusPresentation mobiusBundleCarrier.{u} where
  cutCarrier := mobiusCutCarrier
  components := mobiusComponents
  pairing := twistPairing
  externalCount := 1
  external := twistExternal
  cutExternal := twistCutExternal
  external_exhausted := by
    ext y
    rw [BoundaryTori.image, mem_iUnion]
    obtain ⟨z, rfl⟩ : ∃ z : mobiusBundleSet.{u}, z = y := ⟨y, rfl⟩
    change (𝓡∂ 3).IsBoundaryPoint z ↔ ∃ i, ∃ t, twistExternalCollar.{u} (t, halfZero) = z
    rw [isBoundaryPoint_iff_twistExternal]
    exact ⟨fun ⟨t, ht⟩ => ⟨0, t, ht⟩, fun ⟨_, t, ht⟩ => ⟨t, ht⟩⟩
  cut_boundary_exhausted := by
    rw [twistCutExternal_image]
    exact mobiusCut_boundary
  external_disjoint := by
    rw [twistCutExternal_image]
    exact mobiusCut_external_disjoint
  reconstruction := mobiusReconstruction
  quotient_smooth := contMDiff_mobiusFold
  quotient_oriented x := ⟨(Manifold.differentialEquivOfBijective (𝓡∂ 3) (𝓡∂ 3) mobiusFold
    mfderiv_mobiusFold_bijective x).toLinearEquiv, fun _ => rfl,
      orientation_map_mobiusCutOrientation x⟩
  interiorImage := mobiusInteriorImage
  interiorDiffeomorph := mobiusInteriorDiffeomorph
  interior_map _ := rfl
  seam i := mobiusSeamAt i
  seam_source _ := rfl
  seam_zero := mobiusPresentation.seam_zero
  seam_positive i t s hs hs1 := by
    rw [mobiusPresentation.seam_positive i t s hs hs1]
    change mobiusFold (mobiusRightCollar i (seamMatching t, halfPoint s hs)) =
      mobiusFold (twistRightCollar i (holeMatching i t, halfPoint s hs))
    rw [twistRightCollar_apply, holeTwist_holeMatching]
  seam_negative := mobiusPresentation.seam_negative
  seam_interior := mobiusPresentation.seam_interior
  seam_disjoint := mobiusPresentation.seam_disjoint
  marked_collar _ _ _ := rfl
  external_seam_disjoint _ j := by
    rw [Set.disjoint_left]
    rintro y ⟨⟨hy1, -⟩, hy2⟩ hys
    have hJ := mem_planarModel_of_outer hy1
    have hfar := outer_far hy2
    change 11 / 4 < ‖(pantsOf y).val.1.down‖ at hfar
    rw [pantsOf_val hJ] at hfar
    have := norm_base_lt_of_seam j hys
    change 11 / 4 < ‖mobiusBundleBase y‖ at hfar
    linarith
  leftPiece i := i.succ
  rightPiece _ := 0
  left_owned := mobiusPresentation.left_owned
  right_owned := mobiusPresentation.right_owned
  externalPiece _ := 0
  external_owned _ := by
    rintro _ ⟨t, rfl⟩
    exact ⟨_, rfl⟩

abbrev twistData : SeifertData :=
  ⟨3, 1, [(2, 1), (2, -1)], [], by norm_num, le_rfl, by decide, by decide, rfl⟩

theorem twistData_eq : twistData = twistedIBundleData := rfl

def twistProductPortFun (j : Fin 3) : twistPresentation.{u}.OwnedSide 0 :=
  Fin.cases ⟨.inr (.inr 0), rfl⟩ (fun m => ⟨.inr (.inl m), rfl⟩) j

def twistProductPortInv : twistPresentation.{u}.OwnedSide 0 → Fin 3
  | ⟨.inl m, _⟩ => m.succ
  | ⟨.inr (.inl m), _⟩ => m.succ
  | ⟨.inr (.inr _), _⟩ => 0

def twistProductPort : Fin 3 ≃ twistPresentation.{u}.OwnedSide 0 where
  toFun := twistProductPortFun
  invFun := twistProductPortInv
  left_inv j := by
    fin_cases j <;> rfl
  right_inv s := by
    rcases s with ⟨m | m | e, h⟩
    · exact absurd h (Fin.succ_ne_zero m)
    · rfl
    · obtain rfl : e = 0 := Subsingleton.elim e 0
      rfl

def twistProductPiece : ProductFibredPiece twistPresentation.{u} 0 3 where
  base := pantsPlanarBase
  port := twistProductPort
  trivialization := (productDiffeomorph 3).trans
    (pantsShear.trans (sumInlRangeDiffeomorph (I := 𝓡∂ 3)).symm)
  collar_eq j p hp := by
    apply Subtype.ext
    rw [TorusPresentation.pieceCollar_apply _ _ _ hp]
    fin_cases j <;> rfl

def twistSolidPort (m : Fin 2) : Fin 1 ≃ twistPresentation.{u}.OwnedSide m.succ where
  toFun _ := ⟨.inl m, rfl⟩
  invFun _ := 0
  left_inv j := Subsingleton.elim _ _
  right_inv s := by
    rcases s with ⟨m' | m' | e, h⟩
    · obtain rfl : m' = m := Fin.succ_injective 2 h
      rfl
    · exact absurd h.symm (Fin.succ_ne_zero m)
    · exact absurd h.symm (Fin.succ_ne_zero m)

def twistSolidPiece (m : Fin 2) : SolidTorusPiece twistPresentation.{u} m.succ where
  base := discPlanarBase 2
  port := twistSolidPort m
  trivialization := solidDiffeomorph.trans (solidPieceDiffeomorph m).symm
  collar_eq j p hp := by
    apply Subtype.ext
    rw [TorusPresentation.pieceCollar_apply _ _ _ hp, Subsingleton.elim j 0]
    rfl

def twistPieceEquiv :
    Option (Fin twistData.fillingCount) ≃ Fin twistPresentation.{u}.components.count where
  toFun o := o.elim 0 Fin.succ
  invFun k := Fin.cases none some k
  left_inv o := by
    rcases o with _ | m <;> rfl
  right_inv k := by
    fin_cases k <;> rfl

def twistPortEquiv : Fin twistData.ports ⊕ Fin twistData.fillingCount ≃ Fin twistData.k where
  toFun := Sum.elim (fun _ => 0) Fin.succ
  invFun k := Fin.cases (.inl 0) .inr k
  left_inv o := by
    rcases o with r | m
    · obtain rfl : r = 0 := Subsingleton.elim r 0
      rfl
    · rfl
  right_inv k := by
    fin_cases k <;> rfl

def twistBlock : SeifertBlock mobiusBundleCarrier.{u} twistData where
  presentation := twistPresentation
  piece := twistPieceEquiv.{u}
  product := twistProductPiece
  solid m := twistSolidPiece m
  port := twistPortEquiv
  seam := Equiv.refl _
  free := Equiv.refl _
  free_port r := by
    obtain rfl : r = 0 := Subsingleton.elim r 0
    rfl
  filled_port _ := rfl
  solid_port _ := rfl
  slope m := by
    fin_cases m
    · exact twistedMatching_meridian
    · exact seamMatching_meridian

def mobiusTwistedIBundle : TwistedIBundle mobiusBundleCarrier.{u} := twistBlock

end GC.Seifert
