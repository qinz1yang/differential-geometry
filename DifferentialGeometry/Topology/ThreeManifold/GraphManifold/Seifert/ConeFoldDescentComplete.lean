import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Seifert.ConeFoldDescentExhaust

/-!
# Completeness data of the cone-fold descent

`exhaustFn p = exhaust (conePoint (mirrorMap p))` is the exhaustion of the filled base pulled back
to the descent domain. Every point of the domain lies over a point `z'` of `U` with the same
height and the same `η₀` at which the base value is `f z'` or its conjugate, so
`exhaustFn p = exhaust (f z')` (`exists_exhaustFn_eq`). High in the outer cusp this is
`log y = p 1` (`exhaustFn_eq_cuspInf`, by the outer cusp control of `FoldData` and the explicit
inverse of the outer profile), deep in the inner cusp it is `-log η₀ = (S·p) 1` for the Möbius
isometry `S z = -1/z` (`exhaustFn_eq_cuspZero`, `mobiusLogMap_inv_one`); away from the inner cusp
the height on the triangle is bounded below (`lowHeight_le`), so the rest of the triangle is
compact. The metric facts used for the gradient bound are recorded here: `|v 1| ≤ ‖v‖_g`, the
Euclidean norm is controlled by `‖v‖_g` below a given height, and isometries preserve
`coordinateInner`; the bound itself is in `ConeFoldDescentBound`.
-/

set_option autoImplicit false
noncomputable section
open Complex Set Filter Topology
open DifferentialGeometry DifferentialGeometry.Topology GC.Endpoint GC.GraphManifold GC.Geometry
open scoped ContDiff ComplexConjugate Manifold

universe u

namespace GC.Seifert

private abbrev coord (i : Fin 3) : ModelCoordinates →L[ℝ] ℝ :=
  PiLp.proj 2 (fun _ : Fin 3 => ℝ) i

private theorem coordinateInner_hyp_self (p v : ModelCoordinates) :
    coordinateInner .hyperbolicProduct p v v =
      ((Real.exp (p 1))⁻¹ * v 0) ^ 2 + v 1 ^ 2 + v 2 ^ 2 := by
  simp only [coordinateInner, coordinateCoframe, Fin.sum_univ_three, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, Real.exp_neg]
  ring

theorem abs_one_le_sqrt_coordinateInner (p v : ModelCoordinates) :
    |v 1| ≤ Real.sqrt (coordinateInner .hyperbolicProduct p v v) := by
  apply Real.abs_le_sqrt
  rw [coordinateInner_hyp_self]
  nlinarith [sq_nonneg ((Real.exp (p 1))⁻¹ * v 0), sq_nonneg (v 2)]

theorem norm_le_mul_sqrt_coordinateInner_of_exp_le {Y : ℝ} (hY : 0 ≤ Y) {p : ModelCoordinates}
    (h : Real.exp (p 1) ≤ Y)
    (v : ModelCoordinates) :
    ‖v‖ ≤ (Y + 1) * Real.sqrt (coordinateInner .hyperbolicProduct p v v) := by
  have he := Real.exp_pos (p 1)
  have hQ : 0 ≤ coordinateInner .hyperbolicProduct p v v := by
    rw [coordinateInner_hyp_self]
    positivity
  rw [EuclideanSpace.norm_eq, Fin.sum_univ_three]
  simp only [Real.norm_eq_abs, sq_abs]
  rw [← Real.sqrt_sq (by positivity : (0 : ℝ) ≤ Y + 1), ← Real.sqrt_mul (by positivity)]
  apply Real.sqrt_le_sqrt
  rw [coordinateInner_hyp_self]
  have h0 : v 0 = Real.exp (p 1) * ((Real.exp (p 1))⁻¹ * v 0) := by field_simp
  have h1 : v 0 ^ 2 ≤ (Y + 1) ^ 2 * ((Real.exp (p 1))⁻¹ * v 0) ^ 2 := by
    rw [h0, mul_pow]
    have : Real.exp (p 1) ^ 2 ≤ (Y + 1) ^ 2 := by nlinarith
    have hh : (Real.exp (p 1))⁻¹ * (Real.exp (p 1) * ((Real.exp (p 1))⁻¹ * v 0)) =
        (Real.exp (p 1))⁻¹ * v 0 := by field_simp
    rw [hh]
    exact mul_le_mul_of_nonneg_right this (sq_nonneg _)
  have h2 : (1 : ℝ) ≤ (Y + 1) ^ 2 := by nlinarith
  nlinarith [sq_nonneg (v 1), sq_nonneg (v 2)]

theorem coordinateInner_fderiv_of_pullbackMetric_eq
    {γ : ModelCoordinates ≃ₘ⟮𝓡 3, 𝓡 3⟯ ModelCoordinates}
    (hγ : Diffeomorph.pullbackMetric (coordinateModelMetric .hyperbolicProduct) γ =
      coordinateModelMetric .hyperbolicProduct) (p v : ModelCoordinates) :
    coordinateInner .hyperbolicProduct (γ p) (fderiv ℝ γ p v) (fderiv ℝ γ p v) =
      coordinateInner .hyperbolicProduct p v v := by
  have h := Diffeomorph.pullbackMetric_inner (coordinateModelMetric .hyperbolicProduct) γ p v v
  rw [hγ] at h
  have h2 := (coordinateModelMetric_inner .hyperbolicProduct p v v).symm.trans
    (h.trans (coordinateModelMetric_inner _ _ _ _))
  rw [mfderiv_eq_fderiv] at h2
  exact h2.symm

def invMatrix : Matrix (Fin 2) (Fin 2) ℝ := !![0, -1; 1, 0]

theorem invMatrix_det : 0 < invMatrix.det := by
  simp [invMatrix, Matrix.det_fin_two_of]

theorem mobiusLogMap_inv_one (p : ModelCoordinates) :
    mobiusLogMap (glOfDet invMatrix invMatrix_det) 0 p 1 =
      -Real.log (cuspZeroHeight (logPoint p : ℂ)) := by
  have hz := logPoint_im_pos p
  have hdet : |((glOfDet invMatrix invMatrix_det).det : ℝ)| = 1 := by
    simp [glOfDet, invMatrix, Matrix.det_fin_two_of]
  rw [mobiusLogMap, logCoords_one, UpperHalfPlane.im_smul_eq_div_normSq, hdet, one_mul]
  have hden : UpperHalfPlane.denom (glOfDet invMatrix invMatrix_det) (logPoint p) =
      (logPoint p : ℂ) := by
    change ((invMatrix 1 0 : ℝ) : ℂ) * _ + ((invMatrix 1 1 : ℝ) : ℂ) = _
    simp [invMatrix]
  rw [hden, cuspZeroHeight, ← Real.log_inv, inv_div, UpperHalfPlane.coe_im]

namespace ConeShape.FoldData

variable {σ : ConeShape} (D : σ.FoldData) (c : ConeFilling) (hθ : σ.θ₁ * c.p = Real.pi)

def exhaustFn (p : ModelCoordinates) : ℝ := D.exhaust (c.conePoint (D.mirrorMap.{u} c p))

theorem conePoint_totalMap_eq_f {p : ModelCoordinates} (hσ : σ.θ₂ = 0)
    (hz : (logPoint p : ℂ) ∈ D.patches c hθ) (hre : 0 ≤ (logPoint p : ℂ).re) :
    (logPoint p : ℂ) ∈ D.U ∧ c.conePoint (D.totalMap.{u} c p) = D.f (logPoint p) := by
  by_cases hd : (logPoint p : ℂ) ∈ D.patchDisc c hθ
  · obtain ⟨hU, hf, -, -⟩ := D.discRadius_spec c hθ hd.1 hd.2
    rw [D.totalMap_eq_tubeMap_of_mem_patchDisc c hθ hd, conePoint_tubeMap, hf]
    exact ⟨hU, rfl⟩
  · obtain ⟨hU, hv, -, hf, -⟩ := D.patches_good c hθ hσ hz hre hd
    rw [totalMap, ite_eq_right hv, D.conePoint_liftMap c hf]
    exact ⟨hU, rfl⟩

theorem exists_exhaustFn_eq (hσ : σ.θ₂ = 0) {p : ModelCoordinates}
    (hp : p ∈ D.descentDomain c hθ) :
    ∃ z' : ℂ, z' ∈ D.U ∧ z'.im = Real.exp (p 1) ∧
      cuspZeroHeight z' = cuspZeroHeight (logPoint p : ℂ) ∧
      D.exhaustFn.{u} c p = D.exhaust (D.f z') := by
  have hp' : (logPoint p : ℂ) ∈ D.descentBase c hθ := hp
  have him : (logPoint p : ℂ).im = Real.exp (p 1) := by rw [coe_logPoint']
  by_cases h : p 0 < 0
  · have hz : (logPoint (flipMap p) : ℂ) ∈ D.patches c hθ := by
      rw [coe_logPoint_flipMap]
      exact D.refl_mem_patches_of_mem_descentBase c hθ hp' (by rw [logPoint_re_eq']; exact h.le)
    have hre : 0 ≤ (logPoint (flipMap p) : ℂ).re := by
      rw [logPoint_re_eq', flipMap_zero]
      linarith
    obtain ⟨hU, hf⟩ := D.conePoint_totalMap_eq_f c hθ hσ hz hre
    refine ⟨_, hU, ?_, ?_, ?_⟩
    · rw [coe_logPoint_flipMap, σ.im_refl_zero, him]
    · rw [coe_logPoint_flipMap, cuspZeroHeight, cuspZeroHeight, σ.im_refl_zero]
      congr 1
      simp [ConeShape.refl, Complex.normSq_neg, Complex.normSq_conj]
    · rw [exhaustFn, D.mirrorMap_of_neg c h, conePoint_conjMap, hf, D.exhaust_conj]
  · have hre : 0 ≤ (logPoint p : ℂ).re := by rw [logPoint_re_eq']; exact not_lt.1 h
    obtain ⟨hU, hf⟩ := D.conePoint_totalMap_eq_f c hθ hσ
      (D.mem_patches_of_mem_descentBase c hθ hp' hre) hre
    exact ⟨_, hU, him, rfl, by rw [exhaustFn, D.mirrorMap_of_nonneg c (not_lt.1 h), hf]⟩

def topHeight : ℝ := max D.cuspInfHeight (Real.exp (Real.log (D.outerY₂ + 1) + 1))

def bottomHeight : ℝ := min D.cuspZeroBound (Real.exp (-(-Real.log (D.outerY₂ / 2) + 1)))

theorem bottomHeight_pos : 0 < D.bottomHeight := lt_min D.cuspZeroBound_pos (Real.exp_pos _)

theorem bottomHeight_lt : D.bottomHeight < D.outerY₂ := by
  have hY := D.outerY₂_pos
  have e : Real.exp (-(-Real.log (D.outerY₂ / 2) + 1)) = D.outerY₂ / 2 * Real.exp (-1) := by
    rw [show -(-Real.log (D.outerY₂ / 2) + 1) = Real.log (D.outerY₂ / 2) + -1 by ring,
      Real.exp_add, Real.exp_log (by linarith)]
  have : Real.exp (-1) < 1 := by
    have := Real.exp_lt_exp.2 (show (-1 : ℝ) < 0 by norm_num)
    rwa [Real.exp_zero] at this
  have h1 := min_le_right D.cuspZeroBound (Real.exp (-(-Real.log (D.outerY₂ / 2) + 1)))
  change min D.cuspZeroBound (Real.exp (-(-Real.log (D.outerY₂ / 2) + 1))) < D.outerY₂
  rw [e] at h1 ⊢
  nlinarith

theorem exhaustFn_eq_cuspInf (hσ : σ.θ₂ = 0) {p : ModelCoordinates}
    (hp : p ∈ D.descentDomain c hθ) (hy : D.topHeight < Real.exp (p 1)) :
    D.exhaustFn.{u} c p = p 1 := by
  obtain ⟨z', hU, him, -, he⟩ := D.exists_exhaustFn_eq c hθ hσ hp
  have h1 : D.cuspInfHeight < z'.im := by
    rw [him]
    exact lt_of_le_of_lt (le_max_left _ _) hy
  have h2 : Real.exp (Real.log (D.outerY₂ + 1) + 1) ≤ Real.exp (p 1) :=
    (le_max_right _ _).trans hy.le
  have hY1 : D.outerY₂ + 1 ≤ Real.exp (Real.log (D.outerY₂ + 1) + 1) := by
    rw [Real.exp_add, Real.exp_log (by linarith [D.outerY₂_pos])]
    nlinarith [Real.add_one_le_exp (1 : ℝ), D.outerY₂_pos]
  have hn := D.norm_f_cuspInf z' hU h1
  rw [he, exhaust, hn, him, D.outerExhaust_outerProfile h2, Real.log_exp]
  rw [D.innerExhaust_eq_zero, add_zero]
  have hK := σ.constK_pos
  have hY := D.outerY₂_pos
  have hgt : outerProfile σ.constK D.outerY₁ D.outerY₂ D.outerY₂ <
      outerProfile σ.constK D.outerY₁ D.outerY₂ z'.im :=
    D.outerProfile_lt_outerProfile hY (by rw [him]; linarith)
  rw [outerProfile_self D.outerY₁_lt hY] at hgt
  have hlt : coneProfile σ.constK (D.outerY₂ / 2) < coneProfile σ.constK D.outerY₂ :=
    strictMonoOn_coneProfile hK (by positivity : (0 : ℝ) ≤ D.outerY₂ / 2) hY.le (by linarith)
  have htri : ‖D.f z'‖ ≤ ‖D.f z' + 3 / 2‖ + 3 / 2 := by
    have := norm_sub_le (D.f z' + 3 / 2) (3 / 2 : ℂ)
    rw [add_sub_cancel_right] at this
    have h32 : ‖(3 / 2 : ℂ)‖ = 3 / 2 := by norm_num
    linarith
  rw [hn] at htri
  linarith

theorem exhaustFn_eq_cuspZero (hσ : σ.θ₂ = 0) {p : ModelCoordinates}
    (hp : p ∈ D.descentDomain c hθ) (hη : cuspZeroHeight (logPoint p : ℂ) < D.bottomHeight) :
    D.exhaustFn.{u} c p = -Real.log (cuspZeroHeight (logPoint p : ℂ)) := by
  obtain ⟨z', hU, him, hη', he⟩ := D.exists_exhaustFn_eq c hθ hσ hp
  have hK := σ.constK_pos
  have hY := D.outerY₂_pos
  have hpos : 0 < cuspZeroHeight (logPoint p : ℂ) := by
    unfold cuspZeroHeight
    have hz := logPoint_im_pos p
    exact div_pos (Complex.normSq_pos.2 (ConeShape.ne_zero_of_im_pos hz)) hz
  have h1 : cuspZeroHeight z' < D.cuspZeroBound := by
    rw [hη']
    exact lt_of_lt_of_le hη (min_le_left _ _)
  have hn := D.norm_f_cuspZero hσ z' hU h1
  rw [hη'] at hn
  rw [he, exhaust, hn, D.innerExhaust_coneProfile hpos (hη.le.trans (min_le_right _ _)),
    D.outerExhaust_eq_zero, zero_add]
  have hlt := D.bottomHeight_lt
  have hG : coneProfile σ.constK (cuspZeroHeight (logPoint p : ℂ)) <
      coneProfile σ.constK D.outerY₂ :=
    strictMonoOn_coneProfile hK hpos.le hY.le (by linarith)
  have htri : ‖D.f z'‖ ≤ ‖D.f z' + 3 / 2‖ + 3 / 2 := by
    have := norm_sub_le (D.f z' + 3 / 2) (3 / 2 : ℂ)
    rw [add_sub_cancel_right] at this
    have h32 : ‖(3 / 2 : ℂ)‖ = 3 / 2 := by norm_num
    linarith
  rw [hn] at htri
  have hR := D.outerProfile_lt_outerProfile hY (show D.outerY₂ < D.outerY₂ + 1 by linarith)
  rw [outerProfile_self D.outerY₁_lt hY] at hR
  linarith

theorem lowHeight_le (hσ : σ.θ₂ = 0) {z : ℂ} (hz : z ∈ σ.triangle)
    (hη : D.bottomHeight ≤ cuspZeroHeight z) :
    min (1 / 2) (D.bottomHeight / (2 * (1 / (1 / 2 - σ.width) ^ 2 + 1))) ≤ z.im := by
  set w := 1 / 2 - σ.width
  have hw : 0 < w := by have := σ.descentWidth_lt_half; simp only [w]; linarith
  set Cw := 1 / w ^ 2 + 1
  have hCw : 0 < Cw := by positivity
  have hb := D.bottomHeight_pos
  by_contra hc
  push Not at hc
  have hy := hz.1
  set x := z.re
  set y := z.im
  have hy1 : y < 1 / 2 := lt_of_lt_of_le hc (min_le_left _ _)
  have hy2 : y < D.bottomHeight / (2 * Cw) := lt_of_lt_of_le hc (min_le_right _ _)
  have hx0 : 0 ≤ x := hz.2 0
  have hxW : x ≤ σ.width := by have := hz.2 1; simp only [ConeShape.wallSide] at this; linarith
  have hc4 := σ.cusp_centre hσ
  have hw2 : 0 ≤ (x - 1 / 4) ^ 2 + y ^ 2 - 1 / 16 := by
    have := hz.2 2
    simp only [ConeShape.wallSide, hc4] at this
    exact this
  have hxw : x * w ≤ y ^ 2 := by
    simp only [w]
    nlinarith
  have hx2 : x ≤ y ^ 2 / w := by rw [le_div_iff₀ hw]; linarith
  have hx3 : x ^ 2 ≤ y ^ 2 / w ^ 2 := by
    have h1 : x ^ 2 ≤ (y ^ 2 / w) ^ 2 := pow_le_pow_left₀ hx0 hx2 2
    have h2 : (y ^ 2 / w) ^ 2 ≤ y ^ 2 / w ^ 2 := by
      rw [div_pow, div_le_div_iff_of_pos_right (by positivity)]
      have hy3 : y ^ 2 ≤ 1 := by nlinarith
      calc (y ^ 2) ^ 2 = y ^ 2 * y ^ 2 := by ring
        _ ≤ y ^ 2 * 1 := mul_le_mul_of_nonneg_left hy3 (sq_nonneg y)
        _ = y ^ 2 := by ring
    linarith
  have hN : normSq z ≤ y ^ 2 * Cw := by
    rw [Complex.normSq_apply]
    have : y ^ 2 / w ^ 2 = y ^ 2 * (1 / w ^ 2) := by ring
    simp only [Cw]
    nlinarith
  have hη2 : cuspZeroHeight z ≤ y * Cw := by
    unfold cuspZeroHeight
    rw [div_le_iff₀ hy]
    nlinarith
  have : y * Cw < D.bottomHeight / 2 := by
    rw [lt_div_iff₀ (by positivity : (0 : ℝ) < 2 * Cw)] at hy2
    linarith
  linarith

end ConeShape.FoldData

end GC.Seifert
