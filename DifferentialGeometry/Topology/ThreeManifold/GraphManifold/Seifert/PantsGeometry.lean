import DifferentialGeometry.Geometry.Thurston.Descent
import DifferentialGeometry.Geometry.Thurston.Models.HomogeneousCompleteness
import Mathlib.Analysis.Complex.UpperHalfPlane.Manifold
import Mathlib.Analysis.Complex.UpperHalfPlane.FixedPoints
import Mathlib.NumberTheory.ModularForms.ProperlyDiscontinuous
import Mathlib.NumberTheory.ModularForms.CongruenceSubgroups

/-!
# A complete `H² × ℝ` geometry on (open pants) × S¹: the group side

`mobiusLog g hg` is the Möbius action of `g ∈ GL(2, ℝ)` with `0 < det g` on the upper half-plane,
written in the log chart `x + i eʸ ↦ (x, y)` of the `.hyperbolicProduct` model
`e^{-2y} dx² + dy² + dz²` and trivial on `z`; `mobiusLog_inner` says it is an isometry of the
model (`logPointDeriv` is the derivative of the chart, the Möbius map multiplies it by
`det g / (c w + d)²`). `pantsGroup = ⟨T, U₄⟩` with `U₄ = [[1, 0], [4, 1]]` lies in `Γ₁(4)`, and
`gamma1_four_free`: a point of `ℍ` fixed by `γ ∈ Γ₁(4)` forces `γ` central (so `γ = 1`) or
elliptic, and the trace of an element of `Γ₁(4)` is `≡ 2 mod 4`, never in `(-2, 2)`.
`SL(2, ℤ)` acts properly discontinuously on `ℍ` (pulled back from `𝒮ℒ`), hence so does
`pantsGroup`. The product `pantsGroup × Multiplicative ℤ` acts on `ModelCoordinates` by
`mobiusLogMap` (Möbius in `(x, y)`, unit translation in `z`), freely, properly discontinuously,
smoothly and isometrically; `pantsQuotientGeometry` is K13's `GeometricStructure.quotient` of
`coordinateGeometricStructure .hyperbolicProduct` on `PantsQuotient`, of model
`.hyperbolicProduct`.
-/

set_option autoImplicit false
noncomputable section
open DifferentialGeometry GC.Geometry UpperHalfPlane Matrix MulAction CongruenceSubgroup
open scoped Manifold ContDiff MatrixGroups UpperHalfPlane

namespace GC.Seifert

private abbrev coord (i : Fin 3) : ModelCoordinates →L[ℝ] ℝ :=
  PiLp.proj 2 (fun _ : Fin 3 => ℝ) i

def logPoint (p : ModelCoordinates) : ℍ :=
  ⟨(p 0 : ℂ) + (Real.exp (p 1) : ℂ) * Complex.I, by simp [-Complex.ofReal_exp, Real.exp_pos]⟩

theorem coe_logPoint (p : ModelCoordinates) :
    (logPoint p : ℂ) = (p 0 : ℂ) + (Real.exp (p 1) : ℂ) * Complex.I :=
  rfl

@[simp] theorem logPoint_re (p : ModelCoordinates) : (logPoint p).re = p 0 := by
  rw [← coe_re, coe_logPoint]
  simp

@[simp] theorem logPoint_im (p : ModelCoordinates) : (logPoint p).im = Real.exp (p 1) := by
  rw [← coe_im, coe_logPoint]
  simp [-Complex.ofReal_exp]

def logCoords (z : ℍ) (t : ℝ) : ModelCoordinates :=
  !₂[z.re, Real.log z.im, t]

@[simp] theorem logCoords_zero (z : ℍ) (t : ℝ) : logCoords z t 0 = z.re := by
  simp [logCoords]

@[simp] theorem logCoords_one (z : ℍ) (t : ℝ) : logCoords z t 1 = Real.log z.im := by
  simp [logCoords]

@[simp] theorem logCoords_two (z : ℍ) (t : ℝ) : logCoords z t 2 = t := by
  simp [logCoords]

@[simp] theorem logPoint_logCoords (z : ℍ) (t : ℝ) : logPoint (logCoords z t) = z :=
  ext_re_im (by simp) (by simp [Real.exp_log z.im_pos])

@[simp] theorem logCoords_logPoint (p : ModelCoordinates) : logCoords (logPoint p) (p 2) = p := by
  ext i
  fin_cases i <;> simp

def mobiusLogMap (g : GL (Fin 2) ℝ) (t : ℝ) (p : ModelCoordinates) : ModelCoordinates :=
  logCoords (g • logPoint p) (p 2 + t)

theorem mobiusLogMap_mobiusLogMap (g h : GL (Fin 2) ℝ) (s t : ℝ) (p : ModelCoordinates) :
    mobiusLogMap g s (mobiusLogMap h t p) = mobiusLogMap (g * h) (t + s) p := by
  simp only [mobiusLogMap, logPoint_logCoords, logCoords_two, mul_smul, add_assoc]

theorem mobiusLogMap_one (p : ModelCoordinates) : mobiusLogMap 1 0 p = p := by
  simp [mobiusLogMap]

theorem contDiff_coe_logPoint :
    ContDiff ℝ ∞ (fun p : ModelCoordinates => (logPoint p : ℂ)) := by
  have hc (j : Fin 3) : ContDiff ℝ ∞ (fun q : ModelCoordinates => q j) := (coord j).contDiff
  have hof : ContDiff ℝ ∞ (fun x : ℝ => (x : ℂ)) := Complex.ofRealCLM.contDiff
  exact (hof.comp (hc 0)).add ((hof.comp (hc 1).exp).mul contDiff_const)

theorem continuous_logPoint : Continuous logPoint :=
  isEmbedding_coe.continuous_iff.mpr contDiff_coe_logPoint.continuous

theorem contDiff_mobiusLogMap {g : GL (Fin 2) ℝ} (hg : 0 < g.det.val) (t : ℝ) :
    ContDiff ℝ ∞ (mobiusLogMap g t) := by
  have hc (j : Fin 3) : ContDiff ℝ ∞ (fun q : ModelCoordinates => q j) := (coord j).contDiff
  have hw := contDiff_coe_logPoint
  have hfun : (fun p : ModelCoordinates => ((g • logPoint p : ℍ) : ℂ)) =
      fun p => num g (logPoint p) * (denom g (logPoint p))⁻¹ := by
    funext p
    rw [coe_smul_of_det_pos hg, div_eq_mul_inv]
  have hM : ContDiff ℝ ∞ (fun p : ModelCoordinates => ((g • logPoint p : ℍ) : ℂ)) := by
    rw [hfun]
    exact ((contDiff_const.mul hw).add contDiff_const).mul
      (((contDiff_const.mul hw).add contDiff_const).inv fun p => denom_ne_zero g (logPoint p))
  refine contDiff_euclidean.2 fun i => ?_
  fin_cases i
  · change ContDiff ℝ ∞ (fun p : ModelCoordinates => (g • logPoint p).re)
    have h := Complex.reCLM.contDiff.comp hM
    simp only [Function.comp_def, Complex.reCLM_apply, coe_re] at h
    exact h
  · change ContDiff ℝ ∞ (fun p : ModelCoordinates => Real.log (g • logPoint p).im)
    have h := Complex.imCLM.contDiff.comp hM
    simp only [Function.comp_def, Complex.imCLM_apply, coe_im] at h
    exact h.log fun p => (g • logPoint p).im_pos.ne'
  · change ContDiff ℝ ∞ (fun p : ModelCoordinates => p 2 + t)
    exact (hc 2).add contDiff_const

def logPointDeriv (q : ModelCoordinates) : ModelCoordinates →L[ℝ] ℂ :=
  Complex.ofRealCLM ∘L coord 0 + Complex.I • (Complex.ofRealCLM ∘L (Real.exp (q 1) • coord 1))

theorem logPointDeriv_apply (q v : ModelCoordinates) :
    logPointDeriv q v = (v 0 : ℂ) + ((Real.exp (q 1) * v 1 : ℝ) : ℂ) * Complex.I := by
  simp only [logPointDeriv, _root_.add_apply, ContinuousLinearMap.comp_apply,
    _root_.smul_apply, Complex.ofRealCLM_apply, PiLp.proj_apply, smul_eq_mul,
    Complex.ofReal_mul]
  ring

theorem hasFDerivAt_logPoint (q : ModelCoordinates) :
    HasFDerivAt (fun p : ModelCoordinates => (logPoint p : ℂ)) (logPointDeriv q) q := by
  have h0 : HasFDerivAt (fun p : ModelCoordinates => ((p 0 : ℝ) : ℂ))
      (Complex.ofRealCLM ∘L coord 0) q :=
    Complex.ofRealCLM.hasFDerivAt.comp q (coord 0).hasFDerivAt
  have h1 : HasFDerivAt (fun p : ModelCoordinates => ((Real.exp (p 1) : ℝ) : ℂ))
      (Complex.ofRealCLM ∘L (Real.exp (q 1) • coord 1)) q :=
    Complex.ofRealCLM.hasFDerivAt.comp q (coord 1).hasFDerivAt.exp
  have hfun : (fun p : ModelCoordinates => (logPoint p : ℂ)) =
      fun p => ((p 0 : ℝ) : ℂ) + Complex.I * ((Real.exp (p 1) : ℝ) : ℂ) :=
    funext fun p => by rw [coe_logPoint, mul_comm]
  rw [hfun]
  exact h0.add (h1.const_mul Complex.I)

theorem logPointDeriv_mobiusLogMap {g : GL (Fin 2) ℝ} (hg : 0 < g.det.val) (t : ℝ)
    (p v : ModelCoordinates) :
    logPointDeriv (mobiusLogMap g t p) (fderiv ℝ (mobiusLogMap g t) p v) =
      ((g.det.val : ℂ) / denom g (logPoint p) ^ 2) * logPointDeriv p v := by
  have hd : DifferentiableAt ℝ (mobiusLogMap g t) p :=
    (contDiff_mobiusLogMap hg t).differentiable (by decide) p
  have h1 := (hasFDerivAt_logPoint (mobiusLogMap g t p)).comp p hd.hasFDerivAt
  have h2 := (hasStrictFDerivAt_smul g (logPoint p)).hasFDerivAt.comp p (hasFDerivAt_logPoint p)
  have h2' : HasFDerivAt ((fun q : ModelCoordinates => (logPoint q : ℂ)) ∘ mobiusLogMap g t)
      ((smulFDeriv g (logPoint p)).comp (logPointDeriv p)) p :=
    h2.congr_of_eventuallyEq (Filter.Eventually.of_forall fun q => by
      simp [mobiusLogMap, ofComplex_apply])
  have h := congrArg (fun L : ModelCoordinates →L[ℝ] ℂ => L v) (h1.unique h2')
  simp only [ContinuousLinearMap.comp_apply] at h
  have hg' : 0 < (g : Matrix (Fin 2) (Fin 2) ℝ).det := by
    rwa [← Matrix.GeneralLinearGroup.val_det_apply]
  rw [h]
  simp [smulFDeriv, σ, hg']
  ring

theorem fderiv_mobiusLogMap_two {g : GL (Fin 2) ℝ} (hg : 0 < g.det.val) (t : ℝ)
    (p v : ModelCoordinates) : fderiv ℝ (mobiusLogMap g t) p v 2 = v 2 := by
  have hd : DifferentiableAt ℝ (mobiusLogMap g t) p :=
    (contDiff_mobiusLogMap hg t).differentiable (by decide) p
  have h := (coord 2).hasFDerivAt.comp p hd.hasFDerivAt
  have hfun : (coord 2 ∘ mobiusLogMap g t) = fun q : ModelCoordinates => q 2 + t :=
    funext fun q => by simp [mobiusLogMap]
  rw [hfun] at h
  have h' : HasFDerivAt (fun q : ModelCoordinates => q 2 + t) (coord 2) p :=
    (coord 2).hasFDerivAt.add_const t
  have := congrArg (fun L : ModelCoordinates →L[ℝ] ℝ => L v) (h.unique h')
  simpa using this

private theorem inner_algebra {α β s E δ N v0 v1 w0 w1 a0 a1 b0 b1 : ℝ} (hs : 0 < s)
    (hδ : 0 < δ) (hN : 0 < N) (hE : E = δ * s / N) (hA : α ^ 2 + β ^ 2 = δ ^ 2 / N ^ 2)
    (ha0 : a0 = α * v0 - β * (s * v1)) (ha1 : E * a1 = β * v0 + α * (s * v1))
    (hb0 : b0 = α * w0 - β * (s * w1)) (hb1 : E * b1 = β * w0 + α * (s * w1)) :
    E⁻¹ * a0 * (E⁻¹ * b0) + a1 * b1 = s⁻¹ * v0 * (s⁻¹ * w0) + v1 * w1 := by
  have hE0 : E ≠ 0 := by rw [hE]; positivity
  have h1 : E⁻¹ * a0 * (E⁻¹ * b0) + a1 * b1 = (a0 * b0 + (E * a1) * (E * b1)) / E ^ 2 := by
    field_simp
  have h2 : a0 * b0 + (E * a1) * (E * b1) =
      (α ^ 2 + β ^ 2) * (v0 * w0 + s ^ 2 * (v1 * w1)) := by
    rw [ha0, ha1, hb0, hb1]
    ring
  rw [h1, h2, hA, hE]
  field_simp

theorem mobiusLogMap_coordinateInner {g : GL (Fin 2) ℝ} (hg : 0 < g.det.val) (t : ℝ)
    (p v w : ModelCoordinates) :
    coordinateInner .hyperbolicProduct (mobiusLogMap g t p) (fderiv ℝ (mobiusLogMap g t) p v)
      (fderiv ℝ (mobiusLogMap g t) p w) = coordinateInner .hyperbolicProduct p v w := by
  have hv := logPointDeriv_mobiusLogMap hg t p v
  have hw := logPointDeriv_mobiusLogMap hg t p w
  set A : ℂ := (g.det.val : ℂ) / denom g (logPoint p) ^ 2 with hAdef
  rw [logPointDeriv_apply, logPointDeriv_apply] at hv hw
  have hv0 := congrArg Complex.re hv
  have hv1 := congrArg Complex.im hv
  have hw0 := congrArg Complex.re hw
  have hw1 := congrArg Complex.im hw
  simp only [Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im, Complex.ofReal_re,
    Complex.ofReal_im, Complex.I_re, Complex.I_im] at hv0 hv1 hw0 hw1
  have hN : 0 < Complex.normSq (denom g (logPoint p)) :=
    normSq_denom_pos g (by simp [(Real.exp_pos (p 1)).ne'])
  have hE : Real.exp (mobiusLogMap g t p 1) =
      g.det.val * Real.exp (p 1) / Complex.normSq (denom g (logPoint p)) := by
    rw [show mobiusLogMap g t p 1 = Real.log (g • logPoint p).im by simp [mobiusLogMap],
      Real.exp_log (g • logPoint p).im_pos, im_smul_eq_div_normSq, abs_of_pos hg, logPoint_im]
  have hA : A.re ^ 2 + A.im ^ 2 = g.det.val ^ 2 / Complex.normSq (denom g (logPoint p)) ^ 2 := by
    calc A.re ^ 2 + A.im ^ 2 = Complex.normSq A := by rw [Complex.normSq_apply]; ring
      _ = _ := by rw [hAdef, map_div₀, map_pow, Complex.normSq_ofReal]; ring
  have hv2 := fderiv_mobiusLogMap_two hg t p v
  have hw2 := fderiv_mobiusLogMap_two hg t p w
  have key := inner_algebra (Real.exp_pos (p 1)) hg hN hE hA
    (a0 := fderiv ℝ (mobiusLogMap g t) p v 0)
    (a1 := fderiv ℝ (mobiusLogMap g t) p v 1) (b0 := fderiv ℝ (mobiusLogMap g t) p w 0)
    (b1 := fderiv ℝ (mobiusLogMap g t) p w 1) (v0 := v 0) (v1 := v 1) (w0 := w 0) (w1 := w 1)
    (by linear_combination hv0) (by linear_combination hv1) (by linear_combination hw0)
    (by linear_combination hw1)
  simp only [coordinateInner, coordinateCoframe, Fin.sum_univ_three, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, Real.exp_neg]
  rw [hv2, hw2]
  linear_combination key

def mobiusLog (g : GL (Fin 2) ℝ) (hg : 0 < g.det.val) :
    ModelCoordinates ≃ₘ⟮𝓡 3, 𝓡 3⟯ ModelCoordinates where
  toFun := mobiusLogMap g 0
  invFun := mobiusLogMap g⁻¹ 0
  left_inv p := by rw [mobiusLogMap_mobiusLogMap, inv_mul_cancel, add_zero, mobiusLogMap_one]
  right_inv p := by rw [mobiusLogMap_mobiusLogMap, mul_inv_cancel, add_zero, mobiusLogMap_one]
  contMDiff_toFun := (contDiff_mobiusLogMap hg 0).contMDiff
  contMDiff_invFun := (contDiff_mobiusLogMap (by simpa using hg) 0).contMDiff

theorem mobiusLog_inner (g : GL (Fin 2) ℝ) (hg : 0 < g.det.val) (p : ModelCoordinates)
    (v w : TangentSpace (𝓡 3) p) :
    coordinateInner .hyperbolicProduct (mobiusLog g hg p)
      (mfderiv (𝓡 3) (𝓡 3) (mobiusLog g hg) p v) (mfderiv (𝓡 3) (𝓡 3) (mobiusLog g hg) p w) =
      coordinateInner .hyperbolicProduct p v w := by
  have h : (mobiusLog g hg : ModelCoordinates → ModelCoordinates) = mobiusLogMap g 0 := rfl
  rw [h, mfderiv_eq_fderiv]
  exact mobiusLogMap_coordinateInner hg 0 p v w

def pantsU₄ : SL(2, ℤ) :=
  ⟨!![1, 0; 4, 1], by simp [Matrix.det_fin_two_of]⟩

def pantsGroup : Subgroup SL(2, ℤ) :=
  Subgroup.closure {ModularGroup.T, pantsU₄}

theorem pantsGroup_le_gamma1 : pantsGroup ≤ Gamma1 4 := by
  rw [pantsGroup, Subgroup.closure_le]
  rintro γ (rfl | rfl)
  · refine (Gamma1_mem 4 _).2 ⟨?_, ?_, ?_⟩ <;> simp [ModularGroup.coe_T]
  · refine (Gamma1_mem 4 _).2 ⟨by simp [pantsU₄], by simp [pantsU₄], ?_⟩
    have h : (pantsU₄ 1 0 : ℤ) = 4 := rfl
    rw [h]
    decide

theorem coe_sl_apply (γ : SL(2, ℤ)) (i j : Fin 2) :
    ((γ : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) i j = ((γ i j : ℤ) : ℝ) := by
  simp

theorem det_coe_sl_pos (γ : SL(2, ℤ)) : 0 < (γ : GL (Fin 2) ℝ).det.val := by
  simp

private theorem dvd_of_zmod_eq {a : ℤ} {r : ℤ} (h : ((a : ℤ) : ZMod 4) = (r : ZMod 4)) :
    (4 : ℤ) ∣ a - r := by
  have h' : ((a - r : ℤ) : ZMod 4) = 0 := by push_cast; rw [h, sub_self]
  exact_mod_cast (ZMod.intCast_zmod_eq_zero_iff_dvd (a - r) 4).1 h'

theorem gamma1_four_free {γ : SL(2, ℤ)} (hγ : γ ∈ Gamma1 4) {z : ℍ} (h : γ • z = z) :
    γ = 1 := by
  obtain ⟨ha, hd, hc⟩ := (Gamma1_mem 4 γ).1 hγ
  have ha' : (4 : ℤ) ∣ γ 0 0 - 1 := dvd_of_zmod_eq (r := 1) (by simpa using ha)
  have hd' : (4 : ℤ) ∣ γ 1 1 - 1 := dvd_of_zmod_eq (r := 1) (by simpa using hd)
  have hdet : γ 0 0 * γ 1 1 - γ 0 1 * γ 1 0 = 1 := by
    have := γ.det_coe
    rwa [Matrix.det_fin_two] at this
  have hg : 0 < ((γ : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ).det := by
    rw [← Matrix.GeneralLinearGroup.val_det_apply]
    exact det_coe_sl_pos γ
  by_cases hcen : (γ : GL (Fin 2) ℝ) ∈ Subgroup.center (GL (Fin 2) ℝ)
  · obtain ⟨r, hr⟩ := GeneralLinearGroup.mem_center_iff_val_mem_range_scalar.1 hcen
    have e (i j : Fin 2) : Matrix.scalar (Fin 2) r i j = ((γ i j : ℤ) : ℝ) := by
      rw [hr, coe_sl_apply]
    have e01 := e 0 1
    have e10 := e 1 0
    have e00 := e 0 0
    have e11 := e 1 1
    simp only [Matrix.scalar_apply, Matrix.diagonal_apply_ne _ (by decide : (0 : Fin 2) ≠ 1),
      Matrix.diagonal_apply_ne _ (by decide : (1 : Fin 2) ≠ 0), Matrix.diagonal_apply_eq]
      at e01 e10 e00 e11
    have h01 : γ 0 1 = 0 := by exact_mod_cast e01.symm
    have h10 : γ 1 0 = 0 := by exact_mod_cast e10.symm
    have h0011 : γ 0 0 = γ 1 1 := by exact_mod_cast e00.symm.trans e11
    rw [h01, h0011, zero_mul, sub_zero] at hdet
    have h11 : γ 1 1 = 1 := by
      rcases Int.mul_eq_one_iff_eq_one_or_neg_one.1 hdet with h1 | h1 <;> omega
    ext i j
    fin_cases i <;> fin_cases j <;> simp [h01, h10, h0011, h11]
  · have hell := isElliptic_of_exists_smul_eq_self hg hcen ⟨z, h⟩
    have hell' : ((γ : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ).discr < 0 := hell
    rw [Matrix.discr_fin_two, Matrix.trace_fin_two, Matrix.det_fin_two] at hell'
    simp only [coe_sl_apply] at hell'
    have hint : (γ 0 0 + γ 1 1) ^ 2 - 4 * (γ 0 0 * γ 1 1 - γ 0 1 * γ 1 0) < 0 := by
      exact_mod_cast hell'
    rw [hdet] at hint
    have hlo : -2 < γ 0 0 + γ 1 1 := by nlinarith
    have hhi : γ 0 0 + γ 1 1 < 2 := by nlinarith
    omega

instance properlyDiscontinuousSMul_SL2Z : ProperlyDiscontinuousSMul SL(2, ℤ) ℍ := by
  refine ⟨fun {K L} hK hL => ?_⟩
  have h := ProperlyDiscontinuousSMul.finite_disjoint_inter_image (Γ := 𝒮ℒ) hK hL
  let f : SL(2, ℤ) → 𝒮ℒ := fun γ => ⟨Matrix.SpecialLinearGroup.mapGL ℝ γ, γ, rfl⟩
  have hf : Function.Injective f := fun a b hab =>
    Matrix.SpecialLinearGroup.mapGL_injective (congrArg Subtype.val hab)
  exact (h.preimage hf.injOn).subset fun γ hγ => hγ

def pantsSMul (γ : pantsGroup × Multiplicative ℤ) (p : ModelCoordinates) : ModelCoordinates :=
  logCoords ((γ.1 : SL(2, ℤ)) • logPoint p) (p 2 + (Multiplicative.toAdd γ.2 : ℤ))

instance pantsAction : MulAction (pantsGroup × Multiplicative ℤ) ModelCoordinates where
  smul := pantsSMul
  one_smul p := by
    change pantsSMul 1 p = p
    simp [pantsSMul]
  mul_smul a b p := by
    change pantsSMul (a * b) p = pantsSMul a (pantsSMul b p)
    simp only [pantsSMul, logPoint_logCoords, logCoords_two, Prod.fst_mul, Prod.snd_mul,
      Subgroup.coe_mul, mul_smul, toAdd_mul, Int.cast_add]
    congr 1
    ring

theorem pants_smul_def (γ : pantsGroup × Multiplicative ℤ) (p : ModelCoordinates) :
    γ • p = pantsSMul γ p :=
  rfl

theorem pants_smul_eq_mobiusLogMap (γ : pantsGroup × Multiplicative ℤ) (p : ModelCoordinates) :
    γ • p = mobiusLogMap ((γ.1 : SL(2, ℤ)) : GL (Fin 2) ℝ) (Multiplicative.toAdd γ.2 : ℤ) p :=
  rfl

theorem logPoint_pants_smul (γ : pantsGroup × Multiplicative ℤ) (p : ModelCoordinates) :
    logPoint (γ • p) = (γ.1 : SL(2, ℤ)) • logPoint p :=
  logPoint_logCoords _ _

theorem pants_smul_two (γ : pantsGroup × Multiplicative ℤ) (p : ModelCoordinates) :
    (γ • p) 2 = p 2 + (Multiplicative.toAdd γ.2 : ℤ) :=
  logCoords_two _ _

theorem eq_one_of_pants_smul_eq (γ : pantsGroup × Multiplicative ℤ) (p : ModelCoordinates)
    (h : γ • p = p) : γ = 1 := by
  have h1 : (γ.1 : SL(2, ℤ)) • logPoint p = logPoint p := by
    rw [← logPoint_pants_smul, h]
  have h2 : ((Multiplicative.toAdd γ.2 : ℤ) : ℝ) = 0 := by
    have := congrArg (fun q : ModelCoordinates => q 2) h
    simp only [pants_smul_two] at this
    linarith
  have hγ1 : (γ.1 : SL(2, ℤ)) = 1 := gamma1_four_free (pantsGroup_le_gamma1 γ.1.2) h1
  have hγ2 : Multiplicative.toAdd γ.2 = 0 := by exact_mod_cast h2
  exact Prod.ext (Subtype.ext hγ1) (Multiplicative.toAdd.injective (hγ2.trans toAdd_one.symm))

instance : ContinuousConstSMul (pantsGroup × Multiplicative ℤ) ModelCoordinates :=
  ⟨fun γ => (contDiff_mobiusLogMap (det_coe_sl_pos γ.1) _).continuous⟩

instance : ContMDiffConstSMul (𝓡 3) ∞ (pantsGroup × Multiplicative ℤ) ModelCoordinates :=
  ⟨fun γ => (contDiff_mobiusLogMap (det_coe_sl_pos γ.1) _).contMDiff⟩

instance : IsCancelSMul (pantsGroup × Multiplicative ℤ) ModelCoordinates :=
  isCancelSMul_of_free eq_one_of_pants_smul_eq

instance : ProperlyDiscontinuousSMul (pantsGroup × Multiplicative ℤ) ModelCoordinates := by
  refine ⟨fun {K L} hK hL => ?_⟩
  have h1 := ProperlyDiscontinuousSMul.finite_disjoint_inter_image (Γ := pantsGroup)
    (hK.image continuous_logPoint) (hL.image continuous_logPoint)
  obtain ⟨R, hR⟩ := (hK.union hL).exists_bound_of_continuousOn (coord 2).continuous.continuousOn
  let B : ℤ := ⌈2 * R⌉
  have h2 : (Multiplicative.toAdd ⁻¹' Set.Icc (-B) B).Finite :=
    (Set.finite_Icc (-B) B).preimage Multiplicative.toAdd.injective.injOn
  refine (h1.prod h2).subset ?_
  rintro ⟨γ, n⟩ ⟨_, ⟨k, hk, rfl⟩, hl⟩
  dsimp only at hl
  refine ⟨⟨logPoint ((γ, n) • k), ⟨logPoint k, ⟨k, hk, rfl⟩, (logPoint_pants_smul _ _).symm⟩,
    ⟨_, hl, rfl⟩⟩, ?_⟩
  have hk' := hR k (Or.inl hk)
  have hl' := hR _ (Or.inr hl)
  simp only [PiLp.proj_apply, Real.norm_eq_abs, pants_smul_two] at hk' hl'
  have hB : 2 * R ≤ (B : ℝ) := Int.le_ceil _
  obtain ⟨a1, a2⟩ := abs_le.mp hk'
  obtain ⟨b1, b2⟩ := abs_le.mp hl'
  constructor
  · have : ((-B : ℤ) : ℝ) ≤ (Multiplicative.toAdd n : ℤ) := by push_cast; linarith
    exact_mod_cast this
  · have : ((Multiplicative.toAdd n : ℤ) : ℝ) ≤ (B : ℝ) := by linarith
    exact_mod_cast this

theorem pullbackMetric_pants_smul (γ : pantsGroup × Multiplicative ℤ) :
    Diffeomorph.pullbackMetric (coordinateModelMetric .hyperbolicProduct)
      (MulAction.smulDiffeomorph (n := ∞) (𝓡 3) γ) = coordinateModelMetric .hyperbolicProduct := by
  apply SmoothRiemannianMetric.ext_inner
  intro x v w
  have hfun : ((MulAction.smulDiffeomorph (n := ∞) (𝓡 3) γ :
      ModelCoordinates ≃ₘ⟮𝓡 3, 𝓡 3⟯ ModelCoordinates) : ModelCoordinates → ModelCoordinates) =
      mobiusLogMap ((γ.1 : SL(2, ℤ)) : GL (Fin 2) ℝ) (Multiplicative.toAdd γ.2 : ℤ) :=
    rfl
  rw [Diffeomorph.pullbackMetric_inner, hfun, mfderiv_eq_fderiv]
  exact (coordinateModelMetric_inner _ _ _ _).trans
    ((mobiusLogMap_coordinateInner (det_coe_sl_pos γ.1) _ x v w).trans
      (coordinateModelMetric_inner _ _ _ _).symm)

abbrev PantsQuotient := orbitRel.Quotient (pantsGroup × Multiplicative ℤ) ModelCoordinates

def pantsQuotientGeometry : GeometricStructure (𝓡 3) PantsQuotient :=
  (coordinateGeometricStructure .hyperbolicProduct (by decide)).quotient
    (pantsGroup × Multiplicative ℤ) pullbackMetric_pants_smul (fun h => by cases h)

theorem pantsQuotientGeometry_model : pantsQuotientGeometry.model = .hyperbolicProduct :=
  rfl

end GC.Seifert
