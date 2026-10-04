import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Seifert.ConeFoldApex
import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Seifert.FilledCarrier
import DifferentialGeometry.Geometry.Thurston.ScrewLift
import DifferentialGeometry.Topology.Manifold.InverseFunction

/-!
# The tube map at a cone vertex

Lane A4, tier 4 (design `docs/geometrization/handoffs/20261004-design-a4-cone-fold.md`, §9 and
erratum 9). For a `ConeFilling c` (`p b - a q = 1`) and the disc coordinate `w` at a cone vertex,
the tube map is `tubeOf w s = (3 w e(a s), e(p s))` with `e(t) = Circle.exp (2π t)`, in the
`(z, w)` coordinates of `filledSet`; `coneTube v z s = tubeOf (coneDisc v z) s`. The phases
cancel in `conePoint`, so `conePoint (tubeOf w s) = 3/2 + w^p/2` exactly (`conePoint_tubeOf`),
which is `coneApexOne` at `v = σ.vertexOne` (`conePoint_coneTube_vertexOne`). The map is
`tubeLift ∘ untwist ∘ ofPlane` for X14's untwist map of the screw group with `θ = 2π(-a)/p`,
`ℓ = 1/p`, hence a local diffeomorphism everywhere (`isLocalDiffeomorph_tubeOf`); composed with
`(z, s) ↦ (coneDisc v z, s)`, which is a local diffeomorphism on `{Im z > 0} × ℝ` by the
nonvanishing derivative of `coneDisc`, the tube map `(z, s) ↦ coneTube v z s` is a local
diffeomorphism there (`isLocalDiffeomorphAt_coneTube`, `isLocalDiffeomorphOn_coneTube`). The
deck transformations `(w, s) ↦ (e(k/p) w, s + (k q + n p)/p)` leave it invariant
(`tubeOf_rotate`), and two points have the same image exactly when they differ by one
(`tubeOf_eq_tubeOf_iff`, with witnesses `k = a m`, `n = -b m` from `e(p s) = e(p s')`); on the
central fibre this is `s' - s ∈ (1/p) ℤ` (`tubeOf_zero_eq_iff`). In `ModelCoordinates` the deck
transformations are X14's screws (`tubeModel_screwGenerator`, `tubeModel_fibreTranslation`,
`tubeModel_screwBase`, the last being the inner factor of `screwAt`), and after the radial
adaptation `discMap` the tube map is `(3·, id) ∘ scaledScrewTubeDiffeomorph p a 1` on the screw
quotient (`tubeOf_discMap_eq`). Off the central fibre, `coneChart (tubeOf w s) =
(3/2 + w^p/2, e(s) (unitOf w)^(-q))`, so `coneLift` of that point is `tubeOf w s`
(`coneChart_tubeOf`, `coneLift_tubeOf`); the phase unit `Ψ = unitOf w ^ q` of the design is
`tubePhase`.
-/

set_option autoImplicit false

noncomputable section

open Complex GC.Geometry GC.GraphManifold
open scoped ComplexConjugate ContDiff Manifold

universe u

namespace GC.Seifert

private theorem unitOf_mul' {x y : ℂ} (hx : x ≠ 0) (hy : y ≠ 0) :
    unitOf (x * y) = unitOf x * unitOf y := by
  have h : x * y = (‖x‖ * ‖y‖) • ((unitOf x * unitOf y : Circle) : ℂ) := by
    rw [Circle.coe_mul, ← smul_mul_smul_comm, norm_smul_unitOf, norm_smul_unitOf]
  rw [h, unitOf_smul (mul_pos (norm_pos_iff.mpr hx) (norm_pos_iff.mpr hy))]

private theorem unitOf_circle' (μ : Circle) : unitOf (μ : ℂ) = μ := by
  simpa using unitOf_smul one_pos μ

private theorem unitOf_three : unitOf (3 : ℂ) = 1 := by
  have h := unitOf_smul (by norm_num : (0 : ℝ) < 3) (1 : Circle)
  rwa [Circle.coe_one, Complex.real_smul, mul_one, Complex.ofReal_ofNat] at h

def threeDiffeo : ℂ ≃ₘ⟮𝓘(ℝ, ℂ), 𝓘(ℝ, ℂ)⟯ ℂ where
  toFun w := 3 * w
  invFun w := w / 3
  left_inv w := by ring
  right_inv w := by ring
  contMDiff_toFun := (contDiff_const.mul contDiff_id : ContDiff ℝ ∞ fun w : ℂ => 3 * w).contMDiff
  contMDiff_invFun := (contDiff_id.div_const 3 : ContDiff ℝ ∞ fun w : ℂ => w / 3).contMDiff

def tubeLift : (ℂ × Circle) ≃ₘ⟮𝓘(ℝ, ℂ).prod (𝓡 1), PlaneCircleModel⟯ (PlaneLift.{u} × Circle) :=
  (threeDiffeo.trans (DifferentialGeometry.Topology.uliftDiffeomorph 𝓘(ℝ, ℂ) ℂ)).prodCongr
    (Diffeomorph.refl (𝓡 1) Circle ∞)

theorem tubeLift_apply (y : ℂ × Circle) : tubeLift.{u} y = (ULift.up (3 * y.1), y.2) := rfl

def ofPlaneLinear : (ℂ × ℝ) ≃ₗ[ℝ] ModelCoordinates where
  toFun y := ofPlane y.1 y.2
  invFun x := (planeOf x, x 2)
  map_add' y y' := by
    ext i
    fin_cases i <;> simp [ofPlane]
  map_smul' r y := by
    ext i
    fin_cases i <;> simp [ofPlane]
  left_inv y := by simp
  right_inv x := modelCoordinates_ext (by simp) (by simp)

def ofPlaneDiffeo : (ℂ × ℝ) ≃ₘ⟮𝓘(ℝ, ℂ × ℝ), 𝓡 3⟯ ModelCoordinates :=
  ofPlaneLinear.toContinuousLinearEquiv.toDiffeomorph

theorem ofPlaneDiffeo_apply (y : ℂ × ℝ) : ofPlaneDiffeo y = ofPlane y.1 y.2 := rfl

theorem ofPlaneDiffeo_symm_apply (x : ModelCoordinates) :
    ofPlaneDiffeo.symm x = (planeOf x, x 2) := rfl

theorem isLocalDiffeomorph_untwist (θ ℓ : ℝ) [Fact (ℓ ≠ 0)] :
    IsLocalDiffeomorph (𝓡 3) (𝓘(ℝ, ℂ).prod (𝓡 1)) ∞ (ScrewGroup.untwist θ ℓ) := fun x =>
  (isLocalDiffeomorph_orbitMk (𝓡 3) (ScrewGroup θ ℓ) ModelCoordinates x).comp
    (𝓘(ℝ, ℂ).prod (𝓡 1)) (ℂ × Circle)
    (ScrewGroup.isLocalDiffeomorph_untwistQuotient (Quotient.mk'' x))

def mulLeftEquiv (d : ℂ) (hd : d ≠ 0) : ℂ ≃L[ℝ] ℂ :=
  (ContinuousLinearEquiv.unitsEquivAut ℂ (Units.mk0 d hd)).restrictScalars ℝ

theorem mulLeftEquiv_apply (d : ℂ) (hd : d ≠ 0) (w : ℂ) : mulLeftEquiv d hd w = w * d := rfl

theorem isLocalDiffeomorphAt_coneDisc_prod {v z : ℂ} (hv : 0 < v.im) (hz : 0 < z.im) (s : ℝ) :
    IsLocalDiffeomorphAt 𝓘(ℝ, ℂ × ℝ) 𝓘(ℝ, ℂ × ℝ) ∞
      (fun y : ℂ × ℝ => (coneDisc v y.1, y.2)) (z, s) := by
  set d := (v - conj v) / (z - conj v) ^ 2 with hd
  have hd0 : d ≠ 0 := by
    have h2 : v - conj v ≠ 0 := by
      intro h
      have := congrArg Complex.im h
      simp at this
      linarith
    exact div_ne_zero h2 (pow_ne_zero _ (sub_conj_ne_zero hv hz))
  refine
    DifferentialGeometry.Topology.Manifold.isLocalDiffeomorphAt_of_contMDiffOn_of_hasMFDerivAt_equiv
    _ (U := {y : ℂ × ℝ | 0 < y.1.im}) ?_ ?_ (z, s) hz
    ((mulLeftEquiv d hd0).prodCongr (ContinuousLinearEquiv.refl ℝ ℝ)) ?_
  · rw [contMDiffOn_iff_contDiffOn]
    intro y hy
    exact ((((contDiffAt_coneDisc hv hy).restrict_scalars ℝ).comp y contDiffAt_fst).prodMk
      contDiffAt_snd).contDiffWithinAt
  · exact isOpen_lt continuous_const (Complex.continuous_im.comp continuous_fst)
  · refine HasFDerivAt.hasMFDerivAt ?_
    have hfst : HasFDerivAt (Prod.fst : ℂ × ℝ → ℂ) (ContinuousLinearMap.fst ℝ ℂ ℝ) (z, s) :=
      hasFDerivAt_fst
    have h1 : HasFDerivAt (coneDisc v ∘ Prod.fst)
        (((ContinuousLinearMap.smulRight (1 : ℂ →L[ℂ] ℂ) d).restrictScalars ℝ).comp
          (ContinuousLinearMap.fst ℝ ℂ ℝ)) (z, s) :=
      ((hasDerivAt_coneDisc hv hz).hasFDerivAt.restrictScalars ℝ).comp (z, s) hfst
    have h2 : HasFDerivAt (fun y : ℂ × ℝ => y.2) (ContinuousLinearMap.snd ℝ ℂ ℝ) (z, s) :=
      hasFDerivAt_snd
    have hA : ((mulLeftEquiv d hd0).prodCongr (ContinuousLinearEquiv.refl ℝ ℝ) :
        ℂ × ℝ →L[ℝ] ℂ × ℝ) =
        (((ContinuousLinearMap.smulRight (1 : ℂ →L[ℂ] ℂ) d).restrictScalars ℝ).comp
          (ContinuousLinearMap.fst ℝ ℂ ℝ)).prod (ContinuousLinearMap.snd ℝ ℂ ℝ) := by
      refine ContinuousLinearMap.ext fun y => Prod.ext ?_ ?_
      · simp [mulLeftEquiv_apply]
      · simp
    exact (h1.prodMk h2).congr_fderiv hA.symm

namespace ConeFilling

variable (c : ConeFilling)

def tubePhase (w : ℂ) : Circle := unitOf w ^ c.q

def tubeOf (w : ℂ) (s : ℝ) : PlaneLift.{u} × Circle :=
  (ULift.up (3 * w * (Circle.exp (2 * Real.pi * c.a * s) : ℂ)),
    Circle.exp (2 * Real.pi * c.p * s))

def coneTube (v z : ℂ) (s : ℝ) : PlaneLift.{u} × Circle := c.tubeOf (coneDisc v z) s

def tubeModel (x : ModelCoordinates) : PlaneLift.{u} × Circle := c.tubeOf (planeOf x) (x 2)

def pnat : ℕ+ := ⟨c.p, c.one_le⟩

theorem tubeOf_fst_down (w : ℂ) (s : ℝ) :
    (c.tubeOf.{u} w s).1.down = 3 * w * (Circle.exp (2 * Real.pi * c.a * s) : ℂ) := rfl

theorem tubeOf_snd (w : ℂ) (s : ℝ) :
    (c.tubeOf.{u} w s).2 = Circle.exp (2 * Real.pi * c.p * s) := rfl

theorem coneTube_eq (v z : ℂ) (s : ℝ) : c.coneTube.{u} v z s = c.tubeOf (coneDisc v z) s := rfl

theorem p_ne_zero : (c.p : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne c.p)

theorem det_eq_real : (c.p : ℝ) * c.b - c.a * c.q = 1 := by exact_mod_cast c.det_eq

theorem coe_pnat : ((c.pnat : ℕ) : ℝ) = c.p := rfl

theorem phase_pow_mul_zpow (s : ℝ) :
    Circle.exp (2 * Real.pi * c.a * s) ^ c.p *
      Circle.exp (2 * Real.pi * c.p * s) ^ (-c.a) = 1 := by
  rw [← Circle.exp_natCast_mul, ← Circle.exp_intCast_mul, ← Circle.exp_add, ← Circle.exp_zero]
  congr 1
  push_cast
  ring

theorem conePoint_tubeOf (w : ℂ) (s : ℝ) :
    c.conePoint (c.tubeOf.{u} w s) = 3 / 2 + w ^ c.p / 2 := by
  have h := congrArg (fun u : Circle => (u : ℂ)) (c.phase_pow_mul_zpow s)
  simp only [Circle.coe_mul, Circle.coe_pow, Circle.coe_zpow, Circle.coe_one] at h
  simp only [conePoint, tubeOf, Circle.coe_zpow]
  have e1 : 3 * w * (Circle.exp (2 * Real.pi * c.a * s) : ℂ) / 3 =
      w * (Circle.exp (2 * Real.pi * c.a * s) : ℂ) := by ring
  rw [e1, mul_pow, mul_assoc, h, mul_one]
  push_cast
  ring

theorem conePoint_coneTube (v z : ℂ) (s : ℝ) :
    c.conePoint (c.coneTube.{u} v z s) = 3 / 2 + coneDisc v z ^ c.p / 2 :=
  c.conePoint_tubeOf _ s

theorem conePoint_coneTube_vertexOne (σ : ConeShape) (z : ℂ) (s : ℝ) :
    c.conePoint (c.coneTube.{u} σ.vertexOne z s) = σ.coneApexOne c.p z :=
  c.conePoint_tubeOf _ s

theorem tubeOf_rotate (w : ℂ) (s : ℝ) (k n : ℤ) :
    c.tubeOf.{u} ((Circle.exp (2 * Real.pi * k / c.p) : ℂ) * w)
      (s + (k * c.q + n * c.p) / c.p) = c.tubeOf w s := by
  have hp := c.p_ne_zero
  have hd := c.det_eq_real
  refine Prod.ext (ULift.ext ?_) ?_
  · change 3 * ((Circle.exp (2 * Real.pi * k / c.p) : ℂ) * w) *
      (Circle.exp (2 * Real.pi * c.a * (s + (k * c.q + n * c.p) / c.p)) : ℂ) =
      3 * w * (Circle.exp (2 * Real.pi * c.a * s) : ℂ)
    have h : Circle.exp (2 * Real.pi * k / c.p) *
        Circle.exp (2 * Real.pi * c.a * (s + (k * c.q + n * c.p) / c.p)) =
        Circle.exp (2 * Real.pi * c.a * s) := by
      rw [← Circle.exp_add]
      have e : 2 * Real.pi * k / c.p + 2 * Real.pi * c.a * (s + (k * c.q + n * c.p) / c.p) =
          2 * Real.pi * c.a * s + ((k * c.b + c.a * n : ℤ) : ℝ) * (2 * Real.pi) := by
        push_cast
        field_simp
        linear_combination (-k) * hd
      rw [e, Circle.exp_add, Circle.exp_int_mul_two_pi, mul_one]
    have h' := congrArg (fun u : Circle => (u : ℂ)) h
    simp only [Circle.coe_mul] at h'
    calc 3 * ((Circle.exp (2 * Real.pi * k / c.p) : ℂ) * w) *
          (Circle.exp (2 * Real.pi * c.a * (s + (k * c.q + n * c.p) / c.p)) : ℂ) =
        3 * w * ((Circle.exp (2 * Real.pi * k / c.p) : ℂ) *
          (Circle.exp (2 * Real.pi * c.a * (s + (k * c.q + n * c.p) / c.p)) : ℂ)) := by ring
      _ = 3 * w * (Circle.exp (2 * Real.pi * c.a * s) : ℂ) := by rw [h']
  · change Circle.exp (2 * Real.pi * c.p * (s + (k * c.q + n * c.p) / c.p)) =
      Circle.exp (2 * Real.pi * c.p * s)
    have hX : (c.p : ℝ) * ((k * c.q + n * c.p) / c.p) = k * c.q + n * c.p :=
      mul_div_cancel₀ _ hp
    have e : 2 * Real.pi * c.p * (s + (k * c.q + n * c.p) / c.p) =
        2 * Real.pi * c.p * s + ((k * c.q + n * c.p : ℤ) : ℝ) * (2 * Real.pi) := by
      push_cast
      linear_combination (2 * Real.pi) * hX
    rw [e, Circle.exp_add, Circle.exp_int_mul_two_pi, mul_one]

theorem tubeOf_add_int (w : ℂ) (s : ℝ) (n : ℤ) : c.tubeOf.{u} w (s + n) = c.tubeOf w s := by
  have h := c.tubeOf_rotate.{u} w s 0 n
  have hp := c.p_ne_zero
  simp only [Int.cast_zero, mul_zero, zero_div, Circle.exp_zero, Circle.coe_one, one_mul,
    zero_mul, zero_add] at h
  rwa [mul_div_assoc, div_self hp, mul_one] at h

theorem tubeOf_eq_tubeOf_iff (w w' : ℂ) (s s' : ℝ) :
    c.tubeOf.{u} w s = c.tubeOf w' s' ↔
      ∃ k n : ℤ, w' = (Circle.exp (2 * Real.pi * k / c.p) : ℂ) * w ∧
        s' = s + k * c.q / c.p + n := by
  have hp := c.p_ne_zero
  have hd := c.det_eq_real
  constructor
  · intro h
    have h1 := congrArg (fun x : PlaneLift.{u} × Circle => x.1.down) h
    have h2 := congrArg Prod.snd h
    simp only [tubeOf] at h1 h2
    obtain ⟨m, hm⟩ := Circle.exp_eq_exp.1 h2
    have hm' : (c.p : ℝ) * s = c.p * s' + m := by
      have h2π : (2 * Real.pi : ℝ) ≠ 0 := by positivity
      apply mul_left_cancel₀ h2π
      linear_combination hm
    have hs : s = s' + m / c.p := by
      field_simp
      linear_combination hm'
    refine ⟨c.a * m, -(c.b * m), ?_, ?_⟩
    · have hE : (Circle.exp (2 * Real.pi * ((c.a * m : ℤ) : ℝ) / c.p) : ℂ) *
          Circle.exp (2 * Real.pi * c.a * s') = Circle.exp (2 * Real.pi * c.a * s) := by
        rw [← Circle.coe_mul, ← Circle.exp_add, hs]
        congr 2
        push_cast
        field_simp
        ring
      have hne : (Circle.exp (2 * Real.pi * c.a * s') : ℂ) ≠ 0 := Circle.coe_ne_zero _
      have h3 : 3 * w' * (Circle.exp (2 * Real.pi * c.a * s') : ℂ) =
          3 * ((Circle.exp (2 * Real.pi * ((c.a * m : ℤ) : ℝ) / c.p) : ℂ) * w) *
            (Circle.exp (2 * Real.pi * c.a * s') : ℂ) := by
        calc 3 * w' * (Circle.exp (2 * Real.pi * c.a * s') : ℂ)
            = 3 * w * (Circle.exp (2 * Real.pi * c.a * s) : ℂ) := h1.symm
          _ = 3 * w * ((Circle.exp (2 * Real.pi * ((c.a * m : ℤ) : ℝ) / c.p) : ℂ) *
                Circle.exp (2 * Real.pi * c.a * s')) := by rw [hE]
          _ = _ := by ring
      exact mul_left_cancel₀ three_ne_zero (mul_right_cancel₀ hne h3)
    · rw [hs]
      push_cast
      field_simp
      linear_combination m * hd
  · rintro ⟨k, n, hw, hs⟩
    rw [hw, hs, show s + k * c.q / c.p + n = s + (k * c.q + n * c.p) / c.p by
      field_simp; ring, c.tubeOf_rotate]

theorem coneTube_eq_coneTube_iff (v z z' : ℂ) (s s' : ℝ) :
    c.coneTube.{u} v z s = c.coneTube v z' s' ↔
      ∃ k n : ℤ, coneDisc v z' = (Circle.exp (2 * Real.pi * k / c.p) : ℂ) * coneDisc v z ∧
        s' = s + k * c.q / c.p + n :=
  c.tubeOf_eq_tubeOf_iff _ _ s s'

theorem tubeOf_zero_eq_iff (s s' : ℝ) :
    c.tubeOf.{u} 0 s = c.tubeOf 0 s' ↔ ∃ m : ℤ, s' = s + m / c.p := by
  have hp := c.p_ne_zero
  have hd := c.det_eq_real
  rw [c.tubeOf_eq_tubeOf_iff]
  constructor
  · rintro ⟨k, n, -, hs⟩
    refine ⟨k * c.q + n * c.p, ?_⟩
    rw [hs]
    push_cast
    field_simp
    ring
  · rintro ⟨m, hm⟩
    refine ⟨-(c.a * m), c.b * m, by simp, ?_⟩
    rw [hm]
    push_cast
    field_simp
    linear_combination (-m) * hd

theorem coneTube_refl (σ : ConeShape) (hθ : σ.θ₁ * c.p = Real.pi) {z : ℂ} (hz : 0 < z.im)
    (s : ℝ) :
    c.coneTube.{u} σ.vertexOne (σ.refl 2 (σ.refl 1 z)) (s + c.q / c.p) =
      c.coneTube σ.vertexOne z s := by
  have hp := c.p_ne_zero
  have hc : σ.refl 1 z ≠ σ.centre := by
    intro h
    have := congrArg Complex.im h
    rw [σ.refl_one_eq] at this
    simp at this
    linarith
  have hθ' : 2 * σ.θ₁ = 2 * Real.pi * 1 / c.p := by
    rw [mul_one, eq_div_iff hp, mul_assoc, hθ]
  have h := c.tubeOf_rotate.{u} (coneDisc σ.vertexOne z) s 1 0
  rw [Int.cast_zero, zero_mul, add_zero, Int.cast_one, one_mul] at h
  rw [coneTube_eq, coneTube_eq, σ.coneDisc_vertexOne_refl_two hc, σ.coneDisc_vertexOne_refl_one,
    Complex.conj_conj, ← h]
  congr 2
  rw [Circle.coe_exp, show (2 : ℂ) * (σ.θ₁ : ℂ) * I = ((2 * σ.θ₁ : ℝ) : ℂ) * I by push_cast; ring,
    hθ']

theorem tubeOf_fst_ne_zero {w : ℂ} (hw : w ≠ 0) (s : ℝ) : (c.tubeOf.{u} w s).1.down ≠ 0 :=
  mul_ne_zero (mul_ne_zero three_ne_zero hw) (Circle.coe_ne_zero _)

theorem unitOf_tubeOf {w : ℂ} (hw : w ≠ 0) (s : ℝ) :
    unitOf (c.tubeOf.{u} w s).1.down = unitOf w * Circle.exp (2 * Real.pi * c.a * s) := by
  rw [tubeOf_fst_down, unitOf_mul' (mul_ne_zero three_ne_zero hw) (Circle.coe_ne_zero _),
    unitOf_mul' three_ne_zero hw, unitOf_three, one_mul, unitOf_circle']

theorem coneChart_tubeOf {w : ℂ} (hw : w ≠ 0) (s : ℝ) :
    c.coneChart (c.tubeOf.{u} w s) =
      (ULift.up (3 / 2 + w ^ c.p / 2), Circle.exp (2 * Real.pi * s) * (c.tubePhase w)⁻¹) := by
  have hd := c.det_eq_real
  refine Prod.ext (ULift.ext ?_) ?_
  · exact c.conePoint_tubeOf w s
  · change (linearTorusMap c.chartMatrix
      (unitOf (c.tubeOf.{u} w s).1.down, (c.tubeOf.{u} w s).2)).2 = _
    rw [c.unitOf_tubeOf.{u} hw s, c.tubeOf_snd.{u}]
    simp only [linearTorusMap, chartMatrix, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.empty_val', Matrix.cons_val_fin_one, tubePhase, ← zpow_neg]
    rw [mul_zpow, ← Circle.exp_intCast_mul, ← Circle.exp_intCast_mul, mul_assoc,
      ← Circle.exp_add, mul_comm]
    congr 2
    push_cast
    linear_combination (2 * Real.pi * s) * hd

theorem coneLift_tubeOf {w : ℂ} (hw : w ≠ 0) (s : ℝ) :
    c.coneLift (ULift.up (3 / 2 + w ^ c.p / 2), Circle.exp (2 * Real.pi * s) * (c.tubePhase w)⁻¹) =
      c.tubeOf.{u} w s := by
  rw [← c.coneChart_tubeOf hw s]
  exact c.coneLift_coneChart _ (c.tubeOf_fst_ne_zero.{u} hw s)

theorem tubeOf_eq_tubeLift (w : ℂ) (s : ℝ) :
    c.tubeOf.{u} w s =
      tubeLift (ScrewGroup.untwist (2 * Real.pi * (-c.a) / c.p) (1 / c.p) (ofPlane w s)) := by
  have hp := c.p_ne_zero
  simp only [ScrewGroup.untwist, tubeLift_apply, planeOf_ofPlane, ofPlane_apply_two, tubeOf]
  refine Prod.ext (ULift.ext ?_) ?_
  · change 3 * w * (Circle.exp (2 * Real.pi * c.a * s) : ℂ) =
      3 * ((Circle.exp (-(2 * Real.pi * (-c.a) / c.p * s / (1 / c.p))) : ℂ) * w)
    rw [show -(2 * Real.pi * (-c.a) / c.p * s / (1 / c.p)) = 2 * Real.pi * c.a * s by
      field_simp]
    ring
  · change Circle.exp (2 * Real.pi * c.p * s) = Circle.exp (2 * Real.pi * s / (1 / c.p))
    congr 1
    field_simp

theorem tubeOf_comp_eq :
    (fun y : ℂ × ℝ => c.tubeOf.{u} y.1 y.2) =
      tubeLift ∘ ScrewGroup.untwist (2 * Real.pi * (-c.a) / c.p) (1 / c.p) ∘ ofPlaneDiffeo :=
  funext fun y => c.tubeOf_eq_tubeLift y.1 y.2

theorem isLocalDiffeomorph_tubeOf :
    IsLocalDiffeomorph 𝓘(ℝ, ℂ × ℝ) PlaneCircleModel ∞
      (fun y : ℂ × ℝ => c.tubeOf.{u} y.1 y.2) := by
  have : Fact ((1 / (c.p : ℝ)) ≠ 0) := ⟨one_div_ne_zero c.p_ne_zero⟩
  rw [c.tubeOf_comp_eq]
  intro y
  exact (ofPlaneDiffeo.isLocalDiffeomorph y).comp PlaneCircleModel (PlaneLift.{u} × Circle)
    ((isLocalDiffeomorph_untwist _ _ _).comp PlaneCircleModel (PlaneLift.{u} × Circle)
      (tubeLift.isLocalDiffeomorph _))

theorem isLocalDiffeomorphAt_coneTube {v z : ℂ} (hv : 0 < v.im) (hz : 0 < z.im) (s : ℝ) :
    IsLocalDiffeomorphAt 𝓘(ℝ, ℂ × ℝ) PlaneCircleModel ∞
      (fun y : ℂ × ℝ => c.coneTube.{u} v y.1 y.2) (z, s) :=
  (isLocalDiffeomorphAt_coneDisc_prod hv hz s).comp PlaneCircleModel (PlaneLift.{u} × Circle)
    (c.isLocalDiffeomorph_tubeOf _)

theorem isLocalDiffeomorphOn_coneTube {v : ℂ} (hv : 0 < v.im) :
    IsLocalDiffeomorphOn 𝓘(ℝ, ℂ × ℝ) PlaneCircleModel ∞
      (fun y : ℂ × ℝ => c.coneTube.{u} v y.1 y.2) {y | 0 < y.1.im} :=
  fun y => c.isLocalDiffeomorphAt_coneTube hv y.2 y.1.2

theorem tubeModel_eq_comp :
    c.tubeModel.{u} = (fun y : ℂ × ℝ => c.tubeOf y.1 y.2) ∘ ofPlaneDiffeo.symm := rfl

theorem isLocalDiffeomorph_tubeModel :
    IsLocalDiffeomorph (𝓡 3) PlaneCircleModel ∞ c.tubeModel.{u} := by
  rw [tubeModel_eq_comp]
  intro x
  exact (ofPlaneDiffeo.symm.isLocalDiffeomorph x).comp PlaneCircleModel (PlaneLift.{u} × Circle)
    (c.isLocalDiffeomorph_tubeOf _)

theorem tubeModel_screwDiffeomorph (θ t : ℝ) (x : ModelCoordinates) :
    c.tubeModel.{u} (screwDiffeomorph θ t x) =
      c.tubeOf ((Circle.exp θ : ℂ) * planeOf x) (x 2 + t) := by
  change c.tubeOf (planeOf ((⟨1⟩ : ScrewGroup θ t) • x)) (((⟨1⟩ : ScrewGroup θ t) • x) 2) = _
  rw [ScrewGroup.planeOf_smul, ScrewGroup.smul_apply_two]
  simp

theorem tubeModel_screwGenerator (x : ModelCoordinates) :
    c.tubeModel.{u} (screwGenerator c.pnat c.a 1 x) = c.tubeModel x := by
  have hp := c.p_ne_zero
  have hd := c.det_eq_real
  rw [screwGenerator, tubeModel_screwDiffeomorph, tubeModel]
  have h := c.tubeOf_rotate.{u} (planeOf x) (x 2) (-c.a) c.b
  have e1 : 2 * Real.pi * ((-c.a : ℤ) : ℝ) / c.p =
      2 * Real.pi * (-(c.a : ℝ)) / ((c.pnat : ℕ) : ℝ) := by
    simp only [coe_pnat, Int.cast_neg]
  have e2 : (((-c.a : ℤ) : ℝ) * c.q + c.b * c.p) / c.p = 1 / ((c.pnat : ℕ) : ℝ) := by
    rw [coe_pnat, div_eq_div_iff hp hp]
    push_cast
    linear_combination (c.p : ℝ) * hd
  rw [e1, e2] at h
  exact h

theorem tubeModel_fibreTranslation (n : ℤ) (x : ModelCoordinates) :
    c.tubeModel.{u} (fibreTranslation n x) = c.tubeModel x := by
  rw [fibreTranslation, tubeModel_screwDiffeomorph, Circle.exp_zero, Circle.coe_one, one_mul,
    tubeModel, c.tubeOf_add_int]

theorem tubeModel_screwBase (x : ModelCoordinates) :
    c.tubeModel.{u} (screwDiffeomorph (-2 * Real.pi / c.pnat) (-1 * c.q / c.pnat) x) =
      c.tubeModel x := by
  have hp := c.p_ne_zero
  rw [tubeModel_screwDiffeomorph, tubeModel]
  have h := c.tubeOf_rotate.{u} (planeOf x) (x 2) (-1) 0
  have e1 : 2 * Real.pi * ((-1 : ℤ) : ℝ) / c.p = -2 * Real.pi / ((c.pnat : ℕ) : ℝ) := by
    rw [coe_pnat]
    push_cast
    ring
  have e2 : (((-1 : ℤ) : ℝ) * c.q + ((0 : ℤ) : ℝ) * c.p) / c.p =
      -1 * c.q / ((c.pnat : ℕ) : ℝ) := by
    rw [coe_pnat]
    push_cast
    ring
  rw [e1, e2] at h
  exact h

theorem discMap_circle_mul (μ : Circle) (w : ℂ) : discMap ((μ : ℂ) * w) = (μ : ℂ) * discMap w := by
  simp only [discMap, norm_mul, Circle.norm_coe, one_mul]
  rw [mul_smul_comm]

theorem tubeOf_discMap_eq [Fact ((0 : ℝ) < 1)] (x : ModelCoordinates) :
    c.tubeOf.{u} (discMap (planeOf x)) (x 2) =
      tubeLift (((scaledScrewTubeDiffeomorph c.pnat c.a 1 (Quotient.mk'' x)).1 : ℂ),
        (scaledScrewTubeDiffeomorph c.pnat c.a 1 (Quotient.mk'' x)).2) := by
  rw [scaledScrewTubeDiffeomorph_mk, tubeLift_apply]
  simp only [discDiffeo_apply_coe, div_one, coe_pnat]
  refine Prod.ext (ULift.ext ?_) rfl
  change 3 * discMap (planeOf x) * (Circle.exp (2 * Real.pi * c.a * x 2) : ℂ) =
    3 * discMap ((Circle.exp (2 * Real.pi * c.a * x 2) : ℂ) * planeOf x)
  rw [discMap_circle_mul]
  ring

end ConeFilling

end GC.Seifert
