import DifferentialGeometry.Geometry.Thurston.Models.ConeModel
import DifferentialGeometry.Geometry.Thurston.Transport
import Mathlib.Analysis.SpecialFunctions.Complex.Circle

/-!
# The fibred solid torus `V(p, q)` as the open solid torus `D̊² × S¹`

For the screw group `ScrewGroup θ ℓ` of `ConeModel.lean` (`ℓ ≠ 0`), the map
`untwist θ ℓ (z, t) = (e^{-iθt/ℓ} z, e^{2πit/ℓ}) : ℝ² × ℝ → ℂ × Circle` is invariant
(`ScrewGroup.untwist_smul`) and its restriction to `|2π(t - t₀)/ℓ| < π` is a chart with smooth
inverse built from a branch of `arg` (`ScrewGroup.untwistChart`). Composing with local inverses
of the quotient map shows that the descended map is a local diffeomorphism; it is bijective, hence
a diffeomorphism `ScrewGroup.untwistDiffeo : ScrewQuotient θ ℓ ≃ₘ ℂ × Circle`. With the radial
diffeomorphism `discDiffeo : ℂ ≃ₘ D̊²`, `w ↦ w / √(1 + |w|²)`, this gives
`solidTorusDiffeo p q : FibredSolidTorus p q ≃ₘ D̊² × Circle` (`θ = 2πq/p`, `ℓ = 1/p`); the
untwisting preserves `|z|`, so the sub-cylinder `|z| < 1` corresponds to `|w| < 1`
(`ScrewGroup.norm_untwist_fst`).

Pulling back along it, `coneSolidTorusAtlas p q m` is a model atlas on `D̊² × Circle` for each
`ConnectionModel`, and `coneSolidTorusGeometry` a complete geometric structure when
`m.baseCurvature ≤ 0`.

Fibres. The core `{0} × ℝ` maps onto `{0} × Circle` (`solidTorusDiffeo_core`) and closes up after
length `1/p` (`mk_fibreShift_eq_mk_fibreShift_iff`); for `z ≠ 0` and `p, q` coprime the vertical
line through `(z, t)` closes up exactly after length `1` (`mk_add_fibreShift_eq_mk_iff`), so the
core is the exceptional fibre of multiplicity `p`. Conversely `{w} × Circle` is the image of the
helix `s ↦ (e^{2πiqs/p} ρ⁻¹(w), s/p)` (`solidTorusDiffeo_symm_apply`), which meets the screw orbit
of `(ρ⁻¹(w), 0)` at integer `s` (`screwHelix_int`).
-/

set_option autoImplicit false

noncomputable section
open DifferentialGeometry
open scoped Manifold ContDiff

namespace GC.Geometry

attribute [local instance] finrank_real_complex_fact'

def planeOf (x : ModelCoordinates) : ℂ := (x 0 : ℂ) + (x 1 : ℂ) * Complex.I

@[simp] theorem planeOf_re (x : ModelCoordinates) : (planeOf x).re = x 0 := by
  simp [planeOf]

@[simp] theorem planeOf_im (x : ModelCoordinates) : (planeOf x).im = x 1 := by
  simp [planeOf]

theorem modelCoordinates_ext {x y : ModelCoordinates} (h : planeOf x = planeOf y)
    (h2 : x 2 = y 2) : x = y := by
  have h0 := congrArg Complex.re h
  have h1 := congrArg Complex.im h
  simp only [planeOf_re, planeOf_im] at h0 h1
  ext i
  fin_cases i
  exacts [h0, h1, h2]

def ofPlane (w : ℂ) (t : ℝ) : ModelCoordinates := !₂[w.re, w.im, t]

@[simp] theorem planeOf_ofPlane (w : ℂ) (t : ℝ) : planeOf (ofPlane w t) = w := by
  apply Complex.ext <;> simp [ofPlane]

@[simp] theorem ofPlane_apply_two (w : ℂ) (t : ℝ) : ofPlane w t 2 = t := by
  simp [ofPlane]

theorem planeOf_planeRotation (t : ℝ) (x : ModelCoordinates) :
    planeOf (planeRotation t x) = (Circle.exp t : ℂ) * planeOf x := by
  apply Complex.ext
  · simp [Circle.coe_exp, Complex.exp_ofReal_mul_I_re, Complex.exp_ofReal_mul_I_im]
  · simp [Circle.coe_exp, Complex.exp_ofReal_mul_I_re, Complex.exp_ofReal_mul_I_im]
    ring

theorem planeOf_add_fibreShift (s : ℝ) (x : ModelCoordinates) :
    planeOf (x + fibreShift s) = planeOf x := by
  apply Complex.ext <;> simp

theorem circleExp_mul_circleExp_neg (a : ℝ) (w : ℂ) :
    (Circle.exp a : ℂ) * ((Circle.exp (-a) : ℂ) * w) = w := by
  rw [← mul_assoc, ← Circle.coe_mul, ← Circle.exp_add, add_neg_cancel, Circle.exp_zero,
    Circle.coe_one, one_mul]

theorem circleExp_neg_mul_circleExp (a : ℝ) (w : ℂ) :
    (Circle.exp (-a) : ℂ) * ((Circle.exp a : ℂ) * w) = w := by
  rw [← mul_assoc, ← Circle.coe_mul, ← Circle.exp_add, neg_add_cancel, Circle.exp_zero,
    Circle.coe_one, one_mul]

namespace ScrewGroup

variable {θ ℓ : ℝ}

theorem planeOf_smul (γ : ScrewGroup θ ℓ) (x : ModelCoordinates) :
    planeOf (γ • x) = (Circle.exp (θ * γ.shift) : ℂ) * planeOf x := by
  rw [smul_def, linearPart, translationPart, planeOf_add_fibreShift, planeOf_planeRotation]

def untwist (θ ℓ : ℝ) (x : ModelCoordinates) : ℂ × Circle :=
  ((Circle.exp (-(θ * x 2 / ℓ)) : ℂ) * planeOf x, Circle.exp (2 * Real.pi * x 2 / ℓ))

theorem untwist_smul [Fact (ℓ ≠ 0)] (γ : ScrewGroup θ ℓ) (x : ModelCoordinates) :
    untwist θ ℓ (γ • x) = untwist θ ℓ x := by
  have hℓ : ℓ ≠ 0 := Fact.out
  have h2 := smul_apply_two γ x
  simp only [untwist, h2, planeOf_smul, Prod.mk.injEq]
  constructor
  · rw [← mul_assoc, ← Circle.coe_mul, ← Circle.exp_add]
    rw [show -(θ * (x 2 + ℓ * γ.shift) / ℓ) + θ * γ.shift = -(θ * x 2 / ℓ) by field_simp; ring]
  · rw [show 2 * Real.pi * (x 2 + ℓ * γ.shift) / ℓ =
        2 * Real.pi * x 2 / ℓ + γ.shift * (2 * Real.pi) by field_simp,
      Circle.exp_add, Circle.exp_int_mul_two_pi, mul_one]

theorem norm_untwist_fst (x : ModelCoordinates) :
    ‖(untwist θ ℓ x).1‖ = ‖planeOf x‖ := by
  simp only [untwist, norm_mul, Circle.norm_coe, one_mul]

theorem contDiff_circleExp_coe {f : ModelCoordinates → ℝ} (hf : ContDiff ℝ ∞ f) :
    ContDiff ℝ ∞ fun x => (Circle.exp (f x) : ℂ) := by
  simp only [Circle.coe_exp]
  exact Complex.contDiff_exp.comp ((Complex.ofRealCLM.contDiff.comp hf).mul contDiff_const)

theorem contDiff_planeOf : ContDiff ℝ ∞ planeOf := by
  have hc (j : Fin 3) : ContDiff ℝ ∞ (fun q : ModelCoordinates => q j) :=
    (PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin 3 => ℝ) j).contDiff
  unfold planeOf
  exact (Complex.ofRealCLM.contDiff.comp (hc 0)).add
    ((Complex.ofRealCLM.contDiff.comp (hc 1)).mul contDiff_const)

theorem contMDiff_untwist :
    ContMDiff (𝓡 3) (𝓘(ℝ, ℂ).prod (𝓡 1)) ∞ (untwist θ ℓ) := by
  have h2 : ContDiff ℝ ∞ (fun q : ModelCoordinates => q 2) :=
    (PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin 3 => ℝ) 2).contDiff
  refine ContMDiff.prodMk ?_ ?_
  · exact ((contDiff_circleExp_coe ((contDiff_const.mul h2).div_const ℓ).neg).mul
      contDiff_planeOf).contMDiff
  · exact contMDiff_circleExp.comp ((contDiff_const.mul h2).div_const ℓ).contMDiff

def screwPhase (ℓ t : ℝ) : Circle := Circle.exp (2 * Real.pi * t / ℓ)

def screwLiftHeight (ℓ : ℝ) (x₀ : ModelCoordinates) (c : ℂ) : ℝ :=
  x₀ 2 + ℓ * Complex.arg c / (2 * Real.pi)

def untwistLift (θ ℓ : ℝ) (x₀ : ModelCoordinates) (y : ℂ × Circle) : ModelCoordinates :=
  ofPlane
    ((Circle.exp (θ * screwLiftHeight ℓ x₀ (y.2 * (screwPhase ℓ (x₀ 2))⁻¹ : Circle) / ℓ) : ℂ) *
      y.1)
    (screwLiftHeight ℓ x₀ (y.2 * (screwPhase ℓ (x₀ 2))⁻¹ : Circle))

theorem contDiffAt_liftChart (x₀ : ModelCoordinates) {z : ℂ × ℂ}
    (hz : z.2 ∈ Complex.slitPlane) :
    ContDiffAt ℝ ∞ (fun z : ℂ × ℂ => ofPlane
      ((Circle.exp (θ * screwLiftHeight ℓ x₀ z.2 / ℓ) : ℂ) * z.1)
      (screwLiftHeight ℓ x₀ z.2)) z := by
  have hh : ContDiffAt ℝ ∞ (fun z : ℂ × ℂ => screwLiftHeight ℓ x₀ z.2) z := by
    unfold screwLiftHeight
    exact contDiffAt_const.add ((contDiffAt_const.mul
      ((contDiffAt_arg hz).comp z contDiffAt_snd)).div_const _)
  have he : ContDiffAt ℝ ∞ (fun z : ℂ × ℂ =>
      (Circle.exp (θ * screwLiftHeight ℓ x₀ z.2 / ℓ) : ℂ) * z.1) z := by
    simp only [Circle.coe_exp]
    exact (Complex.contDiff_exp.contDiffAt.comp z ((Complex.ofRealCLM.contDiff.contDiffAt.comp z
      ((contDiffAt_const.mul hh).div_const ℓ)).mul contDiffAt_const)).mul contDiffAt_fst
  refine contDiffAt_euclidean.2 fun i => ?_
  fin_cases i
  · exact Complex.reCLM.contDiff.contDiffAt.comp z he
  · exact Complex.imCLM.contDiff.contDiffAt.comp z he
  · exact hh

theorem contMDiffAt_untwistLift (x₀ : ModelCoordinates) {y : ℂ × Circle}
    (hy : ((y.2 * (screwPhase ℓ (x₀ 2))⁻¹ : Circle) : ℂ) ∈ Complex.slitPlane) :
    ContMDiffAt (𝓘(ℝ, ℂ).prod (𝓡 1)) (𝓡 3) ∞ (untwistLift θ ℓ x₀) y := by
  have hι : ContMDiffAt (𝓘(ℝ, ℂ).prod (𝓡 1)) 𝓘(ℝ, ℂ × ℂ) ∞
      (fun y : ℂ × Circle => (y.1, ((y.2 * (screwPhase ℓ (x₀ 2))⁻¹ : Circle) : ℂ))) y := by
    refine contMDiffAt_fst.prodMk_space ?_
    simp only [Circle.coe_mul]
    exact ((contDiff_id.mul contDiff_const).contDiffAt).comp_contMDiffAt
      ((contMDiff_coe_sphere.contMDiffAt).comp y contMDiffAt_snd)
  exact ContDiffAt.comp_contMDiffAt (x := y)
    (f := fun y : ℂ × Circle => (y.1, ((y.2 * (screwPhase ℓ (x₀ 2))⁻¹ : Circle) : ℂ)))
    (contDiffAt_liftChart (θ := θ) (ℓ := ℓ) x₀ hy) hι

theorem untwist_snd_mul_inv (x₀ x : ModelCoordinates) :
    (untwist θ ℓ x).2 * (screwPhase ℓ (x₀ 2))⁻¹ = Circle.exp (2 * Real.pi * (x 2 - x₀ 2) / ℓ) := by
  simp only [untwist, screwPhase]
  rw [← Circle.exp_neg, ← Circle.exp_add]
  congr 1
  ring

theorem untwistLift_two (x₀ : ModelCoordinates) (y : ℂ × Circle) :
    untwistLift θ ℓ x₀ y 2 = screwLiftHeight ℓ x₀ (y.2 * (screwPhase ℓ (x₀ 2))⁻¹ : Circle) := by
  simp [untwistLift]

variable [Fact (ℓ ≠ 0)]

def untwistChart (θ ℓ : ℝ) [Fact (ℓ ≠ 0)] (x₀ : ModelCoordinates) :
    PartialDiffeomorph (𝓡 3) (𝓘(ℝ, ℂ).prod (𝓡 1)) ModelCoordinates (ℂ × Circle) ∞ where
  toFun := untwist θ ℓ
  invFun := untwistLift θ ℓ x₀
  source := {x | |2 * Real.pi * (x 2 - x₀ 2) / ℓ| < Real.pi}
  target := {y | ((y.2 * (screwPhase ℓ (x₀ 2))⁻¹ : Circle) : ℂ) ∈ Complex.slitPlane}
  map_source' x hx := by
    obtain ⟨h1, h2⟩ := abs_lt.1 (show |2 * Real.pi * (x 2 - x₀ 2) / ℓ| < Real.pi from hx)
    change (((untwist θ ℓ x).2 * (screwPhase ℓ (x₀ 2))⁻¹ : Circle) : ℂ) ∈ Complex.slitPlane
    rw [untwist_snd_mul_inv, Complex.mem_slitPlane_iff_arg, Circle.arg_exp h1 h2.le]
    exact ⟨h2.ne, Circle.coe_ne_zero _⟩
  map_target' y hy := by
    have hℓ : ℓ ≠ 0 := Fact.out
    have hy' : ((y.2 * (screwPhase ℓ (x₀ 2))⁻¹ : Circle) : ℂ) ∈ Complex.slitPlane := hy
    change |2 * Real.pi * (untwistLift θ ℓ x₀ y 2 - x₀ 2) / ℓ| < Real.pi
    have h1 := Complex.neg_pi_lt_arg ((y.2 * (screwPhase ℓ (x₀ 2))⁻¹ : Circle) : ℂ)
    have h2 := Complex.arg_lt_pi_iff.2 ((Complex.mem_slitPlane_iff.1 hy').imp le_of_lt id)
    rw [untwistLift_two, abs_lt]
    have he : 2 * Real.pi *
        (screwLiftHeight ℓ x₀ (y.2 * (screwPhase ℓ (x₀ 2))⁻¹ : Circle) - x₀ 2) / ℓ =
        Complex.arg ((y.2 * (screwPhase ℓ (x₀ 2))⁻¹ : Circle) : ℂ) := by
      unfold screwLiftHeight
      field_simp
      ring
    rw [he]
    exact ⟨h1, h2⟩
  left_inv' x hx := by
    have hℓ : ℓ ≠ 0 := Fact.out
    obtain ⟨h1, h2⟩ := abs_lt.1 (show |2 * Real.pi * (x 2 - x₀ 2) / ℓ| < Real.pi from hx)
    have hh :
        screwLiftHeight ℓ x₀ ((untwist θ ℓ x).2 * (screwPhase ℓ (x₀ 2))⁻¹ : Circle) = x 2 := by
      rw [untwist_snd_mul_inv, screwLiftHeight, Circle.arg_exp h1 h2.le]
      field_simp
      ring
    change untwistLift θ ℓ x₀ (untwist θ ℓ x) = x
    apply modelCoordinates_ext
    · rw [untwistLift, planeOf_ofPlane, hh]
      exact circleExp_mul_circleExp_neg _ _
    · rw [untwistLift_two, hh]
  right_inv' y hy := by
    have hℓ : ℓ ≠ 0 := Fact.out
    change untwist θ ℓ (untwistLift θ ℓ x₀ y) = y
    have hh : 2 * Real.pi * screwLiftHeight ℓ x₀ (y.2 * (screwPhase ℓ (x₀ 2))⁻¹ : Circle) / ℓ =
        2 * Real.pi * x₀ 2 / ℓ + Complex.arg ((y.2 * (screwPhase ℓ (x₀ 2))⁻¹ : Circle) : ℂ) := by
      unfold screwLiftHeight
      field_simp
    refine Prod.ext ?_ ?_
    · change (Circle.exp (-(θ * untwistLift θ ℓ x₀ y 2 / ℓ)) : ℂ) *
        planeOf (untwistLift θ ℓ x₀ y) = y.1
      rw [untwistLift_two, untwistLift, planeOf_ofPlane]
      exact circleExp_neg_mul_circleExp _ _
    · change Circle.exp (2 * Real.pi * untwistLift θ ℓ x₀ y 2 / ℓ) = y.2
      rw [untwistLift_two, hh, Circle.exp_add, Circle.exp_arg]
      change screwPhase ℓ (x₀ 2) * (y.2 * (screwPhase ℓ (x₀ 2))⁻¹) = y.2
      rw [mul_comm, mul_assoc, inv_mul_cancel, mul_one]
  open_source := by
    have hc : Continuous fun x : ModelCoordinates => x 2 :=
      (PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin 3 => ℝ) 2).continuous
    exact isOpen_lt (by fun_prop) continuous_const
  open_target := Complex.isOpen_slitPlane.preimage
    (continuous_subtype_val.comp (continuous_snd.mul continuous_const))
  contMDiffOn_toFun := contMDiff_untwist.contMDiffOn
  contMDiffOn_invFun y hy := (contMDiffAt_untwistLift x₀ hy).contMDiffWithinAt

theorem mem_untwistChart_source (x₀ : ModelCoordinates) : x₀ ∈ (untwistChart θ ℓ x₀).source := by
  change |2 * Real.pi * (x₀ 2 - x₀ 2) / ℓ| < Real.pi
  simp [Real.pi_pos]

end ScrewGroup

abbrev ScrewQuotient (θ ℓ : ℝ) : Type :=
  MulAction.orbitRel.Quotient (ScrewGroup θ ℓ) ModelCoordinates

namespace ScrewGroup

variable {θ ℓ : ℝ} [Fact (ℓ ≠ 0)]

def untwistQuotient (θ ℓ : ℝ) [Fact (ℓ ≠ 0)] : ScrewQuotient θ ℓ → ℂ × Circle :=
  Quotient.lift (untwist θ ℓ) fun a b h => by
    obtain ⟨γ, rfl⟩ := MulAction.mem_orbit_iff.1 (MulAction.orbitRel_apply.1 h)
    exact untwist_smul γ b

@[simp] theorem untwistQuotient_mk (x : ModelCoordinates) :
    untwistQuotient θ ℓ (Quotient.mk'' x) = untwist θ ℓ x :=
  rfl

theorem isLocalDiffeomorph_untwistQuotient :
    IsLocalDiffeomorph (𝓡 3) (𝓘(ℝ, ℂ).prod (𝓡 1)) ∞ (untwistQuotient θ ℓ) := by
  intro q
  obtain ⟨x, rfl⟩ := Quotient.mk''_surjective q
  obtain ⟨Ψ, hx, heq⟩ := isLocalDiffeomorph_orbitMk (𝓡 3) (ScrewGroup θ ℓ) ModelCoordinates x
  have hΨx : Ψ x = Quotient.mk'' x := (heq hx).symm
  refine ⟨Ψ.symm.trans (untwistChart θ ℓ x), ⟨?_, ?_⟩, fun y hy => ?_⟩
  · rw [← hΨx]
    exact Ψ.toPartialEquiv.map_source hx
  · change Ψ.toPartialEquiv.symm (Quotient.mk'' x) ∈ (untwistChart θ ℓ x).source
    rw [← hΨx, Ψ.toPartialEquiv.left_inv hx]
    exact mem_untwistChart_source x
  · have hy1 : y ∈ Ψ.toPartialEquiv.target := hy.1
    have hy' : y = Quotient.mk'' (Ψ.toPartialEquiv.symm y) := by
      rw [heq (Ψ.toPartialEquiv.map_target hy1), Ψ.toPartialEquiv.right_inv hy1]
    change untwistQuotient θ ℓ y = untwist θ ℓ (Ψ.toPartialEquiv.symm y)
    conv_lhs => rw [hy']
    rfl

theorem bijective_untwistQuotient : Function.Bijective (untwistQuotient θ ℓ) := by
  have hℓ : ℓ ≠ 0 := Fact.out
  constructor
  · rintro ⟨x⟩ ⟨y⟩ h
    change untwist θ ℓ x = untwist θ ℓ y at h
    simp only [untwist, Prod.mk.injEq] at h
    obtain ⟨h1, h2⟩ := h
    obtain ⟨m, hm⟩ := Circle.exp_eq_exp.1 h2
    have hx2 : x 2 = y 2 + ℓ * m := by
      field_simp at hm
      linarith
    apply Quot.sound
    refine MulAction.orbitRel_apply.2 (MulAction.mem_orbit_iff.2 ⟨⟨m⟩, ?_⟩)
    apply modelCoordinates_ext
    · have h1' := congrArg (fun c => (Circle.exp (θ * x 2 / ℓ) : ℂ) * c) h1
      simp only [circleExp_mul_circleExp_neg] at h1'
      rw [planeOf_smul, h1', ← mul_assoc, ← Circle.coe_mul, ← Circle.exp_add, hx2]
      rw [show θ * (y 2 + ℓ * m) / ℓ + -(θ * y 2 / ℓ) = θ * m by field_simp; ring]
    · rw [smul_apply_two, hx2]
  · rintro ⟨w, u⟩
    refine ⟨Quotient.mk'' (ofPlane ((Circle.exp (θ * (ℓ * Complex.arg (u : ℂ) / (2 * Real.pi)) / ℓ)
      : ℂ) * w) (ℓ * Complex.arg (u : ℂ) / (2 * Real.pi))), ?_⟩
    rw [untwistQuotient_mk]
    simp only [untwist, planeOf_ofPlane, ofPlane_apply_two, Prod.mk.injEq]
    refine ⟨?_, ?_⟩
    · exact circleExp_neg_mul_circleExp _ _
    · rw [show 2 * Real.pi * (ℓ * Complex.arg (u : ℂ) / (2 * Real.pi)) / ℓ =
        Complex.arg (u : ℂ) by field_simp]
      exact Circle.exp_arg u

def untwistDiffeo (θ ℓ : ℝ) [Fact (ℓ ≠ 0)] :
    ScrewQuotient θ ℓ ≃ₘ⟮𝓡 3, 𝓘(ℝ, ℂ).prod (𝓡 1)⟯ ℂ × Circle :=
  isLocalDiffeomorph_untwistQuotient.diffeomorphOfBijective bijective_untwistQuotient

@[simp] theorem untwistDiffeo_mk (x : ModelCoordinates) :
    untwistDiffeo θ ℓ (Quotient.mk'' x) = untwist θ ℓ x :=
  rfl

end ScrewGroup

def openUnitDisc : TopologicalSpace.Opens ℂ := ⟨Metric.ball 0 1, Metric.isOpen_ball⟩

instance : LocallyCompactSpace openUnitDisc := Metric.isOpen_ball.locallyCompactSpace

theorem mem_openUnitDisc {v : ℂ} : v ∈ openUnitDisc ↔ ‖v‖ < 1 := by
  change v ∈ Metric.ball (0 : ℂ) 1 ↔ _
  rw [Metric.mem_ball, dist_zero_right]

def discMap (w : ℂ) : ℂ := (√(1 + ‖w‖ ^ 2))⁻¹ • w

def discInv (v : ℂ) : ℂ := (√(1 - ‖v‖ ^ 2))⁻¹ • v

theorem norm_discMap_sq (w : ℂ) : ‖discMap w‖ ^ 2 = ‖w‖ ^ 2 / (1 + ‖w‖ ^ 2) := by
  have h : 0 ≤ 1 + ‖w‖ ^ 2 := by positivity
  rw [discMap, norm_smul, mul_pow, Real.norm_eq_abs, sq_abs, inv_pow, Real.sq_sqrt h]
  ring

theorem norm_discMap_lt (w : ℂ) : ‖discMap w‖ < 1 := by
  have h := norm_discMap_sq w
  have h1 : ‖w‖ ^ 2 / (1 + ‖w‖ ^ 2) < 1 := by
    rw [div_lt_one (by positivity)]; linarith
  nlinarith [norm_nonneg (discMap w)]

theorem discInv_discMap (w : ℂ) : discInv (discMap w) = w := by
  have ha : 0 < √(1 + ‖w‖ ^ 2) := Real.sqrt_pos.2 (by positivity)
  have h1 : 1 - ‖discMap w‖ ^ 2 = (√(1 + ‖w‖ ^ 2))⁻¹ ^ 2 := by
    rw [norm_discMap_sq, inv_pow, Real.sq_sqrt (by positivity)]
    field_simp
    ring
  rw [discInv, h1, Real.sqrt_sq (inv_nonneg.2 ha.le), inv_inv, discMap, smul_smul,
    mul_inv_cancel₀ ha.ne', one_smul]

theorem discMap_discInv {v : ℂ} (hv : ‖v‖ < 1) : discMap (discInv v) = v := by
  have hv2 : ‖v‖ ^ 2 < 1 := by nlinarith [norm_nonneg v]
  have ha : 0 < √(1 - ‖v‖ ^ 2) := Real.sqrt_pos.2 (by linarith)
  have hne : 1 - ‖v‖ ^ 2 ≠ 0 := by linarith
  have h1 : 1 + ‖discInv v‖ ^ 2 = (√(1 - ‖v‖ ^ 2))⁻¹ ^ 2 := by
    rw [discInv, norm_smul, mul_pow, Real.norm_eq_abs, sq_abs, inv_pow,
      Real.sq_sqrt (by linarith)]
    field_simp
    ring
  rw [discMap, h1, Real.sqrt_sq (inv_nonneg.2 ha.le), inv_inv, discInv, smul_smul,
    mul_inv_cancel₀ ha.ne', one_smul]

theorem contDiff_discMap : ContDiff ℝ ∞ discMap := by
  have hs : ContDiff ℝ ∞ fun w : ℂ => √(1 + ‖w‖ ^ 2) :=
    (contDiff_const.add (contDiff_norm_sq ℝ)).sqrt fun w => by positivity
  exact (hs.inv fun w => (Real.sqrt_pos.2 (by positivity)).ne').smul contDiff_id

theorem contDiffAt_discInv {v : ℂ} (hv : ‖v‖ < 1) : ContDiffAt ℝ ∞ discInv v := by
  have hv2 : 0 < 1 - ‖v‖ ^ 2 := by nlinarith [norm_nonneg v]
  have hs : ContDiffAt ℝ ∞ (fun w : ℂ => √(1 - ‖w‖ ^ 2)) v :=
    (contDiffAt_const.sub (contDiff_norm_sq ℝ).contDiffAt).sqrt hv2.ne'
  exact (hs.inv (Real.sqrt_pos.2 hv2).ne').smul contDiffAt_id

def discDiffeo : ℂ ≃ₘ⟮𝓘(ℝ, ℂ), 𝓘(ℝ, ℂ)⟯ openUnitDisc where
  toFun w := ⟨discMap w, mem_openUnitDisc.2 (norm_discMap_lt w)⟩
  invFun v := discInv v
  left_inv w := discInv_discMap w
  right_inv v := Subtype.ext (discMap_discInv (mem_openUnitDisc.1 v.2))
  contMDiff_toFun w := (ContMDiffAt.subtypeVal_comp_iff openUnitDisc _ w).1
    contDiff_discMap.contMDiff.contMDiffAt
  contMDiff_invFun v := contMDiffAt_subtype_iff.2
    (contDiffAt_discInv (mem_openUnitDisc.1 v.2)).contMDiffAt

@[simp] theorem discDiffeo_apply_coe (w : ℂ) : (discDiffeo w : ℂ) = discMap w :=
  rfl

@[simp] theorem discDiffeo_symm_apply (v : openUnitDisc) : discDiffeo.symm v = discInv v :=
  rfl

def solidTorusDiffeo (p : ℕ+) (q : ℤ) :
    FibredSolidTorus p q ≃ₘ⟮𝓡 3, 𝓘(ℝ, ℂ).prod (𝓡 1)⟯ openUnitDisc × Circle :=
  (ScrewGroup.untwistDiffeo _ _).trans (discDiffeo.prodCongr (Diffeomorph.refl (𝓡 1) Circle ∞))

theorem ScrewGroup.mk_eq_mk_iff {θ ℓ : ℝ} {x y : ModelCoordinates} :
    (Quotient.mk'' x : ScrewQuotient θ ℓ) = Quotient.mk'' y ↔ ∃ γ : ScrewGroup θ ℓ, γ • y = x := by
  rw [Quotient.eq'', MulAction.orbitRel_apply, MulAction.mem_orbit_iff]

section SolidTorus

variable (p : ℕ+) (q : ℤ)

theorem solidTorusDiffeo_mk (x : ModelCoordinates) :
    solidTorusDiffeo p q (Quotient.mk'' x) =
      (discDiffeo ((Circle.exp (-(2 * Real.pi * q * x 2)) : ℂ) * planeOf x),
        Circle.exp (2 * Real.pi * p * x 2)) := by
  have hp : (p : ℝ) ≠ 0 := by positivity
  change (discDiffeo (ScrewGroup.untwist (2 * Real.pi * q / p) (1 / p) x).1,
    (ScrewGroup.untwist (2 * Real.pi * q / p) (1 / p) x).2) = _
  simp only [ScrewGroup.untwist]
  rw [show 2 * Real.pi * q / p * x 2 / (1 / p) = 2 * Real.pi * q * x 2 by field_simp,
    show 2 * Real.pi * x 2 / (1 / p) = 2 * Real.pi * p * x 2 by field_simp]

theorem solidTorusDiffeo_core (t : ℝ) :
    solidTorusDiffeo p q (Quotient.mk'' (fibreShift t)) =
      (discDiffeo 0, Circle.exp (2 * Real.pi * p * t)) := by
  rw [solidTorusDiffeo_mk]
  have h0 : planeOf (fibreShift t) = 0 := by apply Complex.ext <;> simp
  simp [h0]

theorem mk_fibreShift_eq_mk_fibreShift_iff (t s : ℝ) :
    (Quotient.mk'' (fibreShift t) : FibredSolidTorus p q) = Quotient.mk'' (fibreShift s) ↔
      ∃ n : ℤ, s = t + n / p := by
  rw [ScrewGroup.mk_eq_mk_iff]
  constructor
  · rintro ⟨γ, hγ⟩
    have h2 := congrArg (fun y : ModelCoordinates => y 2) hγ
    simp only [ScrewGroup.smul_apply_two, fibreShift_apply_two] at h2
    refine ⟨-γ.shift, ?_⟩
    push_cast
    linear_combination h2
  · rintro ⟨n, rfl⟩
    refine ⟨⟨-n⟩, ?_⟩
    rw [ScrewGroup.smul_fibreShift]
    congr 1
    push_cast
    ring

theorem mk_add_fibreShift_eq_mk_iff (hpq : IsCoprime (p : ℤ) q) {x : ModelCoordinates}
    (hx : planeOf x ≠ 0) (s : ℝ) :
    (Quotient.mk'' (x + fibreShift s) : FibredSolidTorus p q) = Quotient.mk'' x ↔
      ∃ n : ℤ, s = n := by
  have hp : (p : ℝ) ≠ 0 := by positivity
  rw [ScrewGroup.mk_eq_mk_iff]
  constructor
  · rintro ⟨γ, hγ⟩
    have h2 := congrArg (fun y : ModelCoordinates => y 2) hγ
    simp only [ScrewGroup.smul_apply_two] at h2
    have h2' : x 2 + 1 / p * γ.shift = x 2 + s := by
      rw [h2]
      simp
    have hplane := congrArg planeOf hγ
    rw [ScrewGroup.planeOf_smul, planeOf_add_fibreShift] at hplane
    have hone : Circle.exp (2 * Real.pi * q / p * γ.shift) = 1 := by
      apply Subtype.ext
      have h := mul_right_cancel₀ hx (hplane.trans (one_mul _).symm)
      exact h
    obtain ⟨k, hk⟩ := Circle.exp_eq_one.1 hone
    have hdiv : (p : ℤ) ∣ q * γ.shift := by
      refine ⟨k, ?_⟩
      have hk' : (q : ℝ) * γ.shift = p * k := by
        field_simp at hk
        linarith
      exact_mod_cast hk'
    obtain ⟨j, hj⟩ := hpq.dvd_of_dvd_mul_left hdiv
    refine ⟨j, ?_⟩
    have hj' : (γ.shift : ℝ) = p * j := by exact_mod_cast hj
    rw [hj'] at h2'
    field_simp at h2'
    linarith
  · rintro ⟨j, rfl⟩
    refine ⟨⟨p * j⟩, ?_⟩
    apply modelCoordinates_ext
    · rw [ScrewGroup.planeOf_smul, planeOf_add_fibreShift]
      rw [show 2 * Real.pi * q / p * (((p : ℤ) * j : ℤ) : ℝ) = ((q * j : ℤ) : ℝ) * (2 * Real.pi) by
        push_cast; field_simp, Circle.exp_int_mul_two_pi, Circle.coe_one, one_mul]
    · rw [ScrewGroup.smul_apply_two]
      simp only [PiLp.add_apply, fibreShift_apply_two]
      push_cast
      field_simp

theorem screwHelix_int (z : ℂ) (n : ℤ) :
    ofPlane ((Circle.exp (2 * Real.pi * q * n / p) : ℂ) * z) (n / p) =
      (⟨n⟩ : FibredSolidTorusGroup p q) • ofPlane z 0 := by
  apply modelCoordinates_ext
  · rw [ScrewGroup.planeOf_smul, planeOf_ofPlane, planeOf_ofPlane]
    congr 3
    ring
  · rw [ScrewGroup.smul_apply_two]
    simp only [ofPlane_apply_two]
    ring

theorem solidTorusDiffeo_symm_apply (w : openUnitDisc) (s : ℝ) :
    (solidTorusDiffeo p q).symm (w, Circle.exp (2 * Real.pi * s)) =
      Quotient.mk'' (ofPlane ((Circle.exp (2 * Real.pi * q * s / p) : ℂ) * discInv w) (s / p)) := by
  have hp : (p : ℝ) ≠ 0 := by positivity
  have h : solidTorusDiffeo p q (Quotient.mk''
      (ofPlane ((Circle.exp (2 * Real.pi * q * s / p) : ℂ) * discInv w) (s / p))) =
      (w, Circle.exp (2 * Real.pi * s)) := by
    rw [solidTorusDiffeo_mk, planeOf_ofPlane, ofPlane_apply_two,
      show 2 * Real.pi * q * (s / p) = 2 * Real.pi * q * s / p by ring,
      circleExp_neg_mul_circleExp, ← discDiffeo_symm_apply, Diffeomorph.apply_symm_apply,
      show 2 * Real.pi * p * (s / p) = 2 * Real.pi * s by field_simp]
  rw [← h, Diffeomorph.symm_apply_apply]

def coneSolidTorusMetric (m : ConnectionModel) :
    SmoothRiemannianMetric (𝓘(ℝ, ℂ).prod (𝓡 1)) (openUnitDisc × Circle) :=
  Diffeomorph.pullbackMetricCross (fibredSolidTorusMetric m p q) (solidTorusDiffeo p q).symm

theorem coneSolidTorusAtlas (m : ConnectionModel) :
    HasThurstonAtlas (coneSolidTorusMetric p q m) m.thurston :=
  (fibredSolidTorusAtlas m p q).pullback (solidTorusDiffeo p q).symm

def coneSolidTorusGeometry (m : ConnectionModel) (hm : m.baseCurvature ≤ 0) :
    GeometricStructure (𝓘(ℝ, ℂ).prod (𝓡 1)) (openUnitDisc × Circle) :=
  (fibredSolidTorusGeometry m hm p q).pullback (solidTorusDiffeo p q).symm

theorem coneSolidTorusGeometry_model (m : ConnectionModel) (hm : m.baseCurvature ≤ 0) :
    (coneSolidTorusGeometry p q m hm).model = m.thurston :=
  rfl

theorem coneSolidTorusGeometry_metric (m : ConnectionModel) (hm : m.baseCurvature ≤ 0) :
    (coneSolidTorusGeometry p q m hm).metric = coneSolidTorusMetric p q m :=
  rfl

end SolidTorus

end GC.Geometry
