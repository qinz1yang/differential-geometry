import DifferentialGeometry.Geometry.Thurston.Descent
import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Seifert.PlanarModels
import DifferentialGeometry.Topology.Manifold.OpenEmbedding
import DifferentialGeometry.Topology.Embedding.Diffeomorph

/-!
# The `T² × I` block is Euclidean

Chapter 6, packet K16, first tier: the open good block `T² × I` carries a complete `.euclidean`
geometry on its interior.

`TorusTimesLine` is `E³` modulo the lattice `ℤ e₀ ⊕ ℤ e₁` (`Thurston/Descent.lean`). The map
`flatWrap x = (ρ(x₂) e^{2πi x₀}, e^{2πi x₁}) : E³ → ℂ × S¹`, with the increasing bijection
`flatRadius = ρ : ℝ → (1/2, 3)`, `ρ(t) = (1/2 + 3eᵗ)/(1 + eᵗ)`, inverse
`flatHeight r = log ((r - 1/2)/(3 - r))`, is lattice invariant (`flatWrap_smul`). On the strip
`|2π(x₀ - a₀)|, |2π(x₁ - a₁)| < π` it is a chart whose inverse uses the branch
`liftAngle a w = a + arg (e^{-2πia} w)/(2π)` (`flatChart`). Composing with local inverses of the
quotient map shows that the descended map `flatQuotient` is a local diffeomorphism; it is injective
with image the open annulus `1/2 < ‖z‖ < 3` times the circle (`range_flatQuotient`), so
`flatDiffeo : TorusTimesLine ≃ₘ flatImage`.

The interior of the K06b carrier `annulusCircleCarrier = {1/2 ≤ ‖z‖ ≤ 3} × S¹` is the set where
`planarFunction 2 < 0` (`isInteriorPoint_productSet_two_iff`), which is `flatImage` up to the
universe lift (`annulusInteriorEquiv`). Pulling back `torusTimesLineGeometry` along
`annulusCircleInteriorDiffeo` gives `annulusCircleBlock_interiorGeometry`, of model `.euclidean`
(`annulusCircleBlock_interiorGeometry_model`); completeness is transported by
`GeometricStructure.pullback`.

For an arbitrary `T2Interval` block, two planar bases with the same embedded image are
diffeomorphic (`PlanarBase.diffeomorph`, from `diffeomorphOfRangeEq`), so product-fibred pieces
over them are diffeomorphic (`ProductFibredPiece.pieceDiffeomorph`). A diffeomorphism of pieces
preserves interior points and restricts to their interiors (`pieceInteriorCongr`); composing with
the model gives `T2Interval.interiorGeometry`, again `.euclidean`
(`T2Interval.interiorGeometry_model`).
-/

set_option autoImplicit false

universe u v

noncomputable section
open Set Function
open DifferentialGeometry DifferentialGeometry.Topology GC.Endpoint GC.GraphManifold GC.Geometry
open scoped Manifold ContDiff Topology

local notation "E3" => EuclideanSpace ℝ (Fin 3)

namespace GC.Seifert

attribute [local instance] finrank_real_complex_fact'

def flatRadius (t : ℝ) : ℝ := (1 / 2 + 3 * Real.exp t) / (1 + Real.exp t)

def flatHeight (r : ℝ) : ℝ := Real.log ((r - 1 / 2) / (3 - r))

theorem flatRadius_mem (t : ℝ) : 1 / 2 < flatRadius t ∧ flatRadius t < 3 := by
  have he := Real.exp_pos t
  unfold flatRadius
  constructor
  · rw [lt_div_iff₀ (by linarith)]
    linarith
  · rw [div_lt_iff₀ (by linarith)]
    linarith

theorem flatHeight_flatRadius (t : ℝ) : flatHeight (flatRadius t) = t := by
  have he := Real.exp_pos t
  have h1 : (1 + Real.exp t) ≠ 0 := by positivity
  unfold flatHeight flatRadius
  rw [show ((1 / 2 + 3 * Real.exp t) / (1 + Real.exp t) - 1 / 2) /
      (3 - (1 / 2 + 3 * Real.exp t) / (1 + Real.exp t)) = Real.exp t by
    field_simp
    ring, Real.log_exp]

theorem flatRadius_flatHeight {r : ℝ} (h1 : 1 / 2 < r) (h2 : r < 3) :
    flatRadius (flatHeight r) = r := by
  have h3 : (3 - r) ≠ 0 := by linarith
  unfold flatRadius flatHeight
  rw [Real.exp_log (div_pos (by linarith) (by linarith))]
  field_simp
  ring

theorem contDiff_flatRadius : ContDiff ℝ ∞ flatRadius :=
  (contDiff_const.add (contDiff_const.mul Real.contDiff_exp)).div
    (contDiff_const.add Real.contDiff_exp) fun t => (by positivity : (0 : ℝ) < 1 + Real.exp t).ne'

theorem contDiffAt_flatHeight {r : ℝ} (h1 : 1 / 2 < r) (h2 : r < 3) :
    ContDiffAt ℝ ∞ flatHeight r := by
  have hq : ContDiffAt ℝ ∞ (fun s : ℝ => (s - 1 / 2) / (3 - s)) r :=
    (contDiffAt_id.sub contDiffAt_const).div (contDiffAt_const.sub contDiffAt_id)
      (by simp; linarith)
  change ContDiffAt ℝ ∞ (Real.log ∘ fun s : ℝ => (s - 1 / 2) / (3 - s)) r
  have hpos : 0 < (r - 1 / 2) / (3 - r) := div_pos (by linarith) (by linarith)
  exact ContDiffAt.comp (f := fun s : ℝ => (s - 1 / 2) / (3 - s)) r
    (Real.contDiffAt_log.2 hpos.ne') hq

private theorem contDiffAt_complexArg {z : ℂ} (hz : z ∈ Complex.slitPlane) :
    ContDiffAt ℝ ∞ Complex.arg z := by
  have hlog := (Complex.contDiffAt_log hz (n := ∞)).restrict_scalars ℝ
  have h := Complex.imCLM.contDiff.contDiffAt.comp z hlog
  have hfun : (Complex.imCLM ∘ Complex.log) = Complex.arg := by
    funext w
    exact Complex.log_im w
  rwa [hfun] at h

def liftAngle (a : ℝ) (w : ℂ) : ℝ :=
  a + Complex.arg ((Circle.exp (-(2 * Real.pi * a)) : ℂ) * w) / (2 * Real.pi)

theorem circleExp_neg_mul_real_mul (a t ρ : ℝ) :
    (Circle.exp (-(2 * Real.pi * a)) : ℂ) * ((ρ : ℂ) * Circle.exp (2 * Real.pi * t)) =
      (ρ : ℂ) * Circle.exp (2 * Real.pi * (t - a)) := by
  rw [mul_left_comm, ← Circle.coe_mul, ← Circle.exp_add]
  congr 3
  ring

theorem arg_circleExp_neg_mul {a t ρ : ℝ} (hρ : 0 < ρ) (h : |2 * Real.pi * (t - a)| < Real.pi) :
    Complex.arg ((Circle.exp (-(2 * Real.pi * a)) : ℂ) *
      ((ρ : ℂ) * Circle.exp (2 * Real.pi * t))) = 2 * Real.pi * (t - a) := by
  obtain ⟨h1, h2⟩ := abs_lt.1 h
  rw [circleExp_neg_mul_real_mul, Complex.arg_real_mul _ hρ, Circle.arg_exp h1 h2.le]

theorem liftAngle_eq {a t ρ : ℝ} (hρ : 0 < ρ) (h : |2 * Real.pi * (t - a)| < Real.pi) :
    liftAngle a ((ρ : ℂ) * Circle.exp (2 * Real.pi * t)) = t := by
  rw [liftAngle, arg_circleExp_neg_mul hρ h]
  field_simp
  ring

theorem mem_slitPlane_circleExp_neg_mul {a t ρ : ℝ} (hρ : 0 < ρ)
    (h : |2 * Real.pi * (t - a)| < Real.pi) :
    (Circle.exp (-(2 * Real.pi * a)) : ℂ) * ((ρ : ℂ) * Circle.exp (2 * Real.pi * t)) ∈
      Complex.slitPlane := by
  rw [Complex.mem_slitPlane_iff_arg, arg_circleExp_neg_mul hρ h]
  refine ⟨(abs_lt.1 h).2.ne, ?_⟩
  rw [circleExp_neg_mul_real_mul]
  exact mul_ne_zero (by exact_mod_cast hρ.ne') (Circle.coe_ne_zero _)

theorem norm_mul_circleExp_liftAngle (a : ℝ) (w : ℂ) :
    (‖w‖ : ℂ) * Circle.exp (2 * Real.pi * liftAngle a w) = w := by
  have hv : ‖(Circle.exp (-(2 * Real.pi * a)) : ℂ) * w‖ = ‖w‖ := by
    rw [norm_mul, Circle.norm_coe, one_mul]
  have h2 : 2 * Real.pi * liftAngle a w = 2 * Real.pi * a +
      Complex.arg ((Circle.exp (-(2 * Real.pi * a)) : ℂ) * w) := by
    unfold liftAngle
    field_simp
  rw [h2, Circle.exp_add, Circle.coe_mul, ← hv, mul_left_comm, Circle.coe_exp
    (Complex.arg _), Complex.norm_mul_exp_arg_mul_I, ← mul_assoc, ← Circle.coe_mul,
    ← Circle.exp_add, add_neg_cancel, Circle.exp_zero, Circle.coe_one, one_mul]

theorem circleExp_liftAngle (a : ℝ) (u : Circle) :
    Circle.exp (2 * Real.pi * liftAngle a u) = u := by
  have h := norm_mul_circleExp_liftAngle a u
  rw [Circle.norm_coe, Complex.ofReal_one, one_mul] at h
  exact Circle.coe_inj.1 h

theorem abs_liftAngle_sub_lt {a : ℝ} {w : ℂ}
    (hw : (Circle.exp (-(2 * Real.pi * a)) : ℂ) * w ∈ Complex.slitPlane) :
    |2 * Real.pi * (liftAngle a w - a)| < Real.pi := by
  have he : 2 * Real.pi * (liftAngle a w - a) =
      Complex.arg ((Circle.exp (-(2 * Real.pi * a)) : ℂ) * w) := by
    unfold liftAngle
    field_simp
    ring
  rw [he, abs_lt]
  exact ⟨Complex.neg_pi_lt_arg _,
    Complex.arg_lt_pi_iff.2 ((Complex.mem_slitPlane_iff.1 hw).imp le_of_lt id)⟩

theorem contDiffAt_liftAngle {a : ℝ} {w : ℂ}
    (hw : (Circle.exp (-(2 * Real.pi * a)) : ℂ) * w ∈ Complex.slitPlane) :
    ContDiffAt ℝ ∞ (liftAngle a) w := by
  unfold liftAngle
  exact contDiffAt_const.add (((contDiffAt_complexArg hw).comp w
    ((contDiff_const.mul contDiff_id).contDiffAt)).div_const _)

private theorem euclidean3_ext {x y : E3} (h0 : x 0 = y 0) (h1 : x 1 = y 1) (h2 : x 2 = y 2) :
    x = y := by
  ext i
  fin_cases i
  exacts [h0, h1, h2]

theorem torusTranslations_smul_apply (γ : torusTranslations) (x : E3) :
    (γ • x) 0 = x 0 + ((γ : KleinBottleGroup).glide : ℝ) / 2 ∧
      (γ • x) 1 = x 1 + (γ : KleinBottleGroup).shift ∧ (γ • x) 2 = x 2 := by
  rw [torusTranslations_smul]
  simp [KleinBottleGroup.translationPart, kleinAxis, kleinFibre]

def flatWrap (x : E3) : ℂ × Circle :=
  ((flatRadius (x 2) : ℂ) * Circle.exp (2 * Real.pi * x 0), Circle.exp (2 * Real.pi * x 1))

theorem norm_flatWrap_fst (x : E3) : ‖(flatWrap x).1‖ = flatRadius (x 2) := by
  rw [flatWrap, norm_mul, Circle.norm_coe, mul_one, Complex.norm_real,
    Real.norm_of_nonneg (by linarith [(flatRadius_mem (x 2)).1])]

theorem flatWrap_smul (γ : torusTranslations) (x : E3) : flatWrap (γ • x) = flatWrap x := by
  obtain ⟨r, hr⟩ := γ.2
  obtain ⟨h0, h1, h2⟩ := torusTranslations_smul_apply γ x
  have hr' : ((γ : KleinBottleGroup).glide : ℝ) / 2 = r := by
    rw [hr]
    push_cast
    ring
  simp only [flatWrap, h0, h1, h2, hr']
  refine Prod.ext ?_ ?_
  · dsimp only
    rw [show 2 * Real.pi * (x 0 + r) = 2 * Real.pi * x 0 + r * (2 * Real.pi) by ring,
      Circle.exp_add, Circle.exp_int_mul_two_pi, mul_one]
  · dsimp only
    rw [show 2 * Real.pi * (x 1 + (γ : KleinBottleGroup).shift) =
        2 * Real.pi * x 1 + ((γ : KleinBottleGroup).shift : ℤ) * (2 * Real.pi) by ring,
      Circle.exp_add, Circle.exp_int_mul_two_pi, mul_one]

theorem contMDiff_flatWrap : ContMDiff (𝓡 3) (𝓘(ℝ, ℂ).prod (𝓡 1)) ∞ flatWrap := by
  have hc (j : Fin 3) : ContDiff ℝ ∞ (fun q : E3 => q j) :=
    (PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin 3 => ℝ) j).contDiff
  refine ContMDiff.prodMk ?_ ?_
  · have h1 : ContDiff ℝ ∞ fun x : E3 => (flatRadius (x 2) : ℂ) :=
      Complex.ofRealCLM.contDiff.comp (contDiff_flatRadius.comp (hc 2))
    have h2 : ContDiff ℝ ∞ fun x : E3 => (Circle.exp (2 * Real.pi * x 0) : ℂ) := by
      simp only [Circle.coe_exp]
      exact Complex.contDiff_exp.comp
        ((Complex.ofRealCLM.contDiff.comp (contDiff_const.mul (hc 0))).mul contDiff_const)
    exact (h1.mul h2).contMDiff
  · exact contMDiff_circleExp.comp (contDiff_const.mul (hc 1)).contMDiff

def flatLift (x₀ : E3) (y : ℂ × Circle) : E3 :=
  !₂[liftAngle (x₀ 0) y.1, liftAngle (x₀ 1) y.2, flatHeight ‖y.1‖]

theorem flatLift_zero (x₀ : E3) (y : ℂ × Circle) : flatLift x₀ y 0 = liftAngle (x₀ 0) y.1 := by
  simp [flatLift]

theorem flatLift_one (x₀ : E3) (y : ℂ × Circle) : flatLift x₀ y 1 = liftAngle (x₀ 1) y.2 := by
  simp [flatLift]

theorem flatLift_two (x₀ : E3) (y : ℂ × Circle) : flatLift x₀ y 2 = flatHeight ‖y.1‖ := by
  simp [flatLift]

def flatTarget (x₀ : E3) : Set (ℂ × Circle) :=
  {y | (1 / 2 < ‖y.1‖ ∧ ‖y.1‖ < 3) ∧
    (Circle.exp (-(2 * Real.pi * x₀ 0)) : ℂ) * y.1 ∈ Complex.slitPlane ∧
    (Circle.exp (-(2 * Real.pi * x₀ 1)) : ℂ) * y.2 ∈ Complex.slitPlane}

theorem contMDiffAt_flatLift (x₀ : E3) {y : ℂ × Circle} (hy : y ∈ flatTarget x₀) :
    ContMDiffAt (𝓘(ℝ, ℂ).prod (𝓡 1)) (𝓡 3) ∞ (flatLift x₀) y := by
  obtain ⟨⟨hr1, hr2⟩, h0, h1⟩ := hy
  have hι : ContMDiffAt (𝓘(ℝ, ℂ).prod (𝓡 1)) 𝓘(ℝ, ℂ × ℂ) ∞
      (fun y : ℂ × Circle => (y.1, (y.2 : ℂ))) y :=
    contMDiffAt_fst.prodMk_space ((contMDiff_coe_sphere.contMDiffAt).comp y contMDiffAt_snd)
  have hne : y.1 ≠ 0 := by
    intro h
    rw [h, norm_zero] at hr1
    linarith
  have hG : ContDiffAt ℝ ∞ (fun z : ℂ × ℂ =>
      !₂[liftAngle (x₀ 0) z.1, liftAngle (x₀ 1) z.2, flatHeight ‖z.1‖]) (y.1, (y.2 : ℂ)) := by
    refine contDiffAt_euclidean.2 fun i => ?_
    fin_cases i
    · exact ContDiffAt.comp (x := ((y.1, (y.2 : ℂ)) : ℂ × ℂ)) (f := Prod.fst)
        (g := liftAngle (x₀ 0)) (contDiffAt_liftAngle h0) contDiffAt_fst
    · exact ContDiffAt.comp (x := ((y.1, (y.2 : ℂ)) : ℂ × ℂ)) (f := Prod.snd)
        (g := liftAngle (x₀ 1)) (contDiffAt_liftAngle h1) contDiffAt_snd
    · exact ContDiffAt.comp (x := ((y.1, (y.2 : ℂ)) : ℂ × ℂ)) (f := fun z : ℂ × ℂ => ‖z.1‖)
        (g := flatHeight) (contDiffAt_flatHeight hr1 hr2)
        (ContDiffAt.comp (x := ((y.1, (y.2 : ℂ)) : ℂ × ℂ)) (f := Prod.fst) (g := norm)
          (contDiffAt_norm ℝ hne) contDiffAt_fst)
  exact ContDiffAt.comp_contMDiffAt (x := y)
    (f := fun y : ℂ × Circle => (y.1, (y.2 : ℂ))) hG hι

private theorem circle_eq_one_mul (u : Circle) : (u : ℂ) = ((1 : ℝ) : ℂ) * u := by
  rw [Complex.ofReal_one, one_mul]

def flatChart (x₀ : E3) :
    PartialDiffeomorph (𝓡 3) (𝓘(ℝ, ℂ).prod (𝓡 1)) E3 (ℂ × Circle) ∞ where
  toFun := flatWrap
  invFun := flatLift x₀
  source := {x | |2 * Real.pi * (x 0 - x₀ 0)| < Real.pi ∧ |2 * Real.pi * (x 1 - x₀ 1)| < Real.pi}
  target := flatTarget x₀
  map_source' x hx := by
    obtain ⟨h0, h1⟩ := hx
    have hρ := flatRadius_mem (x 2)
    refine ⟨?_, ?_, ?_⟩
    · rw [norm_flatWrap_fst]
      exact hρ
    · exact mem_slitPlane_circleExp_neg_mul (by linarith [hρ.1]) h0
    · change (Circle.exp _ : ℂ) * (Circle.exp (2 * Real.pi * x 1) : ℂ) ∈ _
      rw [circle_eq_one_mul (Circle.exp (2 * Real.pi * x 1))]
      exact mem_slitPlane_circleExp_neg_mul one_pos h1
  map_target' y hy := by
    obtain ⟨_, h0, h1⟩ := hy
    refine ⟨?_, ?_⟩
    · rw [flatLift_zero]
      exact abs_liftAngle_sub_lt h0
    · rw [flatLift_one]
      exact abs_liftAngle_sub_lt h1
  left_inv' x hx := by
    obtain ⟨h0, h1⟩ := hx
    have hρ := flatRadius_mem (x 2)
    change flatLift x₀ (flatWrap x) = x
    refine euclidean3_ext ?_ ?_ ?_
    · rw [flatLift_zero]
      exact liftAngle_eq (by linarith [hρ.1]) h0
    · rw [flatLift_one]
      change liftAngle (x₀ 1) (Circle.exp (2 * Real.pi * x 1) : ℂ) = x 1
      rw [circle_eq_one_mul (Circle.exp (2 * Real.pi * x 1))]
      exact liftAngle_eq one_pos h1
    · rw [flatLift_two, norm_flatWrap_fst, flatHeight_flatRadius]
  right_inv' y hy := by
    obtain ⟨⟨hr1, hr2⟩, _, _⟩ := hy
    refine Prod.ext ?_ ?_
    · change (flatRadius (flatLift x₀ y 2) : ℂ) * Circle.exp (2 * Real.pi * flatLift x₀ y 0) = y.1
      rw [flatLift_two, flatLift_zero, flatRadius_flatHeight hr1 hr2]
      exact norm_mul_circleExp_liftAngle _ _
    · change Circle.exp (2 * Real.pi * flatLift x₀ y 1) = y.2
      rw [flatLift_one]
      exact circleExp_liftAngle _ _
  open_source := by
    have hc (j : Fin 3) : Continuous fun x : E3 => x j :=
      (PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin 3 => ℝ) j).continuous
    exact (isOpen_lt (continuous_const.mul ((hc 0).sub continuous_const)).abs
      continuous_const).inter
      (isOpen_lt (continuous_const.mul ((hc 1).sub continuous_const)).abs continuous_const)
  open_target := by
    have hn : Continuous fun y : ℂ × Circle => ‖y.1‖ := continuous_norm.comp continuous_fst
    exact ((isOpen_lt continuous_const hn).inter (isOpen_lt hn continuous_const)).inter
      ((Complex.isOpen_slitPlane.preimage (continuous_const.mul continuous_fst)).inter
        (Complex.isOpen_slitPlane.preimage
          (continuous_const.mul (continuous_subtype_val.comp continuous_snd))))
  contMDiffOn_toFun := contMDiff_flatWrap.contMDiffOn
  contMDiffOn_invFun y hy := (contMDiffAt_flatLift x₀ hy).contMDiffWithinAt

theorem mem_flatChart_source (x₀ : E3) : x₀ ∈ (flatChart x₀).source := by
  change |2 * Real.pi * (x₀ 0 - x₀ 0)| < Real.pi ∧ |2 * Real.pi * (x₀ 1 - x₀ 1)| < Real.pi
  simp [Real.pi_pos]

def flatQuotient : TorusTimesLine → ℂ × Circle :=
  Quotient.lift flatWrap fun a b h => by
    obtain ⟨γ, rfl⟩ := MulAction.mem_orbit_iff.1 (MulAction.orbitRel_apply.1 h)
    exact flatWrap_smul γ b

@[simp] theorem flatQuotient_mk (x : E3) : flatQuotient (Quotient.mk'' x) = flatWrap x :=
  rfl

theorem isLocalDiffeomorph_flatQuotient :
    IsLocalDiffeomorph (𝓡 3) (𝓘(ℝ, ℂ).prod (𝓡 1)) ∞ flatQuotient := by
  intro q
  obtain ⟨x, rfl⟩ := Quotient.mk''_surjective q
  obtain ⟨Ψ, hx, heq⟩ := isLocalDiffeomorph_orbitMk (𝓡 3) torusTranslations E3 x
  have hΨx : Ψ x = Quotient.mk'' x := (heq hx).symm
  refine ⟨Ψ.symm.trans (flatChart x), ⟨?_, ?_⟩, fun y hy => ?_⟩
  · rw [← hΨx]
    exact Ψ.toPartialEquiv.map_source hx
  · change Ψ.toPartialEquiv.symm (Quotient.mk'' x) ∈ (flatChart x).source
    rw [← hΨx, Ψ.toPartialEquiv.left_inv hx]
    exact mem_flatChart_source x
  · have hy1 : y ∈ Ψ.toPartialEquiv.target := hy.1
    have hy' : y = Quotient.mk'' (Ψ.toPartialEquiv.symm y) := by
      rw [heq (Ψ.toPartialEquiv.map_target hy1), Ψ.toPartialEquiv.right_inv hy1]
    change flatQuotient y = flatWrap (Ψ.toPartialEquiv.symm y)
    conv_lhs => rw [hy']
    rfl

theorem injective_flatQuotient : Function.Injective flatQuotient := by
  rintro ⟨x⟩ ⟨y⟩ h
  change flatWrap x = flatWrap y at h
  have hn := congrArg (fun p : ℂ × Circle => ‖p.1‖) h
  simp only [norm_flatWrap_fst] at hn
  have h2 : x 2 = y 2 := by rw [← flatHeight_flatRadius (x 2), hn, flatHeight_flatRadius]
  simp only [flatWrap, Prod.mk.injEq] at h
  obtain ⟨h0, h1⟩ := h
  rw [h2] at h0
  have hρ : ((flatRadius (y 2) : ℝ) : ℂ) ≠ 0 := by
    have := (flatRadius_mem (y 2)).1
    exact_mod_cast (by linarith : flatRadius (y 2) ≠ 0)
  obtain ⟨m, hm⟩ := Circle.exp_eq_exp.1 (Circle.coe_inj.1 (mul_left_cancel₀ hρ h0))
  obtain ⟨n, hn'⟩ := Circle.exp_eq_exp.1 h1
  have hpi : (2 * Real.pi) ≠ 0 := by positivity
  have hx0 : x 0 = y 0 + m := mul_left_cancel₀ hpi (by rw [hm]; ring)
  have hx1 : x 1 = y 1 + n := mul_left_cancel₀ hpi (by rw [hn']; ring)
  apply Quot.sound
  refine MulAction.orbitRel_apply.2 (MulAction.mem_orbit_iff.2 ⟨⟨⟨m + m, n⟩, ⟨m, rfl⟩⟩, ?_⟩)
  obtain ⟨g0, g1, g2⟩ := torusTranslations_smul_apply ⟨⟨m + m, n⟩, ⟨m, rfl⟩⟩ y
  refine euclidean3_ext ?_ ?_ ?_
  · rw [g0, hx0]
    push_cast
    ring
  · rw [g1, hx1]
  · rw [g2, h2]

theorem range_flatQuotient :
    range flatQuotient = {y : ℂ × Circle | 1 / 2 < ‖y.1‖ ∧ ‖y.1‖ < 3} := by
  ext y
  constructor
  · rintro ⟨q, rfl⟩
    obtain ⟨x, rfl⟩ := Quotient.mk''_surjective q
    change 1 / 2 < ‖(flatWrap x).1‖ ∧ ‖(flatWrap x).1‖ < 3
    rw [norm_flatWrap_fst]
    exact flatRadius_mem _
  · rintro ⟨h1, h2⟩
    refine ⟨Quotient.mk'' (flatLift 0 y), Prod.ext ?_ ?_⟩
    · change (flatRadius (flatLift 0 y 2) : ℂ) * Circle.exp (2 * Real.pi * flatLift 0 y 0) = y.1
      rw [flatLift_two, flatLift_zero, flatRadius_flatHeight h1 h2]
      exact norm_mul_circleExp_liftAngle _ _
    · change Circle.exp (2 * Real.pi * flatLift 0 y 1) = y.2
      rw [flatLift_one]
      exact circleExp_liftAngle _ _

def flatImage : TopologicalSpace.Opens (ℂ × Circle) := isLocalDiffeomorph_flatQuotient.image

theorem mem_flatImage {y : ℂ × Circle} : y ∈ flatImage ↔ 1 / 2 < ‖y.1‖ ∧ ‖y.1‖ < 3 := by
  change y ∈ isLocalDiffeomorph_flatQuotient.image.1 ↔ _
  rw [IsLocalDiffeomorph.image_coe, range_flatQuotient]
  rfl

def flatDiffeo : TorusTimesLine ≃ₘ⟮𝓡 3, 𝓘(ℝ, ℂ).prod (𝓡 1)⟯ flatImage :=
  DifferentialGeometry.Topology.Manifold.diffeomorphOntoImage flatQuotient
    isLocalDiffeomorph_flatQuotient injective_flatQuotient

theorem flatDiffeo_apply (q : TorusTimesLine) : (flatDiffeo q : ℂ × Circle) = flatQuotient q :=
  rfl

theorem planarFunction_two_neg_iff (z : ℂ) :
    planarFunction 2 z < 0 ↔ 1 / 2 < ‖z‖ ∧ ‖z‖ < 3 := by
  rw [planarFunction_two]
  have h0 := norm_nonneg z
  constructor
  · intro h
    rcases mul_neg_iff.1 h with ⟨ha, hb⟩ | ⟨ha, hb⟩
    · nlinarith
    · constructor <;> nlinarith
  · rintro ⟨h1, h2⟩
    exact mul_neg_of_neg_of_pos (by nlinarith) (by nlinarith)

theorem isInteriorPoint_productSet_two_iff (x : productSet.{u} 2) :
    (𝓡∂ 3).IsInteriorPoint x ↔ 1 / 2 < ‖x.val.1.down‖ ∧ ‖x.val.1.down‖ < 3 := by
  rw [ModelWithCorners.isInteriorPoint_iff_not_isBoundaryPoint, productSet_isBoundaryPoint_iff,
    ← planarFunction_two_neg_iff]
  exact ⟨fun h => lt_of_le_of_ne (x.2 : planarFunction 2 x.val.1.down ≤ 0) h, fun h => h.ne⟩

def annulusInteriorEquiv :
    flatImage ≃ₘ⟮𝓘(ℝ, ℂ).prod (𝓡 1), annulusCircleCarrier.{u}.model⟯
      annulusCircleCarrier.{u}.pieceInterior ⊤ where
  toFun y := ⟨⟨(ULift.up y.1.1, y.1.2),
      ((planarFunction_two_neg_iff y.1.1).2 (mem_flatImage.1 y.2)).le⟩,
    ⟨trivial, (isInteriorPoint_productSet_two_iff ⟨(ULift.up y.1.1, y.1.2),
      ((planarFunction_two_neg_iff y.1.1).2 (mem_flatImage.1 y.2)).le⟩).2 (mem_flatImage.1 y.2)⟩⟩
  invFun x := ⟨(x.1.1.1.down, x.1.1.2),
    mem_flatImage.2 ((isInteriorPoint_productSet_two_iff x.1).1 x.2.2)⟩
  left_inv _ := rfl
  right_inv _ := rfl
  contMDiff_toFun := by
    refine (ContMDiff.subtypeVal_comp_iff (annulusCircleCarrier.{u}.pieceInterior ⊤) _).1 ?_
    refine ((productAtlas.{u} 2).contMDiff_iff_subtype_val _).2 ?_
    exact (contMDiff_planeLift_up.comp (contMDiff_fst.comp contMDiff_subtype_val)).prodMk
      (contMDiff_snd.comp contMDiff_subtype_val)
  contMDiff_invFun := by
    refine (ContMDiff.subtypeVal_comp_iff flatImage _).1 ?_
    have hval : ContMDiff annulusCircleCarrier.{u}.model (𝓘(ℝ, ℂ).prod (𝓡 1)) ∞
        (fun x : annulusCircleCarrier.{u}.Carrier =>
          @Subtype.val (PlaneLift.{u} × Circle) (· ∈ productSet.{u} 2) x) :=
      (productAtlas.{u} 2).contMDiff_subtype_val
    have hv := hval.comp (contMDiff_subtype_val (U := annulusCircleCarrier.{u}.pieceInterior ⊤))
    exact (contMDiff_planeLift_down.comp (contMDiff_fst.comp hv)).prodMk (contMDiff_snd.comp hv)

def annulusCircleInteriorDiffeo :
    annulusCircleCarrier.{u}.pieceInterior ⊤ ≃ₘ⟮annulusCircleCarrier.{u}.model, 𝓡 3⟯
      TorusTimesLine :=
  annulusInteriorEquiv.symm.trans flatDiffeo.symm

def interiorGeometryOfDiffeomorph {N : Type*} [TopologicalSpace N] [ChartedSpace E3 N]
    [IsManifold (𝓡 3) ∞ N] [T2Space N] [SigmaCompactSpace N] (G : GeometricStructure (𝓡 3) N)
    (C : CompactCarrier.{u}) (U : TopologicalSpace.Opens C.Carrier)
    (f : C.pieceInterior U ≃ₘ⟮C.model, 𝓡 3⟯ N) : C.InteriorGeometry U := by
  letI := DifferentialGeometry.Manifold.interiorChartedSpace C.model ∞ (M := C.pieceInterior U)
  letI := DifferentialGeometry.Manifold.interiorIsManifold C.model ∞ (M := C.pieceInterior U)
  exact G.pullback ((DifferentialGeometry.Manifold.interiorAtlasDiffeomorph C.model ∞).symm.trans f)

theorem interiorGeometryOfDiffeomorph_model {N : Type*} [TopologicalSpace N]
    [ChartedSpace E3 N] [IsManifold (𝓡 3) ∞ N] [T2Space N] [SigmaCompactSpace N]
    (G : GeometricStructure (𝓡 3) N) (C : CompactCarrier.{u})
    (U : TopologicalSpace.Opens C.Carrier) (f : C.pieceInterior U ≃ₘ⟮C.model, 𝓡 3⟯ N) :
    letI := DifferentialGeometry.Manifold.interiorChartedSpace C.model ∞ (M := C.pieceInterior U)
    letI := DifferentialGeometry.Manifold.interiorIsManifold C.model ∞ (M := C.pieceInterior U)
    (interiorGeometryOfDiffeomorph G C U f).model = G.model :=
  rfl

def annulusCircleBlock_interiorGeometry :
    annulusCircleBlock.{u}.presentation.cutCarrier.InteriorGeometry
      (annulusCircleBlock.{u}.presentation.components.piece (annulusCircleBlock.{u}.piece none)) :=
  interiorGeometryOfDiffeomorph torusTimesLineGeometry annulusCircleCarrier.{u} ⊤
    annulusCircleInteriorDiffeo

theorem annulusCircleBlock_interiorGeometry_model :
    letI := DifferentialGeometry.Manifold.interiorChartedSpace
      annulusCircleBlock.{u}.presentation.cutCarrier.model ∞
      (M := annulusCircleBlock.{u}.presentation.cutCarrier.pieceInterior
        (annulusCircleBlock.{u}.presentation.components.piece (annulusCircleBlock.{u}.piece none)))
    letI := DifferentialGeometry.Manifold.interiorIsManifold
      annulusCircleBlock.{u}.presentation.cutCarrier.model ∞
      (M := annulusCircleBlock.{u}.presentation.cutCarrier.pieceInterior
        (annulusCircleBlock.{u}.presentation.components.piece (annulusCircleBlock.{u}.piece none)))
    annulusCircleBlock_interiorGeometry.{u}.model = ThurstonModel.euclidean :=
  rfl

section PieceInterior

variable {C : CompactCarrier.{u}} {D : CompactCarrier.{v}} {U : TopologicalSpace.Opens C.Carrier}
  {V : TopologicalSpace.Opens D.Carrier}

def pieceInteriorCongrMap (Ψ : U ≃ₘ⟮C.model, D.model⟯ V) (x : C.pieceInterior U) :
    D.pieceInterior V :=
  ⟨(Ψ ⟨x.1, x.2.1⟩).1, (Ψ ⟨x.1, x.2.1⟩).2,
    ModelWithCorners.isInteriorPoint_iff_isInteriorPoint_val.mp
      (((Ψ.isLocalDiffeomorph _).isInteriorPoint_iff (by simp)).mp
        (ModelWithCorners.isInteriorPoint_iff_isInteriorPoint_val.mpr x.2.2))⟩

theorem pieceInteriorCongrMap_val (Ψ : U ≃ₘ⟮C.model, D.model⟯ V) (x : C.pieceInterior U) :
    (pieceInteriorCongrMap Ψ x : D.Carrier) = (Ψ ⟨x.1, x.2.1⟩ : D.Carrier) :=
  rfl

theorem contMDiff_pieceInteriorCongrMap (Ψ : U ≃ₘ⟮C.model, D.model⟯ V) :
    ContMDiff C.model D.model ∞ (pieceInteriorCongrMap Ψ) := by
  refine (ContMDiff.subtypeVal_comp_iff (D.pieceInterior V) _).1 ?_
  have h := contMDiff_subtype_val.comp
    (Ψ.contMDiff.comp (contMDiff_inclusion (inf_le_left : C.pieceInterior U ≤ U)))
  exact h

def pieceInteriorCongr (Ψ : U ≃ₘ⟮C.model, D.model⟯ V) :
    C.pieceInterior U ≃ₘ⟮C.model, D.model⟯ D.pieceInterior V where
  toFun := pieceInteriorCongrMap Ψ
  invFun := pieceInteriorCongrMap Ψ.symm
  left_inv x := Subtype.ext (by
    change ((Ψ.symm (Ψ ⟨x.1, x.2.1⟩)) : C.Carrier) = x.1
    rw [Ψ.symm_apply_apply])
  right_inv y := Subtype.ext (by
    change ((Ψ (Ψ.symm ⟨y.1, y.2.1⟩)) : D.Carrier) = y.1
    rw [Ψ.apply_symm_apply])
  contMDiff_toFun := contMDiff_pieceInteriorCongrMap Ψ
  contMDiff_invFun := contMDiff_pieceInteriorCongrMap Ψ.symm

end PieceInterior

def PlanarBase.diffeomorph {k : ℕ} (P : PlanarBase.{u} k) (Q : PlanarBase.{v} k) :
    P.surface.Carrier ≃ₘ⟮SurfaceModel.model P.surface.kind, SurfaceModel.model Q.surface.kind⟯
      Q.surface.Carrier :=
  P.isSmoothEmbedding.diffeomorphOfRangeEq Q.isSmoothEmbedding
    (P.range_embedding.trans Q.range_embedding.symm)

theorem PlanarBase.embedding_diffeomorph {k : ℕ} (P : PlanarBase.{u} k) (Q : PlanarBase.{v} k)
    (x : P.surface.Carrier) : Q.embedding (P.diffeomorph Q x) = P.embedding x :=
  P.isSmoothEmbedding.comp_diffeomorphOfRangeEq Q.isSmoothEmbedding _ x

def ProductFibredPiece.pieceDiffeomorph {W : CompactCarrier.{u}} {T : TorusPresentation.{u} W}
    {i : Fin T.components.count} {W' : CompactCarrier.{v}} {T' : TorusPresentation.{v} W'}
    {i' : Fin T'.components.count} {k : ℕ} (P : ProductFibredPiece T i k)
    (Q : ProductFibredPiece T' i' k) :
    T.components.piece i ≃ₘ⟮T.cutCarrier.model, T'.cutCarrier.model⟯ T'.components.piece i' :=
  P.trivialization.symm.trans
    (((P.base.diffeomorph Q.base).prodCongr (Diffeomorph.refl (𝓡 1) Circle ∞)).trans
      Q.trivialization)

def T2Interval.interiorDiffeo {W : CompactCarrier.{u}} (B : T2Interval W) :
    B.presentation.cutCarrier.pieceInterior (B.presentation.components.piece (B.piece none))
      ≃ₘ⟮B.presentation.cutCarrier.model, 𝓡 3⟯ TorusTimesLine :=
  (pieceInteriorCongr (B.product.pieceDiffeomorph annulusCirclePiece.{u})).trans
    annulusCircleInteriorDiffeo

def T2Interval.interiorGeometry {W : CompactCarrier.{u}} (B : T2Interval W) :
    B.presentation.cutCarrier.InteriorGeometry (B.presentation.components.piece (B.piece none)) :=
  interiorGeometryOfDiffeomorph torusTimesLineGeometry _ _ B.interiorDiffeo

theorem T2Interval.interiorGeometry_model {W : CompactCarrier.{u}} (B : T2Interval W) :
    letI := DifferentialGeometry.Manifold.interiorChartedSpace B.presentation.cutCarrier.model ∞
      (M := B.presentation.cutCarrier.pieceInterior
        (B.presentation.components.piece (B.piece none)))
    letI := DifferentialGeometry.Manifold.interiorIsManifold B.presentation.cutCarrier.model ∞
      (M := B.presentation.cutCarrier.pieceInterior
        (B.presentation.components.piece (B.piece none)))
    B.interiorGeometry.model = ThurstonModel.euclidean :=
  rfl

end GC.Seifert
