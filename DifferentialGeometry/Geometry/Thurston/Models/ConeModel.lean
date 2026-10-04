import DifferentialGeometry.Geometry.Thurston.Descent
import DifferentialGeometry.Geometry.Thurston.Models.ConnectionMetrics
import DifferentialGeometry.Geometry.Thurston.Models.HomogeneousCompleteness

/-!
# Fibred solid tori: screw quotients of rotationally symmetric connection metrics

On `ModelCoordinates = ℝ² × ℝ`, a `RadialProfile` `(h, k, m)` gives the metric
`h(r²) (dx² + dy²) + k(r²) (x dx + y dy)² + (dz + m(r²) (x dy - y dx))²` (`RadialProfile.metric`),
positive definite as soon as `h > 0` and `h + k r² > 0`. `ScrewGroup θ ℓ` is `ℤ` acting by
`n ↦ (rotation by n θ about the z-axis, translation by n ℓ)`: affine isometries of `E³`, free and
properly discontinuous for `ℓ ≠ 0`, and isometries of every profile metric
(`RadialProfile.metric_invariant`), so model atlases descend
(`RadialProfile.hasThurstonAtlas_quotient`, via `HasThurstonAtlas.quotient`).

`ConnectionModel.coneProfile` realises the six normal forms of `ConnectionMetrics.lean` by
rotationally symmetric charts (`ConnectionModel.connectionAtlas_coneProfile`):
* `flatProfile l`, gauge `-(l/2)(x dy - y dx)`: the shear `(x, y, z) ↦ (x, y, z - l x y / 2)`
  (`shearChart`) identifies it with `flat`, `l • nil` (`E³` at `l = 0`, `Nil` at `l = 1`);
* `roundProfile R l`, the stereographic sphere of radius `R` with `l (x dy - y dx) / (1 + r²)`:
  literally `round R`, `l • hopf` (`S² × ℝ` at `(1, 0)`, `S³` at `(1/2, 1)`);
* `hyperbolicProfile l`, the hyperboloid chart `(x, y) ↦ (x, y, √(1 + r²))` of `H²` with
  `l (x dy - y dx) / (1 + √(1 + r²))`: the global diffeomorphism `hyperboloidChart l`,
  `(x, y, z) ↦ (x e^{-y}, x² e^{-y} / 2 + sinh y, z + 2 l arctan (x / (e^y + 1)))`, identifies it
  with `hyperbolic`, `l • universalSL2` (`H² × ℝ` at `l = 0`, `SL₂~` at `l = 1`).

`FibredSolidTorus p q` is the quotient by `FibredSolidTorusGroup p q` (`θ = 2πq/p`, `ℓ = 1/p`), the
open fibred solid torus `V(p, q)`. The z-axis is invariant (`ScrewGroup.smul_fibreShift`) and gives
the core fibre; all stabilisers are trivial, so the quotient is a smooth manifold at the core
(no orbifold point). `fibredSolidTorusAtlas m p q` is its model atlas for each of the six models.
When `m.baseCurvature ≤ 0` the charts are global isometries onto complete models, so the metric is
complete (`ConnectionModel.coneProfile_complete`) and `fibredSolidTorusGeometry` is a geometric
structure; for `S² × ℝ` and `S³` the stereographic base omits a point and only the atlas is given.
Coprimality of `p` and `q` is not needed here.
-/

set_option autoImplicit false

noncomputable section
open DifferentialGeometry Bundle Manifold
open scoped Manifold ContDiff

namespace GC.Geometry

private abbrev coord (i : Fin 3) : ModelCoordinates →L[ℝ] ℝ :=
  PiLp.proj 2 (fun _ : Fin 3 => ℝ) i

def planeDot (v w : ModelCoordinates) : ℝ := v 0 * w 0 + v 1 * w 1

def planeCross (v w : ModelCoordinates) : ℝ := v 0 * w 1 - v 1 * w 0

theorem planeDot_comm (v w : ModelCoordinates) : planeDot v w = planeDot w v := by
  unfold planeDot; ring

theorem planeDot_self_nonneg (v : ModelCoordinates) : 0 ≤ planeDot v v :=
  add_nonneg (mul_self_nonneg _) (mul_self_nonneg _)

theorem planeDot_sq_add_planeCross_sq (p v : ModelCoordinates) :
    planeDot p v ^ 2 + planeCross p v ^ 2 = planeDot p p * planeDot v v := by
  unfold planeDot planeCross; ring

structure RadialProfile where
  base : ℝ → ℝ
  radial : ℝ → ℝ
  twist : ℝ → ℝ
  contDiffOn_base : ContDiffOn ℝ ∞ base (Set.Ioi (-1))
  contDiffOn_radial : ContDiffOn ℝ ∞ radial (Set.Ioi (-1))
  contDiffOn_twist : ContDiffOn ℝ ∞ twist (Set.Ioi (-1))
  base_pos : ∀ s, 0 ≤ s → 0 < base s
  base_add_radial_pos : ∀ s, 0 ≤ s → 0 < base s + radial s * s

namespace RadialProfile

variable (P : RadialProfile)

def fibre (p v : ModelCoordinates) : ℝ := v 2 + P.twist (planeDot p p) * planeCross p v

def inner (p v w : ModelCoordinates) : ℝ :=
  P.base (planeDot p p) * planeDot v w +
    P.radial (planeDot p p) * (planeDot p v * planeDot p w) + P.fibre p v * P.fibre p w

theorem inner_symm (p v w : ModelCoordinates) : P.inner p v w = P.inner p w v := by
  unfold inner; rw [planeDot_comm v w]; ring

theorem inner_pos (p v : ModelCoordinates) (hv : v ≠ 0) : 0 < P.inner p v v := by
  have hs := planeDot_self_nonneg p
  have hb := P.base_pos _ hs
  have hbr := P.base_add_radial_pos _ hs
  have hL := planeDot_sq_add_planeCross_sq p v
  have hf := sq_nonneg (P.fibre p v)
  have hc := sq_nonneg (planeCross p v)
  unfold inner
  rcases (planeDot_self_nonneg v).lt_or_eq with hvv | hvv
  · rcases le_or_gt 0 (P.radial (planeDot p p)) with hr | hr
    · have := mul_nonneg hr (sq_nonneg (planeDot p v))
      nlinarith [mul_pos hb hvv]
    · have h1 : P.radial (planeDot p p) * planeDot p v ^ 2 ≥
          P.radial (planeDot p p) * (planeDot p p * planeDot v v) := by
        rw [← hL]; nlinarith
      nlinarith [mul_pos hbr hvv]
  · have h0 : v 0 = 0 := by unfold planeDot at hvv; nlinarith [sq_nonneg (v 0), sq_nonneg (v 1)]
    have h1 : v 1 = 0 := by unfold planeDot at hvv; nlinarith [sq_nonneg (v 0), sq_nonneg (v 1)]
    have h2 : v 2 ≠ 0 := by
      intro h2
      apply hv
      ext i
      fin_cases i <;> simp [h0, h1, h2]
    simp only [fibre, planeDot, planeCross, h0, h1]
    have := pow_pos (abs_pos.mpr h2) 2
    rw [sq_abs] at this
    nlinarith

def dotForm (p : ModelCoordinates) : ModelCoordinates →L[ℝ] ℝ := p 0 • coord 0 + p 1 • coord 1

def fibreForm (p : ModelCoordinates) : ModelCoordinates →L[ℝ] ℝ :=
  coord 2 + P.twist (planeDot p p) • (p 0 • coord 1 - p 1 • coord 0)

def planeForm : ModelCoordinates →L[ℝ] ModelCoordinates →L[ℝ] ℝ :=
  (coord 0).smulRight (coord 0) + (coord 1).smulRight (coord 1)

def bilinear (p : ModelCoordinates) : ModelCoordinates →L[ℝ] ModelCoordinates →L[ℝ] ℝ :=
  let B₀ : ModelCoordinates →L[ℝ] ModelCoordinates →L[ℝ] ℝ := P.base (planeDot p p) • planeForm
  let B₁ : ModelCoordinates →L[ℝ] ModelCoordinates →L[ℝ] ℝ :=
    P.radial (planeDot p p) • (dotForm p).smulRight (dotForm p)
  let B₂ : ModelCoordinates →L[ℝ] ModelCoordinates →L[ℝ] ℝ :=
    (P.fibreForm p).smulRight (P.fibreForm p)
  B₀ + B₁ + B₂

theorem bilinear_apply (p v w : ModelCoordinates) : P.bilinear p v w = P.inner p v w := by
  simp only [bilinear, planeForm, dotForm, fibreForm, add_apply,
    smul_apply, ContinuousLinearMap.smulRight_apply,
    sub_apply, PiLp.proj_apply, smul_eq_mul]
  unfold inner fibre planeDot planeCross
  ring

theorem contDiff_comp_planeDot {f : ℝ → ℝ} (hf : ContDiffOn ℝ ∞ f (Set.Ioi (-1))) :
    ContDiff ℝ ∞ fun p : ModelCoordinates => f (planeDot p p) := by
  have hc (j : Fin 3) : ContDiff ℝ ∞ (fun q : ModelCoordinates => q j) := (coord j).contDiff
  refine hf.comp_contDiff (f := fun p : ModelCoordinates => planeDot p p)
    (by unfold planeDot; fun_prop) fun p => ?_
  have := planeDot_self_nonneg p
  change (-1 : ℝ) < _
  linarith

theorem contDiff_bilinear : ContDiff ℝ ∞ P.bilinear := by
  have hc (j : Fin 3) : ContDiff ℝ ∞ (fun q : ModelCoordinates => q j) := (coord j).contDiff
  have hb := contDiff_comp_planeDot P.contDiffOn_base
  have hr := contDiff_comp_planeDot P.contDiffOn_radial
  have ht := contDiff_comp_planeDot P.contDiffOn_twist
  have hd : ContDiff ℝ ∞ dotForm := by unfold dotForm; fun_prop
  have hf : ContDiff ℝ ∞ P.fibreForm := by unfold fibreForm; fun_prop
  unfold bilinear
  exact ((hb.smul contDiff_const).add (hr.smul (hd.smulRight hd))).add (hf.smulRight hf)

set_option backward.isDefEq.respectTransparency false in
def metric : SmoothRiemannianMetric (𝓡 3) ModelCoordinates where
  inner := P.bilinear
  symm p v w :=
    (P.bilinear_apply p v w).trans ((P.inner_symm p v w).trans (P.bilinear_apply p w v).symm)
  pos p v hv := (P.bilinear_apply p v v).symm ▸ P.inner_pos p v hv
  isVonNBounded p := DifferentialGeometry.Geometry.posDef_isVonNBounded
    (P.bilinear p) (fun v hv => (P.bilinear_apply p v v).symm ▸ P.inner_pos p v hv)
  contMDiff := by
    intro x
    rw [contMDiffAt_section]
    convert! P.contDiff_bilinear.contMDiff.contMDiffAt using 1
    ext p v w
    simp [hom_trivializationAt_apply, ContinuousLinearMap.inCoordinates, TangentSpace]

@[simp] theorem metric_inner (p v w : ModelCoordinates) :
    P.metric.inner p v w = P.inner p v w :=
  P.bilinear_apply p v w

end RadialProfile

def planeRotationEquiv (t : ℝ) : ModelCoordinates ≃ₗ[ℝ] ModelCoordinates where
  toFun v := !₂[Real.cos t * v 0 - Real.sin t * v 1, Real.sin t * v 0 + Real.cos t * v 1, v 2]
  invFun v := !₂[Real.cos t * v 0 + Real.sin t * v 1, Real.cos t * v 1 - Real.sin t * v 0, v 2]
  map_add' v w := by ext i; fin_cases i <;> simp <;> ring
  map_smul' c v := by ext i; fin_cases i <;> simp <;> ring
  left_inv v := by
    ext i; fin_cases i <;> simp
    · linear_combination v 0 * Real.cos_sq_add_sin_sq t
    · linear_combination v 1 * Real.cos_sq_add_sin_sq t
  right_inv v := by
    ext i; fin_cases i <;> simp
    · linear_combination v 0 * Real.cos_sq_add_sin_sq t
    · linear_combination v 1 * Real.cos_sq_add_sin_sq t

def planeRotation (t : ℝ) : ModelCoordinates ≃ₗᵢ[ℝ] ModelCoordinates :=
  { planeRotationEquiv t with
    norm_map' := fun v => by
      rw [EuclideanSpace.norm_eq, EuclideanSpace.norm_eq]
      congr 1
      simp [planeRotationEquiv, Fin.sum_univ_three]
      linear_combination (v 0 ^ 2 + v 1 ^ 2) * Real.cos_sq_add_sin_sq t }

@[simp] theorem planeRotation_apply_zero (t : ℝ) (v : ModelCoordinates) :
    planeRotation t v 0 = Real.cos t * v 0 - Real.sin t * v 1 := by
  simp [planeRotation, planeRotationEquiv]

@[simp] theorem planeRotation_apply_one (t : ℝ) (v : ModelCoordinates) :
    planeRotation t v 1 = Real.sin t * v 0 + Real.cos t * v 1 := by
  simp [planeRotation, planeRotationEquiv]

@[simp] theorem planeRotation_apply_two (t : ℝ) (v : ModelCoordinates) :
    planeRotation t v 2 = v 2 := by
  simp [planeRotation, planeRotationEquiv]

theorem planeDot_planeRotation (t : ℝ) (v w : ModelCoordinates) :
    planeDot (planeRotation t v) (planeRotation t w) = planeDot v w := by
  simp only [planeDot, planeRotation_apply_zero, planeRotation_apply_one]
  linear_combination (v 0 * w 0 + v 1 * w 1) * Real.cos_sq_add_sin_sq t

theorem planeCross_planeRotation (t : ℝ) (v w : ModelCoordinates) :
    planeCross (planeRotation t v) (planeRotation t w) = planeCross v w := by
  simp only [planeCross, planeRotation_apply_zero, planeRotation_apply_one]
  linear_combination (v 0 * w 1 - v 1 * w 0) * Real.cos_sq_add_sin_sq t

def fibreShift (s : ℝ) : ModelCoordinates := !₂[0, 0, s]

@[simp] theorem fibreShift_apply_zero (s : ℝ) : fibreShift s 0 = 0 := rfl

@[simp] theorem fibreShift_apply_one (s : ℝ) : fibreShift s 1 = 0 := rfl

@[simp] theorem fibreShift_apply_two (s : ℝ) : fibreShift s 2 = s := rfl

theorem planeDot_add_fibreShift_left (s : ℝ) (v w : ModelCoordinates) :
    planeDot (v + fibreShift s) w = planeDot v w := by
  simp [planeDot]

theorem planeDot_add_fibreShift_right (s : ℝ) (v w : ModelCoordinates) :
    planeDot v (w + fibreShift s) = planeDot v w := by
  simp [planeDot]

theorem planeCross_add_fibreShift_left (s : ℝ) (v w : ModelCoordinates) :
    planeCross (v + fibreShift s) w = planeCross v w := by
  simp [planeCross]

theorem RadialProfile.inner_rotation (P : RadialProfile) (t s : ℝ) (p v w : ModelCoordinates) :
    P.inner (planeRotation t p + fibreShift s) (planeRotation t v) (planeRotation t w) =
      P.inner p v w := by
  simp only [RadialProfile.inner, RadialProfile.fibre, planeDot_add_fibreShift_left,
    planeDot_add_fibreShift_right, planeCross_add_fibreShift_left, planeDot_planeRotation,
    planeCross_planeRotation,
    planeRotation_apply_two]

@[ext] structure ScrewGroup (θ ℓ : ℝ) where
  shift : ℤ

namespace ScrewGroup

variable {θ ℓ : ℝ}

instance : Mul (ScrewGroup θ ℓ) := ⟨fun a b => ⟨a.shift + b.shift⟩⟩

instance : One (ScrewGroup θ ℓ) := ⟨⟨0⟩⟩

instance : Inv (ScrewGroup θ ℓ) := ⟨fun a => ⟨-a.shift⟩⟩

@[simp] theorem mul_shift (a b : ScrewGroup θ ℓ) : (a * b).shift = a.shift + b.shift := rfl

@[simp] theorem one_shift : (1 : ScrewGroup θ ℓ).shift = 0 := rfl

@[simp] theorem inv_shift (a : ScrewGroup θ ℓ) : a⁻¹.shift = -a.shift := rfl

instance : Group (ScrewGroup θ ℓ) :=
  Group.ofLeftAxioms (fun a b c => by ext; simp [add_assoc]) (fun a => by ext; simp)
    (fun a => by ext; simp)

def linearPart (γ : ScrewGroup θ ℓ) : ModelCoordinates ≃ₗᵢ[ℝ] ModelCoordinates :=
  planeRotation (θ * γ.shift)

def translationPart (γ : ScrewGroup θ ℓ) : ModelCoordinates := fibreShift (ℓ * γ.shift)

instance : MulAction (ScrewGroup θ ℓ) ModelCoordinates where
  smul γ x := γ.linearPart x + γ.translationPart
  one_smul x := by
    change planeRotation (θ * ((0 : ℤ) : ℝ)) x + fibreShift (ℓ * ((0 : ℤ) : ℝ)) = x
    ext i; fin_cases i <;> simp
  mul_smul a b x := by
    change planeRotation (θ * ((a.shift + b.shift : ℤ) : ℝ)) x +
        fibreShift (ℓ * ((a.shift + b.shift : ℤ) : ℝ)) =
      planeRotation (θ * a.shift) (planeRotation (θ * b.shift) x + fibreShift (ℓ * b.shift)) +
        fibreShift (ℓ * a.shift)
    ext i; fin_cases i <;> simp [mul_add, Real.cos_add, Real.sin_add] <;> ring

theorem smul_def (γ : ScrewGroup θ ℓ) (x : ModelCoordinates) :
    γ • x = γ.linearPart x + γ.translationPart :=
  rfl

theorem smul_apply_two (γ : ScrewGroup θ ℓ) (x : ModelCoordinates) :
    (γ • x) 2 = x 2 + ℓ * γ.shift := by
  simp [smul_def, linearPart, translationPart]

theorem eq_one_of_smul_eq [Fact (ℓ ≠ 0)] (γ : ScrewGroup θ ℓ) (x : ModelCoordinates)
    (h : γ • x = x) : γ = 1 := by
  have h2 := congrArg (fun y : ModelCoordinates => y 2) h
  simp only [smul_apply_two, add_eq_left, mul_eq_zero, Int.cast_eq_zero] at h2
  exact ScrewGroup.ext (h2.resolve_left (Fact.out))

theorem finite_norm_translationPart_le [Fact (ℓ ≠ 0)] (R : ℝ) :
    {γ : ScrewGroup θ ℓ | ‖γ.translationPart‖ ≤ R}.Finite := by
  have hℓ : (0 : ℝ) < |ℓ| := abs_pos.mpr Fact.out
  let B : ℤ := ⌈R / |ℓ|⌉
  refine ((Set.finite_Icc (-B) B).image (fun n : ℤ => (⟨n⟩ : ScrewGroup θ ℓ))).subset ?_
  intro γ hγ
  have hR : ‖γ.translationPart‖ ≤ R := hγ
  have hn : ‖γ.translationPart‖ = |ℓ| * |(γ.shift : ℝ)| := by
    rw [EuclideanSpace.norm_eq, ← abs_mul, ← Real.sqrt_sq_eq_abs]
    congr 1
    simp [translationPart, Fin.sum_univ_three]
  rw [hn] at hR
  have hB : R / |ℓ| ≤ B := Int.le_ceil _
  have hle : |(γ.shift : ℝ)| ≤ R / |ℓ| := by
    rw [le_div_iff₀ hℓ]; linarith
  obtain ⟨h1, h2⟩ := abs_le.mp (hle.trans hB)
  refine ⟨γ.shift, ⟨?_, ?_⟩, rfl⟩
  · exact_mod_cast h1
  · exact_mod_cast h2

instance [Fact (ℓ ≠ 0)] : ProperlyDiscontinuousSMul (ScrewGroup θ ℓ) ModelCoordinates :=
  properlyDiscontinuousSMul_of_affine linearPart translationPart smul_def
    finite_norm_translationPart_le

instance : ContinuousConstSMul (ScrewGroup θ ℓ) ModelCoordinates :=
  continuousConstSMul_of_affine linearPart translationPart smul_def

instance : ContMDiffConstSMul (𝓡 3) ∞ (ScrewGroup θ ℓ) ModelCoordinates :=
  contMDiffConstSMul_of_affine linearPart translationPart smul_def

instance [Fact (ℓ ≠ 0)] : IsCancelSMul (ScrewGroup θ ℓ) ModelCoordinates :=
  isCancelSMul_of_free eq_one_of_smul_eq

end ScrewGroup

theorem RadialProfile.metric_invariant (P : RadialProfile) {θ ℓ : ℝ} [Fact (ℓ ≠ 0)]
    (γ : ScrewGroup θ ℓ) :
    Diffeomorph.pullbackMetric P.metric (MulAction.smulDiffeomorph (n := ∞) (𝓡 3) γ) =
      P.metric := by
  apply SmoothRiemannianMetric.ext_inner
  intro x v w
  have hfun : ((MulAction.smulDiffeomorph (n := ∞) (𝓡 3) γ : ModelCoordinates ≃ₘ⟮𝓡 3, 𝓡 3⟯
      ModelCoordinates) : ModelCoordinates → ModelCoordinates) =
      fun y => γ.linearPart y + γ.translationPart := rfl
  have hder : mfderiv (𝓡 3) (𝓡 3) (MulAction.smulDiffeomorph (n := ∞) (𝓡 3) γ) x =
      (γ.linearPart : ModelCoordinates →L[ℝ] ModelCoordinates) := by
    rw [mfderiv_eq_fderiv, hfun]
    exact (γ.linearPart.toContinuousLinearEquiv.hasFDerivAt.add_const _).fderiv
  rw [Diffeomorph.pullbackMetric_inner, hder, hfun]
  exact P.inner_rotation _ _ x v w

theorem RadialProfile.hasThurstonAtlas_quotient (P : RadialProfile) {k : ThurstonModel}
    (hP : HasThurstonAtlas P.metric k) (θ ℓ : ℝ) [Fact (ℓ ≠ 0)] :
    HasThurstonAtlas (quotientMetric (ScrewGroup θ ℓ) P.metric P.metric_invariant) k :=
  hP.quotient P.metric_invariant

private theorem hasFDerivAt_coord (p : ModelCoordinates) (i : Fin 3) :
    HasFDerivAt (fun q : ModelCoordinates => q i) (coord i) p :=
  PiLp.hasFDerivAt_apply 2 p i

private theorem fderiv_apply_coord {f : ModelCoordinates → ModelCoordinates} {p : ModelCoordinates}
    (hf : DifferentiableAt ℝ f p) (v : ModelCoordinates) (i : Fin 3) :
    fderiv ℝ f p v i = fderiv ℝ (fun q => f q i) p v := by
  have h := ((coord i).hasFDerivAt.comp p hf.hasFDerivAt).fderiv
  rw [show (fun q => f q i) = (coord i) ∘ f from rfl, h]
  rfl

def shearMap (l : ℝ) (p : ModelCoordinates) : ModelCoordinates :=
  !₂[p 0, p 1, p 2 - l / 2 * (p 0 * p 1)]

theorem contDiff_shearMap (l : ℝ) : ContDiff ℝ ∞ (shearMap l) := by
  have hc (j : Fin 3) : ContDiff ℝ ∞ (fun q : ModelCoordinates => q j) := (coord j).contDiff
  refine contDiff_euclidean.2 fun i => ?_
  fin_cases i
  · exact hc 0
  · exact hc 1
  · change ContDiff ℝ ∞ (fun q : ModelCoordinates => q 2 - l / 2 * (q 0 * q 1))
    fun_prop

theorem shearMap_shearMap (l : ℝ) (p : ModelCoordinates) : shearMap (-l) (shearMap l p) = p := by
  ext i
  fin_cases i <;> simp [shearMap]
  ring

def shearChart (l : ℝ) : PartialDiffeomorph (𝓡 3) (𝓡 3) ModelCoordinates ModelCoordinates ∞ where
  toFun := shearMap l
  invFun := shearMap (-l)
  source := Set.univ
  target := Set.univ
  map_source' _ _ := Set.mem_univ _
  map_target' _ _ := Set.mem_univ _
  left_inv' p _ := shearMap_shearMap l p
  right_inv' p _ := by simpa using shearMap_shearMap (-l) p
  open_source := isOpen_univ
  open_target := isOpen_univ
  contMDiffOn_toFun := (contDiff_shearMap l).contMDiff.contMDiffOn
  contMDiffOn_invFun := (contDiff_shearMap (-l)).contMDiff.contMDiffOn

theorem fderiv_shearMap (l : ℝ) (p v : ModelCoordinates) :
    fderiv ℝ (shearMap l) p v = !₂[v 0, v 1, v 2 - l / 2 * (v 0 * p 1 + p 0 * v 1)] := by
  have hd := (contDiff_shearMap l).differentiable (by decide) p
  have e0 : fderiv ℝ (fun q => shearMap l q 0) p v = v 0 := by
    rw [show (fun q => shearMap l q 0) = fun q => q 0 from funext fun q => by simp [shearMap],
      (hasFDerivAt_coord p 0).fderiv]
    simp
  have e1 : fderiv ℝ (fun q => shearMap l q 1) p v = v 1 := by
    rw [show (fun q => shearMap l q 1) = fun q => q 1 from funext fun q => by simp [shearMap],
      (hasFDerivAt_coord p 1).fderiv]
    simp
  have e2 : fderiv ℝ (fun q => shearMap l q 2) p v = v 2 - l / 2 * (v 0 * p 1 + p 0 * v 1) := by
    have h : HasFDerivAt (fun q : ModelCoordinates => q 2 - l / 2 * (q 0 * q 1)) _ p :=
      (hasFDerivAt_coord p 2).sub (((hasFDerivAt_coord p 0).mul
        (hasFDerivAt_coord p 1)).const_mul (l / 2))
    rw [show (fun q => shearMap l q 2) = fun q => q 2 - l / 2 * (q 0 * q 1) from
      funext fun q => by simp [shearMap], h.fderiv]
    simp
    ring
  ext i
  rw [fderiv_apply_coord hd]
  fin_cases i
  exacts [e0, e1, e2]

def hyperboloidMap (l : ℝ) (p : ModelCoordinates) : ModelCoordinates :=
  !₂[p 0 * Real.exp (-p 1),
    p 0 ^ 2 * Real.exp (-p 1) / 2 + (Real.exp (p 1) - Real.exp (-p 1)) / 2,
    p 2 + 2 * l * Real.arctan (p 0 / (Real.exp (p 1) + 1))]

theorem contDiff_hyperboloidMap (l : ℝ) : ContDiff ℝ ∞ (hyperboloidMap l) := by
  have hc (j : Fin 3) : ContDiff ℝ ∞ (fun q : ModelCoordinates => q j) := (coord j).contDiff
  refine contDiff_euclidean.2 fun i => ?_
  fin_cases i
  · change ContDiff ℝ ∞ (fun q : ModelCoordinates => q 0 * Real.exp (-q 1))
    fun_prop
  · change ContDiff ℝ ∞ (fun q : ModelCoordinates =>
      q 0 ^ 2 * Real.exp (-q 1) / 2 + (Real.exp (q 1) - Real.exp (-q 1)) / 2)
    fun_prop
  · change ContDiff ℝ ∞ (fun q : ModelCoordinates =>
      q 2 + 2 * l * Real.arctan (q 0 / (Real.exp (q 1) + 1)))
    have hd : ContDiff ℝ ∞ (fun q : ModelCoordinates => q 0 / (Real.exp (q 1) + 1)) :=
      ContDiff.div (hc 0) (by fun_prop) fun q => by positivity
    exact (hc 2).add (contDiff_const.mul hd.arctan)

def hyperboloidHeight (q : ModelCoordinates) : ℝ := √(1 + q 0 ^ 2 + q 1 ^ 2)

theorem hyperboloidHeight_sub_pos (q : ModelCoordinates) : 0 < hyperboloidHeight q - q 1 := by
  have h1 : |q 1| < hyperboloidHeight q := by
    rw [← Real.sqrt_sq_eq_abs]
    exact Real.sqrt_lt_sqrt (sq_nonneg _) (by nlinarith [sq_nonneg (q 0)])
  linarith [le_abs_self (q 1)]

def hyperboloidInv (l : ℝ) (q : ModelCoordinates) : ModelCoordinates :=
  !₂[q 0 / (hyperboloidHeight q - q 1), -Real.log (hyperboloidHeight q - q 1),
    q 2 - 2 * l * Real.arctan (q 0 / (1 + (hyperboloidHeight q - q 1)))]

theorem contDiff_hyperboloidHeight : ContDiff ℝ ∞ hyperboloidHeight := by
  have hc (j : Fin 3) : ContDiff ℝ ∞ (fun q : ModelCoordinates => q j) := (coord j).contDiff
  exact ContDiff.sqrt (by fun_prop) fun q => by positivity

theorem contDiff_hyperboloidInv (l : ℝ) : ContDiff ℝ ∞ (hyperboloidInv l) := by
  have hc (j : Fin 3) : ContDiff ℝ ∞ (fun q : ModelCoordinates => q j) := (coord j).contDiff
  have hd : ContDiff ℝ ∞ (fun q : ModelCoordinates => hyperboloidHeight q - q 1) :=
    contDiff_hyperboloidHeight.sub (hc 1)
  have hne (q : ModelCoordinates) : hyperboloidHeight q - q 1 ≠ 0 :=
    (hyperboloidHeight_sub_pos q).ne'
  refine contDiff_euclidean.2 fun i => ?_
  fin_cases i
  · exact (hc 0).div hd hne
  · exact (hd.log hne).neg
  · change ContDiff ℝ ∞ (fun q : ModelCoordinates =>
      q 2 - 2 * l * Real.arctan (q 0 / (1 + (hyperboloidHeight q - q 1))))
    have hd' : ContDiff ℝ ∞ (fun q : ModelCoordinates => q 0 / (1 + (hyperboloidHeight q - q 1))) :=
      (hc 0).div (contDiff_const.add hd) fun q => by
        have := hyperboloidHeight_sub_pos q; positivity
    exact (hc 2).sub (contDiff_const.mul hd'.arctan)

theorem hyperboloidHeight_hyperboloidMap (l : ℝ) (p : ModelCoordinates) :
    hyperboloidHeight (hyperboloidMap l p) =
      p 0 ^ 2 * Real.exp (-p 1) / 2 + (Real.exp (p 1) + Real.exp (-p 1)) / 2 := by
  have hu := Real.exp_pos (-p 1)
  have he := Real.exp_pos (p 1)
  rw [hyperboloidHeight, Real.sqrt_eq_iff_mul_self_eq (by positivity) (by positivity)]
  simp [hyperboloidMap, Real.exp_neg]
  field_simp
  ring

theorem hyperboloidInv_hyperboloidMap (l : ℝ) (p : ModelCoordinates) :
    hyperboloidInv l (hyperboloidMap l p) = p := by
  have hH := hyperboloidHeight_hyperboloidMap l p
  have he := Real.exp_pos (p 1)
  have hsub : hyperboloidHeight (hyperboloidMap l p) - hyperboloidMap l p 1 = Real.exp (-p 1) := by
    rw [hH]; simp [hyperboloidMap]; ring
  ext i; fin_cases i
  · simp only [hyperboloidInv, hsub]
    simp [hyperboloidMap]
  · simp only [hyperboloidInv, hsub]
    simp
  · simp only [hyperboloidInv, hsub]
    simp [hyperboloidMap, Real.exp_neg]
    field_simp
    ring_nf

theorem hyperboloidMap_hyperboloidInv (l : ℝ) (q : ModelCoordinates) :
    hyperboloidMap l (hyperboloidInv l q) = q := by
  have hd := hyperboloidHeight_sub_pos q
  have hsq : hyperboloidHeight q ^ 2 = 1 + q 0 ^ 2 + q 1 ^ 2 := Real.sq_sqrt (by positivity)
  have hexp : Real.exp (-hyperboloidInv l q 1) = hyperboloidHeight q - q 1 := by
    simp [hyperboloidInv, Real.exp_log hd]
  have hexp' : Real.exp (hyperboloidInv l q 1) = (hyperboloidHeight q - q 1)⁻¹ := by
    rw [← inv_inv (Real.exp _), ← Real.exp_neg, hexp]
  ext i; fin_cases i
  · simp only [hyperboloidMap, hexp]
    simp [hyperboloidInv]
    field_simp
  · simp only [hyperboloidMap, hexp, hexp']
    simp [hyperboloidInv]
    field_simp
    linear_combination (-1 : ℝ) * hsq
  · simp only [hyperboloidMap, hexp']
    simp [hyperboloidInv]
    field_simp
    ring_nf

theorem fderiv_hyperboloidMap (l : ℝ) (p v : ModelCoordinates) :
    fderiv ℝ (hyperboloidMap l) p v =
      !₂[Real.exp (-p 1) * v 0 - p 0 * Real.exp (-p 1) * v 1,
        p 0 * Real.exp (-p 1) * v 0 +
          (-(p 0 ^ 2 * Real.exp (-p 1)) + Real.exp (p 1) + Real.exp (-p 1)) / 2 * v 1,
        v 2 + 2 * l * ((v 0 * (Real.exp (p 1) + 1) - p 0 * Real.exp (p 1) * v 1) /
          ((Real.exp (p 1) + 1) ^ 2 + p 0 ^ 2))] := by
  have hd := (contDiff_hyperboloidMap l).differentiable (by decide) p
  have h1 := hasFDerivAt_coord p 1
  have hE : HasFDerivAt (fun q : ModelCoordinates => Real.exp (-q 1)) _ p := h1.neg.exp
  have hE' : HasFDerivAt (fun q : ModelCoordinates => Real.exp (q 1)) _ p := h1.exp
  have e0 : fderiv ℝ (fun q => hyperboloidMap l q 0) p v =
      Real.exp (-p 1) * v 0 - p 0 * Real.exp (-p 1) * v 1 := by
    have h : HasFDerivAt (fun q : ModelCoordinates => q 0 * Real.exp (-q 1)) _ p :=
      (hasFDerivAt_coord p 0).mul hE
    rw [show (fun q => hyperboloidMap l q 0) = fun q : ModelCoordinates =>
      q 0 * Real.exp (-q 1) from funext fun q => by simp [hyperboloidMap], h.fderiv]
    simp
    ring
  have e1 : fderiv ℝ (fun q => hyperboloidMap l q 1) p v =
      p 0 * Real.exp (-p 1) * v 0 +
        (-(p 0 ^ 2 * Real.exp (-p 1)) + Real.exp (p 1) + Real.exp (-p 1)) / 2 * v 1 := by
    have h : HasFDerivAt (fun q : ModelCoordinates => 2⁻¹ * (q 0 ^ 2 * Real.exp (-q 1)) +
        2⁻¹ * (Real.exp (q 1) - Real.exp (-q 1))) _ p :=
      ((((hasFDerivAt_coord p 0).pow 2).mul hE).const_mul 2⁻¹).add ((hE'.sub hE).const_mul 2⁻¹)
    rw [show (fun q => hyperboloidMap l q 1) = fun q : ModelCoordinates =>
      2⁻¹ * (q 0 ^ 2 * Real.exp (-q 1)) + 2⁻¹ * (Real.exp (q 1) - Real.exp (-q 1)) from
      funext fun q => by simp [hyperboloidMap]; ring, h.fderiv]
    simp
    ring
  have e2 : fderiv ℝ (fun q => hyperboloidMap l q 2) p v =
      v 2 + 2 * l * ((v 0 * (Real.exp (p 1) + 1) - p 0 * Real.exp (p 1) * v 1) /
        ((Real.exp (p 1) + 1) ^ 2 + p 0 ^ 2)) := by
    have hne : Real.exp (p 1) + 1 ≠ 0 := by positivity
    have hden : HasFDerivAt (fun q : ModelCoordinates => (Real.exp (q 1) + 1)⁻¹) _ p :=
      (hasDerivAt_inv hne).comp_hasFDerivAt p (hE'.add_const 1)
    have h : HasFDerivAt (fun q : ModelCoordinates =>
        q 2 + 2 * l * Real.arctan (q 0 * (Real.exp (q 1) + 1)⁻¹)) _ p :=
      (hasFDerivAt_coord p 2).add (((hasFDerivAt_coord p 0).mul hden).arctan.const_mul (2 * l))
    rw [show (fun q => hyperboloidMap l q 2) = fun q : ModelCoordinates =>
      q 2 + 2 * l * Real.arctan (q 0 * (Real.exp (q 1) + 1)⁻¹) from
      funext fun q => by simp [hyperboloidMap, div_eq_mul_inv], h.fderiv]
    simp
    field_simp
    ring
  ext i
  rw [fderiv_apply_coord hd]
  fin_cases i
  exacts [e0, e1, e2]

theorem zero_smul_fibreConnection (α : FibreConnection) : (0 : ℝ) • α = 0 := by
  ext x y <;> simp

theorem RadialProfile.connectionAtlas_of_chart (P : RadialProfile) {σ : BaseCoframe}
    {α : FibreConnection}
    (e : PartialDiffeomorph (𝓡 3) (𝓡 3) ModelCoordinates ModelCoordinates ∞)
    (he : ∀ x, x ∈ e.target)
    (h : ∀ p v w, P.inner (e p) (fderiv ℝ e p v) (fderiv ℝ e p w) = connectionInner σ α p v w) :
    ConnectionAtlas P.metric σ α := by
  intro x
  refine ⟨e, he x, fun p _ v w => ?_⟩
  rw [mfderiv_eq_fderiv]
  exact (P.metric_inner _ _ _).trans (h p v w)

def flatProfile (l : ℝ) : RadialProfile where
  base _ := 1
  radial _ := 0
  twist _ := -(l / 2)
  contDiffOn_base := contDiffOn_const
  contDiffOn_radial := contDiffOn_const
  contDiffOn_twist := contDiffOn_const
  base_pos _ _ := one_pos
  base_add_radial_pos _ _ := by norm_num

theorem flatProfile_inner_shearMap (l : ℝ) (p v w : ModelCoordinates) :
    (flatProfile l).inner (shearMap l p) (fderiv ℝ (shearMap l) p v)
      (fderiv ℝ (shearMap l) p w) = connectionInner .flat (l • .nil) p v w := by
  rw [fderiv_shearMap, fderiv_shearMap]
  simp [RadialProfile.inner, RadialProfile.fibre, flatProfile, planeDot, planeCross, shearMap,
    connectionInner, connectionCoframe, BaseCoframe.flat, FibreConnection.nil, Fin.sum_univ_three]
  ring

theorem flatProfile_connectionAtlas (l : ℝ) :
    ConnectionAtlas (flatProfile l).metric .flat (l • .nil) :=
  (flatProfile l).connectionAtlas_of_chart (shearChart l) (fun x => Set.mem_univ x)
    (flatProfile_inner_shearMap l)

def roundProfile (R l : ℝ) (hR : R ≠ 0) : RadialProfile where
  base s := (2 * R / (1 + s)) ^ 2
  radial _ := 0
  twist s := l / (1 + s)
  contDiffOn_base := by
    refine (contDiffOn_const.div (contDiffOn_const.add contDiffOn_id) fun s hs => ?_).pow 2
    have : (-1 : ℝ) < s := hs
    change 1 + s ≠ 0
    linarith
  contDiffOn_radial := contDiffOn_const
  contDiffOn_twist := by
    refine contDiffOn_const.div (contDiffOn_const.add contDiffOn_id) fun s hs => ?_
    have : (-1 : ℝ) < s := hs
    change 1 + s ≠ 0
    linarith
  base_pos s hs := by
    have : 0 < 1 + s := by linarith
    positivity
  base_add_radial_pos s hs := by
    have : 0 < 1 + s := by linarith
    simp only [zero_mul, add_zero]
    positivity

theorem roundProfile_inner (R l : ℝ) (hR : R ≠ 0) (p v w : ModelCoordinates) :
    (roundProfile R l hR).inner p v w = connectionInner (.round R) (l • .hopf) p v w := by
  have hD : 1 + p 0 ^ 2 + p 1 ^ 2 ≠ 0 := by positivity
  have hD' : 1 + (p 0 * p 0 + p 1 * p 1) ≠ 0 :=
    (add_pos_of_pos_of_nonneg one_pos (planeDot_self_nonneg p)).ne'
  simp [RadialProfile.inner, RadialProfile.fibre, roundProfile, planeDot, planeCross,
    connectionInner, connectionCoframe, BaseCoframe.round, FibreConnection.hopf,
    Fin.sum_univ_three]
  field_simp
  ring

theorem roundProfile_connectionAtlas (R l : ℝ) (hR : R ≠ 0) :
    ConnectionAtlas (roundProfile R l hR).metric (.round R) (l • .hopf) :=
  (roundProfile R l hR).connectionAtlas_of_chart
    (linearChart (ContinuousLinearEquiv.refl ℝ ModelCoordinates)) (fun x => Set.mem_univ x)
    fun p v w => by
      rw [show ((linearChart (ContinuousLinearEquiv.refl ℝ ModelCoordinates) :
          ModelCoordinates → ModelCoordinates)) = id from rfl, fderiv_id]
      exact roundProfile_inner R l hR p v w

def hyperbolicProfile (l : ℝ) : RadialProfile where
  base _ := 1
  radial s := -1 / (1 + s)
  twist s := l / (1 + √(1 + s))
  contDiffOn_base := contDiffOn_const
  contDiffOn_radial := by
    refine contDiffOn_const.div (contDiffOn_const.add contDiffOn_id) fun s hs => ?_
    have : (-1 : ℝ) < s := hs
    change 1 + s ≠ 0
    linarith
  contDiffOn_twist := by
    refine contDiffOn_const.div (contDiffOn_const.add
      ((contDiffOn_const.add contDiffOn_id).sqrt fun s hs => ?_)) fun s _ => ?_
    · have : (-1 : ℝ) < s := hs
      change 1 + s ≠ 0
      linarith
    · positivity
  base_pos _ _ := one_pos
  base_add_radial_pos s hs := by
    have : 0 < 1 + s := by linarith
    rw [show (1 : ℝ) + -1 / (1 + s) * s = 1 / (1 + s) by field_simp; ring]
    positivity

theorem hyperbolicProfile_inner_hyperboloidMap (l : ℝ) (p v w : ModelCoordinates) :
    (hyperbolicProfile l).inner (hyperboloidMap l p) (fderiv ℝ (hyperboloidMap l) p v)
      (fderiv ℝ (hyperboloidMap l) p w) =
        connectionInner .hyperbolic (l • .universalSL2) p v w := by
  have hc : 0 < p 0 ^ 2 * Real.exp (-p 1) / 2 + (Real.exp (p 1) + Real.exp (-p 1)) / 2 := by
    positivity
  have hH := hyperboloidHeight_hyperboloidMap l p
  have hsq : 1 + planeDot (hyperboloidMap l p) (hyperboloidMap l p) =
      (p 0 ^ 2 * Real.exp (-p 1) / 2 + (Real.exp (p 1) + Real.exp (-p 1)) / 2) ^ 2 := by
    rw [← hH, hyperboloidHeight, Real.sq_sqrt (by positivity)]
    unfold planeDot
    ring
  have hrad : (hyperbolicProfile l).radial
      (planeDot (hyperboloidMap l p) (hyperboloidMap l p)) =
      -1 / (p 0 ^ 2 * Real.exp (-p 1) / 2 + (Real.exp (p 1) + Real.exp (-p 1)) / 2) ^ 2 := by
    simp only [hyperbolicProfile, hsq]
  have htw : (hyperbolicProfile l).twist
      (planeDot (hyperboloidMap l p) (hyperboloidMap l p)) =
      l / (1 + (p 0 ^ 2 * Real.exp (-p 1) / 2 + (Real.exp (p 1) + Real.exp (-p 1)) / 2)) := by
    simp only [hyperbolicProfile, hsq, Real.sqrt_sq hc.le]
  simp only [RadialProfile.inner, RadialProfile.fibre, hrad, htw, fderiv_hyperboloidMap]
  have he := Real.exp_pos (p 1)
  have he1 : Real.exp (p 1) + 1 ≠ 0 := by positivity
  have he2 : (Real.exp (p 1) + 1) ^ 2 + p 0 ^ 2 ≠ 0 := by positivity
  simp [hyperbolicProfile, planeDot, planeCross, hyperboloidMap, connectionInner,
    connectionCoframe, BaseCoframe.hyperbolic, FibreConnection.universalSL2, Fin.sum_univ_three,
    Real.exp_neg]
  field_simp
  ring

def hyperboloidChart (l : ℝ) :
    PartialDiffeomorph (𝓡 3) (𝓡 3) ModelCoordinates ModelCoordinates ∞ where
  toFun := hyperboloidMap l
  invFun := hyperboloidInv l
  source := Set.univ
  target := Set.univ
  map_source' _ _ := Set.mem_univ _
  map_target' _ _ := Set.mem_univ _
  left_inv' p _ := hyperboloidInv_hyperboloidMap l p
  right_inv' q _ := hyperboloidMap_hyperboloidInv l q
  open_source := isOpen_univ
  open_target := isOpen_univ
  contMDiffOn_toFun := (contDiff_hyperboloidMap l).contMDiff.contMDiffOn
  contMDiffOn_invFun := (contDiff_hyperboloidInv l).contMDiff.contMDiffOn

theorem hyperbolicProfile_connectionAtlas (l : ℝ) :
    ConnectionAtlas (hyperbolicProfile l).metric .hyperbolic (l • .universalSL2) :=
  (hyperbolicProfile l).connectionAtlas_of_chart (hyperboloidChart l) (fun x => Set.mem_univ x)
    (hyperbolicProfile_inner_hyperboloidMap l)

namespace ConnectionModel

def coneProfile : ConnectionModel → RadialProfile
  | .euclidean => flatProfile 0
  | .sphericalProduct => roundProfile 1 0 one_ne_zero
  | .hyperbolicProduct => hyperbolicProfile 0
  | .nil => flatProfile 1
  | .universalSL2 => hyperbolicProfile 1
  | .spherical => roundProfile (1 / 2) 1 (by norm_num)

theorem connectionAtlas_coneProfile (m : ConnectionModel) :
    ConnectionAtlas m.coneProfile.metric m.base m.form := by
  cases m
  · have h := flatProfile_connectionAtlas 0
    rw [zero_smul_fibreConnection] at h
    exact h
  · have h := roundProfile_connectionAtlas 1 0 one_ne_zero
    rw [zero_smul_fibreConnection] at h
    exact h
  · have h := hyperbolicProfile_connectionAtlas 0
    rw [zero_smul_fibreConnection] at h
    exact h
  · have h := flatProfile_connectionAtlas 1
    rw [FibreConnection.one_smul'] at h
    exact h
  · have h := hyperbolicProfile_connectionAtlas 1
    rw [FibreConnection.one_smul'] at h
    exact h
  · have h := roundProfile_connectionAtlas (1 / 2) 1 (by norm_num)
    rw [FibreConnection.one_smul'] at h
    exact h

theorem hasThurstonAtlas_coneProfile (m : ConnectionModel) :
    HasThurstonAtlas m.coneProfile.metric m.thurston :=
  ConnectionAtlas.hasThurstonAtlas m m.connectionAtlas_coneProfile

theorem thurston_ne_hyperbolic (m : ConnectionModel) : m.thurston ≠ .hyperbolic := by
  cases m <;> decide

end ConnectionModel

abbrev FibredSolidTorusGroup (p : ℕ+) (q : ℤ) : Type :=
  ScrewGroup (2 * Real.pi * q / p) (1 / p)

instance (p : ℕ+) : Fact ((1 : ℝ) / (p : ℝ) ≠ 0) := ⟨by positivity⟩

abbrev FibredSolidTorus (p : ℕ+) (q : ℤ) : Type :=
  MulAction.orbitRel.Quotient (FibredSolidTorusGroup p q) ModelCoordinates

def fibredSolidTorusMetric (m : ConnectionModel) (p : ℕ+) (q : ℤ) :
    SmoothRiemannianMetric (𝓡 3) (FibredSolidTorus p q) :=
  quotientMetric (FibredSolidTorusGroup p q) m.coneProfile.metric m.coneProfile.metric_invariant

theorem fibredSolidTorusAtlas (m : ConnectionModel) (p : ℕ+) (q : ℤ) :
    HasThurstonAtlas (fibredSolidTorusMetric m p q) m.thurston :=
  m.hasThurstonAtlas_coneProfile.quotient m.coneProfile.metric_invariant

theorem ScrewGroup.smul_fibreShift {θ ℓ : ℝ} (γ : ScrewGroup θ ℓ) (t : ℝ) :
    γ • fibreShift t = fibreShift (t + ℓ * γ.shift) := by
  ext i
  fin_cases i <;> simp [ScrewGroup.smul_def, ScrewGroup.linearPart, ScrewGroup.translationPart]

theorem RadialProfile.metric_eq_pullbackMetricCross (P : RadialProfile)
    (h : SmoothRiemannianMetric (𝓡 3) ModelCoordinates)
    (Φ : ModelCoordinates ≃ₘ⟮𝓡 3, 𝓡 3⟯ ModelCoordinates)
    (hΦ : ∀ p v w, P.inner (Φ.symm p) (fderiv ℝ Φ.symm p v) (fderiv ℝ Φ.symm p w) =
      h.inner p v w) :
    P.metric = Diffeomorph.pullbackMetricCross h Φ := by
  apply SmoothRiemannianMetric.ext_inner
  intro x v w
  have hd : Differentiable ℝ Φ :=
    (contMDiff_iff_contDiff.1 Φ.contMDiff).differentiable (by decide)
  have hd' : Differentiable ℝ Φ.symm :=
    (contMDiff_iff_contDiff.1 Φ.symm.contMDiff).differentiable (by decide)
  have hid (u : ModelCoordinates) : fderiv ℝ Φ.symm (Φ x) (fderiv ℝ Φ x u) = u := by
    have hc := fderiv_comp x (hd' (Φ x)) (hd x)
    rw [show (Φ.symm ∘ Φ : ModelCoordinates → ModelCoordinates) = id from
      funext Φ.symm_apply_apply, fderiv_id] at hc
    exact (congrArg (fun T : ModelCoordinates →L[ℝ] ModelCoordinates => T u) hc).symm
  have key (a b : ModelCoordinates) :
      P.inner x a b = h.inner (Φ x) (fderiv ℝ Φ x a) (fderiv ℝ Φ x b) := by
    have k := hΦ (Φ x) (fderiv ℝ Φ x a) (fderiv ℝ Φ x b)
    rwa [hid, hid, Φ.symm_apply_apply] at k
  rw [Diffeomorph.pullbackMetricCross_inner, mfderiv_eq_fderiv]
  exact (P.metric_inner x v w).trans (key v w)

theorem RadialProfile.complete_of_chart (P : RadialProfile)
    {h : SmoothRiemannianMetric (𝓡 3) ModelCoordinates} (hh : RiemannianMetricComplete h)
    (Φ : ModelCoordinates ≃ₘ⟮𝓡 3, 𝓡 3⟯ ModelCoordinates)
    (hΦ : ∀ p v w, P.inner (Φ.symm p) (fderiv ℝ Φ.symm p v) (fderiv ℝ Φ.symm p w) =
      h.inner p v w) :
    RiemannianMetricComplete P.metric := by
  rw [P.metric_eq_pullbackMetricCross h Φ hΦ]
  exact Geometry.Metric.riemannianMetricComplete_pullbackMetricCross hh Φ

def shearDiffeo (l : ℝ) : ModelCoordinates ≃ₘ⟮𝓡 3, 𝓡 3⟯ ModelCoordinates where
  toFun := shearMap (-l)
  invFun := shearMap l
  left_inv p := by simpa using shearMap_shearMap (-l) p
  right_inv p := shearMap_shearMap l p
  contMDiff_toFun := (contDiff_shearMap (-l)).contMDiff
  contMDiff_invFun := (contDiff_shearMap l).contMDiff

def hyperboloidDiffeo (l : ℝ) : ModelCoordinates ≃ₘ⟮𝓡 3, 𝓡 3⟯ ModelCoordinates where
  toFun := hyperboloidInv l
  invFun := hyperboloidMap l
  left_inv q := hyperboloidMap_hyperboloidInv l q
  right_inv p := hyperboloidInv_hyperboloidMap l p
  contMDiff_toFun := (contDiff_hyperboloidInv l).contMDiff
  contMDiff_invFun := (contDiff_hyperboloidMap l).contMDiff

theorem connectionInner_eq_coordinateInner {σ : BaseCoframe} {α : FibreConnection}
    {k : CoordinateModel} (hk : ∀ p v, connectionCoframe σ α p v = coordinateCoframe k p v)
    (p v w : ModelCoordinates) : connectionInner σ α p v w = coordinateInner k p v w := by
  simp only [connectionInner, coordinateInner, hk]

namespace ConnectionModel

theorem coneProfile_complete (m : ConnectionModel) (hm : m.baseCurvature ≤ 0) :
    RiemannianMetricComplete m.coneProfile.metric := by
  cases m
  · refine (flatProfile 0).complete_of_chart euclideanModel_complete (shearDiffeo 0)
      fun p v w => ?_
    have h := flatProfile_inner_shearMap 0 p v w
    rw [zero_smul_fibreConnection, connectionInner_euclidean] at h
    exact h
  · norm_num [baseCurvature] at hm
  · refine (hyperbolicProfile 0).complete_of_chart
      (coordinateModelMetric_complete .hyperbolicProduct) (hyperboloidDiffeo 0) fun p v w => ?_
    have h := hyperbolicProfile_inner_hyperboloidMap 0 p v w
    rw [zero_smul_fibreConnection,
      connectionInner_eq_coordinateInner connectionCoframe_hyperbolicProduct,
      ← coordinateModelMetric_inner] at h
    exact h
  · refine (flatProfile 1).complete_of_chart (coordinateModelMetric_complete .nil)
      (shearDiffeo 1) fun p v w => ?_
    have h := flatProfile_inner_shearMap 1 p v w
    rw [FibreConnection.one_smul', connectionInner_eq_coordinateInner connectionCoframe_nil,
      ← coordinateModelMetric_inner] at h
    exact h
  · refine (hyperbolicProfile 1).complete_of_chart
      (coordinateModelMetric_complete .universalSL2) (hyperboloidDiffeo 1) fun p v w => ?_
    have h := hyperbolicProfile_inner_hyperboloidMap 1 p v w
    rw [FibreConnection.one_smul',
      connectionInner_eq_coordinateInner connectionCoframe_universalSL2,
      ← coordinateModelMetric_inner] at h
    exact h
  · norm_num [baseCurvature] at hm

def coneGeometry (m : ConnectionModel) (hm : m.baseCurvature ≤ 0) :
    GeometricStructure (𝓡 3) ModelCoordinates where
  model := m.thurston
  metric := m.coneProfile.metric
  complete := m.coneProfile_complete hm
  atlas := m.hasThurstonAtlas_coneProfile
  hyperbolic_finite_volume h := absurd h m.thurston_ne_hyperbolic

end ConnectionModel

def fibredSolidTorusGeometry (m : ConnectionModel) (hm : m.baseCurvature ≤ 0) (p : ℕ+) (q : ℤ) :
    GeometricStructure (𝓡 3) (FibredSolidTorus p q) :=
  (m.coneGeometry hm).quotient (FibredSolidTorusGroup p q) m.coneProfile.metric_invariant
    fun h => absurd h m.thurston_ne_hyperbolic

theorem fibredSolidTorusGeometry_model (m : ConnectionModel) (hm : m.baseCurvature ≤ 0)
    (p : ℕ+) (q : ℤ) : (fibredSolidTorusGeometry m hm p q).model = m.thurston :=
  rfl

theorem fibredSolidTorusGeometry_metric (m : ConnectionModel) (hm : m.baseCurvature ≤ 0)
    (p : ℕ+) (q : ℤ) :
    (fibredSolidTorusGeometry m hm p q).metric = fibredSolidTorusMetric m p q :=
  rfl

end GC.Geometry
