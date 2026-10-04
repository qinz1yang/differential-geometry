import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Sphere
import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Seifert.LensGroup
import DifferentialGeometry.Topology.Manifold.LocalDiffeomorph.Coordinates

/-!
# The lens space covering of the three-sphere

For `p ≥ 1` and `j : ZMod p` write `ζ^j = ZMod.toCircle j`. The twisted action
`lensTwist p e j : (z₁, z₂) ↦ (ζ^{e j} z₁, ζ^j z₂)` rotates the circle `z₂ / ‖z₂‖` of the solid
torus `‖z₁‖ ≤ ‖z₂‖` by `ζ^j` and its disc coordinate `z₁` by `ζ^{e j}`. A `TwistedCover p e W` is
a surjective local diffeomorphism from the standard three-sphere onto `W` whose fibres are exactly
the orbits of this action. Functions invariant under the action descend along it
(`TwistedCover.descend`), and maps of the form `x ↦ cover (Ψ x v)` with `v ^ p = f x` do not depend
on the chosen `p`-th root `v` and are smooth (`TwistedCover.contMDiffAt_cover_root`).

The lens space `L(p, q)` is the quotient of the sphere by `(z₁, z₂) ↦ (ζ^k z₁, ζ^{q k} z₂)`.
Writing `a p + b q = 1`, its quotient map is a twisted cover with exponent `b`
(`lensLeftCover`), and its composition with the coordinate swap is a twisted cover with exponent
`q` (`lensRightCover`).
-/

set_option autoImplicit false
noncomputable section
open Set Function Metric Filter
open DifferentialGeometry DifferentialGeometry.Topology GC.Endpoint
open scoped Manifold ContDiff Topology

namespace GC.GraphManifold

attribute [local instance] fact_finrank_euclideanSpace_four finrank_real_complex_fact'

abbrev LensSphere : Type := SphereCarrier.{0}

theorem norm_circle_mul (u : Circle) (z : ℂ) : ‖(u : ℂ) * z‖ = ‖z‖ := by
  rw [norm_mul, Circle.norm_coe, one_mul]

theorem unitOf_circle_mul (u : Circle) {z : ℂ} (hz : z ≠ 0) :
    unitOf ((u : ℂ) * z) = u * unitOf z := by
  apply Circle.ext
  rw [Circle.coe_mul, coe_unitOf (mul_ne_zero (Circle.coe_ne_zero u) hz), coe_unitOf hz,
    norm_circle_mul, Complex.real_smul, Complex.real_smul]
  ring

def circleRootOf (p : ℕ) (t : Circle) : Circle := Circle.exp (Complex.arg (t : ℂ) / p)

theorem circleRootOf_pow (p : ℕ) [NeZero p] (t : Circle) : circleRootOf p t ^ p = t := by
  rw [circleRootOf, ← Circle.exp_nsmul, nsmul_eq_mul,
    mul_div_cancel₀ _ (Nat.cast_ne_zero.mpr (NeZero.ne p)), Circle.exp_arg]

theorem contMDiffAt_circleRootOf (p : ℕ) {t : Circle} (ht : (t : ℂ) ∈ Complex.slitPlane) :
    ContMDiffAt (𝓡 1) (𝓡 1) ∞ (circleRootOf p) t := by
  have harg : ContDiffAt ℝ ∞ (fun z : ℂ => Complex.arg z / p) (t : ℂ) := by
    have h1 : ContDiffAt ℝ ∞ (fun z : ℂ => (Complex.log z).im) (t : ℂ) :=
      Complex.imCLM.contDiff.contDiffAt.comp _ ((Complex.contDiffAt_log ht).restrict_scalars ℝ)
    have h2 : (fun z : ℂ => Complex.arg z / p) = fun z => (Complex.log z).im / p := by
      funext z
      rw [Complex.log_im]
    rw [h2]
    exact h1.div_const _
  exact contMDiff_circleExp.contMDiffAt.comp t
    (harg.contMDiffAt.comp t contMDiff_circle_coe.contMDiffAt)

theorem exists_toCircle_mul_of_pow_eq {p : ℕ} [NeZero p] {v w : Circle} (h : v ^ p = w ^ p) :
    ∃ j : ZMod p, w = ZMod.toCircle j * v := by
  have hu : ((w * v⁻¹ : Circle) : ℂ) ^ p = 1 := by
    rw [← Circle.coe_pow, mul_pow, inv_pow, ← h, mul_inv_cancel, Circle.coe_one]
  obtain ⟨i, -, hi⟩ := (Complex.isPrimitiveRoot_exp p (NeZero.ne p)).eq_pow_of_pow_eq_one hu
  refine ⟨i, ?_⟩
  have hc : ZMod.toCircle (i : ZMod p) = w * v⁻¹ := by
    apply Circle.ext
    rw [ZMod.toCircle_natCast, ← hi, ← Complex.exp_nat_mul]
    congr 1
    ring
  rw [hc, inv_mul_cancel_right]

def localRoot (p : ℕ) (t₀ t : Circle) : Circle := circleRootOf p t₀ * circleRootOf p (t * t₀⁻¹)

theorem localRoot_pow (p : ℕ) [NeZero p] (t₀ t : Circle) : localRoot p t₀ t ^ p = t := by
  rw [localRoot, mul_pow, circleRootOf_pow, circleRootOf_pow, mul_comm t, mul_inv_cancel_left]

theorem contMDiffAt_localRoot (p : ℕ) (t₀ : Circle) :
    ContMDiffAt (𝓡 1) (𝓡 1) ∞ (localRoot p t₀) t₀ := by
  have h1 : ContMDiffAt (𝓡 1) (𝓡 1) ∞ (circleRootOf p) (t₀ * t₀⁻¹) := by
    rw [mul_inv_cancel]
    exact contMDiffAt_circleRootOf p (by simp)
  have h2 : ContMDiffAt (𝓡 1) (𝓡 1) ∞ (fun t : Circle => t * t₀⁻¹) t₀ :=
    (contMDiff_id.mul contMDiff_const).contMDiffAt
  exact contMDiffAt_const.mul (ContMDiffAt.comp (g := circleRootOf p) t₀ h1 h2)

theorem norm_circlePair_sq (u v : Circle) (x : LensSphere) :
    ‖(u : ℂ) * sphereFirst x‖ ^ 2 + ‖(v : ℂ) * sphereSecond x‖ ^ 2 = 1 := by
  rw [norm_circle_mul, norm_circle_mul]
  exact norm_sphereFirst_sq_add x

def circlePairAct (u v : Circle) (x : LensSphere) : LensSphere :=
  sphereOfPair ((u : ℂ) * sphereFirst x) ((v : ℂ) * sphereSecond x) (norm_circlePair_sq u v x)

@[simp] theorem sphereFirst_circlePairAct (u v : Circle) (x : LensSphere) :
    sphereFirst (circlePairAct u v x) = (u : ℂ) * sphereFirst x :=
  sphereFirst_sphereOfPair _ _ _

@[simp] theorem sphereSecond_circlePairAct (u v : Circle) (x : LensSphere) :
    sphereSecond (circlePairAct u v x) = (v : ℂ) * sphereSecond x :=
  sphereSecond_sphereOfPair _ _ _

theorem cliffordHeight_circlePairAct (u v : Circle) (x : LensSphere) :
    cliffordHeight (circlePairAct u v x) = cliffordHeight x := by
  rw [cliffordHeight, cliffordHeight, sphereFirst_circlePairAct, sphereSecond_circlePairAct,
    norm_circle_mul, norm_circle_mul]

theorem sphereSwap_circlePairAct (u v : Circle) (x : LensSphere) :
    sphereSwap (circlePairAct u v x) = circlePairAct v u (sphereSwap x) := by
  apply sphere_ext
  · rw [sphereFirst_sphereSwap, sphereSecond_circlePairAct, sphereFirst_circlePairAct,
      sphereFirst_sphereSwap]
  · rw [sphereSecond_sphereSwap, sphereFirst_circlePairAct, sphereSecond_circlePairAct,
      sphereSecond_sphereSwap]

def lensTwist (p : ℕ) [NeZero p] (e : ℤ) (j : ZMod p) (x : LensSphere) : LensSphere :=
  circlePairAct (ZMod.toCircle ((e : ZMod p) * j)) (ZMod.toCircle j) x

structure TwistedCover (p : ℕ) [NeZero p] (e : ℤ) (W : Type) [TopologicalSpace W]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) W] where
  cover : LensSphere → W
  isLocalDiffeomorph : IsLocalDiffeomorph (𝓡 3) (𝓡 3) ∞ cover
  surjective : Surjective cover
  cover_lensTwist : ∀ j x, cover (lensTwist p e j x) = cover x
  exists_lensTwist : ∀ x y, cover x = cover y → ∃ j, y = lensTwist p e j x

namespace TwistedCover

variable {p : ℕ} [NeZero p] {e : ℤ} {W : Type} [TopologicalSpace W]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) W] (T : TwistedCover p e W)

theorem contMDiff_cover : ContMDiff (𝓡 3) (𝓡 3) ∞ T.cover := T.isLocalDiffeomorph.contMDiff

theorem continuous_cover : Continuous T.cover := T.contMDiff_cover.continuous

def lift (w : W) : LensSphere := (T.surjective w).choose

theorem cover_lift (w : W) : T.cover (T.lift w) = w := (T.surjective w).choose_spec

def descend {X : Type*} (f : LensSphere → X) (w : W) : X := f (T.lift w)

theorem descend_cover {X : Type*} {f : LensSphere → X} {x : LensSphere}
    (hf : ∀ j, f (lensTwist p e j x) = f x) : T.descend f (T.cover x) = f x := by
  obtain ⟨j, hj⟩ := T.exists_lensTwist x (T.lift (T.cover x)) (T.cover_lift _).symm
  rw [descend, hj, hf]

theorem contMDiffAt_descend {F G X : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    [TopologicalSpace G] {J : ModelWithCorners ℝ F G} [TopologicalSpace X] [ChartedSpace G X]
    {f : LensSphere → X} {x : LensSphere}
    (hf : ∀ᶠ y in 𝓝 x, ∀ j, f (lensTwist p e j y) = f y)
    (h : ContMDiffAt (𝓡 3) J ∞ f x) : ContMDiffAt (𝓡 3) J ∞ (T.descend f) (T.cover x) := by
  refine (T.isLocalDiffeomorph x).contMDiffAt_of_comp ?_
  apply h.congr_of_eventuallyEq
  filter_upwards [hf] with y hy
  exact T.descend_cover hy

theorem cover_root_eq {Ψ : Circle → LensSphere}
    (hΨ : ∀ v j, Ψ (ZMod.toCircle j * v) = lensTwist p e j (Ψ v)) {v w : Circle}
    (h : v ^ p = w ^ p) : T.cover (Ψ w) = T.cover (Ψ v) := by
  obtain ⟨j, rfl⟩ := exists_toCircle_mul_of_pow_eq h
  rw [hΨ, T.cover_lensTwist]

theorem cover_root_eq_of_pow {Ψ : Circle → LensSphere}
    (hΨ : ∀ v j, Ψ (ZMod.toCircle j * v) = lensTwist p e j (Ψ v)) {v : Circle} {t : Circle}
    (h : v ^ p = t) : T.cover (Ψ (circleRootOf p t)) = T.cover (Ψ v) :=
  T.cover_root_eq hΨ (h.trans (circleRootOf_pow p t).symm)

theorem contMDiffAt_cover_root {F G X : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    [TopologicalSpace G] {J : ModelWithCorners ℝ F G} [TopologicalSpace X] [ChartedSpace G X]
    {f : X → Circle} {x : X} (hf : ContMDiffAt J (𝓡 1) ∞ f x) {Ψ : X → Circle → LensSphere}
    (hΨ : ∀ v, ContMDiffAt (J.prod (𝓡 1)) (𝓡 3) ∞ (fun y : X × Circle => Ψ y.1 y.2) (x, v))
    (hinv : ∀ y v j, Ψ y (ZMod.toCircle j * v) = lensTwist p e j (Ψ y v)) :
    ContMDiffAt J (𝓡 3) ∞ (fun y => T.cover (Ψ y (circleRootOf p (f y)))) x := by
  have heq : (fun y => T.cover (Ψ y (circleRootOf p (f y)))) =
      fun y => T.cover (Ψ y (localRoot p (f x) (f y))) := by
    funext y
    exact T.cover_root_eq_of_pow (hinv y) (localRoot_pow p _ _)
  rw [heq]
  have hR : ContMDiffAt J (𝓡 1) ∞ (fun y => localRoot p (f x) (f y)) x :=
    (contMDiffAt_localRoot p (f x)).comp x hf
  exact T.contMDiff_cover.contMDiffAt.comp x
    ((hΨ (localRoot p (f x) (f x))).comp x (contMDiffAt_id.prodMk hR))

end TwistedCover

theorem lensCoordinates_fst (x : EuclideanSpace ℝ (Fin 4)) :
    (GC.Seifert.lensCoordinates x).fst = (pairCoordinates x).1 := by
  simp only [GC.Seifert.lensCoordinates, pairCoordinates_apply]
  apply Complex.ext <;> simp [OrthonormalBasis.prod] <;> rfl

theorem lensCoordinates_snd (x : EuclideanSpace ℝ (Fin 4)) :
    (GC.Seifert.lensCoordinates x).snd = (pairCoordinates x).2 := by
  simp only [GC.Seifert.lensCoordinates, pairCoordinates_apply]
  apply Complex.ext <;> simp [OrthonormalBasis.prod] <;> rfl

theorem pairCoordinates_lensPairRotation (u v : Circle) (x : EuclideanSpace ℝ (Fin 4)) :
    pairCoordinates (GC.Seifert.lensPairRotation u v x) =
      ((u : ℂ) * (pairCoordinates x).1, (v : ℂ) * (pairCoordinates x).2) := by
  have h := GC.Seifert.lensCoordinates_lensPairRotation u v x
  refine Prod.ext ?_ ?_
  · rw [← lensCoordinates_fst, h, ← lensCoordinates_fst]
    rfl
  · rw [← lensCoordinates_snd, h, ← lensCoordinates_snd]
    rfl

section Lens

variable (p : ℕ) [NeZero p] (q : ℤ) (hpq : IsCoprime (p : ℤ) q)

abbrev LensCarrier : Type := (GC.Seifert.lensSpaceFormGroup p q hpq).manifold.Carrier

def lensCover (x : LensSphere) : LensCarrier p q hpq :=
  (GC.Seifert.lensSpaceFormGroup p q hpq).projection (sphereDownPoint x)

theorem isLocalDiffeomorph_lensCover :
    IsLocalDiffeomorph (𝓡 3) (𝓡 3) ∞ (lensCover p q hpq) := fun x =>
  (standardThreeSphereLiftDiffeomorph.{0}.symm.isLocalDiffeomorph x).comp
    (hg := (GC.Seifert.lensSpaceFormGroup p q hpq).projection_isLocalDiffeomorph _)

theorem lensCover_surjective : Surjective (lensCover p q hpq) := by
  intro w
  obtain ⟨y, hy⟩ : ∃ y : standardThreeSphere.Carrier,
      (GC.Seifert.lensSpaceFormGroup p q hpq).projection y = w :=
    (GC.Seifert.lensSpaceFormGroup p q hpq).projection_surjective w
  refine ⟨standardThreeSphereLiftDiffeomorph.{0} y, ?_⟩
  rw [lensCover, sphereDownPoint, Diffeomorph.symm_apply_apply, hy]

def lensAct (k : ZMod p) (x : LensSphere) : LensSphere :=
  circlePairAct (ZMod.toCircle k) (ZMod.toCircle ((q : ZMod p) * k)) x

theorem sphereDiffeo_sphereDownPoint (k : ZMod p) (x : LensSphere) :
    Geometry.sphereDiffeo (n := 3) (GC.Seifert.lensSpaceFormAction p q (Multiplicative.ofAdd k))
      (sphereDownPoint x) = sphereDownPoint (lensAct p q k x) := by
  apply Subtype.ext
  rw [Geometry.sphereDiffeo_coe]
  change GC.Seifert.lensSpaceFormAction p q (Multiplicative.ofAdd k) (sphereDown x) =
    sphereDown (lensAct p q k x)
  rw [lensAct, circlePairAct, sphereDown_sphereOfPair, GC.Seifert.lensSpaceFormAction_apply,
    toAdd_ofAdd]
  apply pairCoordinates.injective
  rw [ContinuousLinearEquiv.apply_symm_apply, pairCoordinates_lensPairRotation]
  rfl

theorem lensCover_lensAct (k : ZMod p) (x : LensSphere) :
    lensCover p q hpq (lensAct p q k x) = lensCover p q hpq x := by
  rw [lensCover, lensCover, ← sphereDiffeo_sphereDownPoint]
  exact (GC.Seifert.lensSpaceFormGroup p q hpq).projection_invariant
    ⟨GC.Seifert.lensSpaceFormAction p q (Multiplicative.ofAdd k),
      MonoidHom.mem_range.mpr ⟨_, rfl⟩⟩ _

theorem exists_lensAct_of_lensCover_eq {x y : LensSphere}
    (h : lensCover p q hpq x = lensCover p q hpq y) : ∃ k, y = lensAct p q k x := by
  obtain ⟨γ, hγ⟩ := ((GC.Seifert.lensSpaceFormGroup p q hpq).projection_eq_iff _ _).mp h
  obtain ⟨k, hk⟩ := MonoidHom.mem_range.mp γ.2
  refine ⟨Multiplicative.toAdd k, sphereDown_injective ?_⟩
  have h2 : sphereDownPoint y = sphereDownPoint (lensAct p q (Multiplicative.toAdd k) x) := by
    rw [← hγ, ← sphereDiffeo_sphereDownPoint, ofAdd_toAdd, ← hk]
  exact congrArg Subtype.val h2

def lensCoeffP : ℤ := hpq.choose

def lensCoeffQ : ℤ := hpq.choose_spec.choose

omit [NeZero p] in
theorem lensCoeff_spec : lensCoeffP p q hpq * p + lensCoeffQ p q hpq * q = 1 :=
  hpq.choose_spec.choose_spec

omit [NeZero p] in
theorem lensCoeffQ_mul_q : (lensCoeffQ p q hpq : ZMod p) * (q : ZMod p) = 1 := by
  have h := congrArg (Int.cast : ℤ → ZMod p) (lensCoeff_spec p q hpq)
  push_cast at h
  rwa [ZMod.natCast_self, mul_zero, zero_add] at h

theorem lensTwist_eq_lensAct (j : ZMod p) (x : LensSphere) :
    lensTwist p (lensCoeffQ p q hpq) j x = lensAct p q ((lensCoeffQ p q hpq : ZMod p) * j) x := by
  rw [lensTwist, lensAct, ← mul_assoc, mul_comm (q : ZMod p), lensCoeffQ_mul_q, one_mul]

theorem lensAct_eq_lensTwist (k : ZMod p) (x : LensSphere) :
    lensAct p q k x = lensTwist p (lensCoeffQ p q hpq) ((q : ZMod p) * k) x := by
  rw [lensTwist_eq_lensAct p q hpq, ← mul_assoc, lensCoeffQ_mul_q, one_mul]

def lensLeftCover : TwistedCover p (lensCoeffQ p q hpq) (LensCarrier p q hpq) where
  cover := lensCover p q hpq
  isLocalDiffeomorph := isLocalDiffeomorph_lensCover p q hpq
  surjective := lensCover_surjective p q hpq
  cover_lensTwist j x := by rw [lensTwist_eq_lensAct p q hpq, lensCover_lensAct]
  exists_lensTwist x y h := by
    obtain ⟨k, rfl⟩ := exists_lensAct_of_lensCover_eq p q hpq h
    exact ⟨_, lensAct_eq_lensTwist p q hpq k x⟩

theorem sphereSwap_lensTwist (j : ZMod p) (x : LensSphere) :
    sphereSwap (lensTwist p q j x) = lensAct p q j (sphereSwap x) :=
  sphereSwap_circlePairAct _ _ x

def lensRightCover : TwistedCover p q (LensCarrier p q hpq) where
  cover x := lensCover p q hpq (sphereSwap x)
  isLocalDiffeomorph x := (sphereSwap.isLocalDiffeomorph x).comp
    (hg := isLocalDiffeomorph_lensCover p q hpq _)
  surjective w := by
    obtain ⟨x, hx⟩ := lensCover_surjective p q hpq w
    refine ⟨sphereSwap x, ?_⟩
    change lensCover p q hpq (sphereSwap (sphereSwap x)) = w
    rw [sphereSwap_sphereSwap, hx]
  cover_lensTwist j x := by rw [sphereSwap_lensTwist, lensCover_lensAct]
  exists_lensTwist x y h := by
    obtain ⟨k, hk⟩ := exists_lensAct_of_lensCover_eq p q hpq h
    refine ⟨k, ?_⟩
    rw [← sphereSwap_sphereSwap y, hk, ← sphereSwap_lensTwist, sphereSwap_sphereSwap]

theorem lensLeftCover_cover : (lensLeftCover p q hpq).cover = lensCover p q hpq := rfl

theorem lensRightCover_cover (x : LensSphere) :
    (lensRightCover p q hpq).cover x = lensCover p q hpq (sphereSwap x) := rfl

end Lens

end GC.GraphManifold
