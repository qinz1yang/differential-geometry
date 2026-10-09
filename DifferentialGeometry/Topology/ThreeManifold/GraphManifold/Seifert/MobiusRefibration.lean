import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Seifert.LensGroup
import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Seifert.PlanarModels

/-!
# The Möbius circle bundle refibred over `D²(2, 2)`

Packet RG02 of the P1 survey, parts 1 and 2 and the pants coordinates of part 3. The orientable
circle bundle over the Möbius band (the twisted `I`-bundle over the Klein bottle) is the survey's
`N = (S¹ × A) / ((z, u) ∼ (-z, u⁻¹))`, `A = J⁻¹ (closedBall 0 3)`, `J u = (3/4) (u + u⁻¹)`. It is
realized here, without a new quotient construction, inside the lens space `L(4, -1)`, the quotient
of `S³` by `σ : (w₁, w₂) ↦ (i w₁, -i w₂)` (`mobiusLensGroup = lensSpaceFormGroup 4 (-1)`; `lensPair`
are the coordinates of `lensCoordinates`, the group acts by `lensUnitAction ε`, `ε ^ 4 = 1`).

Model. With `a = w₁²`, `b = w₂²` the invariant quartic `bundleQuartic = ‖a + b‖² - 4 ‖a - b‖²`
descends (`lensDescend`) to `L(4, -1)`; its zero level is regular (`mfderiv_sphereQuartic_ne_zero`:
the Euler identity `dQ(w) w = 4 Q(w)` and the explicit direction `bundleDirection` with
`dQ = ‖bundleGradient‖²`), so `mobiusBundleSet = {Q ≤ 0}` in the universe lift `mobiusLens` is a
regular sublevel set and `mobiusBundleCarrier` is a compact carrier, oriented by `L(4, -1)`, whose
boundary is `{Q = 0}` (`mobiusBundleCarrier_boundary`), the preimage of the circle `‖J‖ = 3`
(`mobiusBundleSet_isBoundaryPoint_iff_base`). On `{Q ≤ 0}` one has `a ≠ b`.
The survey's coordinates are `modelPoint = (z, u)`, `z = (a - b) / ‖a - b‖`,
`u = -(w₁ + w₂) / (w₁ - w₂)`: `joukowski u` is the base point, `σ` acts by
`modelDeck (z, u) = (-z, u⁻¹)` and `-1 = σ²` trivially, and two points of `{Q ≤ 0} ⊆ S³` have
the same image in `L(4, -1)` iff their model points agree or differ by `modelDeck`
(`projection_eq_iff_modelPoint`), and every `(z, u) ∈ S¹ × A` with `u ≠ 0` is a model point
(`exists_sphere_modelPoint`). So `mobiusBundleSet` is `N` as a set, with the smooth structure of
`L(4, -1)`.

Seifert structure. The Hopf rotation `ν • (w₁, w₂) = (ν w₁, ν w₂)` commutes with `σ` and descends
to smooth maps `bundleRotate ν` of `L(4, -1)` and `mobiusBundleRotate ν` of `N`. The base map
`mobiusBundleBase = J = -(3/2) (a + b) / (a - b)` is smooth (`contMDiff_mobiusBundleBase`; local
smoothness of descended functions is `contMDiffAt_lensDescend`), takes values in `closedBall 0 3`,
is onto it (`exists_mobiusBundleBase_eq`), is invariant, and its fibres are the orbits
(`exists_mobiusBundleRotate_eq`). The stabilizer of a point is `{ν² = 1}` off `J = ±3/2`
(`mobiusBundleRotate_eq_self_iff`) and `{ν⁴ = 1}` over the cone points `±3/2`, the hole centres of
`planarModel 3` (`mobiusBundleRotate_eq_self_iff_of_cone`): the two exceptional fibres have
multiplicity `2`. They are `w₁ = 0` (`J = 3/2`, `u = 1`) and `w₂ = 0` (`J = -3/2`, `u = -1`)
(`bundleBasePoint_eq_iff_fst`, `modelAnnulusPoint_eq_one_iff` and the `snd`/`neg_one` versions).

Pants coordinates. The fibre coordinate `pantsFibrePoint = w₁ w₂ / ‖w₁ w₂‖` is `σ`-invariant and
is multiplied by `ν²` under the rotation. On `mobiusPants = {J ∈ planarModel 3}` the map
`(J, w₁ w₂ / ‖w₁ w₂‖)` is a bijection onto `planarModel 3 × S¹` (`mobiusPantsEquiv`) intertwining
the rotation with `(ζ, μ) ↦ (ζ, ν² μ)` (`mobiusPantsCoordinates_rotate`); its second coordinate is
smooth off the exceptional fibres (`contMDiffAt_mobiusBundleFibre`). Smoothness of the inverse, the
solid-torus charts, the seam slopes `(2, ±1)` and the `TwistedIBundle` assembly are not done here.
-/

set_option autoImplicit false

noncomputable section
open Set Metric Function
open DifferentialGeometry DifferentialGeometry.Topology GC.Endpoint GC.GraphManifold
open scoped Manifold ContDiff Topology ComplexConjugate

universe u

namespace GC.Seifert

local instance : Fact (Module.finrank ℝ (EuclideanSpace ℝ (Fin 4)) = 3 + 1) := ⟨by simp⟩

def lensPair : EuclideanSpace ℝ (Fin 4) ≃L[ℝ] ℂ × ℂ :=
  lensCoordinates.toContinuousLinearEquiv.trans (WithLp.prodContinuousLinearEquiv 2 ℝ ℂ ℂ)

theorem lensPair_lensPairRotation (u v : Circle) (x : EuclideanSpace ℝ (Fin 4)) :
    lensPair (lensPairRotation u v x) =
      ((u : ℂ) * (lensPair x).1, (v : ℂ) * (lensPair x).2) := by
  change WithLp.ofLp (lensCoordinates (lensPairRotation u v x)) = _
  rw [lensCoordinates_lensPairRotation]
  rfl

theorem norm_sq_eq_lensPair (x : EuclideanSpace ℝ (Fin 4)) :
    ‖x‖ ^ 2 = ‖(lensPair x).1‖ ^ 2 + ‖(lensPair x).2‖ ^ 2 := by
  rw [← lensCoordinates.norm_map x, WithLp.prod_norm_sq_eq_of_L2]
  rfl

theorem isCoprime_four_neg_one : IsCoprime ((4 : ℕ) : ℤ) (-1) := ⟨0, -1, by norm_num⟩

def mobiusLensGroup : SphericalSpaceFormGroup :=
  lensSpaceFormGroup 4 (-1) isCoprime_four_neg_one

def lensUnitAction (ε : Circle) (p : ℂ × ℂ) : ℂ × ℂ :=
  ((ε : ℂ) * p.1, ((ε⁻¹ : Circle) : ℂ) * p.2)

theorem toCircle_pow_four (k : ZMod 4) : ZMod.toCircle k ^ 4 = 1 := by
  rw [← AddChar.map_nsmul_eq_pow]
  have h : (4 : ℕ) • k = 0 := by
    rw [nsmul_eq_mul]
    have h4 : ((4 : ℕ) : ZMod 4) = 0 := ZMod.natCast_self 4
    rw [h4, zero_mul]
  rw [h, AddChar.map_zero_eq_one]

theorem lensPair_lensSpaceFormAction (k : ZMod 4) (x : EuclideanSpace ℝ (Fin 4)) :
    lensPair (lensSpaceFormAction 4 (-1) (Multiplicative.ofAdd k) x) =
      lensUnitAction (ZMod.toCircle k) (lensPair x) := by
  rw [lensSpaceFormAction_apply, lensPair_lensPairRotation, lensUnitAction, toAdd_ofAdd]
  have h : ZMod.toCircle (((-1 : ℤ) : ZMod 4) * k) = (ZMod.toCircle k)⁻¹ := by
    rw [Int.cast_neg, Int.cast_one, neg_one_mul, AddChar.map_neg_eq_inv]
  rw [h]

theorem exists_lensUnit_of_group (γ : mobiusLensGroup.group) :
    ∃ ε : Circle, ε ^ 4 = 1 ∧
      ∀ x, lensPair (γ.val x) = lensUnitAction ε (lensPair x) := by
  have hγ : γ.val ∈ (lensSpaceFormAction 4 (-1)).range := γ.2
  obtain ⟨k, hk⟩ := MonoidHom.mem_range.mp hγ
  refine ⟨ZMod.toCircle (Multiplicative.toAdd k), toCircle_pow_four _, fun x => ?_⟩
  rw [← hk, ← lensPair_lensSpaceFormAction, ofAdd_toAdd]

theorem exists_group_of_pow_four {ε : Circle} (hε : ε ^ 4 = 1) :
    ∃ γ : mobiusLensGroup.group,
      ∀ x, lensPair (γ.val x) = lensUnitAction ε (lensPair x) := by
  have hmem : (toUnits ε : Circleˣ) ∈ rootsOfUnity 4 Circle := by
    rw [mem_rootsOfUnity, ← map_pow, hε, map_one]
  obtain ⟨k, hk⟩ := (bijective_rootsOfUnityAddChar 4).2 ⟨toUnits ε, hmem⟩
  have hkε : ZMod.toCircle k = ε := by
    have h : toUnits (ZMod.toCircle k) = toUnits ε := congrArg Subtype.val hk
    exact toUnits.injective h
  refine ⟨⟨lensSpaceFormAction 4 (-1) (Multiplicative.ofAdd k),
    MonoidHom.mem_range.mpr ⟨_, rfl⟩⟩, fun x => ?_⟩
  rw [← hkε]
  exact lensPair_lensSpaceFormAction k x

theorem projection_eq_projection_iff (x y : sphere (0 : EuclideanSpace ℝ (Fin 4)) 1) :
    mobiusLensGroup.projection x = mobiusLensGroup.projection y ↔
      ∃ ε : Circle, ε ^ 4 = 1 ∧ lensPair y = lensUnitAction ε (lensPair x) := by
  rw [SphericalSpaceFormGroup.projection_eq_iff]
  constructor
  · rintro ⟨γ, hγ⟩
    obtain ⟨ε, hε, h⟩ := exists_lensUnit_of_group γ
    refine ⟨ε, hε, ?_⟩
    rw [← hγ, Geometry.sphereDiffeo_coe, h]
  · rintro ⟨ε, hε, h⟩
    obtain ⟨γ, hγ⟩ := exists_group_of_pow_four hε
    exact ⟨γ, Subtype.ext (lensPair.injective (by rw [Geometry.sphereDiffeo_coe, hγ, h]))⟩

def lensDescend {α : Type*} (f : ℂ × ℂ → α)
    (hf : ∀ ε : Circle, ε ^ 4 = 1 → ∀ p, f (lensUnitAction ε p) = f p) :
    mobiusLensGroup.Orbit → α :=
  Quotient.lift (fun x : sphere (0 : EuclideanSpace ℝ (Fin 4)) 1 => f (lensPair x))
    fun x y hxy => by
      obtain ⟨ε, hε, h⟩ := (projection_eq_projection_iff x y).mp (Quotient.sound hxy)
      rw [h, hf ε hε]

theorem lensDescend_projection {α : Type*} (f : ℂ × ℂ → α)
    (hf : ∀ ε : Circle, ε ^ 4 = 1 → ∀ p, f (lensUnitAction ε p) = f p)
    (x : sphere (0 : EuclideanSpace ℝ (Fin 4)) 1) :
    lensDescend f hf (mobiusLensGroup.projection x) = f (lensPair x) :=
  rfl

theorem contMDiff_lensDescend {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {f : ℂ × ℂ → F} (hf : ∀ ε : Circle, ε ^ 4 = 1 → ∀ p, f (lensUnitAction ε p) = f p)
    (hs : ContDiff ℝ ∞ f) : ContMDiff (𝓡 3) 𝓘(ℝ, F) ∞ (lensDescend f hf) :=
  mobiusLensGroup.projection_isLocalDiffeomorph.contMDiff_of_comp_of_surjective
    mobiusLensGroup.projection_surjective
    ((hs.comp lensPair.contDiff).contMDiff.comp contMDiff_coe_sphere)

theorem lensUnitAction_sq {ε : Circle} (hε : ε ^ 4 = 1) (p : ℂ × ℂ) :
    (lensUnitAction ε p).1 ^ 2 = (ε : ℂ) ^ 2 * p.1 ^ 2 ∧
      (lensUnitAction ε p).2 ^ 2 = (ε : ℂ) ^ 2 * p.2 ^ 2 := by
  have h4 : (ε : ℂ) ^ 4 = 1 := by rw [← Circle.coe_pow, hε, Circle.coe_one]
  have hinv : ((ε⁻¹ : Circle) : ℂ) ^ 2 = (ε : ℂ) ^ 2 := by
    rw [Circle.coe_inv, inv_pow]
    exact inv_eq_of_mul_eq_one_right (by rw [← pow_add]; exact h4)
  refine ⟨?_, ?_⟩
  · change ((ε : ℂ) * p.1) ^ 2 = _
    ring
  · change (((ε⁻¹ : Circle) : ℂ) * p.2) ^ 2 = _
    rw [mul_pow, hinv]

def bundleQuartic (p : ℂ × ℂ) : ℝ :=
  ‖p.1 ^ 2 + p.2 ^ 2‖ ^ 2 - 4 * ‖p.1 ^ 2 - p.2 ^ 2‖ ^ 2

theorem bundleQuartic_lensUnitAction {ε : Circle} (hε : ε ^ 4 = 1) (p : ℂ × ℂ) :
    bundleQuartic (lensUnitAction ε p) = bundleQuartic p := by
  obtain ⟨h1, h2⟩ := lensUnitAction_sq hε p
  have hn : ‖(ε : ℂ) ^ 2‖ = 1 := by rw [norm_pow, Circle.norm_coe, one_pow]
  simp only [bundleQuartic, h1, h2, ← mul_add, ← mul_sub, norm_mul, hn, one_mul]

theorem contDiff_bundleQuartic : ContDiff ℝ ∞ bundleQuartic :=
  ((contDiff_norm_sq ℝ).comp ((contDiff_fst.pow 2).add (contDiff_snd.pow 2))).sub
    (contDiff_const.mul
      ((contDiff_norm_sq ℝ).comp ((contDiff_fst.pow 2).sub (contDiff_snd.pow 2))))

theorem bundleQuartic_smul (t : ℝ) (p : ℂ × ℂ) :
    bundleQuartic (t • p) = t ^ 4 * bundleQuartic p := by
  have h : ∀ w : ℂ, (t • w) ^ 2 = ((t ^ 2 : ℝ) : ℂ) * w ^ 2 := fun w => by
    rw [Complex.real_smul]
    push_cast
    ring
  simp only [bundleQuartic, Prod.smul_fst, Prod.smul_snd, h, ← mul_add, ← mul_sub, norm_mul,
    Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (sq_nonneg t)]
  ring

theorem fderiv_bundleQuartic_self (p : ℂ × ℂ) :
    fderiv ℝ bundleQuartic p p = 4 * bundleQuartic p := by
  have hd : HasFDerivAt bundleQuartic (fderiv ℝ bundleQuartic p) ((1 : ℝ) • p) := by
    rw [one_smul]
    exact (contDiff_bundleQuartic.differentiable (by simp) p).hasFDerivAt
  have hl : HasDerivAt (fun t : ℝ => t • p) p 1 := by
    simpa using (hasDerivAt_id (1 : ℝ)).smul_const p
  have h1 := HasFDerivAt.comp_hasDerivAt (1 : ℝ) hd hl
  have h2 : HasDerivAt (fun t : ℝ => bundleQuartic (t • p)) (4 * bundleQuartic p) 1 := by
    have he : (fun t : ℝ => bundleQuartic (t • p)) = fun t => t ^ 4 * bundleQuartic p :=
      funext fun t => bundleQuartic_smul t p
    rw [he]
    simpa using (hasDerivAt_pow 4 (1 : ℝ)).mul_const (bundleQuartic p)
  exact h1.unique h2

def bundleGradient (p : ℂ × ℂ) : ℂ :=
  (2 : ℝ) • (p.1 ^ 2 + p.2 ^ 2) - (8 : ℝ) • (p.1 ^ 2 - p.2 ^ 2)

def bundleDirection (p : ℂ × ℂ) : ℂ × ℂ := (bundleGradient p / (2 * p.1), 0)

theorem fst_ne_zero_of_bundleQuartic_eq_zero {p : ℂ × ℂ} (hp : p ≠ 0)
    (h : bundleQuartic p = 0) : p.1 ≠ 0 := by
  intro h1
  apply hp
  simp only [bundleQuartic, h1, zero_pow two_ne_zero, zero_add, zero_sub, norm_neg] at h
  have hb : ‖p.2 ^ 2‖ = 0 := by nlinarith [norm_nonneg (p.2 ^ 2)]
  have h2 : p.2 = 0 := pow_eq_zero_iff two_ne_zero |>.mp (norm_eq_zero.mp hb)
  exact Prod.ext h1 h2

theorem bundleGradient_ne_zero {p : ℂ × ℂ} (hp : p ≠ 0) (h : bundleQuartic p = 0) :
    bundleGradient p ≠ 0 := by
  have h1 := fst_ne_zero_of_bundleQuartic_eq_zero hp h
  intro hX
  have hX' : (2 : ℂ) * (p.1 ^ 2 + p.2 ^ 2) - 8 * (p.1 ^ 2 - p.2 ^ 2) = 0 := by
    have h := hX
    simp only [bundleGradient, Complex.real_smul] at h
    push_cast at h
    exact h
  have hs : p.1 ^ 2 + p.2 ^ 2 = (4 : ℝ) • (p.1 ^ 2 - p.2 ^ 2) := by
    rw [Complex.real_smul]
    push_cast
    linear_combination hX' / 2
  have hn : ‖p.1 ^ 2 + p.2 ^ 2‖ = 4 * ‖p.1 ^ 2 - p.2 ^ 2‖ := by
    rw [hs, norm_smul, Real.norm_of_nonneg (by norm_num : (0 : ℝ) ≤ 4)]
  simp only [bundleQuartic] at h
  rw [hn] at h
  have hz : ‖p.1 ^ 2 - p.2 ^ 2‖ = 0 := by nlinarith [norm_nonneg (p.1 ^ 2 - p.2 ^ 2)]
  have hab : p.1 ^ 2 - p.2 ^ 2 = 0 := norm_eq_zero.mp hz
  rw [hab, smul_zero] at hs
  have ha : p.1 ^ 2 = 0 := by linear_combination (hs + hab) / 2
  exact h1 (pow_eq_zero_iff two_ne_zero |>.mp ha)

theorem fderiv_bundleQuartic_direction {p : ℂ × ℂ} (h1 : p.1 ≠ 0) :
    fderiv ℝ bundleQuartic p (bundleDirection p) = ‖bundleGradient p‖ ^ 2 := by
  set d : ℂ := bundleGradient p / (2 * p.1) with hd
  have hline : HasDerivAt (fun t : ℝ => p.1 + t • d) d 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).smul_const d).const_add p.1
  have hA : HasDerivAt (fun t : ℝ => (p.1 + t • d) ^ 2) (bundleGradient p) 0 := by
    have h := hline.fun_pow 2
    have he : ((2 : ℕ) : ℂ) * (p.1 + (0 : ℝ) • d) ^ (2 - 1) * d = bundleGradient p := by
      rw [zero_smul, add_zero, hd]
      field_simp
      ring
    rwa [he] at h
  have hplus := (hA.add_const (p.2 ^ 2)).norm_sq
  have hminus := ((hA.sub_const (p.2 ^ 2)).norm_sq).const_mul 4
  have hg := hplus.sub hminus
  have hval : 2 * inner ℝ ((p.1 + (0 : ℝ) • d) ^ 2 + p.2 ^ 2) (bundleGradient p) -
      4 * (2 * inner ℝ ((p.1 + (0 : ℝ) • d) ^ 2 - p.2 ^ 2) (bundleGradient p)) =
      ‖bundleGradient p‖ ^ 2 := by
    have key : inner ℝ (bundleGradient p) (bundleGradient p) =
        2 * inner ℝ (p.1 ^ 2 + p.2 ^ 2) (bundleGradient p) -
          8 * inner ℝ (p.1 ^ 2 - p.2 ^ 2) (bundleGradient p) := by
      calc inner ℝ (bundleGradient p) (bundleGradient p) =
          inner ℝ ((2 : ℝ) • (p.1 ^ 2 + p.2 ^ 2) - (8 : ℝ) • (p.1 ^ 2 - p.2 ^ 2))
            (bundleGradient p) := rfl
        _ = _ := by rw [inner_sub_left, real_inner_smul_left, real_inner_smul_left]
    rw [zero_smul, add_zero, ← real_inner_self_eq_norm_sq, key]
    ring
  rw [hval] at hg
  have hfd : HasFDerivAt bundleQuartic (fderiv ℝ bundleQuartic p)
      (p + (0 : ℝ) • bundleDirection p) := by
    rw [zero_smul, add_zero]
    exact (contDiff_bundleQuartic.differentiable (by simp) p).hasFDerivAt
  have hl : HasDerivAt (fun t : ℝ => p + t • bundleDirection p) (bundleDirection p) 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).smul_const (bundleDirection p)).const_add p
  have hcomp := HasFDerivAt.comp_hasDerivAt (0 : ℝ) hfd hl
  have heq : (bundleQuartic ∘ fun t : ℝ => p + t • bundleDirection p) =
      fun t : ℝ => ‖(p.1 + t • d) ^ 2 + p.2 ^ 2‖ ^ 2 -
        4 * ‖(p.1 + t • d) ^ 2 - p.2 ^ 2‖ ^ 2 := by
    funext t
    simp [bundleQuartic, bundleDirection, hd]
  rw [heq] at hcomp
  exact hcomp.unique hg

theorem fderiv_bundleQuartic_ne_zero {p : ℂ × ℂ} (hp : p ≠ 0) (h : bundleQuartic p = 0) :
    fderiv ℝ bundleQuartic p ≠ 0 := by
  intro h0
  have h1 := fst_ne_zero_of_bundleQuartic_eq_zero hp h
  have hX := bundleGradient_ne_zero hp h
  have hv := fderiv_bundleQuartic_direction h1
  have hv' : ‖bundleGradient p‖ ^ 2 = 0 := by
    rw [← hv, h0]
    rfl
  exact hX (norm_eq_zero.mp (pow_eq_zero_iff two_ne_zero |>.mp hv'))

theorem lensPair_ne_zero (x : sphere (0 : EuclideanSpace ℝ (Fin 4)) 1) :
    lensPair (x : EuclideanSpace ℝ (Fin 4)) ≠ 0 := by
  intro h
  have hx := ne_zero_of_mem_unit_sphere x
  exact hx (lensPair.injective (by rw [h, map_zero]))

theorem mfderiv_sphereQuartic_ne_zero (x : sphere (0 : EuclideanSpace ℝ (Fin 4)) 1)
    (hx : bundleQuartic (lensPair x) = 0) :
    mfderiv (𝓡 3) 𝓘(ℝ, ℝ)
      (fun y : sphere (0 : EuclideanSpace ℝ (Fin 4)) 1 => bundleQuartic (lensPair y)) x ≠ 0 := by
  set F : EuclideanSpace ℝ (Fin 4) → ℝ := fun v => bundleQuartic (lensPair v)
  have hF : ContDiff ℝ ∞ F := contDiff_bundleQuartic.comp lensPair.contDiff
  have hFx : HasFDerivAt F ((fderiv ℝ bundleQuartic (lensPair x)).comp
      (lensPair : EuclideanSpace ℝ (Fin 4) →L[ℝ] ℂ × ℂ)) x :=
    ((contDiff_bundleQuartic.differentiable (by simp) _).hasFDerivAt).comp
      (x : EuclideanSpace ℝ (Fin 4)) lensPair.hasFDerivAt
  intro h0
  have hvan : ∀ w ∈ (ℝ ∙ (x : EuclideanSpace ℝ (Fin 4)))ᗮ, fderiv ℝ F x w = 0 := by
    intro w hw
    rw [← range_mvfderiv_subtypeVal (n := 3) x] at hw
    obtain ⟨v, rfl⟩ := hw
    have hc := mfderiv_comp_apply (I := 𝓡 3) (I' := 𝓘(ℝ, EuclideanSpace ℝ (Fin 4)))
      (I'' := 𝓘(ℝ, ℝ)) (g := F) (f := Subtype.val) (x := x)
      (hF.contMDiff.mdifferentiableAt (by simp))
      ((contMDiff_coe_sphere (m := 1) x).mdifferentiableAt one_ne_zero) v
    have hc0 : mfderiv (𝓡 3) 𝓘(ℝ, ℝ) (F ∘ Subtype.val) x v = 0 := by
      change mfderiv (𝓡 3) 𝓘(ℝ, ℝ)
        (fun y : sphere (0 : EuclideanSpace ℝ (Fin 4)) 1 => bundleQuartic (lensPair y)) x v = 0
      rw [h0]
      rfl
    rw [hc0, mfderiv_eq_fderiv] at hc
    exact hc.symm
  have hself : fderiv ℝ F x x = 0 := by
    rw [hFx.fderiv, ContinuousLinearMap.comp_apply]
    change fderiv ℝ bundleQuartic (lensPair x) (lensPair x) = 0
    rw [fderiv_bundleQuartic_self, hx, mul_zero]
  have hall : fderiv ℝ F x = 0 := by
    ext1 w
    have hnorm : ‖(x : EuclideanSpace ℝ (Fin 4))‖ = 1 := norm_eq_of_mem_sphere x
    have hmem : w - inner ℝ (x : EuclideanSpace ℝ (Fin 4)) w • (x : EuclideanSpace ℝ (Fin 4)) ∈
        (ℝ ∙ (x : EuclideanSpace ℝ (Fin 4)))ᗮ := by
      rw [Submodule.mem_orthogonal_singleton_iff_inner_right, inner_sub_right,
        real_inner_smul_right, real_inner_self_eq_norm_sq, hnorm]
      ring
    have hw := hvan _ hmem
    rw [map_sub, map_smul, hself, smul_zero, sub_zero] at hw
    rw [hw]
    rfl
  apply fderiv_bundleQuartic_ne_zero (lensPair_ne_zero x) hx
  rw [hFx.fderiv] at hall
  refine ContinuousLinearMap.ext fun d => ?_
  have := congrArg (fun L => L (lensPair.symm d)) hall
  simpa using this

abbrev mobiusLens : ConnectedClosedOrientedManifold.{u} 3 := mobiusLensGroup.manifold.ulift

instance mobiusLens_secondCountable : SecondCountableTopology mobiusLens.{u}.Carrier :=
  ChartedSpace.secondCountable_of_sigmaCompact (EuclideanSpace ℝ (Fin 3)) mobiusLens.{u}.Carrier

theorem bundleQuartic_invariant :
    ∀ ε : Circle, ε ^ 4 = 1 → ∀ p, bundleQuartic (lensUnitAction ε p) = bundleQuartic p :=
  fun _ hε p => bundleQuartic_lensUnitAction hε p

def lensUp (q : mobiusLensGroup.Orbit) : mobiusLens.{u}.Carrier :=
  ClosedOrientedManifold.uliftDiffeomorph.{0, u}
    mobiusLensGroup.manifold.toClosedOrientedManifold q

def lensDown (y : mobiusLens.{u}.Carrier) : mobiusLensGroup.Orbit :=
  (ClosedOrientedManifold.uliftDiffeomorph.{0, u}
    mobiusLensGroup.manifold.toClosedOrientedManifold).symm y

theorem lensDown_lensUp (q : mobiusLensGroup.Orbit) : lensDown.{u} (lensUp q) = q := rfl

theorem lensUp_lensDown (y : mobiusLens.{u}.Carrier) : lensUp (lensDown y) = y := rfl

theorem contMDiff_lensUp : ContMDiff (𝓡 3) (𝓡 3) ∞ lensUp.{u} :=
  (ClosedOrientedManifold.uliftDiffeomorph.{0, u}
    mobiusLensGroup.manifold.toClosedOrientedManifold).contMDiff

theorem contMDiff_lensDown : ContMDiff (𝓡 3) (𝓡 3) ∞ lensDown.{u} :=
  (ClosedOrientedManifold.uliftDiffeomorph.{0, u}
    mobiusLensGroup.manifold.toClosedOrientedManifold).symm.contMDiff

def mobiusBundleFunction (y : mobiusLens.{u}.Carrier) : ℝ :=
  lensDescend bundleQuartic bundleQuartic_invariant (lensDown y)

theorem contMDiff_mobiusBundleFunction : ContMDiff (𝓡 3) 𝓘(ℝ, ℝ) ∞ mobiusBundleFunction.{u} :=
  (contMDiff_lensDescend bundleQuartic_invariant contDiff_bundleQuartic).comp contMDiff_lensDown

theorem mobiusBundleFunction_regular (y : mobiusLens.{u}.Carrier)
    (hy : mobiusBundleFunction y = 0) :
    mfderiv (𝓡 3) 𝓘(ℝ, ℝ) mobiusBundleFunction y ≠ 0 := by
  obtain ⟨x, hx⟩ := mobiusLensGroup.projection_surjective (lensDown y)
  have hyx : y = lensUp (mobiusLensGroup.projection x) := by
    rw [hx, lensUp_lensDown]
  subst hyx
  exact mfderiv_ne_zero_of_comp (J := 𝓡 3)
    (s := fun z : sphere (0 : EuclideanSpace ℝ (Fin 4)) 1 =>
      lensUp.{u} (mobiusLensGroup.projection z)) (y := x)
    (contMDiff_mobiusBundleFunction.mdifferentiableAt (by simp))
    ((contMDiff_lensUp.comp mobiusLensGroup.projection_isLocalDiffeomorph.contMDiff
      ).mdifferentiableAt (by simp))
    (mfderiv_sphereQuartic_ne_zero x hy)

def mobiusBundleSet : Set mobiusLens.{u}.Carrier := {y | mobiusBundleFunction y ≤ 0}

def mobiusBundleAtlas : SmoothBoundaryAtlas (𝓡 3) 3 mobiusBundleSet.{u} :=
  SmoothBoundaryAtlas.regularSublevel (𝓡 3) (n := 2) (by simp) contMDiff_mobiusBundleFunction 0
    mobiusBundleFunction_regular

instance : ChartedSpace (EuclideanHalfSpace 3) mobiusBundleSet.{u} :=
  mobiusBundleAtlas.toChartedSpace

instance : IsManifold (𝓡∂ 3) ∞ mobiusBundleSet.{u} := mobiusBundleAtlas.isManifold

theorem mobiusBundleSet_isBoundaryPoint_iff (x : mobiusBundleSet.{u}) :
    (𝓡∂ 3).IsBoundaryPoint x ↔ mobiusBundleFunction x.val = 0 :=
  SmoothBoundaryAtlas.regularSublevel_isBoundaryPoint_iff (𝓡 3) (n := 2) (by simp)
    contMDiff_mobiusBundleFunction 0 mobiusBundleFunction_regular x

def mobiusBundleCarrier : CompactCarrier.{u} where
  kind := .withBoundary
  Carrier := mobiusBundleSet.{u}
  charts := (inferInstance : ChartedSpace (EuclideanHalfSpace 3) mobiusBundleSet.{u})
  smooth := (inferInstance : IsManifold (𝓡∂ 3) ∞ mobiusBundleSet.{u})
  compact := isCompact_iff_compactSpace.mp
    (isClosed_le contMDiff_mobiusBundleFunction.continuous continuous_const).isCompact
  orientation := mobiusBundleAtlas.orientation mobiusLens.{u}.orientation

theorem mobiusBundleCarrier_boundary :
    (𝓡∂ 3).boundary mobiusBundleSet.{u} = {x | mobiusBundleFunction x.val = 0} := by
  ext x
  exact mobiusBundleSet_isBoundaryPoint_iff x

def bundleBasePoint (p : ℂ × ℂ) : ℂ := -(3 / 2) * (p.1 ^ 2 + p.2 ^ 2) / (p.1 ^ 2 - p.2 ^ 2)

theorem bundleBasePoint_lensUnitAction {ε : Circle} (hε : ε ^ 4 = 1) (p : ℂ × ℂ) :
    bundleBasePoint (lensUnitAction ε p) = bundleBasePoint p := by
  obtain ⟨h1, h2⟩ := lensUnitAction_sq hε p
  have hne : (ε : ℂ) ^ 2 ≠ 0 := pow_ne_zero _ (Circle.coe_ne_zero ε)
  simp only [bundleBasePoint, h1, h2, ← mul_add, ← mul_sub]
  rw [mul_left_comm, mul_div_mul_left _ _ hne]

def bundleBase : mobiusLensGroup.Orbit → ℂ :=
  lensDescend bundleBasePoint fun _ hε p => bundleBasePoint_lensUnitAction hε p

def rotatePair (ν : Circle) (p : ℂ × ℂ) : ℂ × ℂ := ((ν : ℂ) * p.1, (ν : ℂ) * p.2)

theorem bundleQuartic_rotatePair (ν : Circle) (p : ℂ × ℂ) :
    bundleQuartic (rotatePair ν p) = bundleQuartic p := by
  have hn : ‖(ν : ℂ) ^ 2‖ = 1 := by rw [norm_pow, Circle.norm_coe, one_pow]
  simp only [bundleQuartic, rotatePair, mul_pow, ← mul_add, ← mul_sub, norm_mul, hn, one_mul]

theorem bundleBasePoint_rotatePair (ν : Circle) (p : ℂ × ℂ) :
    bundleBasePoint (rotatePair ν p) = bundleBasePoint p := by
  have hne : (ν : ℂ) ^ 2 ≠ 0 := pow_ne_zero _ (Circle.coe_ne_zero ν)
  simp only [bundleBasePoint, rotatePair, mul_pow, ← mul_add, ← mul_sub]
  rw [mul_left_comm, mul_div_mul_left _ _ hne]

theorem lensUnitAction_rotatePair (ε ν : Circle) (p : ℂ × ℂ) :
    lensUnitAction ε (rotatePair ν p) = rotatePair ν (lensUnitAction ε p) :=
  Prod.ext (mul_left_comm _ _ _) (mul_left_comm _ _ _)

def lensRotation (ν : Circle) : sphere (0 : EuclideanSpace ℝ (Fin 4)) 1 ≃ₘ⟮𝓡 3, 𝓡 3⟯
    sphere (0 : EuclideanSpace ℝ (Fin 4)) 1 :=
  Geometry.sphereDiffeo (lensPairRotation ν ν)

theorem lensPair_lensRotation (ν : Circle) (x : sphere (0 : EuclideanSpace ℝ (Fin 4)) 1) :
    lensPair (lensRotation ν x : EuclideanSpace ℝ (Fin 4)) = rotatePair ν (lensPair x) := by
  rw [lensRotation, Geometry.sphereDiffeo_coe, lensPair_lensPairRotation]
  rfl

def bundleRotate (ν : Circle) : mobiusLensGroup.Orbit → mobiusLensGroup.Orbit :=
  Quotient.map (lensRotation ν) fun x y hxy => by
    obtain ⟨ε, hε, h⟩ := (projection_eq_projection_iff x y).mp (Quotient.sound hxy)
    refine Quotient.exact ((projection_eq_projection_iff _ _).mpr ⟨ε, hε, ?_⟩)
    rw [lensPair_lensRotation, lensPair_lensRotation, h, lensUnitAction_rotatePair]

theorem bundleRotate_projection (ν : Circle) (x : sphere (0 : EuclideanSpace ℝ (Fin 4)) 1) :
    bundleRotate ν (mobiusLensGroup.projection x) =
      mobiusLensGroup.projection (lensRotation ν x) :=
  rfl

theorem contMDiff_bundleRotate (ν : Circle) : ContMDiff (𝓡 3) (𝓡 3) ∞ (bundleRotate ν) :=
  mobiusLensGroup.projection_isLocalDiffeomorph.contMDiff_of_comp_of_surjective
    mobiusLensGroup.projection_surjective
    (mobiusLensGroup.projection_isLocalDiffeomorph.contMDiff.comp (lensRotation ν).contMDiff)

theorem sq_sub_sq_ne_zero_of_bundleQuartic_nonpos {p : ℂ × ℂ} (hp : p ≠ 0)
    (h : bundleQuartic p ≤ 0) : p.1 ^ 2 - p.2 ^ 2 ≠ 0 := by
  intro hab
  simp only [bundleQuartic, hab, norm_zero, zero_pow two_ne_zero, mul_zero, sub_zero] at h
  have h0 : ‖p.1 ^ 2 + p.2 ^ 2‖ = 0 := by nlinarith [norm_nonneg (p.1 ^ 2 + p.2 ^ 2)]
  have hs : p.1 ^ 2 + p.2 ^ 2 = 0 := norm_eq_zero.mp h0
  have h1 : p.1 ^ 2 = 0 := by linear_combination (hs + hab) / 2
  have h2 : p.2 ^ 2 = 0 := by linear_combination (hs - hab) / 2
  exact hp (Prod.ext (pow_eq_zero_iff two_ne_zero |>.mp h1) (pow_eq_zero_iff two_ne_zero |>.mp h2))

theorem bundleQuartic_nonpos_iff {p : ℂ × ℂ} (hab : p.1 ^ 2 - p.2 ^ 2 ≠ 0) :
    bundleQuartic p ≤ 0 ↔ ‖bundleBasePoint p‖ ≤ 3 := by
  have hpos : 0 < ‖p.1 ^ 2 - p.2 ^ 2‖ := norm_pos_iff.mpr hab
  have hJ : ‖bundleBasePoint p‖ = 3 / 2 * ‖p.1 ^ 2 + p.2 ^ 2‖ / ‖p.1 ^ 2 - p.2 ^ 2‖ := by
    rw [bundleBasePoint, norm_div, norm_mul, norm_neg]
    norm_num
  rw [hJ, div_le_iff₀ hpos, bundleQuartic, sub_nonpos]
  have hA := norm_nonneg (p.1 ^ 2 + p.2 ^ 2)
  constructor
  · intro h
    nlinarith
  · intro h
    nlinarith

theorem bundleBasePoint_eq_iff_fst {p : ℂ × ℂ} (hab : p.1 ^ 2 - p.2 ^ 2 ≠ 0) :
    bundleBasePoint p = 3 / 2 ↔ p.1 = 0 := by
  rw [bundleBasePoint, div_eq_iff hab]
  constructor
  · intro h
    have h1 : p.1 ^ 2 = 0 := by linear_combination (-1 / 3 : ℂ) * h
    exact pow_eq_zero_iff two_ne_zero |>.mp h1
  · intro h
    rw [h]
    ring

theorem bundleBasePoint_eq_iff_snd {p : ℂ × ℂ} (hab : p.1 ^ 2 - p.2 ^ 2 ≠ 0) :
    bundleBasePoint p = -(3 / 2) ↔ p.2 = 0 := by
  rw [bundleBasePoint, div_eq_iff hab]
  constructor
  · intro h
    have h1 : p.2 ^ 2 = 0 := by linear_combination (-1 / 3 : ℂ) * h
    exact pow_eq_zero_iff two_ne_zero |>.mp h1
  · intro h
    rw [h]
    ring

def circleI : Circle := Circle.exp (Real.pi / 2)

theorem coe_circleI : (circleI : ℂ) = Complex.I := by
  rw [circleI, Circle.coe_exp]
  push_cast
  exact Complex.exp_pi_div_two_mul_I

theorem circleI_pow_four : circleI ^ 4 = 1 := by
  apply Circle.ext
  rw [Circle.coe_pow, coe_circleI, Circle.coe_one]
  exact Complex.I_pow_four

theorem exists_circle_sq_eq {k : ℂ} (hk : ‖k‖ = 1) : ∃ κ : Circle, (κ : ℂ) ^ 2 = k := by
  refine ⟨Circle.exp (Complex.arg k / 2), ?_⟩
  have h := Complex.norm_mul_exp_arg_mul_I k
  rw [hk, Complex.ofReal_one, one_mul] at h
  rw [Circle.coe_exp, ← Complex.exp_nat_mul]
  convert h using 2
  push_cast
  ring

theorem exists_scalar_of_cross {a b c d : ℂ} (hab : a ≠ 0 ∨ b ≠ 0) (h : c * b = a * d) :
    ∃ k, c = k * a ∧ d = k * b := by
  by_cases ha : a = 0
  · have hb : b ≠ 0 := hab.resolve_left (not_not.mpr ha)
    refine ⟨d / b, ?_, by field_simp⟩
    rw [ha, zero_mul] at h
    rw [ha, mul_zero]
    exact (mul_eq_zero.mp h).resolve_right hb
  · refine ⟨c / a, by field_simp, ?_⟩
    field_simp
    linear_combination -h

theorem exists_rotate_of_bundleBasePoint_eq {p q : ℂ × ℂ}
    (hpn : ‖p.1‖ ^ 2 + ‖p.2‖ ^ 2 = 1) (hqn : ‖q.1‖ ^ 2 + ‖q.2‖ ^ 2 = 1)
    (hp : p.1 ^ 2 - p.2 ^ 2 ≠ 0) (hq : q.1 ^ 2 - q.2 ^ 2 ≠ 0)
    (h : bundleBasePoint p = bundleBasePoint q) :
    ∃ ν ε : Circle, ε ^ 4 = 1 ∧ q = lensUnitAction ε (rotatePair ν p) := by
  rw [bundleBasePoint, bundleBasePoint, div_eq_div_iff hp hq] at h
  have hc : q.1 ^ 2 * p.2 ^ 2 = p.1 ^ 2 * q.2 ^ 2 := by linear_combination (-1 / 3 : ℂ) * h
  have hp0 : p.1 ^ 2 ≠ 0 ∨ p.2 ^ 2 ≠ 0 := by
    by_contra hcon
    rw [not_or, not_not, not_not] at hcon
    exact hp (by rw [hcon.1, hcon.2, sub_zero])
  obtain ⟨k, hk1, hk2⟩ := exists_scalar_of_cross hp0 hc
  have hnorm : ‖k‖ = 1 := by
    have e1 : ‖q.1‖ ^ 2 = ‖k‖ * ‖p.1‖ ^ 2 := by rw [← norm_pow, hk1, norm_mul, norm_pow]
    have e2 : ‖q.2‖ ^ 2 = ‖k‖ * ‖p.2‖ ^ 2 := by rw [← norm_pow, hk2, norm_mul, norm_pow]
    have h3 : ‖k‖ * (‖p.1‖ ^ 2 + ‖p.2‖ ^ 2) = 1 := by rw [mul_add, ← e1, ← e2, hqn]
    rwa [hpn, mul_one] at h3
  obtain ⟨κ, hκ⟩ := exists_circle_sq_eq hnorm
  have hs1 : q.1 = κ * p.1 ∨ q.1 = -(κ * p.1) :=
    sq_eq_sq_iff_eq_or_eq_neg.mp (by rw [hk1, mul_pow, hκ])
  have hs2 : q.2 = κ * p.2 ∨ q.2 = -(κ * p.2) :=
    sq_eq_sq_iff_eq_or_eq_neg.mp (by rw [hk2, mul_pow, hκ])
  have hI : Complex.I * Complex.I = -1 := Complex.I_mul_I
  rcases hs1 with h1 | h1 <;> rcases hs2 with h2 | h2
  · exact ⟨κ, 1, one_pow _, Prod.ext (by simp [lensUnitAction, rotatePair, h1])
      (by simp [lensUnitAction, rotatePair, h2])⟩
  · refine ⟨κ * circleI⁻¹, circleI, circleI_pow_four, Prod.ext ?_ ?_⟩
    · simp only [lensUnitAction, rotatePair, Circle.coe_mul, Circle.coe_inv, coe_circleI, h1,
        Complex.inv_I]
      linear_combination ((κ : ℂ) * p.1) * hI
    · simp only [lensUnitAction, rotatePair, Circle.coe_mul, Circle.coe_inv, coe_circleI, h2,
        Complex.inv_I]
      linear_combination (-((κ : ℂ) * p.2)) * hI
  · refine ⟨κ * circleI, circleI, circleI_pow_four, Prod.ext ?_ ?_⟩
    · simp only [lensUnitAction, rotatePair, Circle.coe_mul, Circle.coe_inv, coe_circleI, h1,
        Complex.inv_I]
      linear_combination (-((κ : ℂ) * p.1)) * hI
    · simp only [lensUnitAction, rotatePair, Circle.coe_mul, Circle.coe_inv, coe_circleI, h2,
        Complex.inv_I]
      linear_combination ((κ : ℂ) * p.2) * hI
  · refine ⟨κ, circleI ^ 2, ?_, Prod.ext ?_ ?_⟩
    · rw [← pow_mul, show 2 * 4 = 4 * 2 from rfl, pow_mul, circleI_pow_four, one_pow]
    · simp only [lensUnitAction, rotatePair, Circle.coe_pow, coe_circleI, h1, Complex.I_sq]
      ring
    · simp only [lensUnitAction, rotatePair, Circle.coe_inv, Circle.coe_pow, coe_circleI, h2,
        Complex.I_sq, inv_neg, inv_one]
      ring

theorem circle_mul_eq_one_of_fst {p : ℂ × ℂ} (h1 : p.1 ≠ 0) {ε ν : Circle}
    (h : p = lensUnitAction ε (rotatePair ν p)) : ε * ν = 1 := by
  have h' := congrArg Prod.fst h
  simp only [lensUnitAction, rotatePair] at h'
  apply Circle.ext
  rw [Circle.coe_mul, Circle.coe_one]
  apply mul_right_cancel₀ h1
  linear_combination -h'

theorem circle_inv_mul_eq_one_of_snd {p : ℂ × ℂ} (h2 : p.2 ≠ 0) {ε ν : Circle}
    (h : p = lensUnitAction ε (rotatePair ν p)) : ε⁻¹ * ν = 1 := by
  have h' := congrArg Prod.snd h
  simp only [lensUnitAction, rotatePair] at h'
  apply Circle.ext
  rw [Circle.coe_mul, Circle.coe_one]
  apply mul_right_cancel₀ h2
  linear_combination -h'

theorem lensUnitAction_inv_rotatePair_fst (ν : Circle) (p : ℂ × ℂ) :
    (lensUnitAction ν⁻¹ (rotatePair ν p)).1 = p.1 := by
  simp only [lensUnitAction, rotatePair, Circle.coe_inv]
  rw [← mul_assoc, inv_mul_cancel₀ (Circle.coe_ne_zero ν), one_mul]

theorem lensUnitAction_rotatePair_snd (ν : Circle) (p : ℂ × ℂ) :
    (lensUnitAction ν (rotatePair ν p)).2 = p.2 := by
  simp only [lensUnitAction, rotatePair, Circle.coe_inv]
  rw [← mul_assoc, inv_mul_cancel₀ (Circle.coe_ne_zero ν), one_mul]

theorem rotate_fix_iff {p : ℂ × ℂ} (h1 : p.1 ≠ 0) (h2 : p.2 ≠ 0) (ν : Circle) :
    (∃ ε : Circle, ε ^ 4 = 1 ∧ p = lensUnitAction ε (rotatePair ν p)) ↔ ν ^ 2 = 1 := by
  constructor
  · rintro ⟨ε, -, h⟩
    have c1 := circle_mul_eq_one_of_fst h1 h
    have hεν : ε = ν := inv_mul_eq_one.mp (circle_inv_mul_eq_one_of_snd h2 h)
    rw [sq, ← hεν]
    rwa [← hεν] at c1
  · intro hν
    refine ⟨ν⁻¹, by rw [inv_pow, show (4 : ℕ) = 2 * 2 from rfl, pow_mul, hν, one_pow, inv_one],
      Prod.ext (lensUnitAction_inv_rotatePair_fst ν p).symm ?_⟩
    have hν' : (ν : ℂ) ^ 2 = 1 := by rw [← Circle.coe_pow, hν, Circle.coe_one]
    simp only [lensUnitAction, rotatePair, inv_inv]
    linear_combination (-p.2) * hν'

theorem rotate_fix_iff_of_fst_eq_zero {p : ℂ × ℂ} (h1 : p.1 = 0) (h2 : p.2 ≠ 0)
    (ν : Circle) :
    (∃ ε : Circle, ε ^ 4 = 1 ∧ p = lensUnitAction ε (rotatePair ν p)) ↔ ν ^ 4 = 1 := by
  constructor
  · rintro ⟨ε, hε, h⟩
    rw [← inv_mul_eq_one.mp (circle_inv_mul_eq_one_of_snd h2 h)]
    exact hε
  · intro hν
    refine ⟨ν, hν, Prod.ext ?_ (lensUnitAction_rotatePair_snd ν p).symm⟩
    simp [lensUnitAction, rotatePair, h1]

theorem rotate_fix_iff_of_snd_eq_zero {p : ℂ × ℂ} (h1 : p.1 ≠ 0) (h2 : p.2 = 0)
    (ν : Circle) :
    (∃ ε : Circle, ε ^ 4 = 1 ∧ p = lensUnitAction ε (rotatePair ν p)) ↔ ν ^ 4 = 1 := by
  constructor
  · rintro ⟨ε, hε, h⟩
    rw [eq_inv_of_mul_eq_one_right (circle_mul_eq_one_of_fst h1 h), inv_pow, hε, inv_one]
  · intro hν
    refine ⟨ν⁻¹, by rw [inv_pow, hν, inv_one],
      Prod.ext (lensUnitAction_inv_rotatePair_fst ν p).symm ?_⟩
    simp [lensUnitAction, rotatePair, h2]

theorem norm_sq_lensPair_sphere (x : sphere (0 : EuclideanSpace ℝ (Fin 4)) 1) :
    ‖(lensPair x).1‖ ^ 2 + ‖(lensPair x).2‖ ^ 2 = 1 := by
  rw [← norm_sq_eq_lensPair, norm_eq_of_mem_sphere x, one_pow]

theorem exists_sphere_rep (y : mobiusBundleSet.{u}) :
    ∃ x : sphere (0 : EuclideanSpace ℝ (Fin 4)) 1,
      lensDown y.val = mobiusLensGroup.projection x ∧ bundleQuartic (lensPair x) ≤ 0 := by
  obtain ⟨x, hx⟩ := mobiusLensGroup.projection_surjective (lensDown y.val)
  refine ⟨x, hx.symm, ?_⟩
  have hy : mobiusBundleFunction y.val ≤ 0 := y.2
  change lensDescend bundleQuartic bundleQuartic_invariant (lensDown y.val) ≤ 0 at hy
  rwa [← hx] at hy

def mobiusBundleBase (y : mobiusBundleSet.{u}) : ℂ := bundleBase (lensDown y.val)

theorem mobiusBundleBase_eq {y : mobiusBundleSet.{u}} {x : sphere (0 : EuclideanSpace ℝ (Fin 4)) 1}
    (hx : lensDown y.val = mobiusLensGroup.projection x) :
    mobiusBundleBase y = bundleBasePoint (lensPair x) := by
  change bundleBase (lensDown y.val) = _
  rw [hx]
  rfl

def mobiusBundleRotate (ν : Circle) (y : mobiusBundleSet.{u}) : mobiusBundleSet.{u} :=
  ⟨lensUp (bundleRotate ν (lensDown y.val)), by
    obtain ⟨x, hx, hq⟩ := exists_sphere_rep y
    change lensDescend bundleQuartic bundleQuartic_invariant
      (lensDown (lensUp (bundleRotate ν (lensDown y.val)))) ≤ 0
    rw [lensDown_lensUp, hx, bundleRotate_projection]
    change bundleQuartic (lensPair (lensRotation ν x : EuclideanSpace ℝ (Fin 4))) ≤ 0
    rwa [lensPair_lensRotation, bundleQuartic_rotatePair]⟩

theorem contMDiff_mobiusBundleRotate (ν : Circle) :
    ContMDiff (𝓡∂ 3) (𝓡∂ 3) ∞ (mobiusBundleRotate.{u} ν) :=
  (mobiusBundleAtlas.contMDiff_iff_subtype_val _).mpr
    (contMDiff_lensUp.comp ((contMDiff_bundleRotate ν).comp
      (contMDiff_lensDown.comp mobiusBundleAtlas.contMDiff_subtype_val)))

theorem mobiusBundleBase_norm_le (y : mobiusBundleSet.{u}) : ‖mobiusBundleBase y‖ ≤ 3 := by
  obtain ⟨x, hx, hq⟩ := exists_sphere_rep y
  rw [mobiusBundleBase_eq hx]
  exact (bundleQuartic_nonpos_iff
    (sq_sub_sq_ne_zero_of_bundleQuartic_nonpos (lensPair_ne_zero x) hq)).mp hq

theorem mobiusBundleBase_rotate (ν : Circle) (y : mobiusBundleSet.{u}) :
    mobiusBundleBase (mobiusBundleRotate ν y) = mobiusBundleBase y := by
  obtain ⟨x, hx, -⟩ := exists_sphere_rep y
  change bundleBase (lensDown (lensUp (bundleRotate ν (lensDown y.val)))) =
    bundleBase (lensDown y.val)
  rw [lensDown_lensUp, hx, bundleRotate_projection]
  change bundleBasePoint (lensPair (lensRotation ν x : EuclideanSpace ℝ (Fin 4))) =
    bundleBasePoint (lensPair x)
  rw [lensPair_lensRotation, bundleBasePoint_rotatePair]

theorem mobiusBundleRotate_eq_iff (ν : Circle) (y z : mobiusBundleSet.{u})
    {x x' : sphere (0 : EuclideanSpace ℝ (Fin 4)) 1}
    (hx : lensDown y.val = mobiusLensGroup.projection x)
    (hx' : lensDown z.val = mobiusLensGroup.projection x') :
    mobiusBundleRotate ν y = z ↔
      ∃ ε : Circle, ε ^ 4 = 1 ∧ lensPair x' = lensUnitAction ε (rotatePair ν (lensPair x)) := by
  rw [Subtype.ext_iff]
  change lensUp (bundleRotate ν (lensDown y.val)) = z.val ↔ _
  rw [← lensPair_lensRotation, ← projection_eq_projection_iff]
  constructor
  · intro h
    have h' := congrArg lensDown h
    rwa [lensDown_lensUp, hx, hx', bundleRotate_projection] at h'
  · intro h
    rw [← lensUp_lensDown z.val, hx', hx, bundleRotate_projection, h]

theorem mobiusBundleRotate_eq_self_iff (y : mobiusBundleSet.{u}) (h1 : mobiusBundleBase y ≠ 3 / 2)
    (h2 : mobiusBundleBase y ≠ -(3 / 2)) (ν : Circle) :
    mobiusBundleRotate ν y = y ↔ ν ^ 2 = 1 := by
  obtain ⟨x, hx, hq⟩ := exists_sphere_rep y
  have hab := sq_sub_sq_ne_zero_of_bundleQuartic_nonpos (lensPair_ne_zero x) hq
  rw [mobiusBundleBase_eq hx] at h1 h2
  rw [mobiusBundleRotate_eq_iff ν y y hx hx]
  exact rotate_fix_iff (fun h => h1 ((bundleBasePoint_eq_iff_fst hab).mpr h))
    (fun h => h2 ((bundleBasePoint_eq_iff_snd hab).mpr h)) ν

theorem mobiusBundleRotate_eq_self_iff_of_cone (y : mobiusBundleSet.{u})
    (h : mobiusBundleBase y = 3 / 2 ∨ mobiusBundleBase y = -(3 / 2)) (ν : Circle) :
    mobiusBundleRotate ν y = y ↔ ν ^ 4 = 1 := by
  obtain ⟨x, hx, hq⟩ := exists_sphere_rep y
  have hp := lensPair_ne_zero x
  have hab := sq_sub_sq_ne_zero_of_bundleQuartic_nonpos hp hq
  rw [mobiusBundleBase_eq hx] at h
  rw [mobiusBundleRotate_eq_iff ν y y hx hx]
  rcases h with h | h
  · have h1 := (bundleBasePoint_eq_iff_fst hab).mp h
    exact rotate_fix_iff_of_fst_eq_zero h1 (fun h2 => hp (Prod.ext h1 h2)) ν
  · have h2 := (bundleBasePoint_eq_iff_snd hab).mp h
    exact rotate_fix_iff_of_snd_eq_zero (fun h1 => hp (Prod.ext h1 h2)) h2 ν

theorem exists_mobiusBundleRotate_eq (y z : mobiusBundleSet.{u})
    (h : mobiusBundleBase y = mobiusBundleBase z) : ∃ ν : Circle, mobiusBundleRotate ν y = z := by
  obtain ⟨x, hx, hq⟩ := exists_sphere_rep y
  obtain ⟨x', hx', hq'⟩ := exists_sphere_rep z
  rw [mobiusBundleBase_eq hx, mobiusBundleBase_eq hx'] at h
  obtain ⟨ν, ε, hε, he⟩ := exists_rotate_of_bundleBasePoint_eq (norm_sq_lensPair_sphere x)
    (norm_sq_lensPair_sphere x')
    (sq_sub_sq_ne_zero_of_bundleQuartic_nonpos (lensPair_ne_zero x) hq)
    (sq_sub_sq_ne_zero_of_bundleQuartic_nonpos (lensPair_ne_zero x') hq') h
  exact ⟨ν, (mobiusBundleRotate_eq_iff ν y z hx hx').mpr ⟨ε, hε, he⟩⟩

theorem exists_mobiusBundleBase_eq (ζ : ℂ) (hζ : ‖ζ‖ ≤ 3) :
    ∃ y : mobiusBundleSet.{u}, mobiusBundleBase y = ζ := by
  have hsum : 0 < ‖ζ - 3 / 2‖ + ‖ζ + 3 / 2‖ := by
    have h := norm_sub_le (ζ + 3 / 2) (ζ - 3 / 2)
    have h3 : (ζ + 3 / 2) - (ζ - 3 / 2) = 3 := by ring
    rw [h3] at h
    norm_num at h
    linarith
  set s : ℝ := (‖ζ - 3 / 2‖ + ‖ζ + 3 / 2‖)⁻¹ with hsdef
  have hs : 0 < s := inv_pos.mpr hsum
  have hs' : (s : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hs.ne'
  obtain ⟨w₁, hw₁⟩ := IsAlgClosed.exists_pow_nat_eq ((s : ℂ) * (ζ - 3 / 2)) two_pos
  obtain ⟨w₂, hw₂⟩ := IsAlgClosed.exists_pow_nat_eq ((s : ℂ) * (ζ + 3 / 2)) two_pos
  have hn : ‖w₁‖ ^ 2 + ‖w₂‖ ^ 2 = 1 := by
    rw [← norm_pow, ← norm_pow, hw₁, hw₂, norm_mul, norm_mul, Complex.norm_real,
      Real.norm_of_nonneg hs.le, ← mul_add, hsdef, inv_mul_cancel₀ hsum.ne']
  have hv : lensPair.symm (w₁, w₂) ∈ sphere (0 : EuclideanSpace ℝ (Fin 4)) 1 := by
    rw [mem_sphere_zero_iff_norm]
    have h := norm_sq_eq_lensPair (lensPair.symm (w₁, w₂))
    rw [ContinuousLinearEquiv.apply_symm_apply] at h
    exact (pow_eq_one_iff_of_nonneg (norm_nonneg _) two_ne_zero).mp (h.trans hn)
  set x : sphere (0 : EuclideanSpace ℝ (Fin 4)) 1 := ⟨_, hv⟩ with hxdef
  have hx : lensPair x = (w₁, w₂) := lensPair.apply_symm_apply _
  have hden : (s : ℂ) * (ζ - 3 / 2) - (s : ℂ) * (ζ + 3 / 2) = -3 * s := by ring
  have hab : (lensPair x).1 ^ 2 - (lensPair x).2 ^ 2 ≠ 0 := by
    rw [hx]
    dsimp only
    rw [hw₁, hw₂, hden]
    exact mul_ne_zero (by norm_num) hs'
  have hJ : bundleBasePoint (lensPair x) = ζ := by
    rw [bundleBasePoint, hx]
    dsimp only
    rw [hw₁, hw₂, hden, div_eq_iff (mul_ne_zero (by norm_num) hs')]
    ring
  have hq : bundleQuartic (lensPair x) ≤ 0 :=
    (bundleQuartic_nonpos_iff hab).mpr (by rw [hJ]; exact hζ)
  exact ⟨⟨lensUp (mobiusLensGroup.projection x), hq⟩, hJ⟩

theorem lensUnitAction_one (p : ℂ × ℂ) : lensUnitAction 1 p = p := by
  simp [lensUnitAction]

theorem lensUnitAction_mul_circleI_sq (ε : Circle) (p : ℂ × ℂ) :
    lensUnitAction (ε * circleI ^ 2) p = -lensUnitAction ε p := by
  refine Prod.ext ?_ ?_ <;>
    simp only [lensUnitAction, Circle.coe_mul, Circle.coe_inv, Circle.coe_pow, coe_circleI,
      Complex.I_sq, mul_inv, inv_neg, inv_one, Prod.neg_mk] <;> ring

def joukowski (u : ℂ) : ℂ := 3 / 4 * (u + u⁻¹)

def modelAnnulusPoint (p : ℂ × ℂ) : ℂ := -(p.1 + p.2) / (p.1 - p.2)

def modelFibrePoint (p : ℂ × ℂ) : ℂ := (p.1 ^ 2 - p.2 ^ 2) / ‖p.1 ^ 2 - p.2 ^ 2‖

def modelPoint (p : ℂ × ℂ) : ℂ × ℂ := (modelFibrePoint p, modelAnnulusPoint p)

def modelDeck (q : ℂ × ℂ) : ℂ × ℂ := (-q.1, q.2⁻¹)

theorem sub_ne_zero_of_sq_sub_sq_ne_zero {p : ℂ × ℂ} (hab : p.1 ^ 2 - p.2 ^ 2 ≠ 0) :
    p.1 - p.2 ≠ 0 ∧ p.1 + p.2 ≠ 0 :=
  ⟨fun h => hab (by rw [sq_sub_sq, h, mul_zero]), fun h => hab (by rw [sq_sub_sq, h, zero_mul])⟩

theorem joukowski_modelAnnulusPoint {p : ℂ × ℂ} (hab : p.1 ^ 2 - p.2 ^ 2 ≠ 0) :
    joukowski (modelAnnulusPoint p) = bundleBasePoint p := by
  obtain ⟨h1, h2⟩ := sub_ne_zero_of_sq_sub_sq_ne_zero hab
  rw [joukowski, modelAnnulusPoint, bundleBasePoint, inv_div, div_neg, neg_div]
  field_simp
  ring

theorem modelAnnulusPoint_eq_one_iff {p : ℂ × ℂ} (hab : p.1 ^ 2 - p.2 ^ 2 ≠ 0) :
    modelAnnulusPoint p = 1 ↔ p.1 = 0 := by
  obtain ⟨h1, -⟩ := sub_ne_zero_of_sq_sub_sq_ne_zero hab
  rw [modelAnnulusPoint, div_eq_one_iff_eq h1]
  constructor
  · intro h
    linear_combination -h / 2
  · intro h
    rw [h]
    ring

theorem modelAnnulusPoint_eq_neg_one_iff {p : ℂ × ℂ} (hab : p.1 ^ 2 - p.2 ^ 2 ≠ 0) :
    modelAnnulusPoint p = -1 ↔ p.2 = 0 := by
  obtain ⟨h1, -⟩ := sub_ne_zero_of_sq_sub_sq_ne_zero hab
  rw [modelAnnulusPoint, div_eq_iff h1]
  constructor
  · intro h
    linear_combination -h / 2
  · intro h
    rw [h]
    ring

theorem modelPoint_lensUnitAction_of_sq_eq_one {ε : Circle} (hε : (ε : ℂ) ^ 2 = 1)
    (p : ℂ × ℂ) : modelPoint (lensUnitAction ε p) = modelPoint p := by
  have hne : (ε : ℂ) ≠ 0 := Circle.coe_ne_zero ε
  have hinv : ((ε⁻¹ : Circle) : ℂ) = ε := by
    rw [Circle.coe_inv]
    exact inv_eq_of_mul_eq_one_right (by rw [← sq, hε])
  have hd : (lensUnitAction ε p).1 ^ 2 - (lensUnitAction ε p).2 ^ 2 = p.1 ^ 2 - p.2 ^ 2 := by
    simp only [lensUnitAction, hinv]
    linear_combination (p.1 ^ 2 - p.2 ^ 2) * hε
  refine Prod.ext ?_ ?_
  · simp only [modelPoint, modelFibrePoint, hd]
  · simp only [modelPoint, modelAnnulusPoint, lensUnitAction, hinv, ← mul_add, ← mul_sub]
    rw [← mul_neg, mul_div_mul_left _ _ hne]

theorem modelPoint_lensUnitAction_of_sq_eq_neg_one {ε : Circle} (hε : (ε : ℂ) ^ 2 = -1)
    (p : ℂ × ℂ) : modelPoint (lensUnitAction ε p) = modelDeck (modelPoint p) := by
  have hne : (ε : ℂ) ≠ 0 := Circle.coe_ne_zero ε
  have hinv : ((ε⁻¹ : Circle) : ℂ) = -ε := by
    rw [Circle.coe_inv]
    exact inv_eq_of_mul_eq_one_right (by rw [mul_neg, ← sq, hε, neg_neg])
  have hd : (lensUnitAction ε p).1 ^ 2 - (lensUnitAction ε p).2 ^ 2 =
      -(p.1 ^ 2 - p.2 ^ 2) := by
    simp only [lensUnitAction, hinv]
    linear_combination (p.1 ^ 2 - p.2 ^ 2) * hε
  refine Prod.ext ?_ ?_
  · simp only [modelPoint, modelDeck, modelFibrePoint, hd, norm_neg, neg_div]
  · simp only [modelPoint, modelDeck, modelAnnulusPoint, lensUnitAction, hinv]
    rw [inv_div, div_neg, neg_div, neg_mul, sub_neg_eq_add, ← sub_eq_add_neg, ← mul_add,
      ← mul_sub, mul_div_mul_left _ _ hne]

theorem sq_eq_one_or_neg_one {ε : Circle} (hε : ε ^ 4 = 1) :
    (ε : ℂ) ^ 2 = 1 ∨ (ε : ℂ) ^ 2 = -1 := by
  have h4 : ((ε : ℂ) ^ 2) ^ 2 = 1 ^ 2 := by
    rw [← pow_mul, one_pow, ← Circle.coe_pow, hε, Circle.coe_one]
  exact sq_eq_sq_iff_eq_or_eq_neg.mp h4

theorem eq_or_eq_neg_of_modelPoint_eq {p q : ℂ × ℂ}
    (hpn : ‖p.1‖ ^ 2 + ‖p.2‖ ^ 2 = 1) (hqn : ‖q.1‖ ^ 2 + ‖q.2‖ ^ 2 = 1)
    (hp : p.1 ^ 2 - p.2 ^ 2 ≠ 0) (hq : q.1 ^ 2 - q.2 ^ 2 ≠ 0)
    (h : modelPoint q = modelPoint p) : q = p ∨ q = -p := by
  obtain ⟨hp1, -⟩ := sub_ne_zero_of_sq_sub_sq_ne_zero hp
  obtain ⟨hq1, -⟩ := sub_ne_zero_of_sq_sub_sq_ne_zero hq
  have ha := congrArg Prod.snd h
  have hf := congrArg Prod.fst h
  simp only [modelPoint, modelAnnulusPoint] at ha
  rw [div_eq_div_iff hq1 hp1] at ha
  have hc : q.1 * p.2 = p.1 * q.2 := by linear_combination ha / 2
  have hp0 : p.1 ≠ 0 ∨ p.2 ≠ 0 := by
    by_contra hcon
    rw [not_or, not_not, not_not] at hcon
    exact hp (by rw [hcon.1, hcon.2]; ring)
  obtain ⟨k, hk1, hk2⟩ := exists_scalar_of_cross hp0 hc
  have hk : ‖k‖ ^ 2 = 1 := by
    have h3 : ‖k‖ ^ 2 * (‖p.1‖ ^ 2 + ‖p.2‖ ^ 2) = 1 := by
      rw [← hqn, hk1, hk2, norm_mul, norm_mul, mul_pow, mul_pow, mul_add]
    rwa [hpn, mul_one] at h3
  have hd : q.1 ^ 2 - q.2 ^ 2 = k ^ 2 * (p.1 ^ 2 - p.2 ^ 2) := by
    rw [hk1, hk2]
    ring
  have hk2' : k ^ 2 = 1 := by
    simp only [modelPoint, modelFibrePoint] at hf
    rw [hd, norm_mul, norm_pow, hk, one_mul] at hf
    have hn : (‖p.1 ^ 2 - p.2 ^ 2‖ : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (norm_ne_zero_iff.mpr hp)
    rw [div_left_inj' hn] at hf
    exact mul_right_cancel₀ hp (by rw [hf, one_mul])
  rcases sq_eq_sq_iff_eq_or_eq_neg.mp (hk2'.trans (one_pow 2).symm) with hk' | hk'
  · left
    exact Prod.ext (by rw [hk1, hk', one_mul]) (by rw [hk2, hk', one_mul])
  · right
    exact Prod.ext (by rw [hk1, hk', neg_one_mul]; rfl) (by rw [hk2, hk', neg_one_mul]; rfl)

theorem projection_eq_iff_modelPoint (x y : sphere (0 : EuclideanSpace ℝ (Fin 4)) 1)
    (hx : bundleQuartic (lensPair x) ≤ 0) (hy : bundleQuartic (lensPair y) ≤ 0) :
    mobiusLensGroup.projection x = mobiusLensGroup.projection y ↔
      modelPoint (lensPair y) = modelPoint (lensPair x) ∨
        modelPoint (lensPair y) = modelDeck (modelPoint (lensPair x)) := by
  rw [projection_eq_projection_iff]
  have hxab := sq_sub_sq_ne_zero_of_bundleQuartic_nonpos (lensPair_ne_zero x) hx
  have hyab := sq_sub_sq_ne_zero_of_bundleQuartic_nonpos (lensPair_ne_zero y) hy
  constructor
  · rintro ⟨ε, hε, h⟩
    rw [h]
    rcases sq_eq_one_or_neg_one hε with h2 | h2
    · exact Or.inl (modelPoint_lensUnitAction_of_sq_eq_one h2 _)
    · exact Or.inr (modelPoint_lensUnitAction_of_sq_eq_neg_one h2 _)
  · have key : ∀ ε : Circle, ε ^ 4 = 1 →
        modelPoint (lensPair y) = modelPoint (lensUnitAction ε (lensPair x)) →
          ∃ ε' : Circle, ε' ^ 4 = 1 ∧ lensPair y = lensUnitAction ε' (lensPair x) := by
      intro ε hε he
      have hn : ‖(lensUnitAction ε (lensPair x)).1‖ ^ 2 +
          ‖(lensUnitAction ε (lensPair x)).2‖ ^ 2 = 1 := by
        simp only [lensUnitAction, norm_mul, Circle.norm_coe, one_mul]
        exact norm_sq_lensPair_sphere x
      have hq : bundleQuartic (lensUnitAction ε (lensPair x)) ≤ 0 := by
        rwa [bundleQuartic_lensUnitAction hε]
      rcases eq_or_eq_neg_of_modelPoint_eq hn (norm_sq_lensPair_sphere y)
          (sq_sub_sq_ne_zero_of_bundleQuartic_nonpos
            (fun h0 => lensPair_ne_zero x (by
              have h1 := congrArg Prod.fst h0
              have h2 := congrArg Prod.snd h0
              simp only [lensUnitAction, Prod.fst_zero, Prod.snd_zero, mul_eq_zero,
                Circle.coe_ne_zero, false_or] at h1 h2
              exact Prod.ext h1 h2)) hq) hyab he with h | h
      · exact ⟨ε, hε, h⟩
      · refine ⟨ε * circleI ^ 2, ?_, by rw [lensUnitAction_mul_circleI_sq, h]⟩
        rw [mul_pow, hε, one_mul, ← pow_mul, show 2 * 4 = 4 * 2 from rfl, pow_mul,
          circleI_pow_four, one_pow]
    rintro (h | h)
    · exact key 1 (one_pow _) (by rw [lensUnitAction_one, h])
    · refine key circleI circleI_pow_four ?_
      rw [h, modelPoint_lensUnitAction_of_sq_eq_neg_one (by rw [coe_circleI, Complex.I_sq])]

def pantsFibrePoint (p : ℂ × ℂ) : ℂ := p.1 * p.2 / ‖p.1 * p.2‖

theorem pantsFibrePoint_lensUnitAction (ε : Circle) (p : ℂ × ℂ) :
    pantsFibrePoint (lensUnitAction ε p) = pantsFibrePoint p := by
  have h : (lensUnitAction ε p).1 * (lensUnitAction ε p).2 = p.1 * p.2 := by
    simp only [lensUnitAction, Circle.coe_inv]
    rw [mul_mul_mul_comm, mul_inv_cancel₀ (Circle.coe_ne_zero ε), one_mul]
  simp only [pantsFibrePoint, h]

theorem pantsFibrePoint_rotatePair (ν : Circle) (p : ℂ × ℂ) :
    pantsFibrePoint (rotatePair ν p) = (ν : ℂ) ^ 2 * pantsFibrePoint p := by
  have h : (rotatePair ν p).1 * (rotatePair ν p).2 = (ν : ℂ) ^ 2 * (p.1 * p.2) := by
    simp only [rotatePair]
    ring
  have hn : ‖(ν : ℂ) ^ 2‖ = 1 := by rw [norm_pow, Circle.norm_coe, one_pow]
  simp only [pantsFibrePoint, h, norm_mul, hn, one_mul, mul_div_assoc]

theorem norm_pantsFibrePoint {p : ℂ × ℂ} (h1 : p.1 ≠ 0) (h2 : p.2 ≠ 0) :
    ‖pantsFibrePoint p‖ = 1 := by
  have hm : ‖p.1 * p.2‖ ≠ 0 := norm_ne_zero_iff.mpr (mul_ne_zero h1 h2)
  rw [pantsFibrePoint, norm_div, Complex.norm_real, Real.norm_of_nonneg (norm_nonneg _),
    div_self hm]

def pantsFibre : mobiusLensGroup.Orbit → ℂ :=
  lensDescend pantsFibrePoint fun ε _ p => pantsFibrePoint_lensUnitAction ε p

def mobiusBundleFibre (y : mobiusBundleSet.{u}) : ℂ := pantsFibre (lensDown y.val)

theorem mobiusBundleFibre_eq {y : mobiusBundleSet.{u}} {x : sphere (0 : EuclideanSpace ℝ (Fin 4)) 1}
    (hx : lensDown y.val = mobiusLensGroup.projection x) :
    mobiusBundleFibre y = pantsFibrePoint (lensPair x) := by
  change pantsFibre (lensDown y.val) = _
  rw [hx]
  rfl

theorem mobiusBundleFibre_rotate (ν : Circle) (y : mobiusBundleSet.{u}) :
    mobiusBundleFibre (mobiusBundleRotate ν y) = (ν : ℂ) ^ 2 * mobiusBundleFibre y := by
  obtain ⟨x, hx, -⟩ := exists_sphere_rep y
  rw [mobiusBundleFibre_eq hx]
  change pantsFibre (lensDown (lensUp (bundleRotate ν (lensDown y.val)))) = _
  rw [lensDown_lensUp, hx, bundleRotate_projection]
  change pantsFibrePoint (lensPair (lensRotation ν x : EuclideanSpace ℝ (Fin 4))) = _
  rw [lensPair_lensRotation, pantsFibrePoint_rotatePair]

theorem fst_snd_ne_zero_of_base {y : mobiusBundleSet.{u}}
    {x : sphere (0 : EuclideanSpace ℝ (Fin 4)) 1}
    (hx : lensDown y.val = mobiusLensGroup.projection x) (hq : bundleQuartic (lensPair x) ≤ 0)
    (h1 : mobiusBundleBase y ≠ 3 / 2) (h2 : mobiusBundleBase y ≠ -(3 / 2)) :
    (lensPair x).1 ≠ 0 ∧ (lensPair x).2 ≠ 0 := by
  have hab := sq_sub_sq_ne_zero_of_bundleQuartic_nonpos (lensPair_ne_zero x) hq
  rw [mobiusBundleBase_eq hx] at h1 h2
  exact ⟨fun h => h1 ((bundleBasePoint_eq_iff_fst hab).mpr h),
    fun h => h2 ((bundleBasePoint_eq_iff_snd hab).mpr h)⟩

theorem norm_mobiusBundleFibre (y : mobiusBundleSet.{u}) (h1 : mobiusBundleBase y ≠ 3 / 2)
    (h2 : mobiusBundleBase y ≠ -(3 / 2)) : ‖mobiusBundleFibre y‖ = 1 := by
  obtain ⟨x, hx, hq⟩ := exists_sphere_rep y
  obtain ⟨hx1, hx2⟩ := fst_snd_ne_zero_of_base hx hq h1 h2
  rw [mobiusBundleFibre_eq hx]
  exact norm_pantsFibrePoint hx1 hx2

theorem eq_of_mobiusBundleBase_eq_of_fibre_eq (y z : mobiusBundleSet.{u})
    (h1 : mobiusBundleBase y ≠ 3 / 2) (h2 : mobiusBundleBase y ≠ -(3 / 2))
    (hb : mobiusBundleBase y = mobiusBundleBase z)
    (hf : mobiusBundleFibre y = mobiusBundleFibre z) :
    y = z := by
  obtain ⟨ν, rfl⟩ := exists_mobiusBundleRotate_eq y z hb
  have hn := norm_mobiusBundleFibre y h1 h2
  have hne : mobiusBundleFibre y ≠ 0 := by
    intro h0
    rw [h0, norm_zero] at hn
    exact zero_ne_one hn
  rw [mobiusBundleFibre_rotate] at hf
  have hν : (ν : ℂ) ^ 2 = 1 := mul_right_cancel₀ hne (by rw [← hf, one_mul])
  have hν' : ν ^ 2 = 1 := Circle.ext (by rw [Circle.coe_pow, hν, Circle.coe_one])
  exact ((mobiusBundleRotate_eq_self_iff y h1 h2 ν).mpr hν').symm

theorem exists_mobiusBundle_base_fibre (ζ μ : ℂ) (hζ : ‖ζ‖ ≤ 3) (h1 : ζ ≠ 3 / 2)
    (h2 : ζ ≠ -(3 / 2)) (hμ : ‖μ‖ = 1) :
    ∃ y : mobiusBundleSet.{u}, mobiusBundleBase y = ζ ∧ mobiusBundleFibre y = μ := by
  obtain ⟨y, hy⟩ := exists_mobiusBundleBase_eq.{u} ζ hζ
  have hn := norm_mobiusBundleFibre y (hy ▸ h1) (hy ▸ h2)
  have hne : mobiusBundleFibre y ≠ 0 := by
    intro h0
    rw [h0, norm_zero] at hn
    exact zero_ne_one hn
  obtain ⟨ν, hν⟩ := exists_circle_sq_eq (k := μ / mobiusBundleFibre y)
    (by rw [norm_div, hμ, hn, div_one])
  refine ⟨mobiusBundleRotate ν y, by rw [mobiusBundleBase_rotate, hy], ?_⟩
  rw [mobiusBundleFibre_rotate, hν, div_mul_cancel₀ _ hne]

def mobiusPants : Set mobiusBundleSet.{u} := {y | mobiusBundleBase y ∈ planarModel 3}

theorem planarModel_three_ne {ζ : ℂ} (hζ : ζ ∈ planarModel 3) :
    ‖ζ‖ ≤ 3 ∧ ζ ≠ 3 / 2 ∧ ζ ≠ -(3 / 2) := by
  rw [mem_planarModel_three] at hζ
  obtain ⟨h0, h1, h2⟩ := hζ
  refine ⟨h0, fun h => ?_, fun h => ?_⟩
  · rw [h] at h1
    norm_num at h1
  · rw [h] at h2
    norm_num at h2

def mobiusPantsCoordinates (y : mobiusPants.{u}) : planarModel 3 × Circle :=
  (⟨mobiusBundleBase y.val, y.2⟩, ⟨mobiusBundleFibre y.val, by
    obtain ⟨-, h1, h2⟩ := planarModel_three_ne y.2
    exact mem_sphere_zero_iff_norm.mpr (norm_mobiusBundleFibre y.val h1 h2)⟩)

theorem mobiusPantsCoordinates_bijective :
    Function.Bijective mobiusPantsCoordinates.{u} := by
  constructor
  · intro y z h
    obtain ⟨-, h1, h2⟩ := planarModel_three_ne y.2
    have hb := congrArg (fun q => (q.1 : ℂ)) h
    have hf := congrArg (fun q => ((q.2 : Circle) : ℂ)) h
    exact Subtype.ext (eq_of_mobiusBundleBase_eq_of_fibre_eq y.val z.val h1 h2 hb hf)
  · rintro ⟨ζ, μ⟩
    obtain ⟨h0, h1, h2⟩ := planarModel_three_ne ζ.2
    obtain ⟨y, hy, hμ⟩ := exists_mobiusBundle_base_fibre.{u} ζ (μ : ℂ) h0 h1 h2
      (Circle.norm_coe μ)
    refine ⟨⟨y, by change mobiusBundleBase y ∈ planarModel 3; rw [hy]; exact ζ.2⟩, ?_⟩
    exact Prod.ext (Subtype.ext hy) (Circle.ext hμ)

def mobiusPantsEquiv : mobiusPants.{u} ≃ planarModel 3 × Circle :=
  Equiv.ofBijective _ mobiusPantsCoordinates_bijective

theorem mobiusPantsCoordinates_rotate (ν : Circle) (y : mobiusPants.{u}) :
    mobiusPantsCoordinates ⟨mobiusBundleRotate ν y.val, by
      change mobiusBundleBase _ ∈ planarModel 3
      rw [mobiusBundleBase_rotate]
      exact y.2⟩ =
      ((mobiusPantsCoordinates y).1, ν ^ 2 * (mobiusPantsCoordinates y).2) := by
  refine Prod.ext (Subtype.ext (mobiusBundleBase_rotate ν y.val)) (Circle.ext ?_)
  change mobiusBundleFibre (mobiusBundleRotate ν y.val) = ((ν ^ 2 : Circle) : ℂ) * _
  rw [mobiusBundleFibre_rotate, Circle.coe_pow]
  rfl

theorem exists_sphere_modelPoint (z u : ℂ) (hz : ‖z‖ = 1) (hu : u ≠ 0)
    (hJ : ‖joukowski u‖ ≤ 3) :
    ∃ x : sphere (0 : EuclideanSpace ℝ (Fin 4)) 1,
      bundleQuartic (lensPair x) ≤ 0 ∧ modelPoint (lensPair x) = (z, u) := by
  have hsum : 0 < ‖u - 1‖ ^ 2 + ‖u + 1‖ ^ 2 := by
    have h := norm_sub_le (u + 1) (u - 1)
    have h2 : (u + 1) - (u - 1) = 2 := by ring
    rw [h2] at h
    norm_num at h
    refine lt_of_le_of_ne (by positivity) fun h0 => ?_
    have h3 : ‖u - 1‖ ^ 2 = 0 := by linarith [sq_nonneg ‖u - 1‖, sq_nonneg ‖u + 1‖]
    have h4 : ‖u + 1‖ ^ 2 = 0 := by linarith [sq_nonneg ‖u - 1‖, sq_nonneg ‖u + 1‖]
    rw [pow_eq_zero_iff two_ne_zero] at h3 h4
    linarith
  set r : ℝ := (Real.sqrt (‖u - 1‖ ^ 2 + ‖u + 1‖ ^ 2))⁻¹ with hrdef
  have hr : 0 < r := inv_pos.mpr (Real.sqrt_pos.mpr hsum)
  have hr2 : r ^ 2 * (‖u - 1‖ ^ 2 + ‖u + 1‖ ^ 2) = 1 := by
    rw [hrdef, inv_pow, Real.sq_sqrt hsum.le, inv_mul_cancel₀ hsum.ne']
  have hun : ‖u‖ ≠ 0 := norm_ne_zero_iff.mpr hu
  obtain ⟨κ, hκ⟩ := exists_circle_sq_eq (k := -z * conj u / ‖u‖) (by
    rw [norm_div, norm_mul, norm_neg, hz, Complex.norm_conj, one_mul, Complex.norm_real,
      Real.norm_of_nonneg (norm_nonneg _), div_self hun])
  obtain ⟨c, hcdef⟩ : ∃ c : ℂ, c = (r : ℂ) * κ := ⟨_, rfl⟩
  have hc : c ≠ 0 := by
    rw [hcdef]
    exact mul_ne_zero (Complex.ofReal_ne_zero.mpr hr.ne') (Circle.coe_ne_zero κ)
  have hcn : ‖c‖ = r := by
    rw [hcdef, norm_mul, Circle.norm_coe, mul_one, Complex.norm_real, Real.norm_of_nonneg hr.le]
  have hn : ‖c * (u - 1)‖ ^ 2 + ‖c * (u + 1)‖ ^ 2 = 1 := by
    rw [norm_mul, norm_mul, hcn, mul_pow, mul_pow, ← mul_add, hr2]
  have hv : lensPair.symm (c * (u - 1), c * (u + 1)) ∈ sphere (0 : EuclideanSpace ℝ (Fin 4)) 1 := by
    rw [mem_sphere_zero_iff_norm]
    have h := norm_sq_eq_lensPair (lensPair.symm (c * (u - 1), c * (u + 1)))
    rw [ContinuousLinearEquiv.apply_symm_apply] at h
    exact (pow_eq_one_iff_of_nonneg (norm_nonneg _) two_ne_zero).mp (h.trans hn)
  set x : sphere (0 : EuclideanSpace ℝ (Fin 4)) 1 := ⟨_, hv⟩ with hxdef
  have hx : lensPair x = (c * (u - 1), c * (u + 1)) := lensPair.apply_symm_apply _
  have hd : (c * (u - 1)) ^ 2 - (c * (u + 1)) ^ 2 = -4 * c ^ 2 * u := by ring
  have hab : (lensPair x).1 ^ 2 - (lensPair x).2 ^ 2 ≠ 0 := by
    rw [hx]
    dsimp only
    rw [hd]
    exact mul_ne_zero (mul_ne_zero (by norm_num) (pow_ne_zero 2 hc)) hu
  have hA : modelAnnulusPoint (lensPair x) = u := by
    have h2c : c * (u - 1) - c * (u + 1) = -2 * c := by ring
    rw [modelAnnulusPoint, hx]
    dsimp only
    rw [h2c, div_eq_iff (mul_ne_zero (by norm_num) hc)]
    ring
  have hF : modelFibrePoint (lensPair x) = z := by
    have hun' : ((‖u‖ : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hun
    have hκ' : (κ : ℂ) ^ 2 * ((‖u‖ : ℝ) : ℂ) = -z * conj u := by
      rw [hκ, div_mul_cancel₀ _ hun']
    have huu : conj u * u = ((‖u‖ : ℝ) : ℂ) ^ 2 := Complex.conj_mul' u
    have hnorm : ‖(c * (u - 1)) ^ 2 - (c * (u + 1)) ^ 2‖ = 4 * r ^ 2 * ‖u‖ := by
      rw [hd, norm_mul, norm_mul, norm_neg, norm_pow, hcn]
      norm_num
    have hne4 : (((4 * r ^ 2 * ‖u‖ : ℝ)) : ℂ) ≠ 0 :=
      Complex.ofReal_ne_zero.mpr (mul_ne_zero (mul_ne_zero (by norm_num) (pow_ne_zero 2 hr.ne'))
        hun)
    rw [modelFibrePoint, hx]
    dsimp only
    rw [hnorm, div_eq_iff hne4, hd, hcdef]
    push_cast
    apply mul_right_cancel₀ hun'
    linear_combination (-4 * (r : ℂ) ^ 2 * u) * hκ' + (4 * (r : ℂ) ^ 2 * z) * huu
  have hq : bundleQuartic (lensPair x) ≤ 0 := by
    rw [bundleQuartic_nonpos_iff hab, ← joukowski_modelAnnulusPoint hab, hA]
    exact hJ
  exact ⟨x, hq, Prod.ext hF hA⟩

theorem contMDiffAt_lensDescend {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {f : ℂ × ℂ → F} (hf : ∀ ε : Circle, ε ^ 4 = 1 → ∀ p, f (lensUnitAction ε p) = f p)
    (x : sphere (0 : EuclideanSpace ℝ (Fin 4)) 1) (hs : ContDiffAt ℝ ∞ f (lensPair x)) :
    ContMDiffAt (𝓡 3) 𝓘(ℝ, F) ∞ (lensDescend f hf) (mobiusLensGroup.projection x) := by
  have hl := mobiusLensGroup.projection_isLocalDiffeomorph x
  have hc : ContMDiffAt (𝓡 3) 𝓘(ℝ, F) ∞
      (fun y : sphere (0 : EuclideanSpace ℝ (Fin 4)) 1 => f (lensPair y))
      (hl.localInverse (mobiusLensGroup.projection x)) := by
    rw [hl.localInverse_left_inv hl.localInverse_mem_target]
    exact (hs.comp (x : EuclideanSpace ℝ (Fin 4)) lensPair.contDiff.contDiffAt).contMDiffAt.comp
      x (contMDiff_coe_sphere x)
  have h := hc.comp (mobiusLensGroup.projection x) hl.contMDiffAt_localInverse
  apply h.congr_of_eventuallyEq
  filter_upwards [hl.localInverse_eventuallyEq_right] with q hq
  change lensDescend f hf q = lensDescend f hf (mobiusLensGroup.projection (hl.localInverse q))
  rw [show mobiusLensGroup.projection (hl.localInverse q) = q from hq]

theorem contDiffAt_bundleBasePoint {p : ℂ × ℂ} (hab : p.1 ^ 2 - p.2 ^ 2 ≠ 0) :
    ContDiffAt ℝ ∞ bundleBasePoint p := by
  have he : bundleBasePoint =
      (fun q : ℂ × ℂ => -(3 / 2) * (q.1 ^ 2 + q.2 ^ 2)) * (fun q : ℂ × ℂ => q.1 ^ 2 - q.2 ^ 2)⁻¹ :=
    funext fun q => div_eq_mul_inv _ _
  rw [he]
  exact (contDiffAt_const.mul ((contDiffAt_fst.pow 2).add (contDiffAt_snd.pow 2))).mul
    (((contDiffAt_fst.pow 2).sub (contDiffAt_snd.pow 2)).inv hab)

theorem contDiffAt_pantsFibrePoint {p : ℂ × ℂ} (h : p.1 * p.2 ≠ 0) :
    ContDiffAt ℝ ∞ pantsFibrePoint p := by
  have he : pantsFibrePoint = (fun q : ℂ × ℂ => q.1 * q.2) *
      (fun q : ℂ × ℂ => ((‖q.1 * q.2‖ : ℝ) : ℂ))⁻¹ :=
    funext fun q => div_eq_mul_inv _ _
  rw [he]
  have hm : ContDiffAt ℝ ∞ (fun q : ℂ × ℂ => q.1 * q.2) p := contDiffAt_fst.mul contDiffAt_snd
  have hnorm : ContDiffAt ℝ ∞ (norm : ℂ → ℝ) (p.1 * p.2) := contDiffAt_norm ℝ h
  have hn' : ContDiffAt ℝ ∞ (fun q : ℂ × ℂ => ‖q.1 * q.2‖) p := hnorm.comp p hm
  have hn : ContDiffAt ℝ ∞ (fun q : ℂ × ℂ => ((‖q.1 * q.2‖ : ℝ) : ℂ)) p :=
    Complex.ofRealCLM.contDiff.contDiffAt.comp p hn'
  exact hm.mul (hn.inv (Complex.ofReal_ne_zero.mpr (norm_ne_zero_iff.mpr h)))

theorem contMDiff_mobiusBundleBase : ContMDiff (𝓡∂ 3) 𝓘(ℝ, ℂ) ∞ mobiusBundleBase.{u} := by
  intro y
  obtain ⟨x, hx, hq⟩ := exists_sphere_rep y
  have h := contMDiffAt_lensDescend (fun _ hε p => bundleBasePoint_lensUnitAction hε p) x
    (contDiffAt_bundleBasePoint
    (sq_sub_sq_ne_zero_of_bundleQuartic_nonpos (lensPair_ne_zero x) hq))
  rw [← hx] at h
  exact h.comp y (contMDiff_lensDown.comp mobiusBundleAtlas.contMDiff_subtype_val).contMDiffAt

theorem contMDiffAt_mobiusBundleFibre (y : mobiusBundleSet.{u}) (h1 : mobiusBundleBase y ≠ 3 / 2)
    (h2 : mobiusBundleBase y ≠ -(3 / 2)) :
    ContMDiffAt (𝓡∂ 3) 𝓘(ℝ, ℂ) ∞ mobiusBundleFibre.{u} y := by
  obtain ⟨x, hx, hq⟩ := exists_sphere_rep y
  obtain ⟨hx1, hx2⟩ := fst_snd_ne_zero_of_base hx hq h1 h2
  have h := contMDiffAt_lensDescend (fun ε _ p => pantsFibrePoint_lensUnitAction ε p) x
    (contDiffAt_pantsFibrePoint (mul_ne_zero hx1 hx2))
  rw [← hx] at h
  exact h.comp y (contMDiff_lensDown.comp mobiusBundleAtlas.contMDiff_subtype_val).contMDiffAt

theorem bundleQuartic_eq_zero_iff {p : ℂ × ℂ} (hab : p.1 ^ 2 - p.2 ^ 2 ≠ 0) :
    bundleQuartic p = 0 ↔ ‖bundleBasePoint p‖ = 3 := by
  have hpos : 0 < ‖p.1 ^ 2 - p.2 ^ 2‖ := norm_pos_iff.mpr hab
  have hJ : ‖bundleBasePoint p‖ = 3 / 2 * ‖p.1 ^ 2 + p.2 ^ 2‖ / ‖p.1 ^ 2 - p.2 ^ 2‖ := by
    rw [bundleBasePoint, norm_div, norm_mul, norm_neg]
    norm_num
  rw [hJ, div_eq_iff hpos.ne', bundleQuartic, sub_eq_zero]
  have hA := norm_nonneg (p.1 ^ 2 + p.2 ^ 2)
  constructor
  · intro h
    nlinarith
  · intro h
    nlinarith

theorem mobiusBundleSet_isBoundaryPoint_iff_base (y : mobiusBundleSet.{u}) :
    (𝓡∂ 3).IsBoundaryPoint y ↔ ‖mobiusBundleBase y‖ = 3 := by
  obtain ⟨x, hx, hq⟩ := exists_sphere_rep y
  rw [mobiusBundleSet_isBoundaryPoint_iff, mobiusBundleBase_eq hx]
  change lensDescend bundleQuartic bundleQuartic_invariant (lensDown y.val) = 0 ↔ _
  rw [hx]
  exact bundleQuartic_eq_zero_iff
    (sq_sub_sq_ne_zero_of_bundleQuartic_nonpos (lensPair_ne_zero x) hq)

end GC.Seifert
