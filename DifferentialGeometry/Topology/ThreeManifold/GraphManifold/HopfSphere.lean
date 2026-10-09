import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.SphereProduct
import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.CliffordCoordinates

set_option autoImplicit false

/-!
# The Hopf fibration of the three-sphere

Writing points of the standard three-sphere as pairs `(z₁, z₂)` of complex numbers
(`sphereFirst`, `sphereSecond`), the Hopf map `hopfMap` sends `(z₁, z₂)` to the point of the
unit sphere of `ℝ³` with plane coordinate `2 z₁ z̄₂` and height `‖z₁‖² - ‖z₂‖²`. It is smooth
and surjective, and its fibres are the circle orbits `(w z₁, w z₂)` (`hopfMap_eq_iff`).

Over the complement of the south pole (`hopfUpper`, where `z₁ ≠ 0`) and of the north pole
(`hopfLower`, where `z₂ ≠ 0`) the Hopf map is trivialized by the phase of `z₁`, resp. `z₂`;
the inverse diffeomorphisms are written explicitly (`hopfUpperPoint`, `hopfLowerPoint`). This
gives the circle fibration `hopfCircleFibration` of the whole sphere over the universe-lifted
two-sphere `sphereTwoSurfaceLift`, and hence the one-piece raw graph presentation
`standardThreeSphereLiftHopfRawGraphPresentation` with no tori.
-/

noncomputable section
open Function Metric ComplexConjugate
open DifferentialGeometry DifferentialGeometry.Topology GC.Endpoint
open scoped Manifold ContDiff Topology

namespace GC.GraphManifold
universe u

private theorem fact_finrank_euclideanSpace_three :
    Fact (Module.finrank ℝ (EuclideanSpace ℝ (Fin 3)) = 2 + 1) :=
  ⟨finrank_euclideanSpace_fin⟩

attribute [local instance] uliftChartedSpace isManifold_ulift finrank_real_complex_fact'
  fact_finrank_euclideanSpace_three

def planeHeightCoordinates : EuclideanSpace ℝ (Fin 3) ≃L[ℝ] ℂ × ℝ :=
  LinearEquiv.toContinuousLinearEquiv
    { toFun := fun x => (⟨x 0, x 1⟩, x 2)
      invFun := fun p => !₂[p.1.re, p.1.im, p.2]
      map_add' := fun x y => by
        refine Prod.ext (Complex.ext ?_ ?_) ?_ <;> simp
      map_smul' := fun c x => by
        refine Prod.ext (Complex.ext ?_ ?_) ?_ <;> simp
      left_inv := fun x => by ext i; fin_cases i <;> simp
      right_inv := fun p => by ext <;> simp }

theorem planeHeightCoordinates_apply (x : EuclideanSpace ℝ (Fin 3)) :
    planeHeightCoordinates x = (⟨x 0, x 1⟩, x 2) := rfl

theorem norm_sq_eq_planeHeightCoordinates (x : EuclideanSpace ℝ (Fin 3)) :
    ‖x‖ ^ 2 = ‖(planeHeightCoordinates x).1‖ ^ 2 + (planeHeightCoordinates x).2 ^ 2 := by
  rw [EuclideanSpace.norm_sq_eq, Fin.sum_univ_three, Complex.sq_norm,
    planeHeightCoordinates_apply, Complex.normSq_apply]
  simp only [Real.norm_eq_abs, sq_abs]
  ring

theorem planeHeightCoordinates_symm_mem_sphere {w : ℂ} {t : ℝ} (h : ‖w‖ ^ 2 + t ^ 2 = 1) :
    planeHeightCoordinates.symm (w, t) ∈ sphere (0 : EuclideanSpace ℝ (Fin 3)) 1 := by
  rw [mem_sphere_zero_iff_norm]
  have hsq : ‖planeHeightCoordinates.symm (w, t)‖ ^ 2 = 1 := by
    rw [norm_sq_eq_planeHeightCoordinates, ContinuousLinearEquiv.apply_symm_apply]
    exact h
  exact (pow_eq_one_iff_of_nonneg (norm_nonneg _) two_ne_zero).mp hsq

abbrev SphereTwoLift : Type u := ULift.{u} (sphere (0 : EuclideanSpace ℝ (Fin 3)) 1)

def sphereTwoSurfaceLift : CompactSurface.{u} where
  kind := .closed
  Carrier := SphereTwoLift.{u}
  charts := uliftChartedSpace _ _
  smooth := isManifold_ulift (𝓡 2) _
  connected := Homeomorph.ulift.connectedSpace_iff.mpr sphereTwoSurface.connected

@[simp]
theorem sphereTwoSurfaceLift_carrier : sphereTwoSurfaceLift.{u}.Carrier = SphereTwoLift.{u} :=
  rfl

def sphereTwoPlane (b : SphereTwoLift.{u}) : ℂ :=
  (planeHeightCoordinates (b.down : EuclideanSpace ℝ (Fin 3))).1

def sphereTwoHeight (b : SphereTwoLift.{u}) : ℝ :=
  (planeHeightCoordinates (b.down : EuclideanSpace ℝ (Fin 3))).2

theorem norm_sphereTwoPlane_sq_add (b : SphereTwoLift.{u}) :
    ‖sphereTwoPlane b‖ ^ 2 + sphereTwoHeight b ^ 2 = 1 := by
  rw [sphereTwoPlane, sphereTwoHeight, ← norm_sq_eq_planeHeightCoordinates,
    mem_sphere_zero_iff_norm.mp b.down.2, one_pow]

theorem neg_one_le_sphereTwoHeight (b : SphereTwoLift.{u}) : -1 ≤ sphereTwoHeight b := by
  nlinarith [norm_sphereTwoPlane_sq_add b, sq_nonneg ‖sphereTwoPlane b‖]

theorem sphereTwoHeight_le_one (b : SphereTwoLift.{u}) : sphereTwoHeight b ≤ 1 := by
  nlinarith [norm_sphereTwoPlane_sq_add b, sq_nonneg ‖sphereTwoPlane b‖]

theorem sphereTwoLift_ext {b c : SphereTwoLift.{u}} (h₁ : sphereTwoPlane b = sphereTwoPlane c)
    (h₂ : sphereTwoHeight b = sphereTwoHeight c) : b = c :=
  ULift.ext (Subtype.ext (planeHeightCoordinates.injective (Prod.ext h₁ h₂)))

def sphereTwoOfPair (w : ℂ) (t : ℝ) (h : ‖w‖ ^ 2 + t ^ 2 = 1) : SphereTwoLift.{u} :=
  ULift.up ⟨planeHeightCoordinates.symm (w, t), planeHeightCoordinates_symm_mem_sphere h⟩

@[simp] theorem sphereTwoPlane_sphereTwoOfPair (w : ℂ) (t : ℝ) (h : ‖w‖ ^ 2 + t ^ 2 = 1) :
    sphereTwoPlane (sphereTwoOfPair.{u} w t h) = w := by
  rw [sphereTwoPlane, sphereTwoOfPair, ContinuousLinearEquiv.apply_symm_apply]

@[simp] theorem sphereTwoHeight_sphereTwoOfPair (w : ℂ) (t : ℝ) (h : ‖w‖ ^ 2 + t ^ 2 = 1) :
    sphereTwoHeight (sphereTwoOfPair.{u} w t h) = t := by
  rw [sphereTwoHeight, sphereTwoOfPair, ContinuousLinearEquiv.apply_symm_apply]

theorem contMDiff_sphereTwoDown : ContMDiff (𝓡 2) 𝓘(ℝ, EuclideanSpace ℝ (Fin 3)) ∞
    (fun b : SphereTwoLift.{u} => (b.down : EuclideanSpace ℝ (Fin 3))) :=
  contMDiff_coe_sphere.comp
    (uliftDiffeomorph (𝓡 2) (sphere (0 : EuclideanSpace ℝ (Fin 3)) 1)).symm.contMDiff

theorem contMDiff_sphereTwoPlane : ContMDiff (𝓡 2) 𝓘(ℝ, ℂ) ∞ sphereTwoPlane.{u} :=
  ((ContinuousLinearMap.fst ℝ ℂ ℝ).comp
    (planeHeightCoordinates : EuclideanSpace ℝ (Fin 3) →L[ℝ] ℂ × ℝ)).contDiff.contMDiff.comp
    contMDiff_sphereTwoDown

theorem contMDiff_sphereTwoHeight : ContMDiff (𝓡 2) 𝓘(ℝ, ℝ) ∞ sphereTwoHeight.{u} :=
  ((ContinuousLinearMap.snd ℝ ℂ ℝ).comp
    (planeHeightCoordinates : EuclideanSpace ℝ (Fin 3) →L[ℝ] ℂ × ℝ)).contDiff.contMDiff.comp
    contMDiff_sphereTwoDown

theorem contMDiff_of_sphereTwoPlane_sphereTwoHeight {F G X : Type*} [NormedAddCommGroup F]
    [NormedSpace ℝ F] [TopologicalSpace G] {J : ModelWithCorners ℝ F G} [TopologicalSpace X]
    [ChartedSpace G X] [IsManifold J ∞ X] {g : X → SphereTwoLift.{u}}
    (h₁ : ContMDiff J 𝓘(ℝ, ℂ) ∞ (fun x => sphereTwoPlane (g x)))
    (h₂ : ContMDiff J 𝓘(ℝ, ℝ) ∞ (fun x => sphereTwoHeight (g x))) :
    ContMDiff J (𝓡 2) ∞ g := by
  have hval : ContMDiff J 𝓘(ℝ, EuclideanSpace ℝ (Fin 3)) ∞
      (fun x => ((g x).down : EuclideanSpace ℝ (Fin 3))) := by
    have heq : (fun x => ((g x).down : EuclideanSpace ℝ (Fin 3))) =
        fun x => planeHeightCoordinates.symm (sphereTwoPlane (g x), sphereTwoHeight (g x)) := by
      funext x
      exact (planeHeightCoordinates.symm_apply_apply _).symm
    rw [heq]
    exact planeHeightCoordinates.symm.contDiff.contMDiff.comp (h₁.prodMk_space h₂)
  exact (uliftDiffeomorph (𝓡 2) (sphere (0 : EuclideanSpace ℝ (Fin 3)) 1)).contMDiff.comp
    (hval.codRestrict_sphere (n := 2) fun x => (g x).down.2)

def hopfPlane (p : SphereCarrier.{u}) : ℂ := 2 * (sphereFirst p * conj (sphereSecond p))

theorem norm_hopfPlane_sq_add (p : SphereCarrier.{u}) :
    ‖hopfPlane p‖ ^ 2 + cliffordHeight p ^ 2 = 1 := by
  have h := norm_sphereFirst_sq_add p
  rw [hopfPlane, cliffordHeight, norm_mul, norm_mul, Complex.norm_conj, Complex.norm_two]
  linear_combination (‖sphereFirst p‖ ^ 2 + ‖sphereSecond p‖ ^ 2 + 1) * h

def hopfMap (p : SphereCarrier.{u}) : SphereTwoLift.{u} :=
  sphereTwoOfPair (hopfPlane p) (cliffordHeight p) (norm_hopfPlane_sq_add p)

@[simp] theorem sphereTwoPlane_hopfMap (p : SphereCarrier.{u}) :
    sphereTwoPlane (hopfMap p) = hopfPlane p :=
  sphereTwoPlane_sphereTwoOfPair _ _ _

@[simp] theorem sphereTwoHeight_hopfMap (p : SphereCarrier.{u}) :
    sphereTwoHeight (hopfMap p) = cliffordHeight p :=
  sphereTwoHeight_sphereTwoOfPair _ _ _

theorem contMDiff_hopfPlane : ContMDiff (𝓡 3) 𝓘(ℝ, ℂ) ∞ hopfPlane.{u} :=
  ((contDiff_const (c := (2 : ℂ))).mul contDiff_id).contMDiff.comp
    ((contDiff_mul (𝕜 := ℝ) (𝔸 := ℂ)).contMDiff.comp (contMDiff_sphereFirst.prodMk_space
      (Complex.conjCLE.contDiff.contMDiff.comp contMDiff_sphereSecond)))

theorem contMDiff_hopfMap : ContMDiff (𝓡 3) (𝓡 2) ∞ hopfMap.{u} :=
  contMDiff_of_sphereTwoPlane_sphereTwoHeight
    (by simpa only [sphereTwoPlane_hopfMap] using contMDiff_hopfPlane)
    (by simpa only [sphereTwoHeight_hopfMap] using contMDiff_cliffordHeight)


def hopfUpperRadius (t : ℝ) : ℝ := √((1 + t) / 2)

def hopfLowerRadius (t : ℝ) : ℝ := √((1 - t) / 2)

theorem hopfUpperRadius_pos {t : ℝ} (ht : -1 < t) : 0 < hopfUpperRadius t :=
  Real.sqrt_pos.mpr (by linarith)

theorem hopfLowerRadius_pos {t : ℝ} (ht : t < 1) : 0 < hopfLowerRadius t :=
  Real.sqrt_pos.mpr (by linarith)

theorem hopfUpperRadius_sq {t : ℝ} (ht : -1 ≤ t) : hopfUpperRadius t ^ 2 = (1 + t) / 2 :=
  Real.sq_sqrt (by linarith)

theorem hopfLowerRadius_sq {t : ℝ} (ht : t ≤ 1) : hopfLowerRadius t ^ 2 = (1 - t) / 2 :=
  Real.sq_sqrt (by linarith)

theorem contDiffAt_hopfUpperRadius {t : ℝ} (ht : -1 < t) : ContDiffAt ℝ ∞ hopfUpperRadius t :=
  ((contDiffAt_const.add contDiffAt_id).div_const 2).sqrt (by simp only [id]; linarith)

theorem contDiffAt_hopfLowerRadius {t : ℝ} (ht : t < 1) : ContDiffAt ℝ ∞ hopfLowerRadius t :=
  ((contDiffAt_const.sub contDiffAt_id).div_const 2).sqrt (by simp only [id]; linarith)

theorem hopfUpperRadius_cliffordHeight (p : SphereCarrier.{u}) :
    hopfUpperRadius (cliffordHeight p) = ‖sphereFirst p‖ := by
  rw [hopfUpperRadius, ← norm_sphereFirst_sq_eq, Real.sqrt_sq (norm_nonneg _)]

theorem hopfLowerRadius_cliffordHeight (p : SphereCarrier.{u}) :
    hopfLowerRadius (cliffordHeight p) = ‖sphereSecond p‖ := by
  rw [hopfLowerRadius, ← norm_sphereSecond_sq_eq, Real.sqrt_sq (norm_nonneg _)]

theorem sphereFirst_ne_zero_of_cliffordHeight_ne {p : SphereCarrier.{u}}
    (h : cliffordHeight p ≠ -1) :
    sphereFirst p ≠ 0 := by
  intro h0
  apply h
  have h1 := norm_sphereFirst_sq_add p
  rw [h0, norm_zero] at h1
  rw [cliffordHeight, h0, norm_zero]
  linarith

theorem sphereSecond_ne_zero_of_cliffordHeight_ne {p : SphereCarrier.{u}}
    (h : cliffordHeight p ≠ 1) :
    sphereSecond p ≠ 0 := by
  intro h0
  apply h
  have h1 := norm_sphereFirst_sq_add p
  rw [h0, norm_zero] at h1
  rw [cliffordHeight, h0, norm_zero]
  linarith

theorem norm_real_smul_circle_sq {r : ℝ} (hr : 0 ≤ r) (w : Circle) :
    ‖r • (w : ℂ)‖ ^ 2 = r ^ 2 := by
  rw [norm_smul, Circle.norm_coe, mul_one, Real.norm_of_nonneg hr]

theorem norm_inv_smul_mul_circle_sq {r : ℝ} (hr : 0 ≤ r) (P : ℂ) (w : Circle) :
    ‖(2 * r)⁻¹ • (P * w)‖ ^ 2 = ‖P‖ ^ 2 / (4 * r ^ 2) := by
  rw [norm_smul, norm_mul, Circle.norm_coe, mul_one, norm_inv,
    Real.norm_of_nonneg (by positivity : (0 : ℝ) ≤ 2 * r)]
  field_simp
  ring

theorem norm_hopfUpperSecond_sq {P : ℂ} {t : ℝ} (h : ‖P‖ ^ 2 + t ^ 2 = 1) (ht : -1 < t)
    (w : Circle) :
    ‖(2 * hopfUpperRadius t)⁻¹ • (conj P * w)‖ ^ 2 = (1 - t) / 2 := by
  have hr := hopfUpperRadius_pos ht
  rw [norm_inv_smul_mul_circle_sq hr.le, Complex.norm_conj, hopfUpperRadius_sq ht.le]
  have h1 : (1 + t) ≠ 0 := by linarith
  field_simp
  linear_combination 4 * h

theorem norm_hopfLowerFirst_sq {P : ℂ} {t : ℝ} (h : ‖P‖ ^ 2 + t ^ 2 = 1) (ht : t < 1)
    (w : Circle) :
    ‖(2 * hopfLowerRadius t)⁻¹ • (P * w)‖ ^ 2 = (1 + t) / 2 := by
  have hr := hopfLowerRadius_pos ht
  rw [norm_inv_smul_mul_circle_sq hr.le, hopfLowerRadius_sq ht.le]
  have h1 : (1 - t) ≠ 0 := by linarith
  field_simp
  linear_combination 4 * h

theorem neg_one_lt_sphereTwoHeight {b : SphereTwoLift.{u}} (hb : sphereTwoHeight b ≠ -1) :
    -1 < sphereTwoHeight b :=
  lt_of_le_of_ne (neg_one_le_sphereTwoHeight b) (Ne.symm hb)

theorem sphereTwoHeight_lt_one {b : SphereTwoLift.{u}} (hb : sphereTwoHeight b ≠ 1) :
    sphereTwoHeight b < 1 :=
  lt_of_le_of_ne (sphereTwoHeight_le_one b) hb

def hopfUpperPoint (b : SphereTwoLift.{u}) (hb : sphereTwoHeight b ≠ -1) (w : Circle) :
    SphereCarrier.{u} :=
  sphereOfPair (hopfUpperRadius (sphereTwoHeight b) • (w : ℂ))
    ((2 * hopfUpperRadius (sphereTwoHeight b))⁻¹ • (conj (sphereTwoPlane b) * w)) (by
      rw [norm_real_smul_circle_sq (hopfUpperRadius_pos (neg_one_lt_sphereTwoHeight hb)).le,
        norm_hopfUpperSecond_sq (norm_sphereTwoPlane_sq_add b) (neg_one_lt_sphereTwoHeight hb),
        hopfUpperRadius_sq (neg_one_lt_sphereTwoHeight hb).le]
      ring)

def hopfLowerPoint (b : SphereTwoLift.{u}) (hb : sphereTwoHeight b ≠ 1) (w : Circle) :
    SphereCarrier.{u} :=
  sphereOfPair ((2 * hopfLowerRadius (sphereTwoHeight b))⁻¹ • (sphereTwoPlane b * w))
    (hopfLowerRadius (sphereTwoHeight b) • (w : ℂ)) (by
      rw [norm_real_smul_circle_sq (hopfLowerRadius_pos (sphereTwoHeight_lt_one hb)).le,
        norm_hopfLowerFirst_sq (norm_sphereTwoPlane_sq_add b) (sphereTwoHeight_lt_one hb),
        hopfLowerRadius_sq (sphereTwoHeight_lt_one hb).le]
      ring)

theorem circle_coe_mul_conj (w : Circle) : (w : ℂ) * conj (w : ℂ) = 1 := by
  rw [Complex.mul_conj, Circle.normSq_coe, Complex.ofReal_one]

theorem hopfMap_hopfUpperPoint (b : SphereTwoLift.{u}) (hb : sphereTwoHeight b ≠ -1)
    (w : Circle) : hopfMap (hopfUpperPoint b hb w) = b := by
  have ht := neg_one_lt_sphereTwoHeight hb
  have hr := hopfUpperRadius_pos ht
  have hinv : (2 * (hopfUpperRadius (sphereTwoHeight b) : ℂ)) *
      (2 * (hopfUpperRadius (sphereTwoHeight b) : ℂ))⁻¹ = 1 :=
    mul_inv_cancel₀ (by
      exact_mod_cast (by positivity : 2 * hopfUpperRadius (sphereTwoHeight b) ≠ 0))
  apply sphereTwoLift_ext
  · rw [sphereTwoPlane_hopfMap, hopfPlane, hopfUpperPoint, sphereFirst_sphereOfPair,
      sphereSecond_sphereOfPair]
    simp only [Complex.real_smul, map_mul, Complex.conj_ofReal, Complex.conj_conj]
    push_cast
    linear_combination (sphereTwoPlane b * (2 * (hopfUpperRadius (sphereTwoHeight b) : ℂ)) *
      (2 * (hopfUpperRadius (sphereTwoHeight b) : ℂ))⁻¹) * circle_coe_mul_conj w +
      sphereTwoPlane b * hinv
  · rw [sphereTwoHeight_hopfMap, cliffordHeight, hopfUpperPoint, sphereFirst_sphereOfPair,
      sphereSecond_sphereOfPair, norm_real_smul_circle_sq hr.le,
      norm_hopfUpperSecond_sq (norm_sphereTwoPlane_sq_add b) ht, hopfUpperRadius_sq ht.le]
    ring

theorem hopfMap_hopfLowerPoint (b : SphereTwoLift.{u}) (hb : sphereTwoHeight b ≠ 1)
    (w : Circle) : hopfMap (hopfLowerPoint b hb w) = b := by
  have ht := sphereTwoHeight_lt_one hb
  have hr := hopfLowerRadius_pos ht
  have hinv : (2 * (hopfLowerRadius (sphereTwoHeight b) : ℂ)) *
      (2 * (hopfLowerRadius (sphereTwoHeight b) : ℂ))⁻¹ = 1 :=
    mul_inv_cancel₀ (by
      exact_mod_cast (by positivity : 2 * hopfLowerRadius (sphereTwoHeight b) ≠ 0))
  apply sphereTwoLift_ext
  · rw [sphereTwoPlane_hopfMap, hopfPlane, hopfLowerPoint, sphereFirst_sphereOfPair,
      sphereSecond_sphereOfPair]
    simp only [Complex.real_smul, map_mul, Complex.conj_ofReal]
    push_cast
    linear_combination (sphereTwoPlane b * (2 * (hopfLowerRadius (sphereTwoHeight b) : ℂ)) *
      (2 * (hopfLowerRadius (sphereTwoHeight b) : ℂ))⁻¹) * circle_coe_mul_conj w +
      sphereTwoPlane b * hinv
  · rw [sphereTwoHeight_hopfMap, cliffordHeight, hopfLowerPoint, sphereFirst_sphereOfPair,
      sphereSecond_sphereOfPair, norm_real_smul_circle_sq hr.le,
      norm_hopfLowerFirst_sq (norm_sphereTwoPlane_sq_add b) ht, hopfLowerRadius_sq ht.le]
    ring


theorem hopfUpperPoint_hopfMap (p : SphereCarrier.{u}) (hp : sphereTwoHeight (hopfMap p) ≠ -1) :
    hopfUpperPoint (hopfMap p) hp (unitOf (sphereFirst p)) = p := by
  have hp' : cliffordHeight p ≠ -1 := by rwa [sphereTwoHeight_hopfMap] at hp
  have hz := sphereFirst_ne_zero_of_cliffordHeight_ne hp'
  have hn : (‖sphereFirst p‖ : ℂ) * (‖sphereFirst p‖ : ℂ)⁻¹ = 1 :=
    mul_inv_cancel₀ (by exact_mod_cast norm_ne_zero_iff.mpr hz)
  apply sphere_ext
  · rw [hopfUpperPoint, sphereFirst_sphereOfPair, sphereTwoHeight_hopfMap,
      hopfUpperRadius_cliffordHeight, norm_smul_unitOf]
  · rw [hopfUpperPoint, sphereSecond_sphereOfPair, sphereTwoHeight_hopfMap,
      hopfUpperRadius_cliffordHeight, sphereTwoPlane_hopfMap, hopfPlane, coe_unitOf hz]
    simp only [Complex.real_smul, map_mul, map_ofNat, Complex.conj_conj]
    push_cast
    linear_combination ((‖sphereFirst p‖ : ℂ)⁻¹ ^ 2 * sphereSecond p) *
        Complex.conj_mul' (sphereFirst p) +
      (sphereSecond p * ((‖sphereFirst p‖ : ℂ) * (‖sphereFirst p‖ : ℂ)⁻¹ + 1)) * hn

theorem hopfLowerPoint_hopfMap (p : SphereCarrier.{u}) (hp : sphereTwoHeight (hopfMap p) ≠ 1) :
    hopfLowerPoint (hopfMap p) hp (unitOf (sphereSecond p)) = p := by
  have hp' : cliffordHeight p ≠ 1 := by rwa [sphereTwoHeight_hopfMap] at hp
  have hz := sphereSecond_ne_zero_of_cliffordHeight_ne hp'
  have hn : (‖sphereSecond p‖ : ℂ) * (‖sphereSecond p‖ : ℂ)⁻¹ = 1 :=
    mul_inv_cancel₀ (by exact_mod_cast norm_ne_zero_iff.mpr hz)
  apply sphere_ext
  · rw [hopfLowerPoint, sphereFirst_sphereOfPair, sphereTwoHeight_hopfMap,
      hopfLowerRadius_cliffordHeight, sphereTwoPlane_hopfMap, hopfPlane, coe_unitOf hz]
    simp only [Complex.real_smul]
    push_cast
    linear_combination ((‖sphereSecond p‖ : ℂ)⁻¹ ^ 2 * sphereFirst p) *
        Complex.mul_conj' (sphereSecond p) +
      (sphereFirst p * ((‖sphereSecond p‖ : ℂ) * (‖sphereSecond p‖ : ℂ)⁻¹ + 1)) * hn
  · rw [hopfLowerPoint, sphereSecond_sphereOfPair, sphereTwoHeight_hopfMap,
      hopfLowerRadius_cliffordHeight, norm_smul_unitOf]

theorem unitOf_sphereFirst_hopfUpperPoint (b : SphereTwoLift.{u}) (hb : sphereTwoHeight b ≠ -1)
    (w : Circle) : unitOf (sphereFirst (hopfUpperPoint b hb w)) = w := by
  rw [hopfUpperPoint, sphereFirst_sphereOfPair,
    unitOf_smul (hopfUpperRadius_pos (neg_one_lt_sphereTwoHeight hb))]

theorem unitOf_sphereSecond_hopfLowerPoint (b : SphereTwoLift.{u}) (hb : sphereTwoHeight b ≠ 1)
    (w : Circle) : unitOf (sphereSecond (hopfLowerPoint b hb w)) = w := by
  rw [hopfLowerPoint, sphereSecond_sphereOfPair,
    unitOf_smul (hopfLowerRadius_pos (sphereTwoHeight_lt_one hb))]

theorem hopfMap_surjective : Surjective hopfMap.{u} := by
  intro b
  by_cases hb : sphereTwoHeight b = -1
  · have hb' : sphereTwoHeight b ≠ 1 := by rw [hb]; norm_num
    exact ⟨hopfLowerPoint b hb' 1, hopfMap_hopfLowerPoint b hb' 1⟩
  · exact ⟨hopfUpperPoint b hb 1, hopfMap_hopfUpperPoint b hb 1⟩

theorem hopfUpperPoint_mul (b : SphereTwoLift.{u}) (hb : sphereTwoHeight b ≠ -1) (w v : Circle) :
    sphereFirst (hopfUpperPoint b hb (w * v)) = w * sphereFirst (hopfUpperPoint b hb v) ∧
      sphereSecond (hopfUpperPoint b hb (w * v)) = w * sphereSecond (hopfUpperPoint b hb v) := by
  simp only [hopfUpperPoint, sphereFirst_sphereOfPair, sphereSecond_sphereOfPair, Circle.coe_mul,
    Complex.real_smul]
  constructor <;> ring

theorem hopfLowerPoint_mul (b : SphereTwoLift.{u}) (hb : sphereTwoHeight b ≠ 1) (w v : Circle) :
    sphereFirst (hopfLowerPoint b hb (w * v)) = w * sphereFirst (hopfLowerPoint b hb v) ∧
      sphereSecond (hopfLowerPoint b hb (w * v)) = w * sphereSecond (hopfLowerPoint b hb v) := by
  simp only [hopfLowerPoint, sphereFirst_sphereOfPair, sphereSecond_sphereOfPair, Circle.coe_mul,
    Complex.real_smul]
  constructor <;> ring

theorem eq_hopfUpperPoint {p : SphereCarrier.{u}} {b : SphereTwoLift.{u}}
    (hb : sphereTwoHeight b ≠ -1) (h : hopfMap p = b) :
    p = hopfUpperPoint b hb (unitOf (sphereFirst p)) := by
  subst h
  exact (hopfUpperPoint_hopfMap p hb).symm

theorem eq_hopfLowerPoint {p : SphereCarrier.{u}} {b : SphereTwoLift.{u}}
    (hb : sphereTwoHeight b ≠ 1) (h : hopfMap p = b) :
    p = hopfLowerPoint b hb (unitOf (sphereSecond p)) := by
  subst h
  exact (hopfLowerPoint_hopfMap p hb).symm

theorem exists_circle_of_hopfMap_eq {p q : SphereCarrier.{u}} (h : hopfMap p = hopfMap q) :
    ∃ w : Circle, sphereFirst q = w * sphereFirst p ∧ sphereSecond q = w * sphereSecond p := by
  by_cases hb : sphereTwoHeight (hopfMap p) = -1
  · have hb' : sphereTwoHeight (hopfMap p) ≠ 1 := by
      rw [hb]
      norm_num
    obtain ⟨h₁, h₂⟩ := hopfLowerPoint_mul (hopfMap p) hb'
      (unitOf (sphereSecond q) / unitOf (sphereSecond p)) (unitOf (sphereSecond p))
    rw [div_mul_cancel, ← eq_hopfLowerPoint hb' h.symm, ← eq_hopfLowerPoint hb' rfl] at h₁ h₂
    exact ⟨_, h₁, h₂⟩
  · obtain ⟨h₁, h₂⟩ := hopfUpperPoint_mul (hopfMap p) hb
      (unitOf (sphereFirst q) / unitOf (sphereFirst p)) (unitOf (sphereFirst p))
    rw [div_mul_cancel, ← eq_hopfUpperPoint hb h.symm, ← eq_hopfUpperPoint hb rfl] at h₁ h₂
    exact ⟨_, h₁, h₂⟩

theorem hopfMap_eq_of_circle {p q : SphereCarrier.{u}} (w : Circle)
    (h₁ : sphereFirst q = w * sphereFirst p) (h₂ : sphereSecond q = w * sphereSecond p) :
    hopfMap p = hopfMap q := by
  apply sphereTwoLift_ext
  · rw [sphereTwoPlane_hopfMap, sphereTwoPlane_hopfMap, hopfPlane, hopfPlane, h₁, h₂, map_mul]
    linear_combination (-2 * sphereFirst p * conj (sphereSecond p)) * circle_coe_mul_conj w
  · rw [sphereTwoHeight_hopfMap, sphereTwoHeight_hopfMap, cliffordHeight, cliffordHeight, h₁, h₂,
      norm_mul, norm_mul, Circle.norm_coe, one_mul, one_mul]

theorem hopfMap_eq_iff (p q : SphereCarrier.{u}) : hopfMap p = hopfMap q ↔
    ∃ w : Circle, sphereFirst q = w * sphereFirst p ∧ sphereSecond q = w * sphereSecond p :=
  ⟨exists_circle_of_hopfMap_eq, fun ⟨w, h₁, h₂⟩ => hopfMap_eq_of_circle w h₁ h₂⟩

def hopfUpper : TopologicalSpace.Opens SphereTwoLift.{u} :=
  ⟨{b | sphereTwoHeight b ≠ -1},
    isOpen_ne_fun contMDiff_sphereTwoHeight.continuous continuous_const⟩

def hopfLower : TopologicalSpace.Opens SphereTwoLift.{u} :=
  ⟨{b | sphereTwoHeight b ≠ 1},
    isOpen_ne_fun contMDiff_sphereTwoHeight.continuous continuous_const⟩

def hopfProjection :
    C((⊤ : TopologicalSpace.Opens (NoCuts.carrier standardThreeSphereLift.{u}).Carrier),
      SphereTwoLift.{u}) :=
  ⟨fun x => hopfMap x.val, contMDiff_hopfMap.continuous.comp continuous_subtype_val⟩

theorem sphereTwoHeight_ne_of_mem_hopfUpper {b : SphereTwoLift.{u}} (hb : b ∈ hopfUpper) :
    sphereTwoHeight b ≠ -1 :=
  hb

theorem sphereTwoHeight_ne_of_mem_hopfLower {b : SphereTwoLift.{u}} (hb : b ∈ hopfLower) :
    sphereTwoHeight b ≠ 1 :=
  hb

theorem hopfProjection_apply
    (x : (⊤ : TopologicalSpace.Opens (NoCuts.carrier standardThreeSphereLift.{u}).Carrier)) :
    hopfProjection x = hopfMap x.val :=
  rfl

theorem contMDiff_hopfHeightFactor (V : TopologicalSpace.Opens SphereTwoLift.{u}) {r : ℝ → ℝ}
    (hr : ∀ b : V, ContDiffAt ℝ ∞ r (sphereTwoHeight b.val)) :
    ContMDiff ((𝓡 2).prod (𝓡 1)) 𝓘(ℝ, ℝ) ∞
      (fun q : V × Circle => r (sphereTwoHeight q.1.val)) := fun q =>
  ContDiffAt.comp_contMDiffAt (f := fun q : V × Circle => sphereTwoHeight q.1.val)
    (hr q.1) ((contMDiff_sphereTwoHeight.comp (contMDiff_subtype_val.comp contMDiff_fst)) q)

theorem contMDiff_hopfPlaneFactor (V : TopologicalSpace.Opens SphereTwoLift.{u}) {f : ℂ → ℂ}
    (hf : ContDiff ℝ ∞ f) : ContMDiff ((𝓡 2).prod (𝓡 1)) 𝓘(ℝ, ℂ) ∞
      (fun q : V × Circle => f (sphereTwoPlane q.1.val) * q.2) :=
  (contDiff_mul (𝕜 := ℝ) (𝔸 := ℂ)).contMDiff.comp
    ((hf.contMDiff.comp (contMDiff_sphereTwoPlane.comp
      (contMDiff_subtype_val.comp contMDiff_fst))).prodMk_space
      (contMDiff_circle_coe.comp contMDiff_snd))

def hopfUpperSection (q : hopfUpper.{u} × Circle) : SphereCarrier.{u} :=
  hopfUpperPoint q.1.val (sphereTwoHeight_ne_of_mem_hopfUpper q.1.prop) q.2

def hopfLowerSection (q : hopfLower.{u} × Circle) : SphereCarrier.{u} :=
  hopfLowerPoint q.1.val (sphereTwoHeight_ne_of_mem_hopfLower q.1.prop) q.2

theorem hopfMap_hopfUpperSection (q : hopfUpper.{u} × Circle) :
    hopfMap (hopfUpperSection q) = q.1.val :=
  hopfMap_hopfUpperPoint _ _ _

theorem hopfMap_hopfLowerSection (q : hopfLower.{u} × Circle) :
    hopfMap (hopfLowerSection q) = q.1.val :=
  hopfMap_hopfLowerPoint _ _ _

theorem unitOf_hopfUpperSection (q : hopfUpper.{u} × Circle) :
    unitOf (sphereFirst (hopfUpperSection q)) = q.2 :=
  unitOf_sphereFirst_hopfUpperPoint _ _ _

theorem unitOf_hopfLowerSection (q : hopfLower.{u} × Circle) :
    unitOf (sphereSecond (hopfLowerSection q)) = q.2 :=
  unitOf_sphereSecond_hopfLowerPoint _ _ _

theorem contMDiff_hopfUpperSection :
    ContMDiff ((𝓡 2).prod (𝓡 1)) (𝓡 3) ∞ hopfUpperSection.{u} := by
  have hR := contMDiff_hopfHeightFactor hopfUpper (r := hopfUpperRadius) fun b =>
    contDiffAt_hopfUpperRadius (neg_one_lt_sphereTwoHeight b.prop)
  have hS := contMDiff_hopfHeightFactor hopfUpper (r := fun t => (2 * hopfUpperRadius t)⁻¹) fun b =>
    (contDiffAt_const.mul (contDiffAt_hopfUpperRadius (neg_one_lt_sphereTwoHeight b.prop))).inv
      (by positivity [hopfUpperRadius_pos (neg_one_lt_sphereTwoHeight b.prop)])
  rw [← contMDiffOn_univ]
  apply contMDiffOn_of_sphereFirst_sphereSecond isOpen_univ
  · simp only [hopfUpperSection, hopfUpperPoint, sphereFirst_sphereOfPair]
    exact (hR.smul (contMDiff_circle_coe.comp contMDiff_snd)).contMDiffOn
  · simp only [hopfUpperSection, hopfUpperPoint, sphereSecond_sphereOfPair]
    exact (hS.smul (contMDiff_hopfPlaneFactor hopfUpper Complex.conjCLE.contDiff)).contMDiffOn

theorem contMDiff_hopfLowerSection :
    ContMDiff ((𝓡 2).prod (𝓡 1)) (𝓡 3) ∞ hopfLowerSection.{u} := by
  have hR := contMDiff_hopfHeightFactor hopfLower (r := hopfLowerRadius) fun b =>
    contDiffAt_hopfLowerRadius (sphereTwoHeight_lt_one b.prop)
  have hS := contMDiff_hopfHeightFactor hopfLower (r := fun t => (2 * hopfLowerRadius t)⁻¹) fun b =>
    (contDiffAt_const.mul (contDiffAt_hopfLowerRadius (sphereTwoHeight_lt_one b.prop))).inv
      (by positivity [hopfLowerRadius_pos (sphereTwoHeight_lt_one b.prop)])
  rw [← contMDiffOn_univ]
  apply contMDiffOn_of_sphereFirst_sphereSecond isOpen_univ
  · simp only [hopfLowerSection, hopfLowerPoint, sphereFirst_sphereOfPair]
    exact (hS.smul (contMDiff_hopfPlaneFactor hopfLower contDiff_id)).contMDiffOn
  · simp only [hopfLowerSection, hopfLowerPoint, sphereSecond_sphereOfPair]
    exact (hR.smul (contMDiff_circle_coe.comp contMDiff_snd)).contMDiffOn

theorem cliffordHeight_ne_of_mem_hopfUpper
    (x : TopologicalSpace.Opens.comap hopfProjection.{u} hopfUpper.{u}) :
    cliffordHeight x.1.1 ≠ -1 := by
  have h : sphereTwoHeight (hopfMap x.1.1) ≠ -1 := x.2
  rwa [sphereTwoHeight_hopfMap] at h

theorem cliffordHeight_ne_of_mem_hopfLower
    (x : TopologicalSpace.Opens.comap hopfProjection.{u} hopfLower.{u}) :
    cliffordHeight x.1.1 ≠ 1 := by
  have h : sphereTwoHeight (hopfMap x.1.1) ≠ 1 := x.2
  rwa [sphereTwoHeight_hopfMap] at h

theorem mem_comap_hopfProjection {V : TopologicalSpace.Opens SphereTwoLift.{u}}
    {x : (⊤ : TopologicalSpace.Opens (NoCuts.carrier standardThreeSphereLift.{u}).Carrier)}
    (h : hopfMap x.val ∈ V) : x ∈ TopologicalSpace.Opens.comap hopfProjection V :=
  h

def hopfUpperTrivialization :
    TopologicalSpace.Opens.comap hopfProjection.{u} hopfUpper.{u} ≃ₘ⟮𝓡 3, (𝓡 2).prod (𝓡 1)⟯
      (hopfUpper.{u} × Circle) where
  toFun x := (⟨hopfMap x.1.1, x.2⟩, unitOf (sphereFirst x.1.1))
  invFun q := ⟨⟨hopfUpperSection q, trivial⟩,
    mem_comap_hopfProjection ((hopfMap_hopfUpperSection q).symm ▸ q.1.2)⟩
  left_inv x := Subtype.ext (Subtype.ext (hopfUpperPoint_hopfMap x.1.1 x.2))
  right_inv q := Prod.ext (Subtype.ext (hopfMap_hopfUpperSection q))
    (unitOf_hopfUpperSection q)
  contMDiff_toFun := by
    have hval : ContMDiff (𝓡 3) (𝓡 3) ∞
        (fun x : TopologicalSpace.Opens.comap hopfProjection.{u} hopfUpper.{u} =>
          (x.1.1 : SphereCarrier.{u})) :=
      contMDiff_subtype_val.comp contMDiff_subtype_val
    refine ContMDiff.prodMk ?_ ?_
    · exact (ContMDiff.subtypeVal_comp_iff hopfUpper _).mp (contMDiff_hopfMap.comp hval)
    · exact contMDiffOn_unitOf.comp_contMDiff (contMDiff_sphereFirst.comp hval) fun x =>
        sphereFirst_ne_zero_of_cliffordHeight_ne (cliffordHeight_ne_of_mem_hopfUpper x)
  contMDiff_invFun := by
    refine (ContMDiff.subtypeVal_comp_iff _ _).mp ?_
    refine (ContMDiff.subtypeVal_comp_iff _ _).mp ?_
    exact contMDiff_hopfUpperSection

def hopfLowerTrivialization :
    TopologicalSpace.Opens.comap hopfProjection.{u} hopfLower.{u} ≃ₘ⟮𝓡 3, (𝓡 2).prod (𝓡 1)⟯
      (hopfLower.{u} × Circle) where
  toFun x := (⟨hopfMap x.1.1, x.2⟩, unitOf (sphereSecond x.1.1))
  invFun q := ⟨⟨hopfLowerSection q, trivial⟩,
    mem_comap_hopfProjection ((hopfMap_hopfLowerSection q).symm ▸ q.1.2)⟩
  left_inv x := Subtype.ext (Subtype.ext (hopfLowerPoint_hopfMap x.1.1 x.2))
  right_inv q := Prod.ext (Subtype.ext (hopfMap_hopfLowerSection q))
    (unitOf_hopfLowerSection q)
  contMDiff_toFun := by
    have hval : ContMDiff (𝓡 3) (𝓡 3) ∞
        (fun x : TopologicalSpace.Opens.comap hopfProjection.{u} hopfLower.{u} =>
          (x.1.1 : SphereCarrier.{u})) :=
      contMDiff_subtype_val.comp contMDiff_subtype_val
    refine ContMDiff.prodMk ?_ ?_
    · exact (ContMDiff.subtypeVal_comp_iff hopfLower _).mp (contMDiff_hopfMap.comp hval)
    · exact contMDiffOn_unitOf.comp_contMDiff (contMDiff_sphereSecond.comp hval) fun x =>
        sphereSecond_ne_zero_of_cliffordHeight_ne (cliffordHeight_ne_of_mem_hopfLower x)
  contMDiff_invFun := by
    refine (ContMDiff.subtypeVal_comp_iff _ _).mp ?_
    refine (ContMDiff.subtypeVal_comp_iff _ _).mp ?_
    exact contMDiff_hopfLowerSection

def hopfChart (c : Bool) : TopologicalSpace.Opens SphereTwoLift.{u} := cond c hopfUpper hopfLower

def hopfChartTrivialization : (c : Bool) →
    TopologicalSpace.Opens.comap hopfProjection.{u} (hopfChart c) ≃ₘ⟮𝓡 3, (𝓡 2).prod (𝓡 1)⟯
      (hopfChart c × Circle)
  | true => hopfUpperTrivialization
  | false => hopfLowerTrivialization

theorem hopfChartTrivialization_fst (c : Bool)
    (x : TopologicalSpace.Opens.comap hopfProjection.{u} (hopfChart c)) :
    ((hopfChartTrivialization c x).1).val = hopfProjection x.val := by
  cases c <;> rfl

theorem mem_hopfChart (b : SphereTwoLift.{u}) :
    b ∈ hopfChart (decide (sphereTwoHeight b ≠ -1)) := by
  by_cases hb : sphereTwoHeight b = -1
  · rw [decide_eq_false (not_not.mpr hb)]
    change sphereTwoHeight b ≠ 1
    rw [hb]
    norm_num
  · rw [decide_eq_true hb]
    exact hb

def hopfCircleFibration : CircleFibration (NoCuts.carrier standardThreeSphereLift.{u}) ⊤ where
  base := sphereTwoSurfaceLift
  projection := hopfProjection
  surjective b := let ⟨p, hp⟩ := hopfMap_surjective b; ⟨⟨p, trivial⟩, hp⟩
  smooth := contMDiff_hopfMap.comp contMDiff_subtype_val
  neighborhood b := hopfChart (decide (sphereTwoHeight b ≠ -1))
  mem_neighborhood := mem_hopfChart
  trivialization _ := hopfChartTrivialization _
  projection_trivialization _ x := hopfChartTrivialization_fst _ x

@[simp]
theorem hopfCircleFibration_base : hopfCircleFibration.{u}.base = sphereTwoSurfaceLift.{u} := rfl

theorem hopfCircleFibration_projection_apply
    (x : (⊤ : TopologicalSpace.Opens (NoCuts.carrier standardThreeSphereLift.{u}).Carrier)) :
    hopfCircleFibration.projection x = hopfMap x.val :=
  rfl

def standardThreeSphereLiftHopfRawGraphPresentation :
    RawGraphPresentation (NoCuts.carrier standardThreeSphereLift.{u}) :=
  RawGraphPresentation.ofClosedCircleFibration _ hopfCircleFibration

end GC.GraphManifold
