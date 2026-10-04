import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Seifert.EmbeddedPieces
import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Seifert.CliffordBlocks
import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Seifert.LensCarrierArithmetic
import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.SphereProduct
import DifferentialGeometry.Topology.Manifold.SmoothBoundaryAtlas.Tangent

/-!
# A two-solid-torus presentation of the sphere product

Lambert hemisphere coordinates give the two actual solid tori in the standard sphere product.
The equator collar agrees with the Clifford disc collar, and conjugation on its first circle
is the meridian-preserving zero lens matching.
-/

set_option autoImplicit false

noncomputable section

open Set Function Metric
open DifferentialGeometry DifferentialGeometry.Topology GC.Endpoint GC.GraphManifold
open scoped Manifold ContDiff Topology

namespace GC.Seifert

abbrev ProductSphere := sphere (0 : EuclideanSpace ℝ (Fin 3)) 1

def productSphereCoordinates : EuclideanSpace ℝ (Fin 3) ≃L[ℝ] ℂ × ℝ :=
  LinearEquiv.toContinuousLinearEquiv
    { toFun := fun x => (⟨x 0, x 1⟩, x 2)
      invFun := fun z => !₂[z.1.re, z.1.im, z.2]
      map_add' := fun x y => by
        refine Prod.ext (Complex.ext ?_ ?_) ?_ <;> simp
      map_smul' := fun c x => by
        refine Prod.ext (Complex.ext ?_ ?_) ?_ <;> simp
      left_inv := fun x => by ext i; fin_cases i <;> simp
      right_inv := fun z => by ext <;> simp }

theorem productSphereCoordinates_norm_sq (x : EuclideanSpace ℝ (Fin 3)) :
    ‖x‖ ^ 2 = ‖(productSphereCoordinates x).1‖ ^ 2 + (productSphereCoordinates x).2 ^ 2 := by
  rw [EuclideanSpace.norm_sq_eq, Fin.sum_univ_three, Complex.sq_norm]
  have he : productSphereCoordinates x = (⟨x 0, x 1⟩, x 2) := rfl
  rw [he, Complex.normSq_apply]
  simp only [Real.norm_eq_abs, sq_abs]
  ring

def productSphereOfCoordinates (z : ℂ) (h : ℝ) (he : ‖z‖ ^ 2 + h ^ 2 = 1) :
    ProductSphere :=
  ⟨productSphereCoordinates.symm (z, h), by
    rw [mem_sphere_zero_iff_norm]
    have hs : ‖productSphereCoordinates.symm (z, h)‖ ^ 2 = 1 := by
      rw [productSphereCoordinates_norm_sq, ContinuousLinearEquiv.apply_symm_apply]
      exact he
    exact (pow_eq_one_iff_of_nonneg (norm_nonneg _) two_ne_zero).mp hs⟩

def productSpherePlane (x : ProductSphere) : ℂ := (productSphereCoordinates x.val).1

def productSphereHeight (x : ProductSphere) : ℝ := (productSphereCoordinates x.val).2

theorem productSphere_coordinates (x : ProductSphere) :
    ‖productSpherePlane x‖ ^ 2 + productSphereHeight x ^ 2 = 1 := by
  rw [productSpherePlane, productSphereHeight, ← productSphereCoordinates_norm_sq,
    mem_sphere_zero_iff_norm.mp x.property, one_pow]

theorem productSphere_ext {x y : ProductSphere} (hz : productSpherePlane x = productSpherePlane y)
    (hh : productSphereHeight x = productSphereHeight y) : x = y := by
  apply Subtype.ext
  apply productSphereCoordinates.injective
  exact Prod.ext hz hh

theorem productSpherePlane_ofCoordinates (z : ℂ) (h : ℝ) (he : ‖z‖ ^ 2 + h ^ 2 = 1) :
    productSpherePlane (productSphereOfCoordinates z h he) = z :=
  congrArg Prod.fst (productSphereCoordinates.apply_symm_apply (z, h))

theorem productSphereHeight_ofCoordinates (z : ℂ) (h : ℝ) (he : ‖z‖ ^ 2 + h ^ 2 = 1) :
    productSphereHeight (productSphereOfCoordinates z h he) = h :=
  congrArg Prod.snd (productSphereCoordinates.apply_symm_apply (z, h))

theorem productSphereHeight_bounds (x : ProductSphere) :
    -1 ≤ productSphereHeight x ∧ productSphereHeight x ≤ 1 := by
  have he := productSphere_coordinates x
  have hp := sq_nonneg ‖productSpherePlane x‖
  constructor <;> nlinarith

instance productSphere_fact : Fact (Module.finrank ℝ (EuclideanSpace ℝ (Fin 3)) = 2 + 1) :=
  ⟨finrank_euclideanSpace_fin⟩

theorem productSpherePlane_smooth :
    ContMDiff (𝓡 2) 𝓘(ℝ, ℂ) ∞ productSpherePlane :=
  let c := (ContinuousLinearMap.fst ℝ ℂ ℝ).comp
    productSphereCoordinates.toContinuousLinearMap
  c.contDiff.contMDiff.comp contMDiff_coe_sphere

theorem productSphereHeight_smooth :
    ContMDiff (𝓡 2) 𝓘(ℝ, ℝ) ∞ productSphereHeight :=
  let c := (ContinuousLinearMap.snd ℝ ℂ ℝ).comp
    productSphereCoordinates.toContinuousLinearMap
  c.contDiff.contMDiff.comp contMDiff_coe_sphere

def productHemisphere (b : Bool) (z : UnitDisc.{0}) : ProductSphere :=
  let w := if b then z.down.val else star z.down.val
  let h := if b then ‖z.down.val‖ ^ 2 - 1 else 1 - ‖z.down.val‖ ^ 2
  productSphereOfCoordinates (Real.sqrt (2 - ‖z.down.val‖ ^ 2) • w) h (by
    have hb : ‖z.down.val‖ ^ 2 ≤ 1 := z.down.property
    rw [norm_smul, mul_pow, Real.norm_eq_abs, sq_abs,
      Real.sq_sqrt (by linarith : 0 ≤ 2 - ‖z.down.val‖ ^ 2)]
    dsimp only [w, h]
    cases b <;> simp only [Bool.false_eq_true, ↓reduceIte, norm_star] <;> ring)

theorem productHemisphere_plane (b : Bool) (z : UnitDisc.{0}) :
    productSpherePlane (productHemisphere b z) =
      Real.sqrt (2 - ‖z.down.val‖ ^ 2) • (if b then z.down.val else star z.down.val) :=
  (productSphereCoordinates.apply_symm_apply _ |> congrArg Prod.fst)

theorem productHemisphere_height (b : Bool) (z : UnitDisc.{0}) :
    productSphereHeight (productHemisphere b z) =
      if b then ‖z.down.val‖ ^ 2 - 1 else 1 - ‖z.down.val‖ ^ 2 :=
  (productSphereCoordinates.apply_symm_apply _ |> congrArg Prod.snd)

theorem productHemisphere_smooth (b : Bool) :
    ContMDiff (𝓡∂ 2) (𝓡 2) ∞ (productHemisphere b) := by
  have hv := contMDiff_disc_val.{0}
  have hn : ContMDiff (𝓡∂ 2) 𝓘(ℝ, ℝ) ∞ (fun z : UnitDisc.{0} => ‖z.down.val‖ ^ 2) :=
    (contDiff_norm_sq ℝ).contMDiff.comp hv
  have hs : ContMDiff (𝓡∂ 2) 𝓘(ℝ, ℝ) ∞
      (fun z : UnitDisc.{0} => Real.sqrt (2 - ‖z.down.val‖ ^ 2)) := by
    intro z
    apply (Real.contDiffAt_sqrt ?_).contMDiffAt.comp z ((contMDiff_const.sub hn) z)
    have hb : ‖z.down.val‖ ^ 2 ≤ 1 := z.down.property
    linarith
  have hw : ContMDiff (𝓡∂ 2) 𝓘(ℝ, ℂ) ∞
      (fun z : UnitDisc.{0} => if b then z.down.val else star z.down.val) := by
    cases b
    · exact Complex.conjCLE.contDiff.contMDiff.comp hv
    · exact hv
  have hh : ContMDiff (𝓡∂ 2) 𝓘(ℝ, ℝ) ∞
      (fun z : UnitDisc.{0} => if b then ‖z.down.val‖ ^ 2 - 1 else 1 - ‖z.down.val‖ ^ 2) := by
    cases b
    · exact contMDiff_const.sub hn
    · exact hn.sub contMDiff_const
  have hval : ContMDiff (𝓡∂ 2) 𝓘(ℝ, EuclideanSpace ℝ (Fin 3)) ∞
      (fun z => (productHemisphere b z).val) :=
    productSphereCoordinates.symm.contDiff.contMDiff.comp ((hs.smul hw).prodMk_space hh)
  exact ContMDiff.codRestrict_sphere hval (fun z => (productHemisphere b z).property)

def productHemisphereInverse (b : Bool) (x : ProductSphere) : ℂ :=
  let v := (Real.sqrt (if b then 1 - productSphereHeight x else
    1 + productSphereHeight x))⁻¹ • productSpherePlane x
  if b then v else star v

theorem productHemisphereInverse_apply (b : Bool) (z : UnitDisc.{0}) :
    productHemisphereInverse b (productHemisphere b z) = z.down.val := by
  have hp : 0 < Real.sqrt (2 - ‖z.down.val‖ ^ 2) :=
    Real.sqrt_pos.mpr (by have hz : ‖z.down.val‖ ^ 2 ≤ 1 := z.down.property; linarith)
  rw [productHemisphereInverse, productHemisphere_plane, productHemisphere_height]
  cases b <;> simp only [Bool.false_eq_true, ↓reduceIte]
  · rw [show 1 + (1 - ‖z.down.val‖ ^ 2) = 2 - ‖z.down.val‖ ^ 2 by ring,
      smul_smul, inv_mul_cancel₀ hp.ne', one_smul, star_star]
  · rw [show 1 - (‖z.down.val‖ ^ 2 - 1) = 2 - ‖z.down.val‖ ^ 2 by ring,
      smul_smul, inv_mul_cancel₀ hp.ne', one_smul]

theorem productHemisphereInverse_smoothAt (b : Bool) (x : ProductSphere)
    (hp : 0 < if b then 1 - productSphereHeight x else 1 + productSphereHeight x) :
    ContMDiffAt (𝓡 2) 𝓘(ℝ, ℂ) ∞ (productHemisphereInverse b) x := by
  have hh : ContMDiffAt (𝓡 2) 𝓘(ℝ, ℝ) ∞
      (fun y => if b then 1 - productSphereHeight y else 1 + productSphereHeight y) x := by
    cases b
    · exact (contMDiff_const.add productSphereHeight_smooth).contMDiffAt
    · exact (contMDiff_const.sub productSphereHeight_smooth).contMDiffAt
  have hs := (Real.contDiffAt_sqrt hp.ne').contMDiffAt.comp x hh
  have hv := (hs.inv₀ (Real.sqrt_pos.mpr hp).ne').smul productSpherePlane_smooth.contMDiffAt
  cases b
  · exact Complex.conjCLE.contDiff.contMDiff.contMDiffAt.comp x hv
  · exact hv

theorem productHemisphere_mfderiv_bijective (b : Bool) (z : UnitDisc.{0}) :
    Function.Bijective (mfderiv (𝓡∂ 2) (𝓡 2) (productHemisphere b) z) := by
  have hp : 0 < if b then 1 - productSphereHeight (productHemisphere b z)
      else 1 + productSphereHeight (productHemisphere b z) := by
    rw [productHemisphere_height]
    have hz : ‖z.down.val‖ ^ 2 ≤ 1 := z.down.property
    cases b <;> simp only [Bool.false_eq_true, ↓reduceIte] <;> linarith
  have hc := mfderiv_comp z
    ((productHemisphereInverse_smoothAt b (productHemisphere b z) hp).mdifferentiableAt (by simp))
    ((productHemisphere_smooth b).mdifferentiableAt (by simp))
  have he : productHemisphereInverse b ∘ productHemisphere b =
      fun w : UnitDisc.{0} => w.down.val := funext (productHemisphereInverse_apply b)
  rw [he] at hc
  have hv : Function.Bijective
      (mfderiv (𝓡∂ 2) 𝓘(ℝ, ℂ) (fun w : UnitDisc.{0} => w.down.val) z) := by
    rw [show (fun w : UnitDisc.{0} => w.down.val) =
      Subtype.val ∘ (uliftDiffeomorph (𝓡∂ 2) unitDiscSet).symm by rfl,
      mfderiv_comp z (unitDiscAtlas.contMDiff_subtype_val.mdifferentiableAt (by simp))
        ((uliftDiffeomorph (𝓡∂ 2) unitDiscSet).symm.contMDiff.mdifferentiableAt (by simp))]
    exact (unitDiscAtlas.mfderiv_subtypeVal_bijective z.down).comp
      ((uliftDiffeomorph (𝓡∂ 2) unitDiscSet).symm.mfderivToContinuousLinearEquiv
        (by simp) z).bijective
  have hi : Function.Injective (mfderiv (𝓡∂ 2) (𝓡 2) (productHemisphere b) z) := by
    intro v w hvw
    apply hv.injective
    rw [hc]
    exact congrArg (mfderiv (𝓡 2) 𝓘(ℝ, ℂ) (productHemisphereInverse b)
      (productHemisphere b z)) hvw
  exact ⟨hi, (LinearMap.injective_iff_surjective_of_finrank_eq_finrank rfl).mp hi⟩

def productHemisphereSide (b : Bool) (x : ProductSphere) : Prop :=
  if b then productSphereHeight x ≤ 0 else 0 ≤ productSphereHeight x

theorem productHemisphere_mem_side (b : Bool) (z : UnitDisc.{0}) :
    productHemisphereSide b (productHemisphere b z) := by
  rw [productHemisphereSide, productHemisphere_height]
  have hb : ‖z.down.val‖ ^ 2 ≤ 1 := z.down.property
  cases b <;> simp only [Bool.false_eq_true, ↓reduceIte] <;> linarith

theorem productHemisphereInverse_norm_sq (b : Bool) (x : ProductSphere)
    (hx : productHemisphereSide b x) :
    ‖productHemisphereInverse b x‖ ^ 2 =
      if b then 1 + productSphereHeight x else 1 - productSphereHeight x := by
  have hcoords := productSphere_coordinates x
  unfold productHemisphereSide at hx
  unfold productHemisphereInverse
  cases b <;> simp only [Bool.false_eq_true, ↓reduceIte] at hx ⊢
  · rw [norm_star, norm_smul, mul_pow, Real.norm_eq_abs, sq_abs, inv_pow,
      Real.sq_sqrt (by linarith : 0 ≤ 1 + productSphereHeight x)]
    rw [inv_mul_eq_div]
    apply (div_eq_iff (by linarith : 1 + productSphereHeight x ≠ 0)).mpr
    nlinarith
  · rw [norm_smul, mul_pow, Real.norm_eq_abs, sq_abs, inv_pow,
      Real.sq_sqrt (by linarith : 0 ≤ 1 - productSphereHeight x)]
    rw [inv_mul_eq_div]
    apply (div_eq_iff (by linarith : 1 - productSphereHeight x ≠ 0)).mpr
    nlinarith

def productHemispherePreimage (b : Bool) (x : ProductSphere)
    (hx : productHemisphereSide b x) : UnitDisc.{0} :=
  ⟨⟨productHemisphereInverse b x, by
    change ‖productHemisphereInverse b x‖ ^ 2 ≤ 1
    rw [productHemisphereInverse_norm_sq b x hx]
    unfold productHemisphereSide at hx
    cases b <;> simp only [Bool.false_eq_true, ↓reduceIte] at hx ⊢ <;> linarith⟩⟩

theorem productHemisphere_preimage (b : Bool) (x : ProductSphere)
    (hx : productHemisphereSide b x) :
    productHemisphere b (productHemispherePreimage b x hx) = x := by
  have hn := productHemisphereInverse_norm_sq b x hx
  have hs := hx
  unfold productHemisphereSide at hs
  apply productSphere_ext
  · rw [productHemisphere_plane]
    change Real.sqrt (2 - ‖productHemisphereInverse b x‖ ^ 2) •
      (if b then productHemisphereInverse b x else star (productHemisphereInverse b x)) = _
    rw [hn, productHemisphereInverse]
    cases b <;> simp only [Bool.false_eq_true, ↓reduceIte, star_star] at hs ⊢
    · rw [show 2 - (1 - productSphereHeight x) = 1 + productSphereHeight x by ring,
        smul_smul, mul_inv_cancel₀ (Real.sqrt_pos.mpr (by linarith)).ne', one_smul]
    · rw [show 2 - (1 + productSphereHeight x) = 1 - productSphereHeight x by ring,
        smul_smul, mul_inv_cancel₀ (Real.sqrt_pos.mpr (by linarith)).ne', one_smul]
  · rw [productHemisphere_height]
    change (if b then ‖productHemisphereInverse b x‖ ^ 2 - 1
      else 1 - ‖productHemisphereInverse b x‖ ^ 2) = _
    rw [hn]
    cases b <;> simp only [Bool.false_eq_true, ↓reduceIte] <;> ring

theorem productHemisphere_injective (b : Bool) : Injective (productHemisphere b) := by
  intro z w he
  apply ULift.ext
  apply Subtype.ext
  exact (productHemisphereInverse_apply b z).symm.trans
    ((congrArg (productHemisphereInverse b) he).trans (productHemisphereInverse_apply b w))

theorem productHemisphere_covers (x : ProductSphere) :
    ∃ b z, productHemisphere b z = x := by
  rcases le_total (productSphereHeight x) 0 with hx | hx
  · exact ⟨true, productHemispherePreimage true x hx, productHemisphere_preimage true x hx⟩
  · exact ⟨false, productHemispherePreimage false x hx, productHemisphere_preimage false x hx⟩

theorem productDiscCollar_norm_sq (t : Circle) (h : EuclideanHalfSpace 1)
    (hh : h.val 0 < 1) :
    ‖(cliffordDiscCollarMap.{0} (t, h)).down.val‖ ^ 2 = 1 - h.val 0 := by
  rw [cliffordDiscCollarMap_val, norm_smul, mul_pow, Real.norm_eq_abs, sq_abs,
    Circle.norm_coe, one_pow, mul_one, mul_pow, sqrt_two_sq, seamFirst_sq,
    seamClamp_of_mem (by linarith) (by linarith [h.property])]
  ring

def productCarrierCoordinatesDiffeomorph : (ProductSphere × Circle) ≃ₘ⟮
    (𝓡 2).prod (𝓡 1), (NoCuts.carrier sphereTwoTimesCircleLift).model⟯
      (NoCuts.carrier sphereTwoTimesCircleLift).Carrier :=
  ((Diffeomorph.refl (𝓡 2) ProductSphere ∞).prodCongr
    sphereOneDiffeomorphCircle.symm).trans sphereTwoTimesCircleModelCopy.equiv

def productCarrierHemisphere (b : Bool) (p : UnitDisc.{0} × Circle) :
    (NoCuts.carrier sphereTwoTimesCircleLift).Carrier :=
  productCarrierCoordinatesDiffeomorph (productHemisphere b p.1, p.2)

theorem productCarrierHemisphere_smooth (b : Bool) :
    ContMDiff ((𝓡∂ 2).prod (𝓡 1)) (NoCuts.carrier sphereTwoTimesCircleLift).model ∞
      (productCarrierHemisphere b) :=
  productCarrierCoordinatesDiffeomorph.contMDiff.comp
    (((productHemisphere_smooth b).comp contMDiff_fst).prodMk contMDiff_snd)

theorem productCarrierHemisphere_mfderiv_bijective (b : Bool) (p : UnitDisc.{0} × Circle) :
    Function.Bijective (mfderiv ((𝓡∂ 2).prod (𝓡 1))
      (NoCuts.carrier sphereTwoTimesCircleLift).model (productCarrierHemisphere b) p) := by
  change Function.Bijective (mfderiv ((𝓡∂ 2).prod (𝓡 1))
    (NoCuts.carrier sphereTwoTimesCircleLift).model
      (productCarrierCoordinatesDiffeomorph ∘ Prod.map (productHemisphere b) id) p)
  have hprod : ContMDiff ((𝓡∂ 2).prod (𝓡 1)) ((𝓡 2).prod (𝓡 1)) ∞
      (Prod.map (productHemisphere b) (id : Circle → Circle)) :=
    (productHemisphere_smooth b).prodMap contMDiff_id
  rw [mfderiv_comp p
    (productCarrierCoordinatesDiffeomorph.contMDiff.mdifferentiableAt (by simp))
    (hprod.mdifferentiableAt (by simp)),
    mfderiv_prodMap ((productHemisphere_smooth b).mdifferentiableAt (by simp))
      (mdifferentiableAt_id (I := 𝓡 1)), mfderiv_id]
  exact (productCarrierCoordinatesDiffeomorph.mfderivToContinuousLinearEquiv
    (by simp) _).bijective.comp
      ((productHemisphere_mfderiv_bijective b p.1).prodMap bijective_id)

theorem productCarrierHemisphere_injective (b : Bool) :
    Injective (productCarrierHemisphere b) := by
  intro p q he
  have hv := productCarrierCoordinatesDiffeomorph.injective he
  apply Prod.ext
  · exact (productHemisphere_injective b) (congrArg Prod.fst hv)
  · exact congrArg (fun y : ProductSphere × Circle => y.2) hv

theorem productCarrierHemisphere_covers
    (x : (NoCuts.carrier sphereTwoTimesCircleLift).Carrier) :
    ∃ b p, productCarrierHemisphere b p = x := by
  let y := productCarrierCoordinatesDiffeomorph.symm x
  obtain ⟨b, z, hz⟩ := productHemisphere_covers y.1
  refine ⟨b, (z, y.2), ?_⟩
  change productCarrierCoordinatesDiffeomorph (productHemisphere b z, y.2) = x
  rw [hz]
  exact productCarrierCoordinatesDiffeomorph.apply_symm_apply x

def productSphereEquator (t : Circle) : ProductSphere :=
  productSphereOfCoordinates t 0 (by rw [Circle.norm_coe]; norm_num)

theorem productSphere_eq_equator_of_height_zero (x : ProductSphere)
    (hx : productSphereHeight x = 0) :
    x = productSphereEquator (unitOf (productSpherePlane x)) := by
  have hn : ‖productSpherePlane x‖ = 1 := by
    have hc := productSphere_coordinates x
    rw [hx] at hc
    nlinarith [norm_nonneg (productSpherePlane x)]
  apply productSphere_ext
  · rw [productSphereEquator, productSpherePlane_ofCoordinates]
    have hu := norm_smul_unitOf (productSpherePlane x)
    rw [hn, one_smul] at hu
    exact hu.symm
  · rw [productSphereEquator, productSphereHeight_ofCoordinates, hx]

theorem productDiscCollar_scale (t : Circle) (h : EuclideanHalfSpace 1)
    (hh : h.val 0 < 1) :
    Real.sqrt (2 - ‖(cliffordDiscCollarMap.{0} (t, h)).down.val‖ ^ 2) *
      ((√2 : ℝ) * seamFirst (-h.val 0)) = Real.sqrt (1 - (h.val 0) ^ 2) := by
  have ha : 0 ≤ ((√2 : ℝ) * seamFirst (-h.val 0)) :=
    mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
  have hs : ((√2 : ℝ) * seamFirst (-h.val 0)) ^ 2 = 1 - h.val 0 := by
    rw [mul_pow, sqrt_two_sq, seamFirst_sq,
      seamClamp_of_mem (by linarith) (by linarith [h.property])]
    ring
  rw [productDiscCollar_norm_sq t h hh]
  have hp : 0 ≤ 2 - (1 - h.val 0) := by linarith [h.property]
  have ht : 0 ≤ 1 - (h.val 0) ^ 2 := by nlinarith [h.property]
  have hleft := mul_nonneg (Real.sqrt_nonneg (2 - (1 - h.val 0))) ha
  have hright := Real.sqrt_nonneg (1 - (h.val 0) ^ 2)
  have hsq : (Real.sqrt (2 - (1 - h.val 0)) * ((√2 : ℝ) * seamFirst (-h.val 0))) ^ 2 =
      (Real.sqrt (1 - (h.val 0) ^ 2)) ^ 2 := by
    rw [mul_pow, Real.sq_sqrt hp, hs, Real.sq_sqrt ht]
    ring
  nlinarith

theorem productHemisphere_collar_plane (b : Bool) (t : Circle) (h : EuclideanHalfSpace 1)
    (hh : h.val 0 < 1) :
    productSpherePlane (productHemisphere b (cliffordDiscCollarMap (t, h))) =
      Real.sqrt (1 - (h.val 0) ^ 2) • (if b then (t : ℂ) else star (t : ℂ)) := by
  rw [productHemisphere_plane]
  have hs := productDiscCollar_scale t h hh
  cases b <;> simp only [Bool.false_eq_true, ↓reduceIte]
  · rw [cliffordDiscCollarMap_val, star_smul, star_trivial, smul_smul]
    rw [← cliffordDiscCollarMap_val (t, h), hs]
  · rw [cliffordDiscCollarMap_val, smul_smul]
    rw [← cliffordDiscCollarMap_val (t, h), hs]

theorem productHemisphere_collar_height (b : Bool) (t : Circle) (h : EuclideanHalfSpace 1)
    (hh : h.val 0 < 1) :
    productSphereHeight (productHemisphere b (cliffordDiscCollarMap (t, h))) =
      if b then -h.val 0 else h.val 0 := by
  rw [productHemisphere_height, productDiscCollar_norm_sq t h hh]
  cases b <;> simp only [Bool.false_eq_true, ↓reduceIte] <;> ring

theorem productCarrier_matching_apply (t : Torus) :
    linearTorusDiffeomorph lensZeroMatrixUnit t = (t.1⁻¹, t.2) := by
  change linearTorusMap lensZeroMatrixUnit t = _
  simp [linearTorusMap, lensZeroMatrixUnit, PrimitiveSlope.val_unitOfDet]

theorem productCarrier_matching_conj (t : Torus) :
    ((linearTorusDiffeomorph lensZeroMatrixUnit t).1 : ℂ) = star (t.1 : ℂ) := by
  rw [productCarrier_matching_apply]
  exact Circle.coe_inv_eq_conj t.1

def productCarrierKind : Fin 2 → ℕ := Function.const _ 1

def productCarrierSide : Fin 1 → Bool → Σ j : Fin 2, Fin (productCarrierKind j) :=
  Function.const _ (fun b => ⟨if b then 0 else 1, ⟨0, by change 0 < 1; decide⟩⟩)

theorem productCarrierSide_bijective :
    Function.Bijective (Sum.elim (Function.uncurry productCarrierSide)
      (Fin.elim0 : Fin 0 → Σ j : Fin 2, Fin (productCarrierKind j))) := by
  constructor
  · intro x y he
    rcases x with ⟨c, b⟩ | x
    · rcases y with ⟨d, a⟩ | y
      · fin_cases c
        fin_cases d
        cases b <;> cases a <;> simp_all [productCarrierSide]
      · exact y.elim0
    · exact x.elim0
  · rintro ⟨j, k⟩
    fin_cases j <;> fin_cases k
    · exact ⟨.inl (0, true), rfl⟩
    · exact ⟨.inl (0, false), rfl⟩

def productEquatorRadius (s : ℝ) : ℝ := √(1 - seamClamp s ^ 2)

theorem productEquatorRadius_sq (s : ℝ) :
    productEquatorRadius s ^ 2 = 1 - seamClamp s ^ 2 := by
  apply Real.sq_sqrt
  have hl := neg_one_le_seamClamp s
  have hr := seamClamp_le_one s
  nlinarith

theorem productEquatorRadius_pos {s : ℝ} (hs : s ∈ Ioo (-1) 1) :
    0 < productEquatorRadius s := by
  rw [productEquatorRadius, seamClamp_of_mem hs.1.le hs.2.le]
  apply Real.sqrt_pos.mpr
  nlinarith [hs.1, hs.2]

def productEquatorMap (y : Circle × ℝ) : ProductSphere :=
  productSphereOfCoordinates (productEquatorRadius y.2 • (y.1 : ℂ)) (seamClamp y.2) (by
    have hr : 0 ≤ productEquatorRadius y.2 := Real.sqrt_nonneg _
    rw [norm_smul, Real.norm_of_nonneg hr, Circle.norm_coe, mul_one,
      productEquatorRadius_sq]
    ring)

def productEquatorInv (x : ProductSphere) : Circle × ℝ :=
  (unitOf (productSpherePlane x), productSphereHeight x)

theorem productEquatorMap_plane (y : Circle × ℝ) :
    productSpherePlane (productEquatorMap y) = productEquatorRadius y.2 • (y.1 : ℂ) :=
  productSpherePlane_ofCoordinates _ _ _

theorem productEquatorMap_height (y : Circle × ℝ) :
    productSphereHeight (productEquatorMap y) = seamClamp y.2 :=
  productSphereHeight_ofCoordinates _ _ _

theorem productEquator_height_mem {x : ProductSphere} (hx : productSpherePlane x ≠ 0) :
    productSphereHeight x ∈ Ioo (-1) 1 := by
  have hp := norm_pos_iff.mpr hx
  have he := productSphere_coordinates x
  have hb := productSphereHeight_bounds x
  constructor <;> nlinarith

theorem productEquatorRadius_height (x : ProductSphere) :
    productEquatorRadius (productSphereHeight x) = ‖productSpherePlane x‖ := by
  have hb := productSphereHeight_bounds x
  rw [productEquatorRadius, seamClamp_of_mem hb.1 hb.2]
  have he : 1 - productSphereHeight x ^ 2 = ‖productSpherePlane x‖ ^ 2 := by
    linarith [productSphere_coordinates x]
  rw [he, Real.sqrt_sq (norm_nonneg _)]

theorem productEquatorRadius_smooth :
    ContDiffOn ℝ ∞ productEquatorRadius (Ioo (-1) 1) := by
  intro s hs
  have hn : 1 - s ^ 2 ≠ 0 := by nlinarith [hs.1, hs.2]
  have hd : ContDiffAt ℝ ∞ (fun t : ℝ => √(1 - t ^ 2)) s :=
    (Real.contDiffAt_sqrt hn).comp s (contDiff_const.sub (contDiff_id.pow 2)).contDiffAt
  apply hd.contDiffWithinAt.congr
  · intro t ht
    rw [productEquatorRadius, seamClamp_of_mem ht.1.le ht.2.le]
  · rw [productEquatorRadius, seamClamp_of_mem hs.1.le hs.2.le]

def productEquator :
    PartialDiffeomorph ((𝓡 1).prod 𝓘(ℝ, ℝ)) (𝓡 2) (Circle × ℝ) ProductSphere ∞ where
  toFun := productEquatorMap
  invFun := productEquatorInv
  source := {y | -1 < y.2 ∧ y.2 < 1}
  target := {x | productSpherePlane x ≠ 0}
  map_source' := by
    intro y hy
    change productSpherePlane (productEquatorMap y) ≠ 0
    rw [productEquatorMap_plane]
    exact smul_ne_zero (productEquatorRadius_pos hy).ne' (Circle.coe_ne_zero _)
  map_target' := fun x hx => productEquator_height_mem hx
  left_inv' := by
    intro y hy
    apply Prod.ext
    · change unitOf (productSpherePlane (productEquatorMap y)) = y.1
      rw [productEquatorMap_plane]
      exact unitOf_smul (productEquatorRadius_pos hy) y.1
    · exact (productEquatorMap_height y).trans (seamClamp_of_mem hy.1.le hy.2.le)
  right_inv' := by
    intro x hx
    apply productSphere_ext
    · rw [productEquatorMap_plane]
      change productEquatorRadius (productSphereHeight x) •
        (unitOf (productSpherePlane x) : ℂ) = productSpherePlane x
      rw [productEquatorRadius_height, norm_smul_unitOf]
    · rw [productEquatorMap_height]
      exact seamClamp_of_mem (productSphereHeight_bounds x).1 (productSphereHeight_bounds x).2
  open_source :=
    (isOpen_lt continuous_const continuous_snd).inter (isOpen_lt continuous_snd continuous_const)
  open_target := isOpen_ne.preimage productSpherePlane_smooth.continuous
  contMDiffOn_toFun := by
    have ho : IsOpen {y : Circle × ℝ | -1 < y.2 ∧ y.2 < 1} :=
      (isOpen_lt continuous_const continuous_snd).inter
        (isOpen_lt continuous_snd continuous_const)
    apply contMDiffOn_sphere_of_val ho
    have hs : ContMDiffOn ((𝓡 1).prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, ℝ) ∞
        (fun y : Circle × ℝ => y.2) {y | -1 < y.2 ∧ y.2 < 1} :=
      contMDiff_snd.contMDiffOn
    have hr := productEquatorRadius_smooth.contMDiffOn.comp hs (fun y hy => hy)
    have hp := contMDiffOn_smul_of_real hr
      (contMDiff_circle_coe.comp contMDiff_fst).contMDiffOn
    have hh : ContMDiffOn ((𝓡 1).prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, ℝ) ∞
        (fun y : Circle × ℝ => seamClamp y.2) {y | -1 < y.2 ∧ y.2 < 1} := by
      apply hs.congr
      intro y hy
      exact seamClamp_of_mem hy.1.le hy.2.le
    exact productSphereCoordinates.symm.contDiff.contMDiff.comp_contMDiffOn
      (hp.prodMk_space hh)
  contMDiffOn_invFun :=
    (contMDiffOn_unitOf.comp productSpherePlane_smooth.contMDiffOn (fun x hx => hx)).prodMk
      productSphereHeight_smooth.contMDiffOn

theorem productEquator_source :
    productEquator.source = {y | -1 < y.2 ∧ y.2 < 1} := rfl

theorem productEquator_apply (y : Circle × ℝ) : productEquator y = productEquatorMap y := rfl


def productEquatorSigned :
    PartialDiffeomorph signedCollarModel ((𝓡 2).prod (𝓡 1))
      (Torus × ℝ) (ProductSphere × Circle) ∞ where
  toFun := fun y => (productEquator (y.1.1, y.2), y.1.2)
  invFun := fun x => (((productEquator.symm x.1).1, x.2),
    (productEquator.symm x.1).2)
  source := signedCollarSource
  target := {x | productSpherePlane x.1 ≠ 0}
  map_source' := fun y hy => productEquator.map_source hy
  map_target' := fun x hx => productEquator.map_target hx
  left_inv' := by
    intro y hy
    have he := productEquator.left_inv (x := (y.1.1, y.2)) hy
    have hf : (productEquator.symm (productEquator (y.1.1, y.2))).1 = y.1.1 :=
      congrArg (fun z : Circle × ℝ => z.1) he
    have hs : (productEquator.symm (productEquator (y.1.1, y.2))).2 = y.2 :=
      congrArg (fun z : Circle × ℝ => z.2) he
    exact Prod.ext (Prod.ext hf rfl) hs
  right_inv' := by
    intro x hx
    exact Prod.ext (productEquator.right_inv hx) rfl
  open_source := isOpen_signedCollarSource
  open_target := (isOpen_ne.preimage productSpherePlane_smooth.continuous).preimage continuous_fst
  contMDiffOn_toFun :=
    (productEquator.contMDiffOn.comp
      ((contMDiff_fst.comp contMDiff_fst).prodMk contMDiff_snd).contMDiffOn
      (fun y hy => hy)).prodMk (contMDiff_snd.comp contMDiff_fst).contMDiffOn
  contMDiffOn_invFun := by
    have hi : ContMDiffOn ((𝓡 2).prod (𝓡 1)) ((𝓡 1).prod 𝓘(ℝ, ℝ)) ∞
        (fun x : ProductSphere × Circle => productEquator.symm x.1)
        {x | productSpherePlane x.1 ≠ 0} :=
      productEquator.symm.contMDiffOn.comp contMDiff_fst.contMDiffOn (fun x hx => hx)
    exact ((contMDiff_fst.comp_contMDiffOn hi).prodMk contMDiff_snd.contMDiffOn).prodMk
      (contMDiff_snd.comp_contMDiffOn hi)

theorem productEquatorSigned_source :
    productEquatorSigned.source = signedCollarSource := rfl

theorem productEquatorSigned_apply (y : Torus × ℝ) :
    productEquatorSigned y = (productEquator (y.1.1, y.2), y.1.2) := rfl

def productCarrierSeam : PartialDiffeomorph signedCollarModel
    (NoCuts.carrier sphereTwoTimesCircleLift).model (Torus × ℝ)
      (NoCuts.carrier sphereTwoTimesCircleLift).Carrier ∞ :=
  productEquatorSigned.trans productCarrierCoordinatesDiffeomorph.toPartialDiffeomorph

theorem productCarrierSeam_source : productCarrierSeam.source = signedCollarSource := by
  ext y
  change (y ∈ signedCollarSource ∧ productEquatorSigned y ∈ Set.univ) ↔ _
  simp only [mem_univ, and_true]

theorem productCarrierSeam_apply (t : Torus) (s : ℝ) :
    productCarrierSeam (t, s) =
      productCarrierCoordinatesDiffeomorph (productEquatorMap (t.1, s), t.2) := rfl

theorem productCarrierSeam_zero (t : Torus) :
    productCarrierSeam (t, 0) =
      productCarrierCoordinatesDiffeomorph (productSphereEquator t.1, t.2) := by
  rw [productCarrierSeam_apply]
  apply congrArg productCarrierCoordinatesDiffeomorph
  apply Prod.ext
  · apply productSphere_ext
    · rw [productEquatorMap_plane, productSphereEquator, productSpherePlane_ofCoordinates]
      simp [productEquatorRadius, seamClamp_of_mem (by norm_num : (-1 : ℝ) ≤ 0)
        (by norm_num : (0 : ℝ) ≤ 1)]
    · rw [productEquatorMap_height, productSphereEquator, productSphereHeight_ofCoordinates]
      exact seamClamp_of_mem (by norm_num) (by norm_num)
  · rfl

theorem productCarrierSeam_neg (t : Torus) (s : ℝ) (hs : s ≤ 0) (h1 : -1 < s) :
    productCarrierSeam (t, s) = productCarrierHemisphere true
      (cliffordDiscCollarMap (t.1, halfPoint (-s) (neg_nonneg.mpr hs)), t.2) := by
  rw [productCarrierSeam_apply]
  apply congrArg productCarrierCoordinatesDiffeomorph
  apply Prod.ext
  · apply productSphere_ext
    · rw [productEquatorMap_plane, productHemisphere_collar_plane true t.1
        (halfPoint (-s) (neg_nonneg.mpr hs)) (by change -s < 1; linarith)]
      change productEquatorRadius s • (t.1 : ℂ) = Real.sqrt (1 - (-s) ^ 2) • (t.1 : ℂ)
      rw [productEquatorRadius, seamClamp_of_mem h1.le (by linarith), neg_sq]
    · rw [productEquatorMap_height, productHemisphere_collar_height true t.1
        (halfPoint (-s) (neg_nonneg.mpr hs)) (by change -s < 1; linarith)]
      change seamClamp s = -(-s)
      rw [seamClamp_of_mem h1.le (by linarith), neg_neg]
  · rfl

theorem productCarrierSeam_pos (t : Torus) (s : ℝ) (hs : 0 ≤ s) (h1 : s < 1) :
    productCarrierSeam (t, s) = productCarrierHemisphere false
      (cliffordDiscCollarMap ((linearTorusDiffeomorph lensZeroMatrixUnit t).1,
        halfPoint s hs), (linearTorusDiffeomorph lensZeroMatrixUnit t).2) := by
  rw [productCarrierSeam_apply, productCarrier_matching_apply]
  apply congrArg productCarrierCoordinatesDiffeomorph
  apply Prod.ext
  · apply productSphere_ext
    · rw [productEquatorMap_plane, productHemisphere_collar_plane false t.1⁻¹
        (halfPoint s hs) h1]
      change productEquatorRadius s • (t.1 : ℂ) =
        Real.sqrt (1 - s ^ 2) • star ((t.1⁻¹ : Circle) : ℂ)
      rw [productEquatorRadius, seamClamp_of_mem (by linarith) h1.le,
        Circle.coe_inv_eq_conj]
      change Real.sqrt (1 - s ^ 2) • (t.1 : ℂ) =
        Real.sqrt (1 - s ^ 2) • star (star (t.1 : ℂ))
      rw [star_star]
    · rw [productEquatorMap_height, productHemisphere_collar_height false t.1⁻¹
        (halfPoint s hs) h1]
      exact seamClamp_of_mem (by linarith) h1.le
  · rfl

theorem productCarrierHemisphere_cross_overlap (b : Bool) (p q : UnitDisc.{0} × Circle)
    (he : productCarrierHemisphere b p = productCarrierHemisphere (!b) q) :
    ∃ t, productCarrierHemisphere b p = productCarrierSeam (t, 0) := by
  have hfold := productCarrierCoordinatesDiffeomorph.injective he
  have hpoint : productHemisphere b p.1 = productHemisphere (!b) q.1 :=
    congrArg (fun y : ProductSphere × Circle => y.1) hfold
  have hl := productHemisphere_mem_side b p.1
  have hr := productHemisphere_mem_side (!b) q.1
  rw [← hpoint] at hr
  have hh : productSphereHeight (productHemisphere b p.1) = 0 := by
    unfold productHemisphereSide at hl hr
    cases b <;> simp only [Bool.not_false, Bool.not_true, Bool.false_eq_true, ↓reduceIte]
      at hl hr ⊢
    · exact le_antisymm hr hl
    · exact le_antisymm hl hr
  refine ⟨(unitOf (productSpherePlane (productHemisphere b p.1)), p.2), ?_⟩
  rw [productCarrierSeam_zero]
  exact congrArg productCarrierCoordinatesDiffeomorph
    (Prod.ext (productSphere_eq_equator_of_height_zero _ hh) rfl)

def productCarrierEmbeddedPieces :
    EmbeddedPieceSystem (NoCuts.carrier sphereTwoTimesCircleLift) where
  count := 2
  count_pos := by decide
  kind := productCarrierKind
  kind_mem j := by simp [productCarrierKind]
  base := Function.const _ unitDiscPlanarBase
  map j := productCarrierHemisphere (decide (j = 0))
  smooth j := productCarrierHemisphere_smooth (decide (j = 0))
  mfderiv_bijective j := productCarrierHemisphere_mfderiv_bijective (decide (j = 0))
  covers := by
    apply eq_univ_of_forall
    intro x
    obtain ⟨b, p, hp⟩ := productCarrierHemisphere_covers x
    cases b
    · exact mem_iUnion.mpr ⟨1, p, hp⟩
    · exact mem_iUnion.mpr ⟨0, p, hp⟩
  seamCount := 1
  side := productCarrierSide
  externalCount := 0
  externalSide := Fin.elim0
  sides_bijective := productCarrierSide_bijective
  matching := Function.const _ (linearTorusDiffeomorph lensZeroMatrixUnit)
  seam := Function.const _ productCarrierSeam
  seam_source c := by
    change (Function.const (Fin 1) productCarrierSeam c).source = signedCollarSource
    exact productCarrierSeam_source
  seam_neg c t s hs h1 := by
    change productCarrierSeam (t, s) = productCarrierHemisphere
      (decide ((productCarrierSide c true).1 = 0)) _
    exact productCarrierSeam_neg t s hs h1
  seam_pos c t s hs h1 := by
    change productCarrierSeam (t, s) = productCarrierHemisphere
      (decide ((productCarrierSide c false).1 = 0)) _
    exact productCarrierSeam_pos t s hs h1
  seam_interior c := by
    change (Function.const (Fin 1) productCarrierSeam c).target ⊆ (𝓡 3).interior _
    rw [ModelWithCorners.interior_eq_univ]
    exact subset_univ _
  external_local i := i.elim0
  overlap := by
    intro j k p q he
    fin_cases j <;> fin_cases k
    · left
      have hp := productCarrierHemisphere_injective true he
      cases hp
      rfl
    · right
      obtain ⟨t, ht⟩ := productCarrierHemisphere_cross_overlap true p q he
      exact ⟨0, t, ht⟩
    · right
      obtain ⟨t, ht⟩ := productCarrierHemisphere_cross_overlap false p q he
      exact ⟨0, t, ht⟩
    · left
      have hp := productCarrierHemisphere_injective false he
      cases hp
      rfl

def productCarrierTorusPresentation :
    TorusPresentation (NoCuts.carrier sphereTwoTimesCircleLift) :=
  productCarrierEmbeddedPieces.toCutSystem.toTorusPresentation

def productCarrierSeamIndex : Fin productCarrierTorusPresentation.pairing.count :=
  ⟨0, by change 0 < 1; decide⟩

theorem productCarrier_components_count : productCarrierTorusPresentation.components.count = 2 :=
  rfl

theorem productCarrier_pairing_count : productCarrierTorusPresentation.pairing.count = 1 := rfl

theorem productCarrier_matching :
    productCarrierTorusPresentation.pairing.matching productCarrierSeamIndex =
      linearTorusDiffeomorph lensZeroMatrixUnit := rfl

theorem productCarrier_left_ne_right :
    productCarrierTorusPresentation.leftPiece productCarrierSeamIndex ≠
      productCarrierTorusPresentation.rightPiece productCarrierSeamIndex := by
  change (0 : Fin 2) ≠ 1
  decide

def productCarrierLeftSide : productCarrierTorusPresentation.OwnedSide
    (productCarrierTorusPresentation.leftPiece productCarrierSeamIndex) :=
  ⟨.inl productCarrierSeamIndex, rfl⟩

def productCarrierRightSide : productCarrierTorusPresentation.OwnedSide
    (productCarrierTorusPresentation.rightPiece productCarrierSeamIndex) :=
  ⟨.inr (.inl productCarrierSeamIndex), rfl⟩

def productCarrierPieceDiffeomorph (j : Fin productCarrierTorusPresentation.components.count) :
    (UnitDisc.{0} × Circle) ≃ₘ⟮(𝓡∂ 2).prod (𝓡 1),
      productCarrierTorusPresentation.cutCarrier.model⟯
        productCarrierTorusPresentation.components.piece j :=
  (productCarrierEmbeddedPieces.certificate.piece j).trivialization

theorem productCarrierLeft_collar (r : Torus × EuclideanHalfSpace 1)
    (hr : r ∈ halfCollarSource) :
    productCarrierTorusPresentation.pieceCollar
      (productCarrierTorusPresentation.leftPiece productCarrierSeamIndex) productCarrierLeftSide r =
        productCarrierPieceDiffeomorph
          (productCarrierTorusPresentation.leftPiece productCarrierSeamIndex)
            (cliffordDiscCollarMap (r.1.1, r.2), r.1.2) := by
  apply Subtype.ext
  rw [TorusPresentation.pieceCollar_apply productCarrierTorusPresentation
    (productCarrierTorusPresentation.leftPiece productCarrierSeamIndex)
      productCarrierLeftSide hr]
  exact productCarrierEmbeddedPieces.toCutSystem.sideCollar_apply
    (productCarrierEmbeddedPieces.toCutSystem.side productCarrierSeamIndex true) r

theorem productCarrierRight_collar (r : Torus × EuclideanHalfSpace 1)
    (hr : r ∈ halfCollarSource) :
    productCarrierTorusPresentation.pieceCollar
      (productCarrierTorusPresentation.rightPiece productCarrierSeamIndex)
        productCarrierRightSide r =
        productCarrierPieceDiffeomorph
          (productCarrierTorusPresentation.rightPiece productCarrierSeamIndex)
            (cliffordDiscCollarMap (r.1.1, r.2), r.1.2) := by
  apply Subtype.ext
  rw [TorusPresentation.pieceCollar_apply productCarrierTorusPresentation
    (productCarrierTorusPresentation.rightPiece productCarrierSeamIndex)
      productCarrierRightSide hr]
  exact productCarrierEmbeddedPieces.toCutSystem.sideCollar_apply
    (productCarrierEmbeddedPieces.toCutSystem.side productCarrierSeamIndex false) r

theorem exists_productCarrierLeft_germ :
    ∃ δ > (0 : ℝ), ∃ Θ : (UnitDisc.{0} × Circle) ≃ₘ⟮(𝓡∂ 2).prod (𝓡 1),
      productCarrierTorusPresentation.cutCarrier.model⟯
        productCarrierTorusPresentation.components.piece
          (productCarrierTorusPresentation.leftPiece productCarrierSeamIndex),
      ∀ r, r ∈ halfCollarSource → r.2.val 0 < δ →
        productCarrierTorusPresentation.pieceCollar
          (productCarrierTorusPresentation.leftPiece productCarrierSeamIndex)
            productCarrierLeftSide r = Θ (cliffordDiscCollarMap (r.1.1, r.2), r.1.2) := by
  refine ⟨1, by norm_num, productCarrierPieceDiffeomorph _, ?_⟩
  intro r hr hlt
  exact productCarrierLeft_collar r (lt_of_lt_of_le (lt_min hr hlt) (min_le_left _ _))

theorem exists_productCarrierRight_germ :
    ∃ δ > (0 : ℝ), ∃ Θ : (UnitDisc.{0} × Circle) ≃ₘ⟮(𝓡∂ 2).prod (𝓡 1),
      productCarrierTorusPresentation.cutCarrier.model⟯
        productCarrierTorusPresentation.components.piece
          (productCarrierTorusPresentation.rightPiece productCarrierSeamIndex),
      ∀ r, r ∈ halfCollarSource → r.2.val 0 < δ →
        productCarrierTorusPresentation.pieceCollar
          (productCarrierTorusPresentation.rightPiece productCarrierSeamIndex)
            productCarrierRightSide r = Θ (cliffordDiscCollarMap (r.1.1, r.2), r.1.2) := by
  refine ⟨1, by norm_num, productCarrierPieceDiffeomorph _, ?_⟩
  intro r hr hlt
  exact productCarrierRight_collar r (lt_of_lt_of_le (lt_min hr hlt) (min_le_left _ _))

end GC.Seifert
