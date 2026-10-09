import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Seifert.MobiusRefibration
import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Seifert.FilledPants
import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.LensCover

/-!
# The Möbius circle bundle as a `D²(2, 2)` block: pieces and seams

Packet RG02, part 3, items (a) and (b), on `mobiusBundleSet ⊆ L(4, -1)` of
`Seifert/MobiusRefibration.lean`. Every local section of the lens quotient is written through the
twisted cover `mobiusCover = lensLeftCover 4 (-1)` of `GraphManifold/LensCover.lean`:
`y ↦ cover (Ψ y (circleRootOf 4 (f y)))` is smooth once `Ψ` is smooth and `ℤ/4`-equivariant in
the root (`TwistedCover.contMDiffAt_cover_root`), so no square root branch is ever chosen.

(a) Pants. For `(ζ, μ)` with `ζ ≠ ±3/2` put `ξ = (ζ - 3/2) / (ζ + 3/2)` and
`(w₁, w₂) = (A μ v⁻¹, B v)` with `A² = ‖ξ‖ / (1 + ‖ξ‖)`, `B² = 1 / (1 + ‖ξ‖)` and
`v⁴ = μ² / unitOf ξ` (`pantsSectionPoint`); its class `pantsSection` has base `J = ζ` and fibre
`w₁ w₂ / ‖w₁ w₂‖ = μ`. On `productSet 3` this is `mobiusPantsFold`: smooth
(`contMDiff_mobiusPantsFold`), with bijective differential (`mfderiv_mobiusPantsFold_bijective`,
through the smooth left inverse `pantsChart = (J, unitOf fibre)`), and a bijection onto
`mobiusPants` (`mobiusPantsFoldEquiv`) inverting `mobiusPantsCoordinates`.

(b) Solid tori. On K06c's `solidSet = {‖z‖ ≤ 3} × S¹` the folds `solidFoldPlus` and
`solidFoldMinus` are smooth, with base `J = ±3/2 + z² w⁻¹ / 18` (a local branch coordinate
`η = z w^(-1/2) / 3` with `J = ±3/2 + η² / 2`, as in K06c's `conePoint` for `p = 2`), fibre
`unitOf z`, and image in `‖J ∓ 3/2‖ ≤ 1/2`. The pairs are `(A z κ⁻¹, B κ)` and `(B κ⁻¹, A z κ)`
with `A, B` built from `54 ± z² w⁻¹` (`coneFirstScaleP`, `coneSecondScaleP`). At height zero the
solid-torus collar is glued to the collar of hole `j = 1, 2` of the pants by
`seamMatching = linearTorusDiffeomorph !![-2, 1; 1, 0]` (`mobiusPantsFold_hole_one_eq`,
`mobiusPantsFold_hole_two_eq`), of determinant `-1`, whose meridian image is `-(2, -1)`
(`seamMatching_meridian`). For this fibre section both holes carry the same slope `±(2, -1)`;
the mixed-sign normalisation of `twistedIBundleData` is a shear of the free port and is left to
consumers. The two collars are the halves of one signed collar: `mobiusSeamPoint j (t, s)`, the
point with base `c_j + (1/2 + s/4) t₁² t₂⁻¹` and fibre `t₁`, is smooth for `|s| < 1` and equals
the folded pants collar of `seamMatching t` at height `s ≥ 0` (`mobiusPantsFold_collar_eq_seam`)
and the folded solid-torus collar of `t` at height `-s ≥ 0` (`solidFoldPlus_collar_eq_seam`,
`solidFoldMinus_collar_eq_seam`).
-/

set_option autoImplicit false

noncomputable section
open Set Metric Function Filter
open DifferentialGeometry DifferentialGeometry.Topology GC.Endpoint GC.GraphManifold
open scoped Manifold ContDiff Topology ComplexConjugate

universe u

namespace GC.Seifert

attribute [local instance] fact_finrank_euclideanSpace_four finrank_real_complex_fact'

abbrev mobiusCover : TwistedCover 4 (lensCoeffQ 4 (-1) isCoprime_four_neg_one)
    (LensCarrier 4 (-1) isCoprime_four_neg_one) :=
  lensLeftCover 4 (-1) isCoprime_four_neg_one

theorem mobiusCover_cover (x : LensSphere) :
    mobiusCover.cover x = mobiusLensGroup.projection (sphereDownPoint x) :=
  rfl

theorem lensPair_sphereDown (x : LensSphere) :
    lensPair (sphereDown x) = (sphereFirst x, sphereSecond x) :=
  Prod.ext (lensCoordinates_fst _) (lensCoordinates_snd _)

theorem lensCoeffQ_cast :
    ((lensCoeffQ 4 (-1) isCoprime_four_neg_one : ℤ) : ZMod 4) = -1 := by
  have h := lensCoeffQ_mul_q 4 (-1) isCoprime_four_neg_one
  rw [Int.cast_neg, Int.cast_one, mul_neg_one] at h
  rw [← h, neg_neg]

theorem toCircle_lensCoeffQ_mul (j : ZMod 4) :
    ZMod.toCircle ((lensCoeffQ 4 (-1) isCoprime_four_neg_one : ZMod 4) * j) =
      (ZMod.toCircle j)⁻¹ := by
  rw [lensCoeffQ_cast, neg_one_mul, AddChar.map_neg_eq_inv]

def pantsXi (ζ : ℂ) : ℂ := (ζ - 3 / 2) / (ζ + 3 / 2)

def pantsFirstScale (ζ : ℂ) : ℝ := √(‖pantsXi ζ‖ / (1 + ‖pantsXi ζ‖))

def pantsSecondScale (ζ : ℂ) : ℝ := √((1 + ‖pantsXi ζ‖)⁻¹)

theorem pantsFirstScale_sq (ζ : ℂ) :
    pantsFirstScale ζ ^ 2 = ‖pantsXi ζ‖ / (1 + ‖pantsXi ζ‖) :=
  Real.sq_sqrt (by positivity)

theorem pantsSecondScale_sq (ζ : ℂ) : pantsSecondScale ζ ^ 2 = (1 + ‖pantsXi ζ‖)⁻¹ :=
  Real.sq_sqrt (by positivity)

theorem pantsScale_sq_add (ζ : ℂ) : pantsFirstScale ζ ^ 2 + pantsSecondScale ζ ^ 2 = 1 := by
  have h : (1 + ‖pantsXi ζ‖) ≠ 0 := by positivity
  rw [pantsFirstScale_sq, pantsSecondScale_sq]
  field_simp
  ring

theorem pantsSecondScale_pos (ζ : ℂ) : 0 < pantsSecondScale ζ :=
  Real.sqrt_pos.mpr (by positivity)

theorem pantsFirstScale_pos {ζ : ℂ} (h1 : ζ ≠ 3 / 2) (h2 : ζ ≠ -(3 / 2)) :
    0 < pantsFirstScale ζ := by
  have hs : ζ + 3 / 2 ≠ 0 := fun h => h2 (by linear_combination h)
  have hd : ζ - 3 / 2 ≠ 0 := fun h => h1 (by linear_combination h)
  have hx : 0 < ‖pantsXi ζ‖ := norm_pos_iff.mpr (div_ne_zero hd hs)
  exact Real.sqrt_pos.mpr (by positivity)

theorem pantsFirstScale_nonneg (ζ : ℂ) : 0 ≤ pantsFirstScale ζ := Real.sqrt_nonneg _

theorem pantsSecondScale_nonneg (ζ : ℂ) : 0 ≤ pantsSecondScale ζ := Real.sqrt_nonneg _

theorem contMDiffAt_complex_mul {F G X : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    [TopologicalSpace G] {J : ModelWithCorners ℝ F G} [TopologicalSpace X] [ChartedSpace G X]
    {f g : X → ℂ} {x : X} (hf : ContMDiffAt J 𝓘(ℝ, ℂ) ∞ f x)
    (hg : ContMDiffAt J 𝓘(ℝ, ℂ) ∞ g x) : ContMDiffAt J 𝓘(ℝ, ℂ) ∞ (fun y => f y * g y) x := by
  have hm : ContDiff ℝ ∞ (fun q : ℂ × ℂ => q.1 * q.2) := contDiff_fst.mul contDiff_snd
  exact hm.contMDiff.contMDiffAt.comp x (hf.prodMk_space hg)

theorem norm_pantsPair (ζ : ℂ) (μ v : Circle) :
    ‖(pantsFirstScale ζ : ℂ) * (μ : ℂ) * ((v⁻¹ : Circle) : ℂ)‖ ^ 2 +
      ‖(pantsSecondScale ζ : ℂ) * (v : ℂ)‖ ^ 2 = 1 := by
  simp only [norm_mul, Circle.norm_coe, mul_one, Complex.norm_real,
    Real.norm_of_nonneg (pantsFirstScale_nonneg ζ), Real.norm_of_nonneg (pantsSecondScale_nonneg ζ)]
  exact pantsScale_sq_add ζ

def pantsSectionPoint (y : PlaneLift.{u} × Circle) (v : Circle) : LensSphere :=
  sphereOfPair ((pantsFirstScale y.1.down : ℂ) * (y.2 : ℂ) * ((v⁻¹ : Circle) : ℂ))
    ((pantsSecondScale y.1.down : ℂ) * (v : ℂ)) (norm_pantsPair _ _ _)

theorem pantsSectionPoint_twist (y : PlaneLift.{u} × Circle) (v : Circle) (j : ZMod 4) :
    pantsSectionPoint y (ZMod.toCircle j * v) =
      lensTwist 4 (lensCoeffQ 4 (-1) isCoprime_four_neg_one) j (pantsSectionPoint y v) := by
  apply sphere_ext
  · rw [lensTwist, sphereFirst_circlePairAct, toCircle_lensCoeffQ_mul, pantsSectionPoint,
      pantsSectionPoint, sphereFirst_sphereOfPair, sphereFirst_sphereOfPair]
    simp only [mul_inv_rev, Circle.coe_mul, Circle.coe_inv]
    ring
  · rw [lensTwist, sphereSecond_circlePairAct, pantsSectionPoint, pantsSectionPoint,
      sphereSecond_sphereOfPair, sphereSecond_sphereOfPair, Circle.coe_mul]
    ring

def pantsRootTarget (y : PlaneLift.{u} × Circle) : Circle :=
  y.2 ^ 2 * (unitOf (pantsXi y.1.down))⁻¹

def pantsSection (y : PlaneLift.{u} × Circle) : mobiusLensGroup.Orbit :=
  mobiusCover.cover (pantsSectionPoint y (circleRootOf 4 (pantsRootTarget y)))

theorem pantsXi_ne_zero {ζ : ℂ} (h1 : ζ ≠ 3 / 2) (h2 : ζ ≠ -(3 / 2)) : pantsXi ζ ≠ 0 :=
  div_ne_zero (fun h => h1 (by linear_combination h)) (fun h => h2 (by linear_combination h))

theorem contDiffAt_pantsXi {ζ : ℂ} (h2 : ζ ≠ -(3 / 2)) : ContDiffAt ℝ ∞ pantsXi ζ := by
  have hs : ζ + 3 / 2 ≠ 0 := fun h => h2 (by linear_combination h)
  have h : ContDiffAt ℂ ∞ (fun z : ℂ => (z - 3 / 2) / (z + 3 / 2)) ζ :=
    (contDiffAt_id.sub contDiffAt_const).div (contDiffAt_id.add contDiffAt_const) hs
  exact h.restrict_scalars ℝ

theorem contDiffAt_norm_pantsXi {ζ : ℂ} (h1 : ζ ≠ 3 / 2) (h2 : ζ ≠ -(3 / 2)) :
    ContDiffAt ℝ ∞ (fun z : ℂ => ‖pantsXi z‖) ζ :=
  (contDiffAt_norm ℝ (pantsXi_ne_zero h1 h2)).comp ζ (contDiffAt_pantsXi h2)

theorem contDiffAt_pantsFirstScale {ζ : ℂ} (h1 : ζ ≠ 3 / 2) (h2 : ζ ≠ -(3 / 2)) :
    ContDiffAt ℝ ∞ pantsFirstScale ζ := by
  have hn := contDiffAt_norm_pantsXi h1 h2
  have hx : 0 < ‖pantsXi ζ‖ := norm_pos_iff.mpr (pantsXi_ne_zero h1 h2)
  have hd : ContDiffAt ℝ ∞ (fun z : ℂ => ‖pantsXi z‖ / (1 + ‖pantsXi z‖)) ζ :=
    hn.div (contDiffAt_const.add hn) (by positivity)
  exact hd.sqrt (by positivity)

theorem contDiffAt_pantsSecondScale {ζ : ℂ} (h1 : ζ ≠ 3 / 2) (h2 : ζ ≠ -(3 / 2)) :
    ContDiffAt ℝ ∞ pantsSecondScale ζ := by
  have hn := contDiffAt_norm_pantsXi h1 h2
  have hd : ContDiffAt ℝ ∞ (fun z : ℂ => (1 + ‖pantsXi z‖)⁻¹) ζ :=
    (contDiffAt_const.add hn).inv (by positivity)
  exact hd.sqrt (by positivity)

def pantsGood (y : PlaneLift.{u} × Circle) : Prop :=
  y.1.down ≠ 3 / 2 ∧ y.1.down ≠ -(3 / 2)

theorem isOpen_pantsGood : IsOpen {y : PlaneLift.{u} × Circle | pantsGood y} :=
  (isOpen_ne_fun (continuous_uliftDown.comp continuous_fst) continuous_const).inter
    (isOpen_ne_fun (continuous_uliftDown.comp continuous_fst) continuous_const)

theorem contMDiffAt_down_fst {y : PlaneLift.{u} × Circle} {g : ℂ → ℂ}
    (hg : ContDiffAt ℝ ∞ g y.1.down) :
    ContMDiffAt PlaneCircleModel 𝓘(ℝ, ℂ) ∞ (fun y : PlaneLift.{u} × Circle => g y.1.down) y :=
  hg.contMDiffAt.comp y (contMDiff_planeLift_down.comp contMDiff_fst).contMDiffAt

theorem contMDiffAt_pantsRootTarget {y : PlaneLift.{u} × Circle} (hy : pantsGood y) :
    ContMDiffAt PlaneCircleModel (𝓡 1) ∞ pantsRootTarget.{u} y := by
  have hxi : ContMDiffAt PlaneCircleModel 𝓘(ℝ, ℂ) ∞
      (fun y : PlaneLift.{u} × Circle => pantsXi y.1.down) y :=
    contMDiffAt_down_fst (contDiffAt_pantsXi hy.2)
  have hu : ContMDiffAt PlaneCircleModel (𝓡 1) ∞
      (fun y : PlaneLift.{u} × Circle => unitOf (pantsXi y.1.down)) y :=
    (contMDiffOn_unitOf.contMDiffAt (isOpen_ne.mem_nhds (pantsXi_ne_zero hy.1 hy.2))).comp y hxi
  exact ((contMDiff_pow 2).contMDiffAt.comp y contMDiff_snd.contMDiffAt).mul hu.inv

theorem contMDiffAt_pantsSectionPoint {y : PlaneLift.{u} × Circle} (hy : pantsGood y)
    (v : Circle) :
    ContMDiffAt (PlaneCircleModel.prod (𝓡 1)) (𝓡 3) ∞
      (fun p : (PlaneLift.{u} × Circle) × Circle => pantsSectionPoint p.1 p.2) (y, v) := by
  let s : Set ((PlaneLift.{u} × Circle) × Circle) := {p | pantsGood p.1}
  have hs : IsOpen s := isOpen_pantsGood.preimage continuous_fst
  have hA : ∀ p ∈ s, ContMDiffAt (PlaneCircleModel.prod (𝓡 1)) 𝓘(ℝ, ℂ) ∞
      (fun p : (PlaneLift.{u} × Circle) × Circle => (pantsFirstScale p.1.1.down : ℂ)) p :=
    fun p hp => (Complex.ofRealCLM.contDiff.contDiffAt.comp _
      (contDiffAt_pantsFirstScale hp.1 hp.2)).contMDiffAt.comp p
        ((contMDiff_planeLift_down.comp contMDiff_fst).comp contMDiff_fst).contMDiffAt
  have hB : ∀ p ∈ s, ContMDiffAt (PlaneCircleModel.prod (𝓡 1)) 𝓘(ℝ, ℂ) ∞
      (fun p : (PlaneLift.{u} × Circle) × Circle => (pantsSecondScale p.1.1.down : ℂ)) p :=
    fun p hp => (Complex.ofRealCLM.contDiff.contDiffAt.comp _
      (contDiffAt_pantsSecondScale hp.1 hp.2)).contMDiffAt.comp p
        ((contMDiff_planeLift_down.comp contMDiff_fst).comp contMDiff_fst).contMDiffAt
  have hμ : ContMDiff (PlaneCircleModel.prod (𝓡 1)) 𝓘(ℝ, ℂ) ∞
      (fun p : (PlaneLift.{u} × Circle) × Circle => (p.1.2 : ℂ)) :=
    contMDiff_circle_coe.comp (contMDiff_snd.comp contMDiff_fst)
  have hv : ContMDiff (PlaneCircleModel.prod (𝓡 1)) 𝓘(ℝ, ℂ) ∞
      (fun p : (PlaneLift.{u} × Circle) × Circle => (p.2 : ℂ)) :=
    contMDiff_circle_coe.comp contMDiff_snd
  have hvi : ContMDiff (PlaneCircleModel.prod (𝓡 1)) 𝓘(ℝ, ℂ) ∞
      (fun p : (PlaneLift.{u} × Circle) × Circle => ((p.2⁻¹ : Circle) : ℂ)) :=
    contMDiff_circle_coe.comp contMDiff_snd.inv
  refine (contMDiffOn_of_sphereFirst_sphereSecond hs ?_ ?_).contMDiffAt
    (hs.mem_nhds (show (y, v) ∈ s from hy))
  · intro p hp
    simp only [pantsSectionPoint, sphereFirst_sphereOfPair]
    exact (contMDiffAt_complex_mul (contMDiffAt_complex_mul (hA p hp) (hμ p))
      (hvi p)).contMDiffWithinAt
  · intro p hp
    simp only [pantsSectionPoint, sphereSecond_sphereOfPair]
    exact (contMDiffAt_complex_mul (hB p hp) (hv p)).contMDiffWithinAt

theorem contMDiffAt_pantsSection {y : PlaneLift.{u} × Circle} (hy : pantsGood y) :
    ContMDiffAt PlaneCircleModel (𝓡 3) ∞ pantsSection.{u} y :=
  mobiusCover.contMDiffAt_cover_root (contMDiffAt_pantsRootTarget hy)
    (contMDiffAt_pantsSectionPoint hy) (fun y' v j => pantsSectionPoint_twist y' v j)

theorem pantsXi_mul {ζ : ℂ} (h2 : ζ ≠ -(3 / 2)) : pantsXi ζ * (ζ + 3 / 2) = ζ - 3 / 2 :=
  div_mul_cancel₀ _ (fun h => h2 (by linear_combination h))

theorem pantsXi_ne_one {ζ : ℂ} (h2 : ζ ≠ -(3 / 2)) : pantsXi ζ ≠ 1 := by
  intro h
  have h' := pantsXi_mul h2
  rw [h, one_mul] at h'
  exact absurd (by linear_combination h' : (3 : ℂ) = 0) (by norm_num)

theorem pantsPair_fst_sq {ζ : ℂ} (μ v : Circle)
    (hv : v ^ 4 = μ ^ 2 * (unitOf (pantsXi ζ))⁻¹) :
    ((pantsFirstScale ζ : ℂ) * (μ : ℂ) * ((v⁻¹ : Circle) : ℂ)) ^ 2 =
      pantsXi ζ * ((pantsSecondScale ζ : ℂ) * (v : ℂ)) ^ 2 := by
  have hU : ((‖pantsXi ζ‖ : ℝ) : ℂ) * (unitOf (pantsXi ζ) : ℂ) = pantsXi ζ := by
    rw [← Complex.real_smul]
    exact norm_smul_unitOf _
  have hv' : (v : ℂ) ^ 4 * (unitOf (pantsXi ζ) : ℂ) = (μ : ℂ) ^ 2 := by
    have h := congrArg (fun c : Circle => (c : ℂ)) hv
    simp only [Circle.coe_pow, Circle.coe_mul, Circle.coe_inv] at h
    rw [h, mul_assoc, inv_mul_cancel₀ (Circle.coe_ne_zero _), mul_one]
  have hA2 : ((pantsFirstScale ζ : ℝ) : ℂ) ^ 2 =
      ((‖pantsXi ζ‖ : ℝ) : ℂ) * ((pantsSecondScale ζ : ℝ) : ℂ) ^ 2 := by
    rw [← Complex.ofReal_pow, ← Complex.ofReal_pow, ← Complex.ofReal_mul, pantsFirstScale_sq,
      pantsSecondScale_sq, div_eq_mul_inv]
  have hVV : (v : ℂ) * (v : ℂ)⁻¹ = 1 := mul_inv_cancel₀ (Circle.coe_ne_zero v)
  set A := ((pantsFirstScale ζ : ℝ) : ℂ)
  set B := ((pantsSecondScale ζ : ℝ) : ℂ)
  set r := ((‖pantsXi ζ‖ : ℝ) : ℂ)
  set U := (unitOf (pantsXi ζ) : ℂ)
  set M := (μ : ℂ)
  set V := (v : ℂ)
  rw [Circle.coe_inv, ← hU]
  linear_combination V⁻¹ ^ 2 * M ^ 2 * hA2 - r * B ^ 2 * V⁻¹ ^ 2 * hv' +
    r * B ^ 2 * U * V ^ 2 * (V * V⁻¹ + 1) * hVV

theorem pantsPair_sub_ne_zero {ζ : ℂ} (h2 : ζ ≠ -(3 / 2)) (v : Circle) :
    pantsXi ζ * ((pantsSecondScale ζ : ℂ) * (v : ℂ)) ^ 2 -
      ((pantsSecondScale ζ : ℂ) * (v : ℂ)) ^ 2 ≠ 0 := by
  have hB : ((pantsSecondScale ζ : ℝ) : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (pantsSecondScale_pos ζ).ne'
  rw [← sub_one_mul]
  exact mul_ne_zero (sub_ne_zero.mpr (pantsXi_ne_one h2))
    (pow_ne_zero 2 (mul_ne_zero hB (Circle.coe_ne_zero v)))

theorem bundleBasePoint_pantsPair {ζ : ℂ} (h2 : ζ ≠ -(3 / 2)) (μ v : Circle)
    (hv : v ^ 4 = μ ^ 2 * (unitOf (pantsXi ζ))⁻¹) :
    bundleBasePoint ((pantsFirstScale ζ : ℂ) * (μ : ℂ) * ((v⁻¹ : Circle) : ℂ),
      (pantsSecondScale ζ : ℂ) * (v : ℂ)) = ζ := by
  rw [bundleBasePoint]
  dsimp only
  rw [pantsPair_fst_sq μ v hv, div_eq_iff (pantsPair_sub_ne_zero h2 v)]
  linear_combination (-((pantsSecondScale ζ : ℂ) * (v : ℂ)) ^ 2) * pantsXi_mul h2

theorem pantsFibrePoint_pantsPair {ζ : ℂ} (h1 : ζ ≠ 3 / 2) (h2 : ζ ≠ -(3 / 2)) (μ v : Circle) :
    pantsFibrePoint ((pantsFirstScale ζ : ℂ) * (μ : ℂ) * ((v⁻¹ : Circle) : ℂ),
      (pantsSecondScale ζ : ℂ) * (v : ℂ)) = μ := by
  have hV : (v : ℂ) ≠ 0 := Circle.coe_ne_zero v
  have hVV : (v : ℂ)⁻¹ * (v : ℂ) = 1 := inv_mul_cancel₀ hV
  have hAB : 0 < pantsFirstScale ζ * pantsSecondScale ζ :=
    mul_pos (pantsFirstScale_pos h1 h2) (pantsSecondScale_pos ζ)
  have hp : (pantsFirstScale ζ : ℂ) * (μ : ℂ) * ((v⁻¹ : Circle) : ℂ) *
      ((pantsSecondScale ζ : ℂ) * (v : ℂ)) =
      ((pantsFirstScale ζ * pantsSecondScale ζ : ℝ) : ℂ) * (μ : ℂ) := by
    rw [Circle.coe_inv]
    push_cast
    linear_combination (pantsFirstScale ζ : ℂ) * (pantsSecondScale ζ : ℂ) * (μ : ℂ) * hVV
  rw [pantsFibrePoint]
  dsimp only
  rw [hp, norm_mul, Circle.norm_coe, mul_one, Complex.norm_real, Real.norm_of_nonneg hAB.le,
    mul_div_cancel_left₀ _ (Complex.ofReal_ne_zero.mpr hAB.ne')]

theorem pantsRootTarget_root (y : PlaneLift.{u} × Circle) :
    circleRootOf 4 (pantsRootTarget y) ^ 4 = y.2 ^ 2 * (unitOf (pantsXi y.1.down))⁻¹ :=
  circleRootOf_pow 4 _

def pantsSectionLift (y : PlaneLift.{u} × Circle) : LensSphere :=
  pantsSectionPoint y (circleRootOf 4 (pantsRootTarget y))

theorem pantsSection_eq (y : PlaneLift.{u} × Circle) :
    pantsSection y = mobiusLensGroup.projection (sphereDownPoint (pantsSectionLift y)) :=
  rfl

theorem lensPair_pantsSectionLift (y : PlaneLift.{u} × Circle) :
    lensPair (sphereDownPoint (pantsSectionLift y) : EuclideanSpace ℝ (Fin 4)) =
      ((pantsFirstScale y.1.down : ℂ) * (y.2 : ℂ) *
        ((circleRootOf 4 (pantsRootTarget y))⁻¹ : Circle),
        (pantsSecondScale y.1.down : ℂ) * (circleRootOf 4 (pantsRootTarget y) : ℂ)) := by
  change lensPair (sphereDown _) = _
  rw [lensPair_sphereDown, pantsSectionLift, pantsSectionPoint, sphereFirst_sphereOfPair,
    sphereSecond_sphereOfPair]

theorem bundleBasePoint_pantsSectionLift {y : PlaneLift.{u} × Circle} (hy : pantsGood y) :
    bundleBasePoint (lensPair (sphereDownPoint (pantsSectionLift y) :
      EuclideanSpace ℝ (Fin 4))) = y.1.down := by
  rw [lensPair_pantsSectionLift]
  exact bundleBasePoint_pantsPair hy.2 _ _ (pantsRootTarget_root y)

theorem pantsFibrePoint_pantsSectionLift {y : PlaneLift.{u} × Circle} (hy : pantsGood y) :
    pantsFibrePoint (lensPair (sphereDownPoint (pantsSectionLift y) :
      EuclideanSpace ℝ (Fin 4))) = y.2 := by
  rw [lensPair_pantsSectionLift]
  exact pantsFibrePoint_pantsPair hy.1 hy.2 _ _

theorem pantsGood_of_mem_productSet (x : productSet.{u} 3) : pantsGood x.val := by
  obtain ⟨-, h1, h2⟩ := planarModel_three_ne
    ((mem_planarSet_iff (Or.inr rfl) x.val.1).mp x.2)
  exact ⟨h1, h2⟩

theorem norm_le_three_of_mem_productSet (x : productSet.{u} 3) : ‖x.val.1.down‖ ≤ 3 :=
  (planarModel_three_ne ((mem_planarSet_iff (Or.inr rfl) x.val.1).mp x.2)).1

theorem pantsSectionLift_quartic (x : productSet.{u} 3) :
    bundleQuartic (lensPair (sphereDownPoint (pantsSectionLift x.val) :
      EuclideanSpace ℝ (Fin 4))) ≤ 0 := by
  have hy := pantsGood_of_mem_productSet x
  have hab : (lensPair (sphereDownPoint (pantsSectionLift x.val) :
      EuclideanSpace ℝ (Fin 4))).1 ^ 2 - (lensPair (sphereDownPoint (pantsSectionLift x.val) :
      EuclideanSpace ℝ (Fin 4))).2 ^ 2 ≠ 0 := by
    rw [lensPair_pantsSectionLift]
    dsimp only
    rw [pantsPair_fst_sq _ _ (pantsRootTarget_root x.val)]
    exact pantsPair_sub_ne_zero hy.2 _
  rw [bundleQuartic_nonpos_iff hab, bundleBasePoint_pantsSectionLift hy]
  exact norm_le_three_of_mem_productSet x

def mobiusPantsFold (x : productSet.{u} 3) : mobiusBundleSet.{u} :=
  ⟨lensUp (pantsSection x.val), pantsSectionLift_quartic x⟩

theorem lensDown_mobiusPantsFold (x : productSet.{u} 3) :
    lensDown (mobiusPantsFold x).val =
      mobiusLensGroup.projection (sphereDownPoint (pantsSectionLift x.val)) :=
  rfl

theorem mobiusBundleBase_mobiusPantsFold (x : productSet.{u} 3) :
    mobiusBundleBase (mobiusPantsFold x) = x.val.1.down := by
  rw [mobiusBundleBase_eq (lensDown_mobiusPantsFold x)]
  exact bundleBasePoint_pantsSectionLift (pantsGood_of_mem_productSet x)

theorem mobiusBundleFibre_mobiusPantsFold (x : productSet.{u} 3) :
    mobiusBundleFibre (mobiusPantsFold x) = x.val.2 := by
  rw [mobiusBundleFibre_eq (lensDown_mobiusPantsFold x)]
  exact pantsFibrePoint_pantsSectionLift (pantsGood_of_mem_productSet x)

theorem contMDiff_mobiusPantsFold : ContMDiff (𝓡∂ 3) (𝓡∂ 3) ∞ mobiusPantsFold.{u} := by
  refine (mobiusBundleAtlas.contMDiff_iff_subtype_val _).mpr fun x => ?_
  exact contMDiff_lensUp.contMDiffAt.comp x ((contMDiffAt_pantsSection
    (pantsGood_of_mem_productSet x)).comp x ((productAtlas.{u} 3).contMDiff_subtype_val x))

theorem mobiusPantsFold_mem_mobiusPants (x : productSet.{u} 3) :
    mobiusPantsFold x ∈ mobiusPants := by
  change mobiusBundleBase (mobiusPantsFold x) ∈ planarModel 3
  rw [mobiusBundleBase_mobiusPantsFold]
  exact (mem_planarSet_iff (Or.inr rfl) x.val.1).mp x.2

theorem mobiusPantsFold_injective : Injective mobiusPantsFold.{u} := by
  intro x x' h
  have hb := congrArg mobiusBundleBase h
  have hf := congrArg mobiusBundleFibre h
  rw [mobiusBundleBase_mobiusPantsFold, mobiusBundleBase_mobiusPantsFold] at hb
  rw [mobiusBundleFibre_mobiusPantsFold, mobiusBundleFibre_mobiusPantsFold] at hf
  exact Subtype.ext (Prod.ext (ULift.ext hb) (Circle.ext hf))

theorem exists_mobiusPantsFold_eq (y : mobiusBundleSet.{u}) (hy : y ∈ mobiusPants) :
    ∃ x : productSet.{u} 3, mobiusPantsFold x = y := by
  obtain ⟨-, h1, h2⟩ := planarModel_three_ne hy
  have hn := norm_mobiusBundleFibre y h1 h2
  let μ : Circle := ⟨mobiusBundleFibre y, mem_sphere_zero_iff_norm.mpr hn⟩
  have hx : ((ULift.up (mobiusBundleBase y) : PlaneLift.{u}), μ) ∈ productSet.{u} 3 :=
    (mem_planarSet_iff (Or.inr rfl) _).mpr hy
  refine ⟨⟨_, hx⟩, eq_of_mobiusBundleBase_eq_of_fibre_eq _ _ ?_ ?_ ?_ ?_⟩
  · rw [mobiusBundleBase_mobiusPantsFold]
    exact h1
  · rw [mobiusBundleBase_mobiusPantsFold]
    exact h2
  · rw [mobiusBundleBase_mobiusPantsFold]
  · rw [mobiusBundleFibre_mobiusPantsFold]

theorem pantsSectionLift_ne_zero {y : PlaneLift.{u} × Circle} (hy : pantsGood y) :
    (lensPair (sphereDownPoint (pantsSectionLift y) : EuclideanSpace ℝ (Fin 4))).1 *
      (lensPair (sphereDownPoint (pantsSectionLift y) : EuclideanSpace ℝ (Fin 4))).2 ≠ 0 := by
  rw [lensPair_pantsSectionLift]
  dsimp only
  refine mul_ne_zero (mul_ne_zero (mul_ne_zero ?_ (Circle.coe_ne_zero _))
    (Circle.coe_ne_zero _)) (mul_ne_zero ?_ (Circle.coe_ne_zero _))
  · exact Complex.ofReal_ne_zero.mpr (pantsFirstScale_pos hy.1 hy.2).ne'
  · exact Complex.ofReal_ne_zero.mpr (pantsSecondScale_pos _).ne'

theorem pantsSectionLift_sq_sub_ne_zero {y : PlaneLift.{u} × Circle} (hy : pantsGood y) :
    (lensPair (sphereDownPoint (pantsSectionLift y) : EuclideanSpace ℝ (Fin 4))).1 ^ 2 -
      (lensPair (sphereDownPoint (pantsSectionLift y) : EuclideanSpace ℝ (Fin 4))).2 ^ 2 ≠ 0 := by
  rw [lensPair_pantsSectionLift]
  dsimp only
  rw [pantsPair_fst_sq _ _ (pantsRootTarget_root y)]
  exact pantsPair_sub_ne_zero hy.2 _

def pantsChart (q : mobiusLens.{u}.Carrier) : PlaneLift.{u} × Circle :=
  (ULift.up (bundleBase (lensDown q)), unitOf (pantsFibre (lensDown q)))

theorem unitOf_circle (μ : Circle) : unitOf (μ : ℂ) = μ := by
  have h := unitOf_smul (r := 1) one_pos μ
  rwa [one_smul] at h

theorem pantsChart_pantsSection {y : PlaneLift.{u} × Circle} (hy : pantsGood y) :
    pantsChart (lensUp (pantsSection y)) = y := by
  refine Prod.ext (ULift.ext (bundleBasePoint_pantsSectionLift hy)) ?_
  change unitOf (pantsFibrePoint (lensPair (sphereDownPoint (pantsSectionLift y) :
    EuclideanSpace ℝ (Fin 4)))) = y.2
  rw [pantsFibrePoint_pantsSectionLift hy, unitOf_circle]

theorem contMDiffAt_pantsChart {y : PlaneLift.{u} × Circle} (hy : pantsGood y) :
    ContMDiffAt (𝓡 3) PlaneCircleModel ∞ pantsChart.{u} (lensUp (pantsSection y)) := by
  set x := sphereDownPoint (pantsSectionLift y)
  have hb : ContMDiffAt (𝓡 3) 𝓘(ℝ, ℂ) ∞ bundleBase (lensDown (lensUp.{u} (pantsSection y))) :=
    contMDiffAt_lensDescend (fun _ hε p => bundleBasePoint_lensUnitAction hε p) x
      (contDiffAt_bundleBasePoint (pantsSectionLift_sq_sub_ne_zero hy))
  have hf : ContMDiffAt (𝓡 3) 𝓘(ℝ, ℂ) ∞ pantsFibre (lensDown (lensUp.{u} (pantsSection y))) :=
    contMDiffAt_lensDescend (fun ε _ p => pantsFibrePoint_lensUnitAction ε p) x
      (contDiffAt_pantsFibrePoint (pantsSectionLift_ne_zero hy))
  have hμ : pantsFibre (lensDown (lensUp.{u} (pantsSection y))) ≠ 0 := by
    change pantsFibrePoint (lensPair (x : EuclideanSpace ℝ (Fin 4))) ≠ 0
    rw [pantsFibrePoint_pantsSectionLift hy]
    exact Circle.coe_ne_zero _
  have hu : ContMDiffAt (𝓡 3) (𝓡 1) ∞ (fun q => unitOf (pantsFibre q))
      (lensDown (lensUp.{u} (pantsSection y))) :=
    (contMDiffOn_unitOf.contMDiffAt (isOpen_ne.mem_nhds hμ)).comp _ hf
  have hd : ContMDiffAt (𝓡 3) (𝓡 3) ∞ lensDown.{u} (lensUp (pantsSection y)) :=
    contMDiff_lensDown.contMDiffAt
  exact (contMDiff_planeLift_up.contMDiffAt.comp _ (hb.comp (lensUp (pantsSection y)) hd)).prodMk
    (hu.comp (lensUp (pantsSection y)) hd)

theorem mfderiv_pantsSection_bijective {y : PlaneLift.{u} × Circle} (hy : pantsGood y) :
    Bijective (mfderiv PlaneCircleModel (𝓡 3) (fun y => lensUp.{u} (pantsSection y)) y) := by
  have hS : MDifferentiableAt PlaneCircleModel (𝓡 3) (fun y => lensUp.{u} (pantsSection y)) y :=
    (contMDiff_lensUp.contMDiffAt.comp y (contMDiffAt_pantsSection hy)).mdifferentiableAt
      (by simp)
  have hC : MDifferentiableAt (𝓡 3) PlaneCircleModel pantsChart.{u}
      (lensUp (pantsSection y)) :=
    (contMDiffAt_pantsChart hy).mdifferentiableAt (by simp)
  have heq : (pantsChart.{u} ∘ fun y => lensUp.{u} (pantsSection y)) =ᶠ[𝓝 y] id := by
    filter_upwards [isOpen_pantsGood.mem_nhds hy] with y' hy'
    exact pantsChart_pantsSection hy'
  have hcomp := mfderiv_comp y hC hS
  rw [heq.mfderiv_eq, mfderiv_id] at hcomp
  have hinj : Injective (mfderiv PlaneCircleModel (𝓡 3)
      (fun y => lensUp.{u} (pantsSection y)) y) := by
    intro v w hvw
    have hv := congrArg (fun L => L v) hcomp
    have hw := congrArg (fun L => L w) hcomp
    simp only [ContinuousLinearMap.comp_apply] at hv hw
    change v = _ at hv
    change w = _ at hw
    rw [hv, hw, hvw]
  refine ⟨hinj, ?_⟩
  have hdim : Module.finrank ℝ (TangentSpace PlaneCircleModel y) =
      Module.finrank ℝ (TangentSpace (𝓡 3) (lensUp.{u} (pantsSection y))) := by
    change Module.finrank ℝ (ℂ × EuclideanSpace ℝ (Fin 1)) =
      Module.finrank ℝ (EuclideanSpace ℝ (Fin 3))
    rw [finrank_planeCircleModel, finrank_euclideanSpace_fin]
  exact (LinearMap.injective_iff_surjective_of_finrank_eq_finrank hdim
    (f := (mfderiv PlaneCircleModel (𝓡 3) (fun y => lensUp.{u} (pantsSection y)) y :
      TangentSpace PlaneCircleModel y →ₗ[ℝ] TangentSpace (𝓡 3) _))).mp hinj

theorem mfderiv_mobiusPantsFold_bijective (x : productSet.{u} 3) :
    Bijective (mfderiv (𝓡∂ 3) (𝓡∂ 3) mobiusPantsFold x) := by
  have hy := pantsGood_of_mem_productSet x
  refine ConeFilling.bijective_mfderiv_of_comp (g := Subtype.val) (K := 𝓡 3)
    (mobiusBundleAtlas.contMDiff_subtype_val.mdifferentiableAt (by simp))
    (contMDiff_mobiusPantsFold.mdifferentiableAt (by simp))
    (mobiusBundleAtlas.mfderiv_subtypeVal_bijective _) ?_
  have hval : MDifferentiableAt (𝓡∂ 3) PlaneCircleModel (Subtype.val : productSet.{u} 3 → _) x :=
    (productAtlas.{u} 3).contMDiff_subtype_val.mdifferentiableAt (by simp)
  have hS : MDifferentiableAt PlaneCircleModel (𝓡 3) (fun y => lensUp.{u} (pantsSection y))
      x.val :=
    (contMDiff_lensUp.contMDiffAt.comp _ (contMDiffAt_pantsSection hy)).mdifferentiableAt
      (by simp)
  change Bijective (mfderiv (𝓡∂ 3) (𝓡 3)
    ((fun y => lensUp.{u} (pantsSection y)) ∘ Subtype.val) x)
  rw [mfderiv_comp x hS hval, ContinuousLinearMap.coe_comp]
  exact (mfderiv_pantsSection_bijective hy).comp
    ((productAtlas.{u} 3).mfderiv_subtypeVal_bijective x)

def mobiusPantsFoldEquiv : productSet.{u} 3 ≃ mobiusPants.{u} :=
  Equiv.ofBijective (fun x => ⟨mobiusPantsFold x, mobiusPantsFold_mem_mobiusPants x⟩)
    ⟨fun x x' h => mobiusPantsFold_injective (congrArg Subtype.val h), fun y => by
      obtain ⟨x, hx⟩ := exists_mobiusPantsFold_eq y.val y.2
      exact ⟨x, Subtype.ext hx⟩⟩

theorem mobiusPantsFoldEquiv_apply (x : productSet.{u} 3) :
    (mobiusPantsFoldEquiv x).val = mobiusPantsFold x :=
  rfl

theorem mobiusPantsCoordinates_mobiusPantsFoldEquiv (x : productSet.{u} 3) :
    mobiusPantsCoordinates (mobiusPantsFoldEquiv x) =
      (⟨x.val.1.down, (mem_planarSet_iff (Or.inr rfl) x.val.1).mp x.2⟩, x.val.2) :=
  Prod.ext (Subtype.ext (mobiusBundleBase_mobiusPantsFold x))
    (Circle.ext (mobiusBundleFibre_mobiusPantsFold x))

def coneSumP (q : ℂ × ℂ) : ℂ := 54 + q.1 ^ 2 * q.2

def coneTauP (q : ℂ × ℂ) : ℝ := ‖q.1‖ ^ 2 / ‖coneSumP q‖

def coneFirstScaleP (q : ℂ × ℂ) : ℝ := √(((1 + coneTauP q) * ‖coneSumP q‖)⁻¹)

def coneSecondScaleP (q : ℂ × ℂ) : ℝ := √((1 + coneTauP q)⁻¹)

theorem coneTauP_nonneg (q : ℂ × ℂ) : 0 ≤ coneTauP q := by
  unfold coneTauP
  positivity

theorem coneFirstScaleP_nonneg (q : ℂ × ℂ) : 0 ≤ coneFirstScaleP q := Real.sqrt_nonneg _

theorem coneSecondScaleP_nonneg (q : ℂ × ℂ) : 0 ≤ coneSecondScaleP q := Real.sqrt_nonneg _

theorem coneSecondScaleP_pos (q : ℂ × ℂ) : 0 < coneSecondScaleP q := by
  have h := coneTauP_nonneg q
  exact Real.sqrt_pos.mpr (inv_pos.mpr (by linarith))

theorem coneFirstScaleP_pos {q : ℂ × ℂ} (hq : coneSumP q ≠ 0) : 0 < coneFirstScaleP q := by
  have h := coneTauP_nonneg q
  have hT : 0 < ‖coneSumP q‖ := norm_pos_iff.mpr hq
  exact Real.sqrt_pos.mpr (inv_pos.mpr (mul_pos (by linarith) hT))

theorem coneScaleP_sq_add (q : ℂ × ℂ) :
    coneFirstScaleP q ^ 2 * ‖q.1‖ ^ 2 + coneSecondScaleP q ^ 2 = 1 := by
  have h0 := coneTauP_nonneg q
  rw [coneFirstScaleP, coneSecondScaleP, Real.sq_sqrt (inv_nonneg.mpr (mul_nonneg (by linarith)
    (norm_nonneg _))), Real.sq_sqrt (inv_nonneg.mpr (by linarith))]
  by_cases hS : ‖coneSumP q‖ = 0
  · have hτ : coneTauP q = 0 := by rw [coneTauP, hS, div_zero]
    rw [hS, mul_zero, inv_zero, zero_mul, hτ]
    norm_num
  · have hK : (1 + coneTauP q) * ‖coneSumP q‖ = ‖coneSumP q‖ + ‖q.1‖ ^ 2 := by
      rw [coneTauP, add_mul, one_mul, div_mul_cancel₀ _ hS]
    have hK0 : ‖coneSumP q‖ + ‖q.1‖ ^ 2 ≠ 0 := by
      have := norm_nonneg (coneSumP q)
      have := sq_nonneg ‖q.1‖
      intro h
      exact hS (by linarith)
    have hinv : (1 + coneTauP q)⁻¹ = ‖coneSumP q‖ * (‖coneSumP q‖ + ‖q.1‖ ^ 2)⁻¹ := by
      rw [← hK, mul_inv, mul_left_comm, mul_inv_cancel₀ hS, mul_one]
    rw [hK, hinv, mul_comm (‖coneSumP q‖), ← mul_add, add_comm (‖q.1‖ ^ 2),
      inv_mul_cancel₀ hK0]

theorem contDiffAt_coneSumP (q : ℂ × ℂ) : ContDiffAt ℝ ∞ coneSumP q :=
  contDiffAt_const.add ((contDiffAt_fst.pow 2).mul contDiffAt_snd)

theorem contDiffAt_coneScales {q : ℂ × ℂ} (hq : coneSumP q ≠ 0) :
    ContDiffAt ℝ ∞ coneFirstScaleP q ∧ ContDiffAt ℝ ∞ coneSecondScaleP q := by
  have hT : ContDiffAt ℝ ∞ (fun q => ‖coneSumP q‖) q :=
    (contDiffAt_norm ℝ hq).comp q (contDiffAt_coneSumP q)
  have hZ : ContDiffAt ℝ ∞ (fun q : ℂ × ℂ => ‖q.1‖ ^ 2) q :=
    (contDiff_norm_sq ℝ).contDiffAt.comp q contDiffAt_fst
  have hT0 : ‖coneSumP q‖ ≠ 0 := norm_ne_zero_iff.mpr hq
  have hτ : ContDiffAt ℝ ∞ coneTauP q := hZ.div hT hT0
  have h0 := coneTauP_nonneg q
  have h1 : ContDiffAt ℝ ∞ (fun q => 1 + coneTauP q) q := contDiffAt_const.add hτ
  have hTp : 0 < ‖coneSumP q‖ := norm_pos_iff.mpr hq
  refine ⟨((h1.mul hT).inv (mul_pos (by linarith) hTp).ne').sqrt ?_,
    (h1.inv (by linarith)).sqrt ?_⟩
  · exact (inv_pos.mpr (mul_pos (by linarith) hTp)).ne'
  · exact (inv_pos.mpr (by linarith)).ne'

def conePair (y : PlaneLift.{u} × Circle) : ℂ × ℂ := (y.1.down, ((y.2⁻¹ : Circle) : ℂ))

theorem contMDiff_conePair : ContMDiff PlaneCircleModel 𝓘(ℝ, ℂ × ℂ) ∞ conePair.{u} :=
  (contMDiff_planeLift_down.comp contMDiff_fst).prodMk_space
    (contMDiff_circle_coe.comp contMDiff_snd.inv)

theorem norm_solidPair (q : ℂ × ℂ) (κ : Circle) :
    ‖(coneFirstScaleP q : ℂ) * q.1 * ((κ⁻¹ : Circle) : ℂ)‖ ^ 2 +
      ‖(coneSecondScaleP q : ℂ) * (κ : ℂ)‖ ^ 2 = 1 := by
  simp only [norm_mul, Circle.norm_coe, mul_one, Complex.norm_real,
    Real.norm_of_nonneg (coneFirstScaleP_nonneg q), Real.norm_of_nonneg (coneSecondScaleP_nonneg q)]
  rw [mul_pow]
  exact coneScaleP_sq_add q

def solidSectionPoint (y : PlaneLift.{u} × Circle) (κ : Circle) : LensSphere :=
  sphereOfPair ((coneFirstScaleP (conePair y) : ℂ) * (conePair y).1 * ((κ⁻¹ : Circle) : ℂ))
    ((coneSecondScaleP (conePair y) : ℂ) * (κ : ℂ)) (norm_solidPair _ κ)

theorem solidSectionPoint_twist (y : PlaneLift.{u} × Circle) (κ : Circle) (j : ZMod 4) :
    solidSectionPoint y (ZMod.toCircle j * κ) =
      lensTwist 4 (lensCoeffQ 4 (-1) isCoprime_four_neg_one) j (solidSectionPoint y κ) := by
  apply sphere_ext
  · rw [lensTwist, sphereFirst_circlePairAct, toCircle_lensCoeffQ_mul, solidSectionPoint,
      solidSectionPoint, sphereFirst_sphereOfPair, sphereFirst_sphereOfPair]
    simp only [mul_inv_rev, Circle.coe_mul, Circle.coe_inv]
    ring
  · rw [lensTwist, sphereSecond_circlePairAct, solidSectionPoint, solidSectionPoint,
      sphereSecond_sphereOfPair, sphereSecond_sphereOfPair, Circle.coe_mul]
    ring

def solidRootTarget (y : PlaneLift.{u} × Circle) : Circle := y.2 * unitOf (coneSumP (conePair y))

def solidSectionLift (y : PlaneLift.{u} × Circle) : LensSphere :=
  solidSectionPoint y (circleRootOf 4 (solidRootTarget y))

def solidSection (y : PlaneLift.{u} × Circle) : mobiusLensGroup.Orbit :=
  mobiusCover.cover (solidSectionLift y)

def coneGood (y : PlaneLift.{u} × Circle) : Prop := coneSumP (conePair y) ≠ 0

theorem isOpen_coneGood : IsOpen {y : PlaneLift.{u} × Circle | coneGood y} :=
  isOpen_ne_fun ((contDiff_iff_contDiffAt.mpr contDiffAt_coneSumP).continuous.comp
    contMDiff_conePair.continuous) continuous_const

theorem contMDiffAt_solidRootTarget {y : PlaneLift.{u} × Circle} (hy : coneGood y) :
    ContMDiffAt PlaneCircleModel (𝓡 1) ∞ solidRootTarget.{u} y := by
  have hS : ContMDiffAt PlaneCircleModel 𝓘(ℝ, ℂ) ∞
      (fun y : PlaneLift.{u} × Circle => coneSumP (conePair y)) y :=
    (contDiffAt_coneSumP _).contMDiffAt.comp y contMDiff_conePair.contMDiffAt
  have hu : ContMDiffAt PlaneCircleModel (𝓡 1) ∞
      (fun y : PlaneLift.{u} × Circle => unitOf (coneSumP (conePair y))) y :=
    (contMDiffOn_unitOf.contMDiffAt (isOpen_ne.mem_nhds hy)).comp y hS
  exact contMDiff_snd.contMDiffAt.mul hu

theorem contMDiffAt_solidSectionPoint {y : PlaneLift.{u} × Circle} (hy : coneGood y)
    (v : Circle) :
    ContMDiffAt (PlaneCircleModel.prod (𝓡 1)) (𝓡 3) ∞
      (fun p : (PlaneLift.{u} × Circle) × Circle => solidSectionPoint p.1 p.2) (y, v) := by
  let s : Set ((PlaneLift.{u} × Circle) × Circle) := {p | coneGood p.1}
  have hs : IsOpen s := isOpen_coneGood.preimage continuous_fst
  have hq : ∀ p ∈ s, ContMDiffAt (PlaneCircleModel.prod (𝓡 1)) 𝓘(ℝ, ℂ × ℂ) ∞
      (fun p : (PlaneLift.{u} × Circle) × Circle => conePair p.1) p :=
    fun p _ => (contMDiff_conePair.comp contMDiff_fst).contMDiffAt
  have hA : ∀ p ∈ s, ContMDiffAt (PlaneCircleModel.prod (𝓡 1)) 𝓘(ℝ, ℂ) ∞
      (fun p : (PlaneLift.{u} × Circle) × Circle => (coneFirstScaleP (conePair p.1) : ℂ)) p :=
    fun p hp => (Complex.ofRealCLM.contDiff.contDiffAt.comp _
      (contDiffAt_coneScales hp).1).contMDiffAt.comp p (hq p hp)
  have hB : ∀ p ∈ s, ContMDiffAt (PlaneCircleModel.prod (𝓡 1)) 𝓘(ℝ, ℂ) ∞
      (fun p : (PlaneLift.{u} × Circle) × Circle => (coneSecondScaleP (conePair p.1) : ℂ)) p :=
    fun p hp => (Complex.ofRealCLM.contDiff.contDiffAt.comp _
      (contDiffAt_coneScales hp).2).contMDiffAt.comp p (hq p hp)
  have hz : ContMDiff (PlaneCircleModel.prod (𝓡 1)) 𝓘(ℝ, ℂ) ∞
      (fun p : (PlaneLift.{u} × Circle) × Circle => (conePair p.1).1) :=
    (contMDiff_planeLift_down.comp contMDiff_fst).comp contMDiff_fst
  have hv : ContMDiff (PlaneCircleModel.prod (𝓡 1)) 𝓘(ℝ, ℂ) ∞
      (fun p : (PlaneLift.{u} × Circle) × Circle => (p.2 : ℂ)) :=
    contMDiff_circle_coe.comp contMDiff_snd
  have hvi : ContMDiff (PlaneCircleModel.prod (𝓡 1)) 𝓘(ℝ, ℂ) ∞
      (fun p : (PlaneLift.{u} × Circle) × Circle => ((p.2⁻¹ : Circle) : ℂ)) :=
    contMDiff_circle_coe.comp contMDiff_snd.inv
  refine (contMDiffOn_of_sphereFirst_sphereSecond hs ?_ ?_).contMDiffAt
    (hs.mem_nhds (show (y, v) ∈ s from hy))
  · intro p hp
    simp only [solidSectionPoint, sphereFirst_sphereOfPair]
    exact (contMDiffAt_complex_mul (contMDiffAt_complex_mul (hA p hp) (hz p))
      (hvi p)).contMDiffWithinAt
  · intro p hp
    simp only [solidSectionPoint, sphereSecond_sphereOfPair]
    exact (contMDiffAt_complex_mul (hB p hp) (hv p)).contMDiffWithinAt

theorem contMDiffAt_solidSection {y : PlaneLift.{u} × Circle} (hy : coneGood y) :
    ContMDiffAt PlaneCircleModel (𝓡 3) ∞ solidSection.{u} y :=
  mobiusCover.contMDiffAt_cover_root (contMDiffAt_solidRootTarget hy)
    (contMDiffAt_solidSectionPoint hy) (fun y' v j => solidSectionPoint_twist y' v j)

theorem solidPair_key {q : ℂ × ℂ} (hq : coneSumP q ≠ 0) (w κ : Circle)
    (hw : ((w⁻¹ : Circle) : ℂ) = q.2) (hκ : κ ^ 4 = w * unitOf (coneSumP q)) :
    (54 + q.1 ^ 2 * q.2) * ((coneFirstScaleP q : ℂ) * q.1 * ((κ⁻¹ : Circle) : ℂ)) ^ 2 =
      q.1 ^ 2 * q.2 * ((coneSecondScaleP q : ℂ) * (κ : ℂ)) ^ 2 := by
  have hU : ((‖coneSumP q‖ : ℝ) : ℂ) * (unitOf (coneSumP q) : ℂ) = coneSumP q := by
    rw [← Complex.real_smul]
    exact norm_smul_unitOf _
  have hκ' : (κ : ℂ) ^ 4 = (w : ℂ) * (unitOf (coneSumP q) : ℂ) := by
    have h := congrArg (fun c : Circle => (c : ℂ)) hκ
    simpa only [Circle.coe_pow, Circle.coe_mul] using h
  have hT : ‖coneSumP q‖ ≠ 0 := norm_ne_zero_iff.mpr hq
  have hA2 : ((coneFirstScaleP q : ℝ) : ℂ) ^ 2 * ((‖coneSumP q‖ : ℝ) : ℂ) =
      ((coneSecondScaleP q : ℝ) : ℂ) ^ 2 := by
    have h0 := coneTauP_nonneg q
    rw [← Complex.ofReal_pow, ← Complex.ofReal_pow, ← Complex.ofReal_mul, coneFirstScaleP,
      coneSecondScaleP, Real.sq_sqrt (inv_nonneg.mpr (mul_nonneg (by linarith) (norm_nonneg _))),
      Real.sq_sqrt (inv_nonneg.mpr (by linarith)), mul_inv, mul_assoc, inv_mul_cancel₀ hT,
      mul_one]
  have hW : (w : ℂ) * q.2 = 1 := by
    rw [← hw, Circle.coe_inv, mul_inv_cancel₀ (Circle.coe_ne_zero w)]
  have hΩ : (κ : ℂ) * (κ : ℂ)⁻¹ = 1 := mul_inv_cancel₀ (Circle.coe_ne_zero κ)
  have hS : coneSumP q = 54 + q.1 ^ 2 * q.2 := rfl
  set A := ((coneFirstScaleP q : ℝ) : ℂ)
  set B := ((coneSecondScaleP q : ℝ) : ℂ)
  set T := ((‖coneSumP q‖ : ℝ) : ℂ)
  set U := (unitOf (coneSumP q) : ℂ)
  set Ω := (κ : ℂ)
  rw [Circle.coe_inv, ← hS]
  linear_combination (-(A ^ 2 * q.1 ^ 2 * Ω⁻¹ ^ 2)) * hU + (U * q.1 ^ 2 * Ω⁻¹ ^ 2) * hA2 +
    q.1 ^ 2 * B ^ 2 * (-(q.2 * Ω⁻¹ ^ 2) * hκ' + q.2 * Ω ^ 2 * (Ω * Ω⁻¹ + 1) * hΩ -
      U * Ω⁻¹ ^ 2 * hW)

theorem solidPair_sub_ne_zero {q : ℂ × ℂ} (hq : coneSumP q ≠ 0) (w κ : Circle)
    (hw : ((w⁻¹ : Circle) : ℂ) = q.2) (hκ : κ ^ 4 = w * unitOf (coneSumP q)) :
    ((coneFirstScaleP q : ℂ) * q.1 * ((κ⁻¹ : Circle) : ℂ)) ^ 2 -
      ((coneSecondScaleP q : ℂ) * (κ : ℂ)) ^ 2 ≠ 0 := by
  intro h
  have hk := solidPair_key hq w κ hw hκ
  have hb : ((coneSecondScaleP q : ℂ) * (κ : ℂ)) ^ 2 ≠ 0 :=
    pow_ne_zero 2 (mul_ne_zero (Complex.ofReal_ne_zero.mpr (coneSecondScaleP_pos q).ne')
      (Circle.coe_ne_zero κ))
  rw [sub_eq_zero.mp h] at hk
  exact hb (by linear_combination hk / 54)

theorem bundleBasePoint_solidPair {q : ℂ × ℂ} (hq : coneSumP q ≠ 0) (w κ : Circle)
    (hw : ((w⁻¹ : Circle) : ℂ) = q.2) (hκ : κ ^ 4 = w * unitOf (coneSumP q)) :
    bundleBasePoint ((coneFirstScaleP q : ℂ) * q.1 * ((κ⁻¹ : Circle) : ℂ),
      (coneSecondScaleP q : ℂ) * (κ : ℂ)) = 3 / 2 + q.1 ^ 2 * q.2 / 18 := by
  rw [bundleBasePoint]
  dsimp only
  rw [div_eq_iff (solidPair_sub_ne_zero hq w κ hw hκ)]
  linear_combination (-1 / 18 : ℂ) * solidPair_key hq w κ hw hκ

theorem pantsFibrePoint_solidPair {q : ℂ × ℂ} (hq : coneSumP q ≠ 0) (hz : q.1 ≠ 0)
    (κ : Circle) :
    pantsFibrePoint ((coneFirstScaleP q : ℂ) * q.1 * ((κ⁻¹ : Circle) : ℂ),
      (coneSecondScaleP q : ℂ) * (κ : ℂ)) = (unitOf q.1 : ℂ) := by
  have hAB : 0 < coneFirstScaleP q * coneSecondScaleP q :=
    mul_pos (coneFirstScaleP_pos hq) (coneSecondScaleP_pos q)
  have hKK : (κ : ℂ)⁻¹ * (κ : ℂ) = 1 := inv_mul_cancel₀ (Circle.coe_ne_zero κ)
  have hp : (coneFirstScaleP q : ℂ) * q.1 * ((κ⁻¹ : Circle) : ℂ) *
      ((coneSecondScaleP q : ℂ) * (κ : ℂ)) =
      ((coneFirstScaleP q * coneSecondScaleP q : ℝ) : ℂ) * q.1 := by
    rw [Circle.coe_inv, Complex.ofReal_mul]
    linear_combination (coneFirstScaleP q : ℂ) * q.1 * (coneSecondScaleP q : ℂ) * hKK
  have hn : ‖((coneFirstScaleP q * coneSecondScaleP q : ℝ) : ℂ) * q.1‖ =
      (coneFirstScaleP q * coneSecondScaleP q) * ‖q.1‖ := by
    rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg hAB.le]
  rw [pantsFibrePoint]
  dsimp only
  rw [hp, hn, Complex.ofReal_mul (coneFirstScaleP q * coneSecondScaleP q) ‖q.1‖,
    mul_div_mul_left _ _ (Complex.ofReal_ne_zero.mpr hAB.ne'), coe_unitOf hz,
    Complex.real_smul, div_eq_inv_mul, Complex.ofReal_inv]

theorem coneGood_of_mem_solidSet (x : solidSet.{u}) : coneGood x.val := by
  intro h
  have hz := (mem_solidSet_iff x.val).mp x.2
  change 54 + x.val.1.down ^ 2 * ((x.val.2⁻¹ : Circle) : ℂ) = 0 at h
  have h1 : (54 : ℂ) = -(x.val.1.down ^ 2 * ((x.val.2⁻¹ : Circle) : ℂ)) := by
    linear_combination h
  have h2 : ‖(54 : ℂ)‖ = ‖x.val.1.down‖ ^ 2 := by
    rw [h1, norm_neg, norm_mul, norm_pow, Circle.norm_coe, mul_one]
  have h3 : ‖(54 : ℂ)‖ = 54 := by norm_num
  rw [h3] at h2
  nlinarith [norm_nonneg x.val.1.down]

theorem lensPair_solidSectionLift (y : PlaneLift.{u} × Circle) :
    lensPair (sphereDownPoint (solidSectionLift y) : EuclideanSpace ℝ (Fin 4)) =
      ((coneFirstScaleP (conePair y) : ℂ) * (conePair y).1 *
        ((circleRootOf 4 (solidRootTarget y))⁻¹ : Circle),
        (coneSecondScaleP (conePair y) : ℂ) * (circleRootOf 4 (solidRootTarget y) : ℂ)) := by
  change lensPair (sphereDown _) = _
  rw [lensPair_sphereDown, solidSectionLift, solidSectionPoint, sphereFirst_sphereOfPair,
    sphereSecond_sphereOfPair]

theorem bundleBasePoint_solidSectionLift {y : PlaneLift.{u} × Circle} (hy : coneGood y) :
    bundleBasePoint (lensPair (sphereDownPoint (solidSectionLift y) :
      EuclideanSpace ℝ (Fin 4))) = 3 / 2 + y.1.down ^ 2 * ((y.2⁻¹ : Circle) : ℂ) / 18 := by
  rw [lensPair_solidSectionLift]
  exact bundleBasePoint_solidPair hy y.2 _ rfl (circleRootOf_pow 4 _)

theorem solidSectionLift_sq_sub_ne_zero {y : PlaneLift.{u} × Circle} (hy : coneGood y) :
    (lensPair (sphereDownPoint (solidSectionLift y) : EuclideanSpace ℝ (Fin 4))).1 ^ 2 -
      (lensPair (sphereDownPoint (solidSectionLift y) : EuclideanSpace ℝ (Fin 4))).2 ^ 2 ≠ 0 := by
  rw [lensPair_solidSectionLift]
  exact solidPair_sub_ne_zero hy y.2 _ rfl (circleRootOf_pow 4 _)

theorem norm_cone_base_sub_le (x : solidSet.{u}) :
    ‖x.val.1.down ^ 2 * ((x.val.2⁻¹ : Circle) : ℂ) / 18‖ ≤ 1 / 2 := by
  have hz := (mem_solidSet_iff x.val).mp x.2
  rw [norm_div, norm_mul, norm_pow, Circle.norm_coe, mul_one]
  have h18 : ‖(18 : ℂ)‖ = 18 := by norm_num
  rw [h18]
  nlinarith [norm_nonneg x.val.1.down]

theorem solidSectionLift_quartic (x : solidSet.{u}) :
    bundleQuartic (lensPair (sphereDownPoint (solidSectionLift x.val) :
      EuclideanSpace ℝ (Fin 4))) ≤ 0 := by
  have hy := coneGood_of_mem_solidSet x
  rw [bundleQuartic_nonpos_iff (solidSectionLift_sq_sub_ne_zero hy),
    bundleBasePoint_solidSectionLift hy]
  have h := norm_cone_base_sub_le x
  calc ‖3 / 2 + x.val.1.down ^ 2 * ((x.val.2⁻¹ : Circle) : ℂ) / 18‖
      ≤ ‖(3 / 2 : ℂ)‖ + ‖x.val.1.down ^ 2 * ((x.val.2⁻¹ : Circle) : ℂ) / 18‖ := norm_add_le _ _
    _ ≤ 3 := by
      have h32 : ‖(3 / 2 : ℂ)‖ = 3 / 2 := by norm_num
      rw [h32]
      linarith

def solidFoldPlus (x : solidSet.{u}) : mobiusBundleSet.{u} :=
  ⟨lensUp (solidSection x.val), solidSectionLift_quartic x⟩

theorem lensDown_solidFoldPlus (x : solidSet.{u}) :
    lensDown (solidFoldPlus x).val =
      mobiusLensGroup.projection (sphereDownPoint (solidSectionLift x.val)) :=
  rfl

theorem contMDiff_solidFoldPlus : ContMDiff (𝓡∂ 3) (𝓡∂ 3) ∞ solidFoldPlus.{u} := by
  refine (mobiusBundleAtlas.contMDiff_iff_subtype_val _).mpr fun x => ?_
  exact contMDiff_lensUp.contMDiffAt.comp x ((contMDiffAt_solidSection
    (coneGood_of_mem_solidSet x)).comp x (solidAtlas.contMDiff_subtype_val x))

theorem mobiusBundleBase_solidFoldPlus (x : solidSet.{u}) :
    mobiusBundleBase (solidFoldPlus x) =
      3 / 2 + x.val.1.down ^ 2 * ((x.val.2⁻¹ : Circle) : ℂ) / 18 := by
  rw [mobiusBundleBase_eq (lensDown_solidFoldPlus x)]
  exact bundleBasePoint_solidSectionLift (coneGood_of_mem_solidSet x)

theorem mobiusBundleFibre_solidFoldPlus (x : solidSet.{u}) (hz : x.val.1.down ≠ 0) :
    mobiusBundleFibre (solidFoldPlus x) = (unitOf x.val.1.down : ℂ) := by
  rw [mobiusBundleFibre_eq (lensDown_solidFoldPlus x), lensPair_solidSectionLift]
  exact pantsFibrePoint_solidPair (coneGood_of_mem_solidSet x) hz _

theorem norm_mobiusBundleBase_solidFoldPlus_sub (x : solidSet.{u}) :
    ‖mobiusBundleBase (solidFoldPlus x) - 3 / 2‖ ≤ 1 / 2 := by
  rw [mobiusBundleBase_solidFoldPlus, add_sub_cancel_left]
  exact norm_cone_base_sub_le x

def seamMatrix : Matrix (Fin 2) (Fin 2) ℤ := !![-2, 1; 1, 0]

theorem det_seamMatrix : seamMatrix.det = -1 := by
  simp [seamMatrix, Matrix.det_fin_two]

def seamUnit : GL (Fin 2) ℤ := PrimitiveSlope.unitOfDet seamMatrix (Or.inr det_seamMatrix)

def seamMatching : Torus ≃ₘ⟮torusModel, torusModel⟯ Torus := linearTorusDiffeomorph seamUnit

theorem seamMatching_apply (t : Torus) : seamMatching t = (t.1 ^ (-2 : ℤ) * t.2, t.1) := by
  change linearTorusMap seamMatrix t = _
  simp [linearTorusMap, seamMatrix]

theorem torusMatrix_seamMatching : torusMatrix seamMatching = seamMatrix :=
  torusMatrix_linearTorusDiffeomorph seamUnit

theorem seamMatching_meridian :
    torusUnit seamMatching • meridianSlope = PrimitiveSlope.mk (2, -1) (by decide) := by
  rw [meridianSlope, PrimitiveSlope.smul_mk, PrimitiveSlope.mk_eq_mk_iff]
  right
  change ((2 : ℤ), (-1 : ℤ)) = -smulVec (torusMatrix seamMatching) (1, 0)
  rw [torusMatrix_seamMatching]
  simp [smulVec, seamMatrix]

theorem circle_seam_inv (t : Torus) :
    conj (((t.1 ^ (-2 : ℤ) * t.2 : Circle)) : ℂ) = (t.1 : ℂ) ^ 2 * ((t.2⁻¹ : Circle) : ℂ) := by
  rw [← Circle.coe_inv_eq_conj, mul_inv_rev, zpow_neg, inv_inv, Circle.coe_mul, Circle.coe_zpow,
    mul_comm]
  norm_cast

theorem productCollar_hole_val (j : Fin 3) (t : Torus) :
    (productCollar.{u} 3 (Or.inr rfl) j (t, halfZero)).val =
      (ULift.up (planarCircleMap 3 j t.1), t.2) :=
  Prod.ext (ULift.ext (planarCollar_zero_val.{u} (Or.inr rfl) j t.1)) rfl

theorem planarCircleMap_hole (j : Fin 3) (hj : j.val ≠ 0) (t : Circle) :
    planarCircleMap 3 j t = (planarCenter 3 j : ℂ) + 1 / 2 * conj (t : ℂ) := by
  simp only [planarCircleMap, planarRadius, hj, ite_false]
  push_cast
  ring

theorem planarCenter_three_one : planarCenter 3 1 = 3 / 2 := by
  simp [planarCenter]

theorem planarCenter_three_two : planarCenter 3 2 = -(3 / 2) := by
  simp [planarCenter]

theorem mobiusBundleBase_mobiusPantsFold_hole (j : Fin 3) (hj : j.val ≠ 0) (t : Torus) :
    mobiusBundleBase
        (mobiusPantsFold (productCollar.{u} 3 (Or.inr rfl) j (seamMatching t, halfZero))) =
      (planarCenter 3 j : ℂ) + (t.1 : ℂ) ^ 2 * ((t.2⁻¹ : Circle) : ℂ) / 2 := by
  rw [mobiusBundleBase_mobiusPantsFold, productCollar_hole_val, planarCircleMap_hole j hj,
    seamMatching_apply, circle_seam_inv]
  ring

theorem mobiusBundleFibre_mobiusPantsFold_hole (j : Fin 3) (t : Torus) :
    mobiusBundleFibre
        (mobiusPantsFold (productCollar.{u} 3 (Or.inr rfl) j (seamMatching t, halfZero))) =
      (t.1 : ℂ) := by
  rw [mobiusBundleFibre_mobiusPantsFold, productCollar_hole_val, seamMatching_apply]

theorem solidCollar_zero_ne (t : Torus) :
    (solidCollar.{u} 2 (t, halfZero)).val.1.down ≠ 0 := by
  rw [solidCollar_zero_val]
  exact smul_ne_zero (by norm_num) (Circle.coe_ne_zero _)

theorem cone_base_solidCollar (t : Torus) :
    (solidCollar.{u} 2 (t, halfZero)).val.1.down ^ 2 *
      (((solidCollar.{u} 2 (t, halfZero)).val.2⁻¹ : Circle) : ℂ) / 18 =
      (t.1 : ℂ) ^ 2 * ((t.2⁻¹ : Circle) : ℂ) / 2 := by
  rw [solidCollar_zero_val]
  dsimp only
  rw [Complex.real_smul]
  push_cast
  ring

theorem norm_cone_base_solidCollar (t : Torus) :
    ‖(t.1 : ℂ) ^ 2 * ((t.2⁻¹ : Circle) : ℂ) / 2‖ = 1 / 2 := by
  rw [norm_div, norm_mul, norm_pow, Circle.norm_coe, Circle.norm_coe]
  norm_num

theorem mobiusPantsFold_hole_one_eq (t : Torus) :
    mobiusPantsFold (productCollar.{u} 3 (Or.inr rfl) 1 (seamMatching t, halfZero)) =
      solidFoldPlus (solidCollar.{u} 2 (t, halfZero)) := by
  have hb : mobiusBundleBase (solidFoldPlus (solidCollar.{u} 2 (t, halfZero))) =
      3 / 2 + (t.1 : ℂ) ^ 2 * ((t.2⁻¹ : Circle) : ℂ) / 2 := by
    rw [mobiusBundleBase_solidFoldPlus, cone_base_solidCollar]
  have hn := norm_cone_base_solidCollar t
  refine (eq_of_mobiusBundleBase_eq_of_fibre_eq _ _ ?_ ?_ ?_ ?_).symm
  · rw [hb]
    intro h
    have h' : (t.1 : ℂ) ^ 2 * ((t.2⁻¹ : Circle) : ℂ) / 2 = 0 := by linear_combination h
    rw [h', norm_zero] at hn
    norm_num at hn
  · rw [hb]
    intro h
    have h' : (t.1 : ℂ) ^ 2 * ((t.2⁻¹ : Circle) : ℂ) / 2 = -3 := by linear_combination h
    rw [h', norm_neg] at hn
    norm_num at hn
  · rw [hb, mobiusBundleBase_mobiusPantsFold_hole 1 (by decide), planarCenter_three_one]
    push_cast
    ring
  · rw [mobiusBundleFibre_solidFoldPlus _ (solidCollar_zero_ne t),
      mobiusBundleFibre_mobiusPantsFold_hole, solidCollar_zero_val]
    dsimp only
    rw [unitOf_smul (by norm_num : (0 : ℝ) < 3)]

def conePairNeg (y : PlaneLift.{u} × Circle) : ℂ × ℂ := (y.1.down, -((y.2⁻¹ : Circle) : ℂ))

theorem contMDiff_conePairNeg : ContMDiff PlaneCircleModel 𝓘(ℝ, ℂ × ℂ) ∞ conePairNeg.{u} :=
  (contMDiff_planeLift_down.comp contMDiff_fst).prodMk_space
    (contMDiff_circle_coe.comp contMDiff_snd.inv).neg

theorem norm_solidPairNeg (q : ℂ × ℂ) (κ : Circle) :
    ‖(coneSecondScaleP q : ℂ) * ((κ⁻¹ : Circle) : ℂ)‖ ^ 2 +
      ‖(coneFirstScaleP q : ℂ) * q.1 * (κ : ℂ)‖ ^ 2 = 1 := by
  simp only [norm_mul, Circle.norm_coe, mul_one, Complex.norm_real,
    Real.norm_of_nonneg (coneFirstScaleP_nonneg q), Real.norm_of_nonneg (coneSecondScaleP_nonneg q)]
  rw [mul_pow, add_comm]
  exact coneScaleP_sq_add q

def solidNegSectionPoint (y : PlaneLift.{u} × Circle) (κ : Circle) : LensSphere :=
  sphereOfPair ((coneSecondScaleP (conePairNeg y) : ℂ) * ((κ⁻¹ : Circle) : ℂ))
    ((coneFirstScaleP (conePairNeg y) : ℂ) * (conePairNeg y).1 * (κ : ℂ)) (norm_solidPairNeg _ κ)

theorem solidNegSectionPoint_twist (y : PlaneLift.{u} × Circle) (κ : Circle) (j : ZMod 4) :
    solidNegSectionPoint y (ZMod.toCircle j * κ) =
      lensTwist 4 (lensCoeffQ 4 (-1) isCoprime_four_neg_one) j (solidNegSectionPoint y κ) := by
  apply sphere_ext
  · rw [lensTwist, sphereFirst_circlePairAct, toCircle_lensCoeffQ_mul, solidNegSectionPoint,
      solidNegSectionPoint, sphereFirst_sphereOfPair, sphereFirst_sphereOfPair]
    simp only [mul_inv_rev, Circle.coe_mul, Circle.coe_inv]
    ring
  · rw [lensTwist, sphereSecond_circlePairAct, solidNegSectionPoint, solidNegSectionPoint,
      sphereSecond_sphereOfPair, sphereSecond_sphereOfPair, Circle.coe_mul]
    ring

def solidNegRootTarget (y : PlaneLift.{u} × Circle) : Circle :=
  (circleI ^ 2 * y.2 * unitOf (coneSumP (conePairNeg y)))⁻¹

def solidNegSectionLift (y : PlaneLift.{u} × Circle) : LensSphere :=
  solidNegSectionPoint y (circleRootOf 4 (solidNegRootTarget y))

def solidNegSection (y : PlaneLift.{u} × Circle) : mobiusLensGroup.Orbit :=
  mobiusCover.cover (solidNegSectionLift y)

def coneNegGood (y : PlaneLift.{u} × Circle) : Prop := coneSumP (conePairNeg y) ≠ 0

theorem isOpen_coneNegGood : IsOpen {y : PlaneLift.{u} × Circle | coneNegGood y} :=
  isOpen_ne_fun ((contDiff_iff_contDiffAt.mpr contDiffAt_coneSumP).continuous.comp
    contMDiff_conePairNeg.continuous) continuous_const

theorem contMDiffAt_solidNegRootTarget {y : PlaneLift.{u} × Circle} (hy : coneNegGood y) :
    ContMDiffAt PlaneCircleModel (𝓡 1) ∞ solidNegRootTarget.{u} y := by
  have hS : ContMDiffAt PlaneCircleModel 𝓘(ℝ, ℂ) ∞
      (fun y : PlaneLift.{u} × Circle => coneSumP (conePairNeg y)) y :=
    (contDiffAt_coneSumP _).contMDiffAt.comp y contMDiff_conePairNeg.contMDiffAt
  have hu : ContMDiffAt PlaneCircleModel (𝓡 1) ∞
      (fun y : PlaneLift.{u} × Circle => unitOf (coneSumP (conePairNeg y))) y :=
    (contMDiffOn_unitOf.contMDiffAt (isOpen_ne.mem_nhds hy)).comp y hS
  exact ((contMDiffAt_const.mul contMDiff_snd.contMDiffAt).mul hu).inv

theorem contMDiffAt_solidNegSectionPoint {y : PlaneLift.{u} × Circle} (hy : coneNegGood y)
    (v : Circle) :
    ContMDiffAt (PlaneCircleModel.prod (𝓡 1)) (𝓡 3) ∞
      (fun p : (PlaneLift.{u} × Circle) × Circle => solidNegSectionPoint p.1 p.2) (y, v) := by
  let s : Set ((PlaneLift.{u} × Circle) × Circle) := {p | coneNegGood p.1}
  have hs : IsOpen s := isOpen_coneNegGood.preimage continuous_fst
  have hq : ∀ p ∈ s, ContMDiffAt (PlaneCircleModel.prod (𝓡 1)) 𝓘(ℝ, ℂ × ℂ) ∞
      (fun p : (PlaneLift.{u} × Circle) × Circle => conePairNeg p.1) p :=
    fun p _ => (contMDiff_conePairNeg.comp contMDiff_fst).contMDiffAt
  have hA : ∀ p ∈ s, ContMDiffAt (PlaneCircleModel.prod (𝓡 1)) 𝓘(ℝ, ℂ) ∞
      (fun p : (PlaneLift.{u} × Circle) × Circle => (coneFirstScaleP (conePairNeg p.1) : ℂ)) p :=
    fun p hp => (Complex.ofRealCLM.contDiff.contDiffAt.comp _
      (contDiffAt_coneScales hp).1).contMDiffAt.comp p (hq p hp)
  have hB : ∀ p ∈ s, ContMDiffAt (PlaneCircleModel.prod (𝓡 1)) 𝓘(ℝ, ℂ) ∞
      (fun p : (PlaneLift.{u} × Circle) × Circle => (coneSecondScaleP (conePairNeg p.1) : ℂ)) p :=
    fun p hp => (Complex.ofRealCLM.contDiff.contDiffAt.comp _
      (contDiffAt_coneScales hp).2).contMDiffAt.comp p (hq p hp)
  have hz : ContMDiff (PlaneCircleModel.prod (𝓡 1)) 𝓘(ℝ, ℂ) ∞
      (fun p : (PlaneLift.{u} × Circle) × Circle => (conePairNeg p.1).1) :=
    (contMDiff_planeLift_down.comp contMDiff_fst).comp contMDiff_fst
  have hv : ContMDiff (PlaneCircleModel.prod (𝓡 1)) 𝓘(ℝ, ℂ) ∞
      (fun p : (PlaneLift.{u} × Circle) × Circle => (p.2 : ℂ)) :=
    contMDiff_circle_coe.comp contMDiff_snd
  have hvi : ContMDiff (PlaneCircleModel.prod (𝓡 1)) 𝓘(ℝ, ℂ) ∞
      (fun p : (PlaneLift.{u} × Circle) × Circle => ((p.2⁻¹ : Circle) : ℂ)) :=
    contMDiff_circle_coe.comp contMDiff_snd.inv
  refine (contMDiffOn_of_sphereFirst_sphereSecond hs ?_ ?_).contMDiffAt
    (hs.mem_nhds (show (y, v) ∈ s from hy))
  · intro p hp
    simp only [solidNegSectionPoint, sphereFirst_sphereOfPair]
    exact (contMDiffAt_complex_mul (hB p hp) (hvi p)).contMDiffWithinAt
  · intro p hp
    simp only [solidNegSectionPoint, sphereSecond_sphereOfPair]
    exact (contMDiffAt_complex_mul (contMDiffAt_complex_mul (hA p hp) (hz p))
      (hv p)).contMDiffWithinAt

theorem contMDiffAt_solidNegSection {y : PlaneLift.{u} × Circle} (hy : coneNegGood y) :
    ContMDiffAt PlaneCircleModel (𝓡 3) ∞ solidNegSection.{u} y :=
  mobiusCover.contMDiffAt_cover_root (contMDiffAt_solidNegRootTarget hy)
    (contMDiffAt_solidNegSectionPoint hy) (fun y' v j => solidNegSectionPoint_twist y' v j)

theorem solidNegPair_key {q : ℂ × ℂ} (hq : coneSumP q ≠ 0) (w κ : Circle)
    (hw : ((w⁻¹ : Circle) : ℂ) = q.2) (hκ : κ⁻¹ ^ 4 = w * unitOf (coneSumP q)) :
    (54 + q.1 ^ 2 * q.2) * ((coneFirstScaleP q : ℂ) * q.1 * (κ : ℂ)) ^ 2 =
      q.1 ^ 2 * q.2 * ((coneSecondScaleP q : ℂ) * ((κ⁻¹ : Circle) : ℂ)) ^ 2 := by
  have h := solidPair_key hq w κ⁻¹ hw hκ
  rwa [inv_inv] at h

theorem solidNegPair_sub_ne_zero {q : ℂ × ℂ} (hq : coneSumP q ≠ 0) (w κ : Circle)
    (hw : ((w⁻¹ : Circle) : ℂ) = q.2) (hκ : κ⁻¹ ^ 4 = w * unitOf (coneSumP q)) :
    ((coneSecondScaleP q : ℂ) * ((κ⁻¹ : Circle) : ℂ)) ^ 2 -
      ((coneFirstScaleP q : ℂ) * q.1 * (κ : ℂ)) ^ 2 ≠ 0 := by
  intro h
  have hk := solidNegPair_key hq w κ hw hκ
  have ha : ((coneSecondScaleP q : ℂ) * ((κ⁻¹ : Circle) : ℂ)) ^ 2 ≠ 0 :=
    pow_ne_zero 2 (mul_ne_zero (Complex.ofReal_ne_zero.mpr (coneSecondScaleP_pos q).ne')
      (Circle.coe_ne_zero _))
  rw [← sub_eq_zero.mp h] at hk
  exact ha (by linear_combination hk / 54)

theorem bundleBasePoint_solidNegPair {q : ℂ × ℂ} (hq : coneSumP q ≠ 0) (w κ : Circle)
    (hw : ((w⁻¹ : Circle) : ℂ) = q.2) (hκ : κ⁻¹ ^ 4 = w * unitOf (coneSumP q)) :
    bundleBasePoint ((coneSecondScaleP q : ℂ) * ((κ⁻¹ : Circle) : ℂ),
      (coneFirstScaleP q : ℂ) * q.1 * (κ : ℂ)) = -(3 / 2) - q.1 ^ 2 * q.2 / 18 := by
  rw [bundleBasePoint]
  dsimp only
  rw [div_eq_iff (solidNegPair_sub_ne_zero hq w κ hw hκ)]
  linear_combination (-1 / 18 : ℂ) * solidNegPair_key hq w κ hw hκ

theorem pantsFibrePoint_solidNegPair {q : ℂ × ℂ} (hq : coneSumP q ≠ 0) (hz : q.1 ≠ 0)
    (κ : Circle) :
    pantsFibrePoint ((coneSecondScaleP q : ℂ) * ((κ⁻¹ : Circle) : ℂ),
      (coneFirstScaleP q : ℂ) * q.1 * (κ : ℂ)) = (unitOf q.1 : ℂ) := by
  have h := pantsFibrePoint_solidPair hq hz κ
  rw [pantsFibrePoint] at h ⊢
  dsimp only at h ⊢
  rwa [show (coneSecondScaleP q : ℂ) * ((κ⁻¹ : Circle) : ℂ) * ((coneFirstScaleP q : ℂ) * q.1 *
    (κ : ℂ)) = (coneFirstScaleP q : ℂ) * q.1 * ((κ⁻¹ : Circle) : ℂ) *
      ((coneSecondScaleP q : ℂ) * (κ : ℂ)) by ring]

theorem coneNegGood_of_mem_solidSet (x : solidSet.{u}) : coneNegGood x.val := by
  intro h
  have hz := (mem_solidSet_iff x.val).mp x.2
  change 54 + x.val.1.down ^ 2 * -((x.val.2⁻¹ : Circle) : ℂ) = 0 at h
  have h1 : (54 : ℂ) = x.val.1.down ^ 2 * ((x.val.2⁻¹ : Circle) : ℂ) := by linear_combination h
  have h2 : ‖(54 : ℂ)‖ = ‖x.val.1.down‖ ^ 2 := by
    rw [h1, norm_mul, norm_pow, Circle.norm_coe, mul_one]
  have h3 : ‖(54 : ℂ)‖ = 54 := by norm_num
  rw [h3] at h2
  nlinarith [norm_nonneg x.val.1.down]

theorem solidNegRootTarget_root (y : PlaneLift.{u} × Circle) :
    (circleRootOf 4 (solidNegRootTarget y))⁻¹ ^ 4 =
      (circleI ^ 2 * y.2) * unitOf (coneSumP (conePairNeg y)) := by
  rw [inv_pow, circleRootOf_pow, solidNegRootTarget, inv_inv]

theorem conePairNeg_snd (y : PlaneLift.{u} × Circle) :
    (((circleI ^ 2 * y.2)⁻¹ : Circle) : ℂ) = (conePairNeg y).2 := by
  change (((circleI ^ 2 * y.2)⁻¹ : Circle) : ℂ) = -((y.2⁻¹ : Circle) : ℂ)
  rw [mul_inv_rev, Circle.coe_mul, Circle.coe_inv (circleI ^ 2), Circle.coe_pow, coe_circleI,
    Complex.I_sq]
  ring

theorem lensPair_solidNegSectionLift (y : PlaneLift.{u} × Circle) :
    lensPair (sphereDownPoint (solidNegSectionLift y) : EuclideanSpace ℝ (Fin 4)) =
      ((coneSecondScaleP (conePairNeg y) : ℂ) *
        ((circleRootOf 4 (solidNegRootTarget y))⁻¹ : Circle),
        (coneFirstScaleP (conePairNeg y) : ℂ) * (conePairNeg y).1 *
          (circleRootOf 4 (solidNegRootTarget y) : ℂ)) := by
  change lensPair (sphereDown _) = _
  rw [lensPair_sphereDown, solidNegSectionLift, solidNegSectionPoint, sphereFirst_sphereOfPair,
    sphereSecond_sphereOfPair]

theorem bundleBasePoint_solidNegSectionLift {y : PlaneLift.{u} × Circle} (hy : coneNegGood y) :
    bundleBasePoint (lensPair (sphereDownPoint (solidNegSectionLift y) :
      EuclideanSpace ℝ (Fin 4))) = -(3 / 2) + y.1.down ^ 2 * ((y.2⁻¹ : Circle) : ℂ) / 18 := by
  rw [lensPair_solidNegSectionLift, bundleBasePoint_solidNegPair hy _ _ (conePairNeg_snd y)
    (solidNegRootTarget_root y)]
  change -(3 / 2) - y.1.down ^ 2 * -((y.2⁻¹ : Circle) : ℂ) / 18 = _
  ring

theorem solidNegSectionLift_sq_sub_ne_zero {y : PlaneLift.{u} × Circle} (hy : coneNegGood y) :
    (lensPair (sphereDownPoint (solidNegSectionLift y) : EuclideanSpace ℝ (Fin 4))).1 ^ 2 -
      (lensPair (sphereDownPoint (solidNegSectionLift y) :
        EuclideanSpace ℝ (Fin 4))).2 ^ 2 ≠ 0 := by
  rw [lensPair_solidNegSectionLift]
  exact solidNegPair_sub_ne_zero hy _ _ (conePairNeg_snd y) (solidNegRootTarget_root y)

theorem solidNegSectionLift_quartic (x : solidSet.{u}) :
    bundleQuartic (lensPair (sphereDownPoint (solidNegSectionLift x.val) :
      EuclideanSpace ℝ (Fin 4))) ≤ 0 := by
  have hy := coneNegGood_of_mem_solidSet x
  rw [bundleQuartic_nonpos_iff (solidNegSectionLift_sq_sub_ne_zero hy),
    bundleBasePoint_solidNegSectionLift hy]
  have h := norm_cone_base_sub_le x
  calc ‖-(3 / 2) + x.val.1.down ^ 2 * ((x.val.2⁻¹ : Circle) : ℂ) / 18‖
      ≤ ‖(-(3 / 2) : ℂ)‖ + ‖x.val.1.down ^ 2 * ((x.val.2⁻¹ : Circle) : ℂ) / 18‖ :=
        norm_add_le _ _
    _ ≤ 3 := by
      have h32 : ‖(-(3 / 2) : ℂ)‖ = 3 / 2 := by norm_num
      rw [h32]
      linarith

def solidFoldMinus (x : solidSet.{u}) : mobiusBundleSet.{u} :=
  ⟨lensUp (solidNegSection x.val), solidNegSectionLift_quartic x⟩

theorem lensDown_solidFoldMinus (x : solidSet.{u}) :
    lensDown (solidFoldMinus x).val =
      mobiusLensGroup.projection (sphereDownPoint (solidNegSectionLift x.val)) :=
  rfl

theorem contMDiff_solidFoldMinus : ContMDiff (𝓡∂ 3) (𝓡∂ 3) ∞ solidFoldMinus.{u} := by
  refine (mobiusBundleAtlas.contMDiff_iff_subtype_val _).mpr fun x => ?_
  exact contMDiff_lensUp.contMDiffAt.comp x ((contMDiffAt_solidNegSection
    (coneNegGood_of_mem_solidSet x)).comp x (solidAtlas.contMDiff_subtype_val x))

theorem mobiusBundleBase_solidFoldMinus (x : solidSet.{u}) :
    mobiusBundleBase (solidFoldMinus x) =
      -(3 / 2) + x.val.1.down ^ 2 * ((x.val.2⁻¹ : Circle) : ℂ) / 18 := by
  rw [mobiusBundleBase_eq (lensDown_solidFoldMinus x)]
  exact bundleBasePoint_solidNegSectionLift (coneNegGood_of_mem_solidSet x)

theorem mobiusBundleFibre_solidFoldMinus (x : solidSet.{u}) (hz : x.val.1.down ≠ 0) :
    mobiusBundleFibre (solidFoldMinus x) = (unitOf x.val.1.down : ℂ) := by
  rw [mobiusBundleFibre_eq (lensDown_solidFoldMinus x), lensPair_solidNegSectionLift]
  exact pantsFibrePoint_solidNegPair (coneNegGood_of_mem_solidSet x) hz _

theorem norm_mobiusBundleBase_solidFoldMinus_add (x : solidSet.{u}) :
    ‖mobiusBundleBase (solidFoldMinus x) + 3 / 2‖ ≤ 1 / 2 := by
  rw [mobiusBundleBase_solidFoldMinus, neg_add_cancel_comm]
  exact norm_cone_base_sub_le x

theorem mobiusPantsFold_hole_two_eq (t : Torus) :
    mobiusPantsFold (productCollar.{u} 3 (Or.inr rfl) 2 (seamMatching t, halfZero)) =
      solidFoldMinus (solidCollar.{u} 2 (t, halfZero)) := by
  have hb : mobiusBundleBase (solidFoldMinus (solidCollar.{u} 2 (t, halfZero))) =
      -(3 / 2) + (t.1 : ℂ) ^ 2 * ((t.2⁻¹ : Circle) : ℂ) / 2 := by
    rw [mobiusBundleBase_solidFoldMinus, cone_base_solidCollar]
  have hn := norm_cone_base_solidCollar t
  refine (eq_of_mobiusBundleBase_eq_of_fibre_eq _ _ ?_ ?_ ?_ ?_).symm
  · rw [hb]
    intro h
    have h' : (t.1 : ℂ) ^ 2 * ((t.2⁻¹ : Circle) : ℂ) / 2 = 3 := by linear_combination h
    rw [h'] at hn
    norm_num at hn
  · rw [hb]
    intro h
    have h' : (t.1 : ℂ) ^ 2 * ((t.2⁻¹ : Circle) : ℂ) / 2 = 0 := by linear_combination h
    rw [h', norm_zero] at hn
    norm_num at hn
  · rw [hb, mobiusBundleBase_mobiusPantsFold_hole 2 (by decide), planarCenter_three_two]
    push_cast
    ring
  · rw [mobiusBundleFibre_solidFoldMinus _ (solidCollar_zero_ne t),
      mobiusBundleFibre_mobiusPantsFold_hole, solidCollar_zero_val]
    dsimp only
    rw [unitOf_smul (by norm_num : (0 : ℝ) < 3)]

def seamBasePoint (j : Fin 3) (t : Torus) (s : ℝ) : ℂ :=
  (planarCenter 3 j : ℂ) + ((1 / 2 + s / 4 : ℝ) : ℂ) * ((t.1 : ℂ) ^ 2 * ((t.2⁻¹ : Circle) : ℂ))

theorem norm_seamBasePoint_sub (j : Fin 3) (t : Torus) {s : ℝ} (hs : -2 < s) :
    ‖seamBasePoint j t s - planarCenter 3 j‖ = 1 / 2 + s / 4 := by
  rw [seamBasePoint, add_sub_cancel_left, norm_mul, Complex.norm_real,
    Real.norm_of_nonneg (by linarith), norm_mul, norm_pow, Circle.norm_coe, Circle.norm_coe]
  ring

theorem planarCenter_hole (j : Fin 3) (hj : j.val ≠ 0) :
    planarCenter 3 j = 3 / 2 ∨ planarCenter 3 j = -(3 / 2) := by
  fin_cases j
  · exact absurd rfl hj
  · exact Or.inl planarCenter_three_one
  · exact Or.inr planarCenter_three_two

theorem seamBasePoint_good (j : Fin 3) (hj : j.val ≠ 0) (t : Torus) {s : ℝ} (hs : -1 < s)
    (hs1 : s < 1) :
    seamBasePoint j t s ≠ 3 / 2 ∧ seamBasePoint j t s ≠ -(3 / 2) ∧ ‖seamBasePoint j t s‖ ≤ 3 := by
  have hn := norm_seamBasePoint_sub j t (s := s) (by linarith)
  have htri : ∀ c : ℂ, ‖seamBasePoint j t s - c‖ ≥
      ‖((planarCenter 3 j : ℝ) : ℂ) - c‖ - (1 / 2 + s / 4) := by
    intro c
    have h := norm_sub_le_norm_sub_add_norm_sub ((planarCenter 3 j : ℝ) : ℂ)
      (seamBasePoint j t s) c
    rw [norm_sub_rev ((planarCenter 3 j : ℝ) : ℂ) (seamBasePoint j t s), hn] at h
    linarith
  have h0 := htri 0
  rw [sub_zero, sub_zero, Complex.norm_real, Real.norm_eq_abs] at h0
  have habs : ‖seamBasePoint j t s‖ ≤ 3 := by
    have h := norm_sub_le (seamBasePoint j t s - ((planarCenter 3 j : ℝ) : ℂ))
      (-((planarCenter 3 j : ℝ) : ℂ))
    rw [sub_neg_eq_add, sub_add_cancel, norm_neg, Complex.norm_real, Real.norm_eq_abs, hn] at h
    rcases planarCenter_hole j hj with hc | hc <;> rw [hc] at h <;> norm_num at h <;> linarith
  rcases planarCenter_hole j hj with hc | hc
  · refine ⟨fun h => ?_, fun h => ?_, habs⟩
    · rw [h, hc] at hn
      norm_num at hn
      linarith
    · have h3 := htri (-(3 / 2))
      rw [h, sub_self, norm_zero, hc] at h3
      norm_num at h3
      linarith
  · refine ⟨fun h => ?_, fun h => ?_, habs⟩
    · have h3 := htri (3 / 2)
      rw [h, sub_self, norm_zero, hc] at h3
      norm_num at h3
      linarith
    · rw [h, hc] at hn
      norm_num at hn
      linarith

def mobiusSeamPoint (j : Fin 3) (t : Torus) (s : ℝ) : mobiusLens.{u}.Carrier :=
  lensUp (pantsSection ((ULift.up (seamBasePoint j t s) : PlaneLift.{u}), t.1))

theorem exists_mobiusSeamPoint (j : Fin 3) (hj : j.val ≠ 0) (t : Torus) {s : ℝ} (hs : -1 < s)
    (hs1 : s < 1) :
    ∃ y : mobiusBundleSet.{u}, y.val = mobiusSeamPoint j t s ∧
      mobiusBundleBase y = seamBasePoint j t s ∧ mobiusBundleFibre y = (t.1 : ℂ) := by
  obtain ⟨h1, h2, h3⟩ := seamBasePoint_good j hj t hs hs1
  have hy : pantsGood (((ULift.up (seamBasePoint j t s) : PlaneLift.{u}), t.1)) := ⟨h1, h2⟩
  have hab := pantsSectionLift_sq_sub_ne_zero hy
  have hb := bundleBasePoint_pantsSectionLift hy
  have hq : bundleQuartic (lensPair (sphereDownPoint (pantsSectionLift
      (((ULift.up (seamBasePoint j t s) : PlaneLift.{u}), t.1))) :
        EuclideanSpace ℝ (Fin 4))) ≤ 0 := by
    rw [bundleQuartic_nonpos_iff hab, hb]
    exact h3
  refine ⟨⟨mobiusSeamPoint j t s, hq⟩, rfl, ?_, ?_⟩
  · rw [mobiusBundleBase_eq (x := sphereDownPoint (pantsSectionLift
      (((ULift.up (seamBasePoint j t s) : PlaneLift.{u}), t.1)))) rfl]
    exact hb
  · rw [mobiusBundleFibre_eq (x := sphereDownPoint (pantsSectionLift
      (((ULift.up (seamBasePoint j t s) : PlaneLift.{u}), t.1)))) rfl]
    exact pantsFibrePoint_pantsSectionLift hy

theorem eq_mobiusSeamPoint (j : Fin 3) (hj : j.val ≠ 0) (t : Torus) {s : ℝ} (hs : -1 < s)
    (hs1 : s < 1) (z : mobiusBundleSet.{u}) (hb : mobiusBundleBase z = seamBasePoint j t s)
    (hf : mobiusBundleFibre z = (t.1 : ℂ)) : z.val = mobiusSeamPoint j t s := by
  obtain ⟨y, hyv, hyb, hyf⟩ := exists_mobiusSeamPoint.{u} j hj t hs hs1
  obtain ⟨h1, h2, -⟩ := seamBasePoint_good j hj t hs hs1
  rw [← hyv]
  exact congrArg Subtype.val (eq_of_mobiusBundleBase_eq_of_fibre_eq y z (hyb ▸ h1) (hyb ▸ h2)
    (hyb.trans hb.symm) (hyf.trans hf.symm)).symm

theorem productCollar_hole_val_height (j : Fin 3) (hj : j.val ≠ 0) (t : Torus) {s : ℝ}
    (hs : 0 ≤ s) (hs1 : s < 1) :
    (productCollar.{u} 3 (Or.inr rfl) j (t, halfPoint s hs)).val =
      (ULift.up ((planarCenter 3 j : ℂ) + ((1 / 2 + s / 4 : ℝ) : ℂ) * conj (t.1 : ℂ)), t.2) := by
  refine Prod.ext (ULift.ext ?_) rfl
  rw [productCollar_apply]
  change (planarCollar.{u} 3 (Or.inr rfl) j (t.1, halfPoint s hs)).val.down = _
  rw [planarCollar_apply_val (Or.inr rfl) j (show (t.1, halfPoint s hs) ∈ circleCollarSource
    from hs1)]
  change (planarCenter 3 j : ℂ) + (planarRadius j + planarSign j * s / 4) • planarTwist j
    (t.1 : ℂ) = _
  simp only [planarRadius, planarSign, planarTwist, hj, ite_false, Complex.real_smul]
  push_cast
  ring

theorem mobiusPantsFold_collar_eq_seam (j : Fin 3) (hj : j.val ≠ 0) (t : Torus) {s : ℝ}
    (hs : 0 ≤ s) (hs1 : s < 1) :
    (mobiusPantsFold (productCollar.{u} 3 (Or.inr rfl) j (seamMatching t, halfPoint s hs))).val =
      mobiusSeamPoint j t s := by
  refine eq_mobiusSeamPoint j hj t (by linarith) hs1 _ ?_ ?_
  · rw [mobiusBundleBase_mobiusPantsFold, productCollar_hole_val_height j hj _ hs hs1,
      seamMatching_apply, circle_seam_inv, seamBasePoint]
  · rw [mobiusBundleFibre_mobiusPantsFold, productCollar_hole_val_height j hj _ hs hs1,
      seamMatching_apply]

theorem seamRadius_two_sq {σ : ℝ} (hσ : σ < 2) : seamRadius 2 (-σ) ^ 2 = 9 * (1 - σ / 2) := by
  have h := div_three_pow_seamRadius 2 (s := -σ) (by linarith)
  rw [div_pow] at h
  linear_combination 9 * h

theorem solidCollar_val_height (t : Torus) {σ : ℝ} (hσ : 0 ≤ σ) (hσ1 : σ < 1) :
    (solidCollar.{u} 2 (t, halfPoint σ hσ)).val.1.down ^ 2 *
      (((solidCollar.{u} 2 (t, halfPoint σ hσ)).val.2⁻¹ : Circle) : ℂ) / 18 =
      ((1 / 2 + -σ / 4 : ℝ) : ℂ) * ((t.1 : ℂ) ^ 2 * ((t.2⁻¹ : Circle) : ℂ)) := by
  rw [solidCollar_apply_val 2 (show (t, halfPoint σ hσ) ∈ halfCollarSource from hσ1)]
  change (seamRadius 2 (-σ) • (t.1 : ℂ)) ^ 2 * ((t.2⁻¹ : Circle) : ℂ) / 18 = _
  rw [Complex.real_smul, mul_pow, ← Complex.ofReal_pow, seamRadius_two_sq (by linarith)]
  push_cast
  ring

theorem solidCollar_val_height_ne (t : Torus) {σ : ℝ} (hσ : 0 ≤ σ) (hσ1 : σ < 1) :
    (solidCollar.{u} 2 (t, halfPoint σ hσ)).val.1.down ≠ 0 := by
  rw [solidCollar_apply_val 2 (show (t, halfPoint σ hσ) ∈ halfCollarSource from hσ1)]
  exact smul_ne_zero (seamRadius_pos 2 (s := -σ) (by linarith)).ne' (Circle.coe_ne_zero _)

theorem unitOf_solidCollar_val (t : Torus) {σ : ℝ} (hσ : 0 ≤ σ) (hσ1 : σ < 1) :
    (unitOf (solidCollar.{u} 2 (t, halfPoint σ hσ)).val.1.down : ℂ) = (t.1 : ℂ) := by
  rw [solidCollar_apply_val 2 (show (t, halfPoint σ hσ) ∈ halfCollarSource from hσ1)]
  change (unitOf (seamRadius 2 (-σ) • (t.1 : ℂ)) : ℂ) = _
  rw [unitOf_smul (seamRadius_pos 2 (by linarith))]

theorem solidFoldPlus_collar_eq_seam (t : Torus) {σ : ℝ} (hσ : 0 ≤ σ) (hσ1 : σ < 1) :
    (solidFoldPlus (solidCollar.{u} 2 (t, halfPoint σ hσ))).val = mobiusSeamPoint 1 t (-σ) := by
  refine eq_mobiusSeamPoint 1 (by decide) t (by linarith) (by linarith) _ ?_ ?_
  · rw [mobiusBundleBase_solidFoldPlus, solidCollar_val_height t hσ hσ1, seamBasePoint,
      planarCenter_three_one]
    push_cast
    ring
  · rw [mobiusBundleFibre_solidFoldPlus _ (solidCollar_val_height_ne t hσ hσ1),
      unitOf_solidCollar_val t hσ hσ1]

theorem solidFoldMinus_collar_eq_seam (t : Torus) {σ : ℝ} (hσ : 0 ≤ σ) (hσ1 : σ < 1) :
    (solidFoldMinus (solidCollar.{u} 2 (t, halfPoint σ hσ))).val = mobiusSeamPoint 2 t (-σ) := by
  refine eq_mobiusSeamPoint 2 (by decide) t (by linarith) (by linarith) _ ?_ ?_
  · rw [mobiusBundleBase_solidFoldMinus, solidCollar_val_height t hσ hσ1, seamBasePoint,
      planarCenter_three_two]
    push_cast
    ring
  · rw [mobiusBundleFibre_solidFoldMinus _ (solidCollar_val_height_ne t hσ hσ1),
      unitOf_solidCollar_val t hσ hσ1]

theorem contMDiffAt_mobiusSeamPoint (j : Fin 3) (hj : j.val ≠ 0) {t : Torus} {s : ℝ}
    (hs : -1 < s) (hs1 : s < 1) :
    ContMDiffAt signedCollarModel (𝓡 3) ∞ (fun p : Torus × ℝ => mobiusSeamPoint.{u} j p.1 p.2)
      (t, s) := by
  obtain ⟨h1, h2, -⟩ := seamBasePoint_good j hj t hs hs1
  have hbase : ContMDiff signedCollarModel 𝓘(ℝ, ℂ) ∞
      (fun p : Torus × ℝ => seamBasePoint j p.1 p.2) := by
    have hr : ContMDiff signedCollarModel 𝓘(ℝ, ℂ) ∞
        (fun p : Torus × ℝ => ((1 / 2 + p.2 / 4 : ℝ) : ℂ)) :=
      Complex.ofRealCLM.contDiff.contMDiff.comp
        ((contDiff_const.add (contDiff_id.div_const _)).contMDiff.comp contMDiff_snd)
    have h1' : ContMDiff signedCollarModel 𝓘(ℝ, ℂ) ∞
        (fun p : Torus × ℝ => (p.1.1 : ℂ) ^ 2) :=
      (contDiff_id.pow 2).contMDiff.comp (contMDiff_circle_coe.comp
        (contMDiff_fst.comp contMDiff_fst))
    have h2' : ContMDiff signedCollarModel 𝓘(ℝ, ℂ) ∞
        (fun p : Torus × ℝ => ((p.1.2⁻¹ : Circle) : ℂ)) :=
      contMDiff_circle_coe.comp ((contMDiff_snd.comp contMDiff_fst).inv)
    intro p
    exact contMDiffAt_const.add (contMDiffAt_complex_mul (hr p)
      (contMDiffAt_complex_mul (h1' p) (h2' p)))
  have hin : ContMDiff signedCollarModel PlaneCircleModel ∞
      (fun p : Torus × ℝ => ((ULift.up (seamBasePoint j p.1 p.2) : PlaneLift.{u}), p.1.1)) :=
    (contMDiff_planeLift_up.comp hbase).prodMk (contMDiff_fst.comp contMDiff_fst)
  have hP : ContMDiffAt signedCollarModel (𝓡 3) ∞ (fun p : Torus × ℝ =>
      pantsSection.{u} ((ULift.up (seamBasePoint j p.1 p.2) : PlaneLift.{u}), p.1.1)) (t, s) :=
    ContMDiffAt.comp (g := pantsSection.{u}) (t, s)
      (contMDiffAt_pantsSection (y := ((ULift.up (seamBasePoint j t s) : PlaneLift.{u}), t.1))
        ⟨h1, h2⟩) hin.contMDiffAt
  exact contMDiff_lensUp.contMDiffAt.comp (t, s) hP

end GC.Seifert
