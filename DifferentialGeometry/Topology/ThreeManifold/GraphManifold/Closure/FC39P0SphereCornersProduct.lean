import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.FC39P0SphereCornersRim
import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.AssemblyL1WSideRimProduct

/-!
# FC39 producer, packet P0 (gate 1): the S³ circle kind, `RimProduct` for the adapted rim charts

Lead condition (2) of the decision of 02:45: the rim-product clause `RimProductAt` is PROVED for the
adapted rim charts `circRim` and the accepted handles `cycleS3Handle` (it is not inherited from
`cycleRimChart`). On the handle quadrant of `rimBox 1`,

  `circRim b e (θ, (x, y)) = (cycleS3Handle b).map (ρ x • A (planeOfCircle θ), endCoord e (τ y))`

with `A = id` (south, `b = false`) or `A = −id` (north, `b = true`), `ρ x = √(1 + x/16)` and
`τ = Q(y/16 − 3/5) − 1` (`b xor e = false`, the handle radius is `1 + s` near `s = 0`) or
`τ = 4 / Q(3/5 − y/16) − 1` (`b xor e = true`, the radius is `4 / (2 − s)` near `s = 1`). To make
`ρ, τ` smooth on all of `ℝ` the variable is first passed through the smooth clamp `circClamp`
(the identity on `[−1, 1]`, values in `[−3/2, 3/2]`).
-/

set_option autoImplicit false

noncomputable section

open Set Function Filter
open DifferentialGeometry DifferentialGeometry.Topology GC.GraphManifold
open Manifold
open scoped Manifold ContDiff Topology

namespace GC.GraphManifold.Assembly.FC39P0

local notation "E2" => EuclideanSpace ℝ (Fin 2)

attribute [local instance] Handle.closedCellChartedSpaceSucc

/-! ## The derivative of the corner coordinate -/

/-- The corner coordinate is differentiable with derivative `1 / (16 · slack′)`. -/
theorem hasDerivAt_circCornerInv (a σ : Bool) {s : ℝ} (hs : |s| < 2) :
    HasDerivAt (circCornerInv a σ) (1 / (16 * circSlackDeriv a σ (circCornerInv a σ s))) s := by
  have hd : DifferentiableAt ℝ (circCornerInv a σ) s :=
    (contDiffAt_circCornerInv a σ hs).differentiableAt (by simp)
  have h1 := (hasDerivAt_circSlack a σ (circCornerInv_pos a σ hs)).comp s hd.hasDerivAt
  have h2 : HasDerivAt (circSlack a σ ∘ circCornerInv a σ) (1 / 16) s := by
    have hl : HasDerivAt (fun s : ℝ => 1 / 16 * s) (1 / 16) s := by
      simpa using (hasDerivAt_id s).const_mul (1 / 16 : ℝ)
    refine hl.congr_of_eventuallyEq ?_
    have hU : ∀ᶠ s' in 𝓝 s, |s'| < 2 := (isOpen_lt continuous_abs continuous_const).mem_nhds hs
    filter_upwards [hU] with s' hs'
    exact circSlack_circCornerInv a σ hs'
  have huniq := h1.unique h2
  have hne := circSlackDeriv_ne_zero a σ (circCornerInv_pos a σ hs)
  have hval : deriv (circCornerInv a σ) s =
      1 / (16 * circSlackDeriv a σ (circCornerInv a σ s)) := by
    rw [eq_div_iff (mul_ne_zero (by norm_num) hne)]
    linear_combination 16 * huniq
  rw [← hval]
  exact hd.hasDerivAt

/-! ## The smooth clamp -/

/-- The smooth clamp: the identity on `[−1, 1]`, zero outside `(−3/2, 3/2)`. -/
def circClamp (y : ℝ) : ℝ :=
  y * Real.smoothTransition (3 - 2 * y) * Real.smoothTransition (3 + 2 * y)

theorem contDiff_circClamp : ContDiff ℝ ∞ circClamp := by
  unfold circClamp
  have hs : ContDiff ℝ ∞ Real.smoothTransition := Real.smoothTransition.contDiff (n := ⊤)
  exact (contDiff_id.mul (hs.comp (contDiff_const.sub (contDiff_const.mul contDiff_id)))).mul
    (hs.comp (contDiff_const.add (contDiff_const.mul contDiff_id)))

theorem circClamp_eq {y : ℝ} (hy : |y| ≤ 1) : circClamp y = y := by
  have hl := (abs_le.1 hy).1
  have hu := (abs_le.1 hy).2
  rw [circClamp, Real.smoothTransition.one_of_one_le (by linarith),
    Real.smoothTransition.one_of_one_le (by linarith), mul_one, mul_one]

theorem abs_circClamp_lt (y : ℝ) : |circClamp y| < 2 := by
  have h1 := Real.smoothTransition.nonneg (3 - 2 * y)
  have h2 := Real.smoothTransition.le_one (3 - 2 * y)
  have h3 := Real.smoothTransition.nonneg (3 + 2 * y)
  have h4 := Real.smoothTransition.le_one (3 + 2 * y)
  rw [circClamp]
  by_cases hy : |y| ≤ 3 / 2
  · rw [abs_mul, abs_mul, abs_of_nonneg h1, abs_of_nonneg h3]
    have := abs_nonneg y
    calc |y| * Real.smoothTransition (3 - 2 * y) * Real.smoothTransition (3 + 2 * y)
        ≤ |y| * 1 * 1 := by gcongr
      _ < 2 := by linarith
  · rw [not_le] at hy
    rcases lt_abs.1 hy with h | h
    · rw [Real.smoothTransition.zero_of_nonpos (by linarith : 3 - 2 * y ≤ 0)]
      simp
    · rw [Real.smoothTransition.zero_of_nonpos (by linarith : 3 + 2 * y ≤ 0)]
      simp

theorem circClamp_eventuallyEq {y : ℝ} (hy : |y| < 1) : circClamp =ᶠ[𝓝 y] id := by
  have hU : ∀ᶠ y' in 𝓝 y, |y'| < 1 := (isOpen_lt continuous_abs continuous_const).mem_nhds hy
  filter_upwards [hU] with y' hy'
  exact circClamp_eq hy'.le

/-! ## The radial and the collar profiles -/

/-- The radial profile `ρ x = √(1 + x/16)` (near `[−1, 1]`). -/
def circRho (x : ℝ) : ℝ :=
  circCornerInv false false (circClamp x)

/-- The collar profile: `Q(y/16 − 3/5) − 1` (side `1`) or `4 / Q(3/5 − y/16) − 1` (side `4`). -/
def circTau : Bool → ℝ → ℝ
  | false, y => circCornerInv true false (circClamp y) - 1
  | true, y => 4 / circCornerInv true true (circClamp y) - 1

theorem contDiff_circRho : ContDiff ℝ ∞ circRho :=
  contDiff_iff_contDiffAt.2 fun x =>
    (contDiffAt_circCornerInv false false (abs_circClamp_lt x)).comp x
      contDiff_circClamp.contDiffAt

theorem contDiff_circTau (σ : Bool) : ContDiff ℝ ∞ (circTau σ) := by
  refine contDiff_iff_contDiffAt.2 fun y => ?_
  have hc := contDiff_circClamp.contDiffAt (x := y)
  cases σ
  · exact ((contDiffAt_circCornerInv true false (abs_circClamp_lt y)).comp y hc).sub
      contDiffAt_const
  · exact (contDiffAt_const.div
      ((contDiffAt_circCornerInv true true (abs_circClamp_lt y)).comp y hc)
      (circCornerInv_pos true true (abs_circClamp_lt y)).ne').sub contDiffAt_const

theorem circRho_eq {x : ℝ} (hx : |x| ≤ 1) : circRho x = circCornerInv false false x := by
  rw [circRho, circClamp_eq hx]

theorem circTau_false_eq {y : ℝ} (hy : |y| ≤ 1) :
    circTau false y = circCornerInv true false y - 1 := by
  rw [circTau, circClamp_eq hy]

theorem circTau_true_eq {y : ℝ} (hy : |y| ≤ 1) :
    circTau true y = 4 / circCornerInv true true y - 1 := by
  rw [circTau, circClamp_eq hy]

theorem circRho_zero : circRho 0 = 1 := by
  rw [circRho_eq (by norm_num), circCornerInv_zero]
  rfl

theorem circTau_zero (σ : Bool) : circTau σ 0 = 0 := by
  cases σ
  · rw [circTau_false_eq (by norm_num), circCornerInv_zero]
    norm_num [circEndVal]
  · rw [circTau_true_eq (by norm_num), circCornerInv_zero]
    norm_num [circEndVal]

theorem circRho_pos (x : ℝ) : 0 < circRho x :=
  circCornerInv_pos false false (abs_circClamp_lt x)

theorem deriv_circRho_pos {x : ℝ} (hx : |x| < 1) : 0 < deriv circRho x := by
  have hx2 : |x| < 2 := by linarith
  have he : circRho =ᶠ[𝓝 x] circCornerInv false false := by
    have := (circClamp_eventuallyEq hx)
    filter_upwards [this] with x' hx'
    rw [circRho, hx']
    rfl
  rw [he.deriv_eq, (hasDerivAt_circCornerInv false false hx2).deriv]
  have hp := circCornerInv_pos false false hx2
  simp only [circSlackDeriv]
  positivity

theorem deriv_circTau_pos (σ : Bool) {y : ℝ} (hy : |y| < 1) : 0 < deriv (circTau σ) y := by
  have hy2 : |y| < 2 := by linarith
  have hc := circClamp_eventuallyEq hy
  have hp := circCornerInv_pos true σ hy2
  cases σ
  · have he : circTau false =ᶠ[𝓝 y] fun y => circCornerInv true false y - 1 := by
      filter_upwards [hc] with y' hy'
      rw [circTau, hy']
      rfl
    rw [he.deriv_eq, ((hasDerivAt_circCornerInv true false hy2).sub_const 1).deriv]
    simp only [circSlackDeriv]
    positivity
  · have he : circTau true =ᶠ[𝓝 y] fun y => 4 / circCornerInv true true y - 1 := by
      filter_upwards [hc] with y' hy'
      rw [circTau, hy']
      rfl
    have hD := (((hasDerivAt_const y (4 : ℝ)).div (hasDerivAt_circCornerInv true true hy2)
      hp.ne').sub_const 1)
    rw [he.deriv_eq,
      (show HasDerivAt (fun y => 4 / circCornerInv true true y - 1) _ y from hD).deriv]
    simp only [circSlackDeriv]
    have hq : 0 < 16 * circCornerInv true true y / (circCornerInv true true y ^ 2 + 4) ^ 2 := by
      positivity
    have key : 1 / (16 * -(16 * circCornerInv true true y /
        (circCornerInv true true y ^ 2 + 4) ^ 2)) < 0 := by
      rw [one_div_neg]
      linarith
    have hden : 0 < circCornerInv true true y ^ 2 := by positivity
    rw [zero_mul, zero_sub, neg_div]
    rw [lt_neg, neg_zero]
    exact div_neg_of_neg_of_pos (by linarith) hden

/-! ## The handle charts in the product coordinates -/

theorem unitOf_smul_planeOfCircle_CIRCB {r : ℝ} (hr : 0 < r) (θ : Circle) :
    unitOf (Complex.orthonormalBasisOneI.repr.symm (r • planeOfCircle θ)) = θ := by
  rw [map_smul, planeOfCircle, LinearIsometryEquiv.symm_apply_apply]
  have hne : (r • (θ : ℂ)) ≠ 0 := smul_ne_zero hr.ne' (Circle.coe_ne_zero θ)
  apply Circle.ext
  rw [coe_unitOf hne, norm_smul, Circle.norm_coe, mul_one, Real.norm_of_nonneg hr.le, smul_smul,
    inv_mul_cancel₀ hr.ne', one_smul]

theorem unitOf_smul_neg_planeOfCircle_CIRCB {r : ℝ} (hr : 0 < r) (θ : Circle) :
    unitOf (Complex.orthonormalBasisOneI.repr.symm (r • -planeOfCircle θ)) =
      circleAntipode_CIRCA θ := by
  rw [smul_neg, map_neg, map_smul, planeOfCircle, LinearIsometryEquiv.symm_apply_apply]
  have hne : -(r • (θ : ℂ)) ≠ 0 := neg_ne_zero.2 (smul_ne_zero hr.ne' (Circle.coe_ne_zero θ))
  apply Circle.ext
  rw [coe_unitOf hne, coe_circleAntipode_CIRCA, norm_neg, norm_smul, Circle.norm_coe, mul_one,
    Real.norm_of_nonneg hr.le, smul_neg, smul_smul, inv_mul_cancel₀ hr.ne', one_smul]

/-- The handle radius at the collar parameter of the side `σ`. -/
theorem cycleHandleRadius_circTau (b e : Bool) {y : ℝ} (hy0 : 0 ≤ y) (hy1 : y < 1) :
    cycleHandleRadius (if b then 1 - endCoord e (circTau (b ^^ e) y) else
      endCoord e (circTau (b ^^ e) y)) = circCornerInv true (b ^^ e) y := by
  have hy : |y| ≤ 1 := by rw [abs_of_nonneg hy0]; exact hy1.le
  have hy2 : |y| < 2 := by linarith
  -- bounds of the two collar parameters
  have hf := circCornerInv_mem_wide true false hy2
  have hf' := circSlack_circCornerInv true false hy2
  have ht := circCornerInv_mem_wide true true hy2
  have ht' := circSlack_circCornerInv true true hy2
  have hfp := circCornerInv_pos true false hy2
  have htp := circCornerInv_pos true true hy2
  -- side `1`: radius `1 + τ` with `0 ≤ τ ≤ 1/4`
  have hτf : 0 ≤ circTau false y ∧ circTau false y ≤ 1 / 4 := by
    rw [circTau_false_eq hy]
    simp only [circSlack] at hf'
    rw [circHeight_add] at hf'
    set R := circCornerInv true false y
    have hR4 : 0 < R ^ 2 + 4 := by positivity
    have h1 : 8 * (R ^ 2 - 1) = 1 / 16 * y * (5 * (R ^ 2 + 4)) := by
      field_simp at hf' ⊢
      linarith
    constructor <;> nlinarith
  -- side `4`: radius `4 / (1 + τ)` with `0 ≤ τ ≤ 1/4`
  have hτt : 0 ≤ circTau true y ∧ circTau true y ≤ 1 / 4 := by
    rw [circTau_true_eq hy]
    simp only [circSlack] at ht'
    rw [circHeight_sub] at ht'
    set R := circCornerInv true true y
    have hR4 : 0 < R ^ 2 + 4 := by positivity
    have h1 : 2 * (16 - R ^ 2) = 1 / 16 * y * (5 * (R ^ 2 + 4)) := by
      field_simp at ht' ⊢
      linarith
    have hR2 : R ^ 2 ≤ 16 := by nlinarith
    have hR3 : (16 / 5) ^ 2 ≤ R ^ 2 := by nlinarith
    have hRle : R ≤ 4 := by nlinarith
    have hRge : 16 / 5 ≤ R := by nlinarith
    constructor
    · rw [sub_nonneg, le_div_iff₀ htp, one_mul]
      exact hRle
    · rw [sub_le_iff_le_add, div_le_iff₀ htp]
      linarith
  cases b <;> cases e <;> simp only [Bool.false_xor, Bool.true_xor, Bool.not_false,
    Bool.not_true, Bool.false_eq_true, ↓reduceIte, endCoord]
  · rw [cycleHandleRadius_inner hτf.2, circTau_false_eq hy]
    ring
  · rw [cycleHandleRadius_outer (by linarith [hτt.2]), circTau_true_eq hy]
    field_simp
    ring
  · rw [cycleHandleRadius_outer (by linarith [hτt.2]), circTau_true_eq hy]
    field_simp
    ring
  · rw [sub_sub_cancel, cycleHandleRadius_inner hτf.2, circTau_false_eq hy]
    ring

/-- The isometry of the rim product: `id` (south) or `−id` (north). -/
def circRimIsometry (b : Bool) : E2 ≃ₗᵢ[ℝ] E2 :=
  if b then LinearIsometryEquiv.neg ℝ else LinearIsometryEquiv.refl ℝ E2

/-- **`RimProduct` for the adapted rim charts** at the end `e` of the handle `cycleS3Handle b`. -/
theorem circRim_rimProductAt (b e : Bool) :
    RimProductAt (W := sphereW) (circRim b e) (cycleS3Handle b) e := by
  refine ⟨1, by norm_num, by norm_num, circRimIsometry b, circRho, circTau (b ^^ e),
    contDiff_circRho, contDiff_circTau _, circRho_zero, circTau_zero _, ?_, ?_, ?_⟩
  · intro x hx
    have hxa : |x| < 1 := abs_lt.2 ⟨hx.1, by linarith [hx.2]⟩
    exact ⟨circRho_pos x, deriv_circRho_pos hxa⟩
  · intro y hy
    exact deriv_circTau_pos _ (abs_lt.2 ⟨by linarith [hy.1], hy.2⟩)
  · intro θ x y w t hx hx' hy hy' hw ht
    have hxa : |x| ≤ 1 := abs_le.2 ⟨hx.le, by linarith⟩
    have hx2 : |x| < 2 := by linarith
    have hy2 : |y| < 2 := abs_lt.2 ⟨by linarith, by linarith⟩
    have hρ := circRho_pos x
    rw [circRim_apply, cycleS3Handle_map, cycleHandleChart_eq_FC39P0]
    dsimp only
    rw [hw, ht]
    simp only [circPlaneMap]
    rw [← cycleHandleRadius_circTau b e hy hy', circRho_eq hxa]
    cases b
    · rw [sphereCircleChart_equiv_symm]
      simp only [circRimIsometry, Bool.false_eq_true, ↓reduceIte, LinearIsometryEquiv.coe_refl,
        id_eq]
    · simp only [circRimIsometry, ↓reduceIte, LinearIsometryEquiv.coe_neg, smul_neg]
      have hs := sphereCircleChart_neg (circCornerInv_pos false false hx2)
        (cycleHandleRadius (1 - endCoord e (circTau (true ^^ e) y))) (circleAntipode_CIRCA θ)
      rw [circleAntipode_antipode_CIRCA, planeOfCircle_antipode_CIRCA] at hs
      simp only [smul_neg] at hs
      exact hs.symm

/-- **`RimProduct` for the rim chart layer of the S³ configuration** (the field
`AdaptedEdgeRimData.product`). -/
theorem sphereRimLayer_rimProduct (h : Fin sphereEdgeLayer.handleCount) (b : Bool) :
    RimProductAt (sphereRimLayer.rimChart h b) (sphereEdgeLayer.handle h) b :=
  circRim_rimProductAt (finTwoEquiv h) b

end GC.GraphManifold.Assembly.FC39P0
