import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Seifert.FillingDisc
import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Seifert.ClassicalInputs

/-!
# The pants with one filled hole as a regular sublevel set

Chapter 6, packet K06c, second part. A `ConeFilling` is `p ≥ 1` with integers `q, a, b`,
`p b - a q = 1`. In `PlaneLift × S¹` with coordinates `(z, w)` the base point is
`conePoint (z, w) = 3/2 + (z/3)^p w^(-a) / 2`, constant along the circle action
`λ (z, w) = (λ^a z, λ^p w)`; the fibre `z = 0` is the cone fibre over `3/2`. The carrier
`filledCarrier` is the regular sublevel set `filledFunction (conePoint x) ≤ 0`, where
`filledFunction` cuts out the disc of radius `3` minus the hole about `-3/2`, so its preimage is the
pants with the hole about `3/2` filled. The value `0` is regular because `conePoint` is a
submersion off `z = 0` (`filledFunction_conePoint_regular`).

The lift `coneLift (ζ, λ) = (seamRadius p (4 ‖ζ - 3/2‖ - 2) T₁, T₂)`,
`T = linearTorusMap !![b, a; q, p] (unit (ζ - 3/2), λ)`, and the chart
`coneChart (z, w) = (conePoint (z, w), (linearTorusMap !![p, -a; -q, b] (unit z, w)).2)` are
inverse (`coneLiftPartialDiffeomorph`, from `ζ ≠ 3/2` to `z ≠ 0`), and `conePoint ∘ coneLift` is the
first projection. The fold `filledFold` is `coneLift` on the pants `productSet 3` and the
inclusion on the solid torus `solidSet = {‖z‖ ≤ 3}`; it is smooth with bijective differential,
and the cut carrier `filledCutCarrier = productSet 3 ⊕ solidSet` is oriented by pulling back the
orientation of the filled carrier along it.
-/

set_option autoImplicit false

noncomputable section
open Set Metric Function
open DifferentialGeometry DifferentialGeometry.Topology GC.Endpoint GC.GraphManifold
open scoped Manifold ContDiff Topology

universe u

namespace GC.Seifert

structure ConeFilling where
  p : ℕ
  q : ℤ
  a : ℤ
  b : ℤ
  one_le : 1 ≤ p
  det_eq : (p : ℤ) * b - a * q = 1

abbrev PlaneCircleModel := 𝓘(ℝ, ℂ).prod (𝓡 1)

namespace ConeFilling

variable (c : ConeFilling)

instance : NeZero c.p := ⟨by have := c.one_le; omega⟩

def liftMatrix : Matrix (Fin 2) (Fin 2) ℤ := !![c.b, c.a; c.q, (c.p : ℤ)]

def chartMatrix : Matrix (Fin 2) (Fin 2) ℤ := !![(c.p : ℤ), -c.a; -c.q, c.b]

theorem liftMatrix_mul_chartMatrix : c.liftMatrix * c.chartMatrix = 1 := by
  have h := c.det_eq
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [liftMatrix, chartMatrix, Matrix.mul_apply, Fin.sum_univ_two] <;> linarith

theorem chartMatrix_mul_liftMatrix : c.chartMatrix * c.liftMatrix = 1 := by
  have h := c.det_eq
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [liftMatrix, chartMatrix, Matrix.mul_apply, Fin.sum_univ_two] <;> linarith

theorem linearTorusMap_chart_lift (x : Torus) :
    linearTorusMap c.chartMatrix (linearTorusMap c.liftMatrix x) = x := by
  rw [← linearTorusMap_mul, chartMatrix_mul_liftMatrix, linearTorusMap_one]

theorem linearTorusMap_lift_chart (x : Torus) :
    linearTorusMap c.liftMatrix (linearTorusMap c.chartMatrix x) = x := by
  rw [← linearTorusMap_mul, liftMatrix_mul_chartMatrix, linearTorusMap_one]

def conePoint (x : PlaneLift.{u} × Circle) : ℂ :=
  ((3 / 2 : ℝ) : ℂ) + (x.1.down / 3) ^ c.p * ((x.2 ^ (-c.a) : Circle) : ℂ) / 2

theorem contMDiff_conePoint : ContMDiff PlaneCircleModel 𝓘(ℝ, ℂ) ∞ c.conePoint.{u} := by
  have h1 : ContMDiff PlaneCircleModel 𝓘(ℝ, ℂ × ℂ) ∞
      (fun x : PlaneLift.{u} × Circle => (x.1.down, ((x.2 ^ (-c.a) : Circle) : ℂ))) :=
    (contMDiff_planeLift_down.comp contMDiff_fst).prodMk_space
      (contMDiff_circle_coe.comp ((contMDiff_circle_zpow _).comp contMDiff_snd))
  have hf : ContDiff ℝ ∞ (fun y : ℂ × ℂ => y.1) := contDiff_fst
  have hs : ContDiff ℝ ∞ (fun y : ℂ × ℂ => y.2) := contDiff_snd
  have h2 : ContDiff ℝ ∞ (fun y : ℂ × ℂ => (y.1 / 3) ^ c.p) := (hf.div_const _).pow c.p
  have h3 : ContDiff ℝ ∞ (fun y : ℂ × ℂ => (y.1 / 3) ^ c.p * y.2 / 2) := (h2.mul hs).div_const _
  have h4 : ContDiff ℝ ∞ (fun y : ℂ × ℂ => ((3 / 2 : ℝ) : ℂ) + (y.1 / 3) ^ c.p * y.2 / 2) :=
    contDiff_const.add h3
  have h := h4.contMDiff.comp h1
  intro x
  exact (h x).congr_of_eventuallyEq (Filter.Eventually.of_forall fun y => rfl)

theorem norm_conePoint_sub (x : PlaneLift.{u} × Circle) :
    ‖c.conePoint x - ((3 / 2 : ℝ) : ℂ)‖ = (‖x.1.down‖ / 3) ^ c.p / 2 := by
  simp [conePoint, norm_pow, Circle.norm_coe]

theorem conePoint_sub (x : PlaneLift.{u} × Circle) :
    c.conePoint x - ((3 / 2 : ℝ) : ℂ) = ((‖x.1.down‖ / 3) ^ c.p / 2 : ℝ) •
      ((linearTorusMap c.chartMatrix (unitOf x.1.down, x.2)).1 : ℂ) := by
  have hz : x.1.down = ((‖x.1.down‖ : ℝ) : ℂ) * (unitOf x.1.down : ℂ) := by
    rw [← Complex.real_smul, norm_smul_unitOf]
  set v := unitOf x.1.down
  set r := ‖x.1.down‖
  simp only [conePoint, linearTorusMap, chartMatrix, Matrix.of_apply, Matrix.cons_val',
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.empty_val', Matrix.cons_val_fin_one,
    Circle.coe_mul, Circle.coe_zpow, zpow_natCast, Complex.real_smul]
  rw [hz]
  push_cast
  ring

theorem unitOf_conePoint_sub (x : PlaneLift.{u} × Circle) (hx : x.1.down ≠ 0) :
    unitOf (c.conePoint x - ((3 / 2 : ℝ) : ℂ)) =
      (linearTorusMap c.chartMatrix (unitOf x.1.down, x.2)).1 := by
  rw [c.conePoint_sub x]
  exact unitOf_smul (by have := norm_pos_iff.mpr hx; positivity) _

theorem conePoint_ne (x : PlaneLift.{u} × Circle) (hx : x.1.down ≠ 0) :
    c.conePoint x ≠ ((3 / 2 : ℝ) : ℂ) := by
  intro h
  have h1 := c.norm_conePoint_sub x
  rw [h, sub_self, norm_zero] at h1
  have : 0 < (‖x.1.down‖ / 3) ^ c.p / 2 := by
    have := norm_pos_iff.mpr hx
    positivity
  linarith

def coneDepth (x : PlaneLift.{u} × Circle) : ℝ := 4 * ‖x.1.down - ((3 / 2 : ℝ) : ℂ)‖ - 2

def coneTorus (x : PlaneLift.{u} × Circle) : Torus :=
  linearTorusMap c.liftMatrix (unitOf (x.1.down - ((3 / 2 : ℝ) : ℂ)), x.2)

def coneLift (x : PlaneLift.{u} × Circle) : PlaneLift.{u} × Circle :=
  (ULift.up (seamRadius c.p (coneDepth x) • ((c.coneTorus x).1 : ℂ)), (c.coneTorus x).2)

def coneChart (y : PlaneLift.{u} × Circle) : PlaneLift.{u} × Circle :=
  (ULift.up (c.conePoint y), (linearTorusMap c.chartMatrix (unitOf y.1.down, y.2)).2)

theorem coneDepth_gt {x : PlaneLift.{u} × Circle} (hx : x.1.down ≠ ((3 / 2 : ℝ) : ℂ)) :
    -2 < coneDepth x := by
  have := norm_pos_iff.mpr (sub_ne_zero.mpr hx)
  unfold coneDepth
  linarith

theorem norm_coneLift (x : PlaneLift.{u} × Circle) (hx : x.1.down ≠ ((3 / 2 : ℝ) : ℂ)) :
    ‖(c.coneLift x).1.down‖ = seamRadius c.p (coneDepth x) :=
  norm_seamRadius_smul c.p (coneDepth_gt hx) _

theorem coneLift_ne_zero (x : PlaneLift.{u} × Circle) (hx : x.1.down ≠ ((3 / 2 : ℝ) : ℂ)) :
    (c.coneLift x).1.down ≠ 0 := by
  rw [← norm_pos_iff, c.norm_coneLift x hx]
  exact seamRadius_pos _ (coneDepth_gt hx)

theorem unitOf_coneLift (x : PlaneLift.{u} × Circle) (hx : x.1.down ≠ ((3 / 2 : ℝ) : ℂ)) :
    unitOf (c.coneLift x).1.down = (c.coneTorus x).1 :=
  unitOf_smul (seamRadius_pos _ (coneDepth_gt hx)) _

theorem conePoint_coneLift (x : PlaneLift.{u} × Circle) (hx : x.1.down ≠ ((3 / 2 : ℝ) : ℂ)) :
    c.conePoint (c.coneLift x) = x.1.down := by
  have h := c.conePoint_sub (c.coneLift x)
  rw [c.norm_coneLift x hx, c.unitOf_coneLift x hx,
    div_three_pow_seamRadius c.p (coneDepth_gt hx)] at h
  have hT : ((c.coneTorus x).1, (c.coneLift x).2) = c.coneTorus x := rfl
  rw [hT, coneTorus, linearTorusMap_chart_lift] at h
  have hr : (1 + coneDepth x / 2) / 2 = ‖x.1.down - ((3 / 2 : ℝ) : ℂ)‖ := by
    unfold coneDepth
    ring
  rw [hr, norm_smul_unitOf] at h
  exact sub_left_injective h

theorem coneChart_coneLift (x : PlaneLift.{u} × Circle) (hx : x.1.down ≠ ((3 / 2 : ℝ) : ℂ)) :
    c.coneChart (c.coneLift x) = x := by
  have hT : (unitOf (c.coneLift x).1.down, (c.coneLift x).2) = c.coneTorus x := by
    rw [c.unitOf_coneLift x hx]
    rfl
  refine Prod.ext (ULift.ext (c.conePoint_coneLift x hx)) ?_
  change (linearTorusMap c.chartMatrix (unitOf (c.coneLift x).1.down, (c.coneLift x).2)).2 = x.2
  rw [hT, coneTorus, linearTorusMap_chart_lift]

theorem coneLift_coneChart (y : PlaneLift.{u} × Circle) (hy : y.1.down ≠ 0) :
    c.coneLift (c.coneChart y) = y := by
  have hpos : 0 < (‖y.1.down‖ / 3) ^ c.p / 2 := by
    have := norm_pos_iff.mpr hy
    positivity
  have hsub : (c.coneChart y).1.down - ((3 / 2 : ℝ) : ℂ) = ((‖y.1.down‖ / 3) ^ c.p / 2 : ℝ) •
      ((linearTorusMap c.chartMatrix (unitOf y.1.down, y.2)).1 : ℂ) :=
    c.conePoint_sub y
  have hdepth : coneDepth (c.coneChart y) = seamDepth c.p ‖y.1.down‖ := by
    unfold coneDepth seamDepth
    rw [hsub, norm_smul, Circle.norm_coe, mul_one, Real.norm_of_nonneg hpos.le]
    ring
  have htorus : c.coneTorus (c.coneChart y) = (unitOf y.1.down, y.2) := by
    unfold coneTorus
    rw [hsub, unitOf_smul hpos]
    exact c.linearTorusMap_lift_chart _
  unfold coneLift
  rw [hdepth, htorus, seamRadius_seamDepth c.p (norm_nonneg _), norm_smul_unitOf]

theorem contMDiffAt_coneLift {x : PlaneLift.{u} × Circle}
    (hx : x.1.down ≠ ((3 / 2 : ℝ) : ℂ)) :
    ContMDiffAt PlaneCircleModel PlaneCircleModel ∞ c.coneLift x := by
  have hd : ContMDiffAt PlaneCircleModel 𝓘(ℝ, ℂ) ∞
      (fun x : PlaneLift.{u} × Circle => x.1.down - ((3 / 2 : ℝ) : ℂ)) x :=
    ((contDiff_id.sub contDiff_const).contMDiff.comp
      (contMDiff_planeLift_down.comp contMDiff_fst)).contMDiffAt
  have hne : x.1.down - ((3 / 2 : ℝ) : ℂ) ≠ 0 := sub_ne_zero.mpr hx
  have hu : ContMDiffAt PlaneCircleModel (𝓡 1) ∞
      (fun x : PlaneLift.{u} × Circle => unitOf (x.1.down - ((3 / 2 : ℝ) : ℂ))) x :=
    (contMDiffOn_unitOf.contMDiffAt (isOpen_ne.mem_nhds hne)).comp x hd
  have hT : ContMDiffAt PlaneCircleModel torusModel ∞ c.coneTorus.{u} x :=
    (contMDiff_linearTorusMap _).contMDiffAt.comp x (hu.prodMk contMDiff_snd.contMDiffAt)
  have hn : ContMDiffAt PlaneCircleModel 𝓘(ℝ, ℝ) ∞
      (fun x : PlaneLift.{u} × Circle => ‖x.1.down - ((3 / 2 : ℝ) : ℂ)‖) x :=
    (contDiffAt_norm ℝ hne).contMDiffAt.comp x hd
  have hdep : ContMDiffAt PlaneCircleModel 𝓘(ℝ, ℝ) ∞ coneDepth.{u} x :=
    ((contDiff_const.mul contDiff_id).sub contDiff_const).contMDiff.contMDiffAt.comp x hn
  have hr : ContMDiffAt PlaneCircleModel 𝓘(ℝ, ℝ) ∞
      (fun x : PlaneLift.{u} × Circle => seamRadius c.p (coneDepth x)) x :=
    (contDiffAt_seamRadius c.p (coneDepth_gt hx)).contMDiffAt.comp x hdep
  have hc : ContMDiffAt PlaneCircleModel 𝓘(ℝ, ℂ) ∞
      (fun x : PlaneLift.{u} × Circle => ((c.coneTorus x).1 : ℂ)) x :=
    contMDiff_circle_coe.contMDiffAt.comp x (contMDiff_fst.contMDiffAt.comp x hT)
  exact (contMDiff_planeLift_up.contMDiffAt.comp x (hr.smul hc)).prodMk
    (contMDiff_snd.contMDiffAt.comp x hT)

theorem contMDiffAt_coneChart {y : PlaneLift.{u} × Circle} (hy : y.1.down ≠ 0) :
    ContMDiffAt PlaneCircleModel PlaneCircleModel ∞ c.coneChart y := by
  have hd : ContMDiffAt PlaneCircleModel 𝓘(ℝ, ℂ) ∞
      (fun y : PlaneLift.{u} × Circle => y.1.down) y :=
    (contMDiff_planeLift_down.comp contMDiff_fst).contMDiffAt
  have hv : ContMDiffAt PlaneCircleModel (𝓡 1) ∞
      (fun y : PlaneLift.{u} × Circle => unitOf y.1.down) y :=
    (contMDiffOn_unitOf.contMDiffAt (isOpen_ne.mem_nhds hy)).comp y hd
  exact (contMDiff_planeLift_up.comp c.contMDiff_conePoint).contMDiffAt.prodMk
    (contMDiff_snd.contMDiffAt.comp y ((contMDiff_linearTorusMap _).contMDiffAt.comp y
      (hv.prodMk contMDiff_snd.contMDiffAt)))

def coneLiftPartialDiffeomorph :
    PartialDiffeomorph PlaneCircleModel PlaneCircleModel (PlaneLift.{u} × Circle)
      (PlaneLift.{u} × Circle) ∞ where
  toFun := c.coneLift
  invFun := c.coneChart
  source := {x | x.1.down ≠ ((3 / 2 : ℝ) : ℂ)}
  target := {y | y.1.down ≠ 0}
  map_source' x hx := c.coneLift_ne_zero x hx
  map_target' y hy := c.conePoint_ne y hy
  left_inv' x hx := c.coneChart_coneLift x hx
  right_inv' y hy := c.coneLift_coneChart y hy
  open_source := isOpen_ne_fun (continuous_uliftDown.comp continuous_fst) continuous_const
  open_target := isOpen_ne_fun (continuous_uliftDown.comp continuous_fst) continuous_const
  contMDiffOn_toFun _ hx := (c.contMDiffAt_coneLift hx).contMDiffWithinAt
  contMDiffOn_invFun _ hy := (c.contMDiffAt_coneChart hy).contMDiffWithinAt

theorem coneLiftPartialDiffeomorph_apply (x : PlaneLift.{u} × Circle) :
    c.coneLiftPartialDiffeomorph x = c.coneLift x := rfl

def filledFunction (ζ : ℂ) : ℝ := sqDist 0 3 ζ * sqDist ((-(3 / 2) : ℝ) : ℂ) (1 / 2) ζ

theorem contDiff_filledFunction : ContDiff ℝ ∞ filledFunction :=
  (contDiff_sqDist _ _).mul (contDiff_sqDist _ _)

theorem norm_add_three_halves_ge (ζ : ℂ) :
    3 - ‖ζ - ((3 / 2 : ℝ) : ℂ)‖ ≤ ‖ζ - ((-(3 / 2) : ℝ) : ℂ)‖ := by
  have := le_norm_sub_planarCenter ζ (3 / 2) (-(3 / 2))
  rw [show |(3 / 2 : ℝ) - -(3 / 2)| = 3 by norm_num] at this
  linarith

theorem filledFunction_nonpos_iff (ζ : ℂ) :
    filledFunction ζ ≤ 0 ↔ ‖ζ‖ ≤ 3 ∧ 1 / 2 ≤ ‖ζ - ((-(3 / 2) : ℝ) : ℂ)‖ := by
  have hc := norm_sub_real_bounds ζ (-(3 / 2))
  rw [abs_neg, abs_of_pos (by norm_num : (0 : ℝ) < 3 / 2)] at hc
  have h0 := norm_nonneg ζ
  have hc0 := norm_nonneg (ζ - ((-(3 / 2) : ℝ) : ℂ))
  simp only [filledFunction, sqDist, sub_zero]
  set a := ‖ζ‖
  set b := ‖ζ - ((-(3 / 2) : ℝ) : ℂ)‖
  constructor
  · intro h
    by_contra hn
    rw [not_and_or, not_le, not_le] at hn
    rcases hn with hn | hn
    · have : 0 < (a ^ 2 - 3 ^ 2) * (b ^ 2 - (1 / 2) ^ 2) :=
        mul_pos (by nlinarith) (by nlinarith)
      linarith
    · have : 0 < (a ^ 2 - 3 ^ 2) * (b ^ 2 - (1 / 2) ^ 2) :=
        mul_pos_of_neg_of_neg (by nlinarith) (by nlinarith)
      linarith
  · rintro ⟨h1, h2⟩
    exact mul_nonpos_iff.mpr (Or.inr ⟨by nlinarith, by nlinarith⟩)

theorem filledFunction_neg_of_near {ζ : ℂ} (h : ‖ζ - ((3 / 2 : ℝ) : ℂ)‖ < 1) :
    filledFunction ζ < 0 := by
  have hb := norm_sub_real_bounds ζ (3 / 2)
  rw [abs_of_pos (by norm_num : (0 : ℝ) < 3 / 2)] at hb
  have h2 := norm_add_three_halves_ge ζ
  have h0 := norm_nonneg ζ
  simp only [filledFunction, sqDist, sub_zero]
  exact mul_neg_of_neg_of_pos (by nlinarith) (by nlinarith)

theorem filledFunction_nonpos_iff_mem {ζ : ℂ} (h : 1 / 2 ≤ ‖ζ - ((3 / 2 : ℝ) : ℂ)‖) :
    filledFunction ζ ≤ 0 ↔ ζ ∈ planarModel 3 := by
  rw [filledFunction_nonpos_iff, mem_planarModel_three]
  exact ⟨fun h' => ⟨h'.1, h, h'.2⟩, fun h' => ⟨h'.1, h'.2.2⟩⟩

theorem filledFunction_regular {ζ : ℂ} (hz : filledFunction ζ = 0) :
    fderiv ℝ filledFunction ζ ≠ 0 := by
  have hd (c : ℂ) (ρ : ℝ) : DifferentiableAt ℝ (sqDist c ρ) ζ :=
    (contDiff_sqDist c ρ).differentiable (by simp) ζ
  have hc := norm_sub_real_bounds ζ (-(3 / 2))
  rw [abs_neg, abs_of_pos (by norm_num : (0 : ℝ) < 3 / 2)] at hc
  have h0 := norm_nonneg ζ
  have hc0 := norm_nonneg (ζ - ((-(3 / 2) : ℝ) : ℂ))
  have he : filledFunction = fun w => sqDist 0 3 w * sqDist ((-(3 / 2) : ℝ) : ℂ) (1 / 2) w := rfl
  rw [he] at hz ⊢
  rcases mul_eq_zero.mp hz with h | h
  · have hn := norm_sub_eq_of_sqDist_eq_zero (by norm_num : (0 : ℝ) ≤ 3) h
    rw [sub_zero] at hn
    refine fderiv_sqDist_mul_ne_zero (hd _ _) h ?_ (by norm_num)
    simp only [sqDist]
    nlinarith
  · have hn := norm_sub_eq_of_sqDist_eq_zero (by norm_num : (0 : ℝ) ≤ 1 / 2) h
    rw [show (fun w => sqDist 0 3 w * sqDist ((-(3 / 2) : ℝ) : ℂ) (1 / 2) w) =
      fun w => sqDist ((-(3 / 2) : ℝ) : ℂ) (1 / 2) w * sqDist 0 3 w from
        funext fun w => mul_comm _ _]
    refine fderiv_sqDist_mul_ne_zero (hd _ _) h ?_ (by norm_num)
    simp only [sqDist, sub_zero]
    nlinarith

theorem comp_mul_ne_zero {L : ℂ →L[ℝ] ℝ} (hL : L ≠ 0) {d : ℂ} (hd : d ≠ 0) :
    L.comp (((1 : ℂ →L[ℂ] ℂ).smulRight d).restrictScalars ℝ) ≠ 0 := by
  intro h
  apply hL
  ext v
  have h2 : (((1 : ℂ →L[ℂ] ℂ).smulRight d).restrictScalars ℝ) (v / d) = v := by
    change v / d * d = v
    exact div_mul_cancel₀ v hd
  have h1 := DFunLike.congr_fun h (v / d)
  rw [ContinuousLinearMap.comp_apply, h2] at h1
  simpa using h1

theorem filledFunction_conePoint_regular (x : PlaneLift.{u} × Circle)
    (hx : filledFunction (c.conePoint x) = 0) :
    mfderiv PlaneCircleModel 𝓘(ℝ, ℝ) (fun x : PlaneLift.{u} × Circle =>
      filledFunction (c.conePoint x)) x ≠ 0 := by
  have hz : x.1.down ≠ 0 := by
    intro h0
    have hn := c.norm_conePoint_sub x
    rw [h0, norm_zero, zero_div, zero_pow (NeZero.ne c.p), zero_div] at hn
    have := filledFunction_neg_of_near (ζ := c.conePoint x) (by rw [hn]; norm_num)
    linarith
  have hG : ContMDiff PlaneCircleModel 𝓘(ℝ, ℝ) ∞
      (fun x : PlaneLift.{u} × Circle => filledFunction (c.conePoint x)) :=
    contDiff_filledFunction.contMDiff.comp c.contMDiff_conePoint
  refine mfderiv_ne_zero_of_comp (J := 𝓘(ℝ, ℂ))
    (s := fun w : ℂ => ((ULift.up w : PlaneLift.{u}), x.2)) (y := x.1.down)
    (hG.mdifferentiableAt (by simp))
    ((contMDiff_planeLift_up.prodMk contMDiff_const).mdifferentiableAt (by simp)) ?_
  set W : ℂ := ((x.2 ^ (-c.a) : Circle) : ℂ)
  have hW : W ≠ 0 := Circle.coe_ne_zero _
  set h : ℂ → ℂ := fun w => ((3 / 2 : ℝ) : ℂ) + (w / 3) ^ c.p * W / 2
  set d : ℂ := (c.p : ℂ) * (x.1.down / 3) ^ (c.p - 1) * (1 / 3) * W / 2
  have hdh : HasDerivAt h d x.1.down := by
    have h1 := (((hasDerivAt_id x.1.down).div_const 3).pow c.p).mul_const W
    have h2 := (h1.div_const 2).const_add ((3 / 2 : ℝ) : ℂ)
    exact h2
  have hd : d ≠ 0 := by
    have hp : (c.p : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne c.p)
    simp only [d]
    exact div_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero hp (pow_ne_zero _
      (div_ne_zero hz (by norm_num)))) (by norm_num)) hW) (by norm_num)
  have hcomp : (fun x : PlaneLift.{u} × Circle => filledFunction (c.conePoint x)) ∘
      (fun w : ℂ => ((ULift.up w : PlaneLift.{u}), x.2)) = filledFunction ∘ h := rfl
  rw [hcomp, mfderiv_eq_fderiv]
  have hf : HasFDerivAt filledFunction (fderiv ℝ filledFunction (h x.1.down)) (h x.1.down) :=
    (contDiff_filledFunction.differentiable (by simp) _).hasFDerivAt
  rw [(hf.comp x.1.down (hdh.hasFDerivAt.restrictScalars ℝ)).fderiv]
  refine comp_mul_ne_zero (filledFunction_regular ?_) hd
  exact hx

def filledSet : Set (PlaneLift.{u} × Circle) := {x | filledFunction (c.conePoint x) ≤ 0}

theorem contMDiff_filledFunction_conePoint : ContMDiff PlaneCircleModel 𝓘(ℝ, ℝ) ∞
    (fun x : PlaneLift.{u} × Circle => filledFunction (c.conePoint x)) :=
  contDiff_filledFunction.contMDiff.comp c.contMDiff_conePoint

def filledAtlas : SmoothBoundaryAtlas PlaneCircleModel 3 c.filledSet.{u} :=
  SmoothBoundaryAtlas.regularSublevel PlaneCircleModel (n := 2) finrank_planeCircleModel
    c.contMDiff_filledFunction_conePoint.{u} 0 c.filledFunction_conePoint_regular

instance : ChartedSpace (EuclideanHalfSpace 3) c.filledSet.{u} := c.filledAtlas.toChartedSpace

instance : IsManifold (𝓡∂ 3) ∞ c.filledSet.{u} := c.filledAtlas.isManifold

theorem filledSet_isBoundaryPoint_iff (y : c.filledSet.{u}) :
    (𝓡∂ 3).IsBoundaryPoint y ↔ filledFunction (c.conePoint y.val) = 0 :=
  SmoothBoundaryAtlas.regularSublevel_isBoundaryPoint_iff PlaneCircleModel (n := 2)
    finrank_planeCircleModel c.contMDiff_filledFunction_conePoint 0
    c.filledFunction_conePoint_regular y

theorem filledSet_isInteriorPoint_iff (y : c.filledSet.{u}) :
    (𝓡∂ 3).IsInteriorPoint y ↔ filledFunction (c.conePoint y.val) < 0 :=
  SmoothBoundaryAtlas.regularSublevel_isInteriorPoint_iff PlaneCircleModel (n := 2)
    finrank_planeCircleModel c.contMDiff_filledFunction_conePoint 0
    c.filledFunction_conePoint_regular y

theorem norm_le_of_mem_filledSet {x : PlaneLift.{u} × Circle} (hx : x ∈ c.filledSet) :
    ‖x.1.down‖ ≤ 27 := by
  have h1 := ((filledFunction_nonpos_iff _).mp hx).1
  have h2 := c.norm_conePoint_sub x
  have h3 := norm_sub_le (c.conePoint x) ((3 / 2 : ℝ) : ℂ)
  rw [Complex.norm_real, Real.norm_of_nonneg (by norm_num)] at h3
  by_contra hn
  rw [not_le] at hn
  have h4 : ‖x.1.down‖ / 3 ≤ (‖x.1.down‖ / 3) ^ c.p :=
    le_self_pow₀ (by linarith) (NeZero.ne c.p)
  linarith

theorem isCompact_filledSet : IsCompact c.filledSet.{u} := by
  have hK : IsCompact (((Homeomorph.ulift : PlaneLift.{u} ≃ₜ ℂ) ⁻¹' closedBall 0 27) ×ˢ
      (univ : Set Circle)) :=
    (Homeomorph.ulift.isCompact_preimage.mpr (isCompact_closedBall 0 27)).prod isCompact_univ
  refine hK.of_isClosed_subset (isClosed_le c.contMDiff_filledFunction_conePoint.continuous
    continuous_const) fun x hx => ⟨?_, mem_univ _⟩
  exact mem_closedBall_zero_iff.mpr (c.norm_le_of_mem_filledSet hx)

instance : CompactSpace c.filledSet.{u} := isCompact_iff_compactSpace.mp c.isCompact_filledSet

abbrev filledCarrier : CompactCarrier.{u} where
  kind := .withBoundary
  Carrier := c.filledSet.{u}
  charts := (inferInstance : ChartedSpace (EuclideanHalfSpace 3) c.filledSet.{u})
  smooth := (inferInstance : IsManifold (𝓡∂ 3) ∞ c.filledSet.{u})
  orientation := c.filledAtlas.orientation planeCircleOrientation

theorem ne_three_halves_of_mem_productSet (x : productSet.{u} 3) :
    x.val.1.down ≠ ((3 / 2 : ℝ) : ℂ) := by
  have h := ((mem_planarModel_three _).mp ((mem_planarSet_iff (Or.inr rfl) x.val.1).mp x.2)).2.1
  intro he
  rw [he, sub_self, norm_zero] at h
  norm_num at h

theorem coneLift_mem_filledSet (x : productSet.{u} 3) : c.coneLift x.val ∈ c.filledSet := by
  change filledFunction (c.conePoint (c.coneLift x.val)) ≤ 0
  rw [c.conePoint_coneLift _ (ne_three_halves_of_mem_productSet x)]
  have hx := (mem_planarModel_three _).mp ((mem_planarSet_iff (Or.inr rfl) x.val.1).mp x.2)
  exact (filledFunction_nonpos_iff _).mpr ⟨hx.1, hx.2.2⟩

theorem filledFunction_conePoint_neg_of_mem_solidSet {x : PlaneLift.{u} × Circle}
    (hx : x ∈ solidSet) : filledFunction (c.conePoint x) < 0 := by
  refine filledFunction_neg_of_near ?_
  rw [c.norm_conePoint_sub]
  have h1 := (mem_solidSet_iff x).mp hx
  have h2 : (‖x.1.down‖ / 3) ^ c.p ≤ 1 := pow_le_one₀ (by positivity) (by linarith)
  linarith

def productFold (x : productSet.{u} 3) : c.filledSet.{u} :=
  ⟨c.coneLift x.val, c.coneLift_mem_filledSet x⟩

def solidFold (x : solidSet.{u}) : c.filledSet.{u} :=
  ⟨x.val, (c.filledFunction_conePoint_neg_of_mem_solidSet x.2).le⟩

abbrev FilledCut : Type u := productSet.{u} 3 ⊕ solidSet.{u}

def filledFold : FilledCut.{u} → c.filledSet.{u} := Sum.elim c.productFold c.solidFold

instance : CompactSpace (productSet.{u} 3) := (productCarrier.{u} 3 (Or.inr rfl)).compact

theorem contMDiff_productFold : ContMDiff (𝓡∂ 3) (𝓡∂ 3) ∞ c.productFold.{u} := by
  refine (c.filledAtlas.contMDiff_iff_subtype_val _).mpr fun x => ?_
  exact (c.contMDiffAt_coneLift (ne_three_halves_of_mem_productSet x)).comp x
    ((productAtlas.{u} 3).contMDiff_subtype_val x)

theorem contMDiff_solidFold : ContMDiff (𝓡∂ 3) (𝓡∂ 3) ∞ c.solidFold.{u} :=
  (c.filledAtlas.contMDiff_iff_subtype_val _).mpr solidAtlas.contMDiff_subtype_val

theorem contMDiff_filledFold : ContMDiff (𝓡∂ 3) (𝓡∂ 3) ∞ c.filledFold.{u} :=
  ContMDiff.sumElim c.contMDiff_productFold c.contMDiff_solidFold

theorem bijective_mfderiv_of_comp {E H M F G N E' H' M' : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [TopologicalSpace M]
    [ChartedSpace H M] [NormedAddCommGroup F] [NormedSpace ℝ F] [TopologicalSpace G]
    {J : ModelWithCorners ℝ F G} [TopologicalSpace N] [ChartedSpace G N]
    [NormedAddCommGroup E'] [NormedSpace ℝ E'] [TopologicalSpace H']
    {K : ModelWithCorners ℝ E' H'} [TopologicalSpace M'] [ChartedSpace H' M']
    {f : M → N} {g : N → M'} {x : M} (hg : MDifferentiableAt J K g (f x))
    (hf : MDifferentiableAt I J f x) (hgb : Bijective (mfderiv J K g (f x)))
    (hb : Bijective (mfderiv I K (g ∘ f) x)) : Bijective (mfderiv I J f x) := by
  rw [mfderiv_comp x hg hf, ContinuousLinearMap.coe_comp] at hb
  refine ⟨hb.injective.of_comp, fun y => ?_⟩
  obtain ⟨v, hv⟩ := hb.surjective (mfderiv J K g (f x) y)
  exact ⟨v, hgb.injective hv⟩

theorem bijective_mfderiv_of_isLocalDiffeomorphAt {E H M F G N : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [TopologicalSpace M]
    [ChartedSpace H M] [NormedAddCommGroup F] [NormedSpace ℝ F] [TopologicalSpace G]
    {J : ModelWithCorners ℝ F G} [TopologicalSpace N] [ChartedSpace G N]
    {f : M → N} {x : M} (h : IsLocalDiffeomorphAt I J ∞ f x) :
    Bijective (mfderiv I J f x) := by
  rw [← h.mfderivToContinuousLinearEquiv_coe (by simp)]
  exact (h.mfderivToContinuousLinearEquiv (by simp)).bijective

theorem mfderiv_productFold_bijective (x : productSet.{u} 3) :
    Bijective (mfderiv (𝓡∂ 3) (𝓡∂ 3) c.productFold x) := by
  have hx := ne_three_halves_of_mem_productSet x
  refine bijective_mfderiv_of_comp (g := Subtype.val) (K := PlaneCircleModel)
    (c.filledAtlas.contMDiff_subtype_val.mdifferentiableAt (by simp))
    (c.contMDiff_productFold.mdifferentiableAt (by simp))
    (c.filledAtlas.mfderiv_subtypeVal_bijective _) ?_
  have hval : MDifferentiableAt (𝓡∂ 3) PlaneCircleModel (Subtype.val : productSet.{u} 3 → _) x :=
    (productAtlas.{u} 3).contMDiff_subtype_val.mdifferentiableAt (by simp)
  have hlift : MDifferentiableAt PlaneCircleModel PlaneCircleModel c.coneLift x.val :=
    (c.contMDiffAt_coneLift hx).mdifferentiableAt (by simp)
  change Bijective (mfderiv (𝓡∂ 3) PlaneCircleModel (c.coneLift ∘ Subtype.val) x)
  rw [mfderiv_comp x hlift hval, ContinuousLinearMap.coe_comp]
  refine Bijective.comp ?_ ((productAtlas.{u} 3).mfderiv_subtypeVal_bijective x)
  exact bijective_mfderiv_of_isLocalDiffeomorphAt
    (c.coneLiftPartialDiffeomorph.isLocalDiffeomorphAt PlaneCircleModel PlaneCircleModel ∞ hx)

theorem mfderiv_solidFold_bijective (x : solidSet.{u}) :
    Bijective (mfderiv (𝓡∂ 3) (𝓡∂ 3) c.solidFold x) :=
  bijective_mfderiv_of_comp (g := Subtype.val) (K := PlaneCircleModel)
    (c.filledAtlas.contMDiff_subtype_val.mdifferentiableAt (by simp))
    (c.contMDiff_solidFold.mdifferentiableAt (by simp))
    (c.filledAtlas.mfderiv_subtypeVal_bijective _) (solidAtlas.mfderiv_subtypeVal_bijective x)

theorem mfderiv_filledFold_bijective (x : FilledCut.{u}) :
    Bijective (mfderiv (𝓡∂ 3) (𝓡∂ 3) c.filledFold x) := by
  have hf : MDifferentiableAt (𝓡∂ 3) (𝓡∂ 3) c.filledFold x :=
    c.contMDiff_filledFold.mdifferentiableAt (by simp)
  rcases x with a | b
  · have hi : MDifferentiableAt (𝓡∂ 3) (𝓡∂ 3)
        (Sum.inl : productSet.{u} 3 → FilledCut.{u}) a :=
      (ContMDiff.inl : ContMDiff (𝓡∂ 3) (𝓡∂ 3) ∞
        (Sum.inl : productSet.{u} 3 → FilledCut.{u})).mdifferentiableAt (by simp)
    have h := mfderiv_comp a hf hi
    rw [hasMFDerivAt_inl.mfderiv] at h
    have hb := c.mfderiv_productFold_bijective a
    change Bijective (mfderiv (𝓡∂ 3) (𝓡∂ 3)
      (c.filledFold ∘ (Sum.inl : productSet.{u} 3 → FilledCut.{u})) a) at hb
    rw [h] at hb
    exact hb
  · have hi : MDifferentiableAt (𝓡∂ 3) (𝓡∂ 3)
        (Sum.inr : solidSet.{u} → FilledCut.{u}) b :=
      (ContMDiff.inr : ContMDiff (𝓡∂ 3) (𝓡∂ 3) ∞
        (Sum.inr : solidSet.{u} → FilledCut.{u})).mdifferentiableAt (by simp)
    have h := mfderiv_comp b hf hi
    rw [hasMFDerivAt_inr.mfderiv] at h
    have hb := c.mfderiv_solidFold_bijective b
    change Bijective (mfderiv (𝓡∂ 3) (𝓡∂ 3)
      (c.filledFold ∘ (Sum.inr : solidSet.{u} → FilledCut.{u})) b) at hb
    rw [h] at hb
    exact hb

def filledCutOrientation : ManifoldOrientation (𝓡∂ 3) FilledCut.{u} 3 :=
  Manifold.manifoldOrientationPullback (𝓡∂ 3) (𝓡∂ 3) finrank_euclideanSpace_fin c.filledFold
    c.contMDiff_filledFold c.mfderiv_filledFold_bijective c.filledCarrier.orientation

theorem orientation_map_filledCutOrientation (x : FilledCut.{u}) :
    Orientation.map (Fin 3) (Manifold.differentialEquivOfBijective (𝓡∂ 3) (𝓡∂ 3) c.filledFold
      c.mfderiv_filledFold_bijective x).toLinearEquiv (c.filledCutOrientation.orientation x) =
      c.filledCarrier.orientation.orientation (c.filledFold x) :=
  Manifold.orientation_map_manifoldOrientationPullback (𝓡∂ 3) (𝓡∂ 3) finrank_euclideanSpace_fin
    c.filledFold c.contMDiff_filledFold c.mfderiv_filledFold_bijective
    c.filledCarrier.orientation x

abbrev filledCutCarrier : CompactCarrier.{u} where
  kind := .withBoundary
  Carrier := FilledCut.{u}
  charts := (inferInstance : ChartedSpace (EuclideanHalfSpace 3) FilledCut.{u})
  smooth := (inferInstance : IsManifold (𝓡∂ 3) ∞ FilledCut.{u})
  orientation := c.filledCutOrientation

end ConeFilling

end GC.Seifert
