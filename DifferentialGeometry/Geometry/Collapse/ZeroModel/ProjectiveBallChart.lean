import DifferentialGeometry.Geometry.Collapse.ZeroModel.ProjectiveBand
import DifferentialGeometry.Topology.Manifold.BallChartOrientation
import DifferentialGeometry.Topology.ThreeManifold.ConnectedSum.OppositeSum

/-!
# The polar ball chart of `ℝP³`

Lane LFR54-QUOT (Q1). The affine chart `v ↦ [(v, 1) / √(1 + ‖v‖²)]` of
`P = projectiveThreeSpaceLift` is a ball chart (`bandBallChart`) whose unit ball is exactly the
polar cap `{w₃² > ½}` (`bandChart_image_ball`), the complement of the equatorial band, and whose unit sphere is the
level `{w₃² = ½}` (`bandChart_image_sphere`). Reflecting it if necessary gives an ORIENTED ball
chart with the same unit-ball and unit-sphere images (`exists_orientedBallChart_image_ball_eq`).
-/

set_option autoImplicit false

noncomputable section

open Set Function Module Metric
open scoped Manifold ContDiff Topology

namespace DifferentialGeometry.Geometry.Collapse.ZeroModel.Projective

open DifferentialGeometry.Topology DifferentialGeometry.Geometry.Collapse.ZeroModel.SpaceForm

universe u

local notation "E3" => EuclideanSpace ℝ (Fin 3)
local notation "E4" => EuclideanSpace ℝ (Fin 4)
local notation "S3" => sphere (0 : EuclideanSpace ℝ (Fin 4)) 1

/-- `ℝ⁴` has dimension `3 + 1`. -/
local instance finrankFourFactChart_LFR54QUOT : Fact (finrank ℝ E4 = 3 + 1) := ⟨by simp⟩

theorem chartSphere_mem (v : E3) : (√(1 + ‖v‖ ^ 2))⁻¹ • e4Join v 1 ∈ S3 := by
  rw [mem_sphere_zero_iff_norm, norm_smul, norm_inv, Real.norm_eq_abs,
    abs_of_nonneg (Real.sqrt_nonneg _)]
  have h := norm_sq_e4Join v 1
  rw [one_pow, add_comm] at h
  rw [← Real.sqrt_sq (norm_nonneg (e4Join v 1)), h]
  have hp : (0 : ℝ) < 1 + ‖v‖ ^ 2 := by positivity
  exact inv_mul_cancel₀ (Real.sqrt_pos.mpr hp).ne'

/-- The point `(v, 1) / √(1 + ‖v‖²)` of `S³`. -/
def chartSphere (v : E3) : S3 := ⟨_, chartSphere_mem v⟩

/-- The affine chart `v ↦ [(v, 1) / √(1 + ‖v‖²)]`. -/
def bandChartMap (v : E3) : projectiveThreeSpaceLift.{u}.Carrier :=
  rpUp (rpGroup.projection (chartSphere v))

/-- `w ↦ w' / w₃` on `S³`. -/
def chartInvSphere (x : S3) : E3 := ((x : E4) 3)⁻¹ • e4Head (x : E4)

theorem chartInvSphere_invariant (x y : S3) (h : rpGroup.projection x = rpGroup.projection y) :
    chartInvSphere x = chartInvSphere y := by
  rcases eq_or_eq_neg_of_rp_projection_eq h with rfl | rfl
  · rfl
  · simp only [chartInvSphere, coe_neg_sphere, e4Head_neg, PiLp.neg_apply, inv_neg, neg_smul,
      smul_neg, neg_neg]

/-- The inverse of the affine chart. -/
def bandChartInv (y : projectiveThreeSpaceLift.{u}.Carrier) : E3 :=
  orbitLift rpGroup chartInvSphere chartInvSphere_invariant (rpDown y)

theorem bandChartInv_rpUp (x : S3) :
    bandChartInv.{u} (rpUp (rpGroup.projection x)) = chartInvSphere x := by
  rw [bandChartInv, rpDown_rpUp]
  rfl

theorem bandFn_bandChartMap (v : E3) : bandFn.{u} (bandChartMap v) = (1 + ‖v‖ ^ 2)⁻¹ := by
  rw [bandChartMap, bandFn_rpUp]
  change ((√(1 + ‖v‖ ^ 2))⁻¹ • e4Join v 1) 3 ^ 2 = _
  rw [PiLp.smul_apply, e4Join_last, smul_eq_mul, mul_one, inv_pow,
    Real.sq_sqrt (by positivity)]

theorem bandChartInv_bandChartMap (v : E3) : bandChartInv.{u} (bandChartMap v) = v := by
  rw [bandChartMap, bandChartInv_rpUp]
  have hc : 0 < (√(1 + ‖v‖ ^ 2))⁻¹ := inv_pos.mpr (Real.sqrt_pos.mpr (by positivity))
  change (((√(1 + ‖v‖ ^ 2))⁻¹ • e4Join v 1) 3)⁻¹ •
    e4Head ((√(1 + ‖v‖ ^ 2))⁻¹ • e4Join v 1) = v
  rw [PiLp.smul_apply, e4Join_last, smul_eq_mul, mul_one, e4Head_smul, e4Head_e4Join, smul_smul,
    inv_mul_cancel₀ hc.ne', one_smul]

theorem bandChartMap_bandChartInv {y : projectiveThreeSpaceLift.{u}.Carrier}
    (hy : 0 < bandFn y) : bandChartMap (bandChartInv y) = y := by
  obtain ⟨x, rfl⟩ := exists_rpUp y
  rw [bandFn_rpUp] at hy
  rw [bandChartInv_rpUp, bandChartMap]
  congr 1
  obtain ⟨w₃, hw₃⟩ : ∃ w₃ : ℝ, (x : E4) 3 = w₃ := ⟨_, rfl⟩
  rw [hw₃] at hy
  have hw : w₃ ≠ 0 := by
    intro h0
    rw [h0] at hy
    norm_num at hy
  have hh := norm_sq_e4Head_sphere x
  rw [hw₃] at hh
  have hci : chartInvSphere x = w₃⁻¹ • e4Head (x : E4) := by rw [chartInvSphere, hw₃]
  have hnorm : ‖chartInvSphere x‖ ^ 2 = (1 - w₃ ^ 2) / w₃ ^ 2 := by
    rw [hci, norm_smul, mul_pow, norm_inv, Real.norm_eq_abs, inv_pow, sq_abs, hh]
    field_simp
  have hsq : √(1 + ‖chartInvSphere x‖ ^ 2) = |w₃|⁻¹ := by
    rw [hnorm, show 1 + (1 - w₃ ^ 2) / w₃ ^ 2 = (|w₃|⁻¹) ^ 2 by
      rw [inv_pow, sq_abs]
      field_simp
      ring]
    exact Real.sqrt_sq (inv_nonneg.mpr (abs_nonneg _))
  have hjoin : e4Join (chartInvSphere x) 1 = w₃⁻¹ • (x : E4) := by
    conv_rhs => rw [← e4Join_head_last (x : E4)]
    rw [smul_e4Join, hci, hw₃, inv_mul_cancel₀ hw]
  have hpt : (chartSphere (chartInvSphere x) : E4) = (|w₃| / w₃) • (x : E4) := by
    change (√(1 + ‖chartInvSphere x‖ ^ 2))⁻¹ • e4Join (chartInvSphere x) 1 = _
    rw [hsq, inv_inv, hjoin, smul_smul, div_eq_mul_inv]
  rcases abs_choice w₃ with ha | ha
  · have : chartSphere (chartInvSphere x) = x := by
      apply Subtype.ext
      rw [hpt, ha, div_self hw, one_smul]
    rw [this]
  · have : chartSphere (chartInvSphere x) = -x := by
      apply Subtype.ext
      rw [hpt, ha, neg_div, div_self hw, neg_one_smul, coe_neg_sphere]
    rw [this, rp_projection_neg]

theorem norm_sq_bandChartInv {y : projectiveThreeSpaceLift.{u}.Carrier} (hy : 0 < bandFn y) :
    ‖bandChartInv y‖ ^ 2 = (1 - bandFn y) / bandFn y := by
  obtain ⟨x, rfl⟩ := exists_rpUp y
  rw [bandFn_rpUp] at hy ⊢
  rw [bandChartInv_rpUp, chartInvSphere, norm_smul, mul_pow, norm_inv, Real.norm_eq_abs, inv_pow,
    sq_abs, norm_sq_e4Head_sphere x]
  field_simp

theorem contMDiff_bandChartMap : ContMDiff 𝓘(ℝ, E3) (𝓡 3) ∞ bandChartMap.{u} := by
  have hg : ContDiff ℝ ∞ (fun v : E3 => (√(1 + ‖v‖ ^ 2))⁻¹ • e4Join v 1) := by
    have hs : ContDiff ℝ ∞ (fun v : E3 => (√(1 + ‖v‖ ^ 2))⁻¹) := by
      refine ContDiff.inv ((contDiff_const.add (contDiff_norm_sq ℝ)).sqrt fun v => ?_) fun v => ?_
      · positivity
      · exact (Real.sqrt_pos.mpr (by positivity)).ne'
    exact hs.smul (contDiff_e4Join.comp (contDiff_id.prodMk contDiff_const))
  exact contMDiff_rpUp_projection.comp (hg.contMDiff.codRestrict_sphere chartSphere_mem)

theorem contMDiffAt_bandChartInv {y : projectiveThreeSpaceLift.{u}.Carrier} (hy : 0 < bandFn y) :
    ContMDiffAt (𝓡 3) 𝓘(ℝ, E3) ∞ bandChartInv y := by
  obtain ⟨x, rfl⟩ := exists_rpUp y
  rw [bandFn_rpUp] at hy
  have hw : (x : E4) 3 ≠ 0 := by
    intro h0
    rw [h0] at hy
    norm_num at hy
  have h1 : ContDiffAt ℝ ∞ (fun w : E4 => (w 3)⁻¹ • e4Head w) (x : E4) :=
    ((EuclideanSpace.proj (3 : Fin 4) : E4 →L[ℝ] ℝ).contDiff.contDiffAt.inv hw).smul
      contDiff_e4Head.contDiffAt
  exact contMDiffAt_orbitLift_rpDown chartInvSphere chartInvSphere_invariant x
    (h1.contMDiffAt.comp x (contMDiff_coe_sphere x))

/-- **The affine chart** as a partial diffeomorphism `ℝ³ → P` onto `{w₃ ≠ 0}`. -/
def bandChart : PartialDiffeomorph 𝓘(ℝ, E3) (𝓡 3) E3 projectiveThreeSpaceLift.{u}.Carrier ∞ where
  toFun := bandChartMap
  invFun := bandChartInv
  source := univ
  target := {y | 0 < bandFn y}
  map_source' := fun v _ => by
    change 0 < bandFn (bandChartMap v)
    rw [bandFn_bandChartMap]
    positivity
  map_target' := fun _ _ => trivial
  left_inv' := fun v _ => bandChartInv_bandChartMap v
  right_inv' := fun _ hy => bandChartMap_bandChartInv hy
  open_source := isOpen_univ
  open_target := isOpen_lt continuous_const continuous_bandFn
  contMDiffOn_toFun := contMDiff_bandChartMap.contMDiffOn
  contMDiffOn_invFun := fun _ hy => (contMDiffAt_bandChartInv hy).contMDiffWithinAt

/-- The affine chart as a ball chart. -/
def bandBallChart : BallChart 3 (𝓡 3) projectiveThreeSpaceLift.{u}.Carrier where
  chart := bandChart
  closedBall_subset_source := fun _ _ => trivial

/-- The unit ball of the affine chart is the polar cap `{w₃² > ½}`. -/
theorem bandChart_image_ball :
    (bandChart.{u} : E3 → projectiveThreeSpaceLift.{u}.Carrier) '' ball 0 1 =
      {y | 1 / 2 < bandFn y} := by
  ext y
  constructor
  · rintro ⟨v, hv, rfl⟩
    change 1 / 2 < bandFn (bandChartMap v)
    rw [bandFn_bandChartMap]
    rw [mem_ball_zero_iff] at hv
    have h1 : ‖v‖ ^ 2 < 1 := by nlinarith [norm_nonneg v]
    rw [lt_inv_comm₀ (by norm_num) (by positivity)]
    linarith
  · intro hy
    change 1 / 2 < bandFn y at hy
    have hpos : 0 < bandFn y := by linarith
    refine ⟨bandChartInv y, ?_, bandChartMap_bandChartInv hpos⟩
    rw [mem_ball_zero_iff]
    have h := norm_sq_bandChartInv hpos
    have h2 : ‖bandChartInv y‖ ^ 2 < 1 := by
      rw [h, div_lt_one hpos]
      linarith
    nlinarith [norm_nonneg (bandChartInv y)]

/-- The unit sphere of the affine chart is the level `{w₃² = ½}`. -/
theorem bandChart_image_sphere :
    (bandChart.{u} : E3 → projectiveThreeSpaceLift.{u}.Carrier) '' sphere 0 1 =
      {y | bandFn y = 1 / 2} := by
  ext y
  constructor
  · rintro ⟨v, hv, rfl⟩
    change bandFn (bandChartMap v) = 1 / 2
    rw [bandFn_bandChartMap, mem_sphere_zero_iff_norm.mp hv]
    norm_num
  · intro hy
    change bandFn y = 1 / 2 at hy
    have hpos : 0 < bandFn y := by rw [hy]; norm_num
    refine ⟨bandChartInv y, ?_, bandChartMap_bandChartInv hpos⟩
    rw [mem_sphere_zero_iff_norm]
    have h := norm_sq_bandChartInv hpos
    rw [hy] at h
    have h1 : ‖bandChartInv y‖ ^ 2 = 1 := by rw [h]; norm_num
    exact (pow_eq_one_iff_of_nonneg (norm_nonneg _) two_ne_zero).mp h1

/-- **An oriented ball chart of `ℝP³` agreeing with the affine chart up to `x ↦ -x`.** -/
theorem exists_orientedBallChart_bandChartMap :
    ∃ c : OrientedBallChart projectiveThreeSpaceLift.{u}.toClosedOrientedManifold,
      (∀ x, c.chart x = bandChartMap x) ∨ (∀ x, c.chart x = bandChartMap (-x)) := by
  rcases BallChart.exists_oriented
      (M := projectiveThreeSpaceLift.{u}.toClosedOrientedManifold) bandBallChart with
    ⟨c, hc⟩ | ⟨c, hc⟩
  · exact ⟨c, Or.inl hc⟩
  · let M := projectiveThreeSpaceLift.{u}.toClosedOrientedManifold
    let d : OrientedBallChart M :=
      { toBallChart := c.reflect.toBallChart
        preserves_orientation := by
          intro x hx
          have h := c.reflect.preserves_orientation x hx
          have ho : M.opposite.opposite.orientation = M.orientation :=
            ManifoldOrientation.opposite_opposite _
          rw [ho] at h
          exact h }
    exact ⟨d, Or.inr fun x => hc (-x)⟩

theorem image_comp_neg_of_symm {α : Type*} (g : E3 → α) {S : Set E3}
    (hS : ∀ x, -x ∈ S ↔ x ∈ S) : (fun x => g (-x)) '' S = g '' S := by
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact ⟨-x, (hS x).mpr hx, rfl⟩
  · rintro ⟨x, hx, rfl⟩
    refine ⟨-x, (hS x).mpr hx, ?_⟩
    change g (-(-x)) = g x
    rw [neg_neg]

theorem orientedBallChart_image_eq_of_bandChartMap
    (c : OrientedBallChart projectiveThreeSpaceLift.{u}.toClosedOrientedManifold)
    (hc : (∀ x, c.chart x = bandChartMap x) ∨ (∀ x, c.chart x = bandChartMap (-x)))
    {S : Set E3} (hS : ∀ x, -x ∈ S ↔ x ∈ S) :
    c.chart '' S = (bandChart.{u} : E3 → projectiveThreeSpaceLift.{u}.Carrier) '' S := by
  rcases hc with hc | hc
  · exact image_congr fun x _ => hc x
  · rw [image_congr fun x _ => hc x]
    exact image_comp_neg_of_symm _ hS

/-- **An oriented ball chart of `ℝP³` whose unit ball is the polar cap `{w₃² > ½}`** and whose
unit sphere is the level `{w₃² = ½}`. -/
theorem exists_orientedBallChart_image_ball_eq :
    ∃ c : OrientedBallChart projectiveThreeSpaceLift.{u}.toClosedOrientedManifold,
      c.chart '' ball (0 : E3) 1 = {y | 1 / 2 < bandFn.{u} y} ∧
        c.chart '' sphere (0 : E3) 1 = {y | bandFn.{u} y = 1 / 2} := by
  obtain ⟨c, hc⟩ := exists_orientedBallChart_bandChartMap.{u}
  refine ⟨c, ?_, ?_⟩
  · rw [orientedBallChart_image_eq_of_bandChartMap c hc fun x => by
      rw [mem_ball_zero_iff, mem_ball_zero_iff, norm_neg]]
    exact bandChart_image_ball
  · rw [orientedBallChart_image_eq_of_bandChartMap c hc fun x => by
      rw [mem_sphere_zero_iff_norm, mem_sphere_zero_iff_norm, norm_neg]]
    exact bandChart_image_sphere

end DifferentialGeometry.Geometry.Collapse.ZeroModel.Projective
