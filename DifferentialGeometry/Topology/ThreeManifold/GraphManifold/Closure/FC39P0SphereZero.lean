import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.FC39P0Base
import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.Inhabitants.CycleBalls
import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.SphereProduct

/-!
# FC39 producer, packet P0 (gate 1), §7.1: the S³ zero kind (two balls, global `h₁ − .4`)

Task-47 draft §7.1 / §7.9 rows "zero finite pieces / models / disjoint", "zero global
functions", for the S³ inhabitant (disposition D10). The S³ model is the tree's
`NoCuts.carrier standardThreeSphereLift.{0}` with the stereographic chart `cycleBallAmbient` of
the cycle inhabitants (pole `e₀`): the stereographic radius `r = ‖y‖` replaces the draft's latitude
`t = 3q₀` (same decomposition type, stated as a deviation in the gate-1 report):

* `Z₋ = sphereInnerBall`: the stereographic ball `‖y‖ ≤ 1/2`, i.e. the cap `q₀ ≤ −15/17`;
* `Z₊ = cycleBallPiece true`: the antipodal radius-one ball, i.e. the cap `q₀ ≥ 3/5`
  (the outer ball of the compiled two-ball cycle, whose handles and rims live in `1 ≤ ‖y‖ ≤ 4`).

The global shifted defining functions are linear in the height `q₀ = ⟪q, e₀⟫`:
`F₋ = q₀ + 15/17`, `F₊ = 3/5 − q₀`; smooth on the whole carrier, every zero regular,
`pieceBoundary = {F = 0}` and `range = {F ≤ 0}` (Q7). Result: `sphereZeroDomains`. The empty cusp
cores of the closed S³ (`sphereCuspCores`) complete the zero / cusp rows (the draft: cusp count
zero, not a validation of the boundary geometry).
-/

set_option autoImplicit false

noncomputable section

open Set Function Metric
open DifferentialGeometry DifferentialGeometry.Topology GC.Endpoint GC.Seifert GC.GraphManifold
open DifferentialGeometry.Topology.Manifold Manifold
open scoped Manifold ContDiff Topology InnerProductSpace

namespace GC.GraphManifold.Assembly.FC39P0

local instance sphereFourDim_FC39P0 :
    Fact (Module.finrank ℝ (EuclideanSpace ℝ (Fin 4)) = 3 + 1) := ⟨by simp⟩

local instance ballCharts_FC39P0 : ChartedSpace (EuclideanHalfSpace 3) (ClosedCell 3) :=
  DifferentialGeometry.Topology.Handle.closedCellChartedSpaceSucc 2

local instance ballSmooth_FC39P0 : IsManifold (𝓡∂ 3) ∞ (ClosedCell 3) :=
  DifferentialGeometry.Topology.Handle.closedCellIsManifold 2

local instance ballConnected_FC39P0 : ConnectedSpace (ClosedCell 3) :=
  closedCell_three_connectedSpace

/-- The carrier of the S³ inhabitants. -/
abbrev sphereW : CompactCarrier.{0} :=
  NoCuts.carrier standardThreeSphereLift.{0}

/-- The pole `e₀` of the stereographic chart. -/
abbrev spherePole : EuclideanSpace ℝ (Fin 4) :=
  (cycleBallPole : EuclideanSpace ℝ (Fin 4))

/-- The point of the unit sphere of `ℝ⁴` underlying a point of the carrier. -/
def spherePoint (x : sphereW.Carrier) : sphere (0 : EuclideanSpace ℝ (Fin 4)) 1 :=
  x.down

theorem spherePoint_ambient (b : Bool) (y : EuclideanSpace ℝ (Fin 3)) :
    spherePoint (cycleBallAmbient b y) =
      if b then -(stereographic' 3 cycleBallPole).symm y else
        (stereographic' 3 cycleBallPole).symm y :=
  cycleBallAmbient_apply b y

theorem spherePoint_injective : Injective spherePoint := fun _ _ h => ULift.ext h

/-- The height `q₀ = ⟪q, e₀⟫` on S³. -/
def sphereHeight (x : sphereW.Carrier) : ℝ :=
  ⟪(spherePoint x : EuclideanSpace ℝ (Fin 4)), spherePole⟫_ℝ

/-- The height of the inverse stereographic projection. -/
theorem inner_stereographic_symm (y : EuclideanSpace ℝ (Fin 3)) :
    ⟪((stereographic' 3 cycleBallPole).symm y : EuclideanSpace ℝ (Fin 4)), spherePole⟫_ℝ =
      (‖y‖ ^ 2 - 4) / (‖y‖ ^ 2 + 4) := by
  rw [stereographic'_symm_apply]
  set U : (ℝ ∙ spherePole)ᗮ ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin 3) :=
    (OrthonormalBasis.fromOrthogonalSpanSingleton 3
      (ne_zero_of_mem_unit_sphere cycleBallPole)).repr
  have hperp : ⟪((U.symm y : (ℝ ∙ spherePole)ᗮ) : EuclideanSpace ℝ (Fin 4)), spherePole⟫_ℝ = 0 :=
    Submodule.inner_left_of_mem_orthogonal (Submodule.mem_span_singleton_self _) (U.symm y).2
  have hnorm : ‖((U.symm y : (ℝ ∙ spherePole)ᗮ) : EuclideanSpace ℝ (Fin 4))‖ = ‖y‖ := by
    rw [Submodule.norm_coe, LinearIsometryEquiv.norm_map]
  have hpp : ⟪spherePole, spherePole⟫_ℝ = 1 := by
    rw [real_inner_self_eq_norm_sq, norm_eq_of_mem_sphere cycleBallPole]
    norm_num
  simp only [hnorm, inner_add_left, inner_smul_left, hperp, hpp, RCLike.conj_to_real]
  have hpos : (0 : ℝ) < ‖y‖ ^ 2 + 4 := by positivity
  field_simp
  ring

theorem sphereHeight_ambient_false (y : EuclideanSpace ℝ (Fin 3)) :
    sphereHeight (cycleBallAmbient false y) = (‖y‖ ^ 2 - 4) / (‖y‖ ^ 2 + 4) := by
  unfold sphereHeight
  rw [spherePoint_ambient]
  exact inner_stereographic_symm y

theorem sphereHeight_ambient_true (y : EuclideanSpace ℝ (Fin 3)) :
    sphereHeight (cycleBallAmbient true y) = -((‖y‖ ^ 2 - 4) / (‖y‖ ^ 2 + 4)) := by
  unfold sphereHeight
  rw [spherePoint_ambient]
  simp only [ite_true, coe_neg_sphere, inner_neg_left]
  rw [inner_stereographic_symm]

/-- Every point of S³ other than the pole is in the image of the chart `cycleBallAmbient false`.
-/
theorem exists_ambient_false {x : sphereW.Carrier} (hx : spherePoint x ≠ cycleBallPole) :
    ∃ y, cycleBallAmbient false y = x := by
  refine ⟨stereographic' 3 cycleBallPole (spherePoint x), ?_⟩
  apply spherePoint_injective
  rw [spherePoint_ambient]
  simp only [Bool.false_eq_true, ite_false]
  exact (stereographic' 3 cycleBallPole).left_inv (by simpa using hx)

/-- Every point of S³ other than the antipode of the pole is in the image of
`cycleBallAmbient true`. -/
theorem exists_ambient_true {x : sphereW.Carrier} (hx : spherePoint x ≠ -cycleBallPole) :
    ∃ y, cycleBallAmbient true y = x := by
  have hx' : -spherePoint x ≠ cycleBallPole := by
    intro h
    exact hx (by rw [← h, neg_neg])
  refine ⟨stereographic' 3 cycleBallPole (-spherePoint x), ?_⟩
  apply spherePoint_injective
  rw [spherePoint_ambient]
  simp only [ite_true]
  rw [(stereographic' 3 cycleBallPole).left_inv (by simpa using hx'), neg_neg]

theorem sphereHeight_le_one (x : sphereW.Carrier) : |sphereHeight x| ≤ 1 := by
  unfold sphereHeight
  have h := abs_real_inner_le_norm (spherePoint x : EuclideanSpace ℝ (Fin 4)) spherePole
  rwa [norm_eq_of_mem_sphere (spherePoint x), norm_eq_of_mem_sphere cycleBallPole, one_mul] at h

theorem sphereHeight_eq_one_iff {x : sphereW.Carrier} :
    sphereHeight x = 1 ↔ spherePoint x = cycleBallPole := by
  constructor
  · intro h
    apply Subtype.ext
    have h1 := inner_eq_norm_mul_iff_real.1 (show ⟪(spherePoint x : EuclideanSpace ℝ (Fin 4)),
        spherePole⟫_ℝ = ‖(spherePoint x : EuclideanSpace ℝ (Fin 4))‖ * ‖spherePole‖ by
      rw [norm_eq_of_mem_sphere (spherePoint x), norm_eq_of_mem_sphere cycleBallPole, one_mul]
      exact h)
    rw [norm_eq_of_mem_sphere (spherePoint x), norm_eq_of_mem_sphere cycleBallPole, one_smul,
      one_smul] at h1
    exact h1
  · intro h
    unfold sphereHeight
    rw [h, real_inner_self_eq_norm_sq, norm_eq_of_mem_sphere cycleBallPole]
    norm_num

theorem sphereHeight_eq_neg_one_iff {x : sphereW.Carrier} :
    sphereHeight x = -1 ↔ spherePoint x = -cycleBallPole := by
  constructor
  · intro h
    have hneg : sphereHeight (ULift.up (-spherePoint x)) = 1 := by
      change ⟪((-spherePoint x : sphere (0 : EuclideanSpace ℝ (Fin 4)) 1) :
        EuclideanSpace ℝ (Fin 4)), spherePole⟫_ℝ = 1
      rw [coe_neg_sphere, inner_neg_left]
      unfold sphereHeight at h
      linarith
    have := (sphereHeight_eq_one_iff (x := ULift.up (-spherePoint x))).1 hneg
    change -spherePoint x = cycleBallPole at this
    rw [← this, neg_neg]
  · intro h
    unfold sphereHeight
    rw [h, coe_neg_sphere, inner_neg_left, real_inner_self_eq_norm_sq,
      norm_eq_of_mem_sphere cycleBallPole]
    norm_num

/-! ## The height is smooth and regular away from the poles -/

/-- The lift diffeomorphism, typed on the unit sphere. -/
abbrev sphereLift : sphere (0 : EuclideanSpace ℝ (Fin 4)) 1 ≃ₘ⟮𝓡 3, 𝓡 3⟯ sphereW.Carrier :=
  standardThreeSphereLiftDiffeomorph.{0}

/-- The height on the unit sphere of `ℝ⁴`. -/
def sphereHeight₀ (q : sphere (0 : EuclideanSpace ℝ (Fin 4)) 1) : ℝ :=
  ⟪(q : EuclideanSpace ℝ (Fin 4)), spherePole⟫_ℝ

theorem sphereHeight_eq_comp : sphereHeight = sphereHeight₀ ∘ sphereLift.symm :=
  rfl

theorem sphereHeight₀_eq : sphereHeight₀ = (innerSL ℝ spherePole) ∘
    ((↑) : sphere (0 : EuclideanSpace ℝ (Fin 4)) 1 → EuclideanSpace ℝ (Fin 4)) := by
  funext q
  exact real_inner_comm _ _

theorem contMDiff_sphereHeight₀ : ContMDiff (𝓡 3) 𝓘(ℝ, ℝ) ∞ sphereHeight₀ := by
  rw [sphereHeight₀_eq]
  exact (innerSL ℝ spherePole).contDiff.contMDiff.comp contMDiff_coe_sphere

theorem contMDiff_sphereHeight : ContMDiff sphereW.model 𝓘(ℝ, ℝ) ∞ sphereHeight := by
  rw [sphereHeight_eq_comp]
  exact contMDiff_sphereHeight₀.comp sphereLift.symm.contMDiff

theorem mfderiv_sphereHeight_ne_zero {x : sphereW.Carrier} (hx : |sphereHeight x| < 1) :
    mfderiv sphereW.model 𝓘(ℝ, ℝ) sphereHeight x ≠ 0 := by
  set q : sphere (0 : EuclideanSpace ℝ (Fin 4)) 1 := sphereLift.symm x with hq
  have hcomp : mfderiv sphereW.model 𝓘(ℝ, ℝ) sphereHeight x =
      (mfderiv (𝓡 3) 𝓘(ℝ, ℝ) sphereHeight₀ q).comp
        (mfderiv sphereW.model (𝓡 3) sphereLift.symm x) := by
    rw [sphereHeight_eq_comp]
    exact mfderiv_comp x (contMDiff_sphereHeight₀.mdifferentiableAt (by simp))
      (sphereLift.symm.contMDiff.mdifferentiableAt (by simp))
  have hg : mfderiv (𝓡 3) 𝓘(ℝ, ℝ) sphereHeight₀ q =
      (innerSL ℝ spherePole).comp
        (mfderiv (𝓡 3) 𝓘(ℝ, EuclideanSpace ℝ (Fin 4))
          ((↑) : sphere (0 : EuclideanSpace ℝ (Fin 4)) 1 → EuclideanSpace ℝ (Fin 4)) q) := by
    have hcoe := (contMDiff_coe_sphere (n := 3) (m := ∞) q).mdifferentiableAt
      (by simp) |>.hasMFDerivAt
    have hlin : HasMFDerivAt 𝓘(ℝ, EuclideanSpace ℝ (Fin 4)) 𝓘(ℝ, ℝ) (innerSL ℝ spherePole)
        (q : EuclideanSpace ℝ (Fin 4)) (innerSL ℝ spherePole) :=
      (innerSL ℝ spherePole).hasFDerivAt.hasMFDerivAt
    rw [sphereHeight₀_eq]
    exact (hlin.comp q hcoe).mfderiv
  have hsx : sphereHeight₀ q = sphereHeight x := rfl
  set s := sphereHeight₀ q with hs
  set u : EuclideanSpace ℝ (Fin 4) := spherePole - s • (q : EuclideanSpace ℝ (Fin 4)) with hu_def
  have hu : u ∈ (ℝ ∙ (q : EuclideanSpace ℝ (Fin 4)))ᗮ := by
    rw [Submodule.mem_orthogonal_singleton_iff_inner_right, hu_def, inner_sub_right,
      inner_smul_right, real_inner_self_eq_norm_sq, norm_eq_of_mem_sphere q, hs, sphereHeight₀]
    ring
  rw [← range_mvfderiv_subtypeVal (n := 3) q] at hu
  obtain ⟨w, hw⟩ := LinearMap.mem_range.1 hu
  rw [ContinuousLinearMap.coe_coe] at hw
  change mfderiv (𝓡 3) 𝓘(ℝ, EuclideanSpace ℝ (Fin 4))
    ((↑) : sphere (0 : EuclideanSpace ℝ (Fin 4)) 1 → EuclideanSpace ℝ (Fin 4)) q w = u at hw
  obtain ⟨v, hv⟩ := (sphereLift.symm.mfderivToContinuousLinearEquiv (by simp) x).surjective w
  change mfderiv sphereW.model (𝓡 3) sphereLift.symm x v = w at hv
  intro h0
  have hval : mfderiv sphereW.model 𝓘(ℝ, ℝ) sphereHeight x v = 0 := by
    rw [h0]
    rfl
  rw [hcomp, hg] at hval
  change (innerSL ℝ spherePole) (mfderiv (𝓡 3) 𝓘(ℝ, EuclideanSpace ℝ (Fin 4))
    ((↑) : sphere (0 : EuclideanSpace ℝ (Fin 4)) 1 → EuclideanSpace ℝ (Fin 4)) q
      (mfderiv sphereW.model (𝓡 3) sphereLift.symm x v)) = 0 at hval
  rw [hv, hw, innerSL_apply_apply, hu_def, inner_sub_right, inner_smul_right,
    real_inner_self_eq_norm_sq, norm_eq_of_mem_sphere cycleBallPole, real_inner_comm] at hval
  change 1 ^ 2 - s * s = 0 at hval
  have : s ^ 2 < 1 := by
    rw [hsx]
    nlinarith [abs_lt.1 hx]
  nlinarith

/-! ## The two zero pieces -/

theorem ambient_source_ball (r : ℝ) :
    closedBall (0 : EuclideanSpace ℝ (Fin 3)) r ⊆ (cycleBallAmbient false).source := by
  rw [cycleBallAmbient_source]
  exact subset_univ _

/-- `Z₋`: the stereographic ball of radius `1/2` (the cap `q₀ ≤ −15/17`). -/
def sphereInnerBall : PieceEmbedding sphereW where
  Piece := ClosedCell 3
  map := closedCellChartMap (cycleBallAmbient false) 0 (1 / 2)
  smooth := contMDiff_closedCellChartMap _ 0 (by norm_num) (ambient_source_ball _)
  mfderiv_bijective x := by
    have hi := injective_mfderiv_closedCellChartMap (cycleBallAmbient false) 0
      (r := 1 / 2) (by norm_num) (ambient_source_ball _) x
    exact ⟨hi, LinearMap.injective_iff_surjective.mp hi⟩
  injective := by
    intro x y hxy
    have h := (cycleBallAmbient false).injOn (by rw [cycleBallAmbient_source]; exact mem_univ _)
      (by rw [cycleBallAmbient_source]; exact mem_univ _) hxy
    simp only [zero_add] at h
    exact Subtype.ext (smul_right_injective _ (by norm_num : (1 / 2 : ℝ) ≠ 0) h)

theorem sphereInnerBall_apply (x : ClosedCell 3) :
    sphereInnerBall.map x = cycleBallAmbient false ((1 / 2 : ℝ) • x.val) := by
  change cycleBallAmbient false (0 + (1 / 2 : ℝ) • x.val) = _
  rw [zero_add]

theorem sphereHeight_innerBall (x : ClosedCell 3) :
    sphereHeight (sphereInnerBall.map x) = (‖x.val‖ ^ 2 / 4 - 4) / (‖x.val‖ ^ 2 / 4 + 4) := by
  rw [sphereInnerBall_apply, sphereHeight_ambient_false, norm_smul, Real.norm_eq_abs,
    abs_of_pos (by norm_num : (0 : ℝ) < 1 / 2)]
  ring_nf

theorem sphereHeight_outerBall (x : ClosedCell 3) :
    sphereHeight ((cycleBallPiece true).map x) = -((‖x.val‖ ^ 2 - 4) / (‖x.val‖ ^ 2 + 4)) :=
  sphereHeight_ambient_true x.val

/-- The model boundary of a closed-cell piece is the unit sphere. -/
theorem closedCell_isBoundaryPoint_iff {x : ClosedCell 3} :
    (𝓡∂ 3).IsBoundaryPoint x ↔ ‖x.val‖ = 1 := by
  change x ∈ (𝓡∂ 3).boundary (ClosedCell 3) ↔ _
  rw [closedCell_boundary_eq_sphere]
  rfl

/-- The stereographic height formula `(t − 4)/(t + 4)` against a level `c < 1`. -/
theorem stereoHeight_le_iff {t c : ℝ} (ht : 0 ≤ t) (hc : c < 1) :
    (t - 4) / (t + 4) ≤ c ↔ t ≤ 4 * (1 + c) / (1 - c) := by
  have hpos : (0 : ℝ) < t + 4 := by linarith
  have h1c : (0 : ℝ) < 1 - c := by linarith
  rw [div_le_iff₀ hpos, le_div_iff₀ h1c]
  constructor <;> intro h <;> nlinarith

theorem stereoHeight_eq_iff {t c : ℝ} (ht : 0 ≤ t) (hc : c < 1) :
    (t - 4) / (t + 4) = c ↔ t = 4 * (1 + c) / (1 - c) := by
  have hpos : (0 : ℝ) < t + 4 := by linarith
  have h1c : (0 : ℝ) < 1 - c := by linarith
  rw [div_eq_iff hpos.ne', eq_div_iff h1c.ne']
  constructor <;> intro h <;> nlinarith

theorem sphereHeight_pole : sphereHeight (ULift.up cycleBallPole) = 1 :=
  sphereHeight_eq_one_iff.2 rfl

theorem sphereHeight_antipole : sphereHeight (ULift.up (-cycleBallPole)) = -1 :=
  sphereHeight_eq_neg_one_iff.2 rfl

/-- The model boundary image of the inner ball is the level `q₀ = −15/17`. -/
theorem pieceBoundary_innerBall :
    pieceBoundary sphereInnerBall = {x | sphereHeight x + 15 / 17 = 0} := by
  ext x
  constructor
  · rintro ⟨v, hv, rfl⟩
    have h1 : ‖v.val‖ = 1 := closedCell_isBoundaryPoint_iff.1 hv
    change sphereHeight (sphereInnerBall.map v) + 15 / 17 = 0
    rw [show sphereHeight (sphereInnerBall.map v) = _ from sphereHeight_innerBall v, h1]
    norm_num
  · intro hx
    change sphereHeight x + 15 / 17 = 0 at hx
    have hne : spherePoint x ≠ cycleBallPole := by
      intro h
      rw [sphereHeight_eq_one_iff.2 h] at hx
      norm_num at hx
    obtain ⟨y, rfl⟩ := exists_ambient_false hne
    rw [sphereHeight_ambient_false] at hx
    have hy := (stereoHeight_eq_iff (sq_nonneg ‖y‖) (by norm_num : (-15 / 17 : ℝ) < 1)).1
      (by linarith)
    have hy' : ‖y‖ = 1 / 2 := by
      have h4 : ‖y‖ ^ 2 = (1 / 2) ^ 2 := by rw [hy]; norm_num
      exact (pow_left_inj₀ (norm_nonneg y) (by norm_num) two_ne_zero).1 h4
    have hv : ‖(2 : ℝ) • y‖ ≤ 1 := by
      rw [norm_smul, hy']
      norm_num
    refine ⟨⟨(2 : ℝ) • y, hv⟩, closedCell_isBoundaryPoint_iff.2 ?_, ?_⟩
    · change ‖(2 : ℝ) • y‖ = 1
      rw [norm_smul, hy']
      norm_num
    · rw [sphereInnerBall_apply]
      change cycleBallAmbient false ((1 / 2 : ℝ) • (2 : ℝ) • y) = _
      rw [smul_smul]
      norm_num

/-- The inner ball is the sublevel `q₀ ≤ −15/17`. -/
theorem range_innerBall :
    range sphereInnerBall.map = {x | sphereHeight x + 15 / 17 ≤ 0} := by
  ext x
  constructor
  · rintro ⟨v, rfl⟩
    change sphereHeight (sphereInnerBall.map v) + 15 / 17 ≤ 0
    rw [show sphereHeight (sphereInnerBall.map v) = _ from sphereHeight_innerBall v]
    have hv : ‖v.val‖ ^ 2 / 4 ≤ 1 / 4 := by
      have := v.property
      have h0 := norm_nonneg v.val
      nlinarith
    have := (stereoHeight_le_iff (by positivity : (0 : ℝ) ≤ ‖v.val‖ ^ 2 / 4)
      (by norm_num : (-15 / 17 : ℝ) < 1)).2 (by norm_num; linarith)
    linarith
  · intro hx
    change sphereHeight x + 15 / 17 ≤ 0 at hx
    have hne : spherePoint x ≠ cycleBallPole := by
      intro h
      rw [sphereHeight_eq_one_iff.2 h] at hx
      norm_num at hx
    obtain ⟨y, rfl⟩ := exists_ambient_false hne
    rw [sphereHeight_ambient_false] at hx
    have hy := (stereoHeight_le_iff (sq_nonneg ‖y‖) (by norm_num : (-15 / 17 : ℝ) < 1)).1
      (by linarith)
    have hy' : ‖y‖ ≤ 1 / 2 := by
      have h4 : ‖y‖ ^ 2 ≤ (1 / 2) ^ 2 := by rw [show (1 / 2 : ℝ) ^ 2 = 1 / 4 by norm_num]; linarith
      exact (pow_le_pow_iff_left₀ (norm_nonneg y) (by norm_num) two_ne_zero).1 h4
    have hv : ‖(2 : ℝ) • y‖ ≤ 1 := by
      rw [norm_smul]
      norm_num
      linarith
    refine ⟨⟨(2 : ℝ) • y, hv⟩, ?_⟩
    rw [sphereInnerBall_apply]
    change cycleBallAmbient false ((1 / 2 : ℝ) • (2 : ℝ) • y) = _
    rw [smul_smul]
    norm_num

/-- The model boundary image of the outer ball is the level `q₀ = 3/5`. -/
theorem pieceBoundary_outerBall :
    pieceBoundary (cycleBallPiece true) = {x | 3 / 5 - sphereHeight x = 0} := by
  ext x
  constructor
  · rintro ⟨v, hv, rfl⟩
    have h1 : ‖v.val‖ = 1 := closedCell_isBoundaryPoint_iff.1 hv
    change 3 / 5 - sphereHeight ((cycleBallPiece true).map v) = 0
    rw [show sphereHeight ((cycleBallPiece true).map v) = _ from sphereHeight_outerBall v, h1]
    norm_num
  · intro hx
    change 3 / 5 - sphereHeight x = 0 at hx
    have hne : spherePoint x ≠ -cycleBallPole := by
      intro h
      rw [sphereHeight_eq_neg_one_iff.2 h] at hx
      norm_num at hx
    obtain ⟨y, rfl⟩ := exists_ambient_true hne
    rw [sphereHeight_ambient_true] at hx
    have hy := (stereoHeight_eq_iff (sq_nonneg ‖y‖) (by norm_num : (-3 / 5 : ℝ) < 1)).1
      (by linarith)
    have hy' : ‖y‖ = 1 := by
      have h4 : ‖y‖ ^ 2 = 1 ^ 2 := by rw [hy]; norm_num
      exact (pow_left_inj₀ (norm_nonneg y) (by norm_num) two_ne_zero).1 h4
    exact ⟨⟨y, hy'.le⟩, closedCell_isBoundaryPoint_iff.2 hy', rfl⟩

/-- The outer ball is the superlevel `q₀ ≥ 3/5`. -/
theorem range_outerBall :
    range (cycleBallPiece true).map = {x | 3 / 5 - sphereHeight x ≤ 0} := by
  ext x
  constructor
  · rintro ⟨v, rfl⟩
    change 3 / 5 - sphereHeight ((cycleBallPiece true).map v) ≤ 0
    rw [show sphereHeight ((cycleBallPiece true).map v) = _ from sphereHeight_outerBall v]
    have hv : ‖v.val‖ ^ 2 ≤ 1 := by
      have := v.property
      have h0 := norm_nonneg v.val
      nlinarith
    have := (stereoHeight_le_iff (sq_nonneg ‖v.val‖) (by norm_num : (-3 / 5 : ℝ) < 1)).2
      (by rw [show (4 * (1 + -3 / 5) / (1 - -3 / 5) : ℝ) = 1 by norm_num]; exact hv)
    linarith
  · intro hx
    change 3 / 5 - sphereHeight x ≤ 0 at hx
    have hne : spherePoint x ≠ -cycleBallPole := by
      intro h
      rw [sphereHeight_eq_neg_one_iff.2 h] at hx
      norm_num at hx
    obtain ⟨y, rfl⟩ := exists_ambient_true hne
    rw [sphereHeight_ambient_true] at hx
    have hy := (stereoHeight_le_iff (sq_nonneg ‖y‖) (by norm_num : (-3 / 5 : ℝ) < 1)).1
      (by linarith)
    have hy' : ‖y‖ ≤ 1 := by
      have h4 : ‖y‖ ^ 2 ≤ 1 ^ 2 := by norm_num at hy ⊢; linarith
      exact (pow_le_pow_iff_left₀ (norm_nonneg y) (by norm_num) two_ne_zero).1 h4
    exact ⟨⟨y, hy'⟩, rfl⟩

/-! ## The zero domains of the S³ inhabitant -/

/-- The two zero pieces `Z₋`, `Z₊`. -/
def sphereZeroPiece : Fin 2 → PieceEmbedding sphereW
  | 0 => sphereInnerBall
  | 1 => cycleBallPiece true

/-- The global shifted defining functions `F₋ = q₀ + 15/17`, `F₊ = 3/5 − q₀`. -/
def sphereZeroRatio : Fin 2 → sphereW.Carrier → ℝ
  | 0 => fun x => sphereHeight x + 15 / 17
  | 1 => fun x => 3 / 5 - sphereHeight x

/-- The two ball models. -/
def sphereZeroModel : (i : Fin 2) →
    ZeroModel (sphereZeroPiece i) ⊕ {C : ClosedZeroPiece sphereW // C.piece = sphereZeroPiece i}
  | 0 => .inl (.ball (Diffeomorph.refl (𝓡∂ 3) (ClosedCell 3) ∞))
  | 1 => .inl (.ball (cycleBallModel true))

theorem sphereZeroRatio_smooth (i : Fin 2) :
    ContMDiff sphereW.model 𝓘(ℝ, ℝ) ∞ (sphereZeroRatio i) := by
  fin_cases i
  · exact contMDiff_sphereHeight.add contMDiff_const
  · exact contMDiff_const.sub contMDiff_sphereHeight

theorem sphereZeroRatio_mfderiv (i : Fin 2) (x : sphereW.Carrier) (hx : |sphereHeight x| < 1) :
    mfderiv sphereW.model 𝓘(ℝ, ℝ) (sphereZeroRatio i) x ≠ 0 := by
  have hS := (contMDiff_sphereHeight x).mdifferentiableAt (by simp) |>.hasMFDerivAt
  have hne := mfderiv_sphereHeight_ne_zero hx
  fin_cases i
  · have hg : HasMFDerivAt 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) (fun t : ℝ => t + 15 / 17) (sphereHeight x)
        (ContinuousLinearMap.id ℝ ℝ) :=
      ((hasFDerivAt_id (sphereHeight x)).add_const (15 / 17 : ℝ)).hasMFDerivAt
    have hd := (hg.comp x hS).mfderiv
    change mfderiv sphereW.model 𝓘(ℝ, ℝ) ((fun t : ℝ => t + 15 / 17) ∘ sphereHeight) x ≠ 0
    rw [hd]
    exact hne
  · have hg : HasMFDerivAt 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) (fun t : ℝ => 3 / 5 - t) (sphereHeight x)
        (-ContinuousLinearMap.id ℝ ℝ) :=
      ((hasFDerivAt_id (sphereHeight x)).const_sub (3 / 5 : ℝ)).hasMFDerivAt
    have hd := (hg.comp x hS).mfderiv
    change mfderiv sphereW.model 𝓘(ℝ, ℝ) ((fun t : ℝ => 3 / 5 - t) ∘ sphereHeight) x ≠ 0
    rw [hd]
    intro h0
    apply hne
    ext v
    have h2 : -(mfderiv sphereW.model 𝓘(ℝ, ℝ) sphereHeight x v) = 0 :=
      congrArg (fun L : TangentSpace sphereW.model x →L[ℝ] ℝ => L v) h0
    exact neg_eq_zero.1 h2

theorem sphereZeroRatio_zero (i : Fin 2) (x : sphereW.Carrier) (hx : sphereZeroRatio i x = 0) :
    |sphereHeight x| < 1 := by
  fin_cases i
  · change sphereHeight x + 15 / 17 = 0 at hx
    rw [abs_lt]
    constructor <;> linarith
  · change 3 / 5 - sphereHeight x = 0 at hx
    rw [abs_lt]
    constructor <;> linarith

theorem sphereZeroPiece_boundary (i : Fin 2) :
    pieceBoundary (sphereZeroPiece i) = {x | sphereZeroRatio i x = 0} := by
  fin_cases i
  · exact pieceBoundary_innerBall
  · exact pieceBoundary_outerBall

theorem sphereZeroPiece_range (i : Fin 2) :
    range (sphereZeroPiece i).map = {x | sphereZeroRatio i x ≤ 0} := by
  fin_cases i
  · exact range_innerBall
  · exact range_outerBall

/-- **The zero domains of the S³ inhabitant** (§5.1): two balls with the global functions. -/
def sphereZeroDomains : ZeroDomains sphereW where
  count := 2
  piece := sphereZeroPiece
  disjoint := by
    intro i j hij
    rw [Set.disjoint_left]
    intro x hi hj
    rw [sphereZeroPiece_range] at hi hj
    fin_cases i <;> fin_cases j
    · exact hij rfl
    · change sphereHeight x + 15 / 17 ≤ 0 at hi
      change 3 / 5 - sphereHeight x ≤ 0 at hj
      linarith
    · change 3 / 5 - sphereHeight x ≤ 0 at hi
      change sphereHeight x + 15 / 17 ≤ 0 at hj
      linarith
    · exact hij rfl
  ratio := sphereZeroRatio
  near _ := ⊤
  near_interior _ _ _ := BoundarylessManifold.isInteriorPoint
  ratio_smooth := sphereZeroRatio_smooth
  ratio_regular i x hx := sphereZeroRatio_mfderiv i x (sphereZeroRatio_zero i x hx)
  zero_subset_near _ _ _ := trivial
  boundary_eq := sphereZeroPiece_boundary
  range_eq := sphereZeroPiece_range
  model := sphereZeroModel

theorem sphereZeroDomains_count : sphereZeroDomains.count = 2 :=
  rfl

/-- **The empty cusp cores of the closed S³** (draft §7.9: count zero; no validation of the
boundary product geometry). -/
def sphereCuspCores : CuspCores sphereW (BoundaryTori.empty sphereW) where
  ports := by
    rw [BoundaryTori.empty_image]
    exact closedCarrier_boundary_eq_empty _
  piece b := b.elim0
  product b := b.elim0
  external_end b := b.elim0
  collar_owned b := b.elim0
  collar_closure_off b := b.elim0
  disjoint b := b.elim0
  cuspFn b := b.elim0
  near b := b.elim0
  near_interior b := b.elim0
  fn_smooth b := b.elim0
  fn_regular b := b.elim0
  internal_eq b := b.elim0
  near_eq b := b.elim0
  internalModelFace b := b.elim0
  internalModelFace_eq b := b.elim0
  externalModelFace b := b.elim0
  externalModelFace_eq b := b.elim0
  modelFace_cases b := b.elim0

end GC.GraphManifold.Assembly.FC39P0
