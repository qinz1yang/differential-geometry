import
  DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.Inhabitants.SolidTorusBallChartSTI
import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.FC39P0Base
import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.AssemblySphereCutCapped

/-!
# S-SOLIDTORUS (suffix `_STI`), part 2: the cap ball piece in the solid torus carrier

The ball zero core `B = {Re z₂ ≥ 4/5}` of the solid torus `X135Radial.carrier` as the image of the
closed unit cell under the graph chart (radius `3/5`), with the global linear ratio
`4/5 - Re z₂`.
-/

set_option autoImplicit false

noncomputable section

open Set Function Manifold
open DifferentialGeometry DifferentialGeometry.Topology GC.Endpoint GC.GraphManifold
open scoped Manifold ContDiff Topology

namespace GC.GraphManifold.Assembly.FC39P0.SolidTorusSTI

/-- The carrier of the instance: the solid torus of the X135 inhabitant. -/
abbrev Wc : CompactCarrier.{0} := X135Radial.carrier

local instance carrierCharts_BallSTI : ChartedSpace (EuclideanHalfSpace 3) Wc.Carrier := by
  change ChartedSpace (EuclideanHalfSpace 3) solidTorusSet.{0}
  exact inferInstance

local instance carrierSmooth_BallSTI : IsManifold (𝓡∂ 3) ∞ Wc.Carrier := by
  change IsManifold (𝓡∂ 3) ∞ solidTorusSet.{0}
  exact inferInstance

local instance ballCharts_STI : ChartedSpace (EuclideanHalfSpace 3) (ClosedCell 3) :=
  DifferentialGeometry.Topology.Handle.closedCellChartedSpaceSucc 2

local instance ballSmooth_STI : IsManifold (𝓡∂ 3) ∞ (ClosedCell 3) :=
  DifferentialGeometry.Topology.Handle.closedCellIsManifold 2

local instance ballConnected_STI : ConnectedSpace (ClosedCell 3) :=
  closedCell_three_connectedSpace

/-- The cap parameter `κ = 4/5`: the ball is `{Re z₂ ≥ κ}`. -/
def capLevel_STI : ℝ := 4 / 5

/-- The chart radius `3/5 = √(1 - κ²)` of the cap. -/
def capRadius_STI : ℝ := 3 / 5

/-- The cap map into `S³`: the closed cell under the graph chart. -/
def capS_STI (x : ClosedCell 3) : SphereCarrier.{0} :=
  DifferentialGeometry.Topology.Manifold.closedCellChartMap graphChart_STI 0 capRadius_STI x

theorem capS_apply_STI (x : ClosedCell 3) :
    capS_STI x = graphMap_STI (capRadius_STI • x.val) := by
  change graphChart_STI (0 + capRadius_STI • x.val) = _
  rw [zero_add]
  rfl

theorem norm_cap_arg_STI (x : ClosedCell 3) : ‖capRadius_STI • x.val‖ ≤ 3 / 5 := by
  rw [norm_smul, capRadius_STI, Real.norm_eq_abs, abs_of_pos (by norm_num)]
  have := x.property
  nlinarith

theorem cap_closedBall_STI : Metric.closedBall (0 : EuclideanSpace ℝ (Fin 3)) capRadius_STI ⊆
    graphChart_STI.source := by
  intro v hv
  change v ∈ Metric.ball (0 : EuclideanSpace ℝ (Fin 3)) 1
  rw [mem_ball_zero_iff]
  rw [mem_closedBall_zero_iff] at hv
  have : capRadius_STI = 3 / 5 := rfl
  linarith

theorem contMDiff_capS_STI : ContMDiff (𝓡∂ 3) (𝓡 3) ∞ capS_STI :=
  DifferentialGeometry.Topology.Manifold.contMDiff_closedCellChartMap graphChart_STI 0
    (by norm_num [capRadius_STI]) cap_closedBall_STI

theorem injective_mfderiv_capS_STI (x : ClosedCell 3) :
    Injective (mfderiv (𝓡∂ 3) (𝓡 3) capS_STI x) :=
  DifferentialGeometry.Topology.Manifold.injective_mfderiv_closedCellChartMap graphChart_STI 0
    (by norm_num [capRadius_STI]) cap_closedBall_STI x

theorem sphereSecond_capS_STI (x : ClosedCell 3) :
    sphereSecond (capS_STI x) = graphSecond_STI (capRadius_STI • x.val) := by
  rw [capS_apply_STI]
  have h := norm_cap_arg_STI x
  exact sphereSecond_graphMap_STI (by nlinarith [norm_nonneg (capRadius_STI • x.val)])

theorem sphereFirst_capS_STI (x : ClosedCell 3) :
    sphereFirst (capS_STI x) = graphFirst_STI (capRadius_STI • x.val) := by
  rw [capS_apply_STI]
  have h := norm_cap_arg_STI x
  exact sphereFirst_graphMap_STI (by nlinarith [norm_nonneg (capRadius_STI • x.val)])

theorem re_second_capS_STI (x : ClosedCell 3) :
    (sphereSecond (capS_STI x)).re = √(1 - (9 / 25) * ‖x.val‖ ^ 2) := by
  rw [sphereSecond_capS_STI, graphSecond_re_STI, norm_smul, capRadius_STI, Real.norm_eq_abs,
    abs_of_pos (by norm_num)]
  congr 1
  ring

theorem cliffordHeight_capS_lt_STI (x : ClosedCell 3) : cliffordHeight (capS_STI x) < 0 := by
  have h1 := norm_sphereFirst_sq_eq (capS_STI x)
  have h2 : ‖sphereFirst (capS_STI x)‖ ^ 2 ≤ 9 / 25 := by
    rw [sphereFirst_capS_STI, Complex.sq_norm, Complex.normSq_apply]
    simp only [graphFirst_STI]
    have hn := norm_sq_fin_three_STI (capRadius_STI • x.val)
    have hb := norm_cap_arg_STI x
    have hs : (capRadius_STI • x.val) 2 ^ 2 ≥ 0 := sq_nonneg _
    nlinarith [norm_nonneg (capRadius_STI • x.val)]
  nlinarith


/-! ## The ball piece in the solid torus -/

/-- The cap map into the solid torus carrier. -/
def capW_STI (x : ClosedCell 3) : Wc.Carrier :=
  ⟨capS_STI x, (cliffordHeight_capS_lt_STI x).le⟩

theorem capW_val_STI (x : ClosedCell 3) : (capW_STI x).val = capS_STI x := rfl

theorem contMDiff_capW_STI : ContMDiff (𝓡∂ 3) (𝓡∂ 3) ∞ capW_STI :=
  (solidTorusAtlas.contMDiff_iff_subtype_val capW_STI).mpr contMDiff_capS_STI

theorem injective_capS_STI : Injective capS_STI := by
  intro x y hxy
  have hx : capRadius_STI • x.val ∈ graphChart_STI.source := cap_closedBall_STI (by
    rw [mem_closedBall_zero_iff]; exact norm_cap_arg_STI x |>.trans (by norm_num [capRadius_STI]))
  have hy : capRadius_STI • y.val ∈ graphChart_STI.source := cap_closedBall_STI (by
    rw [mem_closedBall_zero_iff]; exact norm_cap_arg_STI y |>.trans (by norm_num [capRadius_STI]))
  rw [capS_apply_STI, capS_apply_STI] at hxy
  have h := graphChart_STI.injOn hx hy hxy
  apply Subtype.ext
  have := smul_right_injective (EuclideanSpace ℝ (Fin 3)) (show capRadius_STI ≠ 0 by
    norm_num [capRadius_STI]) h
  exact this

theorem injective_capW_STI : Injective capW_STI := fun _ _ h =>
  injective_capS_STI (congrArg Subtype.val h)

theorem mfderiv_capW_bijective_STI (x : ClosedCell 3) :
    Bijective (mfderiv (𝓡∂ 3) (𝓡∂ 3) capW_STI x) := by
  have hchain := mfderiv_comp x
    (contMDiff_solidTorus_val.mdifferentiableAt (by simp) :
      MDifferentiableAt (𝓡∂ 3) (𝓡 3) (Subtype.val : Wc.Carrier → SphereCarrier.{0})
        (capW_STI x))
    (contMDiff_capW_STI.mdifferentiableAt (by simp))
  have hinj : Injective (mfderiv (𝓡∂ 3) (𝓡∂ 3) capW_STI x) := by
    have h1 : Injective (mfderiv (𝓡∂ 3) (𝓡 3)
        ((Subtype.val : Wc.Carrier → SphereCarrier.{0}) ∘ capW_STI) x) :=
      injective_mfderiv_capS_STI x
    have h2 := hchain ▸ h1
    exact Function.Injective.of_comp h2
  exact ⟨hinj, LinearMap.injective_iff_surjective.mp hinj⟩

/-- **The ball piece** of the solid torus instance. -/
def capPiece_STI : PieceEmbedding Wc where
  Piece := ClosedCell 3
  map := capW_STI
  smooth := contMDiff_capW_STI
  mfderiv_bijective := mfderiv_capW_bijective_STI
  injective := injective_capW_STI


/-! ## The ratio `κ - Re z₂` -/

/-- The global ratio of the ball on `S³`: `κ - Re z₂`. -/
def ratioS_STI (q : SphereCarrier.{0}) : ℝ := capLevel_STI - (sphereSecond q).re

/-- The global ratio of the ball: `κ - Re z₂`. -/
def ratioBall_STI (p : Wc.Carrier) : ℝ := ratioS_STI p.val

theorem contMDiff_ratioS_STI : ContMDiff (𝓡 3) 𝓘(ℝ, ℝ) ∞ ratioS_STI :=
  contMDiff_const.sub (Complex.reCLM.contDiff.contMDiff.comp contMDiff_sphereSecond)

theorem contMDiff_ratioBall_STI : ContMDiff (𝓡∂ 3) 𝓘(ℝ, ℝ) ∞ ratioBall_STI :=
  contMDiff_ratioS_STI.comp contMDiff_solidTorus_val

/-- The ratio has nonzero differential at the chart image of a nonzero point of the open ball. -/
theorem mfderiv_ratioS_ne_zero_chart_STI (v₀ : EuclideanSpace ℝ (Fin 3))
    (hv₀src : v₀ ∈ graphChart_STI.source) (hv₀ne : v₀ ≠ 0) :
    mfderiv (𝓡 3) 𝓘(ℝ, ℝ) ratioS_STI (graphChart_STI v₀) ≠ 0 := by
  have hlt1 : ‖v₀‖ < 1 := by
    have h := hv₀src
    change v₀ ∈ Metric.ball (0 : EuclideanSpace ℝ (Fin 3)) 1 at h
    simpa using h
  have hpos : 0 < 1 - ‖v₀‖ ^ 2 := by nlinarith [norm_nonneg v₀]
  let g : EuclideanSpace ℝ (Fin 3) → ℝ := fun v => capLevel_STI - √(1 - ‖v‖ ^ 2)
  have hcoord : ratioS_STI ∘ graphChart_STI =ᶠ[nhds v₀] g := by
    filter_upwards [graphChart_STI.open_source.mem_nhds hv₀src] with v hv
    have hv1 : ‖v‖ < 1 := by
      have h := hv
      change v ∈ Metric.ball (0 : EuclideanSpace ℝ (Fin 3)) 1 at h
      simpa using h
    change capLevel_STI - (sphereSecond (graphMap_STI v)).re = capLevel_STI - √(1 - ‖v‖ ^ 2)
    rw [sphereSecond_graphMap_STI (by nlinarith [norm_nonneg v]), graphSecond_re_STI]
  have hd : HasFDerivAt g (-((1 / (2 * √(1 - ‖v₀‖ ^ 2))) • (-((2 : ℕ) • innerSL ℝ v₀)))) v₀ :=
    (((hasStrictFDerivAt_norm_sq v₀).hasFDerivAt.const_sub (1 : ℝ)).sqrt hpos.ne').const_sub
      capLevel_STI
  intro hzero
  have hchain := mfderiv_comp v₀
    ((contMDiff_ratioS_STI (graphChart_STI v₀)).mdifferentiableAt (by simp) :
      MDifferentiableAt (𝓡 3) 𝓘(ℝ, ℝ) ratioS_STI (graphChart_STI v₀))
    (graphChart_STI.mdifferentiableAt (by simp) hv₀src)
  rw [hzero, ContinuousLinearMap.zero_comp, mfderiv_eq_fderiv, hcoord.fderiv_eq,
    hd.fderiv] at hchain
  have happ : (-((1 / (2 * √(1 - ‖v₀‖ ^ 2))) • (-((2 : ℕ) • innerSL ℝ v₀))) :
      EuclideanSpace ℝ (Fin 3) →L[ℝ] ℝ) v₀ = 0 := DFunLike.congr_fun hchain v₀
  simp only [neg_apply, smul_apply, innerSL_apply_apply, real_inner_self_eq_norm_sq,
    smul_eq_mul, nsmul_eq_mul, Nat.cast_ofNat] at happ
  have hs : 0 < √(1 - ‖v₀‖ ^ 2) := Real.sqrt_pos.mpr hpos
  have hn : 0 < ‖v₀‖ := norm_pos_iff.mpr hv₀ne
  have h1 : 0 < (1 / (2 * √(1 - ‖v₀‖ ^ 2))) * (2 * ‖v₀‖ ^ 2) := by positivity
  linarith

/-- The ratio has nonzero differential on the open hemisphere away from the pole `(0, 1)`. -/
theorem mfderiv_ratioS_ne_zero_STI (p : SphereCarrier.{0}) (hp : 0 < (sphereSecond p).re)
    (hp1 : (sphereSecond p).re < 1) :
    mfderiv (𝓡 3) 𝓘(ℝ, ℝ) ratioS_STI p ≠ 0 := by
  have hptarget : p ∈ graphChart_STI.target := hp
  have hv₀src : graphInv_STI p ∈ graphChart_STI.source := graphChart_STI.map_target hptarget
  have hpv : graphChart_STI (graphInv_STI p) = p := graphChart_STI.right_inv hptarget
  have hnorm : ‖graphInv_STI p‖ ^ 2 = 1 - (sphereSecond p).re ^ 2 := norm_sq_graphInv_STI p
  have hv₀ne : graphInv_STI p ≠ 0 := by
    intro h
    rw [h, norm_zero] at hnorm
    nlinarith
  have := mfderiv_ratioS_ne_zero_chart_STI (graphInv_STI p) hv₀src hv₀ne
  rwa [hpv] at this

theorem ratioBall_eq_zero_iff_STI {p : Wc.Carrier} :
    ratioBall_STI p = 0 ↔ (sphereSecond p.val).re = 4 / 5 := by
  rw [ratioBall_STI, ratioS_STI, capLevel_STI, sub_eq_zero]
  exact eq_comm

theorem ratioBall_le_zero_iff_STI {p : Wc.Carrier} :
    ratioBall_STI p ≤ 0 ↔ 4 / 5 ≤ (sphereSecond p.val).re := by
  rw [ratioBall_STI, ratioS_STI, capLevel_STI, sub_nonpos]

/-- Points of the solid torus with `Re z₂ ≥ 4/5` are strictly interior. -/
theorem cliffordHeight_lt_of_ratio_STI {p : Wc.Carrier} (h : 4 / 5 ≤ (sphereSecond p.val).re) :
    cliffordHeight p.val < 0 := by
  have h1 := norm_sphereSecond_sq_eq p.val
  have h2 : (4 / 5 : ℝ) ^ 2 ≤ ‖sphereSecond p.val‖ ^ 2 := by
    apply pow_le_pow_left₀ (by norm_num)
    exact h.trans (Complex.re_le_norm _)
  nlinarith

theorem ratioBall_regular_STI (p : Wc.Carrier) (hp : ratioBall_STI p = 0) :
    mfderiv (𝓡∂ 3) 𝓘(ℝ, ℝ) ratioBall_STI p ≠ 0 := by
  have hre := ratioBall_eq_zero_iff_STI.1 hp
  have hval := solidTorusAtlas.mfderiv_subtypeVal_bijective p
  have hf := mfderiv_ratioS_ne_zero_STI p.val (by rw [hre]; norm_num) (by rw [hre]; norm_num)
  have hchain := mfderiv_comp p
    ((contMDiff_ratioS_STI p.val).mdifferentiableAt (by simp) :
      MDifferentiableAt (𝓡 3) 𝓘(ℝ, ℝ) ratioS_STI p.val)
    (contMDiff_solidTorus_val.mdifferentiableAt (by simp) :
      MDifferentiableAt (𝓡∂ 3) (𝓡 3) (Subtype.val : Wc.Carrier → SphereCarrier.{0}) p)
  intro hzero
  apply hf
  have hz : mfderiv (𝓡∂ 3) 𝓘(ℝ, ℝ)
      (ratioS_STI ∘ (Subtype.val : Wc.Carrier → SphereCarrier.{0})) p = 0 := hzero
  have hc := hchain.symm.trans hz
  ext v
  obtain ⟨u, hu⟩ := hval.2 v
  have h1 : (mfderiv (𝓡 3) 𝓘(ℝ, ℝ) ratioS_STI p.val)
      ((mfderiv (𝓡∂ 3) (𝓡 3) (Subtype.val : Wc.Carrier → SphereCarrier.{0}) p) u) = 0 :=
    DFunLike.congr_fun hc u
  rw [hu] at h1
  exact h1


/-! ## Range and boundary of the ball piece -/

theorem exists_cap_preimage_STI {p : Wc.Carrier} (h : 4 / 5 ≤ (sphereSecond p.val).re) :
    ∃ x : ClosedCell 3, capW_STI x = p ∧
      ‖x.val‖ ^ 2 = (25 / 9) * (1 - (sphereSecond p.val).re ^ 2) := by
  have hpos : 0 < (sphereSecond p.val).re := by linarith
  have htarget : p.val ∈ graphChart_STI.target := hpos
  have hnorm := norm_sq_graphInv_STI p.val
  have hsq : (16 / 25 : ℝ) ≤ (sphereSecond p.val).re ^ 2 := by nlinarith
  have hle : ‖(5 / 3 : ℝ) • graphInv_STI p.val‖ ≤ 1 := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos (by norm_num : (0 : ℝ) < 5 / 3)]
    have h1 : ‖graphInv_STI p.val‖ ^ 2 ≤ 9 / 25 := by nlinarith
    have h2 : ‖graphInv_STI p.val‖ ≤ 3 / 5 := by
      by_contra hcon
      have := not_le.mp hcon
      nlinarith [norm_nonneg (graphInv_STI p.val)]
    nlinarith
  refine ⟨⟨(5 / 3 : ℝ) • graphInv_STI p.val, hle⟩, ?_, ?_⟩
  · apply Subtype.ext
    change capS_STI ⟨(5 / 3 : ℝ) • graphInv_STI p.val, hle⟩ = p.val
    rw [capS_apply_STI]
    change graphChart_STI (capRadius_STI • (5 / 3 : ℝ) • graphInv_STI p.val) = p.val
    rw [smul_smul, show capRadius_STI * (5 / 3 : ℝ) = 1 by norm_num [capRadius_STI], one_smul]
    exact graphChart_STI.right_inv htarget
  · change ‖(5 / 3 : ℝ) • graphInv_STI p.val‖ ^ 2 = _
    rw [norm_smul, mul_pow, hnorm, Real.norm_eq_abs, sq_abs]
    ring

theorem range_capPiece_STI : range capPiece_STI.map = {p | ratioBall_STI p ≤ 0} := by
  ext p
  constructor
  · rintro ⟨x₀, rfl⟩
    let x : ClosedCell 3 := x₀
    change ratioBall_STI (capW_STI x) ≤ 0
    rw [ratioBall_le_zero_iff_STI]
    change 4 / 5 ≤ (sphereSecond (capS_STI x)).re
    rw [re_second_capS_STI]
    apply Real.le_sqrt_of_sq_le
    have := x.property
    nlinarith [norm_nonneg x.val]
  · intro hp
    obtain ⟨x, hx, -⟩ := exists_cap_preimage_STI (ratioBall_le_zero_iff_STI.1 hp)
    exact ⟨x, hx⟩

theorem closedCell_isBoundaryPoint_STI {x : ClosedCell 3} :
    (𝓡∂ 3).IsBoundaryPoint x ↔ ‖x.val‖ = 1 := by
  change x ∈ (𝓡∂ 3).boundary (ClosedCell 3) ↔ _
  rw [DifferentialGeometry.Topology.Manifold.closedCell_boundary_eq_sphere 2]
  rfl

theorem pieceBoundary_capPiece_STI :
    pieceBoundary capPiece_STI = {p | ratioBall_STI p = 0} := by
  ext p
  constructor
  · rintro ⟨x₀, hx, rfl⟩
    let x : ClosedCell 3 := x₀
    have h1 : ‖x.val‖ = 1 := closedCell_isBoundaryPoint_STI.1 hx
    change ratioBall_STI (capW_STI x) = 0
    rw [ratioBall_eq_zero_iff_STI]
    change (sphereSecond (capS_STI x)).re = 4 / 5
    rw [re_second_capS_STI, h1]
    rw [show (1 : ℝ) - 9 / 25 * 1 ^ 2 = (4 / 5) ^ 2 by norm_num]
    exact Real.sqrt_sq (by norm_num)
  · intro hp
    have hre := ratioBall_eq_zero_iff_STI.1 hp
    obtain ⟨x, hx, hn⟩ := exists_cap_preimage_STI (by rw [hre])
    refine ⟨x, closedCell_isBoundaryPoint_STI.2 ?_, hx⟩
    rw [hre] at hn
    have : ‖x.val‖ ^ 2 = 1 := by rw [hn]; norm_num
    have h0 : 0 ≤ ‖x.val‖ := norm_nonneg _
    nlinarith


/-! ## The zero domains of the instance -/

/-- The open set `{height < 0}` (the interior of the solid torus). -/
def ballNear_STI : TopologicalSpace.Opens Wc.Carrier :=
  ⟨{p | X135Radial.height p < 0}, isOpen_lt X135Radial.height_continuous continuous_const⟩

theorem ballNear_interior_STI : (ballNear_STI : Set Wc.Carrier) ⊆ Wc.interior := by
  intro p hp
  exact (solidTorus_isInteriorPoint_iff p).mpr hp

/-- **The zero domains of the solid torus instance**: exactly one ball, the cap `Re z₂ ≥ 4/5`. -/
def ballZeroDomains_STI : ZeroDomains Wc where
  count := 1
  piece _ := capPiece_STI
  disjoint i j h := absurd (Subsingleton.elim i j) h
  ratio _ := ratioBall_STI
  near _ := ballNear_STI
  near_interior _ := ballNear_interior_STI
  ratio_smooth _ := contMDiff_ratioBall_STI
  ratio_regular _ p hp := ratioBall_regular_STI p hp
  zero_subset_near _ _ hp :=
    cliffordHeight_lt_of_ratio_STI ((ratioBall_eq_zero_iff_STI.1 hp).ge)
  boundary_eq _ := pieceBoundary_capPiece_STI
  range_eq _ := range_capPiece_STI
  model _ := Sum.inl (.ball (Diffeomorph.refl (𝓡∂ 3) (ClosedCell 3) ∞))


/-- On the ball `Re z₂ ≥ 4/5` the height is below `-1/4`. -/
theorem height_lt_of_ratio_STI {p : Wc.Carrier} (h : 4 / 5 ≤ (sphereSecond p.val).re) :
    X135Radial.height p < -(1 / 4 : ℝ) := by
  have h1 := norm_sphereSecond_sq_eq p.val
  have h2 : (4 / 5 : ℝ) ^ 2 ≤ ‖sphereSecond p.val‖ ^ 2 := by
    apply pow_le_pow_left₀ (by norm_num)
    exact h.trans (Complex.re_le_norm _)
  change cliffordHeight p.val < -(1 / 4 : ℝ)
  nlinarith

/-- The ball is disjoint from the cusp core of the X135 radial instance (`height ≥ -1/4`): the
`zero_cusp_disjoint` field of the junctions. -/
theorem ball_cusp_disjoint_STI :
    Disjoint (range capPiece_STI.map) (range X135Radial.cuspPiece.map) := by
  rw [Set.disjoint_left]
  rintro p hp hc
  change p ∈ range X135Radial.cuspToCarrier at hc
  rw [X135Radial.cuspToCarrier_range] at hc
  have hr : p ∈ range capPiece_STI.map := hp
  rw [range_capPiece_STI] at hr
  have := height_lt_of_ratio_STI (ratioBall_le_zero_iff_STI.1 hr)
  have hc' : -(1 / 4 : ℝ) ≤ X135Radial.height p := hc
  linarith

end GC.GraphManifold.Assembly.FC39P0.SolidTorusSTI
