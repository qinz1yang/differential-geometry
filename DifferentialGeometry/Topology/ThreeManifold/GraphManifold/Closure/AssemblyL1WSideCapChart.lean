import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.AssemblyL1StandardFacts

/-!
# Chapter-14 assembly, item L1, group G3b: the cap chart as a partial diffeomorphism of `ℝ³`

The cap chart `capMap b` (`AssemblyL1Standard.lean`: stereographic coordinate of the direction from
the antipodal pole and the radial coordinate `‖x‖ - 1`; the cap `true` is the mirror image of the
cap `false`) is a smooth partial diffeomorphism `capPD b` from the open half-space
`{0 < ⟪x, capPole b⟫}` onto `{-1 < τ, ‖z‖ < 2}`, with inverse
`capInv b (z, τ) = (1 + τ) • c⁻¹ z` (`c` the stereographic chart from the north pole, reflected for
`b = true`). Consumed by the ball step T3 of lane ASM-L1b: the germs of the two-disk normalization
G2 are `capPD b` followed by the inverse of the neck read in the ball.
-/

set_option autoImplicit false

noncomputable section

open Set Function Metric
open DifferentialGeometry DifferentialGeometry.Topology GC.Endpoint Manifold
open scoped Manifold ContDiff Topology InnerProductSpace

namespace GC.GraphManifold.Assembly

local instance fact_finrank_three_ASML1bC :
    Fact (Module.finrank ℝ (EuclideanSpace ℝ (Fin 3)) = 2 + 1) := ⟨by simp⟩

/-- The inverse of the south cap chart. -/
def southCapInv (q : EuclideanSpace ℝ (Fin 2) × ℝ) : EuclideanSpace ℝ (Fin 3) :=
  (1 + q.2) • ((DifferentialGeometry.Topology.Handle.stereoChart northPole).symm q.1 :
    EuclideanSpace ℝ (Fin 3))

/-- The inverse of the cap chart `b`. -/
def capInv (b : Bool) (q : EuclideanSpace ℝ (Fin 2) × ℝ) : EuclideanSpace ℝ (Fin 3) :=
  if b then reflectThree (southCapInv q) else southCapInv q

/-- The source of the cap chart `b`: the open half-space of the pole `b`. -/
def capSource (b : Bool) : Set (EuclideanSpace ℝ (Fin 3)) :=
  {x | 0 < ⟪x, ((capPole b : sphere (0 : EuclideanSpace ℝ (Fin 3)) 1) :
    EuclideanSpace ℝ (Fin 3))⟫_ℝ}

/-- The target of the cap charts. -/
def capTarget : Set (EuclideanSpace ℝ (Fin 2) × ℝ) := {q | -1 < q.2 ∧ ‖q.1‖ < 2}

theorem isOpen_capSource (b : Bool) : IsOpen (capSource b) :=
  isOpen_lt continuous_const (continuous_id.inner continuous_const)

theorem isOpen_capTarget : IsOpen capTarget :=
  (isOpen_lt continuous_const continuous_snd).inter
    (isOpen_lt (continuous_norm.comp continuous_fst) continuous_const)

theorem inner_south_eq_neg_inner_north (x : EuclideanSpace ℝ (Fin 3)) :
    ⟪x, ((southPole : sphere (0 : EuclideanSpace ℝ (Fin 3)) 1) : EuclideanSpace ℝ (Fin 3))⟫_ℝ =
      -⟪x, ((northPole : sphere (0 : EuclideanSpace ℝ (Fin 3)) 1) :
        EuclideanSpace ℝ (Fin 3))⟫_ℝ := by
  rw [southPole_val, northPole_val, inner_neg_right]

theorem ne_zero_of_mem_capSource {b : Bool} {x : EuclideanSpace ℝ (Fin 3)}
    (hx : x ∈ capSource b) : x ≠ 0 := by
  rintro rfl
  simp [capSource] at hx

/-- The south cap source in terms of the direction: it is the open south hemisphere. -/
theorem inner_sphereDirection_north_neg {x : EuclideanSpace ℝ (Fin 3)} (hx : x ∈ capSource false) :
    ⟪((DifferentialGeometry.Topology.Manifold.sphereDirection southPole x :
        sphere (0 : EuclideanSpace ℝ (Fin 3)) 1) : EuclideanSpace ℝ (Fin 3)),
      ((northPole : sphere (0 : EuclideanSpace ℝ (Fin 3)) 1) : EuclideanSpace ℝ (Fin 3))⟫_ℝ < 0 := by
  have hx0 := ne_zero_of_mem_capSource hx
  have hxs : 0 < ⟪x, ((southPole : sphere (0 : EuclideanSpace ℝ (Fin 3)) 1) :
      EuclideanSpace ℝ (Fin 3))⟫_ℝ := hx
  rw [DifferentialGeometry.Topology.Manifold.coe_sphereDirection _ hx0, inner_smul_left]
  simp only [RCLike.conj_to_real]
  rw [inner_south_eq_neg_inner_north] at hxs
  have hpos : 0 < ‖x‖⁻¹ := inv_pos.mpr (norm_pos_iff.mpr hx0)
  nlinarith

theorem sphereDirection_ne_north {x : EuclideanSpace ℝ (Fin 3)} (hx : x ∈ capSource false) :
    DifferentialGeometry.Topology.Manifold.sphereDirection southPole x ≠ northPole := by
  intro h
  have h1 := inner_sphereDirection_north_neg hx
  rw [h, real_inner_self_eq_norm_sq, norm_eq_of_mem_sphere] at h1
  norm_num at h1

theorem sphereDirection_mem_stereoChart_source {x : EuclideanSpace ℝ (Fin 3)}
    (hx : x ∈ capSource false) :
    DifferentialGeometry.Topology.Manifold.sphereDirection southPole x ∈
      (DifferentialGeometry.Topology.Handle.stereoChart northPole).source := by
  rw [DifferentialGeometry.Topology.Handle.stereoChart_source]
  exact sphereDirection_ne_north hx

theorem southCapMap_mem_capTarget {x : EuclideanSpace ℝ (Fin 3)} (hx : x ∈ capSource false) :
    southCapMap x ∈ capTarget := by
  have hx0 := ne_zero_of_mem_capSource hx
  set θ := DifferentialGeometry.Topology.Manifold.sphereDirection southPole x
  set y := DifferentialGeometry.Topology.Handle.stereoChart northPole θ
  have hθ : (DifferentialGeometry.Topology.Handle.stereoChart northPole).symm y = θ :=
    (DifferentialGeometry.Topology.Handle.stereoChart northPole).left_inv
      (sphereDirection_mem_stereoChart_source hx)
  have hin := DifferentialGeometry.Topology.Handle.inner_stereoChart_symm northPole y
  rw [hθ] at hin
  have hneg := inner_sphereDirection_north_neg hx
  rw [hin] at hneg
  have hpos : (0 : ℝ) < ‖y‖ ^ 2 + 4 := by positivity
  have hy : ‖y‖ ^ 2 < 4 := by
    rw [div_neg_iff] at hneg
    rcases hneg with h | h
    · linarith [h.2]
    · linarith [h.1]
  refine ⟨?_, ?_⟩
  · change -1 < ‖x‖ - 1
    linarith [norm_pos_iff.mpr hx0]
  · change ‖y‖ < 2
    nlinarith [norm_nonneg y]

theorem inner_southCapInv_south_pos {q : EuclideanSpace ℝ (Fin 2) × ℝ} (hq : q ∈ capTarget) :
    0 < ⟪southCapInv q, ((southPole : sphere (0 : EuclideanSpace ℝ (Fin 3)) 1) :
      EuclideanSpace ℝ (Fin 3))⟫_ℝ := by
  obtain ⟨hq1, hq2⟩ := hq
  rw [southCapInv, inner_smul_left, inner_south_eq_neg_inner_north,
    DifferentialGeometry.Topology.Handle.inner_stereoChart_symm]
  simp only [RCLike.conj_to_real]
  have hpos : (0 : ℝ) < ‖q.1‖ ^ 2 + 4 := by positivity
  have hlt : ‖q.1‖ ^ 2 < 4 := by nlinarith [norm_nonneg q.1]
  have h1 : 0 < 1 + q.2 := by linarith
  have h2 : (‖q.1‖ ^ 2 - 4) / (‖q.1‖ ^ 2 + 4) < 0 := div_neg_of_neg_of_pos (by linarith) hpos
  nlinarith

theorem southCapInv_mem_capSource {q : EuclideanSpace ℝ (Fin 2) × ℝ} (hq : q ∈ capTarget) :
    southCapInv q ∈ capSource false :=
  inner_southCapInv_south_pos hq

theorem southCapInv_southCapMap {x : EuclideanSpace ℝ (Fin 3)} (hx : x ∈ capSource false) :
    southCapInv (southCapMap x) = x := by
  have hx0 := ne_zero_of_mem_capSource hx
  have hl : (DifferentialGeometry.Topology.Handle.stereoChart northPole).symm
      (DifferentialGeometry.Topology.Handle.stereoChart northPole
        (DifferentialGeometry.Topology.Manifold.sphereDirection southPole x)) =
      DifferentialGeometry.Topology.Manifold.sphereDirection southPole x :=
    (DifferentialGeometry.Topology.Handle.stereoChart northPole).left_inv
      (sphereDirection_mem_stereoChart_source hx)
  rw [southCapInv, southCapMap_apply]
  simp only [add_sub_cancel]
  erw [hl]
  exact DifferentialGeometry.Topology.Manifold.norm_smul_sphereDirection _ hx0

theorem southCapMap_southCapInv {q : EuclideanSpace ℝ (Fin 2) × ℝ} (hq : q ∈ capTarget) :
    southCapMap (southCapInv q) = q := by
  obtain ⟨hq1, -⟩ := hq
  have h1 : 0 < 1 + q.2 := by linarith
  set θ := (DifferentialGeometry.Topology.Handle.stereoChart northPole).symm q.1
  rw [southCapMap_apply, southCapInv]
  change (DifferentialGeometry.Topology.Handle.stereoChart northPole
      (DifferentialGeometry.Topology.Manifold.sphereDirection southPole
        ((1 + q.2) • (θ : EuclideanSpace ℝ (Fin 3)))),
    ‖(1 + q.2) • (θ : EuclideanSpace ℝ (Fin 3))‖ - 1) = q
  have hr : DifferentialGeometry.Topology.Handle.stereoChart northPole θ = q.1 :=
    (DifferentialGeometry.Topology.Handle.stereoChart northPole).right_inv
      (by rw [DifferentialGeometry.Topology.Handle.stereoChart_target]; exact mem_univ _)
  rw [DifferentialGeometry.Topology.Manifold.sphereDirection_pos_smul _ _ h1]
  erw [hr]
  rw [norm_smul, norm_eq_of_mem_sphere, mul_one, Real.norm_of_nonneg h1.le, add_sub_cancel_left]

/-- The cap source `true` is the mirror image of the cap source `false`. -/
theorem mem_capSource_true_iff {x : EuclideanSpace ℝ (Fin 3)} :
    x ∈ capSource true ↔ reflectThree x ∈ capSource false := by
  change 0 < ⟪x, ((northPole : sphere (0 : EuclideanSpace ℝ (Fin 3)) 1) :
      EuclideanSpace ℝ (Fin 3))⟫_ℝ ↔ 0 < ⟪reflectThree x, ((southPole :
        sphere (0 : EuclideanSpace ℝ (Fin 3)) 1) : EuclideanSpace ℝ (Fin 3))⟫_ℝ
  rw [inner_reflectThree, ← reflectThree_north, reflectThree_reflectThree]

theorem capMap_mem_capTarget {b : Bool} {x : EuclideanSpace ℝ (Fin 3)} (hx : x ∈ capSource b) :
    capMap b x ∈ capTarget := by
  cases b
  · exact southCapMap_mem_capTarget hx
  · exact southCapMap_mem_capTarget (mem_capSource_true_iff.mp hx)

theorem capInv_mem_capSource {b : Bool} {q : EuclideanSpace ℝ (Fin 2) × ℝ} (hq : q ∈ capTarget) :
    capInv b q ∈ capSource b := by
  cases b
  · exact southCapInv_mem_capSource hq
  · apply mem_capSource_true_iff.mpr
    change reflectThree (reflectThree (southCapInv q)) ∈ capSource false
    rw [reflectThree_reflectThree]
    exact southCapInv_mem_capSource hq

theorem capInv_capMap {b : Bool} {x : EuclideanSpace ℝ (Fin 3)} (hx : x ∈ capSource b) :
    capInv b (capMap b x) = x := by
  cases b
  · exact southCapInv_southCapMap hx
  · change reflectThree (southCapInv (southCapMap (reflectThree x))) = x
    rw [southCapInv_southCapMap (mem_capSource_true_iff.mp hx), reflectThree_reflectThree]

theorem capMap_capInv {b : Bool} {q : EuclideanSpace ℝ (Fin 2) × ℝ} (hq : q ∈ capTarget) :
    capMap b (capInv b q) = q := by
  cases b
  · exact southCapMap_southCapInv hq
  · change southCapMap (reflectThree (reflectThree (southCapInv q))) = q
    rw [reflectThree_reflectThree, southCapMap_southCapInv hq]

/-! ## Smoothness -/

theorem contDiffOn_southCapMap : ContDiffOn ℝ ∞ southCapMap (capSource false) := by
  have hdir : ContMDiffOn 𝓘(ℝ, EuclideanSpace ℝ (Fin 3)) (𝓡 2) ∞
      (DifferentialGeometry.Topology.Manifold.sphereDirection southPole) (capSource false) :=
    (DifferentialGeometry.Topology.Manifold.contMDiffOn_sphereDirection (n := 2) southPole).mono
      (fun x hx => ne_zero_of_mem_capSource hx)
  have hst : ContMDiffOn 𝓘(ℝ, EuclideanSpace ℝ (Fin 3)) (𝓡 2) ∞
      (fun x => DifferentialGeometry.Topology.Handle.stereoChart northPole
        (DifferentialGeometry.Topology.Manifold.sphereDirection southPole x)) (capSource false) :=
    (DifferentialGeometry.Topology.Handle.stereoChart northPole).contMDiffOn_toFun.comp hdir
      (fun x hx => sphereDirection_mem_stereoChart_source hx)
  have h1 : ContDiffOn ℝ ∞ (fun x => DifferentialGeometry.Topology.Handle.stereoChart northPole
      (DifferentialGeometry.Topology.Manifold.sphereDirection southPole x)) (capSource false) :=
    contMDiffOn_iff_contDiffOn.mp hst
  have h2 : ContDiffOn ℝ ∞ (fun x : EuclideanSpace ℝ (Fin 3) => ‖x‖ - 1) (capSource false) :=
    fun x hx => ((contDiffAt_norm ℝ (ne_zero_of_mem_capSource hx)).sub
      contDiffAt_const).contDiffWithinAt
  exact h1.prodMk h2

theorem contDiffOn_capMap (b : Bool) : ContDiffOn ℝ ∞ (capMap b) (capSource b) := by
  cases b
  · exact contDiffOn_southCapMap
  · change ContDiffOn ℝ ∞ (fun x => southCapMap (reflectThree x)) (capSource true)
    exact contDiffOn_southCapMap.comp reflectThree.toContinuousLinearEquiv.contDiff.contDiffOn
      (fun x hx => mem_capSource_true_iff.mp hx)

theorem contDiff_southCapInv : ContDiff ℝ ∞ southCapInv := by
  have hs : ContMDiff (𝓡 2) (𝓡 2) ∞
      (DifferentialGeometry.Topology.Handle.stereoChart northPole).symm := by
    have h := (DifferentialGeometry.Topology.Handle.stereoChart northPole).contMDiffOn_invFun
    rw [DifferentialGeometry.Topology.Handle.stereoChart_target] at h
    exact contMDiffOn_univ.mp h
  have hc : ContMDiff (𝓡 2) 𝓘(ℝ, EuclideanSpace ℝ (Fin 3)) ∞
      (fun y => ((DifferentialGeometry.Topology.Handle.stereoChart northPole).symm y :
        EuclideanSpace ℝ (Fin 3))) :=
    (contMDiff_coe_sphere (n := 2)).comp hs
  have hc' : ContDiff ℝ ∞ (fun y => ((DifferentialGeometry.Topology.Handle.stereoChart
      northPole).symm y : EuclideanSpace ℝ (Fin 3))) := contMDiff_iff_contDiff.mp hc
  exact (contDiff_const.add contDiff_snd).smul (hc'.comp contDiff_fst)

theorem contDiff_capInv (b : Bool) : ContDiff ℝ ∞ (capInv b) := by
  cases b
  · exact contDiff_southCapInv
  · exact reflectThree.toContinuousLinearEquiv.contDiff.comp contDiff_southCapInv

/-- **The cap chart as a partial diffeomorphism of `ℝ³`.** -/
def capPD (b : Bool) : PartialDiffeomorph 𝓘(ℝ, EuclideanSpace ℝ (Fin 3))
    𝓘(ℝ, EuclideanSpace ℝ (Fin 2) × ℝ) (EuclideanSpace ℝ (Fin 3))
    (EuclideanSpace ℝ (Fin 2) × ℝ) ∞ where
  toFun := capMap b
  invFun := capInv b
  source := capSource b
  target := capTarget
  map_source' _ hx := capMap_mem_capTarget hx
  map_target' _ hq := capInv_mem_capSource hq
  left_inv' _ hx := capInv_capMap hx
  right_inv' _ hq := capMap_capInv hq
  open_source := isOpen_capSource b
  open_target := isOpen_capTarget
  contMDiffOn_toFun := (contDiffOn_capMap b).contMDiffOn
  contMDiffOn_invFun := (contDiff_capInv b).contMDiff.contMDiffOn

theorem capPD_apply (b : Bool) (x : EuclideanSpace ℝ (Fin 3)) : capPD b x = capMap b x :=
  rfl

theorem capPD_symm_apply (b : Bool) (q : EuclideanSpace ℝ (Fin 2) × ℝ) :
    (capPD b).symm q = capInv b q :=
  rfl

theorem capPD_source (b : Bool) : (capPD b).source = capSource b :=
  rfl

theorem capPD_target (b : Bool) : (capPD b).target = capTarget :=
  rfl

/-- The cap region of the closed cell lies in the cap source. -/
theorem val_mem_capSource_of_mem_neckCapRegion {ε : ℝ} {b : Bool} {x : ClosedCell 3}
    (hx : x ∈ neckCapRegion ε b) : (x : EuclideanSpace ℝ (Fin 3)) ∈ capSource b :=
  hx.2.1

/-- The cap chart `true` is the cap chart `false` after the reflection. -/
theorem capMap_true_eq_comp : capMap true = capMap false ∘ reflectThree :=
  rfl

end GC.GraphManifold.Assembly
