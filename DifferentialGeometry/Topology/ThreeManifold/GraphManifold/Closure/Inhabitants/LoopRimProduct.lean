import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.Inhabitants.CycleRimProduct

/-!
One actual ball and one actual product disk handle in the rotational solid-torus model of S³.
Both distinct rims retain the fixed rounding and genuine disk-times-interval coordinates.
-/

set_option autoImplicit false

noncomputable section

open Set Function Metric Manifold DifferentialGeometry DifferentialGeometry.Topology
open DifferentialGeometry.Topology.Manifold GC.Endpoint GC.GraphManifold
open scoped Manifold ContDiff Topology

namespace GC.GraphManifold.Assembly

attribute [local instance] Handle.closedCellChartedSpaceSucc Handle.closedCellIsManifold

local instance loopBallConnected : ConnectedSpace (ClosedCell 3) :=
  closedCell_three_connectedSpace

local instance loopSphereSecond : SecondCountableTopology SphereCarrier.{0} :=
  secondCountableTopology_sphereCarrier

private def loopForm : ModelCycleNormalForm.{0} 1 (1 / 16) :=
  modelCycleNormalForm (by norm_num) (by norm_num) (by norm_num)

private def loopBall : PieceEmbedding (NoCuts.carrier standardThreeSphereLift.{0}) where
  Piece := ClosedCell 3
  map := loopForm.ball 0
  smooth := loopForm.ball_smooth 0
  mfderiv_bijective := loopForm.ball_mfderiv 0
  injective := loopForm.ball_injective 0

private def loopHandle : EdgeHandle (NoCuts.carrier standardThreeSphereLift.{0}) where
  map := loopForm.handle 0
  smooth := loopForm.handle_smooth 0
  mfderiv_bijective := loopForm.handle_mfderiv 0
  injective := loopForm.handle_injective 0
  interior _q _hq := BoundarylessManifold.isInteriorPoint

private def loopRim (b : Bool) : PartialDiffeomorph ((𝓡 1).prod 𝓘(ℝ, ℝ × ℝ))
    (𝓡 3) (Circle × (ℝ × ℝ)) SphereCarrier.{0} ∞ :=
  standardCycleRim.trans (loopForm.neck 0 b)

private def loopUnion : PieceEmbedding (NoCuts.carrier standardThreeSphereLift.{0}) where
  Piece := solidTorusSet.{0}
  map := Subtype.val
  smooth := contMDiff_solidTorus_val
  mfderiv_bijective := solidTorusAtlas.mfderiv_subtypeVal_bijective
  injective := Subtype.val_injective

private theorem loopRim_source (b : Bool) : (loopRim b).source = univ ×ˢ rimBox 2 := by
  apply subset_antisymm
  · exact fun p hp => hp.1
  · intro p hp
    refine ⟨hp, ?_⟩
    change standardCycleRim p ∈ (loopForm.neck 0 b).source
    rw [loopForm.neck_source]
    have ht := standardCycleRim.map_source hp
    change 7 / 8 < ‖(standardCycleRim p).1‖ ∧
      ‖(standardCycleRim p).1‖ < 9 / 8 ∧ |(standardCycleRim p).2| < 1 / 8 at ht
    exact ⟨by change ‖(standardCycleRim p).1‖ < 1 + 2 * (1 / 16 : ℝ); linarith [ht.2.1],
      by change |(standardCycleRim p).2| < 2 * (1 / 16 : ℝ); linarith [ht.2.2]⟩

private theorem loopRim_disjoint : Disjoint (loopRim false).target (loopRim true).target :=
  (loopForm.neck_disjoint 0 false 0 true (by decide)).mono
    (fun x hx => hx.1) (fun x hx => hx.1)

private theorem loopRim_coordinates {b : Bool} {p : Circle × (ℝ × ℝ)}
    (hp : p ∈ (loopRim b).source) :
    standardCycleRim p ∈ neckDomain (1 / 16) ∧
      ‖(standardCycleRim p).1‖ = 1 + (1 / 16 : ℝ) * p.2.1 := by
  refine ⟨?_, ?_⟩
  · have hh : standardCycleRim p ∈ (loopForm.neck 0 b).source := hp.2
    rwa [loopForm.neck_source] at hh
  · change ‖(1 + (1 / 16 : ℝ) * p.2.1) • planeOfCircle p.1‖ = _
    have hpos : 0 ≤ 1 + (1 / 16 : ℝ) * p.2.1 := by
      have h := (abs_lt.mp hp.1.2.1).1
      linarith
    rw [norm_smul, Real.norm_of_nonneg hpos, planeOfCircle,
      LinearIsometryEquiv.norm_map, Circle.norm_coe, mul_one]

private theorem loopRim_ball {b : Bool} {p : Circle × (ℝ × ℝ)}
    (hp : p ∈ (loopRim b).source) : loopRim b p ∈ range loopBall.map ↔ p.2.2 ≤ 0 := by
  have hh := loopForm.neck_ball 0 b (loopRim_coordinates hp).1
  have he : rimBall 1 0 b = 0 := Subsingleton.elim _ _
  rw [he] at hh
  change loopForm.neck 0 b (standardCycleRim p) ∈ range (loopForm.ball 0) ↔ _
  rw [hh]
  change (1 / 16 : ℝ) * p.2.2 ≤ 0 ↔ p.2.2 ≤ 0
  constructor <;> intro h <;> linarith

private theorem loopRim_handle {b : Bool} {p : Circle × (ℝ × ℝ)}
    (hp : p ∈ (loopRim b).source) : loopRim b p ∈ range loopHandle.map ↔
      0 ≤ p.2.2 ∧ p.2.1 ≤ 0 := by
  change loopForm.neck 0 b (standardCycleRim p) ∈ range (loopForm.handle 0) ↔ _
  rw [loopForm.neck_handle 0 b (loopRim_coordinates hp).1, (loopRim_coordinates hp).2]
  change (0 ≤ (1 / 16 : ℝ) * p.2.2 ∧ 1 + (1 / 16 : ℝ) * p.2.1 ≤ 1) ↔ _
  constructor <;> intro h <;> constructor <;> linarith [h.1, h.2]

private theorem loopEnd_boundary (b : Bool) : loopHandle.endDisk b ⊆
    loopBall.map '' (𝓡∂ 3).boundary loopBall.Piece := by
  intro z hz
  obtain ⟨w, rfl⟩ := hz
  have hn : (w.val, (0 : ℝ)) ∈ neckDomain (1 / 16) := by
    refine ⟨?_, by norm_num⟩
    change ‖w.val‖ < 1 + 2 * (1 / 16 : ℝ)
    linarith [w.property]
  obtain ⟨v, hv, he⟩ := exists_capRegion_capMap_eq
    (show (0 : ℝ) < 1 / 16 by norm_num) (by norm_num) b hn le_rfl
  have hb : v ∈ (𝓡∂ 3).boundary (ClosedCell 3) := by
    rw [closedCell_boundary_eq_sphere 2]
    change ‖v.val‖ = 1
    have hheight := congrArg Prod.snd he
    cases b
    · change ‖v.val‖ - 1 = 0 at hheight
      linarith
    · change ‖reflectThree v.val‖ - 1 = 0 at hheight
      rw [norm_reflectThree] at hheight
      linarith
  refine ⟨v, hb, ?_⟩
  have he0 : rimBall 1 0 b = 0 := Subsingleton.elim _ _
  have hball := loopForm.ball_cap 0 b v hv
  rw [he0, he] at hball
  change loopForm.ball 0 v = loopForm.handle 0 (w, iccEnd b)
  rw [hball, loopForm.handle_end 0 b (w, iccEnd b) (by simp)]
  congr 1
  cases b <;> simp [handleEnd, endCoord, iccEnd]

private theorem loopRim_label (b : Bool) : loopRim b '' {p | p.2 = (0, 0)} =
    (fun w : ClosedCell 2 => loopHandle.map (w, iccEnd b)) '' diskRim := by
  have hθ (θ : Circle) : loopRim b (θ, (0, 0)) =
      loopHandle.map (circleRimPoint θ, iccEnd b) := by
    change loopForm.neck 0 b (neckRim (1 / 16) (θ, (0, 0))) =
      loopForm.handle 0 (circleRimPoint θ, iccEnd b)
    rw [loopForm.handle_end 0 b (circleRimPoint θ, iccEnd b) (by simp)]
    apply congrArg (loopForm.neck 0 b)
    cases b <;> simp [neckRim, handleEnd, endCoord, iccEnd, circleRimPoint_val, planeOfCircle]
  ext z
  constructor
  · rintro ⟨⟨θ, xy⟩, hxy, rfl⟩
    change xy = (0, 0) at hxy
    subst xy
    exact ⟨circleRimPoint θ, circleRimPoint_mem_diskRim θ, (hθ θ).symm⟩
  · rintro ⟨w, hw, rfl⟩
    obtain ⟨θ, hθw⟩ := exists_circleRimPoint_eq hw
    exact ⟨(θ, (0, 0)), rfl, hθw ▸ hθ θ⟩

private def loopRounding (z : SphereCarrier.{0}) : ℝ := by
  classical
  exact if z ∈ (loopRim false).target then standardRimRounding ((loopRim false).symm z).2
  else standardRimRounding ((loopRim true).symm z).2

private theorem loopRounding_pullback (b : Bool) (p : Circle × (ℝ × ℝ))
    (hp : p ∈ (loopRim b).source) :
    loopRounding (loopRim b p) = standardRimRounding p.2 := by
  classical
  cases b
  · rw [loopRounding, ite_eq_left ((loopRim false).map_source hp)]
    exact congrArg (fun q : Circle × (ℝ × ℝ) => standardRimRounding q.2)
      ((loopRim false).left_inv hp)
  · have hnot : loopRim true p ∉ (loopRim false).target :=
      fun h => Set.disjoint_left.mp loopRim_disjoint h ((loopRim true).map_source hp)
    rw [loopRounding, ite_eq_right hnot]
    exact congrArg (fun q : Circle × (ℝ × ℝ) => standardRimRounding q.2)
      ((loopRim true).left_inv hp)

private theorem loopRim_union {b : Bool} {p : Circle × (ℝ × ℝ)}
    (hp : p ∈ (loopRim b).source) :
    loopRim b p ∈ range loopUnion.map ↔ standardRimRounding p.2 ≤ 0 := by
  rw [show range loopUnion.map = solidTorusSet.{0} from Subtype.range_coe]
  change loopForm.neck 0 b (standardCycleRim p) ∈ solidTorusSet ↔ _
  rw [loopForm.neck_union 0 b (loopRim_coordinates hp).1]
  change standardRimRounding ((‖(standardCycleRim p).1‖ - 1) / (1 / 16),
    ((1 / 16 : ℝ) * p.2.2) / (1 / 16)) ≤ 0 ↔ _
  rw [(loopRim_coordinates hp).2]
  have hx : (1 + (1 / 16 : ℝ) * p.2.1 - 1) / (1 / 16) = p.2.1 := by ring
  have hy : ((1 / 16 : ℝ) * p.2.2) / (1 / 16) = p.2.2 := by ring
  rw [hx, hy]

private theorem loop_singleton_union (f : Fin 1 → Set SphereCarrier.{0}) :
    (⋃ k, f k) = f 0 := by
  ext z
  constructor
  · intro hz
    obtain ⟨k, hk⟩ := mem_iUnion.mp hz
    have he : k = 0 := Subsingleton.elim _ _
    exact he ▸ hk
  · exact fun hz => mem_iUnion.mpr ⟨0, hz⟩

private theorem loopUnion_away : range loopUnion.map \ (⋃ b, (loopRim b).target) =
    (range loopBall.map ∪ range loopHandle.map) \ (⋃ b, (loopRim b).target) := by
  ext z
  constructor
  · rintro ⟨hu, hz⟩
    refine ⟨?_, hz⟩
    have hmodel : z ∈ solidTorusSet := by
      change z ∈ range (Subtype.val : solidTorusSet.{0} → SphereCarrier.{0}) at hu
      rwa [Subtype.range_coe] at hu
    rw [loopForm.union_eq] at hmodel
    rcases hmodel with hraw | hneck
    · rw [loop_singleton_union, loop_singleton_union] at hraw
      exact hraw
    · obtain ⟨k, hk⟩ := mem_iUnion.mp hneck
      obtain ⟨b, q, hq, he⟩ := mem_iUnion.mp hk
      have hk0 : k = 0 := Subsingleton.elim _ _
      subst k
      subst z
      by_cases ht : q.2 ≤ 0
      · have he0 : rimBall 1 0 b = 0 := Subsingleton.elim _ _
        left
        exact (he0 ▸ loopForm.neck_ball 0 b hq.1).mpr ht
      · by_cases hw : ‖q.1‖ ≤ 1
        · exact Or.inr ((loopForm.neck_handle 0 b hq.1).mpr ⟨(not_le.mp ht).le, hw⟩)
        · have hs : q ∈ standardCycleRim.target := by
            change 7 / 8 < ‖q.1‖ ∧ ‖q.1‖ < 9 / 8 ∧ |q.2| < 1 / 8
            have hdom := hq.1
            change ‖q.1‖ < 1 + 2 * (1 / 16 : ℝ) ∧ |q.2| < 2 * (1 / 16 : ℝ) at hdom
            exact ⟨by linarith [not_le.mp hw], by linarith [hdom.1], by linarith [hdom.2]⟩
          have hn : q ∈ (loopForm.neck 0 b).source := by
            rw [loopForm.neck_source]
            exact hq.1
          have htarg : loopForm.neck 0 b q ∈ (loopRim b).target := by
            change loopForm.neck 0 b q ∈ (loopForm.neck 0 b).target ∧
              (loopForm.neck 0 b).symm (loopForm.neck 0 b q) ∈ standardCycleRim.target
            have hi := (loopForm.neck 0 b).left_inv hn
            exact ⟨(loopForm.neck 0 b).map_source hn, hi.symm ▸ hs⟩
          exact False.elim (hz (mem_iUnion.mpr ⟨b, htarg⟩))
  · rintro ⟨hu, hz⟩
    refine ⟨?_, hz⟩
    change z ∈ range (Subtype.val : solidTorusSet.{0} → SphereCarrier.{0})
    rw [Subtype.range_coe, loopForm.union_eq]
    left
    rw [loop_singleton_union, loop_singleton_union]
    exact hu

private theorem loopHandle_inter : range loopHandle.map ∩ range loopBall.map =
    loopHandle.endDisk false ∪ loopHandle.endDisk true := by
  have hends (b : Bool) : loopForm.handle 0 '' {q | q.2 = iccEnd b} = loopHandle.endDisk b := by
    ext z
    constructor
    · rintro ⟨⟨w, t⟩, ht, rfl⟩
      change t = iccEnd b at ht
      subst t
      exact ⟨w, rfl⟩
    · rintro ⟨w, rfl⟩
      exact ⟨(w, iccEnd b), rfl, rfl⟩
  change range (loopForm.handle 0) ∩ range (loopForm.ball 0) = _
  rw [loopForm.handle_ball_inter 0 0, ite_eq_left rfl,
    ite_eq_left (Subsingleton.elim (0 : Fin 1) (finRotate 1 0)), hends false, hends true]

def standardLoopBallHandleCycle : BallHandleCycle (NoCuts.carrier standardThreeSphereLift.{0}) :=
  BallHandleCycle.ofLoop loopBall (Diffeomorph.refl (𝓡∂ 3) (ClosedCell 3) ∞) loopHandle
    (loopEnd_boundary false) (loopEnd_boundary true) loopHandle_inter loopRim
    (fun b p => by rw [loopRim_source]; simp only [mem_prod, mem_univ, true_and])
    (fun _b _p hp => loopRim_ball hp) (fun _b _p hp => loopRim_handle hp)
    loopRim_label loopRim_disjoint loopRounding (Function.const Bool 1)
    (Function.const Bool zero_lt_one)
    (fun b p hp => by
      change loopRounding (loopRim b p) = 1 * standardRimRounding p.2
      rw [one_mul]
      exact loopRounding_pullback b p hp)
    loopUnion (fun _b _p hp => loopRim_union hp) loopUnion_away

theorem standardLoopBallHandleCycle_len : standardLoopBallHandleCycle.len = 1 := rfl

theorem standardLoopBallHandleCycle_union :
    range standardLoopBallHandleCycle.union.map = solidTorusSet.{0} := Subtype.range_coe

theorem standardLoopBallHandleCycle_rimProduct : standardLoopBallHandleCycle.RimProduct := by
  intro _k b
  refine ⟨1, by norm_num, by norm_num,
    LinearIsometryEquiv.refl ℝ (EuclideanSpace ℝ (Fin 2)),
    fun x : ℝ => 1 + (1 / 16) * x, fun y : ℝ => (1 / 16) * y,
    contDiff_const.add (contDiff_const.mul contDiff_id),
    contDiff_const.mul contDiff_id, by norm_num, by norm_num, ?_, ?_, ?_⟩
  · intro x hx
    refine ⟨by dsimp; linarith [hx.1], ?_⟩
    rw [deriv_const_add, deriv_const_mul_id]
    norm_num
  · intro y _hy
    rw [deriv_const_mul_id]
    norm_num
  · intro θ x y w t _hx _hx0 _hy _hy1 hw ht
    change loopForm.neck 0 b (neckRim (1 / 16) (θ, (x, y))) = loopForm.handle 0 (w, t)
    change (modelNeck (len := 1) (ε := (1 / 16 : ℝ)) (by norm_num)
      (by norm_num) (by norm_num) 0 b) (neckRim (1 / 16) (θ, (x, y))) =
      modelHandle 1 (1 / 16) 0 (w, t)
    rw [modelHandle_end (len := 1) (ε := (1 / 16 : ℝ))
      (by norm_num) (by norm_num) (by norm_num) 0 b (w, t)]
    apply congrArg (loopForm.neck 0 b)
    apply Prod.ext
    · exact hw.symm
    · change (1 / 16 : ℝ) * y = endCoord b (t : ℝ)
      rw [ht]
      cases b <;> simp [endCoord]

end GC.GraphManifold.Assembly
