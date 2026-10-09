import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.Inhabitants.CycleForm
import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.Inhabitants.CycleRim
import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.AssemblyBallHandleCycle
import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.AssemblyL1StandardFacts
import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.AssemblyDiskOrientedIsotopy
import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.AssemblySphereCutCapped
import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Sphere
import DifferentialGeometry.Topology.Manifold.SmoothBoundaryAtlas.Tangent

/-!
The accepted two-piece rotational model is assembled on its same fixed regular solid-torus
sublevel, retaining the actual four rims, their local rounding and the complete union geometry.
-/

set_option autoImplicit false

noncomputable section

open Set Function Metric Manifold DifferentialGeometry DifferentialGeometry.Topology
open DifferentialGeometry.Topology.Manifold GC.Endpoint GC.GraphManifold
open scoped Manifold ContDiff Topology

namespace GC.GraphManifold.Assembly

attribute [local instance] Handle.closedCellChartedSpaceSucc Handle.closedCellIsManifold

local instance cycleInstanceBallConnected : ConnectedSpace (ClosedCell 3) :=
  closedCell_three_connectedSpace

local instance cycleInstanceSphereSecond : SecondCountableTopology SphereCarrier.{0} :=
  secondCountableTopology_sphereCarrier

private def cycleInstanceModel : ModelCycleNormalForm.{0} 2 (1 / 16) :=
  modelCycleNormalForm (by norm_num) (by norm_num) (by norm_num)

private def cycleInstanceBall (k : Fin 2) :
    PieceEmbedding (NoCuts.carrier standardThreeSphereLift.{0}) where
  Piece := ClosedCell 3
  map := cycleInstanceModel.ball k
  smooth := cycleInstanceModel.ball_smooth k
  mfderiv_bijective := cycleInstanceModel.ball_mfderiv k
  injective := cycleInstanceModel.ball_injective k

private def cycleInstanceHandle (k : Fin 2) :
    EdgeHandle (NoCuts.carrier standardThreeSphereLift.{0}) where
  map := cycleInstanceModel.handle k
  smooth := cycleInstanceModel.handle_smooth k
  mfderiv_bijective := cycleInstanceModel.handle_mfderiv k
  injective := cycleInstanceModel.handle_injective k
  interior := by intro q hq; exact BoundarylessManifold.isInteriorPoint

private def cycleInstanceUnion : PieceEmbedding (NoCuts.carrier standardThreeSphereLift.{0}) where
  Piece := solidTorusSet.{0}
  map := Subtype.val
  smooth := contMDiff_solidTorus_val
  mfderiv_bijective := solidTorusAtlas.mfderiv_subtypeVal_bijective
  injective := Subtype.val_injective

private def cycleInstanceRim (k : Fin 2) (b : Bool) :
    PartialDiffeomorph ((𝓡 1).prod 𝓘(ℝ, ℝ × ℝ)) (𝓡 3)
      (Circle × (ℝ × ℝ)) SphereCarrier.{0} ∞ :=
  standardCycleRim.trans (cycleInstanceModel.neck k b)

private theorem cycleInstanceRim_source (k : Fin 2) (b : Bool) :
    (cycleInstanceRim k b).source = univ ×ˢ rimBox 2 := by
  ext p
  change (p ∈ standardCycleRim.source ∧
    standardCycleRim p ∈ (cycleInstanceModel.neck k b).source) ↔ _
  constructor
  · exact fun hp => hp.1
  · intro hp
    refine ⟨hp, ?_⟩
    rw [cycleInstanceModel.neck_source]
    have ht := standardCycleRim.map_source hp
    change 7 / 8 < ‖(standardCycleRim p).1‖ ∧
      ‖(standardCycleRim p).1‖ < 9 / 8 ∧ |(standardCycleRim p).2| < 1 / 8 at ht
    change ‖(standardCycleRim p).1‖ < 1 + 2 * (1 / 16 : ℝ) ∧
      |(standardCycleRim p).2| < 2 * (1 / 16 : ℝ)
    constructor <;> linarith [ht.2.1, ht.2.2]

private theorem cycleInstanceRim_disjoint {k k' : Fin 2} {b b' : Bool}
    (h : (k, b) ≠ (k', b')) :
    Disjoint (cycleInstanceRim k b).target (cycleInstanceRim k' b').target :=
  (cycleInstanceModel.neck_disjoint k b k' b' h).mono
    (fun x hx => show x ∈ (cycleInstanceModel.neck k b).target from hx.1)
    (fun x hx => show x ∈ (cycleInstanceModel.neck k' b').target from hx.1)

private theorem cycleInstanceRim_neck {k : Fin 2} {b : Bool} {p : Circle × (ℝ × ℝ)}
    (hp : p ∈ (cycleInstanceRim k b).source) :
    standardCycleRim p ∈ neckDomain (1 / 16) := by
  have hh : standardCycleRim p ∈ (cycleInstanceModel.neck k b).source := hp.2
  rwa [cycleInstanceModel.neck_source] at hh

private theorem cycleInstanceRim_norm {k : Fin 2} {b : Bool} {p : Circle × (ℝ × ℝ)}
    (hp : p ∈ (cycleInstanceRim k b).source) :
    ‖(standardCycleRim p).1‖ = 1 + (1 / 16 : ℝ) * p.2.1 := by
  have hx : -2 < p.2.1 := (abs_lt.mp hp.1.2.1).1
  change ‖(1 + (1 / 16 : ℝ) * p.2.1) • planeOfCircle p.1‖ = _
  rw [norm_smul, Real.norm_of_nonneg (by linarith), planeOfCircle,
    LinearIsometryEquiv.norm_map, Circle.norm_coe, mul_one]

private theorem cycleInstanceRim_ball {k : Fin 2} {b : Bool} {p : Circle × (ℝ × ℝ)}
    (hp : p ∈ (cycleInstanceRim k b).source) :
    cycleInstanceRim k b p ∈ range (cycleInstanceBall (rimBall 2 k b)).map ↔ p.2.2 ≤ 0 := by
  change cycleInstanceModel.neck k b (standardCycleRim p) ∈
    range (cycleInstanceModel.ball (rimBall 2 k b)) ↔ _
  rw [cycleInstanceModel.neck_ball k b (cycleInstanceRim_neck hp)]
  change (1 / 16 : ℝ) * p.2.2 ≤ 0 ↔ p.2.2 ≤ 0
  constructor <;> intro h <;> linarith

private theorem cycleInstanceRim_handle {k : Fin 2} {b : Bool} {p : Circle × (ℝ × ℝ)}
    (hp : p ∈ (cycleInstanceRim k b).source) :
    cycleInstanceRim k b p ∈ range (cycleInstanceHandle k).map ↔
      0 ≤ p.2.2 ∧ p.2.1 ≤ 0 := by
  change cycleInstanceModel.neck k b (standardCycleRim p) ∈
    range (cycleInstanceModel.handle k) ↔ _
  rw [cycleInstanceModel.neck_handle k b (cycleInstanceRim_neck hp),
    cycleInstanceRim_norm hp]
  change (0 ≤ (1 / 16 : ℝ) * p.2.2 ∧ 1 + (1 / 16 : ℝ) * p.2.1 ≤ 1) ↔ _
  constructor
  · intro h
    constructor <;> linarith [h.1, h.2]
  · intro h
    constructor <;> linarith [h.1, h.2]

private theorem cycleInstanceRim_quadrant (k : Fin 2) (b : Bool) (p : Circle × (ℝ × ℝ))
    (hp : p ∈ (cycleInstanceRim k b).source) (hx : 0 < p.2.1) (hy : 0 < p.2.2) :
    cycleInstanceRim k b p ∉ (⋃ j, range (cycleInstanceBall j).map) ∪
      ⋃ j, range (cycleInstanceHandle j).map := by
  intro h
  have hh := cycleInstanceModel.neck_pieces k b ⟨(cycleInstanceModel.neck k b).map_source
    (by rw [cycleInstanceModel.neck_source]; exact cycleInstanceRim_neck hp), h⟩
  rcases hh with hb | hhandle
  · have hle := (cycleInstanceRim_ball hp).mp hb
    linarith
  · have hle := (cycleInstanceRim_handle hp).mp hhandle
    linarith [hle.2]

private theorem cycleInstanceRim_label (k : Fin 2) (b : Bool) :
    cycleInstanceRim k b '' {p | p.2 = (0, 0)} =
      (fun x : ClosedCell 2 => (cycleInstanceHandle k).map (x, iccEnd b)) '' diskRim := by
  have heq : ∀ θ : Circle, cycleInstanceRim k b (θ, (0, 0)) =
      (cycleInstanceHandle k).map (circleRimPoint θ, iccEnd b) := by
    intro θ
    change cycleInstanceModel.neck k b (standardCycleRim (θ, (0, 0))) =
      cycleInstanceModel.handle k (circleRimPoint θ, iccEnd b)
    rw [cycleInstanceModel.handle_end k b _ (by simp)]
    congr 1
    cases b <;> simp [standardCycleRim, neckRim, handleEnd, endCoord,
      iccEnd, circleRimPoint_val, planeOfCircle]
  ext x
  constructor
  · rintro ⟨⟨θ, v⟩, hv, rfl⟩
    change v = (0, 0) at hv
    subst v
    exact ⟨circleRimPoint θ, circleRimPoint_mem_diskRim θ, (heq θ).symm⟩
  · rintro ⟨z, hz, rfl⟩
    obtain ⟨θ, rfl⟩ := exists_circleRimPoint_eq hz
    exact ⟨(θ, (0, 0)), rfl, heq θ⟩

private theorem cycleInstanceEndpoint_boundary (k : Fin 2) (b : Bool) :
    (cycleInstanceHandle k).endDisk b ⊆
      (cycleInstanceBall (rimBall 2 k b)).map ''
        (𝓡∂ 3).boundary (cycleInstanceBall (rimBall 2 k b)).Piece := by
  rintro y ⟨p, rfl⟩
  obtain ⟨x, hx, hcap⟩ := exists_capRegion_capMap_eq
    (show (0 : ℝ) < 1 / 16 by norm_num) (by norm_num) b
      (q := (p.val, 0)) (by
        change ‖p.val‖ < 1 + 2 * (1 / 16 : ℝ) ∧ |(0 : ℝ)| < 2 * (1 / 16 : ℝ)
        constructor
        · linarith [p.property]
        · norm_num) le_rfl
  have hxn : ‖x.val‖ = 1 := by
    have hh := congrArg Prod.snd hcap
    cases b
    · change ‖x.val‖ - 1 = 0 at hh
      linarith
    · change ‖reflectThree x.val‖ - 1 = 0 at hh
      rw [norm_reflectThree] at hh
      linarith
  refine ⟨x, ?_, ?_⟩
  · change x ∈ (𝓡∂ 3).boundary (ClosedCell 3)
    rw [closedCell_boundary_eq_sphere 2]
    exact hxn
  · change cycleInstanceModel.ball (rimBall 2 k b) x = cycleInstanceModel.handle k (p, iccEnd b)
    rw [cycleInstanceModel.ball_cap k b x hx, hcap,
      cycleInstanceModel.handle_end k b (p, iccEnd b) (by simp)]
    congr 1
    apply Prod.ext
    · rfl
    · cases b <;> simp [handleEnd, endCoord, iccEnd]

private def cycleInstanceRimIndex (x : SphereCarrier.{0}) : Fin 2 × Bool := by
  classical
  exact if hx : ∃ i : Fin 2 × Bool, x ∈ (cycleInstanceRim i.1 i.2).target then
    Classical.choose hx else (0, false)

private theorem cycleInstanceRimIndex_eq {k : Fin 2} {b : Bool} {x : SphereCarrier.{0}}
    (hx : x ∈ (cycleInstanceRim k b).target) : cycleInstanceRimIndex x = (k, b) := by
  classical
  have hex : ∃ i : Fin 2 × Bool, x ∈ (cycleInstanceRim i.1 i.2).target := ⟨(k, b), hx⟩
  unfold cycleInstanceRimIndex
  rw [dite_eq_left hex]
  by_contra h
  exact Set.disjoint_left.mp (cycleInstanceRim_disjoint h)
    (Classical.choose_spec hex) hx

private def cycleInstanceRounding (x : SphereCarrier.{0}) : ℝ :=
  standardRimRounding
    (((cycleInstanceRim (cycleInstanceRimIndex x).1 (cycleInstanceRimIndex x).2).symm x).2)

private theorem cycleInstanceRounding_pullback (k : Fin 2) (b : Bool)
    (p : Circle × (ℝ × ℝ)) (hp : p ∈ (cycleInstanceRim k b).source) :
    cycleInstanceRounding (cycleInstanceRim k b p) = standardRimRounding p.2 := by
  unfold cycleInstanceRounding
  rw [cycleInstanceRimIndex_eq ((cycleInstanceRim k b).map_source hp)]
  exact congrArg (fun q : Circle × (ℝ × ℝ) => standardRimRounding q.2)
    ((cycleInstanceRim k b).left_inv hp)

private theorem cycleInstanceRim_union {k : Fin 2} {b : Bool} {p : Circle × (ℝ × ℝ)}
    (hp : p ∈ (cycleInstanceRim k b).source) :
    cycleInstanceRim k b p ∈ range cycleInstanceUnion.map ↔ standardRimRounding p.2 ≤ 0 := by
  have hr : range cycleInstanceUnion.map = solidTorusSet.{0} := Subtype.range_coe
  rw [hr]
  change cycleInstanceModel.neck k b (standardCycleRim p) ∈ solidTorusSet ↔ _
  rw [cycleInstanceModel.neck_union k b (cycleInstanceRim_neck hp)]
  have hn := cycleInstanceRim_norm hp
  change standardRimRounding ((‖(standardCycleRim p).1‖ - 1) / (1 / 16),
    (standardCycleRim p).2 / (1 / 16)) ≤ 0 ↔ _
  rw [hn]
  have hx : (1 + (1 / 16 : ℝ) * p.2.1 - 1) / (1 / 16) = p.2.1 := by ring
  have hy : (standardCycleRim p).2 / (1 / 16 : ℝ) = p.2.2 := by
    change ((1 / 16 : ℝ) * p.2.2) / (1 / 16) = p.2.2
    ring
  rw [hx, hy]

private theorem cycleInstanceUnion_away :
    range cycleInstanceUnion.map \ (⋃ k, ⋃ b, (cycleInstanceRim k b).target) =
      ((⋃ k, range (cycleInstanceBall k).map) ∪ ⋃ k, range (cycleInstanceHandle k).map) \
        (⋃ k, ⋃ b, (cycleInstanceRim k b).target) := by
  ext x
  constructor
  · rintro ⟨hx, hnot⟩
    have hu : x ∈ solidTorusSet := by
      rwa [show range cycleInstanceUnion.map = solidTorusSet.{0} from Subtype.range_coe] at hx
    rw [cycleInstanceModel.union_eq] at hu
    refine ⟨?_, hnot⟩
    rcases hu with hraw | hneck
    · exact hraw
    · obtain ⟨k, b, q, hq, rfl⟩ := mem_iUnion.mp hneck |>.imp fun k hk =>
        (mem_iUnion.mp hk).imp fun b hb => hb
      by_cases hy : q.2 ≤ 0
      · exact Or.inl (mem_iUnion.mpr ⟨rimBall 2 k b,
          (cycleInstanceModel.neck_ball k b hq.1).mpr hy⟩)
      · by_cases hx : ‖q.1‖ ≤ 1
        · exact Or.inr (mem_iUnion.mpr ⟨k,
            (cycleInstanceModel.neck_handle k b hq.1).mpr ⟨(not_le.mp hy).le, hx⟩⟩)
        · have hqt : q ∈ standardCycleRim.target := by
            change 7 / 8 < ‖q.1‖ ∧ ‖q.1‖ < 9 / 8 ∧ |q.2| < 1 / 8
            have hn := hq.1
            change ‖q.1‖ < 1 + 2 * (1 / 16 : ℝ) ∧ |q.2| < 2 * (1 / 16 : ℝ) at hn
            exact ⟨by linarith [not_le.mp hx], by linarith [hn.1], by linarith [hn.2]⟩
          have hround : standardCycleRim (standardCycleRim.symm q) = q :=
            standardCycleRim.right_inv hqt
          have hp : standardCycleRim.symm q ∈ (cycleInstanceRim k b).source := by
            refine ⟨standardCycleRim.map_target hqt, ?_⟩
            change standardCycleRim (standardCycleRim.symm q) ∈
              (cycleInstanceModel.neck k b).source
            rw [hround, cycleInstanceModel.neck_source]
            exact hq.1
          have he : cycleInstanceRim k b (standardCycleRim.symm q) =
              cycleInstanceModel.neck k b q := by
            change cycleInstanceModel.neck k b (standardCycleRim (standardCycleRim.symm q)) = _
            rw [hround]
          exact False.elim (hnot (mem_iUnion.mpr ⟨k, mem_iUnion.mpr ⟨b,
            he ▸ (cycleInstanceRim k b).map_source hp⟩⟩))
  · rintro ⟨hraw, hnot⟩
    refine ⟨?_, hnot⟩
    rw [show range cycleInstanceUnion.map = solidTorusSet.{0} from Subtype.range_coe,
      cycleInstanceModel.union_eq]
    exact Or.inl hraw

private theorem cycleInstanceHandle_endImage (k : Fin 2) (b : Bool) :
    cycleInstanceModel.handle k '' {q | q.2 = iccEnd b} =
      (cycleInstanceHandle k).endDisk b := by
  ext z
  constructor
  · rintro ⟨⟨x, t⟩, ht, rfl⟩
    change t = iccEnd b at ht
    subst t
    exact ⟨x, rfl⟩
  · rintro ⟨x, rfl⟩
    exact ⟨(x, iccEnd b), rfl, rfl⟩

def standardBallHandleCycle : BallHandleCycle (NoCuts.carrier standardThreeSphereLift.{0}) where
  len := 2
  len_pos := by norm_num
  ball := cycleInstanceBall
  ballModel := Function.const (Fin 2) (Diffeomorph.refl (𝓡∂ 3) (ClosedCell 3) ∞)
  handle := cycleInstanceHandle
  start_face k := cycleInstanceEndpoint_boundary k false
  end_face k := cycleInstanceEndpoint_boundary k true
  handle_ball_inter k j := by
    change range (cycleInstanceModel.handle k) ∩ range (cycleInstanceModel.ball j) = _
    rw [cycleInstanceModel.handle_ball_inter k j, cycleInstanceHandle_endImage k false,
      cycleInstanceHandle_endImage k true]
  ball_disjoint := cycleInstanceModel.ball_disjoint
  handle_disjoint := cycleInstanceModel.handle_disjoint
  rimChart := cycleInstanceRim
  rim_source k b p := by
    rw [cycleInstanceRim_source]
    simp only [mem_prod, mem_univ, true_and]
  rim_ball := fun _k _b => cycleInstanceRim_ball
  rim_handle := fun _k _b => cycleInstanceRim_handle
  rim_quadrant := cycleInstanceRim_quadrant
  rim_label := cycleInstanceRim_label
  rim_disjoint := fun _k _b _k' _b' => cycleInstanceRim_disjoint
  roundingFn := cycleInstanceRounding
  rimScale := Function.const (Fin 2) (Function.const Bool 1)
  rimScale_pos := fun _k _b => zero_lt_one
  rim_pullback k b p hp := by simpa using cycleInstanceRounding_pullback k b p hp
  union := cycleInstanceUnion
  union_rim := fun _k _b => cycleInstanceRim_union
  union_away := cycleInstanceUnion_away

theorem standardBallHandleCycle_len : standardBallHandleCycle.len = 2 := rfl

theorem standardBallHandleCycle_union :
    range standardBallHandleCycle.union.map = solidTorusSet.{0} := Subtype.range_coe

end GC.GraphManifold.Assembly
