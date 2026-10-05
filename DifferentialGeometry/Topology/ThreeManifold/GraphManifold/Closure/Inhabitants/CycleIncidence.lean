import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.Inhabitants.CycleHandles
import DifferentialGeometry.Topology.Manifold.StereographicAntipodal
import DifferentialGeometry.Topology.Manifold.ClosedCellInterior

/-!
The actual two stereographic vertices meet each of the two polar handles exactly at its
prescribed ends. The radial incidence calculation uses the true antipodal radius-four image.
-/

set_option autoImplicit false

noncomputable section

open Set Function Metric Manifold DifferentialGeometry DifferentialGeometry.Topology
open DifferentialGeometry.Topology.Manifold DifferentialGeometry.Manifold GC.Endpoint
open scoped Manifold ContDiff

namespace GC.GraphManifold.Assembly

attribute [local instance] Handle.closedCellChartedSpaceSucc Handle.closedCellIsManifold

local instance cycleIncidenceDimension :
    Fact (Module.finrank ℝ (EuclideanSpace ℝ (Fin 4)) = 3 + 1) := ⟨by simp⟩

theorem cycleBall_false_mem {v : EuclideanSpace ℝ (Fin 3)} :
    cycleBallAmbient false v ∈ range (cycleBallPiece false).map ↔ ‖v‖ ≤ 1 := by
  constructor
  · rintro ⟨x, hx⟩
    have he := (cycleBallAmbient false).injOn
      (by rw [cycleBallAmbient_source]; exact mem_univ _)
      (by rw [cycleBallAmbient_source]; exact mem_univ _) hx
    change x.val = v at he
    simpa only [he] using x.property
  · intro hv
    exact ⟨⟨v, hv⟩, rfl⟩

theorem cycleBall_true_mem {v : EuclideanSpace ℝ (Fin 3)} :
    cycleBallAmbient false v ∈ range (cycleBallPiece true).map ↔ 4 ≤ ‖v‖ := by
  have hm := mem_antipodal_stereographic_symm_closedBall cycleBallPole
    (by norm_num : (0 : ℝ) < 4) v
  constructor
  · rintro ⟨x, hx⟩
    have he := congrArg ULift.down hx
    change (cycleBallAmbient true x.val).down = (cycleBallAmbient false v).down at he
    rw [cycleBallAmbient_apply, cycleBallAmbient_apply] at he
    simp only [Bool.false_eq_true, ↓reduceIte] at he
    apply hm.mp
    refine ⟨x.val, ?_, ?_⟩
    · simpa only [div_self (by norm_num : (4 : ℝ) ≠ 0), mem_closedBall_zero_iff]
        using x.property
    · change (stereographic' 3 cycleBallPole).symm x.val =
        -(stereographic' 3 cycleBallPole).symm v
      simpa only [neg_neg] using congrArg
        (fun z : sphere (0 : EuclideanSpace ℝ (Fin 4)) 1 => -z) he
  · intro hv
    obtain ⟨x, hx, he⟩ := hm.mpr hv
    refine ⟨⟨x, ?_⟩, ?_⟩
    · simpa only [div_self (by norm_num : (4 : ℝ) ≠ 0), mem_closedBall_zero_iff] using hx
    · apply ULift.ext
      change (cycleBallAmbient true x).down = (cycleBallAmbient false v).down
      rw [cycleBallAmbient_apply, cycleBallAmbient_apply]
      simp only [Bool.false_eq_true, ↓reduceIte]
      change -(stereographic' 3 cycleBallPole).symm x =
        (stereographic' 3 cycleBallPole).symm v
      simpa only [neg_neg] using congrArg
        (fun z : sphere (0 : EuclideanSpace ℝ (Fin 4)) 1 => -z) he

private theorem cycleHandleRadius_zero : cycleHandleRadius 0 = 1 := by
  rw [cycleHandleRadius_inner (by norm_num)]
  norm_num

private theorem cycleHandleRadius_one : cycleHandleRadius 1 = 4 := by
  rw [cycleHandleRadius_outer (by norm_num)]
  norm_num

private theorem cycleHandleRadius_bounds {t : ℝ} (ht : t ∈ Icc 0 1) :
    1 ≤ cycleHandleRadius t ∧ cycleHandleRadius t ≤ 4 := by
  have hl := cycleHandleRadius_strictMono.monotoneOn (show (0 : ℝ) ∈ Icc 0 1 by norm_num)
    ht ht.1
  have hu := cycleHandleRadius_strictMono.monotoneOn ht
    (show (1 : ℝ) ∈ Icc 0 1 by norm_num) ht.2
  simpa only [cycleHandleRadius_zero, cycleHandleRadius_one] using And.intro hl hu

theorem cycleHandleRadius_eq_one {t : ℝ} (ht : t ∈ Icc 0 1) :
    cycleHandleRadius t = 1 ↔ t = 0 := by
  constructor
  · intro he
    exact cycleHandleRadius_strictMono.injOn ht (by norm_num) (he.trans
      cycleHandleRadius_zero.symm)
  · rintro rfl
    exact cycleHandleRadius_zero

theorem cycleHandleRadius_eq_four {t : ℝ} (ht : t ∈ Icc 0 1) :
    cycleHandleRadius t = 4 ↔ t = 1 := by
  constructor
  · intro he
    exact cycleHandleRadius_strictMono.injOn ht (by norm_num) (he.trans
      cycleHandleRadius_one.symm)
  · rintro rfl
    exact cycleHandleRadius_one

theorem cycleS3Handle_ball_false {b : Bool} {p : ClosedCell 2 × Icc (0 : ℝ) 1} :
    (cycleS3Handle b).map p ∈ range (cycleBallPiece false).map ↔
      p.2.val = if b then 1 else 0 := by
  change cycleHandleChart b (p.1.val, p.2.val) ∈ _ ↔ _
  rw [cycleHandleChart_apply, cycleBall_false_mem]
  have ht : (if b then 1 - p.2.val else p.2.val) ∈ Icc (0 : ℝ) 1 := by
    cases b <;> simp only [Bool.false_eq_true, ↓reduceIte] <;>
      constructor <;> linarith [p.2.property.1, p.2.property.2]
  have hun : ∀ θ : sphere (0 : EuclideanSpace ℝ (Fin 3)) 1,
      ‖(θ : EuclideanSpace ℝ (Fin 3))‖ = 1 := by
    intro θ
    simpa only [mem_sphere_zero_iff_norm] using θ.property
  rw [norm_smul, hun, mul_one, Real.norm_eq_abs,
    abs_of_nonneg (by linarith [cycleHandleRadius_bounds ht])]
  have he := cycleHandleRadius_eq_one ht
  have hb := cycleHandleRadius_bounds ht
  cases b <;> simp only [Bool.false_eq_true, ↓reduceIte] at he ⊢ <;>
    constructor
  · intro hh
    exact he.mp (le_antisymm hh hb.1)
  · intro hh
    rw [hh, cycleHandleRadius_zero]
  · intro hh
    have h := he.mp (le_antisymm hh hb.1)
    linarith
  · intro hh
    have h : 1 - p.2.val = 0 := by linarith
    rw [h, cycleHandleRadius_zero]

theorem cycleS3Handle_ball_true {b : Bool} {p : ClosedCell 2 × Icc (0 : ℝ) 1} :
    (cycleS3Handle b).map p ∈ range (cycleBallPiece true).map ↔
      p.2.val = if b then 0 else 1 := by
  change cycleHandleChart b (p.1.val, p.2.val) ∈ _ ↔ _
  rw [cycleHandleChart_apply, cycleBall_true_mem]
  have ht : (if b then 1 - p.2.val else p.2.val) ∈ Icc (0 : ℝ) 1 := by
    cases b <;> simp only [Bool.false_eq_true, ↓reduceIte] <;>
      constructor <;> linarith [p.2.property.1, p.2.property.2]
  have hun : ∀ θ : sphere (0 : EuclideanSpace ℝ (Fin 3)) 1,
      ‖(θ : EuclideanSpace ℝ (Fin 3))‖ = 1 := by
    intro θ
    simpa only [mem_sphere_zero_iff_norm] using θ.property
  rw [norm_smul, hun, mul_one, Real.norm_eq_abs,
    abs_of_nonneg (by linarith [cycleHandleRadius_bounds ht])]
  have he := cycleHandleRadius_eq_four ht
  have hb := cycleHandleRadius_bounds ht
  cases b <;> simp only [Bool.false_eq_true, ↓reduceIte] at he ⊢ <;>
    constructor
  · intro hh
    exact he.mp (le_antisymm hb.2 hh)
  · intro hh
    rw [hh, cycleHandleRadius_one]
  · intro hh
    have h := he.mp (le_antisymm hb.2 hh)
    linarith
  · intro hh
    have h : 1 - p.2.val = 1 := by linarith
    rw [h, cycleHandleRadius_one]

theorem cycleBall_false_boundary {v : EuclideanSpace ℝ (Fin 3)} (hv : ‖v‖ = 1) :
    cycleBallAmbient false v ∈
      (cycleBallPiece false).map '' (𝓡∂ 3).boundary (cycleBallPiece false).Piece := by
  refine ⟨⟨v, hv.le⟩, ?_, rfl⟩
  change (⟨v, hv.le⟩ : ClosedCell 3) ∈ (𝓡∂ 3).boundary (ClosedCell 3)
  rw [closedCell_boundary_eq_sphere 2]
  exact hv

theorem cycleBall_true_boundary {v : EuclideanSpace ℝ (Fin 3)} (hv : ‖v‖ = 4) :
    cycleBallAmbient false v ∈
      (cycleBallPiece true).map '' (𝓡∂ 3).boundary (cycleBallPiece true).Piece := by
  let x : EuclideanSpace ℝ (Fin 3) := (-1 / 4 : ℝ) • v
  have hx : ‖x‖ = 1 := by
    dsimp [x]
    rw [norm_smul, Real.norm_eq_abs, hv]
    norm_num
  refine ⟨⟨x, hx.le⟩, ?_, ?_⟩
  · change (⟨x, hx.le⟩ : ClosedCell 3) ∈ (𝓡∂ 3).boundary (ClosedCell 3)
    rw [closedCell_boundary_eq_sphere 2]
    exact hx
  · have he : (-4 / ‖x‖ ^ 2) • x = v := by
      rw [hx]
      dsimp [x]
      rw [smul_smul]
      norm_num
    have hst := stereographicInverse_antipodal cycleBallPole x
      (norm_pos_iff.mp (by linarith [hx]))
    rw [he] at hst
    apply ULift.ext
    change (cycleBallAmbient true x).down = (cycleBallAmbient false v).down
    rw [cycleBallAmbient_apply, cycleBallAmbient_apply]
    simp only [Bool.false_eq_true, ↓reduceIte]
    exact hst.symm

theorem cycleS3Handle_endpoint_boundary (b e : Bool) :
    (cycleS3Handle b).endDisk e ⊆
      (cycleBallPiece (Bool.xor b e)).map ''
        (𝓡∂ 3).boundary (cycleBallPiece (Bool.xor b e)).Piece := by
  rintro z ⟨x, rfl⟩
  change cycleHandleChart b (x.val, (iccEnd e).val) ∈ _
  rw [cycleHandleChart_apply]
  have hun : ∀ θ : sphere (0 : EuclideanSpace ℝ (Fin 3)) 1,
      ‖(θ : EuclideanSpace ℝ (Fin 3))‖ = 1 := by
    intro θ
    exact mem_sphere_zero_iff_norm.mp θ.property
  cases b <;> cases e
  · apply cycleBall_false_boundary
    simp only [iccEnd, Bool.false_eq_true, ↓reduceIte, cycleHandleRadius_zero,
      norm_smul, Real.norm_eq_abs, abs_one, hun, mul_one]
  · apply cycleBall_true_boundary
    simp only [iccEnd, ↓reduceIte, Bool.false_eq_true, cycleHandleRadius_one,
      norm_smul, Real.norm_eq_abs, hun, mul_one]
    norm_num
  · apply cycleBall_true_boundary
    simp only [iccEnd, Bool.false_eq_true, ↓reduceIte, sub_zero, cycleHandleRadius_one,
      norm_smul, Real.norm_eq_abs, hun, mul_one]
    norm_num
  · apply cycleBall_false_boundary
    simp only [iccEnd, ↓reduceIte, sub_self, cycleHandleRadius_zero,
      norm_smul, Real.norm_eq_abs, abs_one, hun, mul_one]

theorem cycleS3Handle_ball_inter (b v : Bool) :
    range (cycleS3Handle b).map ∩ range (cycleBallPiece v).map =
      (if v = b then (cycleS3Handle b).endDisk false else ∅) ∪
        (if v = !b then (cycleS3Handle b).endDisk true else ∅) := by
  cases b <;> cases v <;>
    simp only [Bool.false_eq_true, Bool.true_eq_false, Bool.not_false, Bool.not_true, ↓reduceIte,
      union_empty,
      empty_union]
  all_goals
    ext z
    constructor
  · rintro ⟨⟨p, rfl⟩, hp⟩
    have ht := cycleS3Handle_ball_false.mp hp
    have he : p.2 = iccEnd false := Subtype.ext ht
    exact ⟨p.1, by rw [← he]⟩
  · rintro ⟨x, rfl⟩
    exact ⟨⟨(x, iccEnd false), rfl⟩, cycleS3Handle_ball_false.mpr rfl⟩
  · rintro ⟨⟨p, rfl⟩, hp⟩
    have ht := cycleS3Handle_ball_true.mp hp
    have he : p.2 = iccEnd true := Subtype.ext ht
    exact ⟨p.1, by rw [← he]⟩
  · rintro ⟨x, rfl⟩
    exact ⟨⟨(x, iccEnd true), rfl⟩, cycleS3Handle_ball_true.mpr rfl⟩
  · rintro ⟨⟨p, rfl⟩, hp⟩
    have ht := cycleS3Handle_ball_false.mp hp
    have he : p.2 = iccEnd true := Subtype.ext ht
    exact ⟨p.1, by rw [← he]⟩
  · rintro ⟨x, rfl⟩
    exact ⟨⟨(x, iccEnd true), rfl⟩, cycleS3Handle_ball_false.mpr rfl⟩
  · rintro ⟨⟨p, rfl⟩, hp⟩
    have ht := cycleS3Handle_ball_true.mp hp
    have he : p.2 = iccEnd false := Subtype.ext ht
    exact ⟨p.1, by rw [← he]⟩
  · rintro ⟨x, rfl⟩
    exact ⟨⟨(x, iccEnd false), rfl⟩, cycleS3Handle_ball_true.mpr rfl⟩

end GC.GraphManifold.Assembly
