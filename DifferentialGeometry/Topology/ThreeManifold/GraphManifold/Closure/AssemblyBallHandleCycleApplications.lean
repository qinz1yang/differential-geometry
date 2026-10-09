import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.AssemblyBallHandleCycle

/-!
# Chapter-14 assembly, item L1: consumers of the ball–handle cycle (group G1)

Regression for erratum E-L1: for a LOOP (`len = 1`, one ball and one handle whose two end disks lie
on the same ball) the new field `rim_quadrant` follows from the V2 fields `rim_ball` and
`rim_handle`, because the only pieces are the chart's own ball and handle. `BallHandleCycle.ofLoop`
builds the corrected structure from exactly the V2 data, and `BallHandleCycle.ofLoop_range_union`
reads off the set-level decomposition of the union (ball, handle and the two fillets).
-/

set_option autoImplicit false

noncomputable section

open Set Function
open DifferentialGeometry DifferentialGeometry.Topology GC.Endpoint GC.Seifert GC.GraphManifold Manifold
open scoped Manifold ContDiff Topology

universe u

namespace GC.GraphManifold.Assembly

local instance ballCharts_ASML1A : ChartedSpace (EuclideanHalfSpace 3) (ClosedCell 3) :=
  DifferentialGeometry.Topology.Handle.closedCellChartedSpaceSucc 2

local instance ballSmooth_ASML1A : IsManifold (𝓡∂ 3) ∞ (ClosedCell 3) :=
  DifferentialGeometry.Topology.Handle.closedCellIsManifold 2

local instance diskCharts_ASML1A : ChartedSpace (EuclideanHalfSpace 2) (ClosedCell 2) :=
  DifferentialGeometry.Topology.Handle.closedCellChartedSpaceSucc 1

namespace BallHandleCycle

variable {W : CompactCarrier.{u}}

theorem fin_one_eq (k j : Fin 1) : k = j := Subsingleton.elim k j

/-- **Loop regression (E-L1).** One ball and one handle attached to it at both ends, with the V2
rim and union data (no `rim_quadrant` input): the corrected `BallHandleCycle` with `len = 1`. -/
def ofLoop (ball : PieceEmbedding W) (ballModel : ball.Piece ≃ₘ⟮𝓡∂ 3, 𝓡∂ 3⟯ ClosedCell 3)
    (handle : EdgeHandle W)
    (start_face : handle.endDisk false ⊆ ball.map '' (𝓡∂ 3).boundary ball.Piece)
    (end_face : handle.endDisk true ⊆ ball.map '' (𝓡∂ 3).boundary ball.Piece)
    (inter : range handle.map ∩ range ball.map = handle.endDisk false ∪ handle.endDisk true)
    (rimChart : Bool →
      PartialDiffeomorph ((𝓡 1).prod 𝓘(ℝ, ℝ × ℝ)) W.model (Circle × (ℝ × ℝ)) W.Carrier ∞)
    (rim_source : ∀ b {p}, p ∈ (rimChart b).source ↔ p.2 ∈ rimBox 2)
    (rim_ball : ∀ b {p}, p ∈ (rimChart b).source → (rimChart b p ∈ range ball.map ↔ p.2.2 ≤ 0))
    (rim_handle : ∀ b {p}, p ∈ (rimChart b).source →
      (rimChart b p ∈ range handle.map ↔ (0 ≤ p.2.2 ∧ p.2.1 ≤ 0)))
    (rim_label : ∀ b, rimChart b '' {p | p.2 = (0, 0)} =
      (fun x : ClosedCell 2 => handle.map (x, iccEnd b)) '' diskRim)
    (rim_disjoint : Disjoint (rimChart false).target (rimChart true).target)
    (roundingFn : W.Carrier → ℝ) (rimScale : Bool → ℝ) (rimScale_pos : ∀ b, 0 < rimScale b)
    (rim_pullback : ∀ b p, p ∈ (rimChart b).source →
      roundingFn (rimChart b p) = rimScale b * standardRimRounding p.2)
    (union : PieceEmbedding W)
    (union_rim : ∀ b {p}, p ∈ (rimChart b).source →
      (rimChart b p ∈ range union.map ↔ standardRimRounding p.2 ≤ 0))
    (union_away : range union.map \ (⋃ b, (rimChart b).target) =
      (range ball.map ∪ range handle.map) \ (⋃ b, (rimChart b).target)) :
    BallHandleCycle W where
  len := 1
  len_pos := Nat.one_pos
  ball _ := ball
  ballModel _ := ballModel
  handle _ := handle
  start_face _ := start_face
  end_face _ := end_face
  handle_ball_inter k j := by
    rw [ite_eq_left (fin_one_eq j k), ite_eq_left (fin_one_eq j (finRotate 1 k))]
    exact inter
  ball_disjoint k k' hk := (hk (fin_one_eq k k')).elim
  handle_disjoint k k' hk := (hk (fin_one_eq k k')).elim
  rimChart _ b := rimChart b
  rim_source _ b := rim_source b
  rim_ball _ b _ hp := rim_ball b hp
  rim_handle _ b _ hp := rim_handle b hp
  rim_quadrant _ b p hp hx hy := by
    rintro (hz | hz)
    · obtain ⟨_, hj⟩ := Set.mem_iUnion.mp hz
      exact absurd ((rim_ball b hp).mp hj) (not_le.mpr hy)
    · obtain ⟨_, hj⟩ := Set.mem_iUnion.mp hz
      exact absurd ((rim_handle b hp).mp hj).2 (not_le.mpr hx)
  rim_label _ b := rim_label b
  rim_disjoint k b k' b' hne := by
    have hkk : k = k' := fin_one_eq k k'
    subst hkk
    have hb : b ≠ b' := fun h => hne (by rw [h])
    cases b <;> cases b'
    · exact (hb rfl).elim
    · exact rim_disjoint
    · exact rim_disjoint.symm
    · exact (hb rfl).elim
  roundingFn := roundingFn
  rimScale _ b := rimScale b
  rimScale_pos _ b := rimScale_pos b
  rim_pullback _ b := rim_pullback b
  union := union
  union_rim _ b _ hp := union_rim b hp
  union_away := by
    simp only [iUnion_const]
    exact union_away

/-- **Consumer.** The union of a loop is the ball, the handle and the two fillets. -/
theorem ofLoop_range_union (ball : PieceEmbedding W)
    (ballModel : ball.Piece ≃ₘ⟮𝓡∂ 3, 𝓡∂ 3⟯ ClosedCell 3) (handle : EdgeHandle W)
    (start_face : handle.endDisk false ⊆ ball.map '' (𝓡∂ 3).boundary ball.Piece)
    (end_face : handle.endDisk true ⊆ ball.map '' (𝓡∂ 3).boundary ball.Piece)
    (inter : range handle.map ∩ range ball.map = handle.endDisk false ∪ handle.endDisk true)
    (rimChart : Bool →
      PartialDiffeomorph ((𝓡 1).prod 𝓘(ℝ, ℝ × ℝ)) W.model (Circle × (ℝ × ℝ)) W.Carrier ∞)
    (rim_source : ∀ b {p}, p ∈ (rimChart b).source ↔ p.2 ∈ rimBox 2)
    (rim_ball : ∀ b {p}, p ∈ (rimChart b).source → (rimChart b p ∈ range ball.map ↔ p.2.2 ≤ 0))
    (rim_handle : ∀ b {p}, p ∈ (rimChart b).source →
      (rimChart b p ∈ range handle.map ↔ (0 ≤ p.2.2 ∧ p.2.1 ≤ 0)))
    (rim_label : ∀ b, rimChart b '' {p | p.2 = (0, 0)} =
      (fun x : ClosedCell 2 => handle.map (x, iccEnd b)) '' diskRim)
    (rim_disjoint : Disjoint (rimChart false).target (rimChart true).target)
    (roundingFn : W.Carrier → ℝ) (rimScale : Bool → ℝ) (rimScale_pos : ∀ b, 0 < rimScale b)
    (rim_pullback : ∀ b p, p ∈ (rimChart b).source →
      roundingFn (rimChart b p) = rimScale b * standardRimRounding p.2)
    (union : PieceEmbedding W)
    (union_rim : ∀ b {p}, p ∈ (rimChart b).source →
      (rimChart b p ∈ range union.map ↔ standardRimRounding p.2 ≤ 0))
    (union_away : range union.map \ (⋃ b, (rimChart b).target) =
      (range ball.map ∪ range handle.map) \ (⋃ b, (rimChart b).target)) :
    range union.map = (range ball.map ∪ range handle.map) ∪
      ⋃ b, rimChart b '' {p | 0 < p.2.1 ∧ 0 < p.2.2 ∧ p.2 ∈ rimBox 1 ∧
        standardRimRounding p.2 ≤ 0} := by
  have h := (ofLoop ball ballModel handle start_face end_face inter rimChart rim_source rim_ball
    rim_handle rim_label rim_disjoint roundingFn rimScale rimScale_pos rim_pullback union union_rim
    union_away).range_union_eq
  simp only [ofLoop, fillet, iUnion_const] at h
  exact h

end BallHandleCycle

end GC.GraphManifold.Assembly
