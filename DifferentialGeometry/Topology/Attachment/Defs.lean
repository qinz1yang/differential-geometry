import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Topology.Constructions

namespace DifferentialGeometry.Topology

universe u v w

abbrev ClosedCell (n : ℕ) : Type :=
  {x : EuclideanSpace ℝ (Fin n) // ‖x‖ ≤ 1}

abbrev CellBoundary (n : ℕ) : Type :=
  {x : EuclideanSpace ℝ (Fin n) // ‖x‖ = 1}

abbrev CellInterior (n : ℕ) : Type :=
  {x : EuclideanSpace ℝ (Fin n) // ‖x‖ < 1}

def cellBoundaryInclusion (n : ℕ) : CellBoundary n → ClosedCell n :=
  fun x => ⟨x, le_of_eq x.2⟩

def closedCellCenter (n : ℕ) : ClosedCell n :=
  ⟨0, by simp⟩

instance closedCellCompactSpace (k : ℕ) : CompactSpace (ClosedCell k) := by
  let f : ClosedCell k → Metric.closedBall (0 : EuclideanSpace ℝ (Fin k)) 1 :=
    fun x => ⟨(x : EuclideanSpace ℝ (Fin k)), by simpa [Metric.mem_closedBall, dist_eq_norm] using x.2⟩
  let g : Metric.closedBall (0 : EuclideanSpace ℝ (Fin k)) 1 → ClosedCell k :=
    fun y => ⟨(y : EuclideanSpace ℝ (Fin k)), by
      have hy : ‖(y : EuclideanSpace ℝ (Fin k))‖ ≤ 1 := by
        have hmem : dist (y : EuclideanSpace ℝ (Fin k)) 0 ≤ 1 := y.2
        simpa [dist_eq_norm] using hmem
      exact hy⟩
  let e : ClosedCell k ≃ₜ Metric.closedBall (0 : EuclideanSpace ℝ (Fin k)) 1 :=
    { toEquiv :=
        { toFun := f
          invFun := g
          left_inv := by intro x; apply Subtype.ext; rfl
          right_inv := by intro y; apply Subtype.ext; rfl }
      continuous_toFun := by
        have hcomp : (fun x : ClosedCell k =>
            ((f x : Metric.closedBall (0 : EuclideanSpace ℝ (Fin k)) 1) : EuclideanSpace ℝ (Fin k))) =
            fun x : ClosedCell k => (x : EuclideanSpace ℝ (Fin k)) := by
          funext x
          rfl
        exact (Topology.IsInducing.subtypeVal.continuous_iff).2 (by
          change Continuous (fun x : ClosedCell k =>
            ((f x : Metric.closedBall (0 : EuclideanSpace ℝ (Fin k)) 1) : EuclideanSpace ℝ (Fin k)))
          rw [hcomp]
          exact continuous_subtype_val)
      continuous_invFun := by
        have hcomp : (fun y : Metric.closedBall (0 : EuclideanSpace ℝ (Fin k)) 1 =>
            ((g y : ClosedCell k) : EuclideanSpace ℝ (Fin k))) =
            fun y : Metric.closedBall (0 : EuclideanSpace ℝ (Fin k)) 1 => (y : EuclideanSpace ℝ (Fin k)) := by
          funext y
          rfl
        exact (Topology.IsInducing.subtypeVal.continuous_iff).2 (by
          change Continuous (fun y : Metric.closedBall (0 : EuclideanSpace ℝ (Fin k)) 1 =>
            ((g y : ClosedCell k) : EuclideanSpace ℝ (Fin k)))
          rw [hcomp]
          exact continuous_subtype_val) }
  exact e.symm.compactSpace

def cellInteriorInclusion (n : ℕ) : CellInterior n → ClosedCell n :=
  fun x => ⟨x, le_of_lt x.2⟩

def adjunctionRel {A : Type v} {B : Type w} {X : Type u} (i : A → B) (φ : A → X) :
    B ⊕ X → B ⊕ X → Prop :=
  fun a b =>
    ∃ x : A,
      (a = Sum.inl (i x) ∧ b = Sum.inr (φ x)) ∨
        (b = Sum.inl (i x) ∧ a = Sum.inr (φ x))

abbrev AdjunctionSpace {A : Type v} {B : Type w} {X : Type u} (i : A → B) (φ : A → X) :
    Type (max w u) :=
  Quot (adjunctionRel i φ)

def adjunctionMk {A : Type v} {B : Type w} {X : Type u} (i : A → B) (φ : A → X) :
    B ⊕ X → AdjunctionSpace i φ :=
  Quot.mk (adjunctionRel i φ)

def adjunctionLower {A : Type v} {B : Type w} {X : Type u} {i : A → B} (φ : A → X) :
    X → AdjunctionSpace i φ :=
  fun x => adjunctionMk i φ (Sum.inr x)

def adjunctionCell {A : Type v} {B : Type w} {X : Type u} (i : A → B) (φ : A → X) :
    B → AdjunctionSpace i φ :=
  fun d => adjunctionMk i φ (Sum.inl d)

theorem adjunction_coherence {A : Type v} {B : Type w} {X : Type u} (i : A → B) (φ : A → X)
    (x : A) :
    adjunctionCell i φ (i x) = adjunctionLower φ (φ x) :=
  Quot.sound ⟨x, Or.inl ⟨rfl, rfl⟩⟩

abbrev CellAdjunctionSpace {X : Type u} (n : ℕ) (φ : CellBoundary n → X) : Type u :=
  AdjunctionSpace (cellBoundaryInclusion n) φ

end DifferentialGeometry.Topology
