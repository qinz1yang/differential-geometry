import DifferentialGeometry.Topology.PiecewiseLinear.SimplexBoundary
import Mathlib.Analysis.Normed.Affine.AddTorsorBases

open Set

namespace DifferentialGeometry.Topology.PiecewiseLinear

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem frontier_convexHull_eq_biUnion_erase [DecidableEq E] (T : Finset E)
    (hT : AffineIndependent ℝ ((↑) : T → E)) (hspan : affineSpan ℝ (T : Set E) = ⊤) :
    frontier (convexHull ℝ (T : Set E)) =
      ⋃ v ∈ T, convexHull ℝ ((T.erase v : Finset E) : Set E) := by
  classical
  let b : AffineBasis T ℝ E :=
    ⟨((↑) : T → E), hT, by
      have hrange : range ((↑) : T → E) = (T : Set E) := Subtype.range_coe
      exact (congrArg (affineSpan ℝ) hrange).trans hspan⟩
  have hrange : range b = (T : Set E) := Subtype.range_coe
  have hclosed : IsClosed (convexHull ℝ (T : Set E)) :=
    (T.finite_toSet.isCompact_convexHull ℝ).isClosed
  have hface (v : T) (x : E) :
      x ∈ convexHull ℝ ((T.erase v.1 : Finset E) : Set E) ↔
        (∀ i, 0 ≤ b.coord i x) ∧ b.coord v x = 0 := by
    have himage : b '' ((Finset.univ.erase v : Finset T) : Set T) =
        ((T.erase v.1 : Finset E) : Set E) := by
      ext y
      constructor
      · rintro ⟨i, hi, rfl⟩
        exact Finset.mem_erase.mpr
          ⟨fun h => (Finset.mem_erase.mp hi).1 (Subtype.ext h), i.2⟩
      · intro hy
        refine ⟨⟨y, (Finset.mem_erase.mp hy).2⟩, ?_, rfl⟩
        exact Finset.mem_erase.mpr
          ⟨fun h => (Finset.mem_erase.mp hy).1 (congrArg Subtype.val h), Finset.mem_univ _⟩
    rw [← himage, mem_convexHull_image_affineBasis_iff]
    simp only [Finset.mem_erase, Finset.mem_univ, and_true, not_not, forall_eq]
  have hfront : frontier (convexHull ℝ (T : Set E)) =
      {x | (∀ i, 0 ≤ b.coord i x) ∧ ¬ ∀ i, 0 < b.coord i x} := by
    rw [hclosed.frontier_eq, ← hrange, b.interior_convexHull, b.convexHull_eq_nonneg_coord]
    rfl
  rw [hfront]
  ext x
  simp only [mem_ofPred_eq, mem_iUnion]
  constructor
  · rintro ⟨h0, hpos⟩
    obtain ⟨i, hi⟩ := not_forall.mp hpos
    exact ⟨i.1, i.2, (hface i x).mpr ⟨h0, le_antisymm (not_lt.mp hi) (h0 i)⟩⟩
  · rintro ⟨v, hv, hx⟩
    obtain ⟨h0, hzero⟩ := (hface ⟨v, hv⟩ x).mp hx
    exact ⟨h0, fun hpos => (ne_of_gt (hpos ⟨v, hv⟩)) hzero⟩

theorem isPLSphere_frontier_convexHull {n : ℕ} (T : Finset E)
    (hT : AffineIndependent ℝ ((↑) : T → E)) (hspan : affineSpan ℝ (T : Set E) = ⊤)
    (hcard : T.card = n + 2) : IsPLSphere n (frontier (convexHull ℝ (T : Set E))) := by
  classical
  let b : AffineBasis T ℝ E :=
    ⟨((↑) : T → E), hT, by
      have hrange : range ((↑) : T → E) = (T : Set E) := Subtype.range_coe
      exact (congrArg (affineSpan ℝ) hrange).trans hspan⟩
  let _ := b.finiteDimensional
  rw [frontier_convexHull_eq_biUnion_erase T hT hspan]
  exact isPLSphere_biUnion_erase T hT hcard

end DifferentialGeometry.Topology.PiecewiseLinear
