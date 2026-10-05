import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.AssemblySphereRecCellChart
import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.AssemblyPieces

/-!
# Chapter-14 assembly, item L1, G3b / T1′: the ball chart of a ball in the interior

Lane ASM-L1e. A ball of a ball–handle cycle is a `PieceEmbedding` `B` with a model diffeomorphism
`e : B.Piece ≃ₘ ClosedCell 3`; with the hypothesis `hint` (its image lies in the interior of `W`)
the closed cell `B.map ∘ e⁻¹` extends to a partial diffeomorphism `B̂` from an open subset of `ℝ³`
containing the closed unit ball into `W` (`PieceEmbedding.exists_ballChart`). This is the chart in
which the ball side of the necks is built (Euclidean convex combinations and Seeley extensions).

* `exists_ballChart_of_closedCell_interior_bijective`: an injective smooth closed `3`-cell of
  bijective differential with values interior points of a `3`-manifold `M` (with or without
  boundary) extends to a ball chart into `M`. The boundaryless case is lane ASM-SPH's
  `exists_ballChart_of_closedCell_bijective` (`Closure/AssemblySphereRecCellChart.lean`), applied in
  the intrinsic interior with its interior atlas; the chart is transported back as in
  `exists_ballChart_of_closedCell_interior` (`Closure/AssemblySphereCutBallChart.lean`).
* `PieceEmbedding.exists_ballChart`: the ball chart of a ball in the interior.
* `ballChart_mem_range_iff`: a point of the chart lies in the ball iff its coordinate lies in
  the closed unit ball (injectivity of the chart).
-/

set_option autoImplicit false

noncomputable section

open Set Function Manifold Metric
open DifferentialGeometry DifferentialGeometry.Topology GC.Endpoint
open scoped Manifold ContDiff Topology

universe u

namespace GC.GraphManifold.Assembly

local instance ballCharts_ASML1eB : ChartedSpace (EuclideanHalfSpace 3) (ClosedCell 3) :=
  DifferentialGeometry.Topology.Handle.closedCellChartedSpaceSucc 2

local instance ballSmooth_ASML1eB : IsManifold (𝓡∂ 3) ∞ (ClosedCell 3) :=
  DifferentialGeometry.Topology.Handle.closedCellIsManifold 2

section Interior

variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ (EuclideanSpace ℝ (Fin 3)) H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M]

/-- **Ball chart of an interior full-rank closed cell.** -/
theorem exists_ballChart_of_closedCell_interior_bijective (c : ClosedCell 3 → M)
    (hc : ContMDiff (𝓡∂ 3) I ∞ c) (hinj : Injective c)
    (hcb : ∀ x, Bijective (mfderiv (𝓡∂ 3) I c x)) (hcI : ∀ x, I.IsInteriorPoint (c x)) :
    ∃ φ : PartialDiffeomorph (𝓡 3) I (EuclideanSpace ℝ (Fin 3)) M ∞,
      closedBall 0 1 ⊆ φ.source ∧ (∀ y ∈ φ.target, I.IsInteriorPoint y) ∧
        ∀ x : ClosedCell 3, φ x.val = c x := by
  let U : TopologicalSpace.Opens M :=
    DifferentialGeometry.Manifold.intrinsicInterior I ∞ (by simp)
  let c' : ClosedCell 3 → U := fun x => ⟨c x, hcI x⟩
  obtain ⟨hc', hcb'⟩ := cell_restrict_properties U c' hc hcb
  let := DifferentialGeometry.Manifold.interiorChartedSpace I ∞ (M := U)
  have := DifferentialGeometry.Manifold.interiorIsManifold I ∞ (M := U)
  let D := DifferentialGeometry.Manifold.interiorAtlasDiffeomorph I ∞ (M := U)
  have hDb : ∀ y : U, Bijective (mfderiv I (𝓡 3) D y) := fun y =>
    (D.mfderivToContinuousLinearEquiv (by simp) y).bijective
  have hA : ContMDiff (𝓡∂ 3) (𝓡 3) ∞ (D ∘ c') := D.contMDiff.comp hc'
  have hAb : ∀ x, Bijective (mfderiv (𝓡∂ 3) (𝓡 3) (D ∘ c') x) := by
    intro x
    rw [mfderiv_comp x (D.contMDiff.mdifferentiableAt (by simp))
      (hc'.mdifferentiableAt (by simp))]
    exact (hDb (c' x)).comp (hcb' x)
  have hAi : Injective (D ∘ c') := fun x y h => hinj (congrArg Subtype.val h)
  obtain ⟨φ, hsrc, hφ⟩ := exists_ballChart_of_closedCell_bijective (D ∘ c') hA hAi hAb
  have hne : Nonempty U := ⟨c' ⟨0, by simp⟩⟩
  let Φ := (φ.trans D.symm.toPartialDiffeomorph).trans
    (DifferentialGeometry.Manifold.openSubtypePartialDiffeomorph I U hne)
  refine ⟨Φ, ?_, ?_, ?_⟩
  · intro x hx
    exact ⟨⟨hsrc hx, trivial⟩, trivial⟩
  · intro y hy
    have hy' : y ∈ (DifferentialGeometry.Manifold.openSubtypePartialDiffeomorph I U hne).target :=
      hy.1
    rw [DifferentialGeometry.Manifold.openSubtypePartialDiffeomorph_target] at hy'
    exact hy'
  · intro x
    change ((φ x.val : U) : M) = c x
    rw [hφ x]
    rfl

end Interior

/-- **The ball chart of a ball in the interior of `W`.** -/
theorem PieceEmbedding.exists_ballChart {W : CompactCarrier.{u}} (B : PieceEmbedding W)
    (e : B.Piece ≃ₘ⟮𝓡∂ 3, 𝓡∂ 3⟯ ClosedCell 3)
    (hint : range B.map ⊆ (W.interior : Set W.Carrier)) :
    ∃ φ : PartialDiffeomorph (𝓡 3) W.model (EuclideanSpace ℝ (Fin 3)) W.Carrier ∞,
      closedBall 0 1 ⊆ φ.source ∧ (∀ y ∈ φ.target, W.model.IsInteriorPoint y) ∧
        ∀ x : ClosedCell 3, φ x.val = B.map (e.symm x) := by
  have hc : ContMDiff (𝓡∂ 3) W.model ∞ (B.map ∘ e.symm) := B.smooth.comp e.symm.contMDiff
  have hcb : ∀ x, Bijective (mfderiv (𝓡∂ 3) W.model (B.map ∘ e.symm) x) := by
    intro x
    rw [mfderiv_comp x (B.smooth.mdifferentiableAt (by simp))
      (e.symm.contMDiff.mdifferentiableAt (by simp))]
    exact (B.mfderiv_bijective _).comp (e.symm.mfderivToContinuousLinearEquiv (by simp) x).bijective
  exact exists_ballChart_of_closedCell_interior_bijective (B.map ∘ e.symm) hc
    (B.injective.comp e.symm.injective) hcb (fun x => hint ⟨_, rfl⟩)

/-- A point of the ball chart lies in the ball iff its coordinate lies in the closed unit ball. -/
theorem ballChart_mem_range_iff {W : CompactCarrier.{u}} (B : PieceEmbedding W)
    (e : B.Piece ≃ₘ⟮𝓡∂ 3, 𝓡∂ 3⟯ ClosedCell 3)
    (φ : PartialDiffeomorph (𝓡 3) W.model (EuclideanSpace ℝ (Fin 3)) W.Carrier ∞)
    (hsrc : closedBall 0 1 ⊆ φ.source) (hφ : ∀ x : ClosedCell 3, φ x.val = B.map (e.symm x))
    {y : EuclideanSpace ℝ (Fin 3)} (hy : y ∈ φ.source) :
    φ y ∈ range B.map ↔ ‖y‖ ≤ 1 := by
  constructor
  · rintro ⟨p, hp⟩
    have hxs : ((e p : ClosedCell 3) : EuclideanSpace ℝ (Fin 3)) ∈ φ.source :=
      hsrc (mem_closedBall_zero_iff.mpr (e p).2)
    have heq : φ ((e p : ClosedCell 3) : EuclideanSpace ℝ (Fin 3)) = φ y := by
      rw [hφ, Diffeomorph.symm_apply_apply, hp]
    rw [← φ.toPartialEquiv.injOn hxs hy heq]
    exact (e p).2
  · intro h
    exact ⟨e.symm ⟨y, h⟩, (hφ ⟨y, h⟩).symm⟩

end GC.GraphManifold.Assembly
