import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.AssemblyL1NecksSlices
import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.AssemblyL1NecksFlip
import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.AssemblyL1NecksBallChart

/-!
# Chapter-14 assembly, item L1, G3b / T1′: consumers of the slices, flips and ball charts

Lane ASM-L1e, group A. One consumer per main theorem of `AssemblyL1NecksSlices`,
`AssemblyL1NecksFlip` and `AssemblyL1NecksBallChart`, in the form the neck construction uses them:

* `BallHandleCycle.exists_rimSlice_nhds`: the rim slices of a cycle have pairwise disjoint open
  neighbourhoods (`isCompact_rimSlice`, `disjoint_rimSlice`, `exists_pairwise_disjoint_open_nhds`);
* `BallHandleCycle.rimHeight_lt_one`: a product height of a rim stays below `1`
  (`rimHeight_lt` against the other end at height `0`);
* `exists_flipNeck_neckPreservesAt_iff`: every neck on a neck domain can be flipped to preserve or
  reverse the orientation of `W` at its centre, as prescribed (`neckPreservesAt_flipNeck_iff`,
  `exists_linearIsometryEquiv_det_neg`);
* `BallHandleCycle.exists_ballCharts`: under `hint`, every ball of the cycle has a ball chart
  (`PieceEmbedding.exists_ballChart`), in which the ball is the closed unit ball
  (`ballChart_mem_range_iff`).
-/

set_option autoImplicit false

noncomputable section

open Set Function Manifold Metric
open DifferentialGeometry DifferentialGeometry.Topology GC.Endpoint
open scoped Manifold ContDiff Topology

universe u

namespace GC.GraphManifold.Assembly

local instance ballCharts_ASML1eA : ChartedSpace (EuclideanHalfSpace 3) (ClosedCell 3) :=
  DifferentialGeometry.Topology.Handle.closedCellChartedSpaceSucc 2

local instance diskCharts_ASML1eA : ChartedSpace (EuclideanHalfSpace 2) (ClosedCell 2) :=
  DifferentialGeometry.Topology.Handle.closedCellChartedSpaceSucc 1

/-- The rim slices of a cycle have pairwise disjoint open neighbourhoods. -/
theorem BallHandleCycle.exists_rimSlice_nhds {W : CompactCarrier.{u}} (C : BallHandleCycle W) :
    ∃ O : Fin C.len × Bool → Set W.Carrier, (∀ p, IsOpen (O p)) ∧
      (∀ p, C.rimSlice p.1 p.2 ⊆ O p) ∧ Pairwise (Disjoint on O) :=
  exists_pairwise_disjoint_open_nhds (K := fun p : Fin C.len × Bool => C.rimSlice p.1 p.2)
    (fun p => C.isCompact_rimSlice p.1 p.2) (fun _ _ hpp' => C.disjoint_rimSlice hpp')

/-- A product height of the rim `false` of a handle stays below `1`. -/
theorem BallHandleCycle.rimHeight_lt_one {W : CompactCarrier.{u}} (C : BallHandleCycle W)
    (k : Fin C.len) {a₀ a₁ : ℝ} (ha₀ : 3 / 4 < a₀) (ha₀' : a₀ ≤ 2) (ha₁ : 3 / 4 < a₁)
    (ha₁' : a₁ ≤ 2)
    (A₀ A₁ : EuclideanSpace ℝ (Fin 2) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin 2))
    {ρ₀ σ₀ ρ₁ σ₁ : ℝ → ℝ} (hσ₀ : ContDiff ℝ ∞ σ₀) (hσ₁ : ContDiff ℝ ∞ σ₁)
    (hρ₀0 : ρ₀ 0 = 1) (hρ₁0 : ρ₁ 0 = 1) (hσ₀0 : σ₀ 0 = 0) (hσ₁0 : σ₁ 0 = 0)
    (hσ₀d : ∀ y ∈ Ico 0 a₀, 0 < deriv σ₀ y) (hσ₁d : ∀ y ∈ Ico 0 a₁, 0 < deriv σ₁ y)
    (heq₀ : ∀ (θ : Circle) (x y : ℝ) (w : ClosedCell 2) (t : Icc (0 : ℝ) 1),
      -a₀ < x → x ≤ 0 → 0 ≤ y → y < a₀ →
      (w : EuclideanSpace ℝ (Fin 2)) = ρ₀ x • A₀ (planeOfCircle θ) →
      (t : ℝ) = endCoord false (σ₀ y) → C.rimChart k false (θ, (x, y)) = (C.handle k).map (w, t))
    (heq₁ : ∀ (θ : Circle) (x y : ℝ) (w : ClosedCell 2) (t : Icc (0 : ℝ) 1),
      -a₁ < x → x ≤ 0 → 0 ≤ y → y < a₁ →
      (w : EuclideanSpace ℝ (Fin 2)) = ρ₁ x • A₁ (planeOfCircle θ) →
      (t : ℝ) = endCoord true (σ₁ y) → C.rimChart k true (θ, (x, y)) = (C.handle k).map (w, t))
    {y₀ : ℝ} (hy₀ : y₀ ∈ Ico 0 a₀) : σ₀ y₀ < 1 := by
  have h := C.rimHeight_lt k ha₀ ha₀' ha₁ ha₁' A₀ A₁ hσ₀ hσ₁ hρ₀0 hρ₁0 hσ₀0 hσ₁0 hσ₀d hσ₁d
    heq₀ heq₁ hy₀ (⟨le_rfl, by linarith⟩ : (0 : ℝ) ∈ Ico 0 a₁)
  rw [hσ₁0, sub_zero] at h
  exact h

/-- Every neck on a neck domain can be flipped to have a prescribed orientation behaviour at
its centre. -/
theorem exists_flipNeck_neckPreservesAt_iff {W : CompactCarrier.{u}}
    (N : PartialDiffeomorph 𝓘(ℝ, EuclideanSpace ℝ (Fin 2) × ℝ) W.model
      (EuclideanSpace ℝ (Fin 2) × ℝ) W.Carrier ∞) {ε' : ℝ} (hε' : 0 < ε')
    (hN : N.source = neckDomain ε') (P : Prop) :
    ∃ F : EuclideanSpace ℝ (Fin 2) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin 2),
      NeckPreservesAt (flipNeck N F) 0 ↔ P := by
  classical
  obtain ⟨R, hR⟩ := exists_linearIsometryEquiv_det_neg
  by_cases h : (NeckPreservesAt N 0 ↔ P)
  · refine ⟨LinearIsometryEquiv.refl ℝ _, ?_⟩
    rw [neckPreservesAt_flipNeck_iff hε' hN]
    have h1 : LinearMap.det (LinearIsometryEquiv.refl ℝ
        (EuclideanSpace ℝ (Fin 2))).toLinearMap = 1 := LinearMap.det_id
    rw [h1]
    simp only [zero_lt_one, iff_true]
    exact h
  · refine ⟨R, ?_⟩
    rw [neckPreservesAt_flipNeck_iff hε' hN]
    have h2 : ¬ (0 < LinearMap.det R.toLinearMap) := not_lt.mpr hR.le
    simp only [h2, iff_false]
    tauto

/-- Under `hint`, every ball of a cycle has a ball chart, in which the ball is the closed unit
ball. -/
theorem BallHandleCycle.exists_ballCharts {W : CompactCarrier.{u}} (C : BallHandleCycle W)
    (hint : ∀ k, range (C.ball k).map ⊆ (W.interior : Set W.Carrier)) :
    ∃ φ : Fin C.len → PartialDiffeomorph (𝓡 3) W.model (EuclideanSpace ℝ (Fin 3)) W.Carrier ∞,
      ∀ j, closedBall 0 1 ⊆ (φ j).source ∧
        (∀ x : ClosedCell 3, φ j x.val = (C.ball j).map ((C.ballModel j).symm x)) ∧
        ∀ {y}, y ∈ (φ j).source → (φ j y ∈ range (C.ball j).map ↔ ‖y‖ ≤ 1) := by
  have h := fun j => (C.ball j).exists_ballChart (C.ballModel j) (hint j)
  choose φ hsrc _ hφ using h
  exact ⟨φ, fun j => ⟨hsrc j, hφ j, fun hy =>
    ballChart_mem_range_iff (C.ball j) (C.ballModel j) (φ j) (hsrc j) (hφ j) hy⟩⟩

end GC.GraphManifold.Assembly
