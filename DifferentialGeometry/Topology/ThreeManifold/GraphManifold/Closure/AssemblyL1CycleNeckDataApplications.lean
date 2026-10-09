import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.AssemblyL1CycleNeckData
import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.AssemblyL1ModelNormalFormApplications

/-!
# Consumers of G3b′ from neck data (lane ASM-L1b3, group G2a)

* `BallHandleCycle.nonempty_solidTorus_of_neckData`: L1 from the neck data of T1′ — the normal
  form of `BallHandleCycle.cycleNormalForm_of_neckData` glued to the model normal form
  (`BallHandleCycle.nonempty_diffeomorph_of_cycleNormalForm`) gives a diffeomorphism of the
  standard solid torus onto the union piece of the cycle.
* `ballRim_eq_iff`: `ballRim` inverts `rimBall` at a fixed end.
-/

set_option autoImplicit false

noncomputable section

open Set Function
open DifferentialGeometry DifferentialGeometry.Topology GC.Endpoint GC.Seifert GC.GraphManifold Manifold
open scoped Manifold ContDiff Topology

universe u

namespace GC.GraphManifold.Assembly

local instance diskCharts_ASML1b3E : ChartedSpace (EuclideanHalfSpace 2) (ClosedCell 2) :=
  DifferentialGeometry.Topology.Handle.closedCellChartedSpaceSucc 1

local instance ballCharts_ASML1b3E : ChartedSpace (EuclideanHalfSpace 3) (ClosedCell 3) :=
  DifferentialGeometry.Topology.Handle.closedCellChartedSpaceSucc 2

/-- `ballRim len · b` and `rimBall len · b` are inverse to each other. -/
theorem ballRim_eq_iff {len : ℕ} {j k : Fin len} {b : Bool} :
    ballRim len j b = k ↔ rimBall len k b = j := by
  constructor
  · rintro rfl
    exact rimBall_ballRim len j b
  · rintro rfl
    exact ballRim_rimBall len k b

/-- **L1 from the neck data of T1′.** -/
theorem BallHandleCycle.nonempty_solidTorus_of_neckData {W : CompactCarrier.{u}}
    (C : BallHandleCycle W) {ε : ℝ} (hε : 0 < ε) (hε' : ε ≤ 1 / 8)
    (N : Fin C.len → Bool → PartialDiffeomorph 𝓘(ℝ, EuclideanSpace ℝ (Fin 2) × ℝ) W.model
      (EuclideanSpace ℝ (Fin 2) × ℝ) W.Carrier ∞)
    (hsrc : ∀ k b, closedNeckDomain ε ⊆ (N k b).source)
    (hdisj : ∀ k b k' b', (k, b) ≠ (k', b') → Disjoint (N k b).target (N k' b').target)
    (hball : ∀ k b {q}, q ∈ (N k b).source →
      (N k b q ∈ range (C.ball (rimBall C.len k b)).map ↔ q.2 ≤ 0))
    (hhandle : ∀ k b {q}, q ∈ (N k b).source →
      (N k b q ∈ range (C.handle k).map ↔ (0 ≤ q.2 ∧ ‖q.1‖ ≤ 1)))
    (hunion : ∀ k b {q}, q ∈ neckDomain ε → (N k b q ∈ range C.union.map ↔ neckRounding ε q ≤ 0))
    (hpieces : ∀ k b, (N k b).target ∩ ((⋃ j, range (C.ball j).map) ∪
      ⋃ j, range (C.handle j).map) ⊆
        range (C.ball (rimBall C.len k b)).map ∪ range (C.handle k).map)
    (hfillet : ∀ k b, C.fillet k b ⊆ N k b '' {q | q ∈ neckDomain ε ∧ neckRounding ε q ≤ 0})
    (hprodN : ∀ k, ∃ A : Bool → EuclideanSpace ℝ (Fin 2) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin 2),
      LinearMap.det (A false).toLinearMap = LinearMap.det (A true).toLinearMap ∧
      ∃ P T : Bool → ℝ → ℝ, (∀ b, ContDiff ℝ ∞ (P b)) ∧ (∀ b, ContDiff ℝ ∞ (T b)) ∧
        (∀ b, P b 1 = 1) ∧ (∀ b s, 0 ≤ s → s ≤ 1 → 0 < P b s) ∧
        (∀ b r, 0 ≤ r → r ≤ 1 → 0 < deriv (fun r : ℝ => r * P b (r ^ 2)) r) ∧
        (∀ b, T b 0 = 0) ∧ (∀ b s, 0 ≤ s → s ≤ 2 * ε → 0 < deriv (T b) s) ∧
        T false (2 * ε) < 1 - T true (2 * ε) ∧
        ∀ b (z : ClosedCell 2) (τ : ℝ) (w : ClosedCell 2) (t : Icc (0 : ℝ) 1),
          0 ≤ τ → τ < 2 * ε →
          (w : EuclideanSpace ℝ (Fin 2)) =
            A b (P b (‖(z : EuclideanSpace ℝ (Fin 2))‖ ^ 2) • z) →
          (t : ℝ) = endCoord b (T b τ) →
          N k b ((z : EuclideanSpace ℝ (Fin 2)), τ) = (C.handle k).map (w, t))
    (hsb : ∀ k x₀ x₁, (C.ball (finRotate C.len k)).map ((C.ballModel _).symm x₀) =
        N (finRotate C.len k) false 0 →
      (C.ball (finRotate C.len k)).map ((C.ballModel _).symm x₁) = N k true 0 →
      ballNeckDetAmb (C.ball (finRotate C.len k)) (C.ballModel _) x₀
        (mfderiv 𝓘(ℝ, EuclideanSpace ℝ (Fin 2) × ℝ) W.model (N (finRotate C.len k) false) 0) *
      ballNeckDetAmb (C.ball (finRotate C.len k)) (C.ballModel _) x₁
        (mfderiv 𝓘(ℝ, EuclideanSpace ℝ (Fin 2) × ℝ) W.model (N k true) 0) < 0) :
    Nonempty (solidTorusCarrier.{u}.Carrier ≃ₘ⟮solidTorusCarrier.{u}.model, 𝓡∂ 3⟯
      C.union.Piece) := by
  obtain ⟨M⟩ := C.cycleNormalForm_of_neckData hε hε' N hsrc hdisj hball hhandle hunion hpieces
    hfillet hprodN hsb
  exact C.nonempty_diffeomorph_of_cycleNormalForm M

end GC.GraphManifold.Assembly
