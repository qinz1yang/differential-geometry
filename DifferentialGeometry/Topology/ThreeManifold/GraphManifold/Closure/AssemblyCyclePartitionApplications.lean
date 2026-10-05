import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.AssemblyCyclePartitionGraph

/-!
# Consumers of the complete cycle partition (FC42 packet H2)

* `exists_complete_cycle_partition`: the B6 output in the exact form of review 40 §3.5 (index
  equivalences with the ball vertices and with `Fin D.handleCount`, orientation, `hends`);
* `CyclePartition.builderData`: for every cycle, the hypotheses `hlen`, `hbinj`, `hv`, `hinj`,
  `hends` of the dry builder `dry_cycleOfCertificate` (review 40 §4.6: B12 needs them);
* counting: `CyclePartition.sum_len_eq_handleCount` and `natCard_isBall_eq_handleCount` (as many
  ball vertices as handles).
-/

set_option autoImplicit false

noncomputable section

open Set Function
open DifferentialGeometry DifferentialGeometry.Topology GC.Endpoint GC.Seifert GC.GraphManifold Manifold
open scoped Manifold ContDiff Topology

universe u

namespace GC.GraphManifold.Assembly

local instance ballChartsA_ASMCYC3 : ChartedSpace (EuclideanHalfSpace 3) (ClosedCell 3) :=
  DifferentialGeometry.Topology.Handle.closedCellChartedSpaceSucc 2

local instance ballSmoothA_ASMCYC3 : IsManifold (𝓡∂ 3) ∞ (ClosedCell 3) :=
  DifferentialGeometry.Topology.Handle.closedCellIsManifold 2

namespace DecompositionCertificate

variable {W : CompactCarrier.{u}} {n : ℕ} {E : BoundaryTori W n} (D : DecompositionCertificate W E)

/-- **B6, corrected output (review 40 §3.5).** Without sphere seams and with no bad vertex, the
ball–handle multigraph has a complete cycle partition: index equivalences with the ball vertices
and with all handles, a traversal orientation and the builder identity. -/
theorem exists_complete_cycle_partition (hsph : D.sphereSeamCount = 0)
    (hball : ∀ f, D.faceKind f = .partitioned →
      (∃ e : D.face f ≃ₜ Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1, D.faceModel f = .inl e) →
      (D.vertex (D.faceOwner f)).IsBall) :
    ∃ (cnt : ℕ) (len : Fin cnt → ℕ), (∀ j, 0 < len j) ∧
      ∃ (ballIdx : (Σ j, Fin (len j)) ≃ {k : Fin D.vertexCount // (D.vertex k).IsBall})
        (handleIdx : (Σ j, Fin (len j)) ≃ Fin D.handleCount) (σ : (Σ j, Fin (len j)) → Bool),
        ∀ j k b, D.handleEnd (handleIdx ⟨j, k⟩) (xor b (σ ⟨j, k⟩)) =
          (ballIdx ⟨j, rimBall (len j) k b⟩ : Fin D.vertexCount) := by
  obtain ⟨P⟩ := D.nonempty_cyclePartition hsph hball
  exact ⟨P.cnt, P.len, P.len_pos, P.ballIdx, P.handleIdx, P.orient, P.handleEnd_eq⟩

namespace CyclePartition

variable {D} (P : D.CyclePartition)

/-- **The dry builder's hypotheses, per cycle** (`dry_cycleOfCertificate`: `hlen`, `hbinj`, `hv`,
`hinj`, `hends`). -/
theorem builderData (j : Fin P.cnt) :
    0 < P.len j ∧ Injective (P.ball j) ∧
      (∀ k, D.vertex (P.ball j k) = .zero (P.ballPiece j k) (.ball (P.ballModel j k))) ∧
      Injective (P.handle j) ∧
      ∀ k b, D.handleEnd (P.handle j k) (xor b (P.orientation j k)) =
        P.ball j (rimBall (P.len j) k b) :=
  ⟨P.len_pos j, P.ball_injective j, P.vertex_ball j, P.handle_injective j, P.handleEnd_handle j⟩

/-- The cycle lengths add up to the number of handles. -/
theorem sum_len_eq_handleCount : ∑ j, P.len j = D.handleCount := by
  have h := Fintype.card_congr P.handleIdx
  rw [Fintype.card_sigma, Fintype.card_fin] at h
  simpa using h

/-- As many ball vertices as cycle positions. -/
theorem natCard_isBall_eq_sum_len :
    Nat.card {k : Fin D.vertexCount // (D.vertex k).IsBall} = ∑ j, P.len j := by
  rw [← Nat.card_congr P.ballIdx, Nat.card_eq_fintype_card, Fintype.card_sigma]
  simp

end CyclePartition

/-- **As many ball vertices as handles** (no sphere seams, no bad vertex). -/
theorem natCard_isBall_eq_handleCount (hsph : D.sphereSeamCount = 0)
    (hball : ∀ f, D.faceKind f = .partitioned →
      (∃ e : D.face f ≃ₜ Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1, D.faceModel f = .inl e) →
      (D.vertex (D.faceOwner f)).IsBall) :
    Nat.card {k : Fin D.vertexCount // (D.vertex k).IsBall} = D.handleCount := by
  obtain ⟨P⟩ := D.nonempty_cyclePartition hsph hball
  rw [P.natCard_isBall_eq_sum_len, P.sum_len_eq_handleCount]

end DecompositionCertificate

end GC.GraphManifold.Assembly
