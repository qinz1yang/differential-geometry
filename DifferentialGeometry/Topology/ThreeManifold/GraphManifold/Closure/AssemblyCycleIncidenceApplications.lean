import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.AssemblyCycleIncidence

/-!
# FC42 packet H1 (part b): consumers of the global incidence

Lane ASM-CYC2.

* `DecompositionCertificate.disjoint_handle_vertex_image_of_ne`: a handle meets no vertex other than
  its two end vertices;
* `DecompositionCertificate.handle_inter_vertex_image_of_ne`: at an end vertex that is not the other
  end, the handle meets the vertex exactly in that end disk;
* `cycle_handle_ball_inter_eq_empty`: in a cycle (builder hypotheses), handle `k` meets no ball
  other than balls `k` and `k + 1`;
* `cycle_pairwise_disjoint`: the three corrected cycle glue facts B9–B11 at once in the shape of the
  `BallHandleCycle` fields `handle_disjoint`, `ball_disjoint` (from `hends`).
-/

set_option autoImplicit false

noncomputable section

open Set Function
open DifferentialGeometry DifferentialGeometry.Topology GC.Endpoint GC.Seifert GC.GraphManifold Manifold
open scoped Manifold ContDiff Topology

universe u

namespace GC.GraphManifold.Assembly

local instance ballChartsH1bA_ASMCYC2 : ChartedSpace (EuclideanHalfSpace 3) (ClosedCell 3) :=
  DifferentialGeometry.Topology.Handle.closedCellChartedSpaceSucc 2

local instance ballSmoothH1bA_ASMCYC2 : IsManifold (𝓡∂ 3) ∞ (ClosedCell 3) :=
  DifferentialGeometry.Topology.Handle.closedCellIsManifold 2

namespace DecompositionCertificate

variable {W : CompactCarrier.{u}} {n : ℕ} {E : BoundaryTori W n} (D : DecompositionCertificate W E)

/-- A handle meets no vertex other than its end vertices. -/
theorem disjoint_handle_vertex_image_of_ne (h : Fin D.handleCount) {v : Fin D.vertexCount}
    (hv : ∀ b, D.handleEnd h b ≠ v) : Disjoint (range (D.handle h).map) (D.vertex v).image := by
  rw [Set.disjoint_iff_inter_eq_empty, D.handle_inter_vertex_image]
  refine eq_empty_of_forall_notMem fun z hz => ?_
  obtain ⟨b, hb, -⟩ := mem_iUnion₂.mp hz
  exact hv b hb

/-- At an end vertex that is not the other end, the handle meets the vertex in that end disk. -/
theorem handle_inter_vertex_image_of_ne (h : Fin D.handleCount) (b : Bool)
    (hne : D.handleEnd h (!b) ≠ D.handleEnd h b) :
    range (D.handle h).map ∩ (D.vertex (D.handleEnd h b)).image = (D.handle h).endDisk b := by
  rw [D.handle_inter_vertex_image]
  apply Subset.antisymm
  · intro z hz
    obtain ⟨b', hb', hz⟩ := mem_iUnion₂.mp hz
    by_cases hbb : b' = b
    · rw [← hbb]
      exact hz
    · have : b' = !b := by cases b <;> cases b' <;> simp_all
      rw [this] at hb'
      exact (hne hb').elim
  · intro z hz
    exact mem_iUnion₂.mpr ⟨b, rfl, hz⟩

end DecompositionCertificate

variable {W : CompactCarrier.{u}} {n : ℕ} {E : BoundaryTori W n}

/-- In a cycle, handle `k` meets no ball other than balls `k` and `k + 1`. -/
theorem cycle_handle_ball_inter_eq_empty (D : DecompositionCertificate W E) (len : ℕ)
    (ballIdx : Fin len → Fin D.vertexCount) (hbinj : Injective ballIdx)
    (P : Fin len → PieceEmbedding W) (eB : ∀ k, (P k).Piece ≃ₘ⟮𝓡∂ 3, 𝓡∂ 3⟯ ClosedCell 3)
    (hv : ∀ k, D.vertex (ballIdx k) = .zero (P k) (.ball (eB k)))
    (handleIdx : Fin len → Fin D.handleCount) (σ : Fin len → Bool)
    (hends : ∀ k b, D.handleEnd (handleIdx k) (xor b (σ k)) = ballIdx (rimBall len k b))
    {k j : Fin len} (hjk : j ≠ k) (hjk' : j ≠ finRotate len k) :
    range ((D.handle (handleIdx k)).orient (σ k)).map ∩ range (P j).map = ∅ := by
  rw [cycle_handle_ball_inter D len ballIdx hbinj P eB hv handleIdx σ hends k j]
  simp only [hjk, hjk', ↓reduceIte, union_empty]

/-- B10 and B11 together, in the shape of the `BallHandleCycle` fields. -/
theorem cycle_pairwise_disjoint (D : DecompositionCertificate W E) (len : ℕ)
    (ballIdx : Fin len → Fin D.vertexCount) (hbinj : Injective ballIdx)
    (P : Fin len → PieceEmbedding W) (eB : ∀ k, (P k).Piece ≃ₘ⟮𝓡∂ 3, 𝓡∂ 3⟯ ClosedCell 3)
    (hv : ∀ k, D.vertex (ballIdx k) = .zero (P k) (.ball (eB k)))
    (handleIdx : Fin len → Fin D.handleCount) (hinj : Injective handleIdx) (σ : Fin len → Bool)
    (hends : ∀ k b, D.handleEnd (handleIdx k) (xor b (σ k)) = ballIdx (rimBall len k b)) :
    (Pairwise fun k k' => Disjoint (range (P k).map) (range (P k').map)) ∧
      Pairwise fun k k' => Disjoint (range ((D.handle (handleIdx k)).orient (σ k)).map)
        (range ((D.handle (handleIdx k')).orient (σ k')).map) :=
  ⟨cycle_ball_disjoint_of_hends D len ballIdx hbinj P eB hv handleIdx σ hends,
    cycle_handle_disjoint D len handleIdx hinj σ⟩

end GC.GraphManifold.Assembly
