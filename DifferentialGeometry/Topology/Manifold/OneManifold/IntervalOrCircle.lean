import DifferentialGeometry.Topology.Manifold.OneManifold.Interval
import DifferentialGeometry.Topology.Manifold.InteriorAtlas

/-!
# The dichotomy for compact connected one-manifolds modelled on the half-line

A compact connected smooth one-manifold modelled on `EuclideanHalfSpace 1` is diffeomorphic to
`[0, 1]` (nonempty boundary, `nonempty_diffeomorph_Icc_of_boundary_nonempty`) or to the circle
(empty boundary: re-chart by interior charts, `interiorChartedSpace`, and apply
`nonempty_circle_diffeomorph_of_finrank_eq_one`).
-/

set_option autoImplicit false

open Set
open scoped Manifold ContDiff Topology

noncomputable section

namespace DifferentialGeometry.Topology.Manifold.OneManifold

variable {M : Type*} [TopologicalSpace M] [ChartedSpace (EuclideanHalfSpace 1) M]
  [IsManifold (𝓡∂ 1) ∞ M] [CompactSpace M] [T2Space M]

theorem nonempty_circle_diffeomorph_of_boundary_eq_empty [ConnectedSpace M]
    (h : (𝓡∂ 1).boundary M = ∅) : Nonempty (Circle ≃ₘ⟮𝓡 1, 𝓡∂ 1⟯ M) := by
  have : BoundarylessManifold (𝓡∂ 1) M := ModelWithCorners.Boundaryless.of_boundary_eq_empty h
  let _ := DifferentialGeometry.Manifold.interiorChartedSpace (𝓡∂ 1) ∞ (M := M)
  have := DifferentialGeometry.Manifold.interiorIsManifold (𝓡∂ 1) ∞ (M := M)
  obtain ⟨e⟩ := nonempty_circle_diffeomorph_of_finrank_eq_one (EuclideanSpace ℝ (Fin 1))
    (EuclideanSpace ℝ (Fin 1)) M 𝓘(ℝ, EuclideanSpace ℝ (Fin 1)) (by simp)
  exact ⟨e.trans (DifferentialGeometry.Manifold.interiorAtlasDiffeomorph (𝓡∂ 1) ∞).symm⟩

theorem nonempty_diffeomorph_Icc_or_circle [ConnectedSpace M] :
    Nonempty (M ≃ₘ⟮𝓡∂ 1, 𝓡∂ 1⟯ Icc (0 : ℝ) 1) ∨ Nonempty (Circle ≃ₘ⟮𝓡 1, 𝓡∂ 1⟯ M) := by
  rcases ((𝓡∂ 1).boundary M).eq_empty_or_nonempty with h | h
  · exact Or.inr (nonempty_circle_diffeomorph_of_boundary_eq_empty h)
  · exact Or.inl (nonempty_diffeomorph_Icc_of_boundary_nonempty h)

/-- Every clopen connected open subset (e.g. a connected component) of a compact smooth
one-manifold with boundary is a closed interval or a circle. -/
theorem nonempty_diffeomorph_Icc_or_circle_of_isClosed (U : TopologicalSpace.Opens M)
    (hU : IsClosed (U : Set M)) (hconn : IsConnected (U : Set M)) :
    Nonempty (U ≃ₘ⟮𝓡∂ 1, 𝓡∂ 1⟯ Icc (0 : ℝ) 1) ∨ Nonempty (Circle ≃ₘ⟮𝓡 1, 𝓡∂ 1⟯ U) := by
  have : CompactSpace U := isCompact_iff_compactSpace.mp hU.isCompact
  have : ConnectedSpace U := isConnected_iff_connectedSpace.mp hconn
  exact nonempty_diffeomorph_Icc_or_circle

instance : LocallyConnectedSpace (EuclideanHalfSpace 1) := by
  have hind : Topology.IsInducing (Subtype.val : EuclideanHalfSpace 1 → EuclideanSpace ℝ (Fin 1)) :=
    Topology.IsEmbedding.subtypeVal.isInducing
  refine locallyConnectedSpace_of_connected_bases
    (fun y (ε : ℝ) => Subtype.val ⁻¹' Metric.ball y.val ε) (fun _ ε => 0 < ε) ?_ ?_
  · intro y
    rw [hind.nhds_eq_comap]
    exact Metric.nhds_basis_ball.comap _
  intro y ε _
  rw [← hind.isPreconnected_image]
  apply Convex.isPreconnected
  have heq : ((Subtype.val : EuclideanHalfSpace 1 → EuclideanSpace ℝ (Fin 1)) ''
      (Subtype.val ⁻¹' Metric.ball y.val ε)) =
      Metric.ball y.val ε ∩ {z | 0 ≤ z 0} := by
    ext z
    constructor
    · rintro ⟨w, hw, rfl⟩
      exact ⟨hw, w.2⟩
    · rintro ⟨hz, hz0⟩
      exact ⟨⟨z, hz0⟩, hz, rfl⟩
  rw [heq]
  refine (convex_ball _ _).inter ?_
  exact convex_halfSpace_ge (f := fun z : EuclideanSpace ℝ (Fin 1) => z 0)
    ⟨fun _ _ => rfl, fun _ _ => rfl⟩ 0

omit [IsManifold (𝓡∂ 1) ∞ M] [CompactSpace M] [T2Space M] in
theorem isOpen_connectedComponent_of_oneManifold (x : M) : IsOpen (connectedComponent x) := by
  have : LocallyConnectedSpace M := ChartedSpace.locallyConnectedSpace (EuclideanHalfSpace 1) M
  exact isOpen_connectedComponent

omit [IsManifold (𝓡∂ 1) ∞ M] [T2Space M] in
theorem finite_connectedComponents_of_oneManifold : Finite (ConnectedComponents M) := by
  have : LocallyConnectedSpace M := ChartedSpace.locallyConnectedSpace (EuclideanHalfSpace 1) M
  infer_instance

/-- The connected component of a point, as an open subset. -/
def componentOpens (x : M) : TopologicalSpace.Opens M :=
  ⟨connectedComponent x, isOpen_connectedComponent_of_oneManifold x⟩

/-- **Compact one-manifolds with boundary, all components.** A compact smooth one-manifold with
boundary has finitely many components, and each is a closed interval or a circle. -/
theorem finite_connectedComponents_and_Icc_or_circle :
    Finite (ConnectedComponents M) ∧ ∀ x : M,
      Nonempty (componentOpens x ≃ₘ⟮𝓡∂ 1, 𝓡∂ 1⟯ Icc (0 : ℝ) 1) ∨
        Nonempty (Circle ≃ₘ⟮𝓡 1, 𝓡∂ 1⟯ componentOpens x) :=
  ⟨finite_connectedComponents_of_oneManifold, fun _ =>
    nonempty_diffeomorph_Icc_or_circle_of_isClosed _ isClosed_connectedComponent
      isConnected_connectedComponent⟩

end DifferentialGeometry.Topology.Manifold.OneManifold
