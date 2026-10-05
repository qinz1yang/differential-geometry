import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.AssemblyRoundedRegionAssemblyMeet
import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.AssemblyRoundedRegionAssemblyFaced
import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.AssemblyFC42ModelsApplications

/-!
# Consumers of FC42 packet T4a §0–§2

* `DecompositionCertificate.rawPiece_of_not_isBall` (consumer of `torusFaced_of_not_isBall`): with
  `μ = 0` (and the closed branches excluded) every non-ball vertex is a Raw piece in the `hpiece`
  format of B3 — the vertex part of the input of `exists_rawGraphPresentation_of_regularCutData`;
* `DecompositionCertificate.nonempty_face_homeomorph_torus_of_not_isBall` (consumer of
  `false_of_face_homeomorph_sphereTwo`): every face of a non-ball vertex is a torus;
* `DecompositionCertificate.seamTorus_trichotomy` (consumer of the deduplication lemmas of §1): a
  certificate torus seam is a vertex–vertex seam off the new zero level, a boundary torus of the
  rounded region, or inside the open circle region;
* `DecompositionCertificate.disjoint_roundedUnion_positive`,
  `DecompositionCertificate.disjoint_nonBall_edgeCircles`,
  `DecompositionCertificate.vertex_inter_vertex_inter_roundedLevel` (consumers of §2): the cycle
  unions, the non-ball vertices and the edge circles meet each other only along vertex–vertex seam
  tori, hence never on the new zero level.
-/

set_option autoImplicit false

noncomputable section

open Set Function
open DifferentialGeometry DifferentialGeometry.Topology GC.Endpoint GC.Seifert GC.GraphManifold Manifold
open scoped Manifold ContDiff Topology

universe u

namespace GC.GraphManifold.Assembly

namespace DecompositionCertificate

variable {W : CompactCarrier.{u}} {n : ℕ} {E : BoundaryTori W n} (D : DecompositionCertificate W E)

/-- **Every non-ball vertex is a Raw piece** (`μ = 0`, closed branches excluded). -/
theorem rawPiece_of_not_isBall (hsph : D.sphereSeamCount = 0) (hbad : D.badVertexCount = 0)
    (hnz : ∀ k C, D.vertex k ≠ .closedZero C)
    (hslim : ¬ ∃ (k : Fin D.vertexCount) (P : PieceEmbedding W) (p : P.Piece → Circle)
      (hp : ContMDiff (𝓡∂ 3) (𝓡 1) ∞ p) (hsub : ∀ q, Surjective (mfderiv (𝓡∂ 3) (𝓡 1) p q))
      (fib : SlimFibre P p) (hcl : (𝓡∂ 3).boundary P.Piece = ∅),
      D.vertex k = .slim P (.overCircle p hp hsub fib hcl))
    (k : Fin D.vertexCount) (hk : ¬ (D.vertex k).IsBall) :
    ∃ X : CompactCarrier.{u}, Nonempty (RawGraphPresentation X) ∧
      Nonempty (X.Carrier ≃ₘ⟮X.model, 𝓡∂ 3⟯ (D.vertex k).piece.Piece) :=
  Vertex.rawPiece_of_torusFaced _ (D.torusFaced_of_not_isBall hsph hbad hnz hslim k hk)

/-- **Every face of a non-ball vertex is a torus** (`μ = 0`). -/
theorem nonempty_face_homeomorph_torus_of_not_isBall (hsph : D.sphereSeamCount = 0)
    (hbad : D.badVertexCount = 0) {f : Fin D.faceCount}
    (hf : ¬ (D.vertex (D.faceOwner f)).IsBall) : Nonempty (D.face f ≃ₜ Circle × Circle) := by
  rcases D.faceModel f with φ | ψ
  · exact (D.false_of_face_homeomorph_sphereTwo hsph hbad hf φ).elim
  · exact ⟨ψ⟩

/-- **The three kinds of certificate torus seams** (`μ = 0`): a vertex–vertex seam avoiding the new
zero level, a boundary torus of the rounded region, or a torus inside the open circle region. -/
theorem seamTorus_trichotomy (hbad : D.badVertexCount = 0) (c : Fin D.torusSeamCount) :
    (D.IsVertexSeam c ∧ Disjoint (D.seamTorus c) D.circ.roundedLevel) ∨
      (∃ l, D.circ.levelTorus l = D.seamTorus c) ∨ D.seamTorus c ⊆ interior D.circ.region := by
  rcases h1 : D.torusSide c true with _ | k
  · rcases h2 : D.torusSide c false with _ | k'
    · exact Or.inr (Or.inr (D.seamTorus_subset_interior_region_of_none_none c h1 h2))
    · exact Or.inr (Or.inl (D.exists_levelTorus_eq_seamTorus_of_none hbad c false h2 h1))
  · rcases h2 : D.torusSide c false with _ | k'
    · exact Or.inr (Or.inl (D.exists_levelTorus_eq_seamTorus_of_none hbad c true h1 h2))
    · have hc : D.IsVertexSeam c := ⟨by rw [h1]; rfl, by rw [h2]; rfl⟩
      exact Or.inl ⟨hc, D.disjoint_seamTorus_roundedLevel c hc⟩

/-- **A cycle union meets no non-ball vertex and no edge circle** (`μ = 0`). -/
theorem disjoint_roundedUnion_positive (hbad : D.badVertexCount = 0) (P : D.CyclePartition)
    (j : Fin P.cnt) :
    Disjoint (range (P.roundedUnion j).map)
      ((⋃ (k : Fin D.vertexCount) (_ : ¬ (D.vertex k).IsBall), (D.vertex k).image) ∪
        ⋃ e, range (D.edgeCircle e).piece.map) :=
  disjoint_union_right.mpr ⟨disjoint_iUnion₂_right.mpr fun k hk =>
    D.disjoint_roundedUnion_vertex hbad P j k hk,
    disjoint_iUnion_right.mpr fun e => D.disjoint_roundedUnion_edgeCircle P j e⟩

/-- **The non-ball vertices meet no edge circle** (`μ = 0`). -/
theorem disjoint_nonBall_edgeCircles (hbad : D.badVertexCount = 0) :
    Disjoint (⋃ (k : Fin D.vertexCount) (_ : ¬ (D.vertex k).IsBall), (D.vertex k).image)
      (⋃ e, range (D.edgeCircle e).piece.map) :=
  disjoint_iUnion₂_left.mpr fun k hk =>
    disjoint_iUnion_right.mpr fun e => D.disjoint_vertex_edgeCircle hbad k hk e

/-- **Two different vertices never meet on the new zero level** (no sphere seam). -/
theorem vertex_inter_vertex_inter_roundedLevel (hsph : D.sphereSeamCount = 0)
    {k k' : Fin D.vertexCount} (hkk' : k ≠ k') :
    (D.vertex k).image ∩ (D.vertex k').image ∩ D.circ.roundedLevel = ∅ := by
  rw [eq_empty_iff_forall_notMem]
  rintro x ⟨hx, hxZ⟩
  obtain ⟨c, hc, hxc⟩ := mem_iUnion₂.mp (D.vertex_inter_vertex_subset_seamTorus hsph hkk' hx)
  exact Set.disjoint_left.mp (D.disjoint_seamTorus_roundedLevel c hc) hxc hxZ

end DecompositionCertificate

end GC.GraphManifold.Assembly
