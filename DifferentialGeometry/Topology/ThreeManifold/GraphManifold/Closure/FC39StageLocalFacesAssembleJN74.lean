import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.FC39StageLocalFacesCornerJN74

/-!
# Draft 74, `local_faces`, step 8: the assembly over all frontier points

Lane S-JUNCTIONS (by S-JUNCTIONS4), G26 part 2 (suffix `_JN74`). The field `local_faces` of
`JunctionRimFacts74` on any rows `R` without cusp pieces, from the face facts `F`, `rim_fibre`,
`edge_region`, `edgeSet ⊆ M₂`, the removal `hKR`, the fibre constancy of `T` and of every face
function, and the per-endpoint EDP05 primitives `hprim` (descended face equation `b_e`, the same
data as the rank inputs of `exists_cornerRank_descended_of_local_JN74`):
the classification (`frontier_classification_JN74`) splits `∂C₁` into the vertical points
(`localFaces_vertical_JN74`), the corners (`localFaces_corner_JN74`) and the horizontal points
(`localFaces_horizontal_JN74`).
-/

set_option autoImplicit false

noncomputable section

open Set Function Filter
open DifferentialGeometry DifferentialGeometry.Topology GC.Endpoint GC.Seifert GC.GraphManifold
open Manifold
open scoped Manifold ContDiff Topology

universe u

namespace GC.GraphManifold.Assembly.FC39P0

variable {W : CompactCarrier.{u}} {n : ℕ} {E : BoundaryTori W n} {A : SmoothStageGeometry74 W E}
  {D : StageCutChoice74 A}

namespace StageCutRows74

variable (R : StageCutRows74 A D)

/-- **`local_faces` over all frontier points of `C₁`.** -/
theorem localFaces_assemble_JN74 [IsEmpty (Fin n)] (F : JunctionFaceFacts74 A D R)
    (hKR : ∀ i, pieceBoundary (A.zero.piece i) ∩ D.slimSet ⊆
      relInt (regionM1 A.zero A.cusp) D.slimSet)
    (rimBase : R.edge.Base → R.circle.Base)
    (hrim : ∀ c ∈ R.edge.cbase, R.edge.rim c = R.circle.fibre (rimBase c))
    (hreg : D.edgeSet ∩ D.M₃ = R.edge.vertical) (hsub : D.edgeSet ⊆ D.M₂)
    (hconstT : ∀ x y : R.circle.domain, (x : W.Carrier) ∈ R.edge.source →
      (y : W.Carrier) ∈ R.edge.source → R.circle.proj y = R.circle.proj x →
      R.cornerT x = R.cornerT y)
    (hconstH : ∀ (Fl : R.slimPieces.ResidualFace) (x y : R.circle.domain),
      (x : W.Carrier) ∈ R.slimPieces.residualNear Fl →
      (y : W.Carrier) ∈ R.slimPieces.residualNear Fl → R.circle.proj y = R.circle.proj x →
      R.slimPieces.residualFn Fl x = R.slimPieces.residualFn Fl y)
    (hprim : ∀ e : R.edge.EdgeEnd, ∃ (b : R.edge.Base → ℝ) (U : TopologicalSpace.Opens R.edge.Base),
      e.1 ∈ U ∧ ContMDiffOn (𝓡 1) 𝓘(ℝ, ℝ) ∞ b U ∧ mfderiv (𝓡 1) 𝓘(ℝ, ℝ) b e.1 ≠ 0 ∧
      R.edge.cbase ∩ U = {c | c ∈ U ∧ 0 ≤ b c} ∧
      ∃ N' : Set W.Carrier, IsOpen N' ∧ R.edge.rim e.1 ⊆ N' ∧ ∀ x ∈ N',
        ∃ hx : x ∈ R.edge.source,
          R.slimPieces.residualFn (F.horizontal e) x = b (R.edge.proj ⟨x, hx⟩)) :
    ∀ c ∈ frontier R.circle.cbase, ∃ U : TopologicalSpace.Opens R.circle.Base, c ∈ U ∧
      ∃ (L : Finset (CircleFaceLabel R.slimPieces.ResidualFace R.edge.EdgeBaseComponent))
        (φ : CircleFaceLabel R.slimPieces.ResidualFace R.edge.EdgeBaseComponent →
          R.circle.Base → ℝ),
        1 ≤ L.card ∧ L.card ≤ 2 ∧
        (∀ f ∈ L, ContMDiffOn (𝓡 2) 𝓘(ℝ, ℝ) ∞ (φ f) U ∧ φ f c = 0 ∧
          {c' | c' ∈ U ∧ c' ∈ R.circle.cbase ∧ φ f c' = 0} =
            {c' | c' ∈ U ∧ c' ∈ R.circle.cbase ∧
              R.circle.fibre c' ⊆ circleFaceSet R.slimPieces R.edge f}) ∧
        (Surjective fun w : TangentSpace (𝓡 2) c =>
          fun f : L => mfderiv (𝓡 2) 𝓘(ℝ, ℝ) (φ f) c w) ∧
        R.circle.cbase ∩ U = {c' | c' ∈ U ∧ ∀ f ∈ L, φ f c' ≤ 0} := by
  intro c hc
  rcases R.frontier_classification_JN74 F rimBase hrim hreg hsub hc with
    ⟨c', hc', hnf, rfl⟩ | ⟨e, rfl⟩ | ⟨x₀, Fl, hx₀, hx₀F, hnoE⟩
  · exact R.localFaces_vertical_JN74 F rimBase hrim hreg hsub hconstT hc' hnf
  · obtain ⟨b, U, heU, hb, hbreg, hCU, hNeq⟩ := hprim e
    exact R.localFaces_corner_JN74 F hKR rimBase hrim hreg hsub hconstT e
      (hconstH (F.horizontal e)) b U heU hb hbreg hCU hNeq
  · exact R.localFaces_horizontal_JN74 F hKR Fl (hconstH Fl) hx₀ hx₀F hnoE

end StageCutRows74

end GC.GraphManifold.Assembly.FC39P0
