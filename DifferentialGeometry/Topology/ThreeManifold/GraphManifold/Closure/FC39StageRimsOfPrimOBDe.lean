import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.FC39StageLocalFacesAssembleOBDe
import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.FC39StageCornerRankPrimOBDe
import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.FC39StageFaceDisjointOBDe

/-!
# Consumer of the cusp-aware kit: `JunctionRimFacts74` and the corner facts from the primitives

Lane O-BD1 (by S-BD2e), G11c consumer (suffix `_OBDe`). The whole `JunctionRimFacts74` of rows with
cusp cores from the labelled rim base, the face facts and the per-endpoint primitives, and the
corner rank / descended facts at an endpoint from the same primitives (the cusp-aware kit of
`FC39StageCuspKitOBDe`, `FC39StageFaceModelOBDe`, `FC39StageLocalFaces*OBDe`,
`FC39StageCornerRankPrimOBDe`).
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

/-- **The rim facts of rows with cusp cores, given the face facts and the endpoint primitives.** -/
theorem exists_rims_of_primitives_OBDe (R : StageCutRows74 A D) (F : JunctionFaceFacts74 A D R)
    (cov : CutCoverFacts74 A D)
    (hKR : ∀ F : NeighbourFace A.zero A.cusp, neighbourSet F ∩ D.slimSet ⊆
      relInt (regionM1 A.zero A.cusp) D.slimSet)
    (rimBase : R.edge.Base → R.circle.Base)
    (hsm : ContMDiffOn (𝓡 1) (𝓡 2) ∞ rimBase R.edge.cbase)
    (hrim : ∀ c ∈ R.edge.cbase, R.edge.rim c = R.circle.fibre (rimBase c))
    (hreg : D.edgeSet ∩ D.M₃ = R.edge.vertical)
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
    Nonempty (JunctionRimFacts74 A D R) :=
  ⟨{ rimBase := rimBase
     rimBase_smooth := hsm
     rim_fibre := hrim
     edge_region := hreg
     local_faces := R.localFaces_assemble_OBDe F cov hKR rimBase hrim hreg cov.edgeSet_subset_M₂
       hconstT hconstH hprim }⟩

/-- **The corner rank and descended facts of rows with cusp cores at an endpoint, from the
primitives.** -/
theorem exists_cornerRankDescended_of_primitives_OBDe (R : StageCutRows74 A D)
    (F : JunctionFaceFacts74 A D R) (G : JunctionRimFacts74 A D R) (cov : CutCoverFacts74 A D)
    (hKR : ∀ F : NeighbourFace A.zero A.cusp, neighbourSet F ∩ D.slimSet ⊆
      relInt (regionM1 A.zero A.cusp) D.slimSet)
    (e : R.edge.EdgeEnd) (d : CornerDescent74 F G e)
    (b : R.edge.Base → ℝ) (U : TopologicalSpace.Opens R.edge.Base) (heU : e.1 ∈ U)
    (hb : ContMDiffOn (𝓡 1) 𝓘(ℝ, ℝ) ∞ b U) (hbreg : mfderiv (𝓡 1) 𝓘(ℝ, ℝ) b e.1 ≠ 0)
    (hCU : R.edge.cbase ∩ U = {c | c ∈ U ∧ 0 ≤ b c})
    (hNeq : ∃ N' : Set W.Carrier, IsOpen N' ∧ R.edge.rim e.1 ⊆ N' ∧ ∀ x ∈ N',
      ∃ hx : x ∈ R.edge.source,
        R.slimPieces.residualFn (F.horizontal e) x = b (R.edge.proj ⟨x, hx⟩)) :
    ∃ K : CornerRank74 F G e, Nonempty (CornerDescended74 K) :=
  StageCutRows74.cornerRankDescended_of_prim_OBDe cov hKR e d b U heU hb hbreg hCU hNeq

end GC.GraphManifold.Assembly.FC39P0
