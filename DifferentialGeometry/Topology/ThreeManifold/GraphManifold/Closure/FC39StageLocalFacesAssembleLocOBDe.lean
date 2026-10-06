import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.FC39StageLocalFacesAssembleJN74
import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.FC39StageLocalFacesHorizLocOBDe
import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.FC39StageLocalFacesCornerLocOBDe

/-!
# Local-constancy `local_faces` over the frontier (cusp-aware)

Lane O-BD1 (by S-BD2e), G11d (suffix `_OBDe`). `localFaces_assemble_OBDe` with the fibre constancy
of the face functions required only on `residualNear Fl ∩ Ω Fl` for open sets `Ω Fl` around the
faces (zero ratios and cusp functions are functions of `E` only near their faces).
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
theorem localFaces_assemble_loc_OBDe (F : JunctionFaceFacts74 A D R)
    (cov : CutCoverFacts74 A D)
    (hKR : ∀ F : NeighbourFace A.zero A.cusp, neighbourSet F ∩ D.slimSet ⊆
      relInt (regionM1 A.zero A.cusp) D.slimSet)
    (rimBase : R.edge.Base → R.circle.Base)
    (hrim : ∀ c ∈ R.edge.cbase, R.edge.rim c = R.circle.fibre (rimBase c))
    (hreg : D.edgeSet ∩ D.M₃ = R.edge.vertical) (hsub : D.edgeSet ⊆ D.M₂)
    (hconstT : ∀ x y : R.circle.domain, (x : W.Carrier) ∈ R.edge.source →
      (y : W.Carrier) ∈ R.edge.source → R.circle.proj y = R.circle.proj x →
      R.cornerT x = R.cornerT y)
    (Ω : R.slimPieces.ResidualFace → Set W.Carrier) (hΩ : ∀ Fl, IsOpen (Ω Fl))
    (hΩF : ∀ Fl, R.slimPieces.residualSet Fl ⊆ Ω Fl)
    (hconstH : ∀ (Fl : R.slimPieces.ResidualFace) (x y : R.circle.domain),
      (x : W.Carrier) ∈ (R.slimPieces.residualNear Fl : Set W.Carrier) ∩ Ω Fl →
      (y : W.Carrier) ∈ (R.slimPieces.residualNear Fl : Set W.Carrier) ∩ Ω Fl →
      R.circle.proj y = R.circle.proj x →
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
    exact R.localFaces_corner_loc_OBDe F cov hKR rimBase hrim hreg hsub hconstT e
      (Ω (F.horizontal e)) (hΩ _) (hΩF _) (hconstH (F.horizontal e)) b U heU hb hbreg hCU hNeq
  · exact R.localFaces_horizontal_loc_OBDe F cov hKR Fl (Ω Fl) (hΩ Fl) (hΩF Fl) (hconstH Fl) hx₀
      hx₀F hnoE


end StageCutRows74

end GC.GraphManifold.Assembly.FC39P0
