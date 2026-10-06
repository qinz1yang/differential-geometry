import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.FC39StageCornerDescentJN74
import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.FC39StageCornerPatchJN74
import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.FC39StageLocalFacesAssembleLocOBDe
import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.FC39StageCornerRankPrimOBDe
import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.FC39StageFaceDisjointOBDe

/-!
# The corner descent with local fibre constancy, and the rims from the primitives (local form)

Lane O-BD1 (by S-BD2e), G11d (suffix `_OBDe`). `cornerDescent_ofFibreConst_JN74` needs the fibre
constancy of the face function on the whole face neighbourhood `residualNear`; for the zero
domains and cusp cores of the boundary it holds only on an open set `Ω` around the face. This file

* `exists_cornerPatch_loc_OBDe`: the whole-fibre patch of a corner whose preimage lies in the edge
  source, in the face neighbourhood and in a given open set `Ω` around the rim;
* `exists_cornerDescent_loc_OBDe`: `CornerDescent74 F G e` from the fibre constancy of `T` and of
  the face function on `residualNear ∩ Ω`;
* `exists_rims_of_primitives_loc_OBDe`: the whole `JunctionRimFacts74` from the primitives with the
  local constancy (`localFaces_assemble_loc_OBDe`).
-/

set_option autoImplicit false

noncomputable section

open Set Function
open DifferentialGeometry DifferentialGeometry.Topology GC.Endpoint GC.Seifert GC.GraphManifold
open Manifold
open scoped Manifold ContDiff Topology

universe u

namespace GC.GraphManifold.Assembly.FC39P0

variable {W : CompactCarrier.{u}} {n : ℕ} {E : BoundaryTori W n} {A : SmoothStageGeometry74 W E}
  {D : StageCutChoice74 A} {R : StageCutRows74 A D}

/-- **The whole-fibre patch of a corner inside a given open set around the rim.** -/
theorem exists_cornerPatch_loc_OBDe (F : JunctionFaceFacts74 A D R) (G : JunctionRimFacts74 A D R)
    (e : R.edge.EdgeEnd) (Ω : Set W.Carrier) (hΩ : IsOpen Ω) (hrim : R.edge.rim e.1 ⊆ Ω) :
    ∃ N : TopologicalSpace.Opens R.circle.Base, G.rimBase e.1 ∈ N ∧
      ∀ x : R.circle.domain, R.circle.proj x ∈ N → (x : W.Carrier) ∈ R.edge.source ∧
        (x : W.Carrier) ∈ R.slimPieces.residualNear (F.horizontal e) ∧ (x : W.Carrier) ∈ Ω := by
  have hcl : IsClosedMap R.circle.proj := isClosedMap_circleBundle74 R.circleFacts
  let U : Set W.Carrier := (R.edge.source : Set W.Carrier) ∩
    (R.slimPieces.residualNear (F.horizontal e) : Set W.Carrier) ∩ Ω
  have hU : IsOpen U :=
    (R.edge.source.isOpen.inter (R.slimPieces.residualNear _).isOpen).inter hΩ
  have hfib : R.circle.proj ⁻¹' {G.rimBase e.1} ⊆ (Subtype.val ⁻¹' U : Set R.circle.domain) := by
    intro x hx
    have hxf : (x : W.Carrier) ∈ R.circle.fibre (G.rimBase e.1) := ⟨x, hx, rfl⟩
    rw [← G.rim_fibre e.1 (R.edge.frontier_cbase_subset e.2)] at hxf
    obtain ⟨z, ⟨hzp, hzh⟩, hzx⟩ := hxf
    refine ⟨⟨hzx ▸ z.2, ?_⟩, hrim ⟨z, ⟨hzp, hzh⟩, hzx⟩⟩
    have hd : (x : W.Carrier) ∈ R.edge.disk e.1 := ⟨z, ⟨hzp, le_of_eq hzh⟩, hzx⟩
    exact R.slimPieces.residualSet_subset_residualNear_JN74 (F.horizontal e)
      (F.horizontal_disk e hd)
  obtain ⟨V, hV, hbV, -, hVsub⟩ := Geometry.Collapse.EdgeDisk.exists_open_tube_subset_EFC hcl
    (N := (Subtype.val ⁻¹' U : Set R.circle.domain)) (hU.preimage continuous_subtype_val) hfib
    (V := Set.univ) isOpen_univ trivial
  exact ⟨⟨V, hV⟩, hbV, fun x hx => ⟨(hVsub hx).1.1, (hVsub hx).1.2, (hVsub hx).2⟩⟩

/-- **`CornerDescent74` at an endpoint from the local fibre constancy** (`T` constant on the
`q₀`-fibres inside the edge source; the face function constant on the `q₀`-fibres inside
`residualNear ∩ Ω`, `Ω` an open set around the rim). -/
theorem exists_cornerDescent_loc_OBDe (F : JunctionFaceFacts74 A D R)
    (G : JunctionRimFacts74 A D R) (e : R.edge.EdgeEnd) (Ω : Set W.Carrier) (hΩ : IsOpen Ω)
    (hrim : R.edge.rim e.1 ⊆ Ω)
    (hconstT : ∀ x y : R.circle.domain, (x : W.Carrier) ∈ R.edge.source →
      (y : W.Carrier) ∈ R.edge.source → R.circle.proj y = R.circle.proj x →
      R.cornerT x = R.cornerT y)
    (hconstH : ∀ x y : R.circle.domain,
      (x : W.Carrier) ∈ (R.slimPieces.residualNear (F.horizontal e) : Set W.Carrier) ∩ Ω →
      (y : W.Carrier) ∈ (R.slimPieces.residualNear (F.horizontal e) : Set W.Carrier) ∩ Ω →
      R.circle.proj y = R.circle.proj x →
      R.slimPieces.residualFn (F.horizontal e) x = R.slimPieces.residualFn (F.horizontal e) y) :
    Nonempty (CornerDescent74 F G e) := by
  obtain ⟨N, hN, hNsub⟩ := exists_cornerPatch_loc_OBDe F G e Ω hΩ hrim
  obtain ⟨p, hp⟩ : ∃ p : R.circle.domain, R.circle.proj p = G.rimBase e.1 := by
    obtain ⟨_, p, hp, rfl⟩ := R.fibre_nonempty_JN74 (G.rimBase e.1)
    exact ⟨p, hp⟩
  exact ⟨cornerDescent_ofFibreConst_JN74 F G e N hN
    (fun x hx => ⟨(hNsub x hx).1, (hNsub x hx).2.1⟩)
    (fun x y hx hxy => hconstT x y (hNsub x hx).1
      (hNsub y (by rw [hxy]; exact hx)).1 hxy)
    (fun x y hx hxy => hconstH x y ⟨(hNsub x hx).2.1, (hNsub x hx).2.2⟩
      ⟨(hNsub y (by rw [hxy]; exact hx)).2.1, (hNsub y (by rw [hxy]; exact hx)).2.2⟩ hxy)
    ⟨p, hp⟩⟩

/-- **The rim facts of rows with cusp cores from the primitives, local-constancy form.** -/
theorem exists_rims_of_primitives_loc_OBDe (F : JunctionFaceFacts74 A D R)
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
    Nonempty (JunctionRimFacts74 A D R) :=
  ⟨{ rimBase := rimBase
     rimBase_smooth := hsm
     rim_fibre := hrim
     edge_region := hreg
     local_faces := R.localFaces_assemble_loc_OBDe F cov hKR rimBase hrim hreg
       cov.edgeSet_subset_M₂ hconstT Ω hΩ hΩF hconstH hprim }⟩

end GC.GraphManifold.Assembly.FC39P0
