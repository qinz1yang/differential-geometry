import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.FC39StageCornerRankPrimJN74
import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.FC39StageFaceModelOBDe

/-!
# Cusp-aware `CornerRank74` and `CornerDescended74` from the primitives

Lane O-BD1 (by S-BD2e), G11c (suffix `_OBDe`). The cusp-aware copy of
`cornerRankDescended_of_prim_JN74` (the closed kit's `[IsEmpty (Fin n)]` is dropped; the face
model is `exists_faceModel_OBDe` and the removal property is stated for the neighbour faces, `hKR
: neighbourSet F ∩ slimSet ⊆ relInt_{M₁} slimSet`; the cover facts `cov` give the disjointness of
zero domains and cusp cores).
-/

set_option autoImplicit false

noncomputable section

open Set Function Filter
open DifferentialGeometry DifferentialGeometry.Topology GC.Endpoint GC.Seifert GC.GraphManifold
open Manifold
open scoped Manifold ContDiff Topology

universe u

namespace GC.GraphManifold.Assembly.FC39P0

variable {W : CompactCarrier.{u}} {n : ℕ} {E : BoundaryTori W n}

namespace StageCutRows74

variable {A : SmoothStageGeometry74 W E} {D : StageCutChoice74 A} {R : StageCutRows74 A D}

/-- **`CornerRank74` and `CornerDescended74` at an endpoint from the EDP05 primitives.** -/
theorem cornerRankDescended_of_prim_OBDe {F : JunctionFaceFacts74 A D R}
    {G : JunctionRimFacts74 A D R}
    (cov : CutCoverFacts74 A D)
    (hKR : ∀ F : NeighbourFace A.zero A.cusp, neighbourSet F ∩ D.slimSet ⊆
      relInt (regionM1 A.zero A.cusp) D.slimSet)
    (e : R.edge.EdgeEnd) (d : CornerDescent74 F G e)
    (b : R.edge.Base → ℝ) (U : TopologicalSpace.Opens R.edge.Base) (heU : e.1 ∈ U)
    (hb : ContMDiffOn (𝓡 1) 𝓘(ℝ, ℝ) ∞ b U) (hbreg : mfderiv (𝓡 1) 𝓘(ℝ, ℝ) b e.1 ≠ 0)
    (hCU : R.edge.cbase ∩ U = {c | c ∈ U ∧ 0 ≤ b c})
    (hNeq : ∃ N' : Set W.Carrier, IsOpen N' ∧ R.edge.rim e.1 ⊆ N' ∧ ∀ x ∈ N',
      ∃ hx : x ∈ R.edge.source,
        R.slimPieces.residualFn (F.horizontal e) x = b (R.edge.proj ⟨x, hx⟩)) :
    ∃ K : CornerRank74 F G e, Nonempty (CornerDescended74 K) := by
  classical
  have hedge : R.edge.edgePiece = D.edgeSet := D.edgePiece_edgeBundle74 R.edgeFacts
  have hec : e.1 ∈ R.edge.cbase := R.edge.frontier_cbase_subset e.2
  have hfibrim : R.circle.fibre (G.rimBase e.1) = R.edge.rim e.1 := (G.rim_fibre _ hec).symm
  obtain ⟨N', hN'o, hrimN', hN'eq⟩ := hNeq
  have hrimsrc : ∀ x ∈ R.edge.rim e.1, ∃ hxS : x ∈ R.edge.source,
      R.edge.proj ⟨x, hxS⟩ = e.1 ∧ R.edge.height ⟨x, hxS⟩ = R.edge.level := by
    rintro x ⟨z, ⟨hz1, hz2⟩, hzx⟩
    have hxS : x ∈ R.edge.source := by
      rw [← hzx]
      exact z.2
    have hz : z = ⟨x, hxS⟩ := Subtype.ext hzx
    subst hz
    exact ⟨hxS, hz1, hz2⟩
  have hrimF : ∀ x ∈ R.edge.rim e.1, x ∈ R.slimPieces.residualSet (F.horizontal e) := by
    rintro x ⟨z, ⟨hz1, hz2⟩, hzx⟩
    exact F.horizontal_disk e ⟨z, ⟨hz1, hz2.le⟩, hzx⟩
  have hb0 : b e.1 = 0 := by
    obtain ⟨_, x, hx, rfl⟩ := R.fibre_nonempty_JN74 (G.rimBase e.1)
    have hxr : (x : W.Carrier) ∈ R.edge.rim e.1 := by
      rw [← hfibrim]
      exact ⟨x, hx, rfl⟩
    obtain ⟨hxS, hxe, -⟩ := hrimsrc _ hxr
    obtain ⟨hxS', hxeq⟩ := hN'eq _ (hrimN' hxr)
    have h0 := R.slimPieces.residualFn_eq_zero_JN74 (F.horizontal e) (hrimF _ hxr)
    rw [hxeq] at h0
    exact hxe ▸ h0
  obtain ⟨U', heU', hU'U, hU'comp⟩ :=
    DifferentialGeometry.Topology.Manifold.exists_nhds_component_iff_JN74 heU hb hb0 hbreg hCU
  have hmodel : ∀ x ∈ R.slimPieces.residualSet (F.horizontal e), ∃ O : Set W.Carrier,
      IsOpen O ∧ x ∈ O ∧ O ⊆ (R.slimPieces.residualNear (F.horizontal e) : Set W.Carrier) ∧
      (∀ y ∈ O, y ∈ D.M₂ ↔ 0 ≤ R.slimPieces.residualFn (F.horizontal e) y) ∧
      ∀ y ∈ O, R.slimPieces.residualFn (F.horizontal e) y = 0 →
        y ∈ R.slimPieces.residualSet (F.horizontal e) :=
    fun x hx => exists_faceModel_OBDe R cov F hKR (F.horizontal e) hx
  let P : Set W.Carrier := {z | z ∈ (R.slimPieces.residualNear (F.horizontal e) : Set W.Carrier) ∧
    (z ∈ D.M₂ ↔ 0 ≤ R.slimPieces.residualFn (F.horizontal e) z)}
  have hrimP : ∀ x ∈ R.edge.rim e.1, x ∈ interior P := fun x hxr => by
    obtain ⟨O, ho, hxo, hOn, hM, -⟩ := hmodel x (hrimF x hxr)
    exact mem_interior.2 ⟨O, fun y hy => ⟨hOn hy, hM y hy⟩, ho, hxo⟩
  have hΩs : IsOpen (Subtype.val '' (R.edge.proj ⁻¹' (U' : Set R.edge.Base) :
      Set R.edge.source) : Set W.Carrier) :=
    R.edge.source.isOpen.isOpenMap_subtype_val _ (U'.isOpen.preimage R.edge.proj.continuous)
  let Ω : Set W.Carrier := interior P ∩ N' ∩
    Subtype.val '' (R.edge.proj ⁻¹' (U' : Set R.edge.Base) : Set R.edge.source)
  have hΩ : ∀ x ∈ R.edge.rim e.1, x ∈ Ω := by
    intro x hxr
    obtain ⟨hxS, hxe, -⟩ := hrimsrc _ hxr
    refine ⟨⟨hrimP x hxr, hrimN' hxr⟩, ⟨x, hxS⟩, ?_, rfl⟩
    change R.edge.proj ⟨x, hxS⟩ ∈ U'
    rw [hxe]
    exact heU'
  have hxΩ : ∀ x : R.circle.domain, (x : W.Carrier) ∈ Ω →
      (x : W.Carrier) ∈ P ∧ ∃ hxS : (x : W.Carrier) ∈ R.edge.source,
        R.edge.proj ⟨x, hxS⟩ ∈ U' ∧
          R.slimPieces.residualFn (F.horizontal e) x = b (R.edge.proj ⟨x, hxS⟩) := by
    intro x ⟨⟨hPi, hN'x⟩, z, hzU, hzx⟩
    have hxS : (x : W.Carrier) ∈ R.edge.source := by
      rw [← hzx]
      exact z.2
    have hz : z = ⟨(x : W.Carrier), hxS⟩ := Subtype.ext hzx
    obtain ⟨hxS', hxeq⟩ := hN'eq _ hN'x
    refine ⟨interior_subset hPi, hxS, ?_, hxeq⟩
    rw [← hz]
    exact hzU
  obtain ⟨p, hpc⟩ : ∃ p : R.circle.domain, R.circle.proj p = G.rimBase e.1 := by
    obtain ⟨_, p, hp, rfl⟩ := R.fibre_nonempty_JN74 (G.rimBase e.1)
    exact ⟨p, hp⟩
  refine exists_cornerRank_descended_of_local_JN74 e d ⟨p, hpc⟩ b U heU hb hbreg
    (Subtype.val ⁻¹' Ω : Set R.circle.domain)
    (((isOpen_interior.inter hN'o).inter hΩs).preimage continuous_subtype_val)
    (fun x hx => hΩ _ (by rw [← hfibrim]; exact ⟨x, hx, rfl⟩))
    (fun x hx => ⟨(hxΩ x hx).2.choose, (hxΩ x hx).1.1⟩)
    (fun x hx => ⟨(hxΩ x hx).2.choose, (hxΩ x hx).2.choose_spec.2⟩)
    (fun x hx => (hxΩ x hx).1.2) ?_ ?_
  · intro x hx
    obtain ⟨hPx, hxS, hπU', hxeq⟩ := hxΩ x hx
    have hT : R.cornerT x = R.edge.height ⟨x, hxS⟩ - R.edge.level := by
      simp only [StageCutRows74.cornerT, hxS, ↓reduceDIte]
    have hπC : R.edge.proj ⟨x, hxS⟩ ∈ R.edge.cbase ↔
        0 ≤ R.slimPieces.residualFn (F.horizontal e) x := by
      rw [hxeq]
      have h := Set.ext_iff.1 hCU (R.edge.proj ⟨x, hxS⟩)
      exact ⟨fun hc => (h.1 ⟨hc, hU'U hπU'⟩).2, fun h0 => (h.2 ⟨hU'U hπU', h0⟩).1⟩
    rw [← hedge, hT]
    constructor
    · rintro ⟨z, ⟨hz1, hz2⟩, hzx⟩
      have : z = ⟨(x : W.Carrier), hxS⟩ := Subtype.ext hzx
      subst this
      exact ⟨hπC.1 hz1, sub_nonpos.2 hz2⟩
    · rintro ⟨h0, ht⟩
      exact ⟨⟨x, hxS⟩, ⟨hπC.2 h0, sub_nonpos.1 ht⟩, rfl⟩
  · intro x hx hxS
    obtain ⟨-, hxS', hπU', -⟩ := hxΩ x hx
    exact hU'comp _ hπU'

end StageCutRows74

end GC.GraphManifold.Assembly.FC39P0
