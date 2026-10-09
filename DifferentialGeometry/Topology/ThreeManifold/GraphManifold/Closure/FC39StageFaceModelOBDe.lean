import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.FC39StageCuspKitOBDe

/-!
# Cusp-aware local models of `M₂` at a residual face, part 2: cusp fronts and the dispatcher

Lane O-BD1 (by S-BD2e), G11c (suffix `_OBDe`). Continues `FC39StageCuspKitOBDe`:

* NEW `faceModel_cusp_OBDe`: at a point of the front of a cusp core lying in `M₂`, an open set on
  which `M₂ = {cuspFn ≥ 0}` and `{cuspFn = 0}` is the front (the slim set is absent by `hKR`, the
  zero domains and the other cores by disjointness, the core is `{cuspFn ≤ 0}` by `near_eq`);
* `exists_faceModel_OBDe`: the drop-in replacement of `exists_faceModel_JN74` without
  `[IsEmpty (Fin n)]`, for every residual face (zero face, cusp front, new end).
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
  {A : SmoothStageGeometry74 W E} {D : StageCutChoice74 A}

/-- **The local model of `M₂` at a point of a cusp front.** -/
theorem faceModel_cusp_OBDe (R : StageCutRows74 A D) (cov : CutCoverFacts74 A D)
    (hKR : ∀ F : NeighbourFace A.zero A.cusp, neighbourSet F ∩ D.slimSet ⊆
      relInt (regionM1 A.zero A.cusp) D.slimSet)
    (b : Fin n) {x₀ : W.Carrier} (hx₀ : x₀ ∈ cuspFront_OBDe A.cusp b) (hM : x₀ ∈ D.M₂) :
    ∃ O : Set W.Carrier, IsOpen O ∧ x₀ ∈ O ∧ O ⊆ (A.cusp.near b : Set W.Carrier) ∧
      (∀ x ∈ O, x ∈ D.M₂ ↔ 0 ≤ A.cusp.cuspFn b x) ∧
      ∀ x ∈ O, A.cusp.cuspFn b x = 0 → x ∈ cuspFront_OBDe A.cusp b := by
  classical
  have hlevel : cuspFront_OBDe A.cusp b =
      {x | x ∈ A.cusp.near b ∧ A.cusp.cuspFn b x = 0} := A.cusp.internal_eq b
  have hxn : x₀ ∈ A.cusp.near b := by
    have h' : x₀ ∈ {x | x ∈ A.cusp.near b ∧ A.cusp.cuspFn b x = 0} := hlevel ▸ hx₀
    exact h'.1
  have hx₀r : x₀ ∈ range (A.cusp.piece b).map := by
    obtain ⟨t, rfl⟩ := hx₀
    exact ⟨_, rfl⟩
  have hM' : x₀ ∈ regionM1 A.zero A.cusp \ relInt (regionM1 A.zero A.cusp) D.slimSet := hM
  have hnosl : x₀ ∉ D.slimSet := fun hs =>
    hM'.2 (hKR (cuspFrontFace_OBDe A.zero A.cusp b)
      ⟨by rw [neighbourSet_cuspFrontFace_OBDe]; exact hx₀, hs⟩)
  have hZc : IsClosed (⋃ i, range (A.zero.piece i).map) := isClosed_zeroUnion_OBDe A.zero
  have hnoZ : x₀ ∉ ⋃ i, range (A.zero.piece i).map := by
    intro h
    obtain ⟨i, hi⟩ := mem_iUnion.1 h
    exact disjoint_left.1 (cov.zero_cusp_disjoint i b) hi hx₀r
  let Co : Set W.Carrier := ⋃ b' ∈ {b' : Fin n | b' ≠ b}, range (A.cusp.piece b').map
  have hCo : IsClosed Co :=
    (Set.toFinite _).isClosed_biUnion fun j _ => (A.cusp.piece j).isClosed_range
  have hnoCo : x₀ ∉ Co := by
    intro h
    obtain ⟨b', hb', hxb'⟩ := mem_iUnion₂.1 h
    exact disjoint_left.1 (A.cusp.disjoint (Ne.symm hb')) hx₀r hxb'
  refine ⟨(D.slimSet)ᶜ ∩ (⋃ i, range (A.zero.piece i).map)ᶜ ∩ Coᶜ ∩ (A.cusp.near b : Set W.Carrier),
    (((isClosed_slimSet_JN74 R).isOpen_compl.inter hZc.isOpen_compl).inter
      hCo.isOpen_compl).inter (A.cusp.near b).isOpen,
    ⟨⟨⟨hnosl, hnoZ⟩, hnoCo⟩, hxn⟩, fun x hx => hx.2, ?_, ?_⟩
  · intro x hx
    obtain ⟨⟨⟨hxsl, hxZ⟩, hxCo⟩, hxn'⟩ := hx
    have hxint : x ∈ W.interior := A.cusp.near_interior b hxn'
    have hxrel : x ∉ relInt (regionM1 A.zero A.cusp) D.slimSet := fun h =>
      hxsl (relInt_subset_JN74 h)
    have hM2 : x ∈ D.M₂ ↔ x ∈ regionM1 A.zero A.cusp := by
      change x ∈ regionM1 A.zero A.cusp \ relInt (regionM1 A.zero A.cusp) D.slimSet ↔ _
      exact ⟨fun h => h.1, fun h => ⟨h, hxrel⟩⟩
    have hint1 : x ∈ interior ((⋃ i, range (A.zero.piece i).map) ∪
        ⋃ b', range (A.cusp.piece b').map) ↔ x ∈ interior (range (A.cusp.piece b).map) := by
      constructor
      · intro h
        rw [mem_interior] at h ⊢
        obtain ⟨V, hV, hVo, hxV⟩ := h
        refine ⟨V ∩ ((⋃ i, range (A.zero.piece i).map)ᶜ ∩ Coᶜ), ?_, hVo.inter
          (hZc.isOpen_compl.inter hCo.isOpen_compl), hxV, ⟨hxZ, hxCo⟩⟩
        rintro y ⟨hyV, hyZ, hyCo⟩
        rcases hV hyV with hz | hc
        · exact absurd hz hyZ
        · obtain ⟨b', hb'⟩ := mem_iUnion.1 hc
          by_cases hbb : b' = b
          · subst hbb
            exact hb'
          · exact absurd (mem_iUnion₂.2 ⟨b', hbb, hb'⟩) hyCo
      · intro h
        refine interior_mono ?_ h
        exact fun y hy => Or.inr (mem_iUnion.2 ⟨b, hy⟩)
    have hint2 : x ∈ interior (range (A.cusp.piece b).map) ↔ A.cusp.cuspFn b x < 0 := by
      constructor
      · intro h
        refine lt_of_mem_interior_sublevel_JN74 hxint
          (((A.cusp.fn_smooth b).contMDiffAt
            ((A.cusp.near b).isOpen.mem_nhds hxn')).mdifferentiableAt (by simp))
          (fun h0 => A.cusp.fn_regular b x hxn' h0) ?_
        refine mem_interior.2 ⟨interior (range (A.cusp.piece b).map) ∩
          (A.cusp.near b : Set W.Carrier), ?_, isOpen_interior.inter (A.cusp.near b).isOpen,
          ⟨h, hxn'⟩⟩
        rintro y ⟨hyI, hyn⟩
        have := (Set.ext_iff.1 (A.cusp.near_eq b) y).1 ⟨interior_subset hyI, hyn⟩
        exact this.2
      · intro hlt
        refine mem_interior.2 ⟨(A.cusp.near b : Set W.Carrier) ∩ A.cusp.cuspFn b ⁻¹' Iio 0, ?_,
          (A.cusp.fn_smooth b).continuousOn.isOpen_inter_preimage (A.cusp.near b).isOpen
            isOpen_Iio, ⟨hxn', hlt⟩⟩
        rintro y ⟨hy2, hy1⟩
        have := (Set.ext_iff.1 (A.cusp.near_eq b) y).2
          ⟨hy2, le_of_lt (show A.cusp.cuspFn b y < 0 from hy1)⟩
        exact this.1
    rw [hM2]
    change x ∈ (interior ((⋃ i, range (A.zero.piece i).map) ∪
        ⋃ b', range (A.cusp.piece b').map))ᶜ ↔ _
    rw [mem_compl_iff, hint1, hint2, not_lt]
  · intro x hx h0
    rw [hlevel]
    exact ⟨hx.2, h0⟩

/-- **The local model of `M₂` at a point of a residual face** (zero face, cusp front or new slim
end; the cusp cores kept): an open neighbourhood of the point in the face neighbourhood on which
`M₂ = {h_F ≥ 0}` and the zero set of `h_F` is the face. -/
theorem exists_faceModel_OBDe (R : StageCutRows74 A D) (cov : CutCoverFacts74 A D)
    (F : JunctionFaceFacts74 A D R)
    (hKR : ∀ F : NeighbourFace A.zero A.cusp, neighbourSet F ∩ D.slimSet ⊆
      relInt (regionM1 A.zero A.cusp) D.slimSet)
    (Fl : R.slimPieces.ResidualFace) {x₀ : W.Carrier} (hx₀ : x₀ ∈ R.slimPieces.residualSet Fl) :
    ∃ O : Set W.Carrier, IsOpen O ∧ x₀ ∈ O ∧ O ⊆ (R.slimPieces.residualNear Fl : Set W.Carrier) ∧
      (∀ x ∈ O, x ∈ D.M₂ ↔ 0 ≤ R.slimPieces.residualFn Fl x) ∧
      ∀ x ∈ O, R.slimPieces.residualFn Fl x = 0 → x ∈ R.slimPieces.residualSet Fl := by
  have hfr : x₀ ∈ frontier D.M₂ := by
    rw [F.frontier_M2]
    exact mem_iUnion.2 ⟨Fl, hx₀⟩
  have hM : x₀ ∈ D.M₂ := (isClosed_M₂_JN74 D).frontier_subset hfr
  rcases Fl with ⟨F' | F', hF'⟩ | e
  · exact faceModel_zero_OBDe R cov hKR F'.1 F'.2 hx₀ hM
  · obtain ⟨b, Fm, hFm⟩ := F'
    subst hFm
    have hx₁ : x₀ ∈ neighbourSet (cuspFrontFace_OBDe A.zero A.cusp b) := hx₀
    rw [neighbourSet_cuspFrontFace_OBDe] at hx₁
    obtain ⟨O, ho, hxO, hOn, hOm, hOl⟩ := faceModel_cusp_OBDe R cov hKR b hx₁ hM
    refine ⟨O, ho, hxO, hOn, hOm, fun x hx h0 => ?_⟩
    have hx2 := hOl x hx h0
    rw [← neighbourSet_cuspFrontFace_OBDe A.zero A.cusp b] at hx2
    exact hx2
  · exact faceModel_newEnd_OBDe R hKR e hx₀ hM

end GC.GraphManifold.Assembly.FC39P0
