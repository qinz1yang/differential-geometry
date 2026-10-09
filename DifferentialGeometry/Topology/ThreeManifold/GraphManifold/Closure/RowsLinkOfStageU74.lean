import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.RowsLinkOfStage74

/-!
# Revised edge table: the open ambient parent `U₂ ∩ q₁⁻¹(V)` (draft 74 §1.3, D74-11)

Lane S-LANDING (`_LND74`), G2d (named revision of the closed landing, review by O-CL0). The first
edge table (`EdgeLink_LND74`, `StageIdent_LND74`) used the WHOLE preimage `q₁⁻¹(V)`; but `q₁` is a
submersion only on the open threshold-5 domain `U₂` (with `T ≤ 4Δ`). The correct source of the edge
bundle over the good open base `V` is the open ambient parent restriction `U₂ ∩ q₁⁻¹(V)`:

* `StageIdentU_LND74 ψ Q q ι U`: the open parent of `Q` is `ψ(U)` (no whole-preimage clause),
  `ι` embeds the base of `Q`, `ι ∘ Q.proj = q ∘ ψ⁻¹`;
* `stageSetU_LND74`: the whole `Q`-preimage of `S` is `ψ(U ∩ q⁻¹(ι S))`;
* `EdgeLinkU_LND74`: the edge table with source `ψ(U ∩ q⁻¹ V)` and disks / rims `ψ(U ∩ {…})`;
* `edgeLinkU_of_stage_LND74`: it from `EdgeLink74` and the identification;
  `edgeSetWU_of_stage_LND74`: `M^edge` on `W`.
-/

set_option autoImplicit false

noncomputable section

open Set Function
open DifferentialGeometry DifferentialGeometry.Topology GC.Endpoint GC.Seifert GC.GraphManifold
open GC.GraphManifold.Assembly
open Manifold
open scoped Manifold ContDiff Topology

universe u v w

namespace GC.GraphManifold.Assembly.FC39P0

variable {X : Type v} {Bs : Type w} [TopologicalSpace Bs] {W : CompactCarrier.{u}}

/-- **Edge table with the open ambient parent** `U ∩ q⁻¹(V)`: `U` the open threshold-5 domain,
`q` the FINAL `q₁`, `Hs` the height, `lvl` the level, `baseOpen` the good open base. -/
def EdgeLinkU_LND74 (ψ : X ≃ W.Carrier) (P : EdgeBundle W) (q : X → Bs) (Hs : X → ℝ) (lvl : ℝ)
    (baseOpen cb : Set Bs) (U edgeSet : Set X) : Prop :=
  ∃ ι : P.Base → Bs, Topology.IsEmbedding ι ∧ range ι = baseOpen ∧ ι '' P.cbase = cb ∧
    (P.source : Set W.Carrier) = ψ '' (U ∩ q ⁻¹' baseOpen) ∧
    (∀ x : P.source, ι (P.proj x) = q (ψ.symm x) ∧ P.height x = Hs (ψ.symm x)) ∧
    P.level = lvl ∧
    (∀ c, P.disk c = ψ '' (U ∩ {p | q p = ι c ∧ Hs p ≤ lvl})) ∧
    (∀ c, P.rim c = ψ '' (U ∩ {p | q p = ι c ∧ Hs p = lvl})) ∧
    P.edgePiece = ψ '' edgeSet

/-- **Identification of a stage with the chain's final map on the open domain `U`**: the open parent
of `Q` is `ψ(U)`, `ι` embeds the base of `Q`, and `ι ∘ Q.proj = q ∘ ψ⁻¹`. -/
structure StageIdentU_LND74 {k : ℕ} (ψ : X ≃ W.Carrier) (Q : StageProj74 W k) (q : X → Bs)
    (ι : Q.Base → Bs) (U : Set X) : Prop where
  emb : Topology.IsEmbedding ι
  proj_eq : ∀ x : Q.parent, ι (Q.proj x) = q (ψ.symm x)
  parent_eq : (Q.parent : Set W.Carrier) = ψ '' U

/-- The whole `Q`-preimage of `S` is `ψ(U ∩ q⁻¹(ι S))`. -/
theorem stageSetU_LND74 {k : ℕ} {ψ : X ≃ W.Carrier} {Q : StageProj74 W k} {q : X → Bs}
    {ι : Q.Base → Bs} {U : Set X} (h : StageIdentU_LND74 ψ Q q ι U) (S : Set Q.Base) :
    {x | ∃ hx : x ∈ Q.parent, Q.proj ⟨x, hx⟩ ∈ S} = ψ '' (U ∩ q ⁻¹' (ι '' S)) := by
  ext x
  constructor
  · rintro ⟨hx, hS⟩
    have hxU : x ∈ ψ '' U := h.parent_eq ▸ hx
    obtain ⟨u, hu, rfl⟩ := hxU
    refine ⟨u, ⟨hu, ?_⟩, rfl⟩
    rw [mem_preimage, ← ψ.symm_apply_apply u, ← h.proj_eq ⟨ψ u, hx⟩]
    exact ⟨_, hS, rfl⟩
  · rintro ⟨u, ⟨hu, y, hy, hyu⟩, rfl⟩
    have hpar : ψ u ∈ Q.parent := by
      rw [← SetLike.mem_coe, h.parent_eq]
      exact ⟨u, hu, rfl⟩
    refine ⟨hpar, ?_⟩
    have h1 := h.proj_eq ⟨ψ u, hpar⟩
    rw [ψ.symm_apply_apply] at h1
    have h2 : Q.proj ⟨ψ u, hpar⟩ = y := h.emb.injective (h1.trans hyu.symm)
    rw [h2]
    exact hy

section Edge

variable {ψ : X ≃ W.Carrier} {n : ℕ} {E : BoundaryTori W n} {A : SmoothStageGeometry74 W E}
  {D : StageCutChoice74 A} {Rw : FC39RowsV2 W E} {q : X → Bs} {ι : A.edge.Base → Bs}
  {Hs : X → ℝ} {Vc Cc : Set Bs} {lvl : ℝ} {U : Set X}

/-- `M^edge` on `W`: the `ψ`-image of `U ∩ q⁻¹(C₂) ∩ {T ≤ level}`. -/
theorem edgeSetWU_of_stage_LND74 (hid : StageIdentU_LND74 ψ A.edge.toStageProj74 q ι U)
    (hH : ∀ x : A.edge.parent, A.edge.height x = Hs (ψ.symm x)) (hlvl : A.edge.level = lvl)
    (hC : ι '' D.C₂ = Cc) : D.edgeSet = ψ '' (U ∩ (q ⁻¹' Cc ∩ {p | Hs p ≤ lvl})) := by
  ext x
  constructor
  · rintro ⟨hx, hc, hh⟩
    have hxU : x ∈ ψ '' U := hid.parent_eq ▸ hx
    obtain ⟨u, hu, rfl⟩ := hxU
    have hqu : q u = ι (A.edge.proj ⟨ψ u, hx⟩) := by
      rw [hid.proj_eq ⟨ψ u, hx⟩, ψ.symm_apply_apply]
    refine ⟨u, ⟨hu, ?_, ?_⟩, rfl⟩
    · rw [mem_preimage, hqu, ← hC]
      exact ⟨_, hc, rfl⟩
    · change Hs u ≤ lvl
      have h3 := hH ⟨ψ u, hx⟩
      rw [ψ.symm_apply_apply] at h3
      rw [← h3, ← hlvl]
      exact hh
  · rintro ⟨u, ⟨hu, hq, hh⟩, rfl⟩
    rw [← hC] at hq
    obtain ⟨y, hy, hyu⟩ := hq
    have hpar : ψ u ∈ A.edge.parent := by
      rw [← SetLike.mem_coe, hid.parent_eq]
      exact ⟨u, hu, rfl⟩
    refine ⟨hpar, ?_, ?_⟩
    · have h1 := hid.proj_eq ⟨ψ u, hpar⟩
      rw [ψ.symm_apply_apply] at h1
      have h2 : A.edge.proj ⟨ψ u, hpar⟩ = y := hid.emb.injective (h1.trans hyu.symm)
      rw [h2]
      exact hy
    · have h3 := hH ⟨ψ u, hpar⟩
      rw [ψ.symm_apply_apply] at h3
      change A.edge.height ⟨ψ u, hpar⟩ ≤ A.edge.level
      rw [h3, hlvl]
      exact hh

/-- The level sets of the revised edge table from the smooth equivalence of the abstract link. -/
theorem edgeLevelSetU_LND74 (L : EdgeLink74 A D Rw)
    (hid : StageIdentU_LND74 ψ A.edge.toStageProj74 q ι U)
    (hH : ∀ x : A.edge.parent, A.edge.height x = Hs (ψ.symm x))
    (hV : ι '' (D.edgeBaseOpen : Set A.edge.Base) = Vc) (hlvl : A.edge.level = lvl) :
    ∃ ι' : Rw.edge.Base → Bs, Topology.IsEmbedding ι' ∧ range ι' = Vc ∧
      ι' '' Rw.edge.cbase = ι '' D.C₂ ∧
      (Rw.edge.source : Set W.Carrier) = ψ '' (U ∩ q ⁻¹' Vc) ∧
      (∀ x : Rw.edge.source, ι' (Rw.edge.proj x) = q (ψ.symm x) ∧
        Rw.edge.height x = Hs (ψ.symm x)) ∧ Rw.edge.level = lvl ∧
      ∀ (Pb : Bs → Prop) (φ : ℝ → Prop), (∀ y, Pb y → y ∈ Vc) →
        Subtype.val '' {x : Rw.edge.source | Pb (ι' (Rw.edge.proj x)) ∧
          φ (Rw.edge.height x)} = ψ '' (U ∩ {p | Pb (q p) ∧ φ (Hs p)}) := by
  obtain ⟨hsrc, ⟨e, he, hCb⟩, hht, hlv, -⟩ := L
  have hemb : Topology.IsEmbedding fun c => ι ((e c : D.edgeBaseOpen) : A.edge.Base) :=
    hid.emb.comp (Topology.IsEmbedding.subtypeVal.comp e.toHomeomorph.isEmbedding)
  have hrange : range (fun c => ι ((e c : D.edgeBaseOpen) : A.edge.Base)) = Vc := by
    rw [← hV]
    ext y
    constructor
    · rintro ⟨c, rfl⟩
      exact ⟨_, (e c).2, rfl⟩
    · rintro ⟨z, hz, rfl⟩
      exact ⟨e.symm ⟨z, hz⟩, by simp⟩
  have hsrcX : (Rw.edge.source : Set W.Carrier) = ψ '' (U ∩ q ⁻¹' Vc) := by
    rw [hsrc, ← hV, ← stageSetU_LND74 hid]
    ext x
    exact A.edge.mem_restrictParent
  have h5 : ∀ x : Rw.edge.source,
      ι ((e (Rw.edge.proj x) : D.edgeBaseOpen) : A.edge.Base) = q (ψ.symm x) ∧
        Rw.edge.height x = Hs (ψ.symm x) := by
    intro x
    obtain ⟨h, hx⟩ := he x
    obtain ⟨h', hh⟩ := hht x
    refine ⟨?_, ?_⟩
    · rw [hx]
      exact hid.proj_eq ⟨x, h⟩
    · rw [hh]
      exact hH ⟨x, h'⟩
  have hcb : (fun c => ι ((e c : D.edgeBaseOpen) : A.edge.Base)) '' Rw.edge.cbase =
      ι '' D.C₂ := by
    rw [← hCb, image_image, image_image]
  refine ⟨_, hemb, hrange, hcb, hsrcX, h5, hlv.trans hlvl, fun Pb φ hPb => ?_⟩
  ext y
  constructor
  · rintro ⟨x, ⟨hP, hφ⟩, rfl⟩
    have hxs : (x : W.Carrier) ∈ ψ '' (U ∩ q ⁻¹' Vc) := hsrcX ▸ x.2
    obtain ⟨u, ⟨hu, -⟩, hux⟩ := hxs
    have hxu : ψ.symm x = u := by rw [← hux, ψ.symm_apply_apply]
    refine ⟨ψ.symm x, ⟨hxu ▸ hu, ?_, ?_⟩, ψ.apply_symm_apply _⟩
    · rw [← (h5 x).1]
      exact hP
    · rw [← (h5 x).2]
      exact hφ
  · rintro ⟨p, ⟨hpU, hP, hφ⟩, rfl⟩
    have hmem : ψ p ∈ (Rw.edge.source : Set W.Carrier) := by
      rw [hsrcX]
      exact ⟨p, ⟨hpU, hPb _ hP⟩, rfl⟩
    have hx5 := h5 ⟨ψ p, hmem⟩
    simp only [Equiv.symm_apply_apply] at hx5
    exact ⟨⟨ψ p, hmem⟩, ⟨by rw [hx5.1]; exact hP, by rw [hx5.2]; exact hφ⟩, rfl⟩

/-- **The revised edge table from the abstract link**: with source `ψ(U ∩ q⁻¹ V)`; `edgeSetc` is
the chain's `M^edge = U ∩ q₁⁻¹(C₂) ∩ {A/s ≤ 4Δ}` (FDC02, inside the open ambient parent). -/
theorem edgeLinkU_of_stage_LND74 (L : EdgeLink74 A D Rw)
    (hid : StageIdentU_LND74 ψ A.edge.toStageProj74 q ι U)
    (hH : ∀ x : A.edge.parent, A.edge.height x = Hs (ψ.symm x))
    (hV : ι '' (D.edgeBaseOpen : Set A.edge.Base) = Vc) (hlvl : A.edge.level = lvl)
    (hC : ι '' D.C₂ = Cc) (hCV : Cc ⊆ Vc) {edgeSetc : Set X}
    (hE : edgeSetc = U ∩ (q ⁻¹' Cc ∩ {p | Hs p ≤ lvl})) :
    EdgeLinkU_LND74 ψ Rw.edge q Hs lvl Vc Cc U edgeSetc := by
  obtain ⟨ι', hemb, hrange, hcb, hsrc, h5, hlv, hgen⟩ := edgeLevelSetU_LND74 L hid hH hV hlvl
  refine ⟨ι', hemb, hrange, hcb.trans hC, hsrc, h5, hlv, fun c => ?_, fun c => ?_, ?_⟩
  · have h := hgen (fun y => y = ι' c) (fun h => h ≤ lvl)
      (fun y hy => hrange ▸ hy ▸ mem_range_self c)
    unfold EdgeBundle.disk
    rw [← h]
    congr 1
    ext x
    simp only [mem_ofPred_eq, hemb.injective.eq_iff, hlv]
  · have h := hgen (fun y => y = ι' c) (fun h => h = lvl)
      (fun y hy => hrange ▸ hy ▸ mem_range_self c)
    unfold EdgeBundle.rim
    rw [← h]
    congr 1
    ext x
    simp only [mem_ofPred_eq, hemb.injective.eq_iff, hlv]
  · have h := hgen (fun y => y ∈ Cc) (fun h => h ≤ lvl) (fun y hy => hrange ▸ hCV hy)
    have hcbC : ι' '' Rw.edge.cbase = Cc := hcb.trans hC
    unfold EdgeBundle.edgePiece
    rw [hE, show U ∩ (q ⁻¹' Cc ∩ {p | Hs p ≤ lvl}) = U ∩ {p | q p ∈ Cc ∧ Hs p ≤ lvl} from rfl,
      ← h]
    congr 1
    ext x
    simp only [mem_ofPred_eq, ← hcbC, hemb.injective.mem_set_image, hlv]

end Edge

end GC.GraphManifold.Assembly.FC39P0
