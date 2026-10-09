import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.FC39StageRowsLink74

/-!
# From the abstract stage link to the boundary-vocabulary tables (draft 74, D74-5, D74-16)

Lane S-LANDING (`_LND74`), G3b kernel. On the boundary route the rows live directly on `W` (no
carrier identification) and the link of D74-16 is stated with the decomposition's own sets: the
stage sources `X_j = Bs.source j` (with the whole fibres `X_j ∩ f_j⁻¹{y}`), the open edge parent,
`ι` into the slim / edge / circle base `B_j`. This module is the plain-data bridge from
`StageRowsLink74` (lane S-JUNCTIONS) to those tables:

* `StageIdentSrc_LND74 Q q ι src`: the open parent of `Q` IS the source `src`, `ι` embeds the base
  of `Q` into the ambient base type and `ι ∘ Q.proj = q` on the parent;
* `stageSetSrc_LND74`: the whole `Q`-preimage of `S` is `src ∩ q⁻¹(ι S)`;
* `slimLinkSrc_of_stage_LND74`, `edgeLinkSrc_of_stage_LND74`, `circleLinkSrc_of_stage_LND74`:
  the slim / edge / circle fields of `BoundaryRowsLink` in plain form.
-/

set_option autoImplicit false

noncomputable section

open Set Function
open DifferentialGeometry DifferentialGeometry.Topology GC.Endpoint GC.Seifert GC.GraphManifold
open Manifold
open scoped Manifold ContDiff Topology

universe u v

namespace GC.GraphManifold.Assembly.FC39P0

variable {W : CompactCarrier.{u}} {Bs : Type v} [TopologicalSpace Bs]

/-- **Identification of a stage with the decomposition's final map and source**: the open parent
of `Q` is the source `src`, `ι` embeds the base of `Q` into the ambient base type, and
`ι ∘ Q.proj = q` on the parent. -/
structure StageIdentSrc_LND74 {k : ℕ} (Q : StageProj74 W k) (q : W.Carrier → Bs)
    (ι : Q.Base → Bs) (src : Set W.Carrier) : Prop where
  emb : Topology.IsEmbedding ι
  proj_eq : ∀ x : Q.parent, ι (Q.proj x) = q x
  parent_eq : (Q.parent : Set W.Carrier) = src

/-- The whole `Q`-preimage of `S` is `src ∩ q⁻¹(ι S)`. -/
theorem stageSetSrc_LND74 {k : ℕ} {Q : StageProj74 W k} {q : W.Carrier → Bs} {ι : Q.Base → Bs}
    {src : Set W.Carrier} (h : StageIdentSrc_LND74 Q q ι src) (S : Set Q.Base) :
    {x | ∃ hx : x ∈ Q.parent, Q.proj ⟨x, hx⟩ ∈ S} = src ∩ q ⁻¹' (ι '' S) := by
  ext x
  constructor
  · rintro ⟨hx, hS⟩
    refine ⟨by rw [← h.parent_eq]; exact hx, ?_⟩
    rw [mem_preimage, ← h.proj_eq ⟨x, hx⟩]
    exact ⟨_, hS, rfl⟩
  · rintro ⟨hx, y, hy, hyx⟩
    have hpar : x ∈ Q.parent := by
      rw [← SetLike.mem_coe, h.parent_eq]
      exact hx
    refine ⟨hpar, ?_⟩
    have h2 : Q.proj ⟨x, hpar⟩ = y := h.emb.injective ((h.proj_eq ⟨x, hpar⟩).trans hyx.symm)
    rw [h2]
    exact hy

section Slim

variable {n : ℕ} {E : BoundaryTori W n} {A : SmoothStageGeometry74 W E} {D : StageCutChoice74 A}
  {Rw : FC39RowsV2 W E} {q : W.Carrier → Bs} {ι : A.slim.Base → Bs} {src : Set W.Carrier}

/-- **The slim fields of the boundary link from the abstract link**: the pieces are the whole
`f₃`-preimages (inside the source `X₃`) of the components of `D₃`. -/
theorem slimLinkSrc_of_stage_LND74 (L : ZeroSlimLink74 A D Rw)
    (hid : StageIdentSrc_LND74 A.slim.toStageProj74 q ι src) {D₃c : Set Bs}
    (hD : ι '' D.D₃ = D₃c) (comp : ActualComponent D.D₃ ≃ ActualComponent D₃c)
    (hcomp : ∀ c, ι '' c.1 = (comp c).1) :
    Rw.slim.union = src ∩ q ⁻¹' D₃c ∧
      ∃ σ : Fin Rw.slim.count ≃ ActualComponent D₃c, ∀ j,
        range (Rw.slim.piece j).map = src ∩ q ⁻¹' (σ j).1 := by
  obtain ⟨-, -, hun, e, he⟩ := L
  refine ⟨?_, e.trans comp, fun j => ?_⟩
  · rw [hun, ← hD, ← stageSetSrc_LND74 hid]
    rfl
  · change range (Rw.slim.piece j).map = src ∩ q ⁻¹' (comp (e j)).1
    rw [he j, ← hcomp, ← stageSetSrc_LND74 hid]

end Slim

section Edge

variable {n : ℕ} {E : BoundaryTori W n} {A : SmoothStageGeometry74 W E} {D : StageCutChoice74 A}
  {Rw : FC39RowsV2 W E} {q : W.Carrier → Bs} {ι : A.edge.Base → Bs} {Hs : W.Carrier → ℝ}
  {lvl : ℝ} {edgeParent : Set W.Carrier}

/-- **The edge fields of the boundary link from the abstract link**: the rows' edge base embeds into
the ambient base with the FINAL map `q = f₂`, the height `Hs`, the level, WHOLE disks
`X₂ ∩ f₂⁻¹{y}` (`X₂ = edgeParent ∩ {Hs ≤ lvl}`), and the edge piece. -/
theorem edgeLinkSrc_of_stage_LND74 (L : EdgeLink74 A D Rw)
    (hid : StageIdentSrc_LND74 A.edge.toStageProj74 q ι edgeParent)
    (hH : ∀ x : A.edge.parent, A.edge.height x = Hs x) (hlvl : A.edge.level = lvl)
    {base1 : Set Bs} (hrange : range ι ⊆ base1) {src1 : Set W.Carrier}
    (hsrc1 : src1 = edgeParent ∩ {p | Hs p ≤ lvl}) {edgePieceB : Set W.Carrier}
    (hC : ι '' D.C₂ = q '' edgePieceB)
    (hE : edgePieceB = edgeParent ∩ q ⁻¹' (ι '' D.C₂) ∩ {p | Hs p ≤ lvl}) :
    ∃ ι' : Rw.edge.Base → Bs, Topology.IsEmbedding ι' ∧ range ι' ⊆ base1 ∧
      ι' '' Rw.edge.cbase = q '' edgePieceB ∧
      (∀ x : Rw.edge.source, (x : W.Carrier) ∈ edgeParent ∧ ι' (Rw.edge.proj x) = q x ∧
        Rw.edge.height x = Hs x) ∧ Rw.edge.level = lvl ∧
      (∀ c', Rw.edge.disk c' = src1 ∩ q ⁻¹' {ι' c'}) ∧ Rw.edge.edgePiece = edgePieceB := by
  obtain ⟨hsrc, ⟨e, he, hCb⟩, hht, hlv, hpc⟩ := L
  have hemb : Topology.IsEmbedding fun c => ι ((e c : D.edgeBaseOpen) : A.edge.Base) :=
    hid.emb.comp (Topology.IsEmbedding.subtypeVal.comp e.toHomeomorph.isEmbedding)
  have hcb : (fun c => ι ((e c : D.edgeBaseOpen) : A.edge.Base)) '' Rw.edge.cbase =
      q '' edgePieceB := by
    rw [← hC, ← hCb, image_image, image_image]
  have h5 : ∀ x : Rw.edge.source, (x : W.Carrier) ∈ edgeParent ∧
      ι ((e (Rw.edge.proj x) : D.edgeBaseOpen) : A.edge.Base) = q x ∧
        Rw.edge.height x = Hs x := by
    intro x
    obtain ⟨h, hx⟩ := he x
    obtain ⟨h', hh⟩ := hht x
    refine ⟨?_, ?_, ?_⟩
    · rw [← hid.parent_eq]
      exact h
    · rw [hx]
      exact hid.proj_eq ⟨x, h⟩
    · rw [hh]
      exact hH ⟨x, h'⟩
  refine ⟨_, hemb, ?_, hcb, h5, hlv.trans hlvl, fun c' => ?_, ?_⟩
  · rintro _ ⟨c, rfl⟩
    exact hrange ⟨_, rfl⟩
  · ext y
    constructor
    · rintro ⟨x, ⟨hP, hφ⟩, rfl⟩
      obtain ⟨hpar, hproj, hheight⟩ := h5 x
      refine ⟨?_, ?_⟩
      · rw [hsrc1]
        exact ⟨hpar, by rw [mem_ofPred_eq, ← hheight, ← hlv.trans hlvl]; exact hφ⟩
      · change q x = _
        rw [← hproj, hP]
    · rintro ⟨hy1, hy2⟩
      rw [hsrc1] at hy1
      obtain ⟨hyp, hyh⟩ := hy1
      have hy2' : q y = ι ((e c' : D.edgeBaseOpen) : A.edge.Base) := hy2
      have hpar : y ∈ A.edge.parent := by
        rw [← SetLike.mem_coe, hid.parent_eq]
        exact hyp
      have h2 : A.edge.proj ⟨y, hpar⟩ = ((e c' : D.edgeBaseOpen) : A.edge.Base) :=
        hid.emb.injective ((hid.proj_eq ⟨y, hpar⟩).trans hy2')
      have hmem : y ∈ (Rw.edge.source : Set W.Carrier) := by
        rw [hsrc]
        exact (A.edge.mem_restrictParent).2 ⟨hpar, by rw [h2]; exact (e c').2⟩
      have h3 : e (Rw.edge.proj ⟨y, hmem⟩) = e c' := Subtype.ext (by
        obtain ⟨h0, hx0⟩ := he ⟨y, hmem⟩
        rw [hx0]
        exact h2)
      refine ⟨⟨y, hmem⟩, ⟨e.injective h3, ?_⟩, rfl⟩
      obtain ⟨h', hh⟩ := hht ⟨y, hmem⟩
      rw [(h5 ⟨y, hmem⟩).2.2, hlv, hlvl]
      exact hyh
  · rw [hpc, hE]
    ext x
    constructor
    · rintro ⟨hx, hc, hh⟩
      have hxp : x ∈ edgeParent := by
        rw [← hid.parent_eq]
        exact hx
      refine ⟨⟨hxp, ?_⟩, ?_⟩
      · rw [mem_preimage, ← hid.proj_eq ⟨x, hx⟩]
        exact ⟨_, hc, rfl⟩
      · rw [mem_ofPred_eq, ← hH ⟨x, hx⟩, ← hlvl]
        exact hh
    · rintro ⟨⟨hxp, hq⟩, hh⟩
      have hpar : x ∈ A.edge.parent := by
        rw [← SetLike.mem_coe, hid.parent_eq]
        exact hxp
      obtain ⟨y, hy, hyx⟩ := hq
      have h2 : A.edge.proj ⟨x, hpar⟩ = y :=
        hid.emb.injective ((hid.proj_eq ⟨x, hpar⟩).trans hyx.symm)
      refine ⟨hpar, by rw [h2]; exact hy, ?_⟩
      rw [hH ⟨x, hpar⟩, hlvl]
      exact hh

end Edge

section Circle

variable {n : ℕ} {E : BoundaryTori W n} {A : SmoothStageGeometry74 W E} {D : StageCutChoice74 A}
  {Rw : FC39RowsV2 W E} {q : W.Carrier → Bs} {ι : A.circle.Base → Bs} {src0 : Set W.Carrier}

/-- **The circle fields of the boundary link from the abstract link**: the rows' circle base embeds
into the ambient base with the FINAL map `q = f₁`, the domain lies in the source `X₁`, the
fibres are the WHOLE fibres `X₁ ∩ f₁⁻¹{y}`, the region is the remainder `R_c`. -/
theorem circleLinkSrc_of_stage_LND74 (L : CircleLink74 A D Rw)
    (hid : StageIdentSrc_LND74 A.circle q ι src0) {base0 : Set Bs} (hrange : range ι ⊆ base0)
    {remB : Set W.Carrier} (hC : ι '' D.C₁ = q '' remB)
    (hR : remB = src0 ∩ q ⁻¹' (ι '' D.C₁)) :
    ∃ ι' : Rw.circle.Base → Bs, Topology.IsEmbedding ι' ∧ range ι' ⊆ base0 ∧
      ι' '' Rw.circle.cbase = q '' remB ∧
      (∀ x : Rw.circle.domain, (x : W.Carrier) ∈ src0 ∧ ι' (Rw.circle.proj x) = q x) ∧
      (∀ c', Rw.circle.fibre c' = src0 ∩ q ⁻¹' {ι' c'}) ∧ Rw.circle.region = remB := by
  obtain ⟨hdom, ⟨e, he, hCb⟩, hregion⟩ := L
  have hemb : Topology.IsEmbedding fun c => ι ((e c : D.circleBaseOpen) : A.circle.Base) :=
    hid.emb.comp (Topology.IsEmbedding.subtypeVal.comp e.toHomeomorph.isEmbedding)
  have hcb : (fun c => ι ((e c : D.circleBaseOpen) : A.circle.Base)) '' Rw.circle.cbase =
      q '' remB := by
    rw [← hC, ← hCb, image_image, image_image]
  have h4 : ∀ x : Rw.circle.domain, (x : W.Carrier) ∈ src0 ∧
      ι ((e (Rw.circle.proj x) : D.circleBaseOpen) : A.circle.Base) = q x := by
    intro x
    obtain ⟨h, hx⟩ := he x
    refine ⟨?_, ?_⟩
    · rw [← hid.parent_eq]
      exact h
    · rw [hx]
      exact hid.proj_eq ⟨x, h⟩
  refine ⟨_, hemb, ?_, hcb, h4, fun c' => ?_, ?_⟩
  · rintro _ ⟨c, rfl⟩
    exact hrange ⟨_, rfl⟩
  · ext y
    constructor
    · rintro ⟨x, hx, rfl⟩
      have hx' : Rw.circle.proj x = c' := hx
      obtain ⟨hs, hq⟩ := h4 x
      exact ⟨hs, by rw [mem_preimage, ← hq, hx']; rfl⟩
    · rintro ⟨hy1, hy2⟩
      have hy2' : q y = ι ((e c' : D.circleBaseOpen) : A.circle.Base) := hy2
      have hpar : y ∈ A.circle.parent := by
        rw [← SetLike.mem_coe, hid.parent_eq]
        exact hy1
      have h2 : A.circle.proj ⟨y, hpar⟩ = ((e c' : D.circleBaseOpen) : A.circle.Base) :=
        hid.emb.injective ((hid.proj_eq ⟨y, hpar⟩).trans hy2')
      have hmem : y ∈ (Rw.circle.domain : Set W.Carrier) := by
        rw [hdom]
        exact (A.circle.mem_restrictParent).2 ⟨hpar, by rw [h2]; exact (e c').2⟩
      refine ⟨⟨y, hmem⟩, ?_, rfl⟩
      have h3 : e (Rw.circle.proj ⟨y, hmem⟩) = e c' := Subtype.ext (by
        obtain ⟨h0, hx0⟩ := he ⟨y, hmem⟩
        rw [hx0]
        exact h2)
      exact e.injective h3
  · rw [hregion, hR, ← stageSetSrc_LND74 hid]
    rfl

end Circle

section CutSets

variable {n : ℕ} {E : BoundaryTori W n} {A : SmoothStageGeometry74 W E} {D : StageCutChoice74 A}

/-- `M^edge = q₁⁻¹(C₂) ∩ {T ≤ level}` on `W`, inside the open edge parent. -/
theorem edgeSetSrc_of_stage_LND74 {q : W.Carrier → Bs} {ι : A.edge.Base → Bs}
    {Hs : W.Carrier → ℝ} {lvl : ℝ} {edgeParent : Set W.Carrier}
    (hid : StageIdentSrc_LND74 A.edge.toStageProj74 q ι edgeParent)
    (hH : ∀ x : A.edge.parent, A.edge.height x = Hs x) (hlvl : A.edge.level = lvl) :
    D.edgeSet = edgeParent ∩ q ⁻¹' (ι '' D.C₂) ∩ {p | Hs p ≤ lvl} := by
  ext x
  constructor
  · rintro ⟨hx, hc, hh⟩
    have hxp : x ∈ edgeParent := by
      rw [← hid.parent_eq]
      exact hx
    refine ⟨⟨hxp, ?_⟩, ?_⟩
    · rw [mem_preimage, ← hid.proj_eq ⟨x, hx⟩]
      exact ⟨_, hc, rfl⟩
    · rw [mem_ofPred_eq, ← hH ⟨x, hx⟩, ← hlvl]
      exact hh
  · rintro ⟨⟨hxp, hq⟩, hh⟩
    have hpar : x ∈ A.edge.parent := by
      rw [← SetLike.mem_coe, hid.parent_eq]
      exact hxp
    obtain ⟨y, hy, hyx⟩ := hq
    have h2 : A.edge.proj ⟨x, hpar⟩ = y :=
      hid.emb.injective ((hid.proj_eq ⟨x, hpar⟩).trans hyx.symm)
    refine ⟨hpar, by rw [h2]; exact hy, ?_⟩
    rw [hH ⟨x, hpar⟩, hlvl]
    exact hh

omit [TopologicalSpace Bs] in
/-- **The regions of the boundary link from the abstract link**: `M₁` (zero domains and cusp
cores), `M₂ = M₁ ∖ int_{M₁} S`, `M₃ = M₂ ∖ int_{M₂} P_e` (relative interiors, §5.7) and the circle
region `R_c = M₃`. -/
theorem regionsLinkSrc_of_stage_LND74 {Rw : FC39RowsV2 W E} (L : RegionsLink74 A D Rw)
    {M₁c pieceB edgeB M₂c M₃c : Set W.Carrier} (hM₁ : regionM1 A.zero A.cusp = M₁c)
    (hS : D.slimSet = pieceB) (hE : D.edgeSet = edgeB) (hM₂ : M₂c = M₁c \ relInt M₁c pieceB)
    (hM₃ : M₃c = M₂c \ relInt M₂c edgeB) :
    regionM1 Rw.zero Rw.cusp = M₁c ∧ regionM2 Rw.slim = M₂c ∧
      regionM3 Rw.slim Rw.edge = M₃c ∧ Rw.circle.region = M₃c := by
  have h2 : D.M₂ = M₂c := by
    change regionM1 A.zero A.cusp \ relInt (regionM1 A.zero A.cusp) D.slimSet = _
    rw [hM₁, hS, hM₂]
  have h3 : D.M₃ = M₃c := by
    change D.M₂ \ relInt D.M₂ D.edgeSet = _
    rw [h2, hE, hM₃]
  exact ⟨L.regionM1_eq.trans hM₁, L.regionM2_eq.trans h2, L.regionM3_eq.trans h3,
    L.region_M3.trans h3⟩

end CutSets

end GC.GraphManifold.Assembly.FC39P0
