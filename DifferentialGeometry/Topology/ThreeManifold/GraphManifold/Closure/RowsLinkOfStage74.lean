import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.FC39StageRowsLink74
import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.RowsLinkKernel74
import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.FC39CarrierTransport74

/-!
# From the abstract stage link to the plain-data link tables (draft 74, D74-5)

Lane S-LANDING (`_LND74`), G2 kernel. `StageRowsLink74 A D Rw` (lane S-JUNCTIONS) is the link of
the rows with the stage geometry `A` and cut choice `D` stated on `W`. The closed route states its
link `ClosedRowsLinkAt74` on the ACTUAL chain objects (sets of the model `X`, maps into the block
space) carried to `W` by the ONE identification `ψ`. This module is the plain-data bridge:

* `StageIdent_LND74 ψ Q q ι`: the stage `Q : StageProj74 W k` of `A` IS the chain's final map `q`
  through `ψ` (`ι : Q.Base → Bs` an embedding of the stage base into the block space,
  `ι ∘ Q.proj = q ∘ ψ⁻¹`, and `q⁻¹(range ι)` lies in the parent: the (RF) whole-fibre fact);
* `stageSet_LND74`: the whole `Q`-preimage of `S` is `ψ(q⁻¹(ι S))`;
* the five tables of `RowsLinkKernel74` from the four tables of `StageRowsLink74` and the
  identification: `edgeLink_of_stage_LND74`, `circleLink_of_stage_LND74`,
  `slimLink_of_stage_LND74`, `regionsLink_of_stage_LND74`.
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

variable {X : Type v} [TopologicalSpace X] {Bs : Type w} [TopologicalSpace Bs]
  {W : CompactCarrier.{u}}

/-- **Identification of a stage with the chain's final map** (D74-5): `ι` embeds the base of the
stage `Q` into the block space, `ι ∘ Q.proj = q ∘ ψ⁻¹` on the parent, and the points over the
range of `ι` all lie in the parent (whole fibres, (RF)). -/
structure StageIdent_LND74 {k : ℕ} (ψ : X ≃ W.Carrier) (Q : StageProj74 W k) (q : X → Bs)
    (ι : Q.Base → Bs) : Prop where
  emb : Topology.IsEmbedding ι
  proj_eq : ∀ x : Q.parent, ι (Q.proj x) = q (ψ.symm x)
  parent_pre : ∀ p, q p ∈ range ι → ψ p ∈ Q.parent

omit [TopologicalSpace X] in
/-- **Inhabitant (empty stage family)**: a stage over an EMPTY base is identified with every map
`q` through the empty embedding (the parent is empty, `range ι = ∅`). -/
theorem stageIdent_of_isEmpty_LND74 {k : ℕ} (ψ : X ≃ W.Carrier) (Q : StageProj74 W k)
    [IsEmpty Q.Base] (q : X → Bs) (ι : Q.Base → Bs) : StageIdent_LND74 ψ Q q ι where
  emb := Topology.IsEmbedding.of_subsingleton ι
  proj_eq := fun x => isEmptyElim (Q.proj x)
  parent_pre := fun p hp => by
    obtain ⟨c, -⟩ := hp
    exact isEmptyElim c

omit [TopologicalSpace X] in
/-- The whole `Q`-preimage of `S` is `ψ(q⁻¹(ι S))`. -/
theorem stageSet_LND74 {k : ℕ} {ψ : X ≃ W.Carrier} {Q : StageProj74 W k} {q : X → Bs}
    {ι : Q.Base → Bs} (h : StageIdent_LND74 ψ Q q ι) (S : Set Q.Base) :
    {x | ∃ hx : x ∈ Q.parent, Q.proj ⟨x, hx⟩ ∈ S} = ψ '' (q ⁻¹' (ι '' S)) := by
  ext x
  constructor
  · rintro ⟨hx, hS⟩
    refine ⟨ψ.symm x, ?_, ψ.apply_symm_apply x⟩
    rw [mem_preimage, ← h.proj_eq ⟨x, hx⟩]
    exact ⟨_, hS, rfl⟩
  · rintro ⟨p, ⟨y, hy, hyp⟩, rfl⟩
    have hpar : ψ p ∈ Q.parent := h.parent_pre p ⟨y, hyp⟩
    refine ⟨hpar, ?_⟩
    have h1 := h.proj_eq ⟨ψ p, hpar⟩
    rw [ψ.symm_apply_apply] at h1
    have h2 : Q.proj ⟨ψ p, hpar⟩ = y := h.emb.injective (h1.trans hyp.symm)
    rw [h2]
    exact hy

/-! ## The edge table -/

section Edge

variable {ψ : X ≃ W.Carrier} {n : ℕ} {E : BoundaryTori W n} {A : SmoothStageGeometry74 W E}
  {D : StageCutChoice74 A} {Rw : FC39RowsV2 W E} {q : X → Bs} {ι : A.edge.Base → Bs}
  {Hs : X → ℝ} {Vc Cc : Set Bs} {lvl : ℝ}

omit [TopologicalSpace X] in
/-- The edge row's disks / rims / piece as `ψ`-images of level sets of `q` and `Hs`, from the
smooth equivalence `e` of the abstract link: a common lemma for the three. -/
theorem edgeLevelSet_LND74 (L : EdgeLink74 A D Rw)
    (hid : StageIdent_LND74 ψ A.edge.toStageProj74 q ι)
    (hH : ∀ x : A.edge.parent, A.edge.height x = Hs (ψ.symm x))
    (hV : ι '' (D.edgeBaseOpen : Set A.edge.Base) = Vc) (hlvl : A.edge.level = lvl) :
    ∃ ι' : Rw.edge.Base → Bs, Topology.IsEmbedding ι' ∧ range ι' = Vc ∧
      ι' '' Rw.edge.cbase = ι '' D.C₂ ∧
      (Rw.edge.source : Set W.Carrier) = ψ '' (q ⁻¹' Vc) ∧
      (∀ x : Rw.edge.source, ι' (Rw.edge.proj x) = q (ψ.symm x) ∧
        Rw.edge.height x = Hs (ψ.symm x)) ∧ Rw.edge.level = lvl ∧
      ∀ (Pb : Bs → Prop) (φ : ℝ → Prop), (∀ y, Pb y → y ∈ Vc) →
        Subtype.val '' {x : Rw.edge.source | Pb (ι' (Rw.edge.proj x)) ∧
          φ (Rw.edge.height x)} = ψ '' {p | Pb (q p) ∧ φ (Hs p)} := by
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
  have hsrcX : (Rw.edge.source : Set W.Carrier) = ψ '' (q ⁻¹' Vc) := by
    rw [hsrc, ← hV, ← stageSet_LND74 hid]
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
    refine ⟨ψ.symm x, ⟨?_, ?_⟩, ψ.apply_symm_apply _⟩
    · rw [← (h5 x).1]
      exact hP
    · rw [← (h5 x).2]
      exact hφ
  · rintro ⟨p, ⟨hP, hφ⟩, rfl⟩
    have hmem : ψ p ∈ (Rw.edge.source : Set W.Carrier) := by
      rw [hsrcX]
      exact ⟨p, hPb _ hP, rfl⟩
    have hx5 := h5 ⟨ψ p, hmem⟩
    simp only [Equiv.symm_apply_apply] at hx5
    exact ⟨⟨ψ p, hmem⟩, ⟨by rw [hx5.1]; exact hP, by rw [hx5.2]; exact hφ⟩, rfl⟩

omit [TopologicalSpace X] in
/-- **The edge table from the abstract link**: `EdgeLink74` + the identification of the edge stage
with the chain's final map `q₁`, the height `A/s` and the level, give `EdgeLink_LND74` on the actual
sets (`edgeSetc` is the chain's `M^edge`, which is `q₁⁻¹(C₂) ∩ {A/s ≤ 4Δ}`: FDC02). -/
theorem edgeLink_of_stage_LND74 (L : EdgeLink74 A D Rw)
    (hid : StageIdent_LND74 ψ A.edge.toStageProj74 q ι)
    (hH : ∀ x : A.edge.parent, A.edge.height x = Hs (ψ.symm x))
    (hV : ι '' (D.edgeBaseOpen : Set A.edge.Base) = Vc) (hlvl : A.edge.level = lvl)
    (hC : ι '' D.C₂ = Cc) (hCV : Cc ⊆ Vc) {edgeSetc : Set X}
    (hE : edgeSetc = q ⁻¹' Cc ∩ {p | Hs p ≤ lvl}) :
    EdgeLink_LND74 ψ Rw.edge q Hs lvl Vc Cc (q ⁻¹' Vc) edgeSetc := by
  obtain ⟨ι', hemb, hrange, hcb, hsrc, h5, hlv, hgen⟩ := edgeLevelSet_LND74 L hid hH hV hlvl
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
    rw [hE, show q ⁻¹' Cc ∩ {p | Hs p ≤ lvl} = {p | q p ∈ Cc ∧ Hs p ≤ lvl} from rfl,
      ← h]
    congr 1
    ext x
    simp only [mem_ofPred_eq, ← hcbC, hemb.injective.mem_set_image, hlv]


end Edge

/-! ## The circle table -/

section Circle

variable {ψ : X ≃ W.Carrier} {n : ℕ} {E : BoundaryTori W n} {A : SmoothStageGeometry74 W E}
  {D : StageCutChoice74 A} {Rw : FC39RowsV2 W E} {q : X → Bs} {ι : A.circle.Base → Bs}
  {Vc Cc : Set Bs}

omit [TopologicalSpace X] in
/-- **The circle table from the abstract link**: `CircleLink74` + the identification of the circle
stage with the chain's final map `q₀` give `CircleLink_LND74` on the actual sets (`regc` is the
chain's `M₃`, saturated: `M₃ = q₀⁻¹(C₁)`, FDC03). -/
theorem circleLink_of_stage_LND74 (L : CircleLink74 A D Rw)
    (hid : StageIdent_LND74 ψ A.circle q ι)
    (hV : ι '' (D.circleBaseOpen : Set A.circle.Base) = Vc) (hC : ι '' D.C₁ = Cc)
    {regc : Set X} (hreg : regc = q ⁻¹' Cc) :
    CircleLink_LND74 ψ Rw.circle q Vc Cc (q ⁻¹' Vc) regc := by
  obtain ⟨hdom, ⟨e, he, hCb⟩, hregion⟩ := L
  have hemb : Topology.IsEmbedding fun c => ι ((e c : D.circleBaseOpen) : A.circle.Base) :=
    hid.emb.comp (Topology.IsEmbedding.subtypeVal.comp e.toHomeomorph.isEmbedding)
  have hrange : range (fun c => ι ((e c : D.circleBaseOpen) : A.circle.Base)) = Vc := by
    rw [← hV]
    ext y
    constructor
    · rintro ⟨c, rfl⟩
      exact ⟨_, (e c).2, rfl⟩
    · rintro ⟨z, hz, rfl⟩
      exact ⟨e.symm ⟨z, hz⟩, by simp⟩
  have hcb : (fun c => ι ((e c : D.circleBaseOpen) : A.circle.Base)) '' Rw.circle.cbase = Cc := by
    rw [← hC, ← hCb, image_image, image_image]
  have hdomX : (Rw.circle.domain : Set W.Carrier) = ψ '' (q ⁻¹' Vc) := by
    rw [hdom, ← hV, ← stageSet_LND74 hid]
    ext x
    exact A.circle.mem_restrictParent
  have hproj : ∀ x : Rw.circle.domain,
      ι ((e (Rw.circle.proj x) : D.circleBaseOpen) : A.circle.Base) = q (ψ.symm x) := by
    intro x
    obtain ⟨h, hx⟩ := he x
    rw [hx]
    exact hid.proj_eq ⟨x, h⟩
  refine ⟨_, hemb, hrange, hcb, hdomX, hproj, fun c => ?_, ?_⟩
  · ext y
    constructor
    · rintro ⟨x, hx, rfl⟩
      refine ⟨ψ.symm x, ?_, ψ.apply_symm_apply _⟩
      have hx' : Rw.circle.proj x = c := hx
      change q (ψ.symm x) = _
      rw [← hproj x, hx']
    · rintro ⟨p, hp, rfl⟩
      have hp' : q p = ι ((e c : D.circleBaseOpen) : A.circle.Base) := hp
      have hmem : ψ p ∈ (Rw.circle.domain : Set W.Carrier) := by
        rw [hdomX]
        refine ⟨p, ?_, rfl⟩
        change q p ∈ Vc
        rw [hp', ← hrange]
        exact mem_range_self c
      have hx := hproj ⟨ψ p, hmem⟩
      simp only [Equiv.symm_apply_apply] at hx
      refine ⟨⟨ψ p, hmem⟩, ?_, rfl⟩
      exact hemb.injective (hx.trans hp')
  · rw [hregion, hreg, ← hC, ← stageSet_LND74 hid]
    rfl

end Circle

/-! ## The slim table -/

section Slim

variable {ψ : X ≃ W.Carrier} {n : ℕ} {E : BoundaryTori W n} {A : SmoothStageGeometry74 W E}
  {D : StageCutChoice74 A} {Rw : FC39RowsV2 W E} {q : X → Bs} {ι : A.slim.Base → Bs}

omit [TopologicalSpace X] in
/-- **The slim table from the abstract link**: the pieces are the whole `f₃`-preimages of the
components of `D₃` (`ι` carries the components of `D.D₃` to those of the chain's `D₃`). -/
theorem slimLink_of_stage_LND74 (L : ZeroSlimLink74 A D Rw)
    (hid : StageIdent_LND74 ψ A.slim.toStageProj74 q ι) {D₃c : Set Bs}
    (hD : ι '' D.D₃ = D₃c) (compEquiv : ActualComponent D.D₃ ≃ ActualComponent D₃c)
    (hcomp : ∀ c, ι '' c.1 = (compEquiv c).1) :
    SlimLink_LND74 ψ Rw.slim (fun c : ActualComponent D₃c => q ⁻¹' c.1) (q ⁻¹' D₃c) := by
  obtain ⟨-, -, hun, e, he⟩ := L
  refine ⟨?_, e.trans compEquiv, fun j => ?_⟩
  · rw [hun, ← hD, ← stageSet_LND74 hid]
    rfl
  · change range (Rw.slim.piece j).map = ψ '' (q ⁻¹' (compEquiv (e j)).1)
    rw [he j, ← hcomp, ← stageSet_LND74 hid]

end Slim

/-! ## The regions table -/

section Regions

variable {EN HN EN' HN' : Type*} [NormedAddCommGroup EN] [NormedSpace ℝ EN] [TopologicalSpace HN]
  [NormedAddCommGroup EN'] [NormedSpace ℝ EN'] [TopologicalSpace HN']
  {I : ModelWithCorners ℝ EN HN} {I' : ModelWithCorners ℝ EN' HN'} {N : Type*}
  [TopologicalSpace N] [ChartedSpace HN N] {W' : CompactCarrier.{u}}

/-- **The regions table from the abstract link** (closed route: no cusp cores): `M₁` is the
complement of the interior of the union of the actual zero domains, `M₂ = M₁ ∖ int_{M₁} slimSet`,
`M₃ = M₂ ∖ int_{M₂} edgeSet` (relative interiors, §5.7), all carried by the diffeomorphism. -/
theorem regionsLink_of_stage_LND74 {ι : Type*} (ψ : N ≃ₘ⟮I, W'.model⟯ W'.Carrier)
    {A : SmoothStageGeometry74 W' (BoundaryTori.empty W')} {D : StageCutChoice74 A}
    {Rw : FC39RowsV2 W' (BoundaryTori.empty W')} (L : RegionsLink74 A D Rw)
    {dom : ι → Set N}
    (hz : ∃ σ : Fin A.zero.count ≃ ι, ∀ i, range (A.zero.piece i).map = ψ '' dom (σ i))
    {slimSetc edgeSetc M₁c M₂c M₃c : Set N} (hS : D.slimSet = ψ '' slimSetc)
    (hE : D.edgeSet = ψ '' edgeSetc) (hM₁ : M₁c = (interior (⋃ k, dom k))ᶜ)
    (hM₂ : M₂c = M₁c \ relInt M₁c slimSetc) (hM₃ : M₃c = M₂c \ relInt M₂c edgeSetc) :
    RegionsLink_LND74 ψ.toEquiv Rw M₁c M₂c M₃c := by
  obtain ⟨σ, hσ⟩ := hz
  have h1 : regionM1 A.zero A.cusp = ψ '' M₁c := by
    unfold regionM1
    simp only [iUnion_of_empty, union_empty]
    simp only [hσ]
    rw [σ.surjective.iUnion_comp (fun k => ψ '' dom k), ← image_iUnion, hM₁, ← image_interior_R74 ψ,
      show (ψ '' (interior (⋃ k, dom k))ᶜ) = (ψ '' interior (⋃ k, dom k))ᶜ from
        ψ.toEquiv.image_compl _]
  have h2 : D.M₂ = ψ '' M₂c := by
    change regionM1 A.zero A.cusp \ relInt (regionM1 A.zero A.cusp) D.slimSet = _
    rw [h1, hS, hM₂, relInt_image_R74 ψ, ← image_sdiff (f := (ψ : N → W'.Carrier)) ψ.injective]
  have h3 : D.M₃ = ψ '' M₃c := by
    change D.M₂ \ relInt D.M₂ D.edgeSet = _
    rw [h2, hE, hM₃, relInt_image_R74 ψ, ← image_sdiff (f := (ψ : N → W'.Carrier)) ψ.injective]
  exact ⟨L.regionM1_eq.trans h1, L.regionM2_eq.trans h2, L.regionM3_eq.trans h3⟩

end Regions

/-! ## The cut sets on `W` -/

section CutSets

variable {ψ : X ≃ W.Carrier} {n : ℕ} {E : BoundaryTori W n} {A : SmoothStageGeometry74 W E}
  {D : StageCutChoice74 A} {Bs' : Type w} [TopologicalSpace Bs']

omit [TopologicalSpace X] in
/-- `slimSet = f₃⁻¹(D₃)` on `W` is the `ψ`-image of the chain's `f₃⁻¹(D₃)`. -/
theorem slimSetW_of_stage_LND74 {q : X → Bs'} {ι : A.slim.Base → Bs'}
    (hid : StageIdent_LND74 ψ A.slim.toStageProj74 q ι) {D₃c : Set Bs'} (hD : ι '' D.D₃ = D₃c) :
    D.slimSet = ψ '' (q ⁻¹' D₃c) := by
  rw [← hD, ← stageSet_LND74 hid]
  rfl

omit [TopologicalSpace X] in
/-- `M^edge = q₁⁻¹(C₂) ∩ {T ≤ level}` on `W` is the `ψ`-image of the chain's level set. -/
theorem edgeSetW_of_stage_LND74 {q : X → Bs'} {ι : A.edge.Base → Bs'} {Hs : X → ℝ} {lvl : ℝ}
    {Cc : Set Bs'} (hid : StageIdent_LND74 ψ A.edge.toStageProj74 q ι)
    (hH : ∀ x : A.edge.parent, A.edge.height x = Hs (ψ.symm x)) (hlvl : A.edge.level = lvl)
    (hC : ι '' D.C₂ = Cc) : D.edgeSet = ψ '' (q ⁻¹' Cc ∩ {p | Hs p ≤ lvl}) := by
  ext x
  constructor
  · rintro ⟨hx, hc, hh⟩
    refine ⟨ψ.symm x, ⟨?_, ?_⟩, ψ.apply_symm_apply x⟩
    · rw [mem_preimage, ← hid.proj_eq ⟨x, hx⟩, ← hC]
      exact ⟨_, hc, rfl⟩
    · change Hs (ψ.symm x) ≤ lvl
      rw [← hH ⟨x, hx⟩, ← hlvl]
      exact hh
  · rintro ⟨p, ⟨hq, hh⟩, rfl⟩
    rw [← hC] at hq
    obtain ⟨y, hy, hyp⟩ := hq
    have hpar : ψ p ∈ A.edge.parent := hid.parent_pre p ⟨y, hyp⟩
    refine ⟨hpar, ?_, ?_⟩
    · have h1 := hid.proj_eq ⟨ψ p, hpar⟩
      rw [ψ.symm_apply_apply] at h1
      have h2 : A.edge.proj ⟨ψ p, hpar⟩ = y := hid.emb.injective (h1.trans hyp.symm)
      rw [h2]
      exact hy
    · have h3 := hH ⟨ψ p, hpar⟩
      rw [ψ.symm_apply_apply] at h3
      change A.edge.height ⟨ψ p, hpar⟩ ≤ A.edge.level
      rw [h3, hlvl]
      exact hh

end CutSets

end GC.GraphManifold.Assembly.FC39P0
