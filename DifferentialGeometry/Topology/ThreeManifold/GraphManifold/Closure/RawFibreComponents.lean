import
  DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.FibreBaseWithBoundaryExcision
import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.FibreRestriction
import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Piece
import DifferentialGeometry.Topology.Manifold.ConnectedInterior

/-!
A chosen saturated regular tube and its actual excision retain the old component indices.
Embedding lifts give the punctured selected fibration; retained patches give all other fibres.
-/

set_option autoImplicit false

noncomputable section

open Set Function Manifold Filter
open DifferentialGeometry DifferentialGeometry.Topology GC.Endpoint GC.Seifert
open scoped Manifold ContDiff Topology

universe u

namespace GC.GraphManifold.RawGraphPresentation

variable {W : CompactCarrier.{u}} (G : RawGraphPresentation W)
variable (i : Fin G.components.count)
variable (β : PartialDiffeomorph 𝓘(ℝ, ℂ) (SurfaceModel.model (G.fibration i).base.kind)
  PlaneLift.{u} (G.fibration i).base.Carrier ∞)
variable (hβ : {z : PlaneLift.{u} | ‖z.down‖ ≤ 3} ⊆ β.source)
variable (φ : PartialDiffeomorph (𝓘(ℝ, ℂ).prod (𝓡 1)) G.cutCarrier.model
  (PlaneLift.{u} × Circle) G.cutCarrier.Carrier ∞)
variable (hsource : φ.source = β.source ×ˢ univ)
variable (hUi : φ.target ⊆ (G.components.piece i ⊓ G.cutCarrier.interior :
  TopologicalSpace.Opens G.cutCarrier.Carrier))
variable (hopen : φ '' {p : PlaneLift.{u} × Circle | ‖p.1.down‖ < 1} =
  Subtype.val '' {x : G.components.piece i |
    (G.fibration i).projection x ∈ β '' {z : PlaneLift.{u} | ‖z.down‖ < 1}})
variable (K : CompactCarrier.{u}) (ι : K.Carrier → G.cutCarrier.Carrier)
variable (hι : IsSmoothEmbedding K.model G.cutCarrier.model ∞ ι)
variable (hrange : range ι = (φ '' {p : PlaneLift.{u} × Circle | ‖p.1.down‖ < 1})ᶜ)
variable (O : PartialDiffeomorph G.cutCarrier.model K.model
  G.cutCarrier.Carrier K.Carrier ∞)
variable (hOs : O.source = (φ '' {p : PlaneLift.{u} × Circle | ‖p.1.down‖ ≤ 1})ᶜ)
variable (hO : ∀ x ∈ O.source, ι (O x) = x)

def rawFibrePreimagePiece (j : Fin G.components.count) : TopologicalSpace.Opens K.Carrier :=
  TopologicalSpace.Opens.comap ⟨ι, hι.contMDiff.continuous⟩ (G.components.piece j)

theorem rawFibrePreimagePiece_mem (j : Fin G.components.count) (x : K.Carrier) :
    x ∈ G.rawFibrePreimagePiece K ι hι j ↔ ι x ∈ G.components.piece j := Iff.rfl

include hβ hsource hUi hOs in
private theorem unselected_retained (j : Fin G.components.count) (hji : j ≠ i)
    (x : G.components.piece j) : x.val ∈ O.source := by
  rw [hOs]
  rintro ⟨p, hp, he⟩
  have hps : p ∈ φ.source := by
    rw [hsource]
    refine ⟨hβ ?_, mem_univ p.2⟩
    change ‖p.1.down‖ ≤ 3
    change ‖p.1.down‖ ≤ 1 at hp
    linarith
  have hpi : φ p ∈ G.components.piece i := (hUi (φ.map_source hps)).1
  have hxi : x.val ∈ G.components.piece i := he ▸ hpi
  exact (Set.disjoint_left.mp (G.components.disjoint hji)) x.property hxi

def rawFibreUnselectedDiffeomorph (j : Fin G.components.count) (hji : j ≠ i) :
    G.rawFibrePreimagePiece K ι hι j ≃ₘ⟮K.model, G.cutCarrier.model⟯
      G.components.piece j where
  toFun x := ⟨ι x.val, x.property⟩
  invFun y := ⟨O y.val, by
    change ι (O y.val) ∈ G.components.piece j
    rw [hO _ (G.unselected_retained i β hβ φ hsource hUi K O hOs j hji y)]
    exact y.property⟩
  left_inv x := by
    apply Subtype.ext
    apply hι.isEmbedding.injective
    exact hO _ (G.unselected_retained i β hβ φ hsource hUi K O hOs j hji
      ⟨ι x.val, x.property⟩)
  right_inv y := Subtype.ext
    (hO _ (G.unselected_retained i β hβ φ hsource hUi K O hOs j hji y))
  contMDiff_toFun := (ContMDiff.subtypeVal_comp_iff _ _).mp
    (hι.contMDiff.comp contMDiff_subtype_val)
  contMDiff_invFun := by
    apply (ContMDiff.subtypeVal_comp_iff _ _).mp
    intro y
    exact (O.contMDiffOn.contMDiffAt (O.open_source.mem_nhds
      (G.unselected_retained i β hβ φ hsource hUi K O hOs j hji y))).comp y
        contMDiff_subtype_val.contMDiffAt

theorem rawFibreUnselectedDiffeomorph_apply (j : Fin G.components.count) (hji : j ≠ i)
    (x : G.rawFibrePreimagePiece K ι hι j) :
    G.rawFibreUnselectedDiffeomorph (i := i) (β := β) (hβ := hβ) (φ := φ)
      (hsource := hsource) (hUi := hUi) K ι hι O hOs hO j hji x =
      ι x.val := rfl

section Selected

variable (B : CompactSurface.{u}) (b : C(B.Carrier, (G.fibration i).base.Carrier))
variable (hb : IsSmoothEmbedding (SurfaceModel.model B.kind)
  (SurfaceModel.model (G.fibration i).base.kind) ∞ b)
variable (hbij : ∀ y, Bijective (mfderiv (SurfaceModel.model B.kind)
  (SurfaceModel.model (G.fibration i).base.kind) b y))
variable (hbrange : range b = (β '' {z : PlaneLift.{u} | ‖z.down‖ < 1})ᶜ)

include hopen hrange hbrange in
private theorem selected_projection_range (x : G.rawFibrePreimagePiece K ι hι i) :
    (G.fibration i).projection ⟨ι x.val, x.property⟩ ∈ range b := by
  rw [hbrange]
  intro hx
  have hi : ι x.val ∈ range ι := mem_range_self x.val
  rw [hrange] at hi
  apply hi
  rw [hopen]
  exact ⟨⟨ι x.val, x.property⟩, hx, rfl⟩

include hopen hrange hbrange in
private theorem selected_restriction_range
    (y : ((G.fibration i).fibreRestrictionCarrier B b hb.isEmbedding.injective
      hb.contMDiff hbij).Carrier) :
    (G.fibration i).fibreRestrictionInclusion B b hb.isEmbedding.injective
      hb.contMDiff hbij y ∈ range ι := by
  rw [hrange]
  intro hy
  rw [hopen] at hy
  obtain ⟨z, hz, he⟩ := hy
  have hzx : z = y.val := Subtype.ext he
  rw [hzx] at hz
  have hp := y.property
  change (G.fibration i).projection y.val ∈ range b at hp
  rw [hbrange] at hp
  exact hp hz

def rawFibreSelectedComparison :
    G.rawFibrePreimagePiece K ι hι i ≃ₘ⟮K.model,
      ((G.fibration i).fibreRestrictionCarrier B b hb.isEmbedding.injective
        hb.contMDiff hbij).model⟯
      ((G.fibration i).fibreRestrictionCarrier B b hb.isEmbedding.injective
        hb.contMDiff hbij).Carrier := by
  let F := G.fibration i
  let R := F.fibreRestrictionCarrier B b hb.isEmbedding.injective hb.contMDiff hbij
  let r := F.fibreRestrictionInclusion B b hb.isEmbedding.injective hb.contMDiff hbij
  let U := G.rawFibrePreimagePiece K ι hι i
  have hr : range r ⊆ range ι := by
    rintro z ⟨y, rfl⟩
    exact G.selected_restriction_range i β φ hopen K ι hrange B b hb hbij hbrange y
  let g := hι.lift r hr
  have hg := hι.contMDiff_lift
    (F.fibreRestrictionInclusion_smooth B b hb.isEmbedding.injective hb.contMDiff hbij) hr
  let f : U → G.cutCarrier.Carrier := ι ∘ Subtype.val
  have hf : ContMDiff K.model G.cutCarrier.model ∞ f :=
    hι.contMDiff.comp contMDiff_subtype_val
  have hu (x : U) : f x ∈ G.components.piece i := x.property
  have hp (x : U) : F.projection ⟨f x, hu x⟩ ∈ range b :=
    G.selected_projection_range i β φ hopen K ι hι hrange B b hbrange x
  let e := F.fibreRestrictionLift B b hb.isEmbedding.injective hb.contMDiff hbij f hu hp
  have he := F.fibreRestrictionLift_smooth B b hb.isEmbedding.injective hb.contMDiff hbij
    hb f hf hu hp
  have hgU (y : R.Carrier) : g y ∈ U := by
    change ι (g y) ∈ G.components.piece i
    rw [hι.comp_lift hr y]
    exact y.val.property
  refine
    { toFun := e
      invFun := fun y => ⟨g y, hgU y⟩
      left_inv := ?_
      right_inv := ?_
      contMDiff_toFun := he
      contMDiff_invFun := (ContMDiff.subtypeVal_comp_iff _ _).mp hg }
  · intro x
    apply Subtype.ext
    apply hι.isEmbedding.injective
    exact hι.comp_lift hr (e x)
  · intro y
    apply Subtype.ext
    apply Subtype.ext
    exact hι.comp_lift hr y

theorem rawFibreSelectedComparison_apply (x : G.rawFibrePreimagePiece K ι hι i) :
    (G.rawFibreSelectedComparison (i := i) (β := β) (φ := φ) (hopen := hopen)
      K ι hι hrange B b hb hbij hbrange x).val.val =
      ι x.val := rfl

end Selected

include hβ hopen hrange in
private theorem selected_fibration :
    Nonempty (CircleFibration K (G.rawFibrePreimagePiece K ι hι i)) ∧
      ConnectedSpace (G.rawFibrePreimagePiece K ι hι i) := by
  obtain ⟨B, b, γ, hBk, hbsm, hb, hbinj, hbij, hbrange, hγs, hγ, hbd, hdisj⟩ :=
    (G.fibration i).base.exists_puncture_of_interiorChart_with_embedding β hβ
  let F := G.fibration i
  let R := F.fibreRestrictionCarrier B b hb.isEmbedding.injective hb.contMDiff hbij
  let e := G.rawFibreSelectedComparison (i := i) (β := β) (φ := φ) (hopen := hopen)
    K ι hι hrange B b hb hbij hbrange
  let et := e.trans (topOpensDiffeomorph (I := R.model) R.Carrier).symm
  let H := (F.fibreRestriction B b hb.isEmbedding.injective hb.contMDiff hbij).ofDiffeomorph et
  exact ⟨⟨H⟩, e.symm.surjective.connectedSpace e.symm.continuous⟩

private theorem rawFibreInteriorConnected (U : TopologicalSpace.Opens K.Carrier)
    (hc : ConnectedSpace U) : ConnectedSpace (K.pieceInterior U) := by
  let := hc
  have he : (K.pieceInterior U : Set K.Carrier) = K.model.interior K.Carrier ∩ U := by
    ext x
    exact and_comm
  apply isConnected_iff_connectedSpace.mp
  rw [he]
  have hp : IsPreconnected (U : Set K.Carrier) :=
    isPreconnected_iff_preconnectedSpace.mpr inferInstance
  have hd := DifferentialGeometry.Topology.Manifold.dense_manifold_interior
    (I := K.model) (M := U)
  obtain ⟨x, hx⟩ := hd.nonempty
  refine ⟨⟨x.val, ?_, x.property⟩,
    DifferentialGeometry.Topology.Manifold.isPreconnected_manifold_interior_inter_open U hp⟩
  exact K.model.isInteriorPoint_iff_isInteriorPoint_val.mp hx

include hβ hsource hUi hopen hι hrange hOs hO in
theorem exists_rawFibreComponents :
    ∃ D : K.Components, Nonempty (∀ j, CircleFibration K (D.piece j)) ∧
      ∃ hc : D.count = G.components.count,
        ∀ (j : Fin G.components.count) (x : K.Carrier),
          x ∈ D.piece (Fin.cast hc.symm j) ↔ ι x ∈ G.components.piece j := by
  obtain ⟨⟨Hselected⟩, hselected⟩ := G.selected_fibration i β hβ φ hopen K ι hι hrange
  have hc (j : Fin G.components.count) :
      ConnectedSpace (G.rawFibrePreimagePiece K ι hι j) := by
    by_cases hji : j = i
    · subst j
      exact hselected
    · let e := G.rawFibreUnselectedDiffeomorph (i := i) (β := β) (hβ := hβ) (φ := φ)
        (hsource := hsource) (hUi := hUi) K ι hι O hOs hO j hji
      have := G.components.connected j
      exact e.symm.surjective.connectedSpace e.symm.continuous
  let D : K.Components :=
    { count := G.components.count
      count_pos := G.components.count_pos
      piece := G.rawFibrePreimagePiece K ι hι
      closed := fun j => (G.components.closed j).preimage hι.contMDiff.continuous
      connected := hc
      disjoint := by
        intro j k hjk
        apply Set.disjoint_left.mpr
        intro x hxj hxk
        exact Set.disjoint_left.mp (G.components.disjoint hjk) hxj hxk
      covers := by
        ext x
        constructor
        · intro hx
          exact mem_univ x
        · intro hx
          have hi : ι x ∈ ⋃ j, (G.components.piece j : Set G.cutCarrier.Carrier) := by
            rw [G.components.covers]
            exact mem_univ _
          obtain ⟨j, hj⟩ := mem_iUnion.mp hi
          exact mem_iUnion.mpr ⟨j, hj⟩
      interior_connected := fun j => rawFibreInteriorConnected K
        (G.rawFibrePreimagePiece K ι hι j) (hc j) }
  have hF (j : Fin G.components.count) : CircleFibration K (D.piece j) := by
    by_cases hji : j = i
    · subst j
      exact Hselected
    · exact (G.fibration j).ofDiffeomorph
        (G.rawFibreUnselectedDiffeomorph (i := i) (β := β) (hβ := hβ) (φ := φ)
          (hsource := hsource) (hUi := hUi) K ι hι O hOs hO j hji)
  exact ⟨D, ⟨hF⟩, rfl, fun j x => Iff.rfl⟩

end GC.GraphManifold.RawGraphPresentation
