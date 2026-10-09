import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Presentation
import DifferentialGeometry.Topology.ThreeManifold.TorusCut.Decomposition
import DifferentialGeometry.Topology.Manifold.OpenSubtypeDiffeomorph
import Mathlib.Analysis.SpecialFunctions.Complex.Circle

set_option autoImplicit false

/-!
# Pieces of a raw graph presentation

Every piece of a raw graph presentation `G` of a compact carrier is itself a raw graph
presentation with one component, no torus pairing, and external boundary tori.

The circle fibration of the piece is transported to the component carrier along the
diffeomorphism from the top open set. The boundary sides of the cut carrier (the left and right
half-collars of each pairing and the cut external collars) are collected in `G.Side`; each collar
target is contained in the piece owning its side, because a half-collar source is connected and
pieces are clopen. Collar targets of distinct sides are disjoint: for different seams or external
tori this follows from the disjointness of their images in the reconstructed carrier, and for the
two sides of one seam from the injectivity of the seam. Restricting the collars owned by a piece
gives its boundary tori, which exhaust the boundary of the component carrier.
-/

noncomputable section
open DifferentialGeometry DifferentialGeometry.Topology GC.Endpoint GC.Topology
open scoped Manifold ContDiff Topology
namespace GC.GraphManifold
universe u

section OpenRestriction

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {E' : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E']
  {H' : Type*} [TopologicalSpace H'] {J : ModelWithCorners ℝ E' H'}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  {N : Type*} [TopologicalSpace N] [ChartedSpace H' N]

def opensComapDiffeomorph (e : M ≃ₘ⟮I, J⟯ N) (V : TopologicalSpace.Opens N) :
    TopologicalSpace.Opens.comap ⟨e, e.continuous⟩ V ≃ₘ⟮I, J⟯ V where
  toFun x := ⟨e x.val, x.property⟩
  invFun y := ⟨e.symm y.val, by
    change e (e.symm y.val) ∈ V
    rw [e.apply_symm_apply]
    exact y.property⟩
  left_inv x := Subtype.ext (e.symm_apply_apply x.val)
  right_inv y := Subtype.ext (e.apply_symm_apply y.val)
  contMDiff_toFun := (ContMDiff.subtypeVal_comp_iff _ _).mp
    (e.contMDiff.comp contMDiff_subtype_val)
  contMDiff_invFun := (ContMDiff.subtypeVal_comp_iff _ _).mp
    (e.symm.contMDiff.comp contMDiff_subtype_val)

@[simp]
theorem opensComapDiffeomorph_apply (e : M ≃ₘ⟮I, J⟯ N) (V : TopologicalSpace.Opens N)
    (x : TopologicalSpace.Opens.comap ⟨e, e.continuous⟩ V) :
    (opensComapDiffeomorph e V x : N) = e x.val := rfl

def topOpensDiffeomorph (M : Type*) [TopologicalSpace M] [ChartedSpace H M] :
    (⊤ : TopologicalSpace.Opens M) ≃ₘ⟮I, I⟯ M where
  toFun := Subtype.val
  invFun x := ⟨x, trivial⟩
  left_inv _ := rfl
  right_inv _ := rfl
  contMDiff_toFun := contMDiff_subtype_val
  contMDiff_invFun := (ContMDiff.subtypeVal_comp_iff _ _).mp contMDiff_id

@[simp]
theorem topOpensDiffeomorph_apply (x : (⊤ : TopologicalSpace.Opens M)) :
    topOpensDiffeomorph (I := I) M x = x.val := rfl

def codRestrictOpens (φ : PartialDiffeomorph I J M N ∞) (U : TopologicalSpace.Opens N)
    (hU : Nonempty U) : PartialDiffeomorph I J M U ∞ :=
  φ.trans (DifferentialGeometry.Manifold.openSubtypePartialDiffeomorph J U hU).symm

theorem codRestrictOpens_source (φ : PartialDiffeomorph I J M N ∞)
    (U : TopologicalSpace.Opens N) (hU : Nonempty U) (h : φ.target ⊆ U) :
    (codRestrictOpens φ U hU).source = φ.source := by
  change φ.source ∩ φ ⁻¹' (DifferentialGeometry.Manifold.openSubtypePartialDiffeomorph J U
    hU).target = φ.source
  rw [DifferentialGeometry.Manifold.openSubtypePartialDiffeomorph_target]
  exact Set.inter_eq_left.mpr fun x hx => h (φ.map_source' hx)

theorem codRestrictOpens_target (φ : PartialDiffeomorph I J M N ∞)
    (U : TopologicalSpace.Opens N) (hU : Nonempty U) :
    (codRestrictOpens φ U hU).target = Subtype.val ⁻¹' φ.target := by
  change Set.univ ∩ Subtype.val ⁻¹' φ.target = _
  exact Set.univ_inter _

theorem codRestrictOpens_apply (φ : PartialDiffeomorph I J M N ∞)
    (U : TopologicalSpace.Opens N) (hU : Nonempty U) {x : M} (hx : φ x ∈ U) :
    (codRestrictOpens φ U hU x : N) = φ x := by
  change ((DifferentialGeometry.Manifold.openSubtypePartialDiffeomorph J U hU).symm (φ x) : N)
    = φ x
  rw [DifferentialGeometry.Manifold.openSubtypePartialDiffeomorph_symm_apply J U hU hx]

end OpenRestriction

def CircleFibration.ofDiffeomorph {C C' : CompactCarrier.{u}}
    {U : TopologicalSpace.Opens C.Carrier} {V : TopologicalSpace.Opens C'.Carrier}
    (F : CircleFibration C U) (e : V ≃ₘ⟮C'.model, C.model⟯ U) : CircleFibration C' V where
  base := F.base
  projection := F.projection.comp ⟨e, e.continuous⟩
  surjective := F.surjective.comp e.surjective
  smooth := F.smooth.comp e.contMDiff
  neighborhood := F.neighborhood
  mem_neighborhood := F.mem_neighborhood
  trivialization b := (opensComapDiffeomorph e
    (TopologicalSpace.Opens.comap F.projection (F.neighborhood b))).trans (F.trivialization b)
  projection_trivialization b _ := F.projection_trivialization b _

def CircleFibration.toComponent {C : CompactCarrier.{u}} (D : C.Components) (i : Fin D.count)
    (F : CircleFibration C (D.piece i)) : CircleFibration (componentCarrier C D i) ⊤ :=
  F.ofDiffeomorph (topOpensDiffeomorph (I := C.model) (D.piece i))

theorem halfPoint_eq_self (h : EuclideanHalfSpace 1) {s : ℝ} (hs : 0 ≤ s) (e : s = h.val 0) :
    halfPoint s hs = h := by
  subst e
  refine Subtype.ext (PiLp.ext fun j => ?_)
  rw [Subsingleton.elim j 0]
  rfl

theorem isPreconnected_halfCollarSource : IsPreconnected halfCollarSource := by
  let f : ℝ → EuclideanHalfSpace 1 := fun s => halfPoint (max s 0) (le_max_right s 0)
  have hf : Continuous f := Continuous.subtype_mk
    ((PiLp.continuous_toLp 2 _).comp
      (continuous_pi fun _ => continuous_id.max continuous_const)) _
  have himg : f '' Set.Ico 0 1 = {h : EuclideanHalfSpace 1 | h.val 0 < 1} := by
    ext h
    constructor
    · rintro ⟨s, hs, rfl⟩
      change max s 0 < 1
      exact max_lt hs.2 one_pos
    · intro hh
      refine ⟨h.val 0, ⟨h.property, hh⟩, halfPoint_eq_self h _ (max_eq_left h.property)⟩
  have hS : IsPreconnected {h : EuclideanHalfSpace 1 | h.val 0 < 1} :=
    himg ▸ isPreconnected_Ico.image f hf.continuousOn
  have : halfCollarSource =
      (Set.univ : Set Torus) ×ˢ {h : EuclideanHalfSpace 1 | h.val 0 < 1} := by
    ext p
    simp [halfCollarSource]
  rw [this]
  exact isPreconnected_univ.prod hS

theorem target_subset_piece_of_source_eq {C : CompactCarrier.{u}} (D : C.Components)
    (φ : PartialDiffeomorph halfCollarModel C.model (Torus × EuclideanHalfSpace 1) C.Carrier ∞)
    (hφ : φ.source = halfCollarSource) {i : Fin D.count} {p : Torus × EuclideanHalfSpace 1}
    (hp : p ∈ φ.source) (hpi : φ p ∈ D.piece i) : φ.target ⊆ D.piece i := by
  rw [← φ.toPartialEquiv.image_source_eq_target]
  have hc : IsPreconnected (φ '' φ.source) := by
    refine IsPreconnected.image ?_ _ φ.contMDiffOn.continuousOn
    rw [hφ]
    exact isPreconnected_halfCollarSource
  exact hc.subset_isClopen ⟨D.closed i, (D.piece i).isOpen⟩ ⟨φ p, ⟨p, hp, rfl⟩, hpi⟩

theorem exists_eq_of_mem_target_of_source_eq {C : CompactCarrier.{u}}
    (φ : PartialDiffeomorph halfCollarModel C.model (Torus × EuclideanHalfSpace 1) C.Carrier ∞)
    (hφ : φ.source = halfCollarSource) {x : C.Carrier} (hx : x ∈ φ.target) :
    ∃ p ∈ halfCollarSource, φ p = x :=
  ⟨φ.symm x, hφ ▸ φ.map_target' hx, φ.right_inv' hx⟩

theorem zero_mem_halfCollarSource (t : Torus) : (t, halfZero) ∈ halfCollarSource := by
  change (0 : ℝ) < 1
  norm_num

namespace RawGraphPresentation
variable {W : CompactCarrier.{u}}

abbrev Side (G : RawGraphPresentation W) :=
  Fin G.pairing.count ⊕ Fin G.pairing.count ⊕ Fin G.externalCount

def sidePiece (G : RawGraphPresentation W) : G.Side → Fin G.components.count
  | .inl k => G.leftPiece k
  | .inr (.inl k) => G.rightPiece k
  | .inr (.inr k) => G.externalPiece k

def sideCollar (G : RawGraphPresentation W) : G.Side →
    PartialDiffeomorph halfCollarModel G.cutCarrier.model (Torus × EuclideanHalfSpace 1)
      G.cutCarrier.Carrier ∞
  | .inl k => G.pairing.leftCollar k
  | .inr (.inl k) => G.pairing.rightCollar k
  | .inr (.inr k) => G.cutExternal.collar k

theorem sideCollar_source (G : RawGraphPresentation W) :
    ∀ s, (G.sideCollar s).source = halfCollarSource
  | .inl k => G.pairing.left_source k
  | .inr (.inl k) => G.pairing.right_source k
  | .inr (.inr k) => G.cutExternal.source_eq k

theorem zero_mem_sideCollar_source (G : RawGraphPresentation W) (s : G.Side) (t : Torus) :
    (t, halfZero) ∈ (G.sideCollar s).source := by
  rw [G.sideCollar_source]
  exact zero_mem_halfCollarSource t

private theorem mem_boundary_of_mem_block (G : RawGraphPresentation W)
    {k : Fin G.pairing.count} {x : G.cutCarrier.Carrier} (hx : x ∈ G.pairing.gluing.block k) :
    x ∈ G.cutCarrier.model.boundary G.cutCarrier.Carrier := by
  rw [G.cut_boundary_exhausted]
  exact Or.inl (Set.mem_iUnion.mpr ⟨k, hx⟩)

theorem sideCollar_zero_mem (G : RawGraphPresentation W) :
    ∀ (s : G.Side) (t : Torus),
      G.sideCollar s (t, halfZero) ∈ G.cutCarrier.model.boundary G.cutCarrier.Carrier ∧
        G.sideCollar s (t, halfZero) ∈ G.components.piece (G.sidePiece s)
  | .inl k, t => by
    change G.pairing.leftCollar k (t, halfZero) ∈ _ ∧ G.pairing.leftCollar k (t, halfZero) ∈ _
    rw [G.pairing.left_zero k t]
    exact ⟨G.mem_boundary_of_mem_block (Or.inl (G.pairing.leftParam k t).property),
      G.left_owned k (G.pairing.leftParam k t).property⟩
  | .inr (.inl k), t => by
    change G.pairing.rightCollar k (t, halfZero) ∈ _ ∧
      G.pairing.rightCollar k (t, halfZero) ∈ _
    rw [G.pairing.right_zero k t]
    exact ⟨G.mem_boundary_of_mem_block (Or.inr (G.pairing.rightParam k t).property),
      G.right_owned k (G.pairing.rightParam k t).property⟩
  | .inr (.inr k), t => ⟨G.cutExternal.boundary_zero k t, G.external_owned k ⟨t, rfl⟩⟩

theorem sideCollar_target_subset (G : RawGraphPresentation W) (s : G.Side) :
    (G.sideCollar s).target ⊆ G.components.piece (G.sidePiece s) :=
  target_subset_piece_of_source_eq _ _ (G.sideCollar_source s)
    (G.zero_mem_sideCollar_source s 1) (G.sideCollar_zero_mem s 1).2

def cutMap (G : RawGraphPresentation W) : G.cutCarrier.Carrier → W.Carrier :=
  fun x => G.reconstruction (G.pairing.quotientMap x)

theorem cutMap_leftCollar (G : RawGraphPresentation W) (k : Fin G.pairing.count)
    {p : Torus × EuclideanHalfSpace 1} (hp : p ∈ halfCollarSource) :
    G.cutMap (G.pairing.leftCollar k p) = G.seam k (p.1, -(p.2.val 0)) := by
  rw [G.seam_negative k p.1 _ (neg_nonpos.mpr p.2.property) (neg_lt_neg hp),
    halfPoint_eq_self p.2 _ (neg_neg _)]
  rfl

theorem cutMap_rightCollar (G : RawGraphPresentation W) (k : Fin G.pairing.count)
    {p : Torus × EuclideanHalfSpace 1} (hp : p ∈ halfCollarSource) :
    G.cutMap (G.pairing.rightCollar k p) =
      G.seam k ((G.pairing.matching k).symm p.1, p.2.val 0) := by
  rw [G.seam_positive k _ _ p.2.property hp, Diffeomorph.apply_symm_apply,
    halfPoint_eq_self p.2 _ rfl]
  rfl

private theorem neg_mem_signedCollarSource {a : ℝ} (t : Torus) (h0 : 0 ≤ a) (h1 : a < 1) :
    (t, -a) ∈ signedCollarSource :=
  ⟨neg_lt_neg h1, lt_of_le_of_lt (neg_nonpos.mpr h0) one_pos⟩

private theorem mem_signedCollarSource {a : ℝ} (t : Torus) (h0 : 0 ≤ a) (h1 : a < 1) :
    (t, a) ∈ signedCollarSource :=
  ⟨lt_of_lt_of_le (neg_lt_zero.mpr one_pos) h0, h1⟩

def sideIndex (G : RawGraphPresentation W) : G.Side → Fin G.pairing.count ⊕ Fin G.externalCount
  | .inl k => .inl k
  | .inr (.inl k) => .inl k
  | .inr (.inr k) => .inr k

def sideRegion (G : RawGraphPresentation W) :
    Fin G.pairing.count ⊕ Fin G.externalCount → Set W.Carrier
  | .inl k => (G.seam k).target
  | .inr k => (G.external.collar k).target

theorem pairwise_disjoint_sideRegion (G : RawGraphPresentation W) :
    Pairwise (fun a b => Disjoint (G.sideRegion a) (G.sideRegion b))
  | .inl _, .inl _, h => G.seam_disjoint fun e => h (congrArg _ e)
  | .inl k, .inr k', _ => (G.external_seam_disjoint k' k).symm
  | .inr k, .inl k', _ => G.external_seam_disjoint k k'
  | .inr _, .inr _, h => G.external.disjoint fun e => h (congrArg _ e)

theorem cutMap_mem_sideRegion (G : RawGraphPresentation W) :
    ∀ (s : G.Side) {x : G.cutCarrier.Carrier}, x ∈ (G.sideCollar s).target →
      G.cutMap x ∈ G.sideRegion (G.sideIndex s)
  | .inl k, x, hx => by
    obtain ⟨p, hp, rfl⟩ :=
      exists_eq_of_mem_target_of_source_eq _ (G.pairing.left_source k) hx
    change G.cutMap (G.pairing.leftCollar k p) ∈ (G.seam k).target
    rw [G.cutMap_leftCollar k hp]
    exact (G.seam k).map_source' (G.seam_source k ▸ neg_mem_signedCollarSource _ p.2.2 hp)
  | .inr (.inl k), x, hx => by
    obtain ⟨p, hp, rfl⟩ :=
      exists_eq_of_mem_target_of_source_eq _ (G.pairing.right_source k) hx
    change G.cutMap (G.pairing.rightCollar k p) ∈ (G.seam k).target
    rw [G.cutMap_rightCollar k hp]
    exact (G.seam k).map_source' (G.seam_source k ▸ mem_signedCollarSource _ p.2.2 hp)
  | .inr (.inr k), x, hx => by
    obtain ⟨p, hp, rfl⟩ :=
      exists_eq_of_mem_target_of_source_eq _ (G.cutExternal.source_eq k) hx
    change G.cutMap (G.cutExternal.collar k p) ∈ (G.external.collar k).target
    rw [cutMap, G.marked_collar k p hp]
    exact (G.external.collar k).map_source' ((G.external.source_eq k).symm ▸ hp)

theorem disjoint_leftCollar_rightCollar (G : RawGraphPresentation W) (k : Fin G.pairing.count) :
    Disjoint (G.pairing.leftCollar k).target (G.pairing.rightCollar k).target := by
  rw [Set.disjoint_left]
  intro x hl hr
  obtain ⟨⟨t, a⟩, hp, rfl⟩ :=
    exists_eq_of_mem_target_of_source_eq _ (G.pairing.left_source k) hl
  obtain ⟨⟨t', a'⟩, hq, hpq⟩ :=
    exists_eq_of_mem_target_of_source_eq _ (G.pairing.right_source k) hr
  have he : G.seam k (t, -(a.val 0)) = G.seam k ((G.pairing.matching k).symm t', a'.val 0) := by
    rw [← G.cutMap_leftCollar k hp, ← G.cutMap_rightCollar k hq, hpq]
  have h2 := congrArg Prod.snd ((G.seam k).toPartialEquiv.injOn
    (G.seam_source k ▸ neg_mem_signedCollarSource t a.2 hp)
    (G.seam_source k ▸ mem_signedCollarSource _ a'.2 hq) he)
  have h0 : a.val 0 = 0 := by
    have := a.2
    have := a'.2
    simp only at h2
    linarith
  have h0' : a'.val 0 = 0 := by
    simp only at h2
    linarith
  have ha : a = halfZero := (halfPoint_eq_self a le_rfl h0.symm).symm
  have ha' : a' = halfZero := (halfPoint_eq_self a' le_rfl h0'.symm).symm
  subst ha ha'
  rw [G.pairing.left_zero] at hpq
  rw [G.pairing.right_zero] at hpq
  refine (G.pairing.gluing.disjoint_left_right k).le_bot
    ⟨(G.pairing.leftParam k t).property, ?_⟩
  rw [← hpq]
  exact (G.pairing.rightParam k t').property

theorem sideCollar_disjoint (G : RawGraphPresentation W) :
    Pairwise (fun s s' : G.Side => Disjoint (G.sideCollar s).target (G.sideCollar s').target) := by
  intro s s' hss'
  by_cases hidx : G.sideIndex s = G.sideIndex s'
  · rcases s with k | k | k <;> rcases s' with k' | k' | k' <;>
      simp only [sideIndex, Sum.inl.injEq, Sum.inr.injEq, reduceCtorEq] at hidx
    · exact (hss' (congrArg Sum.inl hidx)).elim
    · subst hidx
      exact G.disjoint_leftCollar_rightCollar k
    · subst hidx
      exact (G.disjoint_leftCollar_rightCollar k).symm
    · exact (hss' (by rw [hidx])).elim
    · exact (hss' (by rw [hidx])).elim
  · rw [Set.disjoint_left]
    intro x hx hx'
    exact (G.pairwise_disjoint_sideRegion hidx).le_bot
      ⟨G.cutMap_mem_sideRegion s hx, G.cutMap_mem_sideRegion s' hx'⟩

abbrev OwnedSide (G : RawGraphPresentation W) (i : Fin G.components.count) :=
  {s : G.Side // G.sidePiece s = i}

def pieceCollar (G : RawGraphPresentation W) (i : Fin G.components.count) (s : G.OwnedSide i) :
    PartialDiffeomorph halfCollarModel G.cutCarrier.model (Torus × EuclideanHalfSpace 1)
      (G.components.piece i) ∞ :=
  codRestrictOpens (G.sideCollar s.val) (G.components.piece i) (G.components.connected i).toNonempty

theorem sideCollar_target_subset_of_owned (G : RawGraphPresentation W)
    (i : Fin G.components.count) (s : G.OwnedSide i) :
    (G.sideCollar s.val).target ⊆ G.components.piece i :=
  by simpa only [s.property] using G.sideCollar_target_subset s.val

theorem pieceCollar_source (G : RawGraphPresentation W) (i : Fin G.components.count)
    (s : G.OwnedSide i) : (G.pieceCollar i s).source = halfCollarSource :=
  (codRestrictOpens_source _ _ _ (G.sideCollar_target_subset_of_owned i s)).trans
    (G.sideCollar_source s.val)

theorem pieceCollar_target (G : RawGraphPresentation W) (i : Fin G.components.count)
    (s : G.OwnedSide i) :
    (G.pieceCollar i s).target = Subtype.val ⁻¹' (G.sideCollar s.val).target :=
  codRestrictOpens_target _ _ _

theorem pieceCollar_apply (G : RawGraphPresentation W) (i : Fin G.components.count)
    (s : G.OwnedSide i) {p : Torus × EuclideanHalfSpace 1} (hp : p ∈ halfCollarSource) :
    (G.pieceCollar i s p : G.cutCarrier.Carrier) = G.sideCollar s.val p :=
  codRestrictOpens_apply _ _ _ (G.sideCollar_target_subset_of_owned i s
    ((G.sideCollar s.val).map_source' ((G.sideCollar_source s.val).symm ▸ hp)))

def pieceBoundaryTori (G : RawGraphPresentation W) (i : Fin G.components.count) :
    BoundaryTori (componentCarrier G.cutCarrier G.components i)
      (Fintype.card (G.OwnedSide i)) where
  collar j := G.pieceCollar i ((Fintype.equivFin _).symm j)
  source_eq j := G.pieceCollar_source i _
  boundary_zero j t := by
    refine (ModelWithCorners.isBoundaryPoint_iff_isBoundaryPoint_val (I := G.cutCarrier.model)
      (u := G.components.piece i)).mpr ?_
    have h := (G.sideCollar_zero_mem ((Fintype.equivFin _).symm j).val t).1
    rw [← G.pieceCollar_apply i _ (zero_mem_halfCollarSource t)] at h
    exact h
  disjoint j j' h := by
    change Disjoint (G.pieceCollar i _).target (G.pieceCollar i _).target
    rw [G.pieceCollar_target, G.pieceCollar_target]
    exact (G.sideCollar_disjoint fun e =>
      h ((Fintype.equivFin _).symm.injective (Subtype.ext e))).preimage _

theorem pieceBoundaryTori_torusMap (G : RawGraphPresentation W) (i : Fin G.components.count)
    (j : Fin (Fintype.card (G.OwnedSide i))) (t : Torus) :
    ((G.pieceBoundaryTori i).torusMap j t).val =
      G.sideCollar ((Fintype.equivFin _).symm j).val (t, halfZero) :=
  G.pieceCollar_apply i _ (zero_mem_halfCollarSource t)

theorem exists_sideCollar_zero_eq (G : RawGraphPresentation W) {x : G.cutCarrier.Carrier}
    (hx : x ∈ G.cutCarrier.model.boundary G.cutCarrier.Carrier) :
    ∃ (s : G.Side) (t : Torus), G.sideCollar s (t, halfZero) = x := by
  rw [G.cut_boundary_exhausted] at hx
  rcases hx with hx | hx
  · obtain ⟨k, hk⟩ := Set.mem_iUnion.mp hx
    rcases hk with hl | hr
    · refine ⟨.inl k, (G.pairing.leftParam k).symm ⟨x, hl⟩, ?_⟩
      change G.pairing.leftCollar k _ = x
      rw [G.pairing.left_zero, Homeomorph.apply_symm_apply]
    · refine ⟨.inr (.inl k), (G.pairing.rightParam k).symm ⟨x, hr⟩, ?_⟩
      change G.pairing.rightCollar k _ = x
      rw [G.pairing.right_zero, Homeomorph.apply_symm_apply]
  · obtain ⟨k, t, ht⟩ := Set.mem_iUnion.mp hx
    exact ⟨.inr (.inr k), t, ht⟩

theorem pieceBoundaryTori_image (G : RawGraphPresentation W) (i : Fin G.components.count) :
    (componentCarrier G.cutCarrier G.components i).model.boundary
        (componentCarrier G.cutCarrier G.components i).Carrier =
      (G.pieceBoundaryTori i).image := by
  ext x
  constructor
  · intro hx
    have hx' : x.val ∈ G.cutCarrier.model.boundary G.cutCarrier.Carrier :=
      (ModelWithCorners.isBoundaryPoint_iff_isBoundaryPoint_val (I := G.cutCarrier.model)
        (u := G.components.piece i)).mp hx
    obtain ⟨s, t, hst⟩ := G.exists_sideCollar_zero_eq hx'
    have hsi : G.sidePiece s = i := by
      by_contra hne
      exact (G.components.disjoint hne).le_bot
        ⟨hst ▸ (G.sideCollar_zero_mem s t).2, x.property⟩
    refine Set.mem_iUnion.mpr ⟨Fintype.equivFin _ ⟨s, hsi⟩, t, Subtype.ext ?_⟩
    rw [pieceBoundaryTori_torusMap, Equiv.symm_apply_apply]
    exact hst
  · intro hx
    obtain ⟨j, t, rfl⟩ := Set.mem_iUnion.mp hx
    exact (G.pieceBoundaryTori i).boundary_zero j t
end RawGraphPresentation

def componentPieceInteriorHomeomorph (C : CompactCarrier.{u}) (D : C.Components)
    (i : Fin D.count) :
    (componentCarrier C D i).pieceInterior ⊤ ≃ₜ C.pieceInterior (D.piece i) where
  toFun x := ⟨x.val.val, x.val.property,
    (C.model.isInteriorPoint_iff_isInteriorPoint_val (u := D.piece i)).mp x.property.2⟩
  invFun y := ⟨⟨y.val, y.property.1⟩, trivial,
    (C.model.isInteriorPoint_iff_isInteriorPoint_val (u := D.piece i)).mpr y.property.2⟩
  left_inv _ := rfl
  right_inv _ := rfl
  continuous_toFun := by
    refine Continuous.subtype_mk ?_ _
    exact continuous_subtype_val.comp continuous_subtype_val
  continuous_invFun := by
    refine Continuous.subtype_mk (Continuous.subtype_mk ?_ _) _
    exact continuous_subtype_val

def singleComponents (C : CompactCarrier.{u}) [ConnectedSpace C.Carrier]
    (h : ConnectedSpace (C.pieceInterior ⊤)) : C.Components where
  count := 1
  count_pos := Nat.one_pos
  piece _ := ⊤
  closed _ := isClosed_univ
  connected _ := (topOpensDiffeomorph (I := C.model) C.Carrier).toHomeomorph.connectedSpace_iff.mpr
    inferInstance
  disjoint i j h := (h (Subsingleton.elim i j)).elim
  covers := Set.iUnion_const _
  interior_connected _ := h

def componentComponents (C : CompactCarrier.{u}) (D : C.Components) (i : Fin D.count) :
    (componentCarrier C D i).Components :=
  letI : ConnectedSpace (componentCarrier C D i).Carrier := D.connected i
  singleComponents _
    ((componentPieceInteriorHomeomorph C D i).connectedSpace_iff.mpr (D.interior_connected i))

def emptyTorusPairing (C : CompactCarrier.{u}) : TorusPairing C where
  count := 0
  gluing := {
    left := fun k => k.elim0
    right := fun k => k.elim0
    attaching := fun k => k.elim0
    isClosed_left := fun k => k.elim0
    isClosed_right := fun k => k.elim0
    disjoint_left_right := fun k => k.elim0
    disjoint_blocks := fun k => k.elim0 }
  leftParam k := k.elim0
  rightParam k := k.elim0
  matching k := k.elim0
  matching_eq k := k.elim0
  leftCollar k := k.elim0
  rightCollar k := k.elim0
  left_source k := k.elim0
  right_source k := k.elim0
  left_zero k := k.elim0
  right_zero k := k.elim0
  reversing k := k.elim0

theorem iUnion_block_emptyTorusPairing (C : CompactCarrier.{u}) :
    ⋃ k, (emptyTorusPairing C).gluing.block k = ∅ :=
  Set.iUnion_eq_empty.mpr fun k => k.elim0

def emptyTorusPairingHomeomorph (C : CompactCarrier.{u}) :
    (emptyTorusPairing C).QuotientSpace ≃ₜ C.Carrier :=
  (Homeomorph.Quotient.congrRight (fun x y => by
    change (x = y ∨ ∃ k : Fin 0, _) ↔ x = y
    simp)).trans Homeomorph.quotientBot

@[simp]
theorem emptyTorusPairingHomeomorph_quotientMap (C : CompactCarrier.{u}) (x : C.Carrier) :
    emptyTorusPairingHomeomorph C ((emptyTorusPairing C).quotientMap x) = x := rfl

namespace RawGraphPresentation
variable {W : CompactCarrier.{u}}

def ofPiece (G : RawGraphPresentation W) (i : Fin G.components.count) :
    RawGraphPresentation (componentCarrier G.cutCarrier G.components i) where
  cutCarrier := componentCarrier G.cutCarrier G.components i
  components := componentComponents G.cutCarrier G.components i
  fibration _ := CircleFibration.toComponent G.components i (G.fibration i)
  pairing := emptyTorusPairing _
  externalCount := Fintype.card (G.OwnedSide i)
  external := G.pieceBoundaryTori i
  cutExternal := G.pieceBoundaryTori i
  external_exhausted := G.pieceBoundaryTori_image i
  cut_boundary_exhausted := by
    rw [iUnion_block_emptyTorusPairing, Set.empty_union]
    exact G.pieceBoundaryTori_image i
  external_disjoint := by
    rw [iUnion_block_emptyTorusPairing]
    exact Set.empty_disjoint _
  reconstruction := emptyTorusPairingHomeomorph _
  quotient_smooth := contMDiff_id
  quotient_oriented x := by
    refine ⟨LinearEquiv.refl ℝ _, fun v => ?_, ?_⟩
    · change v =
        mfderiv _ _ (id : (componentCarrier G.cutCarrier G.components i).Carrier → _) x v
      rw [mfderiv_id]
      rfl
    · change Orientation.map (Fin 3) (LinearEquiv.refl ℝ (TangentSpace _ x))
          ((componentCarrier G.cutCarrier G.components i).orientation.orientation x) =
        (componentCarrier G.cutCarrier G.components i).orientation.orientation x
      rw [Orientation.map_refl]
      rfl
  interiorImage := (componentCarrier G.cutCarrier G.components i).interior
  interiorDiffeomorph := Diffeomorph.refl _ _ _
  interior_map _ := rfl
  seam k := k.elim0
  seam_source k := k.elim0
  seam_zero k := k.elim0
  seam_positive k := k.elim0
  seam_negative k := k.elim0
  seam_interior k := k.elim0
  seam_disjoint k := k.elim0
  marked_collar _ _ _ := rfl
  external_seam_disjoint _ k := k.elim0
  leftPiece k := k.elim0
  rightPiece k := k.elim0
  left_owned k := k.elim0
  right_owned k := k.elim0
  externalPiece _ := ⟨0, Nat.one_pos⟩
  external_owned _ := Set.subset_univ _

@[simp]
theorem ofPiece_components_count (G : RawGraphPresentation W) (i : Fin G.components.count) :
    (G.ofPiece i).components.count = 1 := rfl

@[simp]
theorem ofPiece_pairing_count (G : RawGraphPresentation W) (i : Fin G.components.count) :
    (G.ofPiece i).pairing.count = 0 := rfl

@[simp]
theorem ofPiece_externalCount (G : RawGraphPresentation W) (i : Fin G.components.count) :
    (G.ofPiece i).externalCount = Fintype.card (G.OwnedSide i) := rfl

theorem ofPiece_external (G : RawGraphPresentation W) (i : Fin G.components.count) :
    (G.ofPiece i).external = G.pieceBoundaryTori i := rfl

end RawGraphPresentation
end GC.GraphManifold
