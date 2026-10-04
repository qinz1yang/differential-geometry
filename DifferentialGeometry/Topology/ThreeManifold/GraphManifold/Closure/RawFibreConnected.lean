import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.FibrePairingTopology
import Mathlib.Topology.Connected.TotallyDisconnected

/-!
The actual retained fibre-excision quotient is connected through the original finite gluing.
-/

set_option autoImplicit false

noncomputable section

open Set Function Manifold
open DifferentialGeometry DifferentialGeometry.Topology GC.Endpoint GC.Seifert
open scoped Manifold ContDiff Topology

universe u

namespace GC.GraphManifold.RawGraphPresentation

private theorem rawComponent_exists {C : CompactCarrier.{u}} (D : C.Components)
    (x : C.Carrier) : ∃ i, x ∈ D.piece i := by
  apply mem_iUnion.mp
  rw [D.covers]
  exact mem_univ x

private def rawComponentIndex {C : CompactCarrier.{u}} (D : C.Components)
    (x : C.Carrier) : Fin D.count := Classical.choose (rawComponent_exists D x)

private theorem rawComponentIndex_mem {C : CompactCarrier.{u}} (D : C.Components)
    (x : C.Carrier) : x ∈ D.piece (rawComponentIndex D x) :=
  Classical.choose_spec (rawComponent_exists D x)

private theorem rawComponentIndex_eq {C : CompactCarrier.{u}} (D : C.Components)
    {x : C.Carrier} {i : Fin D.count} (hx : x ∈ D.piece i) : rawComponentIndex D x = i := by
  by_contra h
  exact (D.disjoint h).le_bot ⟨rawComponentIndex_mem D x, hx⟩

private def rawComponentPoint {C : CompactCarrier.{u}} (D : C.Components)
    (i : Fin D.count) : D.piece i := by
  let := D.connected i
  exact Classical.choice inferInstance

private theorem rawComponentLabel_continuous {C : CompactCarrier.{u}} (D : C.Components)
    (a : Fin D.count → Bool) : Continuous (fun x => a (rawComponentIndex D x)) := by
  apply continuous_iff_continuousAt.mpr
  intro x
  have heq : (fun y => a (rawComponentIndex D y)) =ᶠ[𝓝 x]
      (fun y : C.Carrier => a (rawComponentIndex D x)) := by
    filter_upwards [(D.piece (rawComponentIndex D x)).isOpen.mem_nhds
      (rawComponentIndex_mem D x)] with y hy
    rw [rawComponentIndex_eq D hy]
  exact continuousAt_const.congr heq.symm

variable {M : ConnectedClosedOrientedManifold.{u} 3}
  (G : RawGraphPresentation (NoCuts.carrier M))
variable (φ : PartialDiffeomorph (𝓘(ℝ, ℂ).prod (𝓡 1)) G.cutCarrier.model
  (PlaneLift.{u} × Circle) G.cutCarrier.Carrier ∞)
variable (h3 : {p | ‖p.1.down‖ ≤ 3} ⊆ φ.source)
variable (hI : φ.target ⊆ G.cutCarrier.interior)
variable (K : CompactCarrier.{u}) (ι : K.Carrier → G.cutCarrier.Carrier)
variable (hι : _root_.Topology.IsEmbedding ι)
variable (hrange : range ι = G.FibreCutComplement φ)
variable (D : K.Components) (hc : D.count = G.components.count)
variable (hm : ∀ j x, x ∈ D.piece (Fin.cast hc.symm j) ↔ ι x ∈ G.components.piece j)

include h3 hI hrange in
private theorem rawRetainedBlock_range (j : Fin G.pairing.count) :
    G.pairing.gluing.block j ⊆ range ι := by
  intro x hx
  rw [hrange]
  rintro ⟨p, hp, rfl⟩
  have hs : p ∈ φ.source := h3 (by
    change ‖p.1.down‖ < 1 at hp
    change ‖p.1.down‖ ≤ 3
    linarith)
  have hi := hI (φ.map_source hs)
  have hb : G.cutCarrier.model.IsBoundaryPoint (φ p) := by
    change φ p ∈ G.cutCarrier.model.boundary G.cutCarrier.Carrier
    rw [G.cut_boundary_exhausted]
    exact Or.inl (mem_iUnion.mpr ⟨j, hx⟩)
  exact (G.cutCarrier.model.isInteriorPoint_iff_not_isBoundaryPoint _).mp hi hb

include D hc hm in
private theorem rawRetained_bool_constant
    (f : Quotient (G.fibreRetainedGluing φ h3 hI K ι hι hrange).setoid → Bool)
    (hf : Continuous f) : ∀ x y, f x = f y := by
  let q : K.Carrier → Quotient (G.fibreRetainedGluing φ h3 hI K ι hι hrange).setoid :=
    Quotient.mk''
  let a : Fin G.components.count → Bool := fun j =>
    f (q (rawComponentPoint D (Fin.cast hc.symm j)).val)
  let l : G.cutCarrier.Carrier → Bool := fun x => a (rawComponentIndex G.components x)
  have hl : Continuous l := rawComponentLabel_continuous G.components a
  have hret (x : K.Carrier) : l (ι x) = f (q x) := by
    let j := rawComponentIndex G.components (ι x)
    have hx : x ∈ D.piece (Fin.cast hc.symm j) :=
      (hm j x).mpr (rawComponentIndex_mem G.components (ι x))
    let := D.connected (Fin.cast hc.symm j)
    have hcont : Continuous (fun z : D.piece (Fin.cast hc.symm j) => f (q z.val)) :=
      hf.comp (continuous_quotient_mk'.comp continuous_subtype_val)
    exact (inferInstance : PreconnectedSpace (D.piece (Fin.cast hc.symm j))).constant
      hcont (x := rawComponentPoint D (Fin.cast hc.symm j)) (y := ⟨x, hx⟩)
  have hrel : ∀ x y, G.pairing.gluing.rel x y → l x = l y := by
    intro x y hxy
    rcases hxy with rfl | ⟨j, hx, hy⟩
    · rfl
    · have hyr : y ∈ G.pairing.gluing.block j :=
        hy ▸ G.pairing.gluing.flip_mem_block hx
      obtain ⟨x', hx'⟩ := G.rawRetainedBlock_range φ h3 hI K ι hrange j hx
      obtain ⟨y', hy'⟩ := G.rawRetainedBlock_range φ h3 hI K ι hrange j hyr
      rw [← hx', ← hy', hret, hret]
      congr 1
      apply Quotient.sound
      apply (G.fibreRetainedGluing_rel_iff φ h3 hI K ι hι hrange x' y').mpr
      rw [hx', hy']
      exact Or.inr ⟨j, hx, hy⟩
  let old : G.pairing.QuotientSpace → Bool := Quotient.lift l hrel
  have hold : Continuous old := by
    exact hl.quotient_lift hrel
  let : ConnectedSpace G.pairing.QuotientSpace :=
    G.reconstruction.symm.surjective.connectedSpace G.reconstruction.symm.continuous
  intro x y
  obtain ⟨x', rfl⟩ := Quotient.exists_rep x
  obtain ⟨y', rfl⟩ := Quotient.exists_rep y
  rw [← hret, ← hret]
  exact (inferInstance : PreconnectedSpace G.pairing.QuotientSpace).constant hold
    (x := G.pairing.quotientMap (ι x')) (y := G.pairing.quotientMap (ι y'))

include D hc hm in
theorem fibreRetainedQuotient_connected :
    ConnectedSpace (Quotient (G.fibreRetainedGluing φ h3 hI K ι hι hrange).setoid) := by
  have hpre : PreconnectedSpace
      (Quotient (G.fibreRetainedGluing φ h3 hI K ι hι hrange).setoid) :=
    preconnectedSpace_of_forall_constant
      (G.rawRetained_bool_constant φ h3 hI K ι hι hrange D hc hm)
  let j : Fin D.count := ⟨0, D.count_pos⟩
  have hne : Nonempty (Quotient
      (G.fibreRetainedGluing φ h3 hI K ι hι hrange).setoid) :=
    ⟨Quotient.mk'' (rawComponentPoint D j).val⟩
  exact { toPreconnectedSpace := hpre, toNonempty := hne }

end GC.GraphManifold.RawGraphPresentation
