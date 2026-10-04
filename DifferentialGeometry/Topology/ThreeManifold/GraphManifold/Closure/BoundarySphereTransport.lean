import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.ComponentPatchTransport
import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.RawBoundaryAssembly
import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.SphereCutCarrier

/-!
Canonical component charts keep their actual sum inclusion under the same boundary assembly.
Interior reconstruction injectivity then preserves the original external collar avoidance.
-/

set_option autoImplicit false

noncomputable section

open Set Function
open DifferentialGeometry DifferentialGeometry.Topology GC.Endpoint GC.Seifert
open scoped Manifold ContDiff Topology

universe u v w z

namespace GC.GraphManifold

variable (C D : CompactCarrier.{u}) (hC : C.kind = .withBoundary) (hD : D.kind = .withBoundary)
  [ConnectedSpace C.Carrier] [ConnectedSpace D.Carrier]

set_option backward.isDefEq.respectTransparency false in
def boundaryCanonicalRightDiffeomorph (K : CompactCarrier.{u}) (DK : K.Components)
    (hcut : K = C.withBoundarySum D hC hD)
    (hc : (hcut ▸ DK) = rawBoundarySumComponents C D hC hD)
    (i : Fin DK.count) (hi : i.val = 1) :
    D.Carrier ≃ₘ⟮D.model, (GC.Topology.componentCarrier K DK i).model⟯
      (GC.Topology.componentCarrier K DK i).Carrier := by
  subst K
  cases hc
  have he : i = rawBoundaryRightIndex C D hC hD := Fin.ext hi
  subst i
  exact rawBoundaryRightDiffeomorph C D hC hD

set_option backward.isDefEq.respectTransparency false in
theorem boundaryCanonicalRightDiffeomorph_apply (K : CompactCarrier.{u}) (DK : K.Components)
    (hcut : K = C.withBoundarySum D hC hD)
    (hc : (hcut ▸ DK) = rawBoundarySumComponents C D hC hD)
    (i : Fin DK.count) (hi : i.val = 1) (y : D.Carrier) :
    (boundaryCanonicalRightDiffeomorph C D hC hD K DK hcut hc i hi y).val =
      hcut.symm ▸ (Sum.inr y : (C.withBoundarySum D hC hD).Carrier) := by
  subst K
  cases hc
  have he : i = rawBoundaryRightIndex C D hC hD := Fin.ext hi
  subst i
  exact rawBoundaryRightDiffeomorph_apply C D hC hD y

private theorem carrierCast_injective {K S : CompactCarrier.{u}} (h : K = S) :
    Injective (fun x : S.Carrier => (h.symm ▸ x : K.Carrier)) := by
  cases h
  exact fun x y he => he

end GC.GraphManifold

namespace GC.Seifert.TorusPresentation

variable {W : CompactCarrier.{u}} (T : TorusPresentation W)

theorem cutMap_eq_of_mem_interior {a b : T.cutCarrier.Carrier}
    (ha : a ∈ T.cutCarrier.interior) (he : T.cutMap a = T.cutMap b) : a = b := by
  apply T.pairing.gluing.eq_of_rel_of_notMem
  · intro i hi
    have hb : T.cutCarrier.model.IsBoundaryPoint a := by
      change a ∈ T.cutCarrier.model.boundary T.cutCarrier.Carrier
      rw [T.cut_boundary_exhausted]
      exact Or.inl (mem_iUnion.mpr ⟨i, hi⟩)
    exact (T.cutCarrier.model.isInteriorPoint_iff_not_isBoundaryPoint a).mp ha hb
  · exact Quotient.exact (T.reconstruction.injective he)

end GC.Seifert.TorusPresentation

namespace GC.GraphManifold

variable (C D : CompactCarrier.{u}) (hC : C.kind = .withBoundary) (hD : D.kind = .withBoundary)
  [ConnectedSpace C.Carrier] [ConnectedSpace D.Carrier]
  {N : CompactCarrier.{u}} (T : TorusPresentation N)
  (hcut : T.cutCarrier = C.withBoundarySum D hC hD)
  (hc : (hcut ▸ T.components) = rawBoundarySumComponents C D hC hD)
  (i : Fin T.components.count) (hi : i.val = 1)
  {E : Type v} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type w} [TopologicalSpace H] (I : ModelWithCorners ℝ E H)
  {X : Type z} [TopologicalSpace X] [ChartedSpace H X]
  (p : PartialDiffeomorph I D.model X D.Carrier ∞)
  (x : X) (hx : x ∈ p.source) (hI : p.target ⊆ D.interior)

def boundaryTransportedPatch : PartialDiffeomorph I N.model X N.Carrier ∞ :=
  T.transportComponentPatch i D
    (boundaryCanonicalRightDiffeomorph C D hC hD T.cutCarrier T.components hcut hc i hi)
    I p x hx hI

theorem boundaryTransportedPatch_source :
    (boundaryTransportedPatch C D hC hD T hcut hc i hi I p x hx hI).source = p.source :=
  T.transportComponentPatch_source i D
    (boundaryCanonicalRightDiffeomorph C D hC hD T.cutCarrier T.components hcut hc i hi)
    I p x hx hI

theorem boundaryTransportedPatch_interior :
    (boundaryTransportedPatch C D hC hD T hcut hc i hi I p x hx hI).target ⊆ N.interior :=
  T.transportComponentPatch_interior i D
    (boundaryCanonicalRightDiffeomorph C D hC hD T.cutCarrier T.components hcut hc i hi)
    I p x hx hI

theorem boundaryTransportedPatch_apply (y : X) (hy : y ∈ p.source) :
    boundaryTransportedPatch C D hC hD T hcut hc i hi I p x hx hI y =
      T.cutMap (hcut.symm ▸ (Sum.inr (p y) : (C.withBoundarySum D hC hD).Carrier)) := by
  exact (T.transportComponentPatch_apply i D
    (boundaryCanonicalRightDiffeomorph C D hC hD T.cutCarrier T.components hcut hc i hi)
    I p x hx hI y hy).trans (congrArg T.cutMap
      (boundaryCanonicalRightDiffeomorph_apply C D hC hD
        T.cutCarrier T.components hcut hc i hi (p y)))

include hc i hi hI in
set_option backward.isDefEq.respectTransparency false in
private theorem boundaryTransportedPatch_native_interior (y : X) (hy : y ∈ p.source) :
    (hcut.symm ▸ (Sum.inr (p y) : (C.withBoundarySum D hC hD).Carrier)) ∈
      T.cutCarrier.interior := by
  let e := boundaryCanonicalRightDiffeomorph C D hC hD
    T.cutCarrier T.components hcut hc i hi
  let r := e.toPartialDiffeomorph.trans
    (DifferentialGeometry.Manifold.openSubtypePartialDiffeomorph
      T.cutCarrier.model (T.components.piece i) ⟨e (p y)⟩)
  have hr : p y ∈ r.source := by
    change p y ∈ univ ∧ e (p y) ∈ univ
    exact ⟨mem_univ _, mem_univ _⟩
  have hp : D.model.IsInteriorPoint (p y) := hI (p.map_source hy)
  have hl := r.isLocalDiffeomorphAt D.model T.cutCarrier.model ∞ hr
  have hb := (hl.isInteriorPoint_iff (by simp : (∞ : ℕ∞ω) ≠ 0)).mp hp
  change T.cutCarrier.model.IsInteriorPoint (e (p y)).val at hb
  rwa [boundaryCanonicalRightDiffeomorph_apply] at hb

variable {n : ℕ} (E1 : BoundaryTori C 1) (E2 : BoundaryTori D (n + 1))
  (f : Torus ≃ₘ⟮torusModel, torusModel⟯ Torus)
  (hrev : ReversesBoundaryOrientation (C.withBoundarySum D hC hD)
    (boundaryPortLeftCollar C D hC hD E1)
    (fun q => boundaryPortRightCollar C D hC hD E2 0 (f q.1, q.2)))
  (e : (boundaryPortPairing C D hC hD E1 E2 f hrev).QuotientSpace ≃ₜ N.Carrier)
  (hsquare : ∀ a, e ((boundaryPortPairing C D hC hD E1 E2 f hrev).quotientMap a) =
    T.cutMap (hcut.symm ▸ a))

include hsquare in
set_option backward.isDefEq.respectTransparency false in
theorem boundaryTransportedPatch_square (y : X) (hy : y ∈ p.source) :
    boundaryTransportedPatch C D hC hD T hcut hc i hi I p x hx hI y =
      e ((boundaryPortPairing C D hC hD E1 E2 f hrev).quotientMap (Sum.inr (p y))) :=
  (boundaryTransportedPatch_apply C D hC hD T hcut hc i hi I p x hx hI y hy).trans
    (hsquare (Sum.inr (p y))).symm

include hI hsquare in
set_option backward.isDefEq.respectTransparency false in
theorem boundaryTransportedPatch_external_disjoint
    (δ : ℝ) (hδ : 0 < δ) (hδ1 : δ ≤ 1) (hn : T.externalCount = n)
    (hport : ∀ r q, q ∈ halfCollarSource →
      T.external.collar (Fin.cast hn.symm r) q =
        e ((boundaryPortPairing C D hC hD E1 E2 f hrev).quotientMap
          (Sum.inr (E2.collar r.succ (q.1, halfSpaceScale hδ q.2)))))
    (havoid : ∀ r, Disjoint p.target (E2.collar r).target) :
    ∀ r, Disjoint
      (boundaryTransportedPatch C D hC hD T hcut hc i hi I p x hx hI).target
      (T.external.collar (Fin.cast hn.symm r)).target := by
  intro r
  apply disjoint_left.mpr
  intro y hyp hyt
  let d := boundaryTransportedPatch C D hC hD T hcut hc i hi I p x hx hI
  let a := d.symm y
  have ha : a ∈ p.source := by
    rw [← boundaryTransportedPatch_source C D hC hD T hcut hc i hi I p x hx hI]
    exact d.map_target hyp
  let q := (T.external.collar (Fin.cast hn.symm r)).symm y
  have hq : q ∈ halfCollarSource := by
    rw [← T.external.source_eq]
    exact (T.external.collar (Fin.cast hn.symm r)).map_target hyt
  have hscaled := halfSpaceScale_mem hδ hδ1 hq
  have heq : T.cutMap (hcut.symm ▸ (Sum.inr (p a) :
      (C.withBoundarySum D hC hD).Carrier)) =
      T.cutMap (hcut.symm ▸ (Sum.inr (E2.collar r.succ
        (q.1, halfSpaceScale hδ q.2)) : (C.withBoundarySum D hC hD).Carrier)) := by
    calc
      T.cutMap (hcut.symm ▸ (Sum.inr (p a) :
          (C.withBoundarySum D hC hD).Carrier)) = d a :=
        (boundaryTransportedPatch_apply C D hC hD T hcut hc i hi I p x hx hI a ha).symm
      _ = y := d.right_inv hyp
      _ = T.external.collar (Fin.cast hn.symm r) q :=
        ((T.external.collar (Fin.cast hn.symm r)).right_inv hyt).symm
      _ = e ((boundaryPortPairing C D hC hD E1 E2 f hrev).quotientMap
          (Sum.inr (E2.collar r.succ (q.1, halfSpaceScale hδ q.2)))) := hport r q hq
      _ = _ := hsquare _
  have he := T.cutMap_eq_of_mem_interior
    (boundaryTransportedPatch_native_interior C D hC hD T hcut hc i hi I p hI a ha) heq
  have hp : p a = E2.collar r.succ (q.1, halfSpaceScale hδ q.2) :=
    Sum.inr_injective (carrierCast_injective hcut he)
  exact (disjoint_left.mp (havoid r.succ)) (p.map_source ha)
    (hp.symm ▸ (E2.collar r.succ).map_source ((E2.source_eq r.succ).symm.subset hscaled))


include hc i hi hsquare in
set_option backward.isDefEq.respectTransparency false in
theorem exists_boundarySphereCut
    (d : PartialDiffeomorph sphereSignedCollarModel D.model
      (ClosureSphere.{u} × ℝ) D.Carrier ∞)
    (hd : d.source = sphereSignedCollarSource) (hdI : d.target ⊆ D.interior)
    (δ : ℝ) (hδ : 0 < δ) (hδ1 : δ ≤ 1) (hn : T.externalCount = n)
    (hport : ∀ r q, q ∈ halfCollarSource →
      T.external.collar (Fin.cast hn.symm r) q =
        e ((boundaryPortPairing C D hC hD E1 E2 f hrev).quotientMap
          (Sum.inr (E2.collar r.succ (q.1, halfSpaceScale hδ q.2)))))
    (havoid : ∀ r, Disjoint d.target (E2.collar r).target) :
    ∃ q : PartialDiffeomorph sphereSignedCollarModel N.model
      (ClosureSphere.{u} × ℝ) N.Carrier ∞,
      q.source = sphereSignedCollarSource ∧ q.target ⊆ N.interior ∧
      (∀ z s, (z, s) ∈ sphereSignedCollarSource → q (z, s) =
        e ((boundaryPortPairing C D hC hD E1 E2 f hrev).quotientMap
          (Sum.inr (d (z, s))))) ∧
      ∃ (K : CompactCarrier.{u}) (B : MixedBoundaryCertificate K)
        (ht : B.torusCount = T.externalCount) (h2 : B.sphereCount = 2)
        (fold : K.Carrier → N.Carrier),
        K.kind = .withBoundary ∧ ContMDiff K.model N.model ∞ fold ∧ Surjective fold ∧
        (∀ a, ∃ A : TangentSpace K.model a ≃ₗ[ℝ] TangentSpace N.model (fold a),
          (∀ v, A v = mfderiv K.model N.model fold a v) ∧
          Orientation.map (Fin 3) A (K.orientation.orientation a) =
            N.orientation.orientation (fold a)) ∧
        (∀ r p, p ∈ halfCollarSource →
          fold (B.tori.collar (Fin.cast ht.symm r) p) = T.external.collar r p) ∧
        (∀ r z s (hs : 0 ≤ s), s < 1 →
          fold (B.sphere (Fin.cast h2.symm r) (z, halfPoint s hs)) =
            e ((boundaryPortPairing C D hC hD E1 E2 f hrev).quotientMap
              (Sum.inr (d (z, if r.val = 0 then s else -s))))) ∧
        (∀ a b, fold a = fold b ↔ a = b ∨ ∃ z,
          (a = B.sphere (Fin.cast h2.symm 0) (z, halfZero) ∧
            b = B.sphere (Fin.cast h2.symm 1) (z, halfZero)) ∨
          (a = B.sphere (Fin.cast h2.symm 1) (z, halfZero) ∧
            b = B.sphere (Fin.cast h2.symm 0) (z, halfZero))) ∧
        ∃ ρ : Quotient (Setoid.ker fold) ≃ₜ N.Carrier,
          ∀ a, ρ (Quotient.mk'' a) = fold a := by
  let a : ClosureSphere.{u} × ℝ := (Classical.choice inferInstance, 0)
  have ha : a ∈ d.source := by
    rw [hd]
    exact ⟨mem_univ _, by norm_num [a]⟩
  let q := boundaryTransportedPatch C D hC hD T hcut hc i hi
    sphereSignedCollarModel d a ha hdI
  have hqs : q.source = sphereSignedCollarSource :=
    (boundaryTransportedPatch_source C D hC hD T hcut hc i hi
      sphereSignedCollarModel d a ha hdI).trans hd
  have hqI : q.target ⊆ N.interior := boundaryTransportedPatch_interior
    C D hC hD T hcut hc i hi sphereSignedCollarModel d a ha hdI
  have hq : ∀ z s, (z, s) ∈ sphereSignedCollarSource → q (z, s) =
      e ((boundaryPortPairing C D hC hD E1 E2 f hrev).quotientMap
        (Sum.inr (d (z, s)))) := by
    intro z s hzs
    exact boundaryTransportedPatch_square C D hC hD T hcut hc i hi
      sphereSignedCollarModel d a ha hdI E1 E2 f hrev e hsquare (z, s) (hd.symm.subset hzs)
  have hav : ∀ r, Disjoint (T.external.collar r).target q.target := by
    intro r
    have h := boundaryTransportedPatch_external_disjoint C D hC hD T hcut hc i hi
      sphereSignedCollarModel d a ha hdI E1 E2 f hrev e hsquare δ hδ hδ1 hn hport havoid
      (Fin.cast hn r)
    have hr : Fin.cast hn.symm (Fin.cast hn r) = r := Fin.ext rfl
    rw [hr] at h
    exact h.symm
  obtain ⟨K, B, ht, h2, fold, hk, hsm, hsurj, hO, hold, hsphere, hrel, ρ, hρ⟩ :=
    exists_sphereCutCarrier N q hqs hqI T.external T.external_exhausted hav
  refine ⟨q, hqs, hqI, hq, K, B, ht, h2, fold, hk, hsm, hsurj, hO, hold, ?_, hrel, ρ, hρ⟩
  intro r z s hs hs1
  rw [hsphere r z s hs hs1]
  apply hq
  exact ⟨mem_univ z, by split_ifs <;> constructor <;> linarith⟩

end GC.GraphManifold
