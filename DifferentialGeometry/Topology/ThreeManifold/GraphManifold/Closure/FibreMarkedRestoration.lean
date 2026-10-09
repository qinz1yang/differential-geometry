import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.RegularFibreRestoration
import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.BoundaryPortOrientation
import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.FibrePlugSideDiffeomorph
import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Seifert.CollarGermAdapter

/-!
Replacement of the actual restoration solid by its whole marked side model preserves the same
refilled manifold, with physical orientation reversal supplied before taking the quotient.
-/

set_option autoImplicit false

noncomputable section

open Set Function Manifold
open DifferentialGeometry DifferentialGeometry.Topology GC.Endpoint GC.Seifert
open GC.Endpoint.CompactCarrier GC.Seifert.ElementaryPresentation
open scoped Manifold ContDiff Topology

universe u

namespace GC.GraphManifold

private theorem markedPort_relation {C D : CompactCarrier.{u}}
    {hC : C.kind = .withBoundary} {hD : D.kind = .withBoundary}
    [Nonempty C.Carrier] [Nonempty D.Carrier]
    {E : BoundaryTori C 1} {F : BoundaryTori D 1}
    {f : Torus ≃ₘ⟮torusModel, torusModel⟯ Torus}
    (hr : ReversesBoundaryOrientation (withBoundarySum C D hC hD)
      (boundaryPortLeftCollar C D hC hD E)
      (fun p => boundaryPortRightCollar C D hC hD F 0 (f p.1, p.2)))
    {x y : (withBoundarySum C D hC hD).Carrier} :
    (boundaryPortPairing C D hC hD E F f hr).gluing.rel x y ↔
      x = y ∨ ∃ t : Torus,
        (x = Sum.inl (E.torusMap 0 t) ∧ y = Sum.inr (F.torusMap 0 (f t))) ∨
        (y = Sum.inl (E.torusMap 0 t) ∧ x = Sum.inr (F.torusMap 0 (f t))) := by
  rw [GC.Seifert.TorusPairing.rel_iff_params]
  constructor
  · rintro (he | ⟨j, t, he⟩)
    · exact Or.inl he
    · exact Or.inr ⟨t, he⟩
  · rintro (he | ⟨t, he⟩)
    · exact Or.inl he
    · exact Or.inr ⟨⟨0, Nat.one_pos⟩, t, he⟩

variable (K S : CompactCarrier.{u})
variable (hK : K.kind = .withBoundary) (hS : S.kind = .withBoundary)
variable [Nonempty K.Carrier] [Nonempty S.Carrier]
variable (Γ : BoundaryTori K 1) (E : BoundaryTori S 1)
variable (g : solidSet.{u} ≃ₘ⟮𝓡∂ 3, S.model⟯ S.Carrier)
variable (ψ : Torus ≃ₘ⟮torusModel, torusModel⟯ Torus)
variable (hz : ∀ t, g (solidCollar 1 (t, halfZero)) = E.torusMap 0 (ψ t))
variable (O : ManifoldOrientation (𝓡∂ 3) solidSet.{u} 3)
variable (hr0 : ReversesBoundaryOrientation
  (withBoundarySum (regularFibreRestorationSolid O) K rfl hK)
  (boundaryPortLeftCollar (regularFibreRestorationSolid O) K rfl hK
    (regularFibreRestorationBoundary O))
  (fun p => boundaryPortRightCollar (regularFibreRestorationSolid O) K rfl hK Γ 0 p))
variable (hr1 : ReversesBoundaryOrientation (withBoundarySum K S hK hS)
  (boundaryPortLeftCollar K S hK hS Γ)
  (fun p => boundaryPortRightCollar K S hK hS E 0 (ψ p.1, p.2)))

private abbrev markedModelPairing :=
  boundaryPortPairing (regularFibreRestorationSolid O) K rfl hK
    (regularFibreRestorationBoundary O) Γ (Diffeomorph.refl torusModel Torus ∞) hr0

private abbrev markedSidePairing := boundaryPortPairing K S hK hS Γ E ψ hr1

private def markedSwap : solidSet.{u} ⊕ K.Carrier ≃ₜ K.Carrier ⊕ S.Carrier :=
  (g.toHomeomorph.sumCongr (Homeomorph.refl K.Carrier)).trans (Homeomorph.sumComm _ _)

omit [Nonempty K.Carrier] [Nonempty S.Carrier] in
include hz in
private theorem markedSwap_zero (t : Torus) :
    markedSwap K S g (Sum.inl (solidCollar 1 (t, halfZero))) =
      Sum.inr (E.torusMap 0 (ψ t)) := congrArg Sum.inr (hz t)

variable {K S hK hS Γ E g ψ hz O hr0 hr1}

set_option backward.isDefEq.respectTransparency false in
include hz in
private theorem markedSwap_relation {x y : solidSet.{u} ⊕ K.Carrier} :
    (markedModelPairing K hK Γ O hr0).gluing.rel x y ↔
      (markedSidePairing K S hK hS Γ E ψ hr1).gluing.rel
        (markedSwap K S g x) (markedSwap K S g y) := by
  rw [markedPort_relation, markedPort_relation]
  constructor
  · rintro (rfl | ⟨t, he | he⟩)
    · exact Or.inl rfl
    · obtain ⟨rfl, rfl⟩ := he
      exact Or.inr ⟨t, Or.inr ⟨rfl, markedSwap_zero K S E g ψ hz t⟩⟩
    · obtain ⟨rfl, rfl⟩ := he
      exact Or.inr ⟨t, Or.inl ⟨rfl, markedSwap_zero K S E g ψ hz t⟩⟩
  · rintro (he | ⟨t, he | he⟩)
    · exact Or.inl ((markedSwap K S g).injective he)
    · refine Or.inr ⟨t, Or.inr ⟨?_, ?_⟩⟩
      · apply (markedSwap K S g).injective
        exact he.2.trans (markedSwap_zero K S E g ψ hz t).symm
      · exact (markedSwap K S g).injective he.1
    · refine Or.inr ⟨t, Or.inl ⟨?_, ?_⟩⟩
      · apply (markedSwap K S g).injective
        exact he.2.trans (markedSwap_zero K S E g ψ hz t).symm
      · exact (markedSwap K S g).injective he.1

variable (K S hK hS Γ E g ψ hz O hr0 hr1)

include hz in
private def markedSwapQuotient :
    (markedModelPairing K hK Γ O hr0).QuotientSpace ≃ₜ
      (markedSidePairing K S hK hS Γ E ψ hr1).QuotientSpace := by
  let e : (markedModelPairing K hK Γ O hr0).QuotientSpace ≃
      (markedSidePairing K S hK hS Γ E ψ hr1).QuotientSpace :=
    Quotient.congr (markedSwap K S g).toEquiv
      (fun x y => markedSwap_relation (K := K) (S := S) (hK := hK) (hS := hS)
        (Γ := Γ) (E := E) (g := g) (ψ := ψ) (hz := hz) (O := O)
        (hr0 := hr0) (hr1 := hr1) (x := x) (y := y))
  apply Continuous.homeoOfEquivCompactToT2 (f := e)
  exact (((markedSidePairing K S hK hS Γ E ψ hr1).quotientMap.continuous.comp
    (markedSwap K S g).continuous)).quotient_lift
      (fun x y hxy => Quotient.sound
        ((markedSwap_relation (K := K) (S := S) (hK := hK) (hS := hS)
          (Γ := Γ) (E := E) (g := g) (ψ := ψ) (hz := hz) (O := O)
          (hr0 := hr0) (hr1 := hr1)).mp hxy))

include hz in
private theorem markedSwapQuotient_apply (x : solidSet.{u} ⊕ K.Carrier) :
    markedSwapQuotient K S hK hS Γ E g ψ hz O hr0 hr1
      ((markedModelPairing K hK Γ O hr0).quotientMap x) =
        (markedSidePairing K S hK hS Γ E ψ hr1).quotientMap (markedSwap K S g x) := rfl

def markedRestorationMatching (ψ : Torus ≃ₘ⟮torusModel, torusModel⟯ Torus) (ε : Bool) :
    Torus ≃ₘ⟮torusModel, torusModel⟯ Torus :=
  ψ.trans (if ε then boundaryPortMarkedReflection ψ else Diffeomorph.refl torusModel Torus ∞)

def markedRestorationSolidMap (ε : Bool) : solidSet.{u} ≃ₘ⟮𝓡∂ 3, S.model⟯ S.Carrier :=
  (if ε then boundedPlugSolidReflection else Diffeomorph.refl (𝓡∂ 3) solidSet ∞).trans g

theorem markedRestorationMatching_meridian (ε : Bool) (θ : Circle) :
    markedRestorationMatching ψ ε (θ, 1) = ψ (θ, 1) := by
  cases ε
  · rfl
  · exact boundaryPortMarkedReflection_meridian ψ θ

omit [Nonempty S.Carrier] in
include hz in
private theorem markedRestorationSolidMap_zero (ε : Bool) (t : Torus) :
    markedRestorationSolidMap S g ε (solidCollar 1 (t, halfZero)) =
      E.torusMap 0 (markedRestorationMatching ψ ε t) := by
  cases ε
  · exact hz t
  · change g (boundedPlugSolidReflection (solidCollar 1 (t, halfZero))) = _
    rw [boundedPlugSolidReflection_collar, hz]
    change E.torusMap 0 (ψ (t.1, t.2⁻¹)) =
      E.torusMap 0 (boundaryPortMarkedReflection ψ (ψ t))
    rw [boundaryPortMarkedReflection_apply, ψ.symm_apply_apply]

variable (M : ConnectedClosedOrientedManifold.{u} 3)
variable (φ : PartialDiffeomorph (𝓘(ℝ, ℂ).prod (𝓡 1)) (𝓡 3)
  (PlaneLift.{u} × Circle) M.Carrier ∞)
variable (h3 : {p | ‖p.1.down‖ ≤ 3} ⊆ φ.source)
variable (ι : K.Carrier → M.Carrier)
variable (hι : IsSmoothEmbedding K.model (𝓡 3) ∞ ι)
variable (hr : range ι = (φ '' {p : PlaneLift.{u} × Circle | ‖p.1.down‖ < 1})ᶜ)
variable (hΓ : ∀ p : Torus × EuclideanHalfSpace 1, p ∈ halfCollarSource →
  ι (Γ.collar 0 p) = φ (ULift.up ((1 + p.2.val 0 / 2) • (p.1.1 : ℂ)), p.1.2))
variable (hb : K.model.boundary K.Carrier = Γ.image)
variable (hbij : ∀ x, Bijective (mfderiv K.model (𝓡 3) ι x))
variable (hO : ∀ x, ∃ H : TangentSpace K.model x ≃L[ℝ] TangentSpace (𝓡 3) (ι x),
  H.toContinuousLinearMap = mfderiv K.model (𝓡 3) ι x ∧
  Orientation.map (Fin 3) H.toLinearEquiv (K.orientation.orientation x) =
    M.orientation.orientation (ι x))

private def markedRestorationFold (ε : Bool) : K.Carrier ⊕ S.Carrier → M.Carrier :=
  Sum.elim ι (regularFibreRestorationFill M φ ∘ (markedRestorationSolidMap S g ε).symm)

include hK hS hι h3 in
private theorem markedRestorationFold_smooth (ε : Bool) :
    ContMDiff (withBoundarySum K S hK hS).model (𝓡 3) ∞
      (markedRestorationFold K S g M φ ι ε) := by
  have hi := hι.contMDiff
  have hg := (regularFibreRestorationFill_smooth M φ h3).comp
    (markedRestorationSolidMap S g ε).symm.contMDiff
  cases K with
  | mk k A OK =>
    cases S with
    | mk l B OS =>
      cases hK
      cases hS
      exact hi.sumElim hg

set_option backward.isDefEq.respectTransparency false in
include hz h3 hι hr hΓ hb hbij hO in
theorem exists_markedRegularFibreRestoration :
    ∃ ε : Bool,
    let f := markedRestorationMatching ψ ε
    ∃ hrev : ReversesBoundaryOrientation (withBoundarySum K S hK hS)
      (boundaryPortLeftCollar K S hK hS Γ)
      (fun p => boundaryPortRightCollar K S hK hS E 0 (f p.1, p.2)),
    let P := boundaryPortPairing K S hK hS Γ E f hrev
    ∃ (Q : ConnectedClosedOrientedManifold.{u} 3)
      (ρ : P.QuotientSpace ≃ₜ Q.Carrier)
      (e : Q.Carrier ≃ₘ⟮𝓡 3, 𝓡 3⟯ M.Carrier),
      e.preservesOrientation Q.orientation M.orientation ∧
      ContMDiff (withBoundarySum K S hK hS).model (𝓡 3) ∞ (ρ ∘ P.quotientMap) ∧
      (∀ x : K.Carrier, e (ρ (P.quotientMap (Sum.inl x))) = ι x) ∧
      (∀ y : S.Carrier, e (ρ (P.quotientMap (Sum.inr y))) =
        regularFibreRestorationFill M φ ((markedRestorationSolidMap S g ε).symm y)) ∧
      ∀ θ : Circle, f (θ, 1) = ψ (θ, 1) := by
  obtain ⟨O0, hrev0, Q0, ρ0, e0, hmodel⟩ :=
    exists_regularFibreRestoration M φ h3 K ι Γ hK hι hr hΓ hb hbij hO
  obtain ⟨ε, hrev⟩ := exists_boundaryPortReversingMatching K S hK hS Γ E ψ ψ
  let f := markedRestorationMatching ψ ε
  let gε := markedRestorationSolidMap S g ε
  have hzε : ∀ t, gε (solidCollar 1 (t, halfZero)) = E.torusMap 0 (f t) :=
    markedRestorationSolidMap_zero S E g ψ hz ε
  let P := boundaryPortPairing K S hK hS Γ E f hrev
  let P0 := boundaryPortPairing (regularFibreRestorationSolid O0) K rfl hK
    (regularFibreRestorationBoundary O0) Γ (Diffeomorph.refl torusModel Torus ∞) hrev0
  let H : P0.QuotientSpace ≃ₜ P.QuotientSpace :=
    markedSwapQuotient K S hK hS Γ E gε f hzε O0 hrev0 hrev
  let H0 : P.QuotientSpace ≃ₜ M.Carrier := H.symm.trans (ρ0.trans e0.toHomeomorph)
  have hleft (x : K.Carrier) : H0 (P.quotientMap (Sum.inl x)) = ι x := by
    have hh := markedSwapQuotient_apply K S hK hS Γ E gε f hzε O0 hrev0 hrev
      (Sum.inr x)
    change H (P0.quotientMap (Sum.inr x)) = P.quotientMap (Sum.inl x) at hh
    change e0 (ρ0 (H.symm (P.quotientMap (Sum.inl x)))) = ι x
    rw [← hh, H.symm_apply_apply]
    exact hmodel.2.2.2 x
  have hright (y : S.Carrier) : H0 (P.quotientMap (Sum.inr y)) =
      regularFibreRestorationFill M φ (gε.symm y) := by
    have hh := markedSwapQuotient_apply K S hK hS Γ E gε f hzε O0 hrev0 hrev
      (Sum.inl (gε.symm y))
    change H (P0.quotientMap (Sum.inl (gε.symm y))) =
      P.quotientMap (Sum.inr (gε (gε.symm y))) at hh
    rw [gε.apply_symm_apply] at hh
    change e0 (ρ0 (H.symm (P.quotientMap (Sum.inr y)))) = _
    rw [← hh, H.symm_apply_apply]
    exact hmodel.2.2.1 (gε.symm y)
  let Q := ConnectedClosedOrientedManifold.pullback M H0
  let ρ : P.QuotientSpace ≃ₜ Q.Carrier := Homeomorph.refl P.QuotientSpace
  let e : Q.Carrier ≃ₘ⟮𝓡 3, 𝓡 3⟯ M.Carrier :=
    (ConnectedClosedOrientedManifold.pullbackOrientedDiffeomorph M H0).val
  have hpoint (x : K.Carrier ⊕ S.Carrier) :
      e (ρ (P.quotientMap x)) = markedRestorationFold K S g M φ ι ε x := by
    cases x with
    | inl x => exact hleft x
    | inr y => exact hright y
  have hmap : (ρ ∘ P.quotientMap) = e.symm ∘ markedRestorationFold K S g M φ ι ε := by
    funext x
    exact (e.symm_apply_apply (ρ (P.quotientMap x))).symm.trans (congrArg e.symm (hpoint x))
  refine ⟨ε, hrev, Q, ρ, e,
    (ConnectedClosedOrientedManifold.pullbackOrientedDiffeomorph M H0).property, ?_,
    hleft, hright, markedRestorationMatching_meridian ψ ε⟩
  rw [hmap]
  exact e.symm.contMDiff.comp (markedRestorationFold_smooth K S hK hS g M φ h3 ι hι ε)

set_option backward.isDefEq.respectTransparency false in
include hz h3 hι hr hΓ hb hbij hO in
theorem exists_rawMarkedRegularFibreRestoration
    (G : RawGraphPresentation (NoCuts.carrier M)) :
    ∃ ε : Bool,
    let f := markedRestorationMatching ψ ε
    ∃ hrev : ReversesBoundaryOrientation (withBoundarySum K S hK hS)
      (boundaryPortLeftCollar K S hK hS Γ)
      (fun p => boundaryPortRightCollar K S hK hS E 0 (f p.1, p.2)),
    let P := boundaryPortPairing K S hK hS Γ E f hrev
    ∃ (Q : ConnectedClosedOrientedManifold.{u} 3)
      (ρ : P.QuotientSpace ≃ₜ Q.Carrier)
      (e : Q.Carrier ≃ₘ⟮𝓡 3, 𝓡 3⟯ M.Carrier),
      e.preservesOrientation Q.orientation M.orientation ∧
      Nonempty (RawGraphPresentation (NoCuts.carrier Q)) ∧
      ContMDiff (withBoundarySum K S hK hS).model (𝓡 3) ∞ (ρ ∘ P.quotientMap) ∧
      (∀ x : K.Carrier, e (ρ (P.quotientMap (Sum.inl x))) = ι x) ∧
      (∀ y : S.Carrier, e (ρ (P.quotientMap (Sum.inr y))) =
        regularFibreRestorationFill M φ ((markedRestorationSolidMap S g ε).symm y)) ∧
      ∀ θ : Circle, f (θ, 1) = ψ (θ, 1) := by
  obtain ⟨ε, hrev, Q, ρ, e, he, hq, hl, hr, hm⟩ :=
    exists_markedRegularFibreRestoration K S hK hS Γ E g ψ hz M φ h3 ι hι hr hΓ hb hbij hO
  exact ⟨ε, hrev, Q, ρ, e, he,
    ⟨G.transport e.symm (Diffeomorph.preservesOrientation_symm he)⟩, hq, hl, hr, hm⟩

def markedSolidBoundary : BoundaryTori S 1 :=
  ((regularFibreRestorationBoundary (solidAtlas.orientation planeCircleOrientation)).transport
    (W' := S) g).reparam (Function.const (Fin 1) ψ.symm)

omit [Nonempty S.Carrier] in
theorem markedSolidBoundary_collar (p : Torus × EuclideanHalfSpace 1) :
    (markedSolidBoundary S g ψ).collar 0 p = g (solidCollar 1 (ψ.symm p.1, p.2)) := rfl

omit [Nonempty S.Carrier] in
theorem markedSolidBoundary_zero (t : Torus) :
    g (solidCollar 1 (t, halfZero)) = (markedSolidBoundary S g ψ).torusMap 0 (ψ t) := by
  change g (solidCollar 1 (t, halfZero)) = g (solidCollar 1 (ψ.symm (ψ t), halfZero))
  rw [ψ.symm_apply_apply]

set_option backward.isDefEq.respectTransparency false in
include h3 hι hr hΓ hb hbij hO in
theorem exists_modelMarkedRegularFibreRestoration
    (G : RawGraphPresentation (NoCuts.carrier M)) :
    let E := markedSolidBoundary S g ψ
    ∃ ε : Bool,
    let f := markedRestorationMatching ψ ε
    ∃ hrev : ReversesBoundaryOrientation (withBoundarySum K S hK hS)
      (boundaryPortLeftCollar K S hK hS Γ)
      (fun p => boundaryPortRightCollar K S hK hS E 0 (f p.1, p.2)),
    let P := boundaryPortPairing K S hK hS Γ E f hrev
    ∃ (Q : ConnectedClosedOrientedManifold.{u} 3)
      (ρ : P.QuotientSpace ≃ₜ Q.Carrier)
      (e : Q.Carrier ≃ₘ⟮𝓡 3, 𝓡 3⟯ M.Carrier),
      e.preservesOrientation Q.orientation M.orientation ∧
      Nonempty (RawGraphPresentation (NoCuts.carrier Q)) ∧
      ContMDiff (withBoundarySum K S hK hS).model (𝓡 3) ∞ (ρ ∘ P.quotientMap) ∧
      (∀ x : K.Carrier, e (ρ (P.quotientMap (Sum.inl x))) = ι x) ∧
      (∀ y : S.Carrier, e (ρ (P.quotientMap (Sum.inr y))) =
        regularFibreRestorationFill M φ ((markedRestorationSolidMap S g ε).symm y)) ∧
      ∀ θ : Circle, f (θ, 1) = ψ (θ, 1) :=
  exists_rawMarkedRegularFibreRestoration K S hK hS Γ (markedSolidBoundary S g ψ) g ψ
    (markedSolidBoundary_zero S g ψ) M φ h3 ι hι hr hΓ hb hbij hO G

end GC.GraphManifold
