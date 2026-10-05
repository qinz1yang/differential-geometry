import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.BoundaryPortPairing
import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.SphereCutFactorMaps
import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Seifert.CarrierSurgeryTopology
import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Seifert.FillingProductCharts

/-!
Two physical one-port quotients retain the actual spherical factor maps into the same target.
-/

set_option autoImplicit false

noncomputable section

open Set Function Topology
open DifferentialGeometry DifferentialGeometry.Topology GC.Endpoint GC.Seifert
open GC.Endpoint.CompactCarrier GC.GraphManifold.TorusPairing
open scoped Manifold ContDiff Topology

universe u

namespace GC.GraphManifold

private theorem doublePort_relation {C D : CompactCarrier.{u}}
    {hC : C.kind = .withBoundary} {hD : D.kind = .withBoundary}
    [Nonempty C.Carrier] [Nonempty D.Carrier] {n : ℕ}
    {E : BoundaryTori C 1} {F : BoundaryTori D (n + 1)}
    {f : Torus ≃ₘ⟮torusModel, torusModel⟯ Torus}
    {hf : ReversesBoundaryOrientation (withBoundarySum C D hC hD)
      (boundaryPortLeftCollar C D hC hD E)
      (fun p => boundaryPortRightCollar C D hC hD F 0 (f p.1, p.2))}
    {x y : C.Carrier ⊕ D.Carrier} :
    (boundaryPortPairing C D hC hD E F f hf).quotientMap x =
      (boundaryPortPairing C D hC hD E F f hf).quotientMap y ↔
      x = y ∨ ∃ t : Torus,
        (x = Sum.inl (E.torusMap 0 t) ∧ y = Sum.inr (F.torusMap 0 (f t))) ∨
        (y = Sum.inl (E.torusMap 0 t) ∧ x = Sum.inr (F.torusMap 0 (f t))) := by
  erw [TorusPairing.surgery_quotientMap_eq_iff, GC.Seifert.TorusPairing.rel_iff_params]
  constructor
  · rintro (he | ⟨j, t, he⟩)
    · exact Or.inl he
    · exact Or.inr ⟨t, he⟩
  · rintro (he | ⟨t, he⟩)
    · exact Or.inl he
    · exact Or.inr ⟨⟨0, Nat.one_pos⟩, t, he⟩

private theorem doublePort_left {C D : CompactCarrier.{u}}
    {hC : C.kind = .withBoundary} {hD : D.kind = .withBoundary}
    [Nonempty C.Carrier] [Nonempty D.Carrier] {n : ℕ}
    {E : BoundaryTori C 1} {F : BoundaryTori D (n + 1)}
    {f : Torus ≃ₘ⟮torusModel, torusModel⟯ Torus}
    {hf : ReversesBoundaryOrientation (withBoundarySum C D hC hD)
      (boundaryPortLeftCollar C D hC hD E)
      (fun p => boundaryPortRightCollar C D hC hD F 0 (f p.1, p.2))}
    {x y : C.Carrier} :
    (boundaryPortPairing C D hC hD E F f hf).quotientMap (Sum.inl x) =
      (boundaryPortPairing C D hC hD E F f hf).quotientMap (Sum.inl y) ↔ x = y := by
  erw [doublePort_relation]
  simp

private theorem doublePort_right {C D : CompactCarrier.{u}}
    {hC : C.kind = .withBoundary} {hD : D.kind = .withBoundary}
    [Nonempty C.Carrier] [Nonempty D.Carrier] {n : ℕ}
    {E : BoundaryTori C 1} {F : BoundaryTori D (n + 1)}
    {f : Torus ≃ₘ⟮torusModel, torusModel⟯ Torus}
    {hf : ReversesBoundaryOrientation (withBoundarySum C D hC hD)
      (boundaryPortLeftCollar C D hC hD E)
      (fun p => boundaryPortRightCollar C D hC hD F 0 (f p.1, p.2))}
    {x y : D.Carrier} :
    (boundaryPortPairing C D hC hD E F f hf).quotientMap (Sum.inr x) =
      (boundaryPortPairing C D hC hD E F f hf).quotientMap (Sum.inr y) ↔ x = y := by
  erw [doublePort_relation]
  simp

private theorem doublePort_cross {C D : CompactCarrier.{u}}
    {hC : C.kind = .withBoundary} {hD : D.kind = .withBoundary}
    [Nonempty C.Carrier] [Nonempty D.Carrier] {n : ℕ}
    {E : BoundaryTori C 1} {F : BoundaryTori D (n + 1)}
    {f : Torus ≃ₘ⟮torusModel, torusModel⟯ Torus}
    {hf : ReversesBoundaryOrientation (withBoundarySum C D hC hD)
      (boundaryPortLeftCollar C D hC hD E)
      (fun p => boundaryPortRightCollar C D hC hD F 0 (f p.1, p.2))}
    {x : C.Carrier} {y : D.Carrier} :
    (boundaryPortPairing C D hC hD E F f hf).quotientMap (Sum.inl x) =
      (boundaryPortPairing C D hC hD E F f hf).quotientMap (Sum.inr y) ↔
      ∃ t : Torus, x = E.torusMap 0 t ∧ y = F.torusMap 0 (f t) := by
  erw [doublePort_relation]
  simp

variable (C0 C1 W X0 X1 N : CompactCarrier.{u})
  (hC0 : C0.kind = .withBoundary) (hC1 : C1.kind = .withBoundary)
  (hW : W.kind = .withBoundary) (hX0 : X0.kind = .withBoundary)
  (hX1 : X1.kind = .withBoundary) (hN : N.kind = .withBoundary)
  [Nonempty C0.Carrier] [Nonempty C1.Carrier] [Nonempty W.Carrier]
  [Nonempty X0.Carrier] [Nonempty X1.Carrier] [Nonempty N.Carrier]
  (Γ0 : BoundaryTori C0 1) (Γ1 : BoundaryTori C1 1) (ΓR : BoundaryTori C1 1)
  (hΓ1 : ∀ t, Γ1.torusMap 0 t = ΓR.torusMap 0 t) (EW : BoundaryTori W 2)
  (F0 : BoundaryTori X0 1) (F1 : BoundaryTori X1 1)
  (u0 : C(X0.Carrier, W.Carrier)) (u1 : C(X1.Carrier, W.Carrier))
  (f0 : Torus ≃ₘ⟮torusModel, torusModel⟯ Torus)
  (hrFirst : ReversesBoundaryOrientation (withBoundarySum C0 W hC0 hW)
    (boundaryPortLeftCollar C0 W hC0 hW Γ0)
    (fun p => boundaryPortRightCollar C0 W hC0 hW EW 0 (f0 p.1, p.2)))
variable (eFirst : Quotient (boundaryPortPairing C0 W hC0 hW Γ0 EW f0 hrFirst).gluing.setoid ≃ₜ
  N.Carrier) (EN : BoundaryTori N 1)
  (hENzero : ∀ t, EN.torusMap 0 t = eFirst ((boundaryPortPairing C0 W hC0 hW Γ0 EW f0
    hrFirst).quotientMap (Sum.inr (EW.torusMap 1 t))))
  (g : Torus ≃ₘ⟮torusModel, torusModel⟯ Torus)
  (hrSecond : ReversesBoundaryOrientation (withBoundarySum N C1 hN hC1)
    (boundaryPortLeftCollar N C1 hN hC1 EN)
    (fun p => boundaryPortRightCollar N C1 hN hC1 Γ1 0 (g p.1, p.2)))
variable (Q : ConnectedClosedOrientedManifold.{u} 3)
  (eSecond : Quotient (boundaryPortPairing N C1 hN hC1 EN Γ1 g hrSecond).gluing.setoid ≃ₜ Q.Carrier)
  (hrL : ReversesBoundaryOrientation (withBoundarySum C0 X0 hC0 hX0)
    (boundaryPortLeftCollar C0 X0 hC0 hX0 Γ0)
    (fun p => boundaryPortRightCollar C0 X0 hC0 hX0 F0 0 (f0 p.1, p.2)))
  (hrR : ReversesBoundaryOrientation (withBoundarySum C1 X1 hC1 hX1)
    (boundaryPortLeftCollar C1 X1 hC1 hX1 ΓR)
    (fun p => boundaryPortRightCollar C1 X1 hC1 hX1 F1 0 (g.symm p.1, p.2)))
variable (hu0 : Injective u0) (hu1 : Injective u1)
  (hp0 : ∀ t, u0 (F0.torusMap 0 t) = EW.torusMap 0 t)
  (hp1 : ∀ t, u1 (F1.torusMap 0 t) = EW.torusMap 1 t)
  (hx0 : ∀ t, EW.torusMap 0 t ∉ range u1)
  (hx1 : ∀ t, EW.torusMap 1 t ∉ range u0)
  (z0 : ClosureSphere.{u} → X0.Carrier) (z1 : ClosureSphere.{u} → X1.Carrier)
  (hcross : ∀ x y, u0 x = u1 y ↔ ∃ z, x = z0 z ∧ y = z1 z)
  (hcover : ∀ w, (∃ x, u0 x = w) ∨ ∃ y, u1 y = w)

def doubleBoundaryLeftCutMap : C(C0.Carrier ⊕ X0.Carrier, Q.Carrier) where
  toFun x := eSecond ((boundaryPortPairing N C1 hN hC1 EN Γ1 g hrSecond).quotientMap
    (Sum.inl (eFirst ((boundaryPortPairing C0 W hC0 hW Γ0 EW f0 hrFirst).quotientMap (Sum.map
      id u0 x)))))
  continuous_toFun := eSecond.continuous.comp ((boundaryPortPairing N C1 hN hC1 EN Γ1 g
    hrSecond).quotientMap.continuous.comp
    (continuous_inl.comp (eFirst.continuous.comp ((boundaryPortPairing C0 W hC0 hW Γ0 EW f0
      hrFirst).quotientMap.continuous.comp
      (continuous_id.sumMap u0.continuous)))))

def doubleBoundaryRightCutMap : C(C1.Carrier ⊕ X1.Carrier, Q.Carrier) where
  toFun := Sum.elim
    (fun k => eSecond ((boundaryPortPairing N C1 hN hC1 EN Γ1 g hrSecond).quotientMap (Sum.inr k)))
    (fun y => eSecond ((boundaryPortPairing N C1 hN hC1 EN Γ1 g hrSecond).quotientMap
      (Sum.inl (eFirst ((boundaryPortPairing C0 W hC0 hW Γ0 EW f0 hrFirst).quotientMap (Sum.inr
        (u1 y)))))))
  continuous_toFun :=
    (eSecond.continuous.comp ((boundaryPortPairing N C1 hN hC1 EN Γ1 g
      hrSecond).quotientMap.continuous.comp continuous_inr)).sumElim
      (eSecond.continuous.comp ((boundaryPortPairing N C1 hN hC1 EN Γ1 g
        hrSecond).quotientMap.continuous.comp
        (continuous_inl.comp (eFirst.continuous.comp ((boundaryPortPairing C0 W hC0 hW Γ0 EW f0
          hrFirst).quotientMap.continuous.comp
          (continuous_inr.comp u1.continuous))))))

local notation "leftCut" =>
  GC.GraphManifold.doubleBoundaryLeftCutMap C0 C1 W X0 N hC0 hC1 hW hN Γ0 Γ1 EW u0 f0 hrFirst
    eFirst EN g hrSecond
    Q eSecond
local notation "rightCut" =>
  GC.GraphManifold.doubleBoundaryRightCutMap C0 C1 W X1 N hC0 hC1 hW hN Γ0 Γ1 EW u1 f0 hrFirst
    eFirst EN g hrSecond
    Q eSecond

variable {C0} {C1} {W} {X0} {X1} {N} {hC0} {hC1}
  {hW} {hX0} {hX1} {hN} {Γ0} {Γ1} {ΓR} {hΓ1}
  {EW} {F0} {F1} {u0} {u1} {f0} {hrFirst} {eFirst}
  {EN} {hENzero} {g} {hrSecond} {Q} {eSecond} {hrL} {hrR}
  {hu0} {hu1} {hp0} {hp1} {hx0} {hx1} {z0} {z1}
  {hcross} {hcover}

include hu0 hp0 in
private theorem doubleLeft_relation {x y : C0.Carrier ⊕ X0.Carrier} :
    (boundaryPortPairing C0 W hC0 hW Γ0 EW f0 hrFirst).quotientMap (Sum.map id u0 x) =
      (boundaryPortPairing C0 W hC0 hW Γ0 EW f0 hrFirst).quotientMap (Sum.map id u0 y) ↔
      (boundaryPortPairing C0 X0 hC0 hX0 Γ0 F0 f0 hrL).quotientMap x = (boundaryPortPairing C0
        X0 hC0 hX0 Γ0 F0 f0 hrL).quotientMap y := by
  erw [doublePort_relation, doublePort_relation]
  have hinj : Injective (Sum.map (id : C0.Carrier → C0.Carrier) u0) :=
    Function.Injective.sumMap Function.injective_id hu0
  constructor
  · rintro (he | ⟨t, he | he⟩)
    · exact Or.inl (hinj he)
    · refine Or.inr ⟨t, Or.inl ⟨hinj he.1, ?_⟩⟩
      apply hinj
      exact he.2.trans (congrArg Sum.inr (hp0 (f0 t)).symm)
    · refine Or.inr ⟨t, Or.inr ⟨hinj he.1, ?_⟩⟩
      apply hinj
      exact he.2.trans (congrArg Sum.inr (hp0 (f0 t)).symm)
  · rintro (rfl | ⟨t, he | he⟩)
    · exact Or.inl rfl
    · obtain ⟨rfl, rfl⟩ := he
      exact Or.inr ⟨t, Or.inl ⟨rfl, congrArg Sum.inr (hp0 (f0 t))⟩⟩
    · obtain ⟨rfl, rfl⟩ := he
      exact Or.inr ⟨t, Or.inr ⟨rfl, congrArg Sum.inr (hp0 (f0 t))⟩⟩

include hu0 hp0 in
private theorem doubleLeft_kernel {x y : C0.Carrier ⊕ X0.Carrier} :
    leftCut x = leftCut y ↔ (boundaryPortPairing C0 X0 hC0 hX0 Γ0 F0 f0 hrL).quotientMap x =
      (boundaryPortPairing C0 X0 hC0 hX0 Γ0 F0 f0 hrL).quotientMap y := by
  change eSecond ((boundaryPortPairing N C1 hN hC1 EN Γ1 g hrSecond).quotientMap
    (Sum.inl (eFirst ((boundaryPortPairing C0 W hC0 hW Γ0 EW f0 hrFirst).quotientMap (Sum.map
      id u0 x))))) =
    eSecond ((boundaryPortPairing N C1 hN hC1 EN Γ1 g hrSecond).quotientMap
      (Sum.inl (eFirst ((boundaryPortPairing C0 W hC0 hW Γ0 EW f0 hrFirst).quotientMap (Sum.map
        id u0 y))))) ↔ _
  erw [eSecond.injective.eq_iff, doublePort_left, eFirst.injective.eq_iff]
  exact doubleLeft_relation (hu0 := hu0) (hp0 := hp0)

omit [Nonempty X1.Carrier] in
include hu1 hp1 hENzero hΓ1 in
private theorem doubleRight_cross {k : C1.Carrier} {y : X1.Carrier} :
    rightCut (Sum.inl k) = rightCut (Sum.inr y) ↔
      ∃ t : Torus, k = ΓR.torusMap 0 t ∧ y = F1.torusMap 0 (g.symm t) := by
  change eSecond ((boundaryPortPairing N C1 hN hC1 EN Γ1 g hrSecond).quotientMap (Sum.inr k)) =
    eSecond ((boundaryPortPairing N C1 hN hC1 EN Γ1 g hrSecond).quotientMap
      (Sum.inl (eFirst ((boundaryPortPairing C0 W hC0 hW Γ0 EW f0 hrFirst).quotientMap (Sum.inr
        (u1 y)))))) ↔ _
  constructor
  · intro he
    obtain ⟨t, ht, hk⟩ := (doublePort_cross (hC := hN) (hD := hC1) (E := EN) (F := Γ1)
          (f := g) (hf := hrSecond) (x := _) (y := k)).mp
      (eSecond.injective he).symm
    have hw : u1 y = EW.torusMap 1 t := by
      apply (doublePort_right (hC := hC0) (hD := hW) (E := Γ0) (F := EW)
          (f := f0) (hf := hrFirst) (x := _) (y := _)).mp
      apply eFirst.injective
      exact ht.trans (hENzero t)
    have hy : y = F1.torusMap 0 t := hu1 (hw.trans (hp1 t).symm)
    refine ⟨g t, hk.trans (hΓ1 (g t)), ?_⟩
    simpa only [g.symm_apply_apply] using hy
  · rintro ⟨t, rfl, rfl⟩
    apply eSecond.injective.eq_iff.mpr
    apply Eq.symm
    apply (doublePort_cross (hC := hN) (hD := hC1) (E := EN) (F := Γ1)
          (f := g) (hf := hrSecond) (x := _) (y := _)).mpr
    refine ⟨g.symm t, ?_, ?_⟩
    · exact (congrArg (fun w => eFirst ((boundaryPortPairing C0 W hC0 hW Γ0 EW f0
      hrFirst).quotientMap (Sum.inr w)))
        (hp1 (g.symm t))).trans (hENzero (g.symm t)).symm
    · exact (hΓ1 t).symm.trans (congrArg (Γ1.torusMap 0) (g.apply_symm_apply t).symm)

include hu1 hp1 hENzero hΓ1 in
private theorem doubleRight_kernel {x y : C1.Carrier ⊕ X1.Carrier} :
    rightCut x = rightCut y ↔ (boundaryPortPairing C1 X1 hC1 hX1 ΓR F1 g.symm hrR).quotientMap
      x = (boundaryPortPairing C1 X1 hC1 hX1 ΓR F1 g.symm hrR).quotientMap y := by
  cases x with
  | inl k =>
    cases y with
    | inl l =>
      change eSecond ((boundaryPortPairing N C1 hN hC1 EN Γ1 g hrSecond).quotientMap (Sum.inr k)) =
        eSecond ((boundaryPortPairing N C1 hN hC1 EN Γ1 g hrSecond).quotientMap (Sum.inr l)) ↔ _
      erw [eSecond.injective.eq_iff, doublePort_right, doublePort_left]
    | inr y =>
      erw [doubleRight_cross (hu1 := hu1) (hp1 := hp1) (hENzero := hENzero) (hΓ1 := hΓ1),
        doublePort_cross]
  | inr x =>
    cases y with
    | inl k =>
      have hc : rightCut (Sum.inl k) = rightCut (Sum.inr x) ↔
          (boundaryPortPairing C1 X1 hC1 hX1 ΓR F1 g.symm hrR).quotientMap (Sum.inl k) =
            (boundaryPortPairing C1 X1 hC1 hX1 ΓR F1 g.symm hrR).quotientMap (Sum.inr x) := by
        erw [doubleRight_cross (hu1 := hu1) (hp1 := hp1) (hENzero := hENzero) (hΓ1 := hΓ1),
          doublePort_cross]
      exact (eq_comm.trans hc).trans eq_comm
    | inr y =>
      change eSecond ((boundaryPortPairing N C1 hN hC1 EN Γ1 g hrSecond).quotientMap
        (Sum.inl (eFirst ((boundaryPortPairing C0 W hC0 hW Γ0 EW f0 hrFirst).quotientMap
          (Sum.inr (u1 x)))))) =
        eSecond ((boundaryPortPairing N C1 hN hC1 EN Γ1 g hrSecond).quotientMap
          (Sum.inl (eFirst ((boundaryPortPairing C0 W hC0 hW Γ0 EW f0 hrFirst).quotientMap
            (Sum.inr (u1 y)))))) ↔ _
      erw [eSecond.injective.eq_iff, doublePort_left, eFirst.injective.eq_iff,
        doublePort_right, hu1.eq_iff, doublePort_right]

omit [Nonempty X0.Carrier] [Nonempty X1.Carrier] in
include hp0 hx0 hx1 hENzero hcross in
private theorem doubleCut_cross {x : C0.Carrier ⊕ X0.Carrier}
    {y : C1.Carrier ⊕ X1.Carrier} :
    leftCut x = rightCut y ↔ ∃ z : ClosureSphere.{u},
      x = Sum.inr (z0 z) ∧ y = Sum.inr (z1 z) := by
  cases x with
  | inl k =>
    cases y with
    | inl l =>
      constructor
      · intro he
        obtain ⟨t, ht, htl⟩ := (doublePort_cross (hC := hN) (hD := hC1) (E := EN) (F := Γ1)
          (f := g) (hf := hrSecond) (x := _) (y := l)).mp
          (eSecond.injective he)
        have hi :
            (boundaryPortPairing C0 W hC0 hW Γ0 EW f0 hrFirst).quotientMap (Sum.inl k) =
              (boundaryPortPairing C0 W hC0 hW Γ0 EW f0 hrFirst).quotientMap
                (Sum.inr (EW.torusMap 1 t)) := eFirst.injective (ht.trans (hENzero t))
        obtain ⟨v, hvk, hvw⟩ := (doublePort_cross (hC := hC0) (hD := hW) (E := Γ0) (F := EW)
          (f := f0) (hf := hrFirst) (x := k) (y := _)).mp hi
        exact False.elim (hx1 t ⟨F0.torusMap 0 (f0 v), (hp0 (f0 v)).trans hvw.symm⟩)
      · rintro ⟨z, hx, hy⟩
        exact False.elim (Sum.inl_ne_inr hx)
    | inr y =>
      constructor
      · intro he
        have hi :
            (boundaryPortPairing C0 W hC0 hW Γ0 EW f0 hrFirst).quotientMap (Sum.inl k) =
              (boundaryPortPairing C0 W hC0 hW Γ0 EW f0 hrFirst).quotientMap
                (Sum.inr (u1 y)) := by
          apply eFirst.injective
          exact (doublePort_left (hC := hN) (hD := hC1) (E := EN) (F := Γ1)
          (f := g) (hf := hrSecond) (x := _) (y := _)).mp (eSecond.injective he)
        obtain ⟨t, htk, hty⟩ := (doublePort_cross (hC := hC0) (hD := hW) (E := Γ0) (F := EW)
          (f := f0) (hf := hrFirst) (x := k) (y := _)).mp hi
        exact False.elim (hx0 (f0 t) ⟨y, hty⟩)
      · rintro ⟨z, hx, hy⟩
        exact False.elim (Sum.inl_ne_inr hx)
  | inr x =>
    cases y with
    | inl l =>
      constructor
      · intro he
        obtain ⟨t, ht, htl⟩ := (doublePort_cross (hC := hN) (hD := hC1) (E := EN) (F := Γ1)
          (f := g) (hf := hrSecond) (x := _) (y := l)).mp
          (eSecond.injective he)
        have hw : u0 x = EW.torusMap 1 t := by
          apply (doublePort_right (hC := hC0) (hD := hW) (E := Γ0) (F := EW)
          (f := f0) (hf := hrFirst) (x := _) (y := _)).mp
          exact eFirst.injective (ht.trans (hENzero t))
        exact False.elim (hx1 t ⟨x, hw⟩)
      · rintro ⟨z, hx, hy⟩
        exact False.elim (Sum.inl_ne_inr hy)
    | inr y =>
      change eSecond ((boundaryPortPairing N C1 hN hC1 EN Γ1 g hrSecond).quotientMap
        (Sum.inl (eFirst
          ((boundaryPortPairing C0 W hC0 hW Γ0 EW f0 hrFirst).quotientMap (Sum.inr (u0 x)))))) =
        eSecond ((boundaryPortPairing N C1 hN hC1 EN Γ1 g hrSecond).quotientMap
          (Sum.inl (eFirst
            ((boundaryPortPairing C0 W hC0 hW Γ0 EW f0 hrFirst).quotientMap
              (Sum.inr (u1 y)))))) ↔ _
      erw [eSecond.injective.eq_iff, doublePort_left, eFirst.injective.eq_iff,
        doublePort_right, hcross]
      simp only [Sum.inr.injEq]

variable (C0) (C1) (W) (X0) (X1) (N) (hC0) (hC1)
  (hW) (hX0) (hX1) (hN) (Γ0) (Γ1) (ΓR) (hΓ1)
  (EW) (F0) (F1) (u0) (u1) (f0) (hrFirst) (eFirst)
  (EN) (hENzero) (g) (hrSecond) (Q) (eSecond) (hrL) (hrR)
  (hu0) (hu1) (hp0) (hp1) (hx0) (hx1) (z0) (z1)
  (hcross) (hcover)

include hu0 hp0 in
def doubleBoundaryLeftFactorMap : C((boundaryPortPairing C0 X0 hC0 hX0 Γ0 F0 f0
  hrL).QuotientSpace, Q.Carrier) where
  toFun := Quotient.lift leftCut (fun x y hxy =>
    ((doubleLeft_kernel
    (C0 := C0) (C1 := C1) (W := W) (X0 := X0)
    (N := N) (hC0 := hC0) (hC1 := hC1) (hW := hW)
    (hX0 := hX0) (hN := hN) (Γ0 := Γ0) (Γ1 := Γ1)
    (EW := EW) (F0 := F0) (u0 := u0) (f0 := f0)
    (hrFirst := hrFirst) (eFirst := eFirst) (EN := EN) (g := g)
    (hrSecond := hrSecond) (Q := Q) (eSecond := eSecond) (hrL := hrL)
    (hu0 := hu0) (hp0 := hp0) (x := x) (y := y))).mpr (Quotient.sound hxy))
  continuous_toFun := (leftCut).continuous.quotient_lift (fun x y hxy =>
    ((doubleLeft_kernel
    (C0 := C0) (C1 := C1) (W := W) (X0 := X0)
    (N := N) (hC0 := hC0) (hC1 := hC1) (hW := hW)
    (hX0 := hX0) (hN := hN) (Γ0 := Γ0) (Γ1 := Γ1)
    (EW := EW) (F0 := F0) (u0 := u0) (f0 := f0)
    (hrFirst := hrFirst) (eFirst := eFirst) (EN := EN) (g := g)
    (hrSecond := hrSecond) (Q := Q) (eSecond := eSecond) (hrL := hrL)
    (hu0 := hu0) (hp0 := hp0) (x := x) (y := y))).mpr (Quotient.sound hxy))

include hu1 hp1 hENzero hΓ1 in
def doubleBoundaryRightFactorMap : C((boundaryPortPairing C1 X1 hC1 hX1 ΓR F1 g.symm
  hrR).QuotientSpace, Q.Carrier) where
  toFun := Quotient.lift rightCut (fun x y hxy =>
    ((doubleRight_kernel
    (C0 := C0) (C1 := C1) (W := W) (X1 := X1)
    (N := N) (hC0 := hC0) (hC1 := hC1) (hW := hW)
    (hX1 := hX1) (hN := hN) (Γ0 := Γ0) (Γ1 := Γ1)
    (ΓR := ΓR) (hΓ1 := hΓ1) (EW := EW) (F1 := F1)
    (u1 := u1) (f0 := f0) (hrFirst := hrFirst) (eFirst := eFirst)
    (EN := EN) (hENzero := hENzero) (g := g) (hrSecond := hrSecond)
    (Q := Q) (eSecond := eSecond) (hrR := hrR) (hu1 := hu1)
    (hp1 := hp1) (x := x) (y := y))).mpr (Quotient.sound hxy))
  continuous_toFun := (rightCut).continuous.quotient_lift (fun x y hxy =>
    ((doubleRight_kernel
    (C0 := C0) (C1 := C1) (W := W) (X1 := X1)
    (N := N) (hC0 := hC0) (hC1 := hC1) (hW := hW)
    (hX1 := hX1) (hN := hN) (Γ0 := Γ0) (Γ1 := Γ1)
    (ΓR := ΓR) (hΓ1 := hΓ1) (EW := EW) (F1 := F1)
    (u1 := u1) (f0 := f0) (hrFirst := hrFirst) (eFirst := eFirst)
    (EN := EN) (hENzero := hENzero) (g := g) (hrSecond := hrSecond)
    (Q := Q) (eSecond := eSecond) (hrR := hrR) (hu1 := hu1)
    (hp1 := hp1) (x := x) (y := y))).mpr (Quotient.sound hxy))

local notation "FL" => doubleBoundaryLeftFactorMap
    (C0 := C0) (C1 := C1) (W := W) (X0 := X0)
    (N := N) (hC0 := hC0) (hC1 := hC1) (hW := hW)
    (hX0 := hX0) (hN := hN) (Γ0 := Γ0) (Γ1 := Γ1)
    (EW := EW) (F0 := F0) (u0 := u0) (f0 := f0)
    (hrFirst := hrFirst) (eFirst := eFirst) (EN := EN) (g := g)
    (hrSecond := hrSecond) (Q := Q) (eSecond := eSecond) (hrL := hrL)
    (hu0 := hu0) (hp0 := hp0)
local notation "FR" => doubleBoundaryRightFactorMap
    (C0 := C0) (C1 := C1) (W := W) (X1 := X1)
    (N := N) (hC0 := hC0) (hC1 := hC1) (hW := hW)
    (hX1 := hX1) (hN := hN) (Γ0 := Γ0) (Γ1 := Γ1)
    (ΓR := ΓR) (hΓ1 := hΓ1) (EW := EW) (F1 := F1)
    (u1 := u1) (f0 := f0) (hrFirst := hrFirst) (eFirst := eFirst)
    (EN := EN) (hENzero := hENzero) (g := g) (hrSecond := hrSecond)
    (Q := Q) (eSecond := eSecond) (hrR := hrR) (hu1 := hu1)
    (hp1 := hp1)

include hu0 hp0 in
theorem doubleBoundaryLeftFactorMap_injective : Injective FL := by
  intro l r he
  obtain ⟨x, rfl⟩ := Quotient.mk''_surjective l
  obtain ⟨y, rfl⟩ := Quotient.mk''_surjective r
  exact ((doubleLeft_kernel
    (C0 := C0) (C1 := C1) (W := W) (X0 := X0)
    (N := N) (hC0 := hC0) (hC1 := hC1) (hW := hW)
    (hX0 := hX0) (hN := hN) (Γ0 := Γ0) (Γ1 := Γ1)
    (EW := EW) (F0 := F0) (u0 := u0) (f0 := f0)
    (hrFirst := hrFirst) (eFirst := eFirst) (EN := EN) (g := g)
    (hrSecond := hrSecond) (Q := Q) (eSecond := eSecond) (hrL := hrL)
    (hu0 := hu0) (hp0 := hp0) (x := x) (y := y))).mp he

include hu1 hp1 hENzero hΓ1 in
theorem doubleBoundaryRightFactorMap_injective : Injective FR := by
  intro l r he
  obtain ⟨x, rfl⟩ := Quotient.mk''_surjective l
  obtain ⟨y, rfl⟩ := Quotient.mk''_surjective r
  exact ((doubleRight_kernel
    (C0 := C0) (C1 := C1) (W := W) (X1 := X1)
    (N := N) (hC0 := hC0) (hC1 := hC1) (hW := hW)
    (hX1 := hX1) (hN := hN) (Γ0 := Γ0) (Γ1 := Γ1)
    (ΓR := ΓR) (hΓ1 := hΓ1) (EW := EW) (F1 := F1)
    (u1 := u1) (f0 := f0) (hrFirst := hrFirst) (eFirst := eFirst)
    (EN := EN) (hENzero := hENzero) (g := g) (hrSecond := hrSecond)
    (Q := Q) (eSecond := eSecond) (hrR := hrR) (hu1 := hu1)
    (hp1 := hp1) (x := x) (y := y))).mp he

variable {C0} {C1} {W} {X0} {X1} {N} {hC0} {hC1}
  {hW} {hX0} {hX1} {hN} {Γ0} {Γ1} {ΓR} {hΓ1}
  {EW} {F0} {F1} {u0} {u1} {f0} {hrFirst} {eFirst}
  {EN} {hENzero} {g} {hrSecond} {Q} {eSecond} {hrL} {hrR}
  {hu0} {hu1} {hp0} {hp1} {hx0} {hx1} {z0} {z1}
  {hcross} {hcover}

include hu0 hu1 hp0 hp1 hx0 hx1 hENzero hΓ1 hcross in
private theorem doubleFactors_cross {l : (boundaryPortPairing C0 X0 hC0 hX0 Γ0 F0 f0
  hrL).QuotientSpace}
    {r : (boundaryPortPairing C1 X1 hC1 hX1 ΓR F1 g.symm hrR).QuotientSpace} :
    (FL) l = (FR) r ↔ ∃ z : ClosureSphere.{u},
      l = (boundaryPortPairing C0 X0 hC0 hX0 Γ0 F0 f0 hrL).quotientMap (Sum.inr (z0 z)) ∧
        r = (boundaryPortPairing C1 X1 hC1 hX1 ΓR F1 g.symm hrR).quotientMap (Sum.inr (z1 z)) := by
  obtain ⟨x, rfl⟩ := Quotient.mk''_surjective l
  obtain ⟨y, rfl⟩ := Quotient.mk''_surjective r
  constructor
  · intro he
    obtain ⟨z, hx, hy⟩ := ((doubleCut_cross
    (C0 := C0) (C1 := C1) (W := W) (X0 := X0)
    (X1 := X1) (N := N) (hC0 := hC0) (hC1 := hC1)
    (hW := hW) (hN := hN) (Γ0 := Γ0) (Γ1 := Γ1)
    (EW := EW) (F0 := F0) (u0 := u0) (u1 := u1)
    (f0 := f0) (hrFirst := hrFirst) (eFirst := eFirst) (EN := EN)
    (hENzero := hENzero) (g := g) (hrSecond := hrSecond) (Q := Q)
    (eSecond := eSecond) (hp0 := hp0) (hx0 := hx0) (hx1 := hx1)
    (z0 := z0) (z1 := z1) (hcross := hcross) (x := x) (y := y))).mp he
    exact ⟨z, congrArg (boundaryPortPairing C0 X0 hC0 hX0 Γ0 F0 f0 hrL).quotientMap hx,
      congrArg (boundaryPortPairing C1 X1 hC1 hX1 ΓR F1 g.symm hrR).quotientMap hy⟩
  · rintro ⟨z, hx, hy⟩
    rw [hx, hy]
    exact ((doubleCut_cross
    (C0 := C0) (C1 := C1) (W := W) (X0 := X0)
    (X1 := X1) (N := N) (hC0 := hC0) (hC1 := hC1)
    (hW := hW) (hN := hN) (Γ0 := Γ0) (Γ1 := Γ1)
    (EW := EW) (F0 := F0) (u0 := u0) (u1 := u1)
    (f0 := f0) (hrFirst := hrFirst) (eFirst := eFirst) (EN := EN)
    (hENzero := hENzero) (g := g) (hrSecond := hrSecond) (Q := Q)
    (eSecond := eSecond) (hp0 := hp0) (hx0 := hx0) (hx1 := hx1)
    (z0 := z0) (z1 := z1) (hcross := hcross) (x := Sum.inr (z0 z))
      (y := Sum.inr (z1 z)))).mpr ⟨z, rfl, rfl⟩

include hu0 hu1 hp0 hp1 hENzero hΓ1 hcover in
private theorem doubleFactors_cover : range (FL) ∪ range (FR) = univ := by
  ext q
  constructor
  · intro hq
    exact mem_univ q
  · intro hq
    obtain ⟨v, rfl⟩ := eSecond.surjective q
    obtain ⟨p, rfl⟩ := Quotient.mk''_surjective v
    cases p with
    | inl n =>
      obtain ⟨w, rfl⟩ := eFirst.surjective n
      obtain ⟨p, rfl⟩ := Quotient.mk''_surjective w
      cases p with
      | inl k =>
        exact Or.inl ⟨(boundaryPortPairing C0 X0 hC0 hX0 Γ0 F0 f0 hrL).quotientMap (Sum.inl k), rfl⟩
      | inr w =>
        rcases hcover w with ⟨x, rfl⟩ | ⟨y, rfl⟩
        · exact Or.inl ⟨(boundaryPortPairing C0 X0 hC0 hX0 Γ0 F0 f0 hrL).quotientMap (Sum.inr
          x), rfl⟩
        · exact Or.inr ⟨(boundaryPortPairing C1 X1 hC1 hX1 ΓR F1 g.symm hrR).quotientMap
          (Sum.inr y), rfl⟩
    | inr k =>
      exact Or.inr ⟨(boundaryPortPairing C1 X1 hC1 hX1 ΓR F1 g.symm hrR).quotientMap (Sum.inl
        k), rfl⟩

variable (C0) (C1) (W) (X0) (X1) (N) (hC0) (hC1)
  (hW) (hX0) (hX1) (hN) (Γ0) (Γ1) (ΓR) (hΓ1)
  (EW) (F0) (F1) (u0) (u1) (f0) (hrFirst) (eFirst)
  (EN) (hENzero) (g) (hrSecond) (Q) (eSecond) (hrL) (hrR)
  (hu0) (hu1) (hp0) (hp1) (hx0) (hx1) (z0) (z1)
  (hcross) (hcover)

include hu0 hu1 hp0 hp1 hx0 hx1 hENzero hΓ1 hcross hcover in
theorem exists_doubleBoundaryFactors :
    ∃ (L : C((boundaryPortPairing C0 X0 hC0 hX0 Γ0 F0 f0 hrL).QuotientSpace, Q.Carrier))
      (R : C((boundaryPortPairing C1 X1 hC1 hX1 ΓR F1 g.symm hrR).QuotientSpace, Q.Carrier)),
      Injective L ∧ Injective R ∧
      (∀ k : C0.Carrier, L ((boundaryPortPairing C0 X0 hC0 hX0 Γ0 F0 f0 hrL).quotientMap
        (Sum.inl k)) =
        eSecond ((boundaryPortPairing N C1 hN hC1 EN Γ1 g hrSecond).quotientMap (Sum.inl
          (eFirst ((boundaryPortPairing C0 W hC0 hW Γ0 EW f0 hrFirst).quotientMap (Sum.inl k)))))) ∧
      (∀ x : X0.Carrier, L ((boundaryPortPairing C0 X0 hC0 hX0 Γ0 F0 f0 hrL).quotientMap
        (Sum.inr x)) =
        eSecond ((boundaryPortPairing N C1 hN hC1 EN Γ1 g hrSecond).quotientMap
          (Sum.inl (eFirst ((boundaryPortPairing C0 W hC0 hW Γ0 EW f0 hrFirst).quotientMap
            (Sum.inr (u0 x))))))) ∧
      (∀ k : C1.Carrier, R ((boundaryPortPairing C1 X1 hC1 hX1 ΓR F1 g.symm hrR).quotientMap
        (Sum.inl k)) =
        eSecond ((boundaryPortPairing N C1 hN hC1 EN Γ1 g hrSecond).quotientMap (Sum.inr k))) ∧
      (∀ y : X1.Carrier, R ((boundaryPortPairing C1 X1 hC1 hX1 ΓR F1 g.symm hrR).quotientMap
        (Sum.inr y)) =
        eSecond ((boundaryPortPairing N C1 hN hC1 EN Γ1 g hrSecond).quotientMap
          (Sum.inl (eFirst ((boundaryPortPairing C0 W hC0 hW Γ0 EW f0 hrFirst).quotientMap
            (Sum.inr (u1 y))))))) ∧
      (∀ l : (boundaryPortPairing C0 X0 hC0 hX0 Γ0 F0 f0 hrL).QuotientSpace, ∀ r :
        (boundaryPortPairing C1 X1 hC1 hX1 ΓR F1 g.symm hrR).QuotientSpace,
        L l = R r ↔ ∃ z : ClosureSphere.{u},
          l = (boundaryPortPairing C0 X0 hC0 hX0 Γ0 F0 f0 hrL).quotientMap (Sum.inr (z0 z)) ∧
            r = (boundaryPortPairing C1 X1 hC1 hX1 ΓR F1 g.symm hrR).quotientMap (Sum.inr (z1 z))) ∧
      range L ∪ range R = univ := by
  refine ⟨(FL), (FR), ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact doubleBoundaryLeftFactorMap_injective
      (C0 := C0) (C1 := C1) (W := W) (X0 := X0)
      (N := N) (hC0 := hC0) (hC1 := hC1) (hW := hW)
      (hX0 := hX0) (hN := hN) (Γ0 := Γ0) (Γ1 := Γ1)
      (EW := EW) (F0 := F0) (u0 := u0) (f0 := f0)
      (hrFirst := hrFirst) (eFirst := eFirst) (EN := EN) (g := g)
      (hrSecond := hrSecond) (Q := Q) (eSecond := eSecond) (hrL := hrL)
      (hu0 := hu0) (hp0 := hp0)
  · exact doubleBoundaryRightFactorMap_injective
      (C0 := C0) (C1 := C1) (W := W) (X1 := X1)
      (N := N) (hC0 := hC0) (hC1 := hC1) (hW := hW)
      (hX1 := hX1) (hN := hN) (Γ0 := Γ0) (Γ1 := Γ1)
      (ΓR := ΓR) (hΓ1 := hΓ1) (EW := EW) (F1 := F1)
      (u1 := u1) (f0 := f0) (hrFirst := hrFirst) (eFirst := eFirst)
      (EN := EN) (hENzero := hENzero) (g := g) (hrSecond := hrSecond)
      (Q := Q) (eSecond := eSecond) (hrR := hrR) (hu1 := hu1)
      (hp1 := hp1)
  · exact fun k => rfl
  · exact fun x => rfl
  · exact fun k => rfl
  · exact fun y => rfl
  · intro l r
    exact doubleFactors_cross
      (C0 := C0) (C1 := C1) (W := W) (X0 := X0)
      (X1 := X1) (N := N) (hC0 := hC0) (hC1 := hC1)
      (hW := hW) (hX0 := hX0) (hX1 := hX1) (hN := hN)
      (Γ0 := Γ0) (Γ1 := Γ1) (ΓR := ΓR) (hΓ1 := hΓ1)
      (EW := EW) (F0 := F0) (F1 := F1) (u0 := u0)
      (u1 := u1) (f0 := f0) (hrFirst := hrFirst) (eFirst := eFirst)
      (EN := EN) (hENzero := hENzero) (g := g) (hrSecond := hrSecond)
      (Q := Q) (eSecond := eSecond) (hrL := hrL) (hrR := hrR)
      (hu0 := hu0) (hu1 := hu1) (hp0 := hp0) (hp1 := hp1)
      (hx0 := hx0) (hx1 := hx1) (z0 := z0) (z1 := z1)
      (hcross := hcross) (l := l) (r := r)
  · exact doubleFactors_cover
      (C0 := C0) (C1 := C1) (W := W) (X0 := X0)
      (X1 := X1) (N := N) (hC0 := hC0) (hC1 := hC1)
      (hW := hW) (hX0 := hX0) (hX1 := hX1) (hN := hN)
      (Γ0 := Γ0) (Γ1 := Γ1) (ΓR := ΓR) (hΓ1 := hΓ1)
      (EW := EW) (F0 := F0) (F1 := F1) (u0 := u0)
      (u1 := u1) (f0 := f0) (hrFirst := hrFirst) (eFirst := eFirst)
      (EN := EN) (hENzero := hENzero) (g := g) (hrSecond := hrSecond)
      (Q := Q) (eSecond := eSecond) (hrL := hrL) (hrR := hrR)
      (hu0 := hu0) (hu1 := hu1) (hp0 := hp0) (hp1 := hp1)
      (hcover := hcover)

end GC.GraphManifold
