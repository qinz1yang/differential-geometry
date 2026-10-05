import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.PlugCutFactorGeometry
import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.PlugDoubleBoundaryAssembly
import
  DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.DoubleBoundaryFactorQuotients

/-!
The original plug and its two physical excisions assemble on one closed carrier.
The same two quotient reconstructions retain both uncapped factor maps and their exact cut squares.
-/

set_option autoImplicit false
noncomputable section
open Set Function Manifold
open DifferentialGeometry DifferentialGeometry.Topology GC.Endpoint GC.GraphManifold GC.Seifert
open GC.Endpoint.CompactCarrier
open scoped Manifold ContDiff Topology
universe u
namespace GC.Seifert.ElementaryPresentation
open SplitTube

variable {W : CompactCarrier.{u}} (E : ElementaryPresentation W)
  {j : Fin E.toTorus.pairing.count} {b : Bool} (h : E.IsSplitSeam j b)
  (hlin : E.IsLinearSeam j)
  (d : PartialDiffeomorph sphereSignedCollarModel W.model
    (ClosureSphere.{u} × ℝ) W.Carrier ∞) (hs : d.source = sphereSignedCollarSource)
  (hI : d.target ⊆ W.interior)
  (heq : ∀ z s, d (z, s) = E.boundedSplitTubeMap h hlin (z.down, s))
  (hc : E.toTorus.components.count = 2) (hn : E.toTorus.pairing.count = 1)
  {ρ : ℝ} (hρ : 0 < ρ) (hρ1 : ρ ≤ 1)
  (havρ : ∀ r, Disjoint ((E.toTorus.external.shrink hρ hρ1).collar r).target d.target)


local notation "Cᵢ" i => E.plugComponentCutCarrier h hlin d hs heq hc hn i
local notation "Bᵢ" i => E.plugSideBoundary h hlin d hs hI heq hc hn hρ hρ1 havρ i
local notation "EW" => E.plugCutBoundaryPorts h hc hn hρ hρ1
local notation "uᵢ" i => E.plugCutFactor h hlin d hs heq hc hn i
local notation "zᵢ" i => E.plugCutFactorZero h hlin d hs heq hc hn i

private theorem plugPhysicalPorts_exhausted : W.model.boundary W.Carrier = (EW).image := by
  rw [E.toTorus.external_exhausted, ← E.toTorus.external.shrink_image hρ hρ1]
  ext x
  simp only [BoundaryTori.image, mem_iUnion, mem_range]
  constructor
  · rintro ⟨j, t, ht⟩
    obtain ⟨i, rfl⟩ := (E.fibrePlugCutPortEquiv h hc hn).surjective j
    exact ⟨i, t, ht⟩
  · rintro ⟨i, t, ht⟩
    exact ⟨E.fibrePlugCutPortEquiv h hc hn i, t, ht⟩

private theorem plugPhysicalPorts_reversal
    (hW : W.kind = .withBoundary) (K : CompactCarrier.{u})
    (hK : K.kind = .withBoundary) [Nonempty K.Carrier]
    (Γ : BoundaryTori K 1) (i : Fin 2) (f : Torus ≃ₘ⟮torusModel, torusModel⟯ Torus) :
    let : Nonempty (Cᵢ i).Carrier := ⟨(zᵢ i) (ULift.up poleS2)⟩
    let : Nonempty W.Carrier := ⟨(EW).torusMap i torusBase⟩
    ReversesBoundaryOrientation (K.withBoundarySum (Cᵢ i) hK rfl)
      (boundaryPortLeftCollar K (Cᵢ i) hK rfl Γ)
      (fun p => boundaryPortRightCollar K (Cᵢ i) hK rfl (Bᵢ i).tori 0 (f p.1, p.2)) →
    ReversesBoundaryOrientation (K.withBoundarySum W hK hW)
      (boundaryPortLeftCollar K W hK hW Γ)
      (fun p => boundaryPortRightCollar K W hK hW (EW) i (f p.1, p.2)) := by
  let : Nonempty (Cᵢ i).Carrier := ⟨(zᵢ i) (ULift.up poleS2)⟩
  let : Nonempty W.Carrier := ⟨(EW).torusMap i torusBase⟩
  dsimp only
  intro hr
  have hfold := boundarySum_reversal_of_orientedFold K (Cᵢ i) W hK rfl hW (uᵢ i)
    (E.plugCutFactor_positive h hlin d hs heq hc hn i)
    (E.plugCutFactor_smooth h hlin d hs heq hc hn i) (Γ.collar 0) ((Bᵢ i).tori.collar 0)
    (Γ.source_eq 0) ((Bᵢ i).tori.source_eq 0) f hr
  apply reversesBoundaryOrientation_congrOn hfold
  · intro p hp
    rfl
  · intro p hp
    exact (congrArg (Sum.inr : W.Carrier → (K.withBoundarySum W hK hW).Carrier)
      (E.plugCutFactor_collar h hlin d hs hI heq hc hn hρ hρ1 havρ i
        (f p.1, p.2) hp)).trans
      (boundaryPortRightCollar_apply K W hK hW (EW) i (f p.1, p.2)).symm

variable (hW : W.kind = .withBoundary) [ConnectedSpace W.Carrier]
  (K0 K1 : CompactCarrier.{u}) (hK0 : K0.kind = .withBoundary)
  (hK1 : K1.kind = .withBoundary) [ConnectedSpace K0.Carrier] [ConnectedSpace K1.Carrier]
  (Γ0 : BoundaryTori K0 1) (Γ1 : BoundaryTori K1 1)
  (hb0 : K0.model.boundary K0.Carrier = Γ0.image)
  (hb1 : K1.model.boundary K1.Carrier = Γ1.image)
  (f0 f1 : Torus ≃ₘ⟮torusModel, torusModel⟯ Torus)

include hI havρ hb0 hb1 in
theorem exists_plugPhysicalFactorAssembly
    (R0 : RawGraphPresentation K0) (R1 : RawGraphPresentation K1) :
    let : Nonempty (Cᵢ (0 : Fin 2)).Carrier := ⟨(zᵢ (0 : Fin 2)) (ULift.up poleS2)⟩
    let : Nonempty (Cᵢ (1 : Fin 2)).Carrier := ⟨(zᵢ (1 : Fin 2)) (ULift.up poleS2)⟩
    ∀ (hr0 : ReversesBoundaryOrientation (K0.withBoundarySum (Cᵢ (0 : Fin 2)) hK0 rfl)
      (boundaryPortLeftCollar K0 (Cᵢ (0 : Fin 2)) hK0 rfl Γ0)
      (fun p => boundaryPortRightCollar K0 (Cᵢ (0 : Fin 2)) hK0 rfl
        (Bᵢ (0 : Fin 2)).tori 0 (f0 p.1, p.2))),
    ∀ (hr1 : ReversesBoundaryOrientation (K1.withBoundarySum (Cᵢ (1 : Fin 2)) hK1 rfl)
      (boundaryPortLeftCollar K1 (Cᵢ (1 : Fin 2)) hK1 rfl Γ1)
      (fun p => boundaryPortRightCollar K1 (Cᵢ (1 : Fin 2)) hK1 rfl
        (Bᵢ (1 : Fin 2)).tori 0 (f1 p.1, p.2))),
    let P0 := boundaryPortPairing K0 (Cᵢ (0 : Fin 2)) hK0 rfl
      Γ0 (Bᵢ (0 : Fin 2)).tori f0 hr0
    let P1 := boundaryPortPairing K1 (Cᵢ (1 : Fin 2)) hK1 rfl
      Γ1 (Bᵢ (1 : Fin 2)).tori f1 hr1
    ∃ (N : CompactCarrier.{u}) (hN : N.kind = .withBoundary) (hconn : ConnectedSpace N.Carrier)
      (T1 : TorusPresentation N) (δ1 : ℝ) (hδ1 : 0 < δ1) (hδ11 : δ1 ≤ 1)
      (hcut1 : T1.cutCarrier = K0.withBoundarySum W hK0 hW),
      (hcut1 ▸ T1.components) = rawBoundarySumComponents K0 W hK0 hW ∧
      ∃ hrev0 : ReversesBoundaryOrientation (K0.withBoundarySum W hK0 hW)
        (boundaryPortLeftCollar K0 W hK0 hW Γ0)
        (fun p => boundaryPortRightCollar K0 W hK0 hW (EW) 0 (f0 p.1, p.2)),
      (hcut1 ▸ T1.pairing) =
        (boundaryPortPairing K0 W hK0 hW Γ0 (EW) f0 hrev0).shrink hδ1 hδ11 ∧
      ∃ hen : T1.externalCount = 1,
      let EN : BoundaryTori N 1 := hen ▸ T1.external
      let : ConnectedSpace N.Carrier := hconn
      (∀ p, p ∈ halfCollarSource → EN.collar 0 p =
        T1.cutMap (hcut1.symm ▸ Sum.inr ((EW).collar 1 (p.1, halfSpaceScale hδ1 p.2)))) ∧
      ∃ hrev1 : ReversesBoundaryOrientation (N.withBoundarySum K1 hN hK1)
        (boundaryPortLeftCollar N K1 hN hK1 EN)
        (fun p => boundaryPortRightCollar N K1 hN hK1 (Γ1.shrink hδ1 hδ11) 0
          (f1.symm p.1, p.2)),
      ∃ (δ2 : ℝ) (hδ2 : 0 < δ2) (hδ21 : δ2 ≤ 1)
        (Q : ConnectedClosedOrientedManifold.{u} 3) (T2 : TorusPresentation (NoCuts.carrier Q))
        (hcut2 : T2.cutCarrier = N.withBoundarySum K1 hN hK1),
        (hcut2 ▸ T2.components) = rawBoundarySumComponents N K1 hN hK1 ∧
        (hcut2 ▸ T2.pairing) =
          (boundaryPortPairing N K1 hN hK1 EN (Γ1.shrink hδ1 hδ11) f1.symm hrev1).shrink
            hδ2 hδ21 ∧ T2.externalCount = 0 ∧
        Nonempty (RawGraphPresentation (NoCuts.carrier Q)) ∧
        ∃ (L : C(P0.QuotientSpace, Q.Carrier)) (R : C(P1.QuotientSpace, Q.Carrier)),
          Injective L ∧ Injective R ∧
          (∀ x, L (P0.quotientMap (Sum.inl x)) =
            T2.cutMap (hcut2.symm ▸ Sum.inl (T1.cutMap (hcut1.symm ▸ Sum.inl x)))) ∧
          (∀ x, L (P0.quotientMap (Sum.inr x)) =
            T2.cutMap (hcut2.symm ▸ Sum.inl (T1.cutMap (hcut1.symm ▸ Sum.inr ((uᵢ 0) x))))) ∧
          (∀ x, R (P1.quotientMap (Sum.inl x)) = T2.cutMap (hcut2.symm ▸ Sum.inr x)) ∧
          (∀ x, R (P1.quotientMap (Sum.inr x)) =
            T2.cutMap (hcut2.symm ▸ Sum.inl (T1.cutMap (hcut1.symm ▸ Sum.inr ((uᵢ 1) x))))) ∧
          (∀ x y, L x = R y ↔ ∃ z : ClosureSphere.{u},
            x = P0.quotientMap (Sum.inr ((zᵢ 0) z)) ∧
              y = P1.quotientMap (Sum.inr ((zᵢ 1) z))) ∧ range L ∪ range R = univ := by
  let : Nonempty (Cᵢ (0 : Fin 2)).Carrier := ⟨(zᵢ (0 : Fin 2)) (ULift.up poleS2)⟩
  let : Nonempty (Cᵢ (1 : Fin 2)).Carrier := ⟨(zᵢ (1 : Fin 2)) (ULift.up poleS2)⟩
  dsimp only
  intro hr0 hr1
  have hrev0 := E.plugPhysicalPorts_reversal h hlin d hs hI heq hc hn hρ hρ1 havρ
    hW K0 hK0 Γ0 0 f0 hr0
  have hrev1 := E.plugPhysicalPorts_reversal h hlin d hs hI heq hc hn hρ hρ1 havρ
    hW K1 hK1 Γ1 1 f1 hr1
  have hbW := E.plugPhysicalPorts_exhausted h hc hn hρ hρ1
  obtain ⟨N, hN, hconn, T1, δ1, hδ1, hδ11, hcut1, hc1, hp1, hen,
    e1, hr2, he1, hEN, δ2, hδ2, hδ21, Q, T2, hcut2, hc2, hp2, hz, hraw, e2, he2⟩ :=
    exists_plugDoubleBoundaryAssembly K0 W K1 hK0 hW hK1 Γ0 (EW) Γ1 hb0 hbW hb1
      f0 f1 hrev0 hrev1 R0 E.toRaw R1
  let : ConnectedSpace N.Carrier := hconn
  let EN : BoundaryTori N 1 := hen ▸ T1.external
  have hENzero : ∀ t, EN.torusMap 0 t = e1
      ((boundaryPortPairing K0 W hK0 hW Γ0 (EW) f0 hrev0).quotientMap
        (Sum.inr ((EW).torusMap 1 t))) := by
    intro t
    have ht : EN.torusMap 0 t =
        T1.cutMap (hcut1.symm ▸ Sum.inr ((EW).torusMap 1 t)) := by
      have ht0 := hEN (t, halfZero) (zero_mem_halfCollarSource t)
      simpa only [EN, BoundaryTori.torusMap, halfSpaceScale_halfZero] using ht0
    exact ht.trans (he1 _).symm
  have hΓ1 : ∀ t, (Γ1.shrink hδ1 hδ11).torusMap 0 t = Γ1.torusMap 0 t := by
    intro t
    rw [BoundaryTori.shrink_torusMap]
  obtain ⟨L, R, hiL, hiR, hL0, hL1, hR0, hR1, hcross, hcover⟩ :=
    exists_doubleBoundaryFactors K0 K1 W (Cᵢ (0 : Fin 2)) (Cᵢ (1 : Fin 2)) N
      hK0 hK1 hW rfl rfl hN Γ0 (Γ1.shrink hδ1 hδ11) Γ1 hΓ1 (EW)
      (Bᵢ (0 : Fin 2)).tori (Bᵢ (1 : Fin 2)).tori (uᵢ 0) (uᵢ 1) f0 hrev0 e1 EN
      hENzero f1.symm hr2 Q e2 hr0 hr1
      (E.plugCutFactor_injective h hlin d hs heq hc hn 0)
      (E.plugCutFactor_injective h hlin d hs heq hc hn 1)
      (E.plugCutFactor_port h hlin d hs hI heq hc hn hρ hρ1 havρ 0)
      (E.plugCutFactor_port h hlin d hs hI heq hc hn hρ hρ1 havρ 1)
      (E.plugCutFactor_port_exclusive h hlin d hs hI heq hc hn hρ hρ1 havρ 0 1 (by decide))
      (E.plugCutFactor_port_exclusive h hlin d hs hI heq hc hn hρ hρ1 havρ 1 0 (by decide))
      (zᵢ 0) (zᵢ 1) (fun x y => E.plugCutFactor_cross)
      (E.plugCutFactor_covers h hlin d hs heq hc hn)
  refine ⟨N, hN, hconn, T1, δ1, hδ1, hδ11, hcut1, hc1, hrev0, hp1, hen,
    hEN, hr2, δ2, hδ2, hδ21, Q, T2, hcut2, hc2, hp2, hz, hraw,
    L, R, hiL, hiR, ?_, ?_, ?_, ?_, hcross, hcover⟩
  · intro x
    exact (hL0 x).trans ((he2 _).trans
      (congrArg (fun y : N.Carrier => T2.cutMap (hcut2.symm ▸ Sum.inl y)) (he1 _)))
  · intro x
    exact (hL1 x).trans ((he2 _).trans
      (congrArg (fun y : N.Carrier => T2.cutMap (hcut2.symm ▸ Sum.inl y)) (he1 _)))
  · intro x
    exact (hR0 x).trans (he2 _)
  · intro x
    exact (hR1 x).trans ((he2 _).trans
      (congrArg (fun y : N.Carrier => T2.cutMap (hcut2.symm ▸ Sum.inl y)) (he1 _)))

end GC.Seifert.ElementaryPresentation
