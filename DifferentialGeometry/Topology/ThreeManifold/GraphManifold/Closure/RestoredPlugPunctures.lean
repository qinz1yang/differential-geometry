import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.BoundaryCappingFactorMaps
import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.PlugSideCapping

/-!
The actual single-side cap and the unchanged positive component chart have the same unit images.
Physical restoration then identifies the same uncapped torus quotient with the summand puncture.
-/

set_option autoImplicit false

noncomputable section

open Set Function Manifold
open DifferentialGeometry DifferentialGeometry.Topology GC.Endpoint GC.GraphManifold GC.Seifert
open GC.Endpoint.CompactCarrier GC.GraphManifold.RelativeSphereCapping
open scoped Manifold ContDiff Topology

universe u

namespace GC.Seifert.ElementaryPresentation

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
  (i : Fin 2)

local notation "Cᵢ" => E.plugComponentCutCarrier h hlin d hs heq hc hn i
local notation "Sᵢ" => E.plugComponentCapCarrier h hlin d hs hI heq hc hn hρ hρ1 havρ i
local notation "Bᵢ" => E.plugSideBoundary h hlin d hs hI heq hc hn hρ hρ1 havρ i
local notation "Kᵢ" => E.plugSideCapping h hlin d hs hI heq hc hn hρ hρ1 havρ i
local notation "pᵢ" => E.plugComponentCapBallChart h hlin d hs hI heq hc hn hρ hρ1 havρ i

theorem plugCapChart_closedUnit_image :
    (pᵢ).chart '' Metric.closedBall 0 1 = range ((Kᵢ).cap 0) := by
  apply (Set.image_injective.mpr Subtype.val_injective)
  have he : (fun x => ((Kᵢ).cap 0 x).val) =
      (E.fibrePlugCutBoundary d hs hρ hρ1 hI havρ).sphereCapReparameterizedCap i := by
    funext x
    exact E.plugSideCapping_cap h hlin d hs hI heq hc hn hρ hρ1 havρ i x
  exact (E.plugComponentCapChart_closedUnit_image
    h hlin d hs hI heq hc hn hρ hρ1 havρ i).trans
      ((congrArg Set.range he).symm.trans (Set.range_comp' Subtype.val ((Kᵢ).cap 0)))

theorem plugCapChart_openUnit_image :
    (pᵢ).chart '' Metric.ball 0 1 = (Kᵢ).cap 0 '' {x : ClosedCell 3 | ‖x.val‖ < 1} := by
  apply (Set.image_injective.mpr Subtype.val_injective)
  have he : (fun x => ((Kᵢ).cap 0 x).val) =
      (E.fibrePlugCutBoundary d hs hρ hρ1 hI havρ).sphereCapReparameterizedCap i := by
    funext x
    exact E.plugSideCapping_cap h hlin d hs hI heq hc hn hρ hρ1 havρ i x
  exact (E.plugComponentCapChart_openUnit_image
    h hlin d hs hI heq hc hn hρ hρ1 havρ i).trans
      ((congrArg (fun f => f '' {x : ClosedCell 3 | ‖x.val‖ < 1}) he).symm.trans
        (Set.image_image Subtype.val ((Kᵢ).cap 0) {x : ClosedCell 3 | ‖x.val‖ < 1}).symm)

theorem plugCapChart_boundary_cap (z : ClosureSphere.{u}) :
    (pᵢ).chart z.down.val = (Kᵢ).cap 0 (closureSphereToBall z) := by
  apply Subtype.ext
  exact (E.plugComponentCapChart_boundary h hlin d hs hI heq hc hn hρ hρ1 havρ i z).trans
    (((E.fibrePlugCutBoundary d hs hρ hρ1 hI havρ).sphereCapReparameterizedCap_boundary i
      z).symm.trans
      (E.plugSideCapping_cap h hlin d hs hI heq hc hn hρ hρ1 havρ i
        (closureSphereToBall z)).symm)

variable (C1 : CompactCarrier.{u}) (hC1 : C1.kind = .withBoundary)
  [Nonempty C1.Carrier] [Nonempty (E.plugComponentCutCarrier h hlin d hs heq hc hn i).Carrier]
    [Nonempty (E.plugComponentCapCarrier h hlin d hs hI heq hc hn hρ hρ1 havρ i).Carrier]
  (E1 : BoundaryTori C1 1) (f : Torus ≃ₘ⟮torusModel, torusModel⟯ Torus)
  (hr0 : ReversesBoundaryOrientation (withBoundarySum C1 (E.plugComponentCutCarrier h hlin d hs
    heq hc hn i) hC1 rfl)
    (boundaryPortLeftCollar C1 (E.plugComponentCutCarrier h hlin d hs heq hc hn i) hC1 rfl E1)
    (fun p => boundaryPortRightCollar C1 (E.plugComponentCutCarrier h hlin d hs heq hc hn i) hC1 rfl
      (boundaryCappingTori (E.plugComponentCutCarrier h hlin d hs heq hc hn i) (E.plugSideBoundary
        h hlin d hs hI heq hc hn hρ hρ1 havρ i) rfl) 0 (f p.1, p.2)))
  (hr1 : ReversesBoundaryOrientation (withBoundarySum C1 (E.plugComponentCapCarrier h hlin d hs hI
    heq hc hn hρ hρ1 havρ i) hC1 rfl)
    (boundaryPortLeftCollar C1 (E.plugComponentCapCarrier h hlin d hs hI heq hc hn hρ hρ1 havρ i)
      hC1 rfl E1)
    (fun p => boundaryPortRightCollar C1 (E.plugComponentCapCarrier h hlin d hs hI heq hc hn hρ
      hρ1 havρ i) hC1 rfl
      (boundaryCappingRetained (E.plugComponentCutCarrier h hlin d hs heq hc hn i)
        (E.plugComponentCapCarrier h hlin d hs hI heq hc hn hρ hρ1 havρ i) (E.plugSideBoundary h
        hlin d hs hI heq hc hn hρ hρ1 havρ i) rfl (E.plugSideCapping h hlin d hs hI heq hc hn hρ
        hρ1 havρ i)) 0 (f p.1, p.2)))

local notation "P0" => boundaryCappingUncappedPairing C1 (E.plugComponentCutCarrier h hlin d hs
  heq hc hn i) hC1 rfl (E.plugSideBoundary h hlin d hs hI heq hc hn hρ hρ1 havρ i) rfl E1 f hr0
local notation "P1" => boundaryCappingCappedPairing C1 (E.plugComponentCutCarrier h hlin d hs heq
  hc hn i) (E.plugComponentCapCarrier h hlin d hs hI heq hc hn hρ hρ1 havρ i) hC1 rfl
  (E.plugSideBoundary h hlin d hs hI heq hc hn hρ hρ1 havρ i) rfl (E.plugSideCapping h hlin d hs
  hI heq hc hn hρ hρ1 havρ i) E1 f hr1
local notation "core" => boundaryCappingCore C1 (E.plugComponentCutCarrier h hlin d hs heq hc hn
  i) (E.plugComponentCapCarrier h hlin d hs hI heq hc hn hρ hρ1 havρ i) hC1 rfl rfl
  (E.plugSideBoundary h hlin d hs hI heq hc hn hρ hρ1 havρ i) rfl (E.plugSideCapping h hlin d hs
  hI heq hc hn hρ hρ1 havρ i) E1 f hr0 hr1
local notation "qcap" => boundaryCappingCap C1 (E.plugComponentCutCarrier h hlin d hs heq hc hn i)
  (E.plugComponentCapCarrier h hlin d hs hI heq hc hn hρ hρ1 havρ i) hC1 rfl (E.plugSideBoundary h
  hlin d hs hI heq hc hn hρ hρ1 havρ i) rfl (E.plugSideCapping h hlin d hs hI heq hc hn hρ hρ1
  havρ i) E1 f hr1
local notation "qopen" => boundaryCappingOpenCaps C1 (E.plugComponentCutCarrier h hlin d hs heq hc
  hn i) (E.plugComponentCapCarrier h hlin d hs hI heq hc hn hρ hρ1 havρ i) hC1 rfl
  (E.plugSideBoundary h hlin d hs hI heq hc hn hρ hρ1 havρ i) rfl (E.plugSideCapping h hlin d hs
  hI heq hc hn hρ hρ1 havρ i) E1 f hr1

variable (M : ConnectedClosedOrientedManifold.{u} 3)
  (φ : PartialDiffeomorph (𝓘(ℝ, ℂ).prod (𝓡 1)) (𝓡 3)
    (PlaneLift.{u} × Circle) M.Carrier ∞)
  (h3 : {p : PlaneLift.{u} × Circle | ‖p.1.down‖ ≤ 3} ⊆ φ.source)
  (g : solidSet.{u} ≃ₘ⟮𝓡∂ 3, (E.plugComponentCapCarrier h hlin d hs hI heq hc hn hρ hρ1 havρ
    i).model⟯ (E.plugComponentCapCarrier h hlin d hs hI heq hc hn hρ hρ1 havρ i).Carrier) (ε : Bool)
  (H : (boundaryCappingCappedPairing C1 (E.plugComponentCutCarrier h hlin d hs heq hc hn i)
    (E.plugComponentCapCarrier h hlin d hs hI heq hc hn hρ hρ1 havρ i) hC1 rfl (E.plugSideBoundary
    h hlin d hs hI heq hc hn hρ hρ1 havρ i) rfl (E.plugSideCapping h hlin d hs hI heq hc hn hρ hρ1
    havρ i) E1 f hr1).QuotientSpace ≃ₜ M.Carrier)
  (hH : ∀ y : (E.plugComponentCapCarrier h hlin d hs hI heq hc hn hρ hρ1 havρ i).Carrier, H
    ((boundaryCappingCappedPairing C1 (E.plugComponentCutCarrier h hlin d hs heq hc hn i)
    (E.plugComponentCapCarrier h hlin d hs hI heq hc hn hρ hρ1 havρ i) hC1 rfl (E.plugSideBoundary
    h hlin d hs hI heq hc hn hρ hρ1 havρ i) rfl (E.plugSideCapping h hlin d hs hI heq hc hn hρ hρ1
    havρ i) E1 f hr1).quotientMap (Sum.inr y)) =
    regularFibreRestorationFill M φ ((markedRestorationSolidMap (E.plugComponentCapCarrier h hlin
      d hs hI heq hc hn hρ hρ1 havρ i) g ε).symm y))

include h3 g hr0 hH in
theorem exists_restoredPlugPuncture :
    ∃ c : BallChart 3 (𝓡 3) M.Carrier,
      c.chart.source = Metric.ball 0 (5 / 2) ∧
      (∀ x, c.chart x = regularFibreRestorationFill M φ
        ((markedRestorationSolidMap (E.plugComponentCapCarrier h hlin d hs hI heq hc hn hρ hρ1
          havρ i) g ε).symm ((E.plugComponentCapBallChart h hlin d hs hI heq hc hn hρ hρ1 havρ
          i).chart x))) ∧
      ∃ e : (boundaryCappingUncappedPairing C1 (E.plugComponentCutCarrier h hlin d hs heq hc hn i)
        hC1 rfl (E.plugSideBoundary h hlin d hs hI heq hc hn hρ hρ1 havρ i) rfl E1 f
        hr0).QuotientSpace ≃ₜ c.Punctured,
        (∀ x, (e x).val = H (core x)) ∧
        ∀ z : ClosureSphere.{u},
          e ((boundaryCappingUncappedPairing C1 (E.plugComponentCutCarrier h hlin d hs heq hc hn
            i) hC1 rfl (E.plugSideBoundary h hlin d hs hI heq hc hn hρ hρ1 havρ i) rfl E1 f
            hr0).quotientMap (Sum.inr ((E.plugSideBoundary h hlin d hs hI heq hc hn hρ hρ1 havρ
            i).sphere 0 ((E.plugSideCapping h hlin d hs hI heq hc hn hρ hρ1 havρ i).attaching 0 z,
            halfZero)))) =
            c.boundaryMap z.down := by
  obtain ⟨c, hcs, hcx, hcimage, _⟩ := E.exists_restoredPlugCapBallChart
    h hlin d hs hI heq hc hn hρ hρ1 havρ i M φ h3 g ε
  have hsingle : qopen = qcap 0 '' {a : ClosedCell 3 | ‖a.val‖ < 1} := by
    change (⋃ k : Fin 1, _) = _
    ext x
    constructor
    · intro hx
      obtain ⟨k, hk⟩ := mem_iUnion.mp hx
      have hk0 : k = 0 := Subsingleton.elim k 0
      exact hk0 ▸ hk
    · intro hx
      exact mem_iUnion.mpr ⟨0, hx⟩
  have hi : c.chart '' Metric.ball 0 1 = H '' qopen := by
    rw [hcimage, E.plugCapChart_openUnit_image h hlin d hs hI heq hc hn hρ hρ1 havρ i]
    rw [hsingle, Set.image_image, Set.image_image]
    apply Set.image_congr
    intro a ha
    exact (hH ((E.plugSideCapping h hlin d hs hI heq hc hn hρ hρ1 havρ i).cap 0 a)).symm
  let e0 := boundaryCappingCorePunctureHomeomorph
    C1 (E.plugComponentCutCarrier h hlin d hs heq hc hn i) (E.plugComponentCapCarrier h hlin d hs
      hI heq hc hn hρ hρ1 havρ i) hC1 rfl rfl (E.plugSideBoundary h hlin d hs hI heq hc hn hρ hρ1
      havρ i) rfl (E.plugSideCapping h hlin d hs hI heq hc hn hρ hρ1 havρ i) E1 f hr0 hr1
  let e1 : ↥(qopen)ᶜ ≃ₜ c.Punctured := H.subtype (fun x => by
    change x ∉ qopen ↔ H x ∉ c.chart '' Metric.ball 0 1
    rw [hi, H.injective.mem_set_image])
  let e := e0.trans e1
  refine ⟨c, hcs, hcx, e, fun x => rfl, ?_⟩
  intro z
  apply Subtype.ext
  change H ((boundaryCappingCappedPairing C1 (E.plugComponentCutCarrier h hlin d hs heq hc hn i)
    (E.plugComponentCapCarrier h hlin d hs hI heq hc hn hρ hρ1 havρ i) hC1 rfl (E.plugSideBoundary
    h hlin d hs hI heq hc hn hρ hρ1 havρ i) rfl (E.plugSideCapping h hlin d hs hI heq hc hn hρ hρ1
    havρ i) E1 f hr1).quotientMap (Sum.inr ((E.plugSideCapping h hlin d hs hI heq hc hn hρ hρ1
    havρ i).core
    ((E.plugSideBoundary h hlin d hs hI heq hc hn hρ hρ1 havρ i).sphere 0 ((E.plugSideCapping h
      hlin d hs hI heq hc hn hρ hρ1 havρ i).attaching 0 z, halfZero))))) = c.chart z.down.val
  rw [← (E.plugSideCapping h hlin d hs hI heq hc hn hρ hρ1 havρ i).boundary_eq 0 z, hH, hcx,
    E.plugCapChart_boundary_cap h hlin d hs hI heq hc hn hρ hρ1 havρ i z]

end GC.Seifert.ElementaryPresentation
