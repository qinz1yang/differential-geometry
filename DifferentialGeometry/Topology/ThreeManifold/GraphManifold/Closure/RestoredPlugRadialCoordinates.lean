import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.PlugComponentCapCollarGerm
import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.RestoredPlugPunctures

/-!
The same physical component cap collar becomes the exact radial collar of its restored ball chart.
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

variable (c : OrientedBallChart M.toClosedOrientedManifold)
  (hcx : ∀ x, c.chart x = regularFibreRestorationFill M φ
    ((markedRestorationSolidMap (E.plugComponentCapCarrier h hlin d hs hI heq hc hn hρ hρ1
      havρ i) g ε).symm
        ((E.plugComponentCapBallChart h hlin d hs hI heq hc hn hρ hρ1 havρ i).chart x)))
  (e : (boundaryCappingUncappedPairing C1 (E.plugComponentCutCarrier h hlin d hs heq hc hn i)
    hC1 rfl (E.plugSideBoundary h hlin d hs hI heq hc hn hρ hρ1 havρ i) rfl E1 f
      hr0).QuotientSpace ≃ₜ c.toBallChart.Punctured)
  (hcore : ∀ x, (e x).val = H (boundaryCappingCore C1
    (E.plugComponentCutCarrier h hlin d hs heq hc hn i)
    (E.plugComponentCapCarrier h hlin d hs hI heq hc hn hρ hρ1 havρ i) hC1 rfl rfl
    (E.plugSideBoundary h hlin d hs hI heq hc hn hρ hρ1 havρ i) rfl
    (E.plugSideCapping h hlin d hs hI heq hc hn hρ hρ1 havρ i) E1 f hr0 hr1 x))

include hH hcx hcore in
theorem exists_restoredPlugRadialCoordinates :
    ∃ η > (0 : ℝ), ∃ hη1 : η ≤ 1 / 4,
      ∀ (z : Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1) (s : ℝ)
        (hs0 : 0 ≤ s) (hsη : s < η),
        e ((P0).quotientMap (Sum.inr ((Bᵢ).sphere 0
          ((Kᵢ).attaching 0 (ULift.up z), halfPoint (2 * s) (by linarith))))) =
          c.toBallChart.radialMap z (1 + s) ⟨by linarith, by linarith⟩ := by
  obtain ⟨η, hη, hη1, hg⟩ := E.exists_plugComponentCapCollarGerm
    h hlin d hs hI heq hc hn hρ hρ1 havρ
  refine ⟨η, hη, hη1, ?_⟩
  intro z s hs0 hsη
  apply Subtype.ext
  rw [hcore]
  change H ((P1).quotientMap (Sum.inr ((Kᵢ).core ((Bᵢ).sphere 0
    ((Kᵢ).attaching 0 (ULift.up z), halfPoint (2 * s) (by linarith)))))) =
      c.chart ((1 + s) • z.val)
  rw [hH]
  have hp := hg i (ULift.up z) (1 + s) (by linarith) (by linarith)
  have hv : 2 * (1 + s) - 2 = 2 * s := by ring
  simp only [hv] at hp
  rw [← hp, ← hcx]

end GC.Seifert.ElementaryPresentation
