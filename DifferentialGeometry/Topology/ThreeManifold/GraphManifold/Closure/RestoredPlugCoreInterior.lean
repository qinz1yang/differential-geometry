import
  DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.CanonicalRestoredPlugData
import
  DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.BoundaryCappingCapAvoidance

/-!
The unchanged plug cap chart keeps every physical core point in the same open puncture interior.
The original quotient homeomorphism retains its literal left-factor square there.
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

theorem restoredPlugCoreInterior
    (M : ConnectedClosedOrientedManifold.{u} 3)
    (φ : PartialDiffeomorph (𝓘(ℝ, ℂ).prod (𝓡 1)) (𝓡 3)
      (PlaneLift.{u} × Circle) M.Carrier ∞)
    (K : CompactCarrier.{u}) (hK : K.kind = .withBoundary)
    (ι : K.Carrier → M.Carrier) (Γ : BoundaryTori K 1)
    (f : Torus ≃ₘ⟮torusModel, torusModel⟯ Torus) :
    let C := E.plugComponentCutCarrier h hlin d hs heq hc hn i
    let S := E.plugComponentCapCarrier h hlin d hs hI heq hc hn hρ hρ1 havρ i
    let B := E.plugSideBoundary h hlin d hs hI heq hc hn hρ hρ1 havρ i
    let Ki := E.plugSideCapping h hlin d hs hI heq hc hn hρ hρ1 havρ i
    let p := E.plugComponentCapBallChart h hlin d hs hI heq hc hn hρ hρ1 havρ i
    let : Nonempty K.Carrier := ⟨Γ.collar 0 (torusBase, halfZero)⟩
    let : Nonempty C.Carrier := E.plugCoreCutNonempty h hlin d hs heq hc hn i
    let : Nonempty S.Carrier := E.plugCoreCapNonempty h hlin d hs hI heq hc hn hρ hρ1 havρ i
    ∀ (g : solidSet.{u} ≃ₘ⟮𝓡∂ 3, S.model⟯ S.Carrier) (ε : Bool),
    ∀ hr0 : ReversesBoundaryOrientation (withBoundarySum K C hK rfl)
      (boundaryPortLeftCollar K C hK rfl Γ)
      (fun q => boundaryPortRightCollar K C hK rfl B.tori 0 (f q.1, q.2)),
    ∀ hr1 : ReversesBoundaryOrientation (withBoundarySum K S hK rfl)
      (boundaryPortLeftCollar K S hK rfl Γ)
      (fun q => boundaryPortRightCollar K S hK rfl Ki.retained 0 (f q.1, q.2)),
    let P0 := boundaryCappingUncappedPairing K C hK rfl B rfl Γ f hr0
    let P1 := boundaryCappingCappedPairing K C S hK rfl B rfl Ki Γ f hr1
    ∀ (H : P1.QuotientSpace ≃ₜ M.Carrier)
      (c : OrientedBallChart M.toClosedOrientedManifold)
      (e : P0.QuotientSpace ≃ₜ c.Punctured),
    (∀ k : K.Carrier, H (P1.quotientMap (Sum.inl k)) = ι k) →
    (∀ y : S.Carrier, H (P1.quotientMap (Sum.inr y)) = markedRestorationFill M φ S g ε y) →
    (∀ x, c.chart x = markedRestorationFill M φ S g ε (p.chart x)) →
    (∀ x, (e x).val = H (boundaryCappingCore K C S hK rfl rfl B rfl Ki Γ f hr0 hr1 x)) →
    ∃ hmem : ∀ k : K.Carrier, ι k ∈ c.toBallChart.interior,
      ∀ k : K.Carrier, e (P0.quotientMap (Sum.inl k)) =
        c.toBallChart.interiorToPunctured ⟨ι k, hmem k⟩ := by
  dsimp only
  intro g ε hr0 hr1 H c e hleft hright hcx hcore
  let C := E.plugComponentCutCarrier h hlin d hs heq hc hn i
  let S := E.plugComponentCapCarrier h hlin d hs hI heq hc hn hρ hρ1 havρ i
  let B := E.plugSideBoundary h hlin d hs hI heq hc hn hρ hρ1 havρ i
  let Ki := E.plugSideCapping h hlin d hs hI heq hc hn hρ hρ1 havρ i
  let p := E.plugComponentCapBallChart h hlin d hs hI heq hc hn hρ hρ1 havρ i
  let : Nonempty K.Carrier := ⟨Γ.collar 0 (torusBase, halfZero)⟩
  let : Nonempty C.Carrier := E.plugCoreCutNonempty h hlin d hs heq hc hn i
  let : Nonempty S.Carrier := E.plugCoreCapNonempty h hlin d hs hI heq hc hn hρ hρ1 havρ i
  have hcap : c.chart '' Metric.closedBall 0 1 =
      H '' range (boundaryCappingCap K C S hK rfl B rfl Ki Γ f hr1 0) := by
    have hp : p.chart '' Metric.closedBall 0 1 = range (Ki.cap 0) :=
      E.plugCapChart_closedUnit_image h hlin d hs hI heq hc hn hρ hρ1 havρ i
    ext y
    constructor
    · rintro ⟨x, hx, rfl⟩
      have hm : p.chart x ∈ range (Ki.cap 0) := hp ▸ ⟨x, hx, rfl⟩
      obtain ⟨v, hv⟩ := hm
      refine ⟨_, ⟨v, rfl⟩, ?_⟩
      change H ((boundaryCappingCappedPairing K C S hK rfl B rfl Ki Γ f hr1).quotientMap
        (Sum.inr (Ki.cap 0 v))) = c.chart x
      rw [hright, hv]
      exact (hcx x).symm
    · rintro ⟨y, ⟨v, rfl⟩, rfl⟩
      have hm : Ki.cap 0 v ∈ p.chart '' Metric.closedBall 0 1 := hp.symm ▸ ⟨v, rfl⟩
      obtain ⟨x, hx, hpx⟩ := hm
      refine ⟨x, hx, ?_⟩
      change c.chart x =
        H ((boundaryCappingCappedPairing K C S hK rfl B rfl Ki Γ f hr1).quotientMap
          (Sum.inr (Ki.cap 0 v)))
      rw [hright, hcx, hpx]
  have hmem (k : K.Carrier) : ι k ∈ c.toBallChart.interior := by
    have hh := boundaryCappingLeft_memChartInterior K C S hK rfl rfl B rfl Ki Γ f hr0 hr1
      M H c.toBallChart 0 hcap k
    exact (hleft k) ▸ hh
  refine ⟨hmem, ?_⟩
  intro k
  apply Subtype.ext
  change (e ((boundaryCappingUncappedPairing K C hK rfl B rfl Γ f hr0).quotientMap
    (Sum.inl k))).val = ι k
  exact (hcore _).trans ((congrArg H
    (boundaryCappingCore_left K C S hK rfl rfl B rfl Ki Γ f hr0 hr1 k)).trans (hleft k))

end GC.Seifert.ElementaryPresentation
