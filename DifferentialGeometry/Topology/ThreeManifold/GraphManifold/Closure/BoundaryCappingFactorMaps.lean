import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.BoundaryCappingCommutation
import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Seifert.EmbeddedPieces
import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.RestorationPatchTransport
import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.PlugComponentCapCharts
import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.FibreMarkedRestoration
import DifferentialGeometry.Topology.ThreeManifold.ConnectedSum.Collar

/-!
The original positive-height boundary collar provides a real interior point of the left factor.
Its image in the same capped torus quotient avoids all closed cap balls, including their boundary.
-/

set_option autoImplicit false

noncomputable section

open Set Function Manifold
open DifferentialGeometry DifferentialGeometry.Topology GC.Endpoint GC.Seifert
open GC.Endpoint.CompactCarrier GC.GraphManifold
open scoped Manifold ContDiff Topology

universe u

namespace GC.GraphManifold.RelativeSphereCapping

variable (C1 C2 S : CompactCarrier.{u})
  (hC1 : C1.kind = .withBoundary) (hC2 : C2.kind = .withBoundary)
  (hS : S.kind = .withBoundary)
  [Nonempty C1.Carrier] [Nonempty C2.Carrier] [Nonempty S.Carrier]
  (B : MixedBoundaryCertificate C2) (ht : B.torusCount = 1)
  (K : RelativeSphereCapping C2 S B) (E1 : BoundaryTori C1 1)
  (f : Torus ≃ₘ⟮torusModel, torusModel⟯ Torus)
  (hr0 : ReversesBoundaryOrientation (withBoundarySum C1 C2 hC1 hC2)
    (boundaryPortLeftCollar C1 C2 hC1 hC2 E1)
    (fun p => boundaryPortRightCollar C1 C2 hC1 hC2 (boundaryCappingTori C2 B ht) 0
      (f p.1, p.2)))
  (hr1 : ReversesBoundaryOrientation (withBoundarySum C1 S hC1 hS)
    (boundaryPortLeftCollar C1 S hC1 hS E1)
    (fun p => boundaryPortRightCollar C1 S hC1 hS
      (boundaryCappingRetained C2 S B ht K) 0 (f p.1, p.2)))

local notation "P0" => boundaryCappingUncappedPairing C1 C2 hC1 hC2 B ht E1 f hr0
local notation "P1" => boundaryCappingCappedPairing C1 C2 S hC1 hS B ht K E1 f hr1
local notation "core" => boundaryCappingCore C1 C2 S hC1 hC2 hS B ht K E1 f hr0 hr1
local notation "cap" => boundaryCappingCap C1 C2 S hC1 hS B ht K E1 f hr1

def boundaryCappingFactorLeftPoint : C1.Carrier :=
  E1.collar 0 (torusBase, halfPoint (1 / 2) (by norm_num))

omit [Nonempty C1.Carrier] in
theorem boundaryCappingFactorLeftPoint_interior :
    C1.model.IsInteriorPoint (boundaryCappingFactorLeftPoint C1 E1) := by
  let p : Torus × EuclideanHalfSpace 1 := (torusBase, halfPoint (1 / 2) (by norm_num))
  have hp : p ∈ (E1.collar 0).source := by
    rw [E1.source_eq]
    change (1 / 2 : ℝ) < 1
    norm_num
  have hi : halfCollarModel.IsInteriorPoint p := by
    apply halfCollarModel_isInteriorPoint'
    change (0 : ℝ) < 1 / 2
    norm_num
  exact ((E1.collar 0).isLocalDiffeomorphAt halfCollarModel C1.model ∞ hp).isInteriorPoint_iff
    (by simp) |>.mp hi

include hC2 hr0 in
theorem boundaryCappingLeftInterior_avoidsClosedCaps (x : C1.Carrier)
    (hx : C1.model.IsInteriorPoint x) :
    (P1).quotientMap (Sum.inl x) ∉ ⋃ i, range (cap i) := by
  intro hm
  obtain ⟨i, a, ha⟩ := mem_iUnion.mp hm
  have hmem : core ((P0).quotientMap (Sum.inl x)) ∈ range core ∩ range (cap i) :=
    ⟨⟨_, rfl⟩, ⟨a, ha⟩⟩
  rw [boundaryCapping_core_cap_intersection] at hmem
  obtain ⟨z, hz⟩ := hmem
  have he := (boundaryCappingCore_isEmbedding C1 C2 S hC1 hC2 hS B ht K E1 f hr0 hr1).injective hz
  have hr := Quotient.exact he
  change (P0).gluing.rel
    (Sum.inr (B.sphere i (z, halfZero))) (Sum.inl x) at hr
  have hr' := (TorusPairing.rel_iff_params (P0)
    (Sum.inr (B.sphere i (z, halfZero))) (Sum.inl x)).mp hr
  rcases hr' with he | ⟨j, t, h | h⟩
  · exact Sum.inr_ne_inl he
  · have he : Sum.inr (B.sphere i (z, halfZero)) = Sum.inl (E1.torusMap 0 t) := h.1
    exact Sum.inr_ne_inl he
  · have he : Sum.inl x = Sum.inl (E1.torusMap 0 t) := h.1
    have hx' : x = E1.torusMap 0 t := Sum.inl_injective he
    have hb : C1.model.IsBoundaryPoint x := hx'.symm ▸ E1.boundary_zero 0 t
    exact (C1.model.isInteriorPoint_iff_not_isBoundaryPoint x).mp hx hb

include hC2 hr0 in
theorem boundaryCappingFactorLeftPoint_avoidsClosedCaps :
    (P1).quotientMap (Sum.inl (boundaryCappingFactorLeftPoint C1 E1)) ∉ ⋃ i, range (cap i) :=
  boundaryCappingLeftInterior_avoidsClosedCaps C1 C2 S hC1 hC2 hS B ht K E1 f hr0 hr1
    (boundaryCappingFactorLeftPoint C1 E1) (boundaryCappingFactorLeftPoint_interior C1 E1)

end GC.GraphManifold.RelativeSphereCapping

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
  (i : Fin 2) (M : ConnectedClosedOrientedManifold.{u} 3)
  (φ : PartialDiffeomorph (𝓘(ℝ, ℂ).prod (𝓡 1)) (𝓡 3)
    (PlaneLift.{u} × Circle) M.Carrier ∞)
  (h3 : {p : PlaneLift.{u} × Circle | ‖p.1.down‖ ≤ 3} ⊆ φ.source)


variable (g : solidSet.{u} ≃ₘ⟮𝓡∂ 3, (E.plugComponentCapCarrier h hlin d hs hI heq hc hn hρ hρ1
  havρ i).model⟯ (E.plugComponentCapCarrier h hlin d hs hI heq hc hn hρ hρ1 havρ i).Carrier) (ε :
  Bool)


include h3 g in
theorem exists_restoredPlugCapBallChart :
    ∃ c : BallChart 3 (𝓡 3) M.Carrier,
      c.chart.source = Metric.ball 0 (5 / 2) ∧
      (∀ x, c.chart x = regularFibreRestorationFill M φ ((markedRestorationSolidMap
        (E.plugComponentCapCarrier h hlin d hs hI heq hc hn hρ hρ1 havρ i) g ε).symm
        ((E.plugComponentCapBallChart h hlin d hs hI heq hc hn hρ hρ1 havρ i).chart x))) ∧
      (∀ A : Set (EuclideanSpace ℝ (Fin 3)), c.chart '' A =
        (regularFibreRestorationFill M φ ∘ (markedRestorationSolidMap (E.plugComponentCapCarrier h
          hlin d hs hI heq hc hn hρ hρ1 havρ i) g ε).symm) '' ((E.plugComponentCapBallChart h hlin
          d hs hI heq hc hn hρ hρ1 havρ i).chart '' A)) ∧
      ∀ t : Torus, φ (ULift.up ((5 / 4 : ℝ) • (t.1 : ℂ)), t.2) ∈ c.interior := by
  have hx : (0 : EuclideanSpace ℝ (Fin 3)) ∈ (E.plugComponentCapBallChart h hlin d hs hI heq hc hn
    hρ hρ1 havρ i).chart.source :=
    (E.plugComponentCapBallChart h hlin d hs hI heq hc hn hρ hρ1 havρ i).closedBall_subset_source
      (by simp)
  obtain ⟨q, hq, ht, he⟩ :=
    exists_restorationTransportedPatch M φ h3 (E.plugComponentCapCarrier h hlin d hs hI heq hc hn
      hρ hρ1 havρ i) (markedRestorationSolidMap (E.plugComponentCapCarrier h hlin d hs hI heq hc
      hn hρ hρ1 havρ i) g ε) (E.plugComponentCapBallChart h hlin d hs hI heq hc hn hρ hρ1 havρ
      i).chart 0 hx
  let c : BallChart 3 (𝓡 3) M.Carrier :=
    { chart := q
      closedBall_subset_source := hq.symm ▸ (E.plugComponentCapBallChart h hlin d hs hI heq hc hn
        hρ hρ1 havρ i).closedBall_subset_source }
  refine ⟨c, hq.trans
    (E.plugComponentCapChart_source h hlin d hs hI heq hc hn hρ hρ1 havρ i), he, ?_, ?_⟩
  · intro A
    rw [← Set.image_comp]
    exact Set.image_congr (fun x hx => he x)
  · intro t hm
    obtain ⟨x, hx, hpoint⟩ := hm
    let p0 : PlaneLift.{u} × Circle := (ULift.up ((5 / 4 : ℝ) • (t.1 : ℂ)), t.2)
    have hnorm : ‖p0.1.down‖ = 5 / 4 := by
      change ‖(5 / 4 : ℝ) • (t.1 : ℂ)‖ = 5 / 4
      rw [norm_smul]
      norm_num
    have hsrc : p0 ∈ φ.source := h3 (by change ‖p0.1.down‖ ≤ 3; rw [hnorm]; norm_num)
    have himg : φ p0 ∈ range (regularFibreRestorationFill M φ) :=
      ⟨(markedRestorationSolidMap (E.plugComponentCapCarrier h hlin d hs hI heq hc hn hρ hρ1 havρ
        i) g ε).symm ((E.plugComponentCapBallChart h hlin d hs hI heq hc hn hρ hρ1 havρ i).chart
        x), (he x).symm.trans hpoint⟩
    rw [regularFibreRestorationFill_range] at himg
    obtain ⟨p, hp, hpeq⟩ := himg
    have hps : p ∈ φ.source := by
      apply h3
      change ‖p.1.down‖ ≤ 3
      change ‖p.1.down‖ ≤ 1 at hp
      linarith
    have hpp : p = p0 := φ.injOn hps hsrc hpeq
    have hn0 : ‖p0.1.down‖ ≤ 1 := hpp ▸ hp
    rw [hnorm] at hn0
    norm_num at hn0

end GC.Seifert.ElementaryPresentation
