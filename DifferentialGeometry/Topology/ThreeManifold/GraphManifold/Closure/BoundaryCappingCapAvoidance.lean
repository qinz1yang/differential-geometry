import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.BoundaryCappingFactorMaps

/-!
Every physical point of the original left factor avoids the closed sphere caps in the same
capped torus quotient. The cross relation is excluded by the actual sphere and torus collars.
-/

set_option autoImplicit false

noncomputable section

open Set Function Manifold
open DifferentialGeometry DifferentialGeometry.Topology GC.Endpoint GC.Seifert
open GC.Endpoint.CompactCarrier GC.GraphManifold
open scoped Manifold ContDiff Topology

universe u

namespace GC.GraphManifold.RelativeSphereCapping

private theorem capAvoidanceTori_map {C : CompactCarrier.{u}} {n m : ℕ}
    (hn : n = m) (E : BoundaryTori C n) (i : Fin m) (t : Torus) :
    (hn ▸ E).torusMap i t = E.torusMap (Fin.cast hn.symm i) t := by
  cases hn
  rfl

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

include hC2 hr0 in
theorem boundaryCappingLeft_avoidsClosedCaps (x : C1.Carrier) :
    (P1).quotientMap (Sum.inl x) ∉ ⋃ i, range (cap i) := by
  intro hm
  obtain ⟨i, a, ha⟩ := mem_iUnion.mp hm
  have hi : core ((P0).quotientMap (Sum.inl x)) ∈ range core ∩ range (cap i) :=
    ⟨⟨_, rfl⟩, ⟨a, ha⟩⟩
  rw [boundaryCapping_core_cap_intersection] at hi
  obtain ⟨z, hz⟩ := hi
  have he := (boundaryCappingCore_isEmbedding C1 C2 S hC1 hC2 hS B ht K E1 f
    hr0 hr1).injective hz
  have hr := Quotient.exact he
  change (P0).gluing.rel (Sum.inr (B.sphere i (z, halfZero))) (Sum.inl x) at hr
  rcases (TorusPairing.rel_iff_params (P0)
    (Sum.inr (B.sphere i (z, halfZero))) (Sum.inl x)).mp hr with he | ⟨j, t, h | h⟩
  · exact Sum.inr_ne_inl he
  · exact Sum.inr_ne_inl h.1
  · have he : B.sphere i (z, halfZero) =
        (boundaryCappingTori C2 B ht).torusMap 0 (f t) := Sum.inr_injective h.2
    unfold boundaryCappingTori at he
    rw [capAvoidanceTori_map] at he
    have htor : B.tori.torusMap (Fin.cast ht.symm 0) (f t) ∈
        (B.tori.collar (Fin.cast ht.symm 0)).target :=
      (B.tori.collar (Fin.cast ht.symm 0)).map_source (by
        rw [B.tori.source_eq]
        change (0 : ℝ) < 1
        norm_num)
    have hsphere : B.sphere i (z, halfZero) ∈ (B.sphere i).target :=
      (B.sphere i).map_source (by
        rw [B.sphere_source]
        change (0 : ℝ) < 1
        norm_num)
    exact (B.cross_disjoint (Fin.cast ht.symm 0) i).le_bot ⟨htor, he ▸ hsphere⟩

include hC2 hr0 in
theorem boundaryCappingLeft_memChartInterior
    (M : ConnectedClosedOrientedManifold.{u} 3)
    (H : (P1).QuotientSpace ≃ₜ M.Carrier)
    (c : BallChart 3 (𝓡 3) M.Carrier) (i : Fin B.sphereCount)
    (hcap : c.chart '' Metric.closedBall 0 1 = H '' range (cap i))
    (x : C1.Carrier) : H ((P1).quotientMap (Sum.inl x)) ∈ c.interior := by
  rw [BallChart.mem_interior, hcap]
  rintro ⟨y, hy, he⟩
  have hxy : y = (P1).quotientMap (Sum.inl x) := H.injective he
  have hm : (P1).quotientMap (Sum.inl x) ∈ ⋃ i, range (cap i) :=
    mem_iUnion.mpr ⟨i, hxy ▸ hy⟩
  exact boundaryCappingLeft_avoidsClosedCaps C1 C2 S hC1 hC2 hS B ht K E1 f hr0 hr1 x hm

end GC.GraphManifold.RelativeSphereCapping
