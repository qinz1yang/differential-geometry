import DifferentialGeometry.Geometry.Collapse.LocalExport.BoundarySlimArcsBCF
import DifferentialGeometry.Topology.Manifold.OneManifold.GenericEndpointsInline

/-!
# BCF01 G1b without the named `Prop` `GenericEndpoints_BCF` (lane S-BCF134c, suffix `_BCF`)

`BoundarySlimArcsBCF.lean` (G10) proves the arc decomposition of a chart-interval `K₃` through the
named `Prop` `GraphAtlas1_BCF.GenericEndpoints_BCF` (`genericEndpoints_BCF`, then
`exists_halfChart_of_cover_BCF`). This file gives the same two theorems from the inline form of the
endpoint conditions (S-CLEAN G2, `exists_halfChart_of_cover_inline_SCL`), the two conditions being
read off `ends_distinct` directly. The old module no longer has a consumer here.

* `BoundarySlimChartIntervals_BIFc.endpoints_inline_BCF`: `ends_distinct` ⟹ the two inline
  conditions;
* `BoundarySlimChartIntervals_BIFc.exists_arcs_inline_BCF`: the arc decomposition of `Ki.K₃`
  (finitely many smooth regular disjoint arcs, no loops — G0);
* `exists_compactSlimChoiceV2_of_intervals_inline_BCF01`: G1b, strengthened to `Kc.K₃ = Ki.K₃`.
-/

set_option autoImplicit false

noncomputable section

open Set Function Metric Bundle Manifold Filter Topology
open scoped ContDiff Manifold Topology ENNReal
open DifferentialGeometry.Topology.Ehresmann DifferentialGeometry.Topology.Manifold
open DifferentialGeometry.Geometry.Riemannian GC.MetricGeometry
open DifferentialGeometry GC.Endpoint DifferentialGeometry.Geometry.Hyperbolic
open DifferentialGeometry.Analysis DifferentialGeometry.Topology

namespace DifferentialGeometry.Geometry.Collapse

local notation "E3" => EuclideanSpace ℝ (Fin 3)

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace

attribute [local instance] nezero_finrank_euclideanThree_LC87

attribute [local instance] interiorCharted_BDRY1 interiorManifold_BDRY1
  connectedSpace_interior_BDRY2

variable {K : ℕ} {A : ℝ → ℝ} {β : ℕ → ℝ}
  {βd εN Λ w Δ σs σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs ζ Λz θ : ℝ}
  {W : CompactCarrier.{0}} [ConnectedSpace W.Carrier] {g : SmoothRiemannianMetric W.model W.Carrier}
  {δn : ℝ} {n : ℕ} {B : NearlyCuspidalBoundary W g K δn}
  {oM : ManifoldOrientation 𝓘(ℝ, E3) (W.pieceInterior ⊤) 3}
  {S : BoundarySupply K A β βd εN Λ w Δ σs σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs ζ Λz θ W g
    δn n B oM} {Φ : BoundaryInteriorSlots_BIF S} {D : BoundaryAugmentedData S Φ} {Kj : ℕ}
  {Ξ Sg eg c cw : Fin 3 → ℝ} {bcut bder κ : ℝ}
  {C : BoundaryGaf02Chain D Kj Ξ Sg eg c cw bcut bder κ}

namespace BoundarySlimChartIntervals_BIFc

variable {Bs : BoundaryGaf02BasesV2 C} {ι : Type*} {At : GraphAtlas1_BCF ι (Bs.base 2)}
  (Ki : BoundarySlimChartIntervals_BIFc Bs At)

/-- **The two endpoint conditions, inline**: the pairwise distinct endpoints of a chart-interval
`K₃` (`ends_distinct`) give distinct ends of each interval and no shared end of two intervals. -/
theorem endpoints_inline_BCF :
    (∀ r, At.param (Ki.chart r) (Ki.lo r) ≠ At.param (Ki.chart r) (Ki.hi r)) ∧
      ∀ r s, r ≠ s → ∀ p ∈ ({At.param (Ki.chart r) (Ki.lo r), At.param (Ki.chart r) (Ki.hi r)} :
          Set _), p ∉ ({At.param (Ki.chart s) (Ki.lo s), At.param (Ki.chart s) (Ki.hi s)} :
          Set _) := by
  have hinj := Ki.ends_distinct
  refine ⟨fun r h => ?_, fun r s hrs p hp hp' => ?_⟩
  · have := @hinj (r, false) (r, true) (by simpa using h)
    simp at this
  · have hp1 : ∃ x : Bool, p = At.param (Ki.chart r) (if x then Ki.hi r else Ki.lo r) := by
      rcases hp with rfl | rfl
      · exact ⟨false, rfl⟩
      · exact ⟨true, rfl⟩
    have hp2 : ∃ y : Bool, p = At.param (Ki.chart s) (if y then Ki.hi s else Ki.lo s) := by
      rcases hp' with rfl | rfl
      · exact ⟨false, rfl⟩
      · exact ⟨true, rfl⟩
    obtain ⟨x, hx⟩ := hp1
    obtain ⟨y, hy⟩ := hp2
    have := @hinj (r, x) (s, y) (hx.symm.trans hy)
    exact hrs (congrArg Prod.fst this)

/-- **The arc decomposition of a chart-interval `K₃`** on the boundary route (inline endpoint
conditions): finitely many smooth regular pairwise disjoint arcs in `B₃` whose union is exactly
`Ki.K₃`; the shared kernel's loops are excluded by G0. -/
theorem exists_arcs_inline_BCF (WF : BoundaryWholeFiberSpecV2 C Bs) :
    ∃ Dm : SmoothCompactOneDomain_BCF (Bs.base 2), Dm.carrier = Ki.K₃ ∧ Dm.l = 0 ∧
      (⋃ k, Dm.arc k '' Icc 0 1) = Ki.K₃ := by
  obtain ⟨hdist, hdisj⟩ := Ki.endpoints_inline_BCF
  have hch : ∀ y : Ki.K₃, ∃ d : HalfChart_BCF (Bs.base 2) Ki.K₃, y.1 ∈ d.O := fun y =>
    At.exists_halfChart_of_cover_inline_SCL (fun r => ⟨Ki.lo_lt_hi r, Ki.Icc_subset r⟩) hdist hdisj
      y.2
  choose ch hch using hch
  obtain ⟨Dm, hDm⟩ := exists_smoothCompactOneDomain_BCF ⟨ch, hch⟩ Ki.slimCut_BIFc.isCompact
  clear ch hch hdist hdisj
  have hl : Dm.l = 0 := by
    by_contra hl
    obtain ⟨j⟩ : Nonempty (Fin Dm.l) := ⟨⟨0, Nat.pos_of_ne_zero hl⟩⟩
    have hsub : range (Dm.loop j) ⊆ Bs.base 2 := fun y hy =>
      Dm.subset_base (Dm.carrier_eq ▸ Or.inr (mem_iUnion.mpr ⟨j, hy⟩))
    exact Bs.no_closed_slimBase_component_BCF01 WF hsub (Dm.loop_range_isCompact_BCF j)
      (Dm.loop_range_nonempty_BCF j) (Dm.loop_relOpen j)
  refine ⟨Dm, hDm, hl, ?_⟩
  have hloops : (⋃ j, range (Dm.loop j)) = ∅ := by
    refine iUnion_eq_empty.mpr fun j => ?_
    exact absurd j.2 (by omega)
  have h1 : Dm.carrier = ⋃ k, Dm.arc k '' Icc 0 1 := by
    rw [Dm.carrier_eq, hloops]
    exact Set.union_empty _
  exact h1.symm.trans hDm

end BoundarySlimChartIntervals_BIFc

/-- **G1b BCF01 (text v3), strengthened, without the named `Prop`**: a chart-interval `K₃` is the
union of finitely many disjoint smooth arcs of a compact slim choice with the SAME `K₃`, hence the
same slim piece. -/
theorem exists_compactSlimChoiceV2_of_intervals_inline_BCF01 {Bs : BoundaryGaf02BasesV2 C}
    (WF : BoundaryWholeFiberSpecV2 C Bs) {ι : Type*} {At : GraphAtlas1_BCF ι (Bs.base 2)}
    (Ki : BoundarySlimChartIntervals_BIFc Bs At) :
    ∃ Kc : BoundaryCompactSlimChoiceV2 Bs,
      Kc.K₃ = Ki.K₃ ∧ Kc.piece = Bs.slimPieceOf_BIFc Ki.K₃ := by
  obtain ⟨Dm, hDm, -, hU⟩ := Ki.exists_arcs_inline_BCF WF
  refine ⟨{
    arcCount := Dm.m
    arc := Dm.arc
    arc_smooth := Dm.arc_smooth
    arc_injOn := Dm.arc_injOn
    arc_deriv := Dm.arc_deriv
    arc_disjoint := Dm.arc_disjoint
    arc_subset_base := fun k y hy =>
      Dm.subset_base (Dm.carrier_eq ▸ Or.inl (mem_iUnion.mpr ⟨k, hy⟩))
    slabs_subset := hU ▸ Ki.slabs_subset
    faces_subset := hU ▸ Ki.faces_subset
    piece_regular := hU ▸ Ki.piece_regular }, hU, ?_⟩
  change Bs.source 2 ∩ C.stageMap 2 ⁻¹' ((⋃ k, Dm.arc k '' Icc 0 1) ∩ Bs.slimBaseDomain_BIFc) =
    Bs.slimPieceOf_BIFc Ki.K₃
  rw [hU]
  rfl

end DifferentialGeometry.Geometry.Collapse
