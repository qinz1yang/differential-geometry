import DifferentialGeometry.Geometry.Collapse.LocalExport.BoundaryCompactSlimFacesBCF

/-!
# BCF01 / ZSP04: no closed component of an open-stage base (lane B-BCF134; D69 on G1)

Blueprint `master207B.tex`, BCF01 (B:9713–9715): "A closed zero or slim component would be open and
closed in connected `M` and lie in its interior; in the present nonempty-boundary case it cannot
occur." Review 69 / lead 14:2x: the shared `K₃` kernel keeps interval AND circle classes; the
binding excludes the closed ones. This file proves the exclusion.

* `no_clopen_compact_base_part_BCF` (generic kernel): `f` continuous on an open `U ≠ univ` of a
  connected Hausdorff space, `f(U) ⊆ Bs`, `f|U` proper over `Bs`; then no nonempty compact
  relatively open `Γ ⊆ Bs` meets `f(U)` (its preimage `U ∩ f⁻¹Γ` would be clopen and nonempty).
* `BoundaryGaf02Bases.source_ne_univ_BCF`: every source domain misses a boundary point
  (`source_buffered`: `X_j ⊆ {D > 10}`; `count_pos`: `∂W ≠ ∅`).
* `BoundaryGaf02Bases.no_closed_base_component_BCF` (binding, circle and slim stages): no nonempty
  compact relatively open subset of `B_st`, `st ≠ 1` — in particular no circle component of the
  slim base `B₃` and no closed component of the circle base `B₁`.
-/

set_option autoImplicit false

noncomputable section

open Set Function Metric Bundle Manifold Filter
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

/-- **No clopen compact part of the base** (generic): for `f` continuous on an open `U ≠ univ` of a
connected Hausdorff space with `f(U) ⊆ Bs` and `f|U` proper over `Bs`, a compact relatively open
`Γ ⊆ Bs` has empty preimage in `U`. -/
theorem no_clopen_compact_base_part_BCF {X H : Type*} [TopologicalSpace X] [T2Space X]
    [ConnectedSpace X] [TopologicalSpace H] (f : X → H) (U : Set X) (Bs : Set H) (hU : IsOpen U)
    (hUne : U ≠ univ) (hcont : ContinuousOn f U) (hmaps : MapsTo f U Bs)
    (hproper : ∀ Kc ⊆ Bs, IsCompact Kc → IsCompact (U ∩ f ⁻¹' Kc)) {Γ : Set H} (hΓB : Γ ⊆ Bs)
    (hΓc : IsCompact Γ) (hΓo : ∃ O : Set H, IsOpen O ∧ O ∩ Bs = Γ) :
    U ∩ f ⁻¹' Γ = ∅ := by
  by_contra hne
  obtain ⟨O, hO, hOΓ⟩ := hΓo
  have heq : U ∩ f ⁻¹' Γ = U ∩ f ⁻¹' O := by
    ext x
    constructor
    · rintro ⟨hxU, hxΓ⟩
      exact ⟨hxU, (hOΓ.symm ▸ hxΓ : f x ∈ O ∩ Bs).1⟩
    · rintro ⟨hxU, hxO⟩
      exact ⟨hxU, hOΓ ▸ ⟨hxO, hmaps hxU⟩⟩
  have hclopen : IsClopen (U ∩ f ⁻¹' Γ) :=
    ⟨(hproper Γ hΓB hΓc).isClosed, heq ▸ hcont.isOpen_inter_preimage hU hO⟩
  rcases isClopen_iff.mp hclopen with h | h
  · exact hne h
  · exact hUne (eq_univ_of_univ_subset (h ▸ inter_subset_left))

variable {K : ℕ} {A : ℝ → ℝ} {β : ℕ → ℝ}
  {βd εN Λ w Δ σs σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs ζ Λz θ : ℝ}
  {W : CompactCarrier.{0}} [ConnectedSpace W.Carrier] {g : SmoothRiemannianMetric W.model W.Carrier}
  {δn : ℝ} {n : ℕ} {B : NearlyCuspidalBoundary W g K δn}
  {oM : ManifoldOrientation 𝓘(ℝ, E3) (W.pieceInterior ⊤) 3}
  {S : BoundarySupply K A β βd εN Λ w Δ σs σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs ζ Λz θ W g
    δn n B oM} {Φ : BoundaryInteriorSlots_BIF S} {D : BoundaryAugmentedData S Φ} {Kj : ℕ}
  {Ξ Sg eg c cw : Fin 3 → ℝ} {bcut bder κ : ℝ}
  {C : BoundaryGaf02Chain D Kj Ξ Sg eg c cw bcut bder κ}

/-- **Every source domain misses `∂W`**: `X_st ⊆ {D > 10}` and `∂W ≠ ∅`. -/
theorem BoundaryGaf02Bases.source_ne_univ_BCF (Bs : BoundaryGaf02Bases C)
    (WF : BoundaryWholeFiberSpec C Bs) (st : Fin 3) : Bs.source st ≠ univ := by
  intro h
  obtain ⟨x, hx⟩ := (B.connected ⟨0, B.count_pos⟩).nonempty
  have hxb : x ∈ W.model.boundary W.Carrier := B.covers ▸ mem_iUnion.mpr ⟨_, hx⟩
  have hlt := WF.source_buffered st (h ▸ mem_univ x)
  have hle : distanceToBoundary W g x ≤ 0 := by
    unfold distanceToBoundary
    calc (⨅ q : W.model.boundary W.Carrier, riemannianEDistOf g x q) ≤
          riemannianEDistOf g x (⟨x, hxb⟩ : W.model.boundary W.Carrier) := iInf_le _ _
      _ = 0 := riemannianEDistOf_self _ _
  exact absurd (hlt.trans_le hle) (by simp)

/-- **No closed component of the circle or slim base** (BCF01, B:9713–9715): a nonempty compact
relatively open subset of `B_st` (`st ≠ 1`) does not exist; in particular `B₃` has no circle
component. -/
theorem BoundaryGaf02Bases.no_closed_base_component_BCF (Bs : BoundaryGaf02Bases C)
    (WF : BoundaryWholeFiberSpec C Bs) {st : Fin 3} (hst : st ≠ 1)
    {Γ : Set (BoundaryAmbient_BIF S.IntTag_BAUGA (Fin S.packet.cusp.count))} (hΓB : Γ ⊆ Bs.base st)
    (hΓc : IsCompact Γ) (hΓo : ∃ O, IsOpen O ∧ O ∩ Bs.base st = Γ) : Γ = ∅ := by
  have hmaps : MapsTo (C.stageMap st) (Bs.source st) (Bs.base st) :=
    fun p hp => Bs.image_eq st ▸ mem_image_of_mem _ hp
  have h0 := no_clopen_compact_base_part_BCF (C.stageMap st) (Bs.source st) (Bs.base st)
    (Bs.isOpen_source st hst) (Bs.source_ne_univ_BCF WF st) (Bs.continuousOn_stageMap_BCF st)
    hmaps (Bs.proper st) hΓB hΓc hΓo
  refine eq_empty_of_forall_notMem fun y hy => ?_
  obtain ⟨p, hp, rfl⟩ : y ∈ C.stageMap st '' Bs.source st := (Bs.image_eq st).symm ▸ hΓB hy
  exact (eq_empty_iff_forall_notMem.mp h0) p ⟨hp, hy⟩

end DifferentialGeometry.Geometry.Collapse
