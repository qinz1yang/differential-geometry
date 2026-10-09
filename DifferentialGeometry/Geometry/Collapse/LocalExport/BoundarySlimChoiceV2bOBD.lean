import DifferentialGeometry.Geometry.Collapse.LocalExport.BoundarySlimChartIntervalsBCFApplications
import DifferentialGeometry.Geometry.Collapse.LocalExport.BoundaryInterfaceFibresV2b
import DifferentialGeometry.Geometry.Collapse.LocalExport.BoundaryActualZeroDomainsBGR

/-!
# BCF01's compact slim choice on the whole-fibre layer v2b (lane O-BD1)

The BCF01 producer `exists_boundaryCompactSlimChoiceV2_BCF01` (lane S-BCF134c) takes the v2
whole-fibre layer `BoundaryWholeFiberSpecV2`, whose buffer `{D > 10}` is not available for the
actual bases (named revision for text v3.2: v2b, `{D > 5}`). The v2 layer enters only through the
slim product charts (`slim_chart`: graph atlas of `B₃`, relative openness of `f₃|X₃`) and through
`source ≠ univ` (a boundary point has `D = 0`), both of which hold on v2b. This module ports the
producer chain to v2b, proofs unchanged:

* `BoundaryWholeFiberSpecV2b.slimBase_graphAtlas_OBD`, `slimStage_relOpen_OBD`;
* `BoundaryGaf02BasesV2.source_ne_univ_OBD`, `no_closed_base_component_OBD`,
  `no_closed_slimBase_component_OBD` (G0 on v2b);
* `BoundarySlimChartIntervals_BIFc.exists_arcs_OBD`, `exists_compactSlimChoiceV2_of_intervals_OBD`
  (G1b on v2b);
* `BoundaryActualZeroDomains_BIFc.slimPiece_regular_OBD`;
* `BoundaryGaf02ChainE.slimBaseDomain_regular_OBD`, `exists_slimChartIntervals_OBD` (G1a on v2b,
  `f₃(∂M₁ ∩ X₃)` finite by `frontier_M₁_image_finite_V2b_BGR`),
  **`exists_boundaryCompactSlimChoiceV2_OBD`** (G1 on v2b).
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

section Generic

variable {S : BoundarySupply K A β βd εN Λ w Δ σs σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs ζ Λz
    θ W g δn n B oM} {Φ : BoundaryInteriorSlots_BIF S} {D : BoundaryAugmentedData S Φ} {Kj : ℕ}
  {Ξ Sg eg c cw : Fin 3 → ℝ} {bcut bder κ : ℝ}
  {C : BoundaryGaf02Chain D Kj Ξ Sg eg c cw bcut bder κ}

namespace BoundaryWholeFiberSpecV2b

variable {Bs : BoundaryGaf02BasesV2 C}

/-- **A graph atlas of the slim base** from the v2b whole-fibre layer. -/
theorem slimBase_graphAtlas_OBD (WF : BoundaryWholeFiberSpecV2b C Bs) :
    Nonempty (GraphAtlas1_BCF (Bs.base 2) (Bs.base 2)) := by
  refine exists_graphAtlas_of_immersions_BCF fun y hy => ?_
  rcases WF.slim_chart y hy with h | h
  · exact h.exists_base_immersion_BCF
  · exact h.exists_base_immersion_BCF

/-- **A4c from the v2b layer**: `f₃|X₃` is a relatively open map onto `B₃`. -/
theorem slimStage_relOpen_OBD (WF : BoundaryWholeFiberSpecV2b C Bs) :
    ∀ U ⊆ Bs.source 2, IsOpen U → ∃ O : Set (BoundaryAmbient_BIF S.IntTag_BAUGA
      (Fin S.packet.cusp.count)), IsOpen O ∧ O ∩ Bs.base 2 = C.stageMap 2 '' U := by
  intro U hUX hU
  have hloc : ∀ y ∈ C.stageMap 2 '' U, ∃ O : Set (BoundaryAmbient_BIF S.IntTag_BAUGA
      (Fin S.packet.cusp.count)), IsOpen O ∧ y ∈ O ∧ O ∩ Bs.base 2 ⊆ C.stageMap 2 '' U := by
    rintro y ⟨p, hpU, rfl⟩
    have hyB : C.stageMap 2 p ∈ Bs.base 2 := Bs.image_eq 2 ▸ mem_image_of_mem _ (hUX hpU)
    rcases WF.slim_chart _ hyB with h | h
    · exact h.exists_relOpen_subset_image_BCF hUX hU hpU rfl
    · exact h.exists_relOpen_subset_image_BCF hUX hU hpU rfl
  choose O hO hyO hOU using hloc
  refine ⟨⋃ y, ⋃ hy : y ∈ C.stageMap 2 '' U, O y hy,
    isOpen_iUnion fun y => isOpen_iUnion fun hy => hO y hy, ?_⟩
  ext w
  constructor
  · rintro ⟨hw, hwB⟩
    obtain ⟨y, hy, hwy⟩ := mem_iUnion₂.mp hw
    exact hOU y hy ⟨hwy, hwB⟩
  · intro hw
    obtain ⟨p, hpU, rfl⟩ := hw
    exact ⟨mem_iUnion₂.mpr ⟨_, ⟨p, hpU, rfl⟩, hyO _ ⟨p, hpU, rfl⟩⟩,
      Bs.image_eq 2 ▸ mem_image_of_mem _ (hUX hpU)⟩

end BoundaryWholeFiberSpecV2b

namespace BoundaryGaf02BasesV2

variable (Bs : BoundaryGaf02BasesV2 C)

/-- **Every source domain misses `∂W`** on v2b: `X_st ⊆ {D > 5}` and `∂W ≠ ∅`. -/
theorem source_ne_univ_OBD (WF : BoundaryWholeFiberSpecV2b C Bs) (st : Fin 3) :
    Bs.source st ≠ univ := by
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

/-- **No closed component of an open-stage base** (`st ≠ 1`) on v2b. -/
theorem no_closed_base_component_OBD (WF : BoundaryWholeFiberSpecV2b C Bs) {st : Fin 3}
    (hst : st ≠ 1)
    {Γ : Set (BoundaryAmbient_BIF S.IntTag_BAUGA (Fin S.packet.cusp.count))} (hΓB : Γ ⊆ Bs.base st)
    (hΓc : IsCompact Γ) (hΓo : ∃ O, IsOpen O ∧ O ∩ Bs.base st = Γ) : Γ = ∅ := by
  have hmaps : MapsTo (C.stageMap st) (Bs.source st) (Bs.base st) :=
    fun p hp => Bs.image_eq st ▸ mem_image_of_mem _ hp
  have h0 := no_clopen_compact_base_part_BCF (C.stageMap st) (Bs.source st) (Bs.base st)
    (Bs.isOpen_source st hst) (Bs.source_ne_univ_OBD WF st) (Bs.continuousOn_stageMap_BCF st)
    hmaps (Bs.proper st) hΓB hΓc hΓo
  refine eq_empty_of_forall_notMem fun y hy => ?_
  obtain ⟨p, hp, rfl⟩ : y ∈ C.stageMap st '' Bs.source st := (Bs.image_eq st).symm ▸ hΓB hy
  exact (eq_empty_iff_forall_notMem.mp h0) p ⟨hp, hy⟩

/-- **G0 on v2b**: no nonempty compact relatively open subset of `B₃`. -/
theorem no_closed_slimBase_component_OBD (WF : BoundaryWholeFiberSpecV2b C Bs)
    {Y : Set (BoundaryAmbient_BIF S.IntTag_BAUGA (Fin S.packet.cusp.count))} (hYB : Y ⊆ Bs.base 2)
    (hYc : IsCompact Y) (hYne : Y.Nonempty) :
    ¬ ∃ O : Set (BoundaryAmbient_BIF S.IntTag_BAUGA (Fin S.packet.cusp.count)),
      IsOpen O ∧ O ∩ Bs.base 2 = Y := fun hYo =>
  hYne.ne_empty (Bs.no_closed_base_component_OBD WF (st := 2) (by decide) hYB hYc hYo)

end BoundaryGaf02BasesV2

namespace BoundarySlimChartIntervals_BIFc

variable {Bs : BoundaryGaf02BasesV2 C} {ι : Type*} {At : GraphAtlas1_BCF ι (Bs.base 2)}
  (Ki : BoundarySlimChartIntervals_BIFc Bs At)

/-- **The arc decomposition of a chart-interval `K₃`** on v2b (loops excluded by G0 on v2b). -/
theorem exists_arcs_OBD (WF : BoundaryWholeFiberSpecV2b C Bs) :
    ∃ Dm : SmoothCompactOneDomain_BCF (Bs.base 2), Dm.carrier = Ki.K₃ ∧ Dm.l = 0 ∧
      (⋃ k, Dm.arc k '' Icc 0 1) = Ki.K₃ := by
  have hch : ∀ y : Ki.K₃, ∃ d : HalfChart_BCF (Bs.base 2) Ki.K₃, y.1 ∈ d.O := fun y =>
    At.exists_halfChart_of_cover_BCF (fun r => ⟨Ki.lo_lt_hi r, Ki.Icc_subset r⟩)
      Ki.genericEndpoints_BCF y.2
  choose ch hch using hch
  obtain ⟨Dm, hDm⟩ := exists_smoothCompactOneDomain_BCF ⟨ch, hch⟩ Ki.slimCut_BIFc.isCompact
  have hl : Dm.l = 0 := by
    by_contra hl
    obtain ⟨j⟩ : Nonempty (Fin Dm.l) := ⟨⟨0, Nat.pos_of_ne_zero hl⟩⟩
    have hsub : range (Dm.loop j) ⊆ Bs.base 2 := fun y hy =>
      Dm.subset_base (Dm.carrier_eq ▸ Or.inr (mem_iUnion.mpr ⟨j, hy⟩))
    exact Bs.no_closed_slimBase_component_OBD WF hsub (Dm.loop_range_isCompact_BCF j)
      (Dm.loop_range_nonempty_BCF j) (Dm.loop_relOpen j)
  refine ⟨Dm, hDm, hl, ?_⟩
  have hloops : (⋃ j, range (Dm.loop j)) = ∅ := by
    refine iUnion_eq_empty.mpr fun j => ?_
    exact (Fin.elim0 (hl ▸ j))
  rw [← hDm, Dm.carrier_eq, hloops, union_empty]

end BoundarySlimChartIntervals_BIFc

/-- **G1b on v2b**: a chart-interval `K₃` is the union of finitely many disjoint smooth arcs of a
compact slim choice with the SAME `K₃`, hence the same slim piece. -/
theorem exists_compactSlimChoiceV2_of_intervals_OBD {Bs : BoundaryGaf02BasesV2 C}
    (WF : BoundaryWholeFiberSpecV2b C Bs) {ι : Type*} {At : GraphAtlas1_BCF ι (Bs.base 2)}
    (Ki : BoundarySlimChartIntervals_BIFc Bs At) :
    ∃ Kc : BoundaryCompactSlimChoiceV2 Bs, Kc.K₃ = Ki.K₃ ∧
      Kc.piece = Bs.slimPieceOf_BIFc Ki.K₃ := by
  obtain ⟨Dm, hDm, -, hU⟩ := Ki.exists_arcs_OBD WF
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

/-- **The slim piece of a compact `K` is regular when `K ∩ D₃` is regular in `B₃`** (v2b). -/
theorem BoundaryActualZeroDomains_BIFc.slimPiece_regular_OBD {Bs : BoundaryGaf02BasesV2 C}
    (WF : BoundaryWholeFiberSpecV2b C Bs) (Z : BoundaryActualZeroDomains_BIFc C Bs)
    {Kset : Set (BoundaryAmbient_BIF S.IntTag_BAUGA (Fin S.packet.cusp.count))}
    (hK : IsCompact Kset)
    (hKB : Kset ⊆ Bs.base 2)
    (hreg : Kset ∩ Bs.slimBaseDomain_BIFc ⊆
      closure (relInterior_BIF (Bs.base 2) (Kset ∩ Bs.slimBaseDomain_BIFc))) :
    closure (interior (Bs.slimPieceOf_BIFc Kset)) = Bs.slimPieceOf_BIFc Kset := by
  have hmaps : MapsTo (C.stageMap 2) (Bs.source 2) (Bs.base 2) :=
    fun p hp => Bs.image_eq 2 ▸ mem_image_of_mem _ hp
  have hclosed : IsClosed (Bs.slimPieceOf_BIFc Kset) := by
    have heq : Bs.slimPieceOf_BIFc Kset = (Bs.source 2 ∩ C.stageMap 2 ⁻¹' Kset) ∩ C.M₁_BIFc := by
      ext q
      constructor
      · intro hq
        exact ⟨⟨hq.1, hq.2.1⟩, Z.slimPieceOf_subset_M₁_BIF Kset hq⟩
      · rintro ⟨⟨hqX, hqK⟩, hqM⟩
        exact ⟨hqX, hqK, q, ⟨hqM, hqX⟩, rfl⟩
    rw [heq]
    exact ((Bs.proper 2 Kset hKB hK).inter_right C.isClosed_M₁_BCF).isClosed
  refine Subset.antisymm ((closure_mono interior_subset).trans hclosed.closure_subset) ?_
  exact subset_closure_interior_inter_preimage_BCF (Bs.isOpen_source 2 (by decide))
    (Bs.continuousOn_stageMap_BCF 2) hmaps WF.slimStage_relOpen_OBD hreg

end Generic

variable {S : BoundarySupply K A β βd εN Λ w Δ σs σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs ζ Λz
    θ W g δn n B oM} {Γ Sg eg : Fin 3 → ℝ}
  {DP : BoundaryAugmentedDataPV3 S (actualSlotsV2_BAUGD S) Γ Sg eg} {Kj : ℕ}
  {Ξ c cw : Fin 3 → ℝ} {bcut bder κ cadj : ℝ}

namespace BoundaryGaf02ChainE

variable (C : BoundaryGaf02ChainE DP Kj Ξ c cw bcut bder κ cadj)

/-- **`D₃` is regular in `B₃`** on v2b: `D₃ ⊆ cl(int_{B₃} D₃)`. -/
theorem slimBaseDomain_regular_OBD {Bs : BoundaryGaf02BasesV2 C.toChain}
    (WF : BoundaryWholeFiberSpecV2b C.toChain Bs) {rd : ℝ} (hrd : 0 < rd) (hrd4 : rd < 1 / 10000)
    (hrdc : 20 * (c 2 + 1) * rd < 1 / 1000000)
    (hprem : 1000 * δn ^ 2 < w / (2 * (1 + 2 * Λ⁻¹) ^ 3) * min (1 / 2) (rd / 4) ^ 2)
    (hθ : θ < 1 / 100) :
    Bs.slimBaseDomain_BIFc ⊆ closure (relInterior_BIF (Bs.base 2) Bs.slimBaseDomain_BIFc) :=
  image_subset_closure_relInterior_BCF (Bs.isOpen_source 2 (by decide))
    (Bs.continuousOn_stageMap_BCF 2) WF.slimStage_relOpen_OBD
    (C.M₁_subset_closure_interior_BCF hrd hrd4 hrdc hprem hθ)

/-- **G1a on v2b, chart intervals**: over ANY graph atlas `At` of `B₃`, finitely many closed chart
intervals with pairwise distinct endpoints, (K) and a regular slim piece. Premises: `εr < 1/2` and
E4's (the finiteness of `f₃(∂M₁ ∩ X₃)`, F4c / F5 / F5z on v2b). -/
theorem exists_slimChartIntervals_OBD {Bs : BoundaryGaf02BasesV2 C.toChain}
    (WF : BoundaryWholeFiberSpecV2b C.toChain Bs) (Z : BoundaryActualZeroDomains_BIFc C.toChain Bs)
    (hεr : εr < 1 / 2) {rd : ℝ} (hrd : 0 < rd) (hrd4 : rd < 1 / 10000)
    (hrdc : 20 * (c 2 + 1) * rd < 1 / 1000000)
    (hprem : 1000 * δn ^ 2 < w / (2 * (1 + 2 * Λ⁻¹) ^ 3) * min (1 / 2) (rd / 4) ^ 2)
    (hθ : θ < 1 / 100) {ι : Type*} (At : GraphAtlas1_BCF ι (Bs.base 2)) :
    Nonempty (BoundarySlimChartIntervals_BIFc Bs At) := by
  have hfin := C.frontier_M₁_image_finite_V2b_BGR WF hεr hrd hrd4 hrdc hprem hθ
  have hslab := C.isCompact_slabImage_BCF Bs
  have hKc := hslab.union hfin.isCompact
  have hmaps : MapsTo (C.toChain.stageMap 2) (Bs.source 2) (Bs.base 2) :=
    fun p hp => Bs.image_eq 2 ▸ mem_image_of_mem _ hp
  have hKB : C.toChain.stageMap 2 '' (Subtype.val '' S.slimSlabs_BIF) ∪
      C.toChain.stageMap 2 '' (frontier C.toChain.M₁_BIFc ∩ Bs.source 2) ⊆ Bs.base 2 := by
    refine union_subset ?_ ?_
    · rintro _ ⟨_, ⟨q, ⟨j, hj, h1, h2⟩, rfl⟩, rfl⟩
      exact hmaps (Bs.slim_original_subset q j hj h1 h2)
    · rintro _ ⟨p, hp, rfl⟩
      exact hmaps hp.2
  have hKfront : Bs.slimBaseDomain_BIFc \ relInterior_BIF (Bs.base 2) Bs.slimBaseDomain_BIFc ⊆
      C.toChain.stageMap 2 '' (Subtype.val '' S.slimSlabs_BIF) ∪
        C.toChain.stageMap 2 '' (frontier C.toChain.M₁_BIFc ∩ Bs.source 2) :=
    Z.relFrontier_slimBaseDomain_subset_BCF.trans subset_union_right
  obtain ⟨m, ch, lo, hi, hab, hdist, hdisj, hcpt, hsub, hKint, hreg⟩ :=
    At.exists_cover_union_generic_inline_SCL hKc hKB finite_empty
      (C.slimBaseDomain_regular_OBD WF hrd hrd4 hrdc hprem hθ) hKfront
  refine ⟨{
    count := m
    chart := ch
    lo := lo
    hi := hi
    lo_lt_hi := fun r => (hab r).1
    Icc_subset := fun r => (hab r).2.1
    ends_distinct := ?_
    slabs_subset := fun y hy => hKint (subset_union_left hy)
    faces_subset := fun y hy => hKint (subset_union_right hy)
    piece_regular := Z.slimPiece_regular_OBD WF hcpt hsub hreg }⟩
  rintro ⟨r, x⟩ ⟨r', x'⟩ hxx
  by_cases hrr : r = r'
  · subst hrr
    have hx : x = x' := by
      by_contra hne
      refine hdist r ?_
      cases x <;> cases x' <;> first | exact absurd rfl hne | simpa using hxx | simpa using hxx.symm
    rw [hx]
  · exfalso
    have hmem : At.param (ch r) (if x then hi r else lo r) ∈
        ({At.param (ch r) (lo r), At.param (ch r) (hi r)} : Set _) := by
      cases x <;> simp
    have hmem' : At.param (ch r') (if x' then hi r' else lo r') ∈
        ({At.param (ch r') (lo r'), At.param (ch r') (hi r')} : Set _) := by
      cases x' <;> simp
    have hxx' : At.param (ch r) (if x then hi r else lo r) =
        At.param (ch r') (if x' then hi r' else lo r') := hxx
    exact hdisj r r' hrr _ hmem (by rw [hxx']; exact hmem')

/-- **G1 BCF01 on v2b, composed**: a compact slim choice, from G1a over `B₃`'s own graph atlas and
G1b. Premises: `εr < 1/2` and E4's. -/
theorem exists_boundaryCompactSlimChoiceV2_OBD {Bs : BoundaryGaf02BasesV2 C.toChain}
    (WF : BoundaryWholeFiberSpecV2b C.toChain Bs) (Z : BoundaryActualZeroDomains_BIFc C.toChain Bs)
    (hεr : εr < 1 / 2) {rd : ℝ} (hrd : 0 < rd) (hrd4 : rd < 1 / 10000)
    (hrdc : 20 * (c 2 + 1) * rd < 1 / 1000000)
    (hprem : 1000 * δn ^ 2 < w / (2 * (1 + 2 * Λ⁻¹) ^ 3) * min (1 / 2) (rd / 4) ^ 2)
    (hθ : θ < 1 / 100) :
    Nonempty (BoundaryCompactSlimChoiceV2 Bs) := by
  obtain ⟨At⟩ := WF.slimBase_graphAtlas_OBD
  obtain ⟨Ki⟩ := C.exists_slimChartIntervals_OBD WF Z hεr hrd hrd4 hrdc hprem hθ At
  obtain ⟨Kc, -, -⟩ := exists_compactSlimChoiceV2_of_intervals_OBD WF Ki
  exact ⟨Kc⟩

end BoundaryGaf02ChainE

end DifferentialGeometry.Geometry.Collapse
