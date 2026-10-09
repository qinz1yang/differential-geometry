import DifferentialGeometry.Geometry.Collapse.LocalExport.BoundarySlimCutFacesBCF
import DifferentialGeometry.Topology.Manifold.OneManifold.CompactOneManifoldChoiceBCFApplications

/-!
# BCF01 G1b on the v2 objects: chart intervals ⟹ disjoint smooth arcs with the SAME `K₃`
(lane B-BCF134; text v3 §G G1b, review 74 D74-9)

Text v3 G1b `exists_compactSlimChoiceV2_of_intervals_BCF01`: a chart-interval `K₃`
(`BoundarySlimChartIntervals_BIFc Bs At`, pairwise distinct endpoints) is replaced by finitely many
disjoint smooth arcs. Proved here with the SAME set: the shared kernel's core
(`exists_smoothCompactOneDomain_BCF`, half charts from `exists_halfChart_of_cover_BCF`) writes the
interval union as finitely many smooth regular arcs AND loops; the loops are excluded on the boundary
route by G0 (`no_closed_slimBase_component_BCF01`: a loop range would be a nonempty compact relatively
open subset of `B₃`). Hence `Kc.K₃ = Ki.K₃` and the slim piece, `M₂`, … are unchanged; the
`D₃`-neighbourhood and the finiteness of `∂D₃` of the frozen docstring are not needed, nor is `Z`
(verbatim frozen form kept as an `example`).

* `BoundarySlimChartIntervals_BIFc.genericEndpoints_BCF`: distinct endpoints in the kernel's form;
* `BoundarySlimChartIntervals_BIFc.exists_arcs_BCF`: the arc decomposition of `Ki.K₃`;
* `exists_compactSlimChoiceV2_of_intervals_BCF01` (G1b, strengthened to `Kc.K₃ = Ki.K₃`).
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

section ProductChart

variable {EM HM M : Type*} [NormedAddCommGroup EM] [NormedSpace ℝ EM] [TopologicalSpace HM]
  [TopologicalSpace M] [ChartedSpace HM M] {IM : ModelWithCorners ℝ EM HM}
  {EF HF F : Type*} [NormedAddCommGroup EF] [NormedSpace ℝ EF] [TopologicalSpace HF]
  [TopologicalSpace F] [ChartedSpace HF F] {IF : ModelWithCorners ℝ EF HF}
  {H : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H]

/-- **Local openness from a product chart**: if `f` has a smooth local product chart over `B` at
`y = f p` with `p ∈ U ⊆ X`, `U` open, then some open `O ∋ y` has `O ∩ B ⊆ f '' U`. -/
theorem SmoothProductChartAt_BIFc.exists_relOpen_subset_image_BCF {k : ℕ} {f : M → H} {X : Set M}
    {B : Set H} {y : H} (h : SmoothProductChartAt_BIFc IM IF (F := F) k f X B y) {U : Set M}
    (hUX : U ⊆ X) (hU : IsOpen U) {p : M} (hpU : p ∈ U) (hpy : f p = y) :
    ∃ O : Set H, IsOpen O ∧ y ∈ O ∧ O ∩ B ⊆ f '' U := by
  obtain ⟨σ, φ, O, h0, -, hσ, -, hO, hrσ, hφ, hrφ, hf⟩ := h
  have hpφ : p ∈ range φ := hrφ ▸ ⟨hUX hpU, 0, by rw [h0, hpy]⟩
  obtain ⟨⟨x₀, z₀⟩, hx₀⟩ := hpφ
  have hx0 : x₀ = 0 := hσ.injective (by rw [← hf x₀ z₀, hx₀, hpy, h0])
  subst hx0
  have hpre : IsOpen (φ ⁻¹' U) := hU.preimage hφ.isEmbedding.continuous
  obtain ⟨N, Mz, hN, -, hN0, hz₀, hNM⟩ := isOpen_prod_iff.mp hpre 0 z₀ (by
    change φ (0, z₀) ∈ U
    rw [hx₀]
    exact hpU)
  obtain ⟨G, hG, hGN⟩ := hσ.isInducing.isOpen_iff.mp hN
  refine ⟨G ∩ O, hG.inter hO, ⟨?_, ?_⟩, ?_⟩
  · have : (0 : EuclideanSpace ℝ (Fin k)) ∈ σ ⁻¹' G := hGN ▸ hN0
    rw [← h0]
    exact this
  · have : y ∈ B ∩ O := hrσ ▸ ⟨0, h0⟩
    exact this.2
  · rintro w ⟨⟨hwG, hwO⟩, hwB⟩
    obtain ⟨x, hx⟩ : w ∈ range σ := hrσ ▸ ⟨hwB, hwO⟩
    have hxN : x ∈ N := hGN ▸ (show σ x ∈ G by rw [hx]; exact hwG)
    exact ⟨φ (x, z₀), hNM ⟨hxN, hz₀⟩, by rw [hf, hx]⟩

end ProductChart

namespace BoundarySlimChartIntervals_BIFc

variable {Bs : BoundaryGaf02BasesV2 C} {ι : Type*} {At : GraphAtlas1_BCF ι (Bs.base 2)}
  (Ki : BoundarySlimChartIntervals_BIFc Bs At)

/-- The pairwise distinct endpoints of a chart-interval `K₃`, in the shared kernel's form. -/
theorem genericEndpoints_BCF : At.GenericEndpoints_BCF Ki.chart Ki.lo Ki.hi := by
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

/-- **The arc decomposition of a chart-interval `K₃`** on the boundary route: finitely many smooth
regular pairwise disjoint arcs in `B₃` whose union is exactly `Ki.K₃` (the shared kernel's loops are
excluded by G0). -/
theorem exists_arcs_BCF (WF : BoundaryWholeFiberSpecV2 C Bs) :
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
    exact Bs.no_closed_slimBase_component_BCF01 WF hsub (Dm.loop_range_isCompact_BCF j)
      (Dm.loop_range_nonempty_BCF j) (Dm.loop_relOpen j)
  refine ⟨Dm, hDm, hl, ?_⟩
  have hloops : (⋃ j, range (Dm.loop j)) = ∅ := by
    refine iUnion_eq_empty.mpr fun j => ?_
    exact (Fin.elim0 (hl ▸ j))
  rw [← hDm, Dm.carrier_eq, hloops, union_empty]

end BoundarySlimChartIntervals_BIFc

/-- **G1b BCF01 (text v3), strengthened**: a chart-interval `K₃` is the union of finitely many
disjoint smooth arcs of a compact slim choice with the SAME `K₃`, hence the same slim piece. -/
theorem exists_compactSlimChoiceV2_of_intervals_BCF01 {Bs : BoundaryGaf02BasesV2 C}
    (WF : BoundaryWholeFiberSpecV2 C Bs) {ι : Type*} {At : GraphAtlas1_BCF ι (Bs.base 2)}
    (Ki : BoundarySlimChartIntervals_BIFc Bs At) :
    ∃ Kc : BoundaryCompactSlimChoiceV2 Bs, Kc.K₃ = Ki.K₃ ∧ Kc.piece = Bs.slimPieceOf_BIFc Ki.K₃ := by
  obtain ⟨Dm, hDm, -, hU⟩ := Ki.exists_arcs_BCF WF
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

/-- G1b in the conclusion form of text v3 (`Kc.K₃ ⊆ Ki.K₃`; the frozen hypothesis `Z` is not used). -/
example {Bs : BoundaryGaf02BasesV2 C} (WF : BoundaryWholeFiberSpecV2 C Bs)
    {ι : Type} {At : GraphAtlas1_BCF ι (Bs.base 2)}
    (Ki : BoundarySlimChartIntervals_BIFc Bs At) :
    ∃ Kc : BoundaryCompactSlimChoiceV2 Bs, Kc.K₃ ⊆ Ki.K₃ ∧ Kc.piece = Bs.slimPieceOf_BIFc Ki.K₃ := by
  obtain ⟨Kc, hK, hP⟩ := exists_compactSlimChoiceV2_of_intervals_BCF01 WF Ki
  exact ⟨Kc, hK.le, hP⟩

namespace BoundaryWholeFiberSpecV2

variable {Bs : BoundaryGaf02BasesV2 C}

/-- **A4c from the whole-fibre layer**: `f₃|X₃` is a relatively open map onto `B₃` (the slim product
charts of `WF` are local projections). -/
theorem slimStage_relOpen_BCF (WF : BoundaryWholeFiberSpecV2 C Bs) :
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

end BoundaryWholeFiberSpecV2

/-- **Regularity transfer**: an open continuous `f|U` (relatively open onto `Bs`) pulls a set that is
regular in `Bs` back to a set regular in the source. -/
theorem subset_closure_interior_inter_preimage_BCF {X H : Type*} [TopologicalSpace X]
    [TopologicalSpace H] {f : X → H} {U : Set X} {Bs A : Set H} (hU : IsOpen U)
    (hcont : ContinuousOn f U) (hmaps : MapsTo f U Bs)
    (hopen : ∀ V ⊆ U, IsOpen V → ∃ O : Set H, IsOpen O ∧ O ∩ Bs = f '' V)
    (hA : A ⊆ closure (relInterior_BIF Bs A)) :
    U ∩ f ⁻¹' A ⊆ closure (interior (U ∩ f ⁻¹' A)) := by
  rintro x ⟨hxU, hxA⟩
  rw [_root_.mem_closure_iff]
  intro V hV hxV
  obtain ⟨O, hO, hOB⟩ := hopen (V ∩ U) inter_subset_right (hV.inter hU)
  have hfxO : f x ∈ O ∩ Bs := hOB ▸ mem_image_of_mem f ⟨hxV, hxU⟩
  obtain ⟨y, hyO, hyA⟩ := _root_.mem_closure_iff.mp (hA hxA) O hO hfxO.1
  obtain ⟨hyB, O', hO', hyO', hO'A⟩ := mem_relInterior_iff_BCF.mp hyA
  obtain ⟨v, ⟨hvV, hvU⟩, rfl⟩ : y ∈ f '' (V ∩ U) := hOB ▸ ⟨hyO, hyB⟩
  refine ⟨v, hvV, ?_⟩
  rw [mem_interior]
  refine ⟨V ∩ (U ∩ f ⁻¹' O'), fun z hz => ⟨hz.2.1, hO'A ⟨hz.2.2, hmaps hz.2.1⟩⟩,
    hV.inter (hcont.isOpen_inter_preimage hU hO'), hvV, hvU, hyO'⟩

/-- **The slim piece of a compact `K` is regular when `K ∩ D₃` is regular in `B₃`** (the piece
regularity of BCF01 (K), from A4c, saturation `Z` and properness). -/
theorem BoundaryActualZeroDomains_BIFc.slimPiece_regular_BCF {Bs : BoundaryGaf02BasesV2 C}
    (WF : BoundaryWholeFiberSpecV2 C Bs) (Z : BoundaryActualZeroDomains_BIFc C Bs)
    {Kset : Set (BoundaryAmbient_BIF S.IntTag_BAUGA (Fin S.packet.cusp.count))} (hK : IsCompact Kset)
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
    (Bs.continuousOn_stageMap_BCF 2) hmaps WF.slimStage_relOpen_BCF hreg

end DifferentialGeometry.Geometry.Collapse
