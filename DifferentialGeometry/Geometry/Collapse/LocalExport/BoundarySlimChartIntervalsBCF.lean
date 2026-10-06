import DifferentialGeometry.Geometry.Collapse.LocalExport.BoundarySlimSlabsCompactBCF
import DifferentialGeometry.Geometry.Collapse.LocalExport.BoundarySlimFibreEqualityApplicationsBGR
import DifferentialGeometry.Geometry.Collapse.LocalExport.BoundarySlimDomainFrontierBCF
import DifferentialGeometry.Geometry.Collapse.LocalExport.BoundaryInterfaceSlimCutV2
import DifferentialGeometry.Topology.Manifold.OneManifold.GenericEndpointsInline

/-!
# BCF01 G1a: the chart-interval `K₃` over ANY graph atlas of `B₃` (lane S-BCF134c, suffix `_BCF`)

Text v3.1 §G G1a `exists_slimChartIntervals_BCF01`, on the enhanced chain (the frozen `ChainE`
section): over any `GraphAtlas1_BCF ι (Bs.base 2)`, finitely many closed chart intervals with
pairwise distinct endpoints whose union `K₃` contains the images of the original slim slabs and of
`∂M₁ ∩ X₃` in its relative interior and has a regular slim piece. Assembly (blueprint BCF01):

* input (c), compactness of `f₃(slabs)`: `BoundarySupplyCore.isCompact_val_slimSlabs_BCF`
  (original proper slim bundle) + `slim_original_subset` + continuity of `f₃` on `X₃`;
* input (a), `f₃(∂M₁ ∩ X₃)` finite: `frontier_M₁_image_finite_BGR` (F4c + F5 + F5z; carries E4's
  numerical premises `rd`, `hθ`: the lead's named revision v3.2, as F4c / F5 / F5z);
* input (b), `D₃` regular in `B₃`: the removed region `P = Z ∪ C_∂` is closed (zero domains
  compact, cusp cores closed: BCG06), so `M₁ = (int P)ᶜ ⊆ cl(int M₁)`
  (`compl_interior_subset_closure_interior_BCF`); `f₃|X₃` is relatively open (A4c from `WF`), so
  `D₃ = f₃(M₁ ∩ X₃) ⊆ cl(int_{B₃} D₃)` (`image_subset_closure_relInterior_BCF`);
* `hKfront`: `∂_{B₃} D₃ ⊆ f₃(∂M₁ ∩ X₃)` (`relFrontier_slimBaseDomain_subset_BCF`, G14);
* the kernel `exists_cover_union_generic_inline_SCL` (no named `Prop`; AMD) with `Fset = ∅`, then
  `slimPiece_regular_BCF` (G10) for the regular piece.

* `compl_interior_subset_closure_interior_BCF`, `image_subset_closure_relInterior_BCF`: generic;
* `BoundaryGaf02ChainE.isClosed_zeroCuspUnion_BCF`, `M₁_subset_closure_interior_BCF`,
  `slimBaseDomain_regular_BCF`, `isCompact_slabImage_BCF`;
* `BoundaryGaf02ChainE.exists_slimChartIntervals_BCF01` (G1a).
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

/-- **The complement of the interior of a closed set is regular**: for a closed `P`,
`(int P)ᶜ ⊆ cl(int (int P)ᶜ)` (every neighbourhood of a point outside `int P` meets the open set
`Pᶜ ⊆ int (int P)ᶜ`). -/
theorem compl_interior_subset_closure_interior_BCF {X : Type*} [TopologicalSpace X] {P : Set X}
    (hP : IsClosed P) : (interior P)ᶜ ⊆ closure (interior (interior P)ᶜ) := by
  intro p hp
  rw [_root_.mem_closure_iff]
  intro N hN hpN
  by_contra hne
  have hN0 : N ∩ interior (interior P)ᶜ = ∅ := not_nonempty_iff_eq_empty.mp hne
  have hNP : N ⊆ P := by
    intro q hq
    by_contra hqP
    have hq' : q ∈ interior (interior P)ᶜ :=
      mem_interior.mpr ⟨Pᶜ, fun y hy hyi => hy (interior_subset hyi), hP.isOpen_compl, hqP⟩
    exact (eq_empty_iff_forall_notMem.mp hN0) q ⟨hq, hq'⟩
  exact hp (mem_interior.mpr ⟨N, hNP, hN, hpN⟩)

/-- **Regularity of a base domain from regularity of the source** (generic): if `f` is
continuous on an open `U` and maps open subsets of `U` onto relatively open subsets of `Bs`, a
regular `M` (`M ⊆ cl(int M)`) has `f(M ∩ U) ⊆ cl(int_{Bs} f(M ∩ U))`. -/
theorem image_subset_closure_relInterior_BCF {X H : Type*} [TopologicalSpace X] [TopologicalSpace H]
    {f : X → H} {U : Set X} {Bs : Set H} (hU : IsOpen U) (hcont : ContinuousOn f U)
    (hopen : ∀ V ⊆ U, IsOpen V → ∃ O : Set H, IsOpen O ∧ O ∩ Bs = f '' V) {M : Set X}
    (hM : M ⊆ closure (interior M)) :
    f '' (M ∩ U) ⊆ closure (relInterior_BIF Bs (f '' (M ∩ U))) := by
  rintro _ ⟨p, ⟨hpM, hpU⟩, rfl⟩
  rw [_root_.mem_closure_iff]
  intro O' hO' hyO'
  have hV : IsOpen (U ∩ f ⁻¹' O') := hcont.isOpen_inter_preimage hU hO'
  obtain ⟨q, hqV, hqM⟩ := _root_.mem_closure_iff.mp (hM hpM) _ hV ⟨hpU, hyO'⟩
  have hW : IsOpen (U ∩ f ⁻¹' O' ∩ interior M) := hV.inter isOpen_interior
  obtain ⟨O'', hO'', hOW⟩ := hopen _ (fun x hx => hx.1.1) hW
  have hqW : q ∈ U ∩ f ⁻¹' O' ∩ interior M := ⟨hqV, hqM⟩
  have hfq : f q ∈ O'' ∩ Bs := hOW ▸ mem_image_of_mem f hqW
  refine ⟨f q, hqV.2, ?_⟩
  refine mem_relInterior_iff_BCF.mpr ⟨hfq.2, O'', hO'', hfq.1, ?_⟩
  rw [hOW]
  rintro _ ⟨x, hx, rfl⟩
  exact ⟨x, ⟨interior_subset hx.2, hx.1.1⟩, rfl⟩

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
    δn n B oM} {Γ Sg eg : Fin 3 → ℝ}
  {DP : BoundaryAugmentedDataPV3 S (actualSlotsV2_BAUGD S) Γ Sg eg} {Kj : ℕ}
  {Ξ c cw : Fin 3 → ℝ} {bcut bder κ cadj : ℝ}

namespace BoundaryGaf02ChainE

variable (C : BoundaryGaf02ChainE DP Kj Ξ c cw bcut bder κ cadj)

/-- **The removed region `Z ∪ C_∂` is closed** (zero domains compact, cusp cores closed by BCG06;
premises of E4). -/
theorem isClosed_zeroCuspUnion_BCF {rd : ℝ} (hrd : 0 < rd) (hrd4 : rd < 1 / 10000)
    (hrdc : 20 * (c 2 + 1) * rd < 1 / 1000000)
    (hprem : 1000 * δn ^ 2 < w / (2 * (1 + 2 * Λ⁻¹) ^ 3) * min (1 / 2) (rd / 4) ^ 2)
    (hθ : θ < 1 / 100) :
    IsClosed ((⋃ k, C.toChain.actualZeroDomain_BIFc k) ∪ C.toChain.cuspCores_BIF) := by
  have hcomp := (C.bcg06_on_boundary_chain_BGR hrd hrd4 hrdc hprem hθ).1
  refine (isClosed_iUnion_of_finite fun k => (C.isCompact_actualZeroDomain_BGR k).isClosed).union ?_
  exact isClosed_iUnion_of_finite fun i => (hcomp i).compact_core.isClosed

/-- **`M₁` is regular**: `M₁ ⊆ cl(int M₁)` (the complement of the interior of a closed set). -/
theorem M₁_subset_closure_interior_BCF {rd : ℝ} (hrd : 0 < rd) (hrd4 : rd < 1 / 10000)
    (hrdc : 20 * (c 2 + 1) * rd < 1 / 1000000)
    (hprem : 1000 * δn ^ 2 < w / (2 * (1 + 2 * Λ⁻¹) ^ 3) * min (1 / 2) (rd / 4) ^ 2)
    (hθ : θ < 1 / 100) :
    C.toChain.M₁_BIFc ⊆ closure (interior C.toChain.M₁_BIFc) :=
  compl_interior_subset_closure_interior_BCF (C.isClosed_zeroCuspUnion_BCF hrd hrd4 hrdc hprem hθ)

/-- **`D₃` is regular in `B₃`** (BCF01 input (b)): `D₃ ⊆ cl(int_{B₃} D₃)`, from the regularity of
`M₁` and A4c (`f₃|X₃` is relatively open, from `WF`). -/
theorem slimBaseDomain_regular_BCF {Bs : BoundaryGaf02BasesV2 C.toChain}
    (WF : BoundaryWholeFiberSpecV2 C.toChain Bs) {rd : ℝ} (hrd : 0 < rd) (hrd4 : rd < 1 / 10000)
    (hrdc : 20 * (c 2 + 1) * rd < 1 / 1000000)
    (hprem : 1000 * δn ^ 2 < w / (2 * (1 + 2 * Λ⁻¹) ^ 3) * min (1 / 2) (rd / 4) ^ 2)
    (hθ : θ < 1 / 100) :
    Bs.slimBaseDomain_BIFc ⊆ closure (relInterior_BIF (Bs.base 2) Bs.slimBaseDomain_BIFc) :=
  image_subset_closure_relInterior_BCF (Bs.isOpen_source 2 (by decide))
    (Bs.continuousOn_stageMap_BCF 2) WF.slimStage_relOpen_BCF
    (C.M₁_subset_closure_interior_BCF hrd hrd4 hrdc hprem hθ)

/-- **`f₃(slabs)` is compact** (BCF01 input (c)): the original closed slim slabs are compact, lie in
`X₃` (GAF07) and `f₃` is continuous there. -/
theorem isCompact_slabImage_BCF (Bs : BoundaryGaf02BasesV2 C.toChain) :
    IsCompact (C.toChain.stageMap 2 '' (Subtype.val '' S.slimSlabs_BIF)) := by
  have hΔ : 0 < Δ := C.std.2.1
  refine (S.toBoundarySupplyCore.isCompact_val_slimSlabs_BCF hΔ).image_of_continuousOn
    ((Bs.continuousOn_stageMap_BCF 2).mono ?_)
  rintro _ ⟨q, ⟨j, hj, h1, h2⟩, rfl⟩
  exact Bs.slim_original_subset q j hj h1 h2

/-- **G1a BCF01, chart intervals** (v3.1 §G, on the enhanced chain; the numerical premises are those
of F4c / F5 / F5z, named revision v3.2): over ANY graph atlas `At` of `B₃`, finitely many closed
chart intervals with pairwise distinct endpoints, (K) and a regular slim piece. -/
theorem exists_slimChartIntervals_BCF01 {Bs : BoundaryGaf02BasesV2 C.toChain}
    (WF : BoundaryWholeFiberSpecV2 C.toChain Bs) (Z : BoundaryActualZeroDomains_BIFc C.toChain Bs)
    {rd : ℝ} (hrd : 0 < rd) (hrd4 : rd < 1 / 10000) (hrdc : 20 * (c 2 + 1) * rd < 1 / 1000000)
    (hprem : 1000 * δn ^ 2 < w / (2 * (1 + 2 * Λ⁻¹) ^ 3) * min (1 / 2) (rd / 4) ^ 2)
    (hθ : θ < 1 / 100) {ι : Type*} (At : GraphAtlas1_BCF ι (Bs.base 2)) :
    Nonempty (BoundarySlimChartIntervals_BIFc Bs At) := by
  have hfin := C.frontier_M₁_image_finite_BGR WF Z hrd hrd4 hrdc hprem hθ
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
      (C.slimBaseDomain_regular_BCF WF hrd hrd4 hrdc hprem hθ) hKfront
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
    piece_regular := Z.slimPiece_regular_BCF WF hcpt hsub hreg }⟩
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

end BoundaryGaf02ChainE

end DifferentialGeometry.Geometry.Collapse
