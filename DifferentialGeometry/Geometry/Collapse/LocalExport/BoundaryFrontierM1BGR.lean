import DifferentialGeometry.Geometry.Collapse.LocalExport.BoundaryCuspCoreChainEBGR
import DifferentialGeometry.Geometry.Collapse.LocalExport.BoundarySlimArcsBCF
import DifferentialGeometry.Geometry.Collapse.LocalExport.BoundarySlimCutFacesBCF

/-!
# BCG07 F4c and the point-set halves of F5 / F5z on the enhanced chain (lane B-BCG-ROWS)

Targets F4c / F5 / F5z of `TargetsBoundary-v3.1.lean.txt` (§F) on ONE enhanced chain
`C : BoundaryGaf02ChainE DP …`, the actual zero domains `Z` of the SAME chain (v2 bases `Bs`) and
the same chain's cusp cores (BCG06, E4 / E4b of B-BCG-ROWS G17).

* topology: `interior_iUnion_of_disjoint_closed_BGR`, **`frontier_compl_interior_iUnion_BGR`**
  (`∂(int ⋃ P_i)ᶜ = ⋃ F_i` for finitely many pairwise disjoint closed `P_i` with
  `∂P_i = F_i ⊆ closure (int P_i)`), `subset_piece_of_isPreconnected_BGR`;
* Fermat at interior points (minimum form): `mfderiv_eq_zero_of_isLocalMin_BGR`,
  `mem_closure_lt_of_mfderiv_ne_zero_BGR`;
* `isInteriorPoint_of_mem_actualZeroFace_BGR`, `actualZeroFace_subset_closure_interior_BGR`
  (regular zero faces), `cuspFront_subset_closure_interior_BGR` (BCG06's regular level),
  `cuspCore_disjoint_actualZeroDomain_BGR`;
* **`frontier_M₁_of_defining_BGR`** (kernel: any analytic half `Zd`), **`frontier_M₁_BGR`** (F4c on
  `Z`, premises of E4);
* `isPreconnected_slimFibre_BGR`, **`fibre_subset_frontier_M₁_BGR`** (`∂M₁` is saturated by whole
  slim fibres: A4c openness of `f₃|X₃` from `WF` + `Z.face_saturated`);
* `faceFront_closed_disjoint_BGR`, `frontier_M₁_eq_iUnion_sum_BGR`;
* **`zeroFace_fibre_subset_BGR`** (F5z point-set half), **`cuspFront_fibre_subset_BGR`** (F5
  point-set half): the whole slim fibre through a face / front point of `X₃` lies in that face /
  front. (The equality with ONE fibre needs the isolation of the base value — next step.)
-/

set_option autoImplicit false

noncomputable section

open Set Function Metric Bundle Manifold Filter
open scoped ContDiff Manifold Topology ENNReal
open DifferentialGeometry.Topology.Ehresmann DifferentialGeometry.Topology.Manifold
open DifferentialGeometry.Geometry.Riemannian GC.MetricGeometry
open DifferentialGeometry GC.Endpoint DifferentialGeometry.Geometry.Hyperbolic
open DifferentialGeometry.Analysis

namespace DifferentialGeometry.Geometry.Collapse

local notation "E3" => EuclideanSpace ℝ (Fin 3)
local notation "ℝ²" => EuclideanSpace ℝ (Fin 2)

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace

attribute [local instance] nezero_finrank_euclideanThree_LC87

attribute [local instance] interiorCharted_BDRY1 interiorManifold_BDRY1
  connectedSpace_interior_BDRY2

section Topology

variable {X ι : Type*} [TopologicalSpace X] [Finite ι] {P : ι → Set X}

/-- The interior of a finite union of pairwise disjoint closed sets is the union of interiors. -/
theorem interior_iUnion_of_disjoint_closed_BGR (hc : ∀ i, IsClosed (P i))
    (hd : Pairwise (Disjoint on P)) : interior (⋃ i, P i) = ⋃ i, interior (P i) := by
  refine Subset.antisymm (fun x hx => ?_) (iUnion_subset fun i => interior_mono
    (subset_iUnion P i))
  obtain ⟨i, hi⟩ := mem_iUnion.mp (interior_subset hx)
  have hopen : IsOpen (interior (⋃ j, P j) ∩ ⋂ j : {j // j ≠ i}, (P j)ᶜ) :=
    isOpen_interior.inter (isOpen_iInter_of_finite fun j => (hc j).isOpen_compl)
  have hxN : x ∈ interior (⋃ j, P j) ∩ ⋂ j : {j // j ≠ i}, (P j)ᶜ :=
    ⟨hx, mem_iInter.mpr fun j hxj => Set.disjoint_left.mp (hd j.2.symm) hi hxj⟩
  have hsub : interior (⋃ j, P j) ∩ ⋂ j : {j // j ≠ i}, (P j)ᶜ ⊆ P i := by
    rintro y ⟨hy, hy'⟩
    obtain ⟨j, hj⟩ := mem_iUnion.mp (interior_subset hy)
    by_cases hji : j = i
    · exact hji ▸ hj
    · exact absurd hj (mem_iInter.mp hy' ⟨j, hji⟩)
  exact mem_iUnion.mpr ⟨i, mem_interior.mpr ⟨_, hsub, hopen, hxN⟩⟩

/-- **The frontier of `(int ⋃ P_i)ᶜ`** for finitely many pairwise disjoint closed sets `P_i`
with `∂P_i = F_i ⊆ closure (int P_i)`: it is `⋃ F_i`. -/
theorem frontier_compl_interior_iUnion_BGR {F : ι → Set X} (hc : ∀ i, IsClosed (P i))
    (hd : Pairwise (Disjoint on P)) (hF : ∀ i, frontier (P i) = F i)
    (hreg : ∀ i, F i ⊆ closure (interior (P i))) :
    frontier (interior (⋃ i, P i))ᶜ = ⋃ i, F i := by
  have hcl : ∀ i, closure (interior (P i)) = P i := fun i =>
    Subset.antisymm (closure_minimal interior_subset (hc i)) (by
      intro x hx
      by_cases hxi : x ∈ interior (P i)
      · exact subset_closure hxi
      · exact hreg i (hF i ▸ ((hc i).frontier_eq ▸ ⟨hx, hxi⟩)))
  rw [frontier_compl, isOpen_interior.frontier_eq, interior_iUnion_of_disjoint_closed_BGR hc hd,
    closure_iUnion_of_finite]
  simp_rw [hcl]
  ext x
  simp only [Set.mem_sdiff, mem_iUnion, not_exists]
  constructor
  · rintro ⟨⟨i, hi⟩, hn⟩
    exact ⟨i, hF i ▸ (hc i).frontier_eq ▸ ⟨hi, hn i⟩⟩
  · rintro ⟨i, hi⟩
    rw [← hF i, (hc i).frontier_eq] at hi
    refine ⟨⟨i, hi.1⟩, fun j hj => ?_⟩
    by_cases hji : j = i
    · exact hi.2 (hji ▸ hj)
    · exact Set.disjoint_left.mp (hd hji) (interior_subset hj) hi.1


/-- A preconnected set inside a finite union of pairwise disjoint closed sets, meeting the piece
`F i`, lies in `F i`. -/
theorem subset_piece_of_isPreconnected_BGR {F : ι → Set X} (hc : ∀ i, IsClosed (F i))
    (hd : Pairwise (Disjoint on F)) {s : Set X} (hs : IsPreconnected s) (hsub : s ⊆ ⋃ i, F i)
    {p : X} (hps : p ∈ s) {i : ι} (hpi : p ∈ F i) : s ⊆ F i := by
  have hv : IsClosed (⋃ j : {j // j ≠ i}, F j) := isClosed_iUnion_of_finite fun j => hc j
  have huv : F i ∩ ⋃ j : {j // j ≠ i}, F j = ∅ := by
    refine eq_empty_iff_forall_notMem.mpr fun x ⟨hx, hx'⟩ => ?_
    obtain ⟨j, hj⟩ := mem_iUnion.mp hx'
    exact Set.disjoint_left.mp (hd j.2.symm) hx hj
  have hcover : s ⊆ F i ∪ ⋃ j : {j // j ≠ i}, F j := by
    intro x hx
    obtain ⟨j, hj⟩ := mem_iUnion.mp (hsub hx)
    by_cases hji : j = i
    · exact Or.inl (hji ▸ hj)
    · exact Or.inr (mem_iUnion.mpr ⟨⟨j, hji⟩, hj⟩)
  rcases isPreconnected_iff_subset_of_disjoint_closed.mp hs _ _ (hc i) hv hcover
      (by rw [huv, inter_empty]) with h | h
  · exact h
  · exact absurd (show p ∈ F i ∩ ⋃ j : {j // j ≠ i}, F j from ⟨hpi, h hps⟩) (by rw [huv]; simp)

end Topology

section Fermat

variable {W : CompactCarrier.{0}}

/-- **Fermat at an interior point of `W`, minimum form.** -/
theorem mfderiv_eq_zero_of_isLocalMin_BGR {f : W.Carrier → ℝ} {x : W.Carrier}
    (hx : W.model.IsInteriorPoint x) (hf : IsLocalMin f x) :
    mfderiv W.model 𝓘(ℝ, ℝ) f x = 0 := by
  by_cases hd : MDifferentiableAt W.model 𝓘(ℝ, ℝ) f x
  · rw [hd.mfderiv]
    have h0 : fderivWithin ℝ (writtenInExtChartAt W.model 𝓘(ℝ, ℝ) x f) (range W.model)
        ((extChartAt W.model x) x) = 0 := by
      rw [fderivWithin_of_mem_nhds (mem_interior_iff_mem_nhds.mp hx)]
      apply IsLocalMin.fderiv_eq_zero
      have hw : writtenInExtChartAt W.model 𝓘(ℝ, ℝ) x f = f ∘ (extChartAt W.model x).symm := by
        ext y
        simp [writtenInExtChartAt]
      rw [hw]
      apply IsLocalMin.comp_continuous
      · rw [extChartAt_to_inv]
        exact hf
      · exact continuousAt_extChartAt_symm x
    rw [h0]
    ext v
    simp
  · exact mfderiv_zero_of_not_mdifferentiableAt hd

/-- A real function with nonzero differential at an interior point takes strictly smaller values
arbitrarily close to it. -/
theorem mem_closure_lt_of_mfderiv_ne_zero_BGR {f : W.Carrier → ℝ} {x : W.Carrier}
    (hx : W.model.IsInteriorPoint x) (hf : mfderiv W.model 𝓘(ℝ, ℝ) f x ≠ 0) :
    x ∈ closure {y | f y < f x} := by
  rw [mem_closure_iff_nhds]
  intro U hU
  by_contra h
  rw [not_nonempty_iff_eq_empty, eq_empty_iff_forall_notMem] at h
  refine hf (mfderiv_eq_zero_of_isLocalMin_BGR hx (Filter.mem_of_superset hU fun y hy => ?_))
  exact not_lt.mp fun hlt : f y < f x => h y ⟨hy, hlt⟩

end Fermat

section Fibres

variable {K : ℕ} {A : ℝ → ℝ} {β : ℕ → ℝ}
  {βd εN Λ w Δ σs σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs ζ Λz θ : ℝ}
  {W : CompactCarrier.{0}} [ConnectedSpace W.Carrier] {g : SmoothRiemannianMetric W.model W.Carrier}
  {δn : ℝ} {n : ℕ} {B : NearlyCuspidalBoundary W g K δn}
  {oM : ManifoldOrientation 𝓘(ℝ, E3) (W.pieceInterior ⊤) 3}
  {S : BoundarySupply K A β βd εN Λ w Δ σs σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs ζ Λz θ W g
    δn n B oM} {Φ : BoundaryInteriorSlots_BIF S} {D : BoundaryAugmentedData S Φ} {Kj : ℕ}
  {Ξ Sg eg c cw : Fin 3 → ℝ} {bcut bder κ : ℝ}
  {C : BoundaryGaf02Chain D Kj Ξ Sg eg c cw bcut bder κ} {Bs : BoundaryGaf02BasesV2 C}

/-- **Whole slim fibres are preconnected** (`≃ₜ S²` or `≃ₜ T²`). -/
theorem isPreconnected_slimFibre_BGR (WF : BoundaryWholeFiberSpecV2 C Bs) {y : _}
    (hy : y ∈ Bs.base 2) : IsPreconnected (Bs.fibre 2 y) := by
  rw [isPreconnected_iff_preconnectedSpace]
  rcases WF.slim_fibre_BIFc y hy with ⟨⟨e⟩⟩ | ⟨⟨e⟩⟩
  · have : PreconnectedSpace (Metric.sphere (0 : E3) 1) := by
      rw [← isPreconnected_iff_preconnectedSpace]
      refine (isConnected_sphere ?_ 0 zero_le_one).isPreconnected
      rw [← Module.finrank_eq_rank, finrank_euclideanSpace, Fintype.card_fin]
      exact_mod_cast (by norm_num : 1 < 3)
    exact e.symm.surjective.denseRange.preconnectedSpace e.symm.continuous
  · exact e.symm.surjective.denseRange.preconnectedSpace e.symm.continuous

/-- **The frontier of `M₁` is saturated by whole slim fibres** (A4c openness of `f₃|X₃` from
`WF`, and `Z.face_saturated` at `st = 2`): a frontier point in `X₃` has its whole fibre in `∂M₁`. -/
theorem fibre_subset_frontier_M₁_BGR (WF : BoundaryWholeFiberSpecV2 C Bs)
    (Z : BoundaryActualZeroDomains_BIFc C Bs) {p : W.Carrier} (hp : p ∈ frontier C.M₁_BIFc)
    (hpX : p ∈ Bs.source 2) : Bs.fibre 2 (C.stageMap 2 p) ⊆ frontier C.M₁_BIFc := by
  have hcl := C.isClosed_M₁_BCF
  have hsat : ∀ x ∈ Bs.source 2, ∀ z ∈ Bs.source 2, C.stageMap 2 z = C.stageMap 2 x →
      x ∈ C.M₁_BIFc → z ∈ C.M₁_BIFc := fun x hx z hz hzx hxM =>
    Z.face_saturated 2 (by decide) x hx z hz hzx hxM
  have hpM : p ∈ C.M₁_BIFc := hcl.frontier_subset hp
  rintro q ⟨hqX, hq⟩
  have hqp : C.stageMap 2 q = C.stageMap 2 p := hq
  have hqM : q ∈ C.M₁_BIFc := hsat p hpX q hqX hqp hpM
  rw [hcl.frontier_eq]
  refine ⟨hqM, fun hqI => ?_⟩
  obtain ⟨O, hO, hOB⟩ := WF.slimStage_relOpen_BCF (interior C.M₁_BIFc ∩ Bs.source 2)
    inter_subset_right (isOpen_interior.inter (Bs.isOpen_source 2 (by decide)))
  have hqO : C.stageMap 2 q ∈ O := by
    have h : C.stageMap 2 q ∈ C.stageMap 2 '' (interior C.M₁_BIFc ∩ Bs.source 2) :=
      mem_image_of_mem _ ⟨hqI, hqX⟩
    rw [← hOB] at h
    exact h.1
  have hN : IsOpen (Bs.source 2 ∩ C.stageMap 2 ⁻¹' O) :=
    (Bs.continuousOn_stageMap_BCF 2).isOpen_inter_preimage (Bs.isOpen_source 2 (by decide)) hO
  have hNM : Bs.source 2 ∩ C.stageMap 2 ⁻¹' O ⊆ C.M₁_BIFc := by
    rintro z ⟨hzX, hzO⟩
    have hzB : C.stageMap 2 z ∈ O ∩ Bs.base 2 :=
      ⟨hzO, Bs.image_eq 2 ▸ mem_image_of_mem _ hzX⟩
    rw [hOB] at hzB
    obtain ⟨z', ⟨hz'I, hz'X⟩, hz'z⟩ := hzB
    exact hsat z' hz'X z hzX hz'z.symm (interior_subset hz'I)
  have hpI : p ∈ interior C.M₁_BIFc :=
    mem_interior.mpr ⟨_, hNM, hN, hpX, show C.stageMap 2 p ∈ O from hqp ▸ hqO⟩
  rw [hcl.frontier_eq] at hp
  exact hp.2 hpI

end Fibres

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

/-- Points of an actual zero face of `C.E` are interior points of `W` (G12: the face is a
`val`-image). -/
theorem isInteriorPoint_of_mem_actualZeroFace_BGR (k : S.ZeroIdx_BAUGC) {x : W.Carrier}
    (hx : x ∈ C.toChain.actualZeroFace_BIFc k) : W.model.IsInteriorPoint x := by
  obtain ⟨-, -, -, -, -, -, -, -, -, hΔ, -, -, he, hT, -⟩ := C.std
  have hT1 : 1 ≤ T := by nlinarith only [hT, hΔ]
  rw [C.toChain.actualZeroFace_eq_image_BGR hT1 he k] at hx
  obtain ⟨y, -, rfl⟩ := hx
  exact y.property.2

/-- **A regular zero face lies in the closure of the interior of its domain** (Fermat at the
interior face points, `defFn_regular`). -/
theorem actualZeroFace_subset_closure_interior_BGR (Zd : BoundaryZeroDefining_BIFc C.toChain)
    (k : S.ZeroIdx_BAUGC) :
    C.toChain.actualZeroFace_BIFc k ⊆ closure (interior (C.toChain.actualZeroDomain_BIFc k)) := by
  intro x hx
  have h0 : Zd.defFn k x = 0 := by
    have h := hx
    rw [Zd.face_eq k] at h
    exact h
  have hcl := mem_closure_lt_of_mfderiv_ne_zero_BGR
    (C.isInteriorPoint_of_mem_actualZeroFace_BGR k hx) (Zd.defFn_regular k x h0)
  rw [h0] at hcl
  refine closure_mono ?_ hcl
  rw [Zd.domain_eq k]
  exact interior_maximal (fun y (hy : Zd.defFn k y < 0) => le_of_lt hy)
    (isOpen_lt (Zd.defFn_smooth k).continuous continuous_const)

/-- **Every cusp front lies in the closure of the interior of its core** (BCG6-K's regular level
`coreLevel = 40` at interior front points; premises of E4). -/
theorem cuspFront_subset_closure_interior_BGR {rd : ℝ} (hrd : 0 < rd) (hrd4 : rd < 1 / 10000)
    (hrdc : 20 * (c 2 + 1) * rd < 1 / 1000000)
    (hprem : 1000 * δn ^ 2 < w / (2 * (1 + 2 * Λ⁻¹) ^ 3) * min (1 / 2) (rd / 4) ^ 2)
    (hθ : θ < 1 / 100) (i : Fin S.packet.cusp.count) :
    C.toChain.cuspFront_BIF i ⊆ closure (interior (C.toChain.cuspCore_BIF i)) := by
  have hεd := epsBoundary_lt_BGR hrd hrdc
  have hBI := (C.bcg04_row_BGR hrd hprem).2.1 3 i
  have hBFM := (C.bcg05_row_BGR hθ hrd hrd4 hprem).1 3 i
  have hc₃ := C.validity.c_two_lt_E4
  have hR := BoundaryCollarPacket.register_R_BCG6K hεd hc₃
  have hu : ContMDiff W.model 𝓘(ℝ, ℝ) ∞ (chainBoundaryU_BCG6K C.toChain.E i) :=
    contMDiff_chainBoundaryU_BCG6K (C.stage_smooth_BAUGD 3) i
  intro x hx
  change x ∈ S.packet.toBoundaryCollarPacket.cuspFront_BCG6K i (chainBoundaryU_BCG6K C.toChain.E)
    (chainBoundaryV_BCG6K C.toChain.E) at hx
  change x ∈ closure (interior (S.packet.toBoundaryCollarPacket.cuspCore_BCG6K i
    (chainBoundaryU_BCG6K C.toChain.E) (chainBoundaryV_BCG6K C.toChain.E)))
  have hint := (S.packet.toBoundaryCollarPacket.mem_strip_of_mem_front_BCG6K hεd hBI hx).2
  have hx40 : S.packet.toBoundaryCollarPacket.coreLevel_BCG6K i
      (chainBoundaryU_BCG6K C.toChain.E i) x = 40 := by
    rw [S.packet.toBoundaryCollarPacket.cuspFront_eq_BCG6K hεd hBI hBFM] at hx
    exact hx
  have hreg := S.packet.toBoundaryCollarPacket.mfderiv_coreLevel_ne_zero_BCG6K i
    (cuspTolerance_le_thousandth_BCUSP1 _ _ _) hu C.toChain.c_two_pos_BCG6K.le hR
    (fun y _ => (hBI y).1) (C.bcg04_derivative_on_boundary_chain_BGR i) (le_of_eq hx40)
  have hcl := mem_closure_lt_of_mfderiv_ne_zero_BGR hint hreg
  rw [hx40] at hcl
  refine closure_mono ?_ hcl
  rw [S.packet.toBoundaryCollarPacket.cuspCore_eq_BCG6K hεd hBI hBFM]
  exact interior_maximal (fun y (hy : S.packet.toBoundaryCollarPacket.coreLevel_BCG6K i
      (chainBoundaryU_BCG6K C.toChain.E i) y < 40) => le_of_lt hy)
    (isOpen_lt (S.packet.toBoundaryCollarPacket.contMDiff_coreLevel_BCG6K i hu).continuous
      continuous_const)

/-- The actual zero domains and the cusp cores of `C.E` are pairwise disjoint (separated branch
`DP.separated`: E4b's spec, zero domains inside the original zero balls). -/
theorem cuspCore_disjoint_actualZeroDomain_BGR {rd : ℝ} (hrd : 0 < rd) (hrd4 : rd < 1 / 10000)
    (hrdc : 20 * (c 2 + 1) * rd < 1 / 1000000)
    (hprem : 1000 * δn ^ 2 < w / (2 * (1 + 2 * Λ⁻¹) ^ 3) * min (1 / 2) (rd / 4) ^ 2)
    (hθ : θ < 1 / 100) (i : Fin S.packet.cusp.count) (k : S.ZeroIdx_BAUGC) :
    Disjoint (C.toChain.cuspCore_BIF i) (C.toChain.actualZeroDomain_BIFc k) :=
  S.toBoundarySupplyCore.cuspCore_disjoint_of_subset_supplyZeroBall_BCG6K
    (C.bcg06_coreSpec_on_chain_BGR hrd hrd4 hrdc hprem hθ) C.toChain.actualZeroDomain_BIFc
    (fun k => k.1) (fun k => ⟨(Set.Finite.mem_toFinset _).mp k.2,
      C.actualZeroDomain_subset_ball_BGR k⟩) i k

/-- **F4c, kernel form** (any analytic half `Zd` of the actual zero domains on the SAME chain):
`frontier M₁ = ⋃ (ZF)_k ∪ ⋃ H_b`. Premises: the `r_∂` block and `θ < 1/100` (those of E4 — the
cusp fronts need BCG06's regular level). -/
theorem frontier_M₁_of_defining_BGR (Zd : BoundaryZeroDefining_BIFc C.toChain) {rd : ℝ}
    (hrd : 0 < rd) (hrd4 : rd < 1 / 10000) (hrdc : 20 * (c 2 + 1) * rd < 1 / 1000000)
    (hprem : 1000 * δn ^ 2 < w / (2 * (1 + 2 * Λ⁻¹) ^ 3) * min (1 / 2) (rd / 4) ^ 2)
    (hθ : θ < 1 / 100) :
    frontier C.toChain.M₁_BIFc =
      (⋃ k, C.toChain.actualZeroFace_BIFc k) ∪ ⋃ i, C.toChain.cuspFront_BIF i := by
  have hcomp := (C.bcg06_on_boundary_chain_BGR hrd hrd4 hrdc hprem hθ).1
  have hspec := C.bcg06_coreSpec_on_chain_BGR hrd hrd4 hrdc hprem hθ
  have hM : C.toChain.M₁_BIFc = (interior (⋃ t, Sum.elim C.toChain.actualZeroDomain_BIFc
      C.toChain.cuspCore_BIF t))ᶜ := by
    rw [iUnion_sum]
    rfl
  have hR : (⋃ k, C.toChain.actualZeroFace_BIFc k) ∪ ⋃ i, C.toChain.cuspFront_BIF i =
      ⋃ t, Sum.elim C.toChain.actualZeroFace_BIFc C.toChain.cuspFront_BIF t := by
    rw [iUnion_sum]
    rfl
  rw [hM, hR]
  refine frontier_compl_interior_iUnion_BGR ?_ ?_ ?_ ?_
  · rintro (k | i)
    · exact (C.isCompact_actualZeroDomain_BGR k).isClosed
    · exact (hcomp i).compact_core.isClosed
  · rintro (k | i) (k' | i') hne
    · exact C.actualZeroDomain_pairwise_disjoint_BGR fun h => hne (congrArg Sum.inl h)
    · exact (C.cuspCore_disjoint_actualZeroDomain_BGR hrd hrd4 hrdc hprem hθ i' k).symm
    · exact C.cuspCore_disjoint_actualZeroDomain_BGR hrd hrd4 hrdc hprem hθ i k'
    · exact hspec.pairwise_disjoint i i' fun h => hne (congrArg Sum.inr h)
  · rintro (k | i)
    · exact Zd.frontier_eq k
    · exact (hcomp i).relative_frontier_eq
  · rintro (k | i)
    · exact C.actualZeroFace_subset_closure_interior_BGR Zd k
    · exact C.cuspFront_subset_closure_interior_BGR hrd hrd4 hrdc hprem hθ i

/-- **F4c `frontier_M₁`** (v3.1 frozen statement, with E4's premises): on the actual zero domains
`Z` of the SAME chain and the same chain's cusp fronts, `∂M₁ = ⋃ (ZF)_k ∪ ⋃ H_b`. -/
theorem frontier_M₁_BGR {Bs : BoundaryGaf02BasesV2 C.toChain}
    (Z : BoundaryActualZeroDomains_BIFc C.toChain Bs) {rd : ℝ} (hrd : 0 < rd)
    (hrd4 : rd < 1 / 10000) (hrdc : 20 * (c 2 + 1) * rd < 1 / 1000000)
    (hprem : 1000 * δn ^ 2 < w / (2 * (1 + 2 * Λ⁻¹) ^ 3) * min (1 / 2) (rd / 4) ^ 2)
    (hθ : θ < 1 / 100) :
    frontier C.toChain.M₁_BIFc =
      (⋃ k, C.toChain.actualZeroFace_BIFc k) ∪ ⋃ i, C.toChain.cuspFront_BIF i :=
  C.frontier_M₁_of_defining_BGR Z.toBoundaryZeroDefining_BIFc hrd hrd4 hrdc hprem hθ

/-- **The zero faces and the cusp fronts of `C.E` form one finite family of pairwise disjoint
closed sets** (faces inside the zero domains, fronts inside the cores; premises of E4). -/
theorem faceFront_closed_disjoint_BGR (Zd : BoundaryZeroDefining_BIFc C.toChain) {rd : ℝ}
    (hrd : 0 < rd) (hrd4 : rd < 1 / 10000) (hrdc : 20 * (c 2 + 1) * rd < 1 / 1000000)
    (hprem : 1000 * δn ^ 2 < w / (2 * (1 + 2 * Λ⁻¹) ^ 3) * min (1 / 2) (rd / 4) ^ 2)
    (hθ : θ < 1 / 100) :
    (∀ t, IsClosed (Sum.elim C.toChain.actualZeroFace_BIFc C.toChain.cuspFront_BIF t)) ∧
      Pairwise (Disjoint on Sum.elim C.toChain.actualZeroFace_BIFc C.toChain.cuspFront_BIF) := by
  have hcomp := (C.bcg06_on_boundary_chain_BGR hrd hrd4 hrdc hprem hθ).1
  have hspec := C.bcg06_coreSpec_on_chain_BGR hrd hrd4 hrdc hprem hθ
  have hfZ : ∀ k, C.toChain.actualZeroFace_BIFc k ⊆ C.toChain.actualZeroDomain_BIFc k :=
    fun k x hx => by
      rw [Zd.face_eq k] at hx
      rw [Zd.domain_eq k]
      exact le_of_eq hx
  have hfC : ∀ i, C.toChain.cuspFront_BIF i ⊆ C.toChain.cuspCore_BIF i := fun i => by
    have h := (hcomp i).compact_core.isClosed.frontier_subset
    rw [(hcomp i).relative_frontier_eq] at h
    exact h
  refine ⟨?_, ?_⟩
  · rintro (k | i)
    · change IsClosed (C.toChain.actualZeroFace_BIFc k)
      rw [Zd.face_eq k]
      exact isClosed_eq (Zd.defFn_smooth k).continuous continuous_const
    · have h := isClosed_frontier (s := S.packet.toBoundaryCollarPacket.cuspCore_BCG6K i
        (chainBoundaryU_BCG6K C.toChain.E) (chainBoundaryV_BCG6K C.toChain.E))
      rw [(hcomp i).relative_frontier_eq] at h
      exact h
  · rintro (k | i) (k' | i') hne
    · exact (C.actualZeroDomain_pairwise_disjoint_BGR fun h => hne (congrArg Sum.inl h)).mono
        (hfZ k) (hfZ k')
    · exact (C.cuspCore_disjoint_actualZeroDomain_BGR hrd hrd4 hrdc hprem hθ i' k).symm.mono
        (hfZ k) (hfC i')
    · exact (C.cuspCore_disjoint_actualZeroDomain_BGR hrd hrd4 hrdc hprem hθ i k').mono
        (hfC i) (hfZ k')
    · exact (hspec.pairwise_disjoint i i' fun h => hne (congrArg Sum.inr h)).mono (hfC i)
        (hfC i')

/-- `∂M₁` as the union of the `Sum`-indexed family of faces and fronts (F4c). -/
theorem frontier_M₁_eq_iUnion_sum_BGR {Bs : BoundaryGaf02BasesV2 C.toChain}
    (Z : BoundaryActualZeroDomains_BIFc C.toChain Bs) {rd : ℝ} (hrd : 0 < rd)
    (hrd4 : rd < 1 / 10000) (hrdc : 20 * (c 2 + 1) * rd < 1 / 1000000)
    (hprem : 1000 * δn ^ 2 < w / (2 * (1 + 2 * Λ⁻¹) ^ 3) * min (1 / 2) (rd / 4) ^ 2)
    (hθ : θ < 1 / 100) :
    frontier C.toChain.M₁_BIFc =
      ⋃ t, Sum.elim C.toChain.actualZeroFace_BIFc C.toChain.cuspFront_BIF t := by
  rw [C.frontier_M₁_BGR Z hrd hrd4 hrdc hprem hθ, iUnion_sum]
  rfl

/-- **F5z, point-set part**: the whole slim fibre through a point of a zero face in `X₃` lies in
that face (saturation of `∂M₁`, F4c, connected fibre, disjoint closed faces / fronts). -/
theorem zeroFace_fibre_subset_BGR {Bs : BoundaryGaf02BasesV2 C.toChain}
    (WF : BoundaryWholeFiberSpecV2 C.toChain Bs) (Z : BoundaryActualZeroDomains_BIFc C.toChain Bs)
    {rd : ℝ} (hrd : 0 < rd) (hrd4 : rd < 1 / 10000) (hrdc : 20 * (c 2 + 1) * rd < 1 / 1000000)
    (hprem : 1000 * δn ^ 2 < w / (2 * (1 + 2 * Λ⁻¹) ^ 3) * min (1 / 2) (rd / 4) ^ 2)
    (hθ : θ < 1 / 100) (k : S.ZeroIdx_BAUGC) {p : W.Carrier}
    (hp : p ∈ C.toChain.actualZeroFace_BIFc k) (hpX : p ∈ Bs.source 2) :
    Bs.fibre 2 (C.toChain.stageMap 2 p) ⊆ C.toChain.actualZeroFace_BIFc k := by
  have hF := C.frontier_M₁_eq_iUnion_sum_BGR Z hrd hrd4 hrdc hprem hθ
  have hpF : p ∈ frontier C.toChain.M₁_BIFc := hF ▸ mem_iUnion.mpr ⟨Sum.inl k, hp⟩
  obtain ⟨hc, hd⟩ := C.faceFront_closed_disjoint_BGR Z.toBoundaryZeroDefining_BIFc hrd hrd4 hrdc
    hprem hθ
  exact subset_piece_of_isPreconnected_BGR hc hd
    (isPreconnected_slimFibre_BGR WF (Bs.image_eq 2 ▸ mem_image_of_mem _ hpX))
    ((fibre_subset_frontier_M₁_BGR WF Z hpF hpX).trans hF.subset) ⟨hpX, rfl⟩
    (i := Sum.inl k) hp

/-- **F5, point-set part**: the whole slim fibre through a point of a cusp front in `X₃` lies in
that front. -/
theorem cuspFront_fibre_subset_BGR {Bs : BoundaryGaf02BasesV2 C.toChain}
    (WF : BoundaryWholeFiberSpecV2 C.toChain Bs) (Z : BoundaryActualZeroDomains_BIFc C.toChain Bs)
    {rd : ℝ} (hrd : 0 < rd) (hrd4 : rd < 1 / 10000) (hrdc : 20 * (c 2 + 1) * rd < 1 / 1000000)
    (hprem : 1000 * δn ^ 2 < w / (2 * (1 + 2 * Λ⁻¹) ^ 3) * min (1 / 2) (rd / 4) ^ 2)
    (hθ : θ < 1 / 100) (i : Fin S.packet.cusp.count) {p : W.Carrier}
    (hp : p ∈ C.toChain.cuspFront_BIF i) (hpX : p ∈ Bs.source 2) :
    Bs.fibre 2 (C.toChain.stageMap 2 p) ⊆ C.toChain.cuspFront_BIF i := by
  have hF := C.frontier_M₁_eq_iUnion_sum_BGR Z hrd hrd4 hrdc hprem hθ
  have hpF : p ∈ frontier C.toChain.M₁_BIFc := hF ▸ mem_iUnion.mpr ⟨Sum.inr i, hp⟩
  obtain ⟨hc, hd⟩ := C.faceFront_closed_disjoint_BGR Z.toBoundaryZeroDefining_BIFc hrd hrd4 hrdc
    hprem hθ
  exact subset_piece_of_isPreconnected_BGR hc hd
    (isPreconnected_slimFibre_BGR WF (Bs.image_eq 2 ▸ mem_image_of_mem _ hpX))
    ((fibre_subset_frontier_M₁_BGR WF Z hpF hpX).trans hF.subset) ⟨hpX, rfl⟩
    (i := Sum.inr i) hp

end BoundaryGaf02ChainE

end DifferentialGeometry.Geometry.Collapse
