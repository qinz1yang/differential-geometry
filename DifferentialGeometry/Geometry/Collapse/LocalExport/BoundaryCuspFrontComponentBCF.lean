import DifferentialGeometry.Geometry.Collapse.LocalExport.BoundaryCuspTorusClauseBCF

/-!
# BCF03's cusp dichotomy, point-set part (lane S-BCF134c, suffix `_BCF`; text v3.1 G7 part 2)

Blueprint BCF03: "If `H_b` meets `X₃`, BCF01 already identifies it with a whole torus boundary
fiber of `S` [...]. Otherwise it is disjoint from `S` and remains an entire component of `∂M₂`.
[...] `H_b` is disjoint from `P`, hence `H_b ⊂ R`, and a whole smooth boundary component of `R`."

Everything of this that is point-set topology on the delivered objects (no smoothness of `M₂`, no
face count), on ANY slim cut or the arc form:

* generic: `eq_connectedComponentIn_of_closed_split_BCF` (a preconnected closed `H ⊆ F ⊆ H ∪ Q`, `Q`
  closed and disjoint from `H`, is the connected component of `F` at any of its points),
  `isClosed_sdiff_relInterior_BCF`, `relInterior_subset_BCF`, `frontier_remainder_subset_BCF`
  (`∂(M \ int_M P) ⊆ ∂M ∪ P` for closed `M`, `P`);
* `BoundaryGaf02ChainE.isPreconnected_cuspFront_BCF`: a cusp front is connected (the smooth
  `T² × [0,1]` of BCG06);
* `BoundaryActualZeroDomains_BIFc.isClosed_slimPieceOf_BCF`: the slim piece of a compact cut is
  closed;
* **`BoundaryGaf02ChainE.cuspFront_component_frontier_M₂_BCF`** (L1): a cusp front disjoint from
  `X₃` lies in `∂M₂`, is disjoint from `S`, and IS a connected component of `∂M₂`;
* **`BoundaryGaf02ChainE.cuspFront_component_frontier_remainder_BCF`** (L2, arc form): if moreover
  the edge piece is closed (BCF02's compactness) and misses the front (the disk count of a torus
  face, FC40 on the BCF03 partition — the inputs left to those rows), then the front is a
  connected component of `∂R_c`, lies in `R_c` and misses `P_e`: the right branch of the frozen
  dichotomy.
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

section Generic

variable {X : Type*} [TopologicalSpace X]

/-- A closed preconnected `H ⊆ F ⊆ H ∪ Q` with `Q` closed and disjoint from `H` is the connected
component of `F` at each of its points. -/
theorem eq_connectedComponentIn_of_closed_split_BCF {H Q F : Set X} (hHc : IsClosed H)
    (hQc : IsClosed Q) (hHQ : Disjoint H Q) (hH : IsPreconnected H) (hHF : H ⊆ F)
    (hF : F ⊆ H ∪ Q) {p : X} (hp : p ∈ H) : H = connectedComponentIn F p := by
  refine Subset.antisymm (hH.subset_connectedComponentIn hp hHF) ?_
  have hpc : IsPreconnected (connectedComponentIn F p) := isPreconnected_connectedComponentIn
  have hpF : p ∈ connectedComponentIn F p := mem_connectedComponentIn (hHF hp)
  have hsub : connectedComponentIn F p ⊆ F := connectedComponentIn_subset F p
  rcases isPreconnected_iff_subset_of_disjoint_closed.mp hpc H Q hHc hQc (hsub.trans hF)
    (by rw [hHQ.inter_eq, inter_empty]) with h | h
  · exact h
  · exact absurd (h hpF) (Set.disjoint_left.mp hHQ hp)

/-- The relative interior of `Z` in `Y` lies in `Z`. -/
theorem relInterior_subset_BCF {Y Z : Set X} : relInterior_BIF Y Z ⊆ Z := fun x hx => by
  obtain ⟨hxY, O, -, hxO, hO⟩ := mem_relInterior_iff_BCF.mp hx
  exact hO ⟨hxO, hxY⟩

/-- `M \ int_M A` is closed for a closed `M`. -/
theorem isClosed_sdiff_relInterior_BCF {M : Set X} (hM : IsClosed M) (A : Set X) :
    IsClosed (M \ relInterior_BIF M A) := by
  have h : M \ relInterior_BIF M A = Subtype.val '' (interior (Subtype.val ⁻¹' A : Set M))ᶜ := by
    ext x
    constructor
    · rintro ⟨hxM, hx⟩
      exact ⟨⟨x, hxM⟩, fun hi => hx ⟨⟨x, hxM⟩, hi, rfl⟩, rfl⟩
    · rintro ⟨y, hy, rfl⟩
      refine ⟨y.2, fun ⟨z, hz, hzy⟩ => hy ?_⟩
      have hzy' : z = y := Subtype.ext hzy
      rwa [hzy'] at hz
  rw [h]
  exact hM.isClosedEmbedding_subtypeVal.isClosedMap _ isOpen_interior.isClosed_compl

/-- **The frontier of the remainder**: `∂(M \ int_M P) ⊆ ∂M ∪ P` for closed `M` and `P`. -/
theorem frontier_remainder_subset_BCF {M P : Set X} (hM : IsClosed M) (hP : IsClosed P) :
    frontier (M \ relInterior_BIF M P) ⊆ frontier M ∪ P := by
  intro x hx
  by_contra hne
  rw [mem_union, not_or] at hne
  obtain ⟨hxF, hxP⟩ := hne
  have hxM : x ∈ M := (hM.closure_subset_iff.mpr sdiff_subset) hx.1
  have hxi : x ∈ interior M := by
    by_contra h
    exact hxF ⟨subset_closure hxM, h⟩
  apply hx.2
  rw [mem_interior]
  refine ⟨interior M ∩ Pᶜ, ?_, isOpen_interior.inter hP.isOpen_compl, hxi, hxP⟩
  intro y hy
  exact ⟨interior_subset hy.1, fun hr => hy.2 (relInterior_subset_BCF hr)⟩

end Generic

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
    δn n B oM}

namespace BoundaryActualZeroDomains_BIFc

variable {Φ : BoundaryInteriorSlots_BIF S} {D : BoundaryAugmentedData S Φ} {Kj : ℕ}
  {Ξ Sg eg c cw : Fin 3 → ℝ} {bcut bder κ : ℝ}
  {C : BoundaryGaf02Chain D Kj Ξ Sg eg c cw bcut bder κ} {Bs : BoundaryGaf02BasesV2 C}

/-- **The slim piece of a compact cut is closed** (properness of `f₃|X₃`, `S ⊆ M₁` closed). -/
theorem isClosed_slimPieceOf_BCF (Z : BoundaryActualZeroDomains_BIFc C Bs)
    {Kset : Set (BoundaryAmbient_BIF S.IntTag_BAUGA (Fin S.packet.cusp.count))}
    (hK : IsCompact Kset) (hKB : Kset ⊆ Bs.base 2) : IsClosed (Bs.slimPieceOf_BIFc Kset) := by
  have heq : Bs.slimPieceOf_BIFc Kset = (Bs.source 2 ∩ C.stageMap 2 ⁻¹' Kset) ∩ C.M₁_BIFc := by
    ext q
    constructor
    · intro hq
      exact ⟨⟨hq.1, hq.2.1⟩, Z.slimPieceOf_subset_M₁_BIF Kset hq⟩
    · rintro ⟨⟨hqX, hqK⟩, hqM⟩
      exact ⟨hqX, hqK, q, ⟨hqM, hqX⟩, rfl⟩
  rw [heq]
  exact ((Bs.proper 2 Kset hKB hK).inter_right C.isClosed_M₁_BCF).isClosed

end BoundaryActualZeroDomains_BIFc

variable {Γ Sg eg : Fin 3 → ℝ}
  {DP : BoundaryAugmentedDataPV3 S (actualSlotsV2_BAUGD S) Γ Sg eg} {Kj : ℕ}
  {Ξ c cw : Fin 3 → ℝ} {bcut bder κ cadj : ℝ}

namespace BoundaryGaf02ChainE

variable (C : BoundaryGaf02ChainE DP Kj Ξ c cw bcut bder κ cadj)

/-- **A cusp front is connected and nonempty** (the smooth `T² × [0,1]` of BCG06: the front is the
image of `T² × {1}`). -/
theorem isConnected_cuspFront_BCF {rd : ℝ} (hrd : 0 < rd) (hrd4 : rd < 1 / 10000)
    (hrdc : 20 * (c 2 + 1) * rd < 1 / 1000000)
    (hprem : 1000 * δn ^ 2 < w / (2 * (1 + 2 * Λ⁻¹) ^ 3) * min (1 / 2) (rd / 4) ^ 2)
    (hθ : θ < 1 / 100) (i : Fin S.packet.cusp.count) :
    IsConnected (C.toChain.cuspFront_BIF i) := by
  have hcomp := (C.bcg06_on_boundary_chain_BGR hrd hrd4 hrdc hprem hθ).1 i
  have hfc : C.toChain.cuspFront_BIF i ⊆ C.toChain.cuspCore_BIF i := by
    have h := hcomp.compact_core.isClosed.frontier_subset
    rw [hcomp.relative_frontier_eq] at h
    exact h
  obtain ⟨cs, hcs⟩ := hcomp.labelled_smooth_product
  let _ := cs
  obtain ⟨-, -, -, D, -, hD1⟩ := hcs
  have hset : C.toChain.cuspFront_BIF i =
      (fun p => ((D p : C.toChain.cuspCore_BIF i) : W.Carrier)) '' {p | (p.2 : ℝ) = 1} := by
    ext x
    constructor
    · intro hx
      obtain ⟨p, hp⟩ := D.surjective ⟨x, hfc hx⟩
      have hp' : ((D p : C.toChain.cuspCore_BIF i) : W.Carrier) = x := congrArg Subtype.val hp
      exact ⟨p, (hD1 p).mp (by rw [hp']; exact hx), hp'⟩
    · rintro ⟨p, hp, rfl⟩
      exact (hD1 p).mpr hp
  rw [hset]
  have hP : IsConnected {p : Torus × Icc (0 : ℝ) 1 | (p.2 : ℝ) = 1} := by
    have : {p : Torus × Icc (0 : ℝ) 1 | (p.2 : ℝ) = 1} =
        (univ : Set Torus) ×ˢ {(⟨1, zero_le_one, le_rfl⟩ : Icc (0 : ℝ) 1)} := by
      ext ⟨t, q⟩
      constructor
      · intro h
        exact ⟨mem_univ t, Subtype.ext h⟩
      · rintro ⟨-, hq⟩
        exact congrArg Subtype.val hq
    rw [this]
    exact isConnected_univ.prod isConnected_singleton
  exact hP.image _ (continuous_subtype_val.comp D.continuous).continuousOn

/-- A cusp front is preconnected. -/
theorem isPreconnected_cuspFront_BCF {rd : ℝ} (hrd : 0 < rd) (hrd4 : rd < 1 / 10000)
    (hrdc : 20 * (c 2 + 1) * rd < 1 / 1000000)
    (hprem : 1000 * δn ^ 2 < w / (2 * (1 + 2 * Λ⁻¹) ^ 3) * min (1 / 2) (rd / 4) ^ 2)
    (hθ : θ < 1 / 100) (i : Fin S.packet.cusp.count) :
    IsPreconnected (C.toChain.cuspFront_BIF i) :=
  (C.isConnected_cuspFront_BCF hrd hrd4 hrdc hprem hθ i).isPreconnected

/-- **The closed split of `∂M₂` at a cusp front off `X₃`**: for a front `H` disjoint from `X₃` there
is a closed `Q` disjoint from `H` with `S ⊆ Q` and `H ⊆ ∂M₂ ⊆ H ∪ Q` (`Q` = the other faces and
fronts of `∂M₁` together with the slim piece; F4c, G3). -/
theorem cuspFront_split_BCF {Bs : BoundaryGaf02BasesV2 C.toChain}
    (Z : BoundaryActualZeroDomains_BIFc C.toChain Bs) {rd : ℝ} (hrd : 0 < rd)
    (hrd4 : rd < 1 / 10000) (hrdc : 20 * (c 2 + 1) * rd < 1 / 1000000)
    (hprem : 1000 * δn ^ 2 < w / (2 * (1 + 2 * Λ⁻¹) ^ 3) * min (1 / 2) (rd / 4) ^ 2)
    (hθ : θ < 1 / 100)
    {Kset : Set (BoundaryAmbient_BIF S.IntTag_BAUGA (Fin S.packet.cusp.count))}
    (hK : BoundarySlimCut_BIFc Bs Kset) (i : Fin S.packet.cusp.count)
    (hi : C.toChain.cuspFront_BIF i ∩ Bs.source 2 = ∅) :
    ∃ Q : Set W.Carrier, IsClosed Q ∧ Disjoint (C.toChain.cuspFront_BIF i) Q ∧
      Bs.slimPieceOf_BIFc Kset ⊆ Q ∧
      C.toChain.cuspFront_BIF i ⊆ frontier (Bs.M₂Of_BIFc Kset) ∧
      frontier (Bs.M₂Of_BIFc Kset) ⊆ C.toChain.cuspFront_BIF i ∪ Q := by
  have hF4c := C.frontier_M₁_eq_iUnion_sum_BGR Z hrd hrd4 hrdc hprem hθ
  obtain ⟨hcl, hdisj⟩ := C.faceFront_closed_disjoint_BGR Z.toBoundaryZeroDefining_BIFc hrd hrd4
    hrdc hprem hθ
  have hSc : IsClosed (Bs.slimPieceOf_BIFc Kset) :=
    Z.isClosed_slimPieceOf_BCF hK.isCompact hK.subset_base
  have hHc : IsClosed (C.toChain.cuspFront_BIF i) := hcl (Sum.inr i)
  have hQ1c : IsClosed (⋃ t : {t : S.ZeroIdx_BAUGC ⊕ Fin S.packet.cusp.count // t ≠ Sum.inr i},
      Sum.elim C.toChain.actualZeroFace_BIFc C.toChain.cuspFront_BIF t.1) :=
    isClosed_iUnion_of_finite fun t => hcl t.1
  have hHQ1 : Disjoint (C.toChain.cuspFront_BIF i)
      (⋃ t : {t : S.ZeroIdx_BAUGC ⊕ Fin S.packet.cusp.count // t ≠ Sum.inr i},
        Sum.elim C.toChain.actualZeroFace_BIFc C.toChain.cuspFront_BIF t.1) :=
    Set.disjoint_iUnion_right.mpr fun t => hdisj (Ne.symm t.2)
  have hHS : Disjoint (C.toChain.cuspFront_BIF i) (Bs.slimPieceOf_BIFc Kset) :=
    Set.disjoint_left.mpr fun x hx hxS => by
      have : x ∈ C.toChain.cuspFront_BIF i ∩ Bs.source 2 := ⟨hx, hxS.1⟩
      rw [hi] at this
      exact this
  have hHf : C.toChain.cuspFront_BIF i ⊆ frontier C.toChain.M₁_BIFc := fun x hx =>
    hF4c ▸ mem_iUnion.mpr ⟨Sum.inr i, hx⟩
  obtain ⟨-, hG3, -⟩ := bcf01_faces_BCF01 Z hK
  refine ⟨(⋃ t : {t : S.ZeroIdx_BAUGC ⊕ Fin S.packet.cusp.count // t ≠ Sum.inr i},
      Sum.elim C.toChain.actualZeroFace_BIFc C.toChain.cuspFront_BIF t.1) ∪
      Bs.slimPieceOf_BIFc Kset, hQ1c.union hSc, hHQ1.union_right hHS, subset_union_right, ?_, ?_⟩
  · intro x hx
    rw [hG3]
    exact Or.inl ⟨hHf hx, fun hxS => Set.disjoint_left.mp hHS hx hxS⟩
  · intro x hx
    rw [hG3] at hx
    rcases hx with ⟨hx1, -⟩ | ⟨hx2, -⟩
    · obtain ⟨t, ht⟩ := mem_iUnion.mp (hF4c ▸ hx1)
      by_cases hti : t = Sum.inr i
      · subst hti
        exact Or.inl ht
      · exact Or.inr (Or.inl (mem_iUnion.mpr ⟨⟨t, hti⟩, ht⟩))
    · exact Or.inr (Or.inr (hSc.frontier_subset hx2))

/-- **L1: a cusp front off `X₃` is a whole connected component of `∂M₂`** (and misses `S`): the
first half of the right branch of BCF03's dichotomy ("remains an entire component of `∂M₂`"),
for ANY slim cut. -/
theorem cuspFront_component_frontier_M₂_BCF {Bs : BoundaryGaf02BasesV2 C.toChain}
    (Z : BoundaryActualZeroDomains_BIFc C.toChain Bs) {rd : ℝ} (hrd : 0 < rd)
    (hrd4 : rd < 1 / 10000) (hrdc : 20 * (c 2 + 1) * rd < 1 / 1000000)
    (hprem : 1000 * δn ^ 2 < w / (2 * (1 + 2 * Λ⁻¹) ^ 3) * min (1 / 2) (rd / 4) ^ 2)
    (hθ : θ < 1 / 100)
    {Kset : Set (BoundaryAmbient_BIF S.IntTag_BAUGA (Fin S.packet.cusp.count))}
    (hK : BoundarySlimCut_BIFc Bs Kset) (i : Fin S.packet.cusp.count)
    (hi : C.toChain.cuspFront_BIF i ∩ Bs.source 2 = ∅) {p : W.Carrier}
    (hp : p ∈ C.toChain.cuspFront_BIF i) :
    C.toChain.cuspFront_BIF i ⊆ frontier (Bs.M₂Of_BIFc Kset) ∧
      Disjoint (C.toChain.cuspFront_BIF i) (Bs.slimPieceOf_BIFc Kset) ∧
      C.toChain.cuspFront_BIF i = connectedComponentIn (frontier (Bs.M₂Of_BIFc Kset)) p := by
  obtain ⟨Q, hQc, hHQ, hSQ, hHF, hF⟩ := C.cuspFront_split_BCF Z hrd hrd4 hrdc hprem hθ hK i hi
  obtain ⟨hcl, -⟩ := C.faceFront_closed_disjoint_BGR Z.toBoundaryZeroDefining_BIFc hrd hrd4 hrdc
    hprem hθ
  exact ⟨hHF, hHQ.mono_right hSQ, eq_connectedComponentIn_of_closed_split_BCF (hcl (Sum.inr i)) hQc
    hHQ (C.isPreconnected_cuspFront_BCF hrd hrd4 hrdc hprem hθ i) hHF hF hp⟩

/-- **L2: the right branch of BCF03's cusp dichotomy** (arc form): a cusp front off `X₃` whose torus
face carries no horizontal disk (`H_b ∩ P_e = ∅`) and whose edge piece is closed (BCF02) is a whole
connected component of `∂R_c`, lies in `R_c` and misses `P_e`. The two inputs `hPe`, `hdisk` are
exactly what this lane cannot supply: BCF02's compactness of `P_e` and the disk count of a torus
(FC40 on the BCF03 partition). -/
theorem cuspFront_component_frontier_remainder_BCF {Bs : BoundaryGaf02BasesV2 C.toChain}
    (Z : BoundaryActualZeroDomains_BIFc C.toChain Bs) {rd : ℝ} (hrd : 0 < rd)
    (hrd4 : rd < 1 / 10000) (hrdc : 20 * (c 2 + 1) * rd < 1 / 1000000)
    (hprem : 1000 * δn ^ 2 < w / (2 * (1 + 2 * Λ⁻¹) ^ 3) * min (1 / 2) (rd / 4) ^ 2)
    (hθ : θ < 1 / 100) (Kc : BoundaryCompactSlimChoiceV2 Bs) (hPe : IsClosed Kc.edgePiece)
    (i : Fin S.packet.cusp.count) (hi : C.toChain.cuspFront_BIF i ∩ Bs.source 2 = ∅)
    (hdisk : Disjoint (C.toChain.cuspFront_BIF i) Kc.edgePiece) {p : W.Carrier}
    (hp : p ∈ C.toChain.cuspFront_BIF i) :
    p ∈ Kc.remainder ∧ C.toChain.cuspFront_BIF i = connectedComponentIn (frontier Kc.remainder) p ∧
      Disjoint (C.toChain.cuspFront_BIF i) Kc.edgePiece := by
  obtain ⟨Q, hQc, hHQ, hSQ, hHF, hF⟩ := C.cuspFront_split_BCF Z hrd hrd4 hrdc hprem hθ
    Kc.slimCut_BIFc i hi
  obtain ⟨hcl, -⟩ := C.faceFront_closed_disjoint_BGR Z.toBoundaryZeroDefining_BIFc hrd hrd4 hrdc
    hprem hθ
  have hM₂c : IsClosed Kc.M₂ := isClosed_sdiff_relInterior_BCF C.toChain.isClosed_M₁_BCF Kc.piece
  have hRc : IsClosed Kc.remainder := isClosed_sdiff_relInterior_BCF hM₂c Kc.edgePiece
  have hHM : C.toChain.cuspFront_BIF i ⊆ Kc.M₂ := fun x hx => hM₂c.frontier_subset (hHF hx)
  have hHR : C.toChain.cuspFront_BIF i ⊆ Kc.remainder := fun x hx =>
    ⟨hHM hx, fun hxr => Set.disjoint_left.mp hdisk hx (relInterior_subset_BCF hxr)⟩
  have hHFR : C.toChain.cuspFront_BIF i ⊆ frontier Kc.remainder := fun x hx =>
    ⟨subset_closure (hHR hx), fun hxi => (hHF hx).2 (interior_mono sdiff_subset hxi)⟩
  have hFR : frontier Kc.remainder ⊆ C.toChain.cuspFront_BIF i ∪ (Q ∪ Kc.edgePiece) := by
    intro x hx
    rcases frontier_remainder_subset_BCF hM₂c hPe hx with hx1 | hx2
    · rcases hF hx1 with h | h
      · exact Or.inl h
      · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr hx2)
  exact ⟨hHR hp, eq_connectedComponentIn_of_closed_split_BCF (hcl (Sum.inr i)) (hQc.union hPe)
    (hHQ.union_right hdisk) (C.isPreconnected_cuspFront_BCF hrd hrd4 hrdc hprem hθ i) hHFR hFR hp,
    hdisk⟩

end BoundaryGaf02ChainE

end DifferentialGeometry.Geometry.Collapse
