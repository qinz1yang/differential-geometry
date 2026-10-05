import DifferentialGeometry.Geometry.Collapse.LocalExport.BoundaryInterfaceCoresSat
import DifferentialGeometry.Geometry.Collapse.LocalExport.BoundaryInterfaceCorollaries
import DifferentialGeometry.Geometry.Collapse.LocalExport.BoundaryRigidityContributorBGR
import DifferentialGeometry.Geometry.Collapse.LocalExport.BoundaryActualSlot

/-!
# Zero cores with saturated faces: the algebraic saturation and the `Sat` kernel (lane B-BCG-ROWS)

Blueprint `master207B.tex`, BCG07 (B:9471, "every whole fibre of `π_jE` meeting `H_b` lies in
`H_b`", "the connected-fibre argument of ZSP03 applies to both sorts of disjoint internal face");
ZSP03 (B:6481). Closed twins: `Gaf02Chain.zero_face_saturated_ZSP35`,
`Gaf02Chain.zero_base_function_ZSP35` (`Fibration/ActualStageChainZeroFaces.lean`). Lead decision
2026-10-05 13:4x: the producer of B-BCF134's `BoundaryInitialCoresSpecSat` is this lane's.

* Topology: `mem_interior_of_isPreconnected_BGR` (a preconnected set meeting `int A` whose
  intersection with a frontier carrier `F ⊇ ∂A`, `F ∩ int A = ∅`, is all-or-nothing lies in
  `int A`); `isPreconnected_of_homeomorph_BGR`; finite disjoint closed pieces
  (`frontier_iUnion_subset_of_finite_BGR`, `disjoint_iUnion_frontier_interior_BGR`).
* Algebra on the chain: the zero blocks of `C.E` are constant along every `f_st`-fibre when the
  zero tag is a stage tag (`zeroSlot_eq_of_stageMap_eq_BGR`); the canonical (ZF) face
  `zeroFace_BGR` and marker sublevel `zeroSublevel_BGR` are saturated
  (`zeroFace_saturated_BGR`, `zeroSublevel_saturated_BGR`); the base function `u_k/v_k − 2/5`
  descends through `π_st` (`zero_base_function_BGR`); on the ACTUAL slot every zero tag is a tag of
  every stage (`zeroTag_mem_stageTags_BGR`).
* **`BoundaryInitialCoresSpec.toSat_of_frontier_BGR`**: B-BCF134's `face_saturated` from a frontier
  carrier `F` saturated along the stage maps and the connected whole fibres of
  `BoundaryWholeFiberSpec` (ZSP03's connected-fibre argument);
  **`BoundaryInitialCoresSpec.toSat_of_faces_BGR`**: the same with `F` = the zero faces and the cusp
  fronts, from `∂Z_k = (ZF)_k` (ZSP02 on `C.E`) and BCG06's `∂C_b = H_b`.
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

variable {X : Type*} [TopologicalSpace X]

/-- **ZSP03's connected-fibre argument**: let `F ⊇ ∂A` with `F ∩ int A = ∅`, and `Z` preconnected
such that `Z` meets `F` only if `Z ⊆ F`. If `Z` meets `int A`, then `Z ⊆ int A`. -/
theorem mem_interior_of_isPreconnected_BGR {A F Z : Set X} (hZ : IsPreconnected Z)
    (hfr : frontier A ⊆ F) (hFA : Disjoint F (interior A))
    (hsat : (Z ∩ F).Nonempty → Z ⊆ F) {p q : X} (hp : p ∈ Z) (hq : q ∈ Z)
    (hqA : q ∈ interior A) : p ∈ interior A := by
  have hZF : ¬ (Z ∩ F).Nonempty := fun h => Set.disjoint_left.mp hFA (hsat h hq) hqA
  have hcover : Z ⊆ interior A ∪ (closure A)ᶜ := by
    intro x hx
    by_cases hxi : x ∈ interior A
    · exact Or.inl hxi
    · refine Or.inr fun hxc => hZF ⟨x, hx, hfr ⟨hxc, hxi⟩⟩
  have hdisj : Disjoint (interior A) (closure A)ᶜ :=
    Set.disjoint_left.mpr fun x hx hxc => hxc (interior_subset.trans subset_closure hx)
  exact hZ.subset_left_of_subset_union isOpen_interior isClosed_closure.isOpen_compl hdisj hcover
    ⟨q, hq, hqA⟩ hp

/-- A set homeomorphic to a preconnected space is preconnected. -/
theorem isPreconnected_of_homeomorph_BGR {Y : Type*} [TopologicalSpace Y] [PreconnectedSpace Y]
    {s : Set X} (e : s ≃ₜ Y) : IsPreconnected s := by
  have h := isPreconnected_range (f := fun y : Y => ((e.symm y : s) : X))
    (continuous_subtype_val.comp e.symm.continuous)
  have hr : range (fun y : Y => ((e.symm y : s) : X)) = s := by
    ext x
    refine ⟨fun ⟨y, hy⟩ => hy ▸ (e.symm y).2, fun hx => ⟨e ⟨x, hx⟩, ?_⟩⟩
    simp
  rwa [hr] at h

/-- The frontier of a finite union lies in the union of the frontiers. -/
theorem frontier_iUnion_subset_of_finite_BGR {ι : Type*} [Finite ι] (P : ι → Set X) :
    frontier (⋃ i, P i) ⊆ ⋃ i, frontier (P i) := by
  intro x ⟨hxc, hxi⟩
  rw [closure_iUnion_of_finite] at hxc
  obtain ⟨i, hi⟩ := mem_iUnion.mp hxc
  refine mem_iUnion.mpr ⟨i, hi, fun hint => hxi ?_⟩
  exact interior_mono (subset_iUnion P i) hint

/-- **Disjoint closed pieces**: the frontier of a piece of a finite family of pairwise disjoint
closed sets never meets the interior of the union. -/
theorem disjoint_iUnion_frontier_interior_BGR {ι : Type*} [Finite ι] (P : ι → Set X)
    (hcl : ∀ i, IsClosed (P i)) (hd : Pairwise (Disjoint on P)) :
    Disjoint (⋃ i, frontier (P i)) (interior (⋃ i, P i)) := by
  rw [Set.disjoint_left]
  intro x hx hxA
  obtain ⟨j, hxj⟩ := mem_iUnion.mp hx
  have hxPj : x ∈ P j := (hcl j).frontier_subset hxj
  set U : Set X := interior (⋃ i, P i) ∩ (⋃ i ∈ ({j}ᶜ : Set ι), P i)ᶜ with hU
  have hcl' : IsClosed (⋃ i ∈ ({j}ᶜ : Set ι), P i) :=
    (Set.toFinite _).isClosed_biUnion fun i _ => hcl i
  have hUo : IsOpen U := isOpen_interior.inter hcl'.isOpen_compl
  have hxU : x ∈ U := by
    refine ⟨hxA, ?_⟩
    simp only [mem_compl_iff, mem_iUnion, not_exists]
    intro i hi hxi
    exact Set.disjoint_left.mp (hd (Ne.symm hi)) hxPj hxi
  have hUP : U ⊆ P j := by
    intro y ⟨hyA, hyo⟩
    obtain ⟨i, hyi⟩ := mem_iUnion.mp (interior_subset hyA)
    by_contra hyj
    have hij : i ≠ j := fun h => hyj (h ▸ hyi)
    exact hyo (mem_biUnion (show i ∈ ({j}ᶜ : Set ι) from hij) hyi)
  exact hxj.2 (interior_maximal hUP hUo hxU)

end Topology

variable {K : ℕ} {A : ℝ → ℝ} {β : ℕ → ℝ}
  {βd εN Λ w Δ σs σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs ζ Λz θ : ℝ}
  {W : CompactCarrier.{0}} [ConnectedSpace W.Carrier] {g : SmoothRiemannianMetric W.model W.Carrier}
  {δn : ℝ} {n : ℕ} {B : NearlyCuspidalBoundary W g K δn}
  {oM : ManifoldOrientation 𝓘(ℝ, E3) (W.pieceInterior ⊤) 3}

/-- On the ACTUAL slot every zero tag is a tag of every stage (`Q_j^∂ ⊇ Q₄`, closed pattern). -/
theorem zeroTag_mem_stageTags_BGR
    (S : BoundarySupply K A β βd εN Λ w Δ σs σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs ζ Λz θ
      W g δn n B oM) (k : S.ZeroIdx_BAUGC) (st : Fin 3) :
    S.zeroTag_BAUGC k ∈ (actualSlots_BAUGD S).stageTags st := by
  fin_cases st
  · exact Finset.mem_univ _
  · exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, rfl⟩
  · exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, rfl⟩

namespace BoundaryGaf02Chain

variable {S : BoundarySupply K A β βd εN Λ w Δ σs σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs ζ
  Λz θ W g δn n B oM} {Φ : BoundaryInteriorSlots_BIF S} {D : BoundaryAugmentedData S Φ}
  {Kj : ℕ} {Ξ Sg eg c cw : Fin 3 → ℝ} {bcut bder κ : ℝ}
  (C : BoundaryGaf02Chain D Kj Ξ Sg eg c cw bcut bder κ)

/-- **The interior blocks of the stage tags are constant along the fibres of `f_st = π_st ∘ E`.** -/
theorem slot_eq_of_stageMap_eq_BGR {st : Fin 3} {t : S.IntTag_BAUGA} (ht : t ∈ Φ.stageTags st)
    {p q : W.Carrier} (h : C.stageMap st q = C.stageMap st p) :
    C.E q (Sum.inl t) = C.E p (Sum.inl t) := by
  have h1 := congrArg (fun v : BoundaryAmbient_BIF S.IntTag_BAUGA (Fin S.packet.cusp.count) =>
    v (Sum.inl t)) h
  simp only [BoundaryGaf02Chain.stageMap] at h1
  change blockRestrict (Φ.stageTagsAug st) (C.E q) (Sum.inl t) =
    blockRestrict (Φ.stageTagsAug st) (C.E p) (Sum.inl t) at h1
  rwa [BoundaryInteriorSlots_BIF.stageTagsAug, blockRestrict_disjSum_inl_BGR ht,
    blockRestrict_disjSum_inl_BGR ht] at h1

/-- **The canonical zero face** (ZF) of `C.E` at the zero centre `k`:
`E⁻¹{v_k ≥ .9R_k, u_k = .4v_k}` (closed `zspFace_ZSP35`). -/
def zeroFace_BGR (k : S.ZeroIdx_BAUGC) : Set W.Carrier :=
  {p | 9 / 10 * S.zeroRadius_BAUGC k ≤ (C.E p (Sum.inl (S.zeroTag_BAUGC k))).snd ∧
    ((C.E p (Sum.inl (S.zeroTag_BAUGC k))).fst : ℝ²) 0 =
      2 / 5 * (C.E p (Sum.inl (S.zeroTag_BAUGC k))).snd}

/-- **The canonical zero marker sublevel** of `C.E` at `k`: `E⁻¹{v_k ≥ .9R_k, u_k ≤ .4v_k}`. -/
def zeroSublevel_BGR (k : S.ZeroIdx_BAUGC) : Set W.Carrier :=
  {p | 9 / 10 * S.zeroRadius_BAUGC k ≤ (C.E p (Sum.inl (S.zeroTag_BAUGC k))).snd ∧
    ((C.E p (Sum.inl (S.zeroTag_BAUGC k))).fst : ℝ²) 0 ≤
      2 / 5 * (C.E p (Sum.inl (S.zeroTag_BAUGC k))).snd}

/-- **(ZF) is saturated** for every `f_st` whose stage tags contain the zero tag. -/
theorem zeroFace_saturated_BGR {st : Fin 3} {k : S.ZeroIdx_BAUGC}
    (ht : S.zeroTag_BAUGC k ∈ Φ.stageTags st) {p q : W.Carrier} (hp : p ∈ C.zeroFace_BGR k)
    (h : C.stageMap st q = C.stageMap st p) : q ∈ C.zeroFace_BGR k := by
  have he := C.slot_eq_of_stageMap_eq_BGR ht h
  simp only [zeroFace_BGR, Set.mem_ofPred_eq] at hp ⊢
  rw [he]
  exact hp

/-- **The marker sublevel is saturated** for every `f_st` whose stage tags contain the zero tag. -/
theorem zeroSublevel_saturated_BGR {st : Fin 3} {k : S.ZeroIdx_BAUGC}
    (ht : S.zeroTag_BAUGC k ∈ Φ.stageTags st) {p q : W.Carrier} (hp : p ∈ C.zeroSublevel_BGR k)
    (h : C.stageMap st q = C.stageMap st p) : q ∈ C.zeroSublevel_BGR k := by
  have he := C.slot_eq_of_stageMap_eq_BGR ht h
  simp only [zeroSublevel_BGR, Set.mem_ofPred_eq] at hp ⊢
  rw [he]
  exact hp

/-- **The base function descends** (ZSP03): `b_k(w) = u_k(w)/v_k(w) − 2/5` satisfies
`b_k ∘ f_st = b_k ∘ E` when the zero tag is a stage tag. -/
theorem zero_base_function_BGR {st : Fin 3} {k : S.ZeroIdx_BAUGC}
    (ht : S.zeroTag_BAUGC k ∈ Φ.stageTags st) (p : W.Carrier) :
    ((C.stageMap st p (Sum.inl (S.zeroTag_BAUGC k))).fst : ℝ²) 0 /
        (C.stageMap st p (Sum.inl (S.zeroTag_BAUGC k))).snd - 2 / 5 =
      ((C.E p (Sum.inl (S.zeroTag_BAUGC k))).fst : ℝ²) 0 /
        (C.E p (Sum.inl (S.zeroTag_BAUGC k))).snd - 2 / 5 := by
  change ((blockRestrict (Φ.stageTagsAug st) (C.E p) (Sum.inl (S.zeroTag_BAUGC k))).fst : ℝ²) 0 /
        (blockRestrict (Φ.stageTagsAug st) (C.E p) (Sum.inl (S.zeroTag_BAUGC k))).snd - 2 / 5 = _
  rw [BoundaryInteriorSlots_BIF.stageTagsAug, blockRestrict_disjSum_inl_BGR ht]

end BoundaryGaf02Chain

namespace BoundaryInitialCoresSpec

variable {S : BoundarySupply K A β βd εN Λ w Δ σs σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs ζ
  Λz θ W g δn n B oM} {Φ : BoundaryInteriorSlots_BIF S} {D : BoundaryAugmentedData S Φ}
  {Kj : ℕ} {Ξ Sg eg c cw : Fin 3 → ℝ} {bcut bder κ : ℝ}
  {C : BoundaryGaf02Chain D Kj Ξ Sg eg c cw bcut bder κ} {Bs : BoundaryGaf02Bases C}

/-- The whole circle and slim fibres are preconnected. -/
theorem isPreconnected_fibre_BGR (WF : BoundaryWholeFiberSpec C Bs) {st : Fin 3} (hst : st ≠ 1)
    {y : BoundaryAmbient_BIF S.IntTag_BAUGA (Fin S.packet.cusp.count)} (hy : y ∈ Bs.base st) :
    IsPreconnected (Bs.fibre st y) := by
  fin_cases st
  · obtain ⟨e⟩ := WF.circle_fibre y hy
    exact isPreconnected_of_homeomorph_BGR e
  · exact absurd rfl hst
  · obtain ⟨e⟩ := WF.slim_fibre y hy
    exact isPreconnected_of_homeomorph_BGR e

/-- **The `Sat` kernel** (ZSP03's connected-fibre argument on the boundary chain): a frontier
carrier `F ⊇ ∂(Z ∪ C_∂)` disjoint from `int(Z ∪ C_∂)` and saturated along the circle and slim stage
maps, together with the connected whole fibres, makes `M₁ ∩ X_st` saturated (`st ≠ 1`). -/
def toSat_of_frontier_BGR (ZC : BoundaryInitialCoresSpec C) (WF : BoundaryWholeFiberSpec C Bs)
    (F : Set W.Carrier) (hfr : frontier ((⋃ k, ZC.core k) ∪ C.cuspCores_BIF) ⊆ F)
    (hFA : Disjoint F (interior ((⋃ k, ZC.core k) ∪ C.cuspCores_BIF)))
    (hFsat : ∀ st : Fin 3, st ≠ 1 → ∀ p ∈ Bs.source st, ∀ q ∈ Bs.source st,
      C.stageMap st q = C.stageMap st p → p ∈ F → q ∈ F) :
    BoundaryInitialCoresSpecSat C Bs where
  toBoundaryInitialCoresSpec := ZC
  face_saturated := fun st hst p hp q hq hpq hpA hqA => by
    have hy : C.stageMap st p ∈ Bs.base st := Bs.image_eq st ▸ mem_image_of_mem _ hp
    have hZ := isPreconnected_fibre_BGR WF hst hy
    refine hpA (mem_interior_of_isPreconnected_BGR hZ hfr hFA ?_ ⟨hp, rfl⟩ ⟨hq, hpq⟩ hqA)
    rintro ⟨r, ⟨hrX, hr⟩, hrF⟩ x ⟨hxX, hx⟩
    exact hFsat st hst r hrX x hxX (hx.trans hr.symm) hrF

/-- The underlying cores of `toSat_of_frontier_BGR` are the given ones. -/
theorem toSat_of_frontier_toSpec_BGR (ZC : BoundaryInitialCoresSpec C)
    (WF : BoundaryWholeFiberSpec C Bs) (F : Set W.Carrier)
    (hfr : frontier ((⋃ k, ZC.core k) ∪ C.cuspCores_BIF) ⊆ F)
    (hFA : Disjoint F (interior ((⋃ k, ZC.core k) ∪ C.cuspCores_BIF)))
    (hFsat : ∀ st : Fin 3, st ≠ 1 → ∀ p ∈ Bs.source st, ∀ q ∈ Bs.source st,
      C.stageMap st q = C.stageMap st p → p ∈ F → q ∈ F) :
    (ZC.toSat_of_frontier_BGR WF F hfr hFA hFsat).toBoundaryInitialCoresSpec = ZC :=
  rfl

/-- **The `Sat` kernel with the actual faces** (ZSP03 + BCG07 on the boundary chain): if every core
is bounded by the canonical (ZF) face of its zero centre (ZSP02 on `C.E`), every cusp core is
closed with frontier its global front `H_b` (BCG06), the pieces are pairwise disjoint and the zero
tags are stage tags, then the cores carry B-BCF134's `face_saturated`. -/
def toSat_of_faces_BGR (ZC : BoundaryInitialCoresSpec C) (WF : BoundaryWholeFiberSpec C Bs)
    (idx : Fin ZC.count → S.ZeroIdx_BAUGC)
    (hZF : ∀ k, frontier (ZC.core k) = C.zeroFace_BGR (idx k))
    (hCF : ∀ i, frontier (C.cuspCore_BIF i) = C.cuspFront_BIF i)
    (hCcl : ∀ i, IsClosed (C.cuspCore_BIF i))
    (hZC : ∀ k i, Disjoint (ZC.core k) (C.cuspCore_BIF i))
    (hCC : Pairwise (Disjoint on C.cuspCore_BIF))
    (htags : ∀ k st, S.zeroTag_BAUGC (idx k) ∈ Φ.stageTags st) :
    BoundaryInitialCoresSpecSat C Bs :=
  ZC.toSat_of_frontier_BGR WF (⋃ j, frontier (Sum.elim ZC.core C.cuspCore_BIF j))
    (by
      have h := frontier_iUnion_subset_of_finite_BGR (Sum.elim ZC.core C.cuspCore_BIF)
      rwa [Set.iUnion_sum] at h)
    (by
      have h := disjoint_iUnion_frontier_interior_BGR (Sum.elim ZC.core C.cuspCore_BIF)
        (fun j => by
          rcases j with k | i
          · exact (ZC.isCompact_core k).isClosed
          · exact hCcl i)
        (by
          rintro (k | i) (k' | i') hne
          · exact ZC.pairwise_disjoint (fun h => hne (congrArg Sum.inl h))
          · exact hZC k i'
          · exact (hZC k' i).symm
          · exact hCC (fun h => hne (congrArg Sum.inr h)))
      have hA : (⋃ j, Sum.elim ZC.core C.cuspCore_BIF j) =
          (⋃ k, ZC.core k) ∪ C.cuspCores_BIF := Set.iUnion_sum
      rwa [hA] at h)
    (fun st _ p _ q _ hpq hp => by
      obtain ⟨j, hj⟩ := mem_iUnion.mp hp
      refine mem_iUnion.mpr ⟨j, ?_⟩
      rcases j with k | i
      · change q ∈ frontier (ZC.core k)
        change p ∈ frontier (ZC.core k) at hj
        rw [hZF] at hj ⊢
        exact C.zeroFace_saturated_BGR (htags k st) hj hpq
      · change q ∈ frontier (C.cuspCore_BIF i)
        change p ∈ frontier (C.cuspCore_BIF i) at hj
        rw [hCF] at hj ⊢
        exact C.cuspFront_saturated_BIF st i hj hpq)

end BoundaryInitialCoresSpec

/-- **On the ACTUAL slot** the zero tags are stage tags (`zeroTag_mem_stageTags_BGR`): the `Sat`
kernel from the actual faces needs only ZSP02's and BCG06's frontier equalities and disjointness. -/
def BoundaryInitialCoresSpec.toSat_of_faces_actualSlots_BGR
    {S : BoundarySupply K A β βd εN Λ w Δ σs σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs ζ Λz θ
      W g δn n B oM} {D : BoundaryAugmentedData S (actualSlots_BAUGD S)} {Kj : ℕ}
    {Ξ Sg eg c cw : Fin 3 → ℝ} {bcut bder κ : ℝ}
    {C : BoundaryGaf02Chain D Kj Ξ Sg eg c cw bcut bder κ} {Bs : BoundaryGaf02Bases C}
    (ZC : BoundaryInitialCoresSpec C)
    (WF : BoundaryWholeFiberSpec C Bs) (idx : Fin ZC.count → S.ZeroIdx_BAUGC)
    (hZF : ∀ k, frontier (ZC.core k) = C.zeroFace_BGR (idx k))
    (hCF : ∀ i, frontier (C.cuspCore_BIF i) = C.cuspFront_BIF i)
    (hCcl : ∀ i, IsClosed (C.cuspCore_BIF i))
    (hZC : ∀ k i, Disjoint (ZC.core k) (C.cuspCore_BIF i))
    (hCC : Pairwise (Disjoint on C.cuspCore_BIF)) : BoundaryInitialCoresSpecSat C Bs :=
  ZC.toSat_of_faces_BGR WF idx hZF hCF hCcl hZC hCC fun k st =>
    zeroTag_mem_stageTags_BGR S (idx k) st

end DifferentialGeometry.Geometry.Collapse
