import DifferentialGeometry.Geometry.Collapse.LocalExport.BoundaryInterfaceFibresV2

/-!
# Boundary route interfaces v2, part 3: the actual zero domains of `C.E` (lane BIFACEc)

External review 69 §1.6 and lead disposition D69-4 (binding). v1's `BoundaryInitialCoresSpec C`
does not bind `core k` to `C.E` (its F4d is false for arbitrary cores, and a frontier type does
not determine the FC39 zero model). Here the zero domains ARE definitions of the SAME chain:

* `BoundaryGaf02Chain.actualZeroDomain_BIFc C k`: ZSP02's actual zero domain
  `Z_k = B_ĝ(z_k, .35R_k) ∪ {v_k(E) ≥ .9R_k, u_k(E) ≤ .4 v_k(E)}` at the zero block of `C.E`
  (closed twin `zspDomain_ZSP35`; NO bare ratio `u/v ≤ 2/5`, undefined where the marker vanishes);
  `actualZeroFace_BIFc C k`: `{v_k(E) ≥ .9R_k, u_k(E) = .4 v_k(E)}` (`zspFace_ZSP35`).
* `BoundaryActualZeroDomains_BIFc C Bs` (statement shape; PRODUCER = lane B-BCG-ROWS, section F):
  per zero index `k` a GLOBAL smooth defining function `defFn k` regular on its zero set with
  `Z_k = {defFn k ≤ 0}`, `face = {defFn k = 0}`, `∂Z_k = face`, the identification with the
  retained ratio ONLY on an open neighbourhood of the face where the marker is positive
  (`.99R_k < v_k(E)`, `defFn k = u_k/v_k − 2/5`), the transport of the ORIGINAL model sublevel
  `{radial_k ≤ 2/5}` onto `Z_k` by an ambient diffeomorphism of `W` (closed twin:
  `Gaf02ChainE.zsp02_domain_ZSP35`), the placement (`Z_k ⊆` original zero ball, `.38`-ball in the
  interior, compact, pairwise disjoint), the STANDARD smooth face parametrization (`S²` or `T²`,
  review 70 D70-5; closed `Gaf02ChainE.zsp02_face_standard_param_ZSP35`) and the saturation of
  `M₁` by the circle / slim fibres of the v2 bases (closed `Gaf02Chain.zero_face_saturated_ZSP35`).
* Weak projections: `toInitialCoresSpec_BIFc` (v1's `BoundaryInitialCoresSpec C`, cores = the actual
  domains, frontier types derived from the standard parametrization) and `toSat_BIFc`
  (`BoundaryInitialCoresSpecSat C Bs₁` on any v1 BASES object with the same circle / slim sources;
  the WEAK interface consumed by BCF01-G3 / BCF03).
* Inhabitant: `BoundaryGaf02Chain.emptyActualZeroDomains_BIFc` (no zero centre, empty v2 bases).
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
local notation "ℝ²" => EuclideanSpace ℝ (Fin 2)

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

namespace BoundarySupplyCore

/-- The original radial function `radial_k` of the selected zero ball of the zero index `k`. -/
def zeroRadial_BIFc (S : BoundarySupplyCore K A β βd εN Λ w Δ σs σc μ b s b' s' ε γc βc Lmax τ γ δ
    εr e T V vs ζ Λz W g δn n B oM) (k : S.ZeroIdx_BAUGC) : W.pieceInterior ⊤ → ℝ :=
  letI := inducedMetricSpace S.completion.metric
  letI := S.completion.complete
  letI := S.family.instMetricN
  letI := S.family.instChartedN
  letI := S.family.instMetricC
  (S.family.zero.zero k.1 ((Set.Finite.mem_toFinset _).mp k.2)).radial

end BoundarySupplyCore

namespace BoundaryGaf02Chain

/-- The zero-block marker `v_k(E p)` of the chain. -/
def zeroMarker_BIFc (C : BoundaryGaf02Chain D Kj Ξ Sg eg c cw bcut bder κ) (k : S.ZeroIdx_BAUGC)
    (p : W.Carrier) : ℝ :=
  (C.E p (Sum.inl (S.zeroTag_BAUGC k))).snd

/-- The zero-block retained coordinate `u_k(E p)` of the chain. -/
def zeroCoord_BIFc (C : BoundaryGaf02Chain D Kj Ξ Sg eg c cw bcut bder κ) (k : S.ZeroIdx_BAUGC)
    (p : W.Carrier) : ℝ :=
  ((C.E p (Sum.inl (S.zeroTag_BAUGC k))).fst : ℝ²) 0

/-- **ZSP02's actual zero domain of `C.E`** (closed twin `zspDomain_ZSP35`):
`Z_k = B_ĝ(z_k, .35R_k) ∪ {v_k(E) ≥ .9R_k, u_k(E) ≤ .4 v_k(E)}`. -/
def actualZeroDomain_BIFc (C : BoundaryGaf02Chain D Kj Ξ Sg eg c cw bcut bder κ)
    (k : S.ZeroIdx_BAUGC) : Set W.Carrier :=
  (letI := inducedMetricSpace S.completion.metric
   Subtype.val '' ball k.1 (35 / 100 * S.zeroRadius_BAUGC k)) ∪
  {p | 9 / 10 * S.zeroRadius_BAUGC k ≤ C.zeroMarker_BIFc k p ∧
    C.zeroCoord_BIFc k p ≤ 2 / 5 * C.zeroMarker_BIFc k p}

/-- **ZSP02's actual zero face** (ZF) of `C.E` (closed twin `zspFace_ZSP35`):
`{v_k(E) ≥ .9R_k, u_k(E) = .4 v_k(E)}`. -/
def actualZeroFace_BIFc (C : BoundaryGaf02Chain D Kj Ξ Sg eg c cw bcut bder κ)
    (k : S.ZeroIdx_BAUGC) : Set W.Carrier :=
  {p | 9 / 10 * S.zeroRadius_BAUGC k ≤ C.zeroMarker_BIFc k p ∧
    C.zeroCoord_BIFc k p = 2 / 5 * C.zeroMarker_BIFc k p}

end BoundaryGaf02Chain

/-- **The actual zero domains of `C.E`, analytic half** (review 69 §1.6, D69-4): a GLOBAL smooth
defining function per zero index, regular on its zero set, with `Z_k = {defFn ≤ 0}`,
`face = {defFn = 0}`, `∂Z_k = face`, equal to the retained ratio `u_k/v_k − 2/5` ONLY near the face
(where `.99R_k < v_k`), and the transport of the original model sublevel onto `Z_k` by an ambient
diffeomorphism of `W`. -/
structure BoundaryZeroDefining_BIFc (C : BoundaryGaf02Chain D Kj Ξ Sg eg c cw bcut bder κ) :
    Type where
  /-- The global defining functions (`h₁ − .4` of ZSP02). -/
  defFn : S.ZeroIdx_BAUGC → W.Carrier → ℝ
  defFn_smooth : ∀ k, ContMDiff W.model 𝓘(ℝ, ℝ) ∞ (defFn k)
  defFn_regular : ∀ k p, defFn k p = 0 → mfderiv W.model 𝓘(ℝ, ℝ) (defFn k) p ≠ 0
  /-- `Z_k = {defFn k ≤ 0}` (the GLOBAL sublevel). -/
  domain_eq : ∀ k, C.actualZeroDomain_BIFc k = {p | defFn k p ≤ 0}
  /-- `face = {defFn k = 0}`. -/
  face_eq : ∀ k, C.actualZeroFace_BIFc k = {p | defFn k p = 0}
  /-- `∂Z_k = face` (ZSP02 (ZF)). -/
  frontier_eq : ∀ k, frontier (C.actualZeroDomain_BIFc k) = C.actualZeroFace_BIFc k
  /-- Near the face the marker is positive and `defFn k = u_k/v_k − 2/5`. -/
  ratio_near : ∀ k, ∃ O : Set W.Carrier, IsOpen O ∧ C.actualZeroFace_BIFc k ⊆ O ∧
    ∀ p ∈ O, 99 / 100 * S.zeroRadius_BAUGC k < C.zeroMarker_BIFc k p ∧
      defFn k p = C.zeroCoord_BIFc k p / C.zeroMarker_BIFc k p - 2 / 5
  /-- (ZH) the original model sublevel `{radial_k ≤ 2/5}` and level `{radial_k = 2/5}` go onto
  `Z_k` and its face under ONE ambient diffeomorphism of `W`. -/
  transport : ∀ k, ∃ Ψ : W.Carrier ≃ₘ⟮W.model, W.model⟯ W.Carrier,
    Ψ '' (Subtype.val '' {q | S.zeroRadial_BIFc k q ≤ 2 / 5}) = C.actualZeroDomain_BIFc k ∧
      Ψ '' (Subtype.val '' {q | S.zeroRadial_BIFc k q = 2 / 5}) = C.actualZeroFace_BIFc k

/-- **The actual zero domains of `C.E`** (review 69 §1.6, D69-4; statement shape frozen here,
PRODUCER = lane B-BCG-ROWS): the analytic half `BoundaryZeroDefining_BIFc`, the placement of the
domains (inside the original zero balls, the `.38`-balls in their interiors, compact, pairwise
disjoint), the STANDARD smooth face parametrization (`S²` or `T²`) and the saturation of
`M₁ = W \ int(Z ∪ C_∂)` by the circle / slim fibres of the v2 bases `Bs`. -/
structure BoundaryActualZeroDomains_BIFc (C : BoundaryGaf02Chain D Kj Ξ Sg eg c cw bcut bder κ)
    (Bs : BoundaryGaf02BasesV2 C) : Type extends BoundaryZeroDefining_BIFc C where
  /-- `Z_k` lies in the original selected zero ball (Riemannian ball of `g`). -/
  domain_subset_ball : ∀ k, C.actualZeroDomain_BIFc k ⊆
    riemannianBallOf g k.1.val (S.zeroRadius_BAUGC k)
  /-- ZSP02 (ZB) at `a = 2/5`: the `ĝ`-ball `B(z_k, .38R_k)` lies in the interior of `Z_k`. -/
  zero_cover : ∀ k (q : W.pieceInterior ⊤),
    (letI := inducedMetricSpace S.completion.metric; dist q k.1) < 38 / 100 * S.zeroRadius_BAUGC k →
      q.val ∈ interior (C.actualZeroDomain_BIFc k)
  isCompact_domain : ∀ k, IsCompact (C.actualZeroDomain_BIFc k)
  pairwise_disjoint : Pairwise (Disjoint on C.actualZeroDomain_BIFc)
  /-- The STANDARD smooth face type: `S²` or `T²` (review 70 D70-5). -/
  face_param : ∀ k,
    (∃ e : GC.GraphManifold.ClosureSphere.{0} → W.Carrier, IsSmoothEmbedding (𝓡 2) W.model ∞ e ∧
        range e = C.actualZeroFace_BIFc k) ∨
      ∃ e : Circle × Circle → W.Carrier, IsSmoothEmbedding ((𝓡 1).prod (𝓡 1)) W.model ∞ e ∧
        range e = C.actualZeroFace_BIFc k
  /-- (F4d) `M₁ ∩ X_st` is a union of whole `f_st`-fibres (`st ≠ 1`). -/
  face_saturated : ∀ st : Fin 3, st ≠ 1 → ∀ p ∈ Bs.source st, ∀ q ∈ Bs.source st,
    C.stageMap st q = C.stageMap st p →
    p ∉ interior ((⋃ k, C.actualZeroDomain_BIFc k) ∪ C.cuspCores_BIF) →
    q ∉ interior ((⋃ k, C.actualZeroDomain_BIFc k) ∪ C.cuspCores_BIF)

namespace BoundaryActualZeroDomains_BIFc

variable {C : BoundaryGaf02Chain D Kj Ξ Sg eg c cw bcut bder κ} {Bs : BoundaryGaf02BasesV2 C}
  (Z : BoundaryActualZeroDomains_BIFc C Bs)

include Z in
/-- **Derived face type** (topological): the frontier of `Z_k` is `≃ₜ S²` or `≃ₜ T²`. -/
theorem nonempty_frontier_homeomorph_BIFc (k : S.ZeroIdx_BAUGC) :
    Nonempty (frontier (C.actualZeroDomain_BIFc k) ≃ₜ Metric.sphere (0 : E3) 1) ∨
      Nonempty (frontier (C.actualZeroDomain_BIFc k) ≃ₜ Circle × Circle) := by
  rw [Z.frontier_eq k]
  rcases Z.face_param k with ⟨e, he, hr⟩ | ⟨e, he, hr⟩
  · exact Or.inl ⟨((he.isEmbedding.toHomeomorph).trans (Homeomorph.setCongr hr)).symm.trans
      Homeomorph.ulift⟩
  · exact Or.inr ⟨((he.isEmbedding.toHomeomorph).trans (Homeomorph.setCongr hr)).symm⟩

/-- **Weak projection to v1's cores** (`BoundaryInitialCoresSpec C`): the cores are the ACTUAL
zero domains of `C.E`, enumerated by `Fintype.equivFin` of the zero index. -/
def toInitialCoresSpec_BIFc : BoundaryInitialCoresSpec C where
  count := Fintype.card S.ZeroIdx_BAUGC
  core i := C.actualZeroDomain_BIFc ((Fintype.equivFin S.ZeroIdx_BAUGC).symm i)
  centre i := ((Fintype.equivFin S.ZeroIdx_BAUGC).symm i).1
  centre_mem i := (Set.Finite.mem_toFinset _).mp ((Fintype.equivFin S.ZeroIdx_BAUGC).symm i).2
  core_subset_ball i :=
    ⟨(Set.Finite.mem_toFinset _).mp ((Fintype.equivFin S.ZeroIdx_BAUGC).symm i).2,
      Z.domain_subset_ball _⟩
  zero_cover z hz := ⟨Fintype.equivFin S.ZeroIdx_BAUGC ⟨z, (Set.Finite.mem_toFinset _).mpr hz⟩,
    by rw [Equiv.symm_apply_apply], fun q hq => by
      rw [Equiv.symm_apply_apply]
      exact Z.zero_cover _ q hq⟩
  isCompact_core i := Z.isCompact_domain _
  pairwise_disjoint i j hij :=
    Z.pairwise_disjoint ((Fintype.equivFin S.ZeroIdx_BAUGC).symm.injective.ne hij)
  face_type i := Z.nonempty_frontier_homeomorph_BIFc _

/-- The projected cores have the same union as the actual zero domains. -/
theorem toInitialCoresSpec_union_BIFc :
    (⋃ i, Z.toInitialCoresSpec_BIFc.core i) = ⋃ k, C.actualZeroDomain_BIFc k :=
  (Fintype.equivFin S.ZeroIdx_BAUGC).symm.surjective.iUnion_comp C.actualZeroDomain_BIFc

/-- **Weak projection to the saturated cores** (`BoundaryInitialCoresSpecSat C Bs₁`, consumed by
BCF01-G3 / BCF03) on any v1 BASES object with the same circle and slim sources. -/
def toSat_BIFc (Bs₁ : BoundaryGaf02Bases C) (hs : ∀ st, st ≠ 1 → Bs₁.source st = Bs.source st) :
    BoundaryInitialCoresSpecSat C Bs₁ where
  toBoundaryInitialCoresSpec := Z.toInitialCoresSpec_BIFc
  face_saturated := fun st hst p hp q hq hpq hpM => by
    rw [Z.toInitialCoresSpec_union_BIFc] at hpM ⊢
    exact Z.face_saturated st hst p (hs st hst ▸ hp) q (hs st hst ▸ hq) hpq hpM

end BoundaryActualZeroDomains_BIFc

namespace BoundaryGaf02Chain

variable {D : BoundaryAugmentedData S S.emptySlots_BIF}
  (C : BoundaryGaf02Chain D Kj Ξ Sg eg c cw bcut bder κ)

/-- With no selected zero centre the zero index is empty. -/
theorem isEmpty_zeroIdx_BIFc (hz0 : letI := inducedMetricSpace S.completion.metric
    letI := S.completion.complete
    letI := S.family.instMetricN
    letI := S.family.instChartedN
    letI := S.family.instMetricC
    S.family.zero.centres = ∅) : IsEmpty S.ZeroIdx_BAUGC :=
  ⟨fun k => by
    exact Set.eq_empty_iff_forall_notMem.mp hz0 k.1 ((Set.Finite.mem_toFinset _).mp k.2)⟩

/-- **Inhabitant**: the actual zero domains on the empty-family chain with no zero centre (no zero
index; the saturation is vacuous on the empty v2 bases). -/
def emptyActualZeroDomains_BIFc (hc : ∀ st, S.stageCentres_BIF st = ∅)
    (hF : Continuous S.boundaryOriginalMap)
    (hz0 : letI := inducedMetricSpace S.completion.metric
      letI := S.completion.complete
      letI := S.family.instMetricN
      letI := S.family.instChartedN
      letI := S.family.instMetricC
      S.family.zero.centres = ∅) :
    BoundaryActualZeroDomains_BIFc C (C.emptyBasesV2_BIFc hc hF) :=
  haveI := isEmpty_zeroIdx_BIFc (S := S) hz0
  { defFn := fun _ _ => 0
    defFn_smooth := fun k => isEmptyElim k
    defFn_regular := fun k => isEmptyElim k
    domain_eq := fun k => isEmptyElim k
    face_eq := fun k => isEmptyElim k
    frontier_eq := fun k => isEmptyElim k
    ratio_near := fun k => isEmptyElim k
    transport := fun k => isEmptyElim k
    domain_subset_ball := fun k => isEmptyElim k
    zero_cover := fun k => isEmptyElim k
    isCompact_domain := fun k => isEmptyElim k
    pairwise_disjoint := fun k => isEmptyElim k
    face_param := fun k => isEmptyElim k
    face_saturated := fun _ _ p hp => (notMem_empty p hp).elim }

end BoundaryGaf02Chain

end DifferentialGeometry.Geometry.Collapse
