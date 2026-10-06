import DifferentialGeometry.Geometry.Collapse.LocalExport.BoundaryCuspBaseEquationOBD
import DifferentialGeometry.Geometry.Collapse.LocalExport.BoundaryBcg07RowBGR
import DifferentialGeometry.Geometry.Collapse.LocalExport.BoundaryV2bConsumersBGR
import DifferentialGeometry.Geometry.Collapse.LocalExport.BoundaryFrontierM1BGR

/-!
# BCG07 07.g3, second half: the slim base domain near a cusp frontier point (lane O-BD2b)

Lane O-BD1 (by O-BD2b, suffix `_OBD`), group G3c. Blueprint BCG07 g3: `D₃ = f₃(M₁ ∩ X₃)` has
smooth boundary "whose cusp equation is `u_b/v_b − 40 = 0`". With the base cusp function
`φ_b = J_b¹ − 40 J_b²` of G3b (`φ_b ∘ f₃ = u_b − 40 v_b`, base differential `≠ 0`):

* `exists_open_fibre_subset_of_proper_OBD` (generic tube lemma): for a proper restriction
  `f|U : U → B` and an open `N` containing the whole fibre over `y₀ ∈ B`, some open `O ∋ y₀` has
  all its `U`-fibres inside `N` (from `isClosed_relImage_of_proper_BGR`);
* `relImage_iff_of_local_sublevel_OBD` (generic): the local sublevel description of `M`;
* **`BoundaryGaf02ChainE.slimBaseDomain_cuspEquation_OBD`** (A4 data `Bs`, `WF` v2b; the zero
  domains `Z`; E4b premises): if the cusp front `H_b` meets `X₃`, then `H_b` is the whole slim
  fibre over ONE point `y₀ ∈ B₃` with `φ_b y₀ = 0`, and on an open `O ∋ y₀`,
  `D₃ ∩ O = {y ∈ B₃ ∩ O | 0 ≤ φ_b y}` — `D₃` is cut out near `y₀` by the cusp equation, whose
  base differential is nonzero (G3b `cuspBase_differential_ne_zero_OBD`).
-/

set_option autoImplicit false

noncomputable section

open Set Function Metric Bundle Manifold Filter Topology
open scoped ContDiff Manifold Topology ENNReal
open DifferentialGeometry.Topology.Ehresmann DifferentialGeometry.Topology.Manifold
open DifferentialGeometry.Geometry.Riemannian GC.MetricGeometry
open DifferentialGeometry GC.Endpoint DifferentialGeometry.Geometry.Hyperbolic
open DifferentialGeometry.Analysis DifferentialGeometry.Topology GC.GraphManifold
  GC.GraphManifold.Assembly GC.GraphManifold.Assembly.FC39P0

namespace DifferentialGeometry.Geometry.Collapse

local notation "E3" => EuclideanSpace ℝ (Fin 3)

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace

attribute [local instance] nezero_finrank_euclideanThree_LC87

attribute [local instance] interiorCharted_BDRY1 interiorManifold_BDRY1
  connectedSpace_interior_BDRY2

section Generic

variable {X Y : Type*} [TopologicalSpace X]

/-- **Tube lemma for a proper restriction**: if `f|U : U → B` is proper (compact preimages of
compact subsets of `B = f(U)`) and the whole fibre over `y₀ ∈ B` lies in the open `N`, then some
open `O ∋ y₀` has every `U`-fibre over `O` inside `N`. -/
theorem exists_open_fibre_subset_of_proper_OBD [MetricSpace Y] {f : X → Y} {U : Set X}
    {Bs : Set Y} (hcont : ContinuousOn f U) (himg : f '' U = Bs)
    (hproper : ∀ Kc ⊆ Bs, IsCompact Kc → IsCompact (U ∩ f ⁻¹' Kc)) {N : Set X} (hN : IsOpen N)
    {y₀ : Y} (hy₀ : y₀ ∈ Bs) (hfib : U ∩ f ⁻¹' {y₀} ⊆ N) :
    ∃ O : Set Y, IsOpen O ∧ y₀ ∈ O ∧ ∀ q ∈ U, f q ∈ O → q ∈ N := by
  have hcl := isClosed_relImage_of_proper_BGR hcont himg hproper hN.isClosed_compl
  obtain ⟨t, ht, hteq⟩ := isClosed_induced_iff.mp hcl
  have hmaps : ∀ q ∈ U, f q ∈ Bs := fun q hq => himg ▸ mem_image_of_mem f hq
  refine ⟨tᶜ, ht.isOpen_compl, fun hy => ?_, fun q hq hqO => ?_⟩
  · have hmem : (⟨y₀, hy₀⟩ : Bs) ∈ Subtype.val ⁻¹' t := hy
    rw [hteq] at hmem
    obtain ⟨q, ⟨hqN, hqU⟩, hqy⟩ := hmem
    exact hqN (hfib ⟨hqU, hqy⟩)
  · by_contra hqN
    have hmem : (⟨f q, hmaps q hq⟩ : Bs) ∈ Subtype.val ⁻¹' (f '' (Nᶜ ∩ U)) :=
      ⟨q, ⟨hqN, hq⟩, rfl⟩
    rw [← hteq] at hmem
    exact hqO hmem

/-- **The local sublevel description of a relative image**: if near the fibres over `O` the set
`M = (int(A ∪ C))ᶜ` is described by `C ∩ N = {F ≤ 0}`, the level `{F = 0}` lies in `M`, the
fibres over `O` lie in `N \ A`, and `F = φ ∘ f`, then over `O` the relative image `f(M ∩ U)` is
`{0 ≤ φ}`. -/
theorem relImage_iff_of_local_sublevel_OBD {f : X → Y} {U : Set X} {Bs : Set Y}
    (himg : f '' U = Bs) {A Cs M N : Set X} (hM : M = (interior (A ∪ Cs))ᶜ) (hN : IsOpen N)
    {F : X → ℝ} {φ : Y → ℝ} (hF : ContinuousOn F N) (hpb : ∀ q, φ (f q) = F q)
    (hcore : Cs ∩ N = {x | x ∈ N ∧ F x ≤ 0}) (hlev : {x | x ∈ N ∧ F x = 0} ⊆ M) {O : Set Y}
    (hO : ∀ q ∈ U, f q ∈ O → q ∈ N ∧ q ∉ A) {y : Y} (hy : y ∈ Bs ∩ O) :
    y ∈ f '' (M ∩ U) ↔ 0 ≤ φ y := by
  obtain ⟨hyB, hyO⟩ := hy
  constructor
  · rintro ⟨q, ⟨hqM, hqU⟩, rfl⟩
    rw [hpb]
    by_contra hneg
    push Not at hneg
    have hqN := (hO q hqU hyO).1
    have hopen : IsOpen {x | x ∈ N ∧ F x < 0} := hF.isOpen_inter_preimage hN isOpen_Iio
    have hsub : {x | x ∈ N ∧ F x < 0} ⊆ A ∪ Cs := fun x hx => Or.inr (by
      have h : x ∈ Cs ∩ N := by rw [hcore]; exact ⟨hx.1, hx.2.le⟩
      exact h.1)
    rw [hM] at hqM
    exact hqM (interior_maximal hsub hopen ⟨hqN, hneg⟩)
  · intro hφ
    rw [← himg] at hyB
    obtain ⟨q, hqU, rfl⟩ := hyB
    obtain ⟨hqN, hqA⟩ := hO q hqU hyO
    rw [hpb] at hφ
    refine ⟨q, ⟨?_, hqU⟩, rfl⟩
    rcases hφ.lt_or_eq with hpos | hzero
    · rw [hM]
      intro hint
      rcases interior_subset hint with hA | hC
      · exact hqA hA
      · have h : q ∈ Cs ∩ N := ⟨hC, hqN⟩
        rw [hcore] at h
        exact absurd h.2 (not_le.mpr hpos)
    · exact hlev ⟨hqN, hzero.symm⟩

end Generic

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

/-- The removed set split at the cusp `i`: `⋃ Z_k ∪ C_∂ = (⋃ Z_k ∪ ⋃_{j ≠ i} C_j) ∪ C_i`. -/
theorem removed_split_OBD (i : Fin S.packet.cusp.count) :
    (⋃ k, C.toChain.actualZeroDomain_BIFc k) ∪ C.toChain.cuspCores_BIF =
      ((⋃ k, C.toChain.actualZeroDomain_BIFc k) ∪ ⋃ (j) (_ : j ≠ i), C.toChain.cuspCore_BIF j) ∪
        C.toChain.cuspCore_BIF i := by
  ext x
  simp only [BoundaryGaf02Chain.cuspCores_BIF, mem_union, mem_iUnion]
  constructor
  · rintro (h | ⟨j, hj⟩)
    · exact Or.inl (Or.inl h)
    · by_cases hji : j = i
      · exact Or.inr (hji ▸ hj)
      · exact Or.inl (Or.inr ⟨j, hji, hj⟩)
  · rintro ((h | ⟨j, -, hj⟩) | h)
    · exact Or.inl h
    · exact Or.inr ⟨j, hj⟩
    · exact Or.inr ⟨i, h⟩

/-- The cusp front avoids the other removed sets: the zero domains and the other cores (E4b). -/
theorem cuspFront_subset_sep_OBD {rd : ℝ} (hrd : 0 < rd) (hrd4 : rd < 1 / 10000)
    (hrdc : 20 * (c 2 + 1) * rd < 1 / 1000000)
    (hprem : 1000 * δn ^ 2 < w / (2 * (1 + 2 * Λ⁻¹) ^ 3) * min (1 / 2) (rd / 4) ^ 2)
    (hθ : θ < 1 / 100) (i : Fin S.packet.cusp.count) {near : Set W.Carrier} {F : W.Carrier → ℝ}
    (hfront : C.toChain.cuspFront_BIF i = {x | x ∈ near ∧ F x = 0})
    (hcore : C.toChain.cuspCore_BIF i ∩ near = {x | x ∈ near ∧ F x ≤ 0}) :
    C.toChain.cuspFront_BIF i ⊆ near ∩ ((⋃ k, C.toChain.actualZeroDomain_BIFc k) ∪
      ⋃ (j) (_ : j ≠ i), C.toChain.cuspCore_BIF j)ᶜ := by
  intro x hx
  have hx' : x ∈ near ∧ F x = 0 := by rw [hfront] at hx; exact hx
  have hxC : x ∈ C.toChain.cuspCore_BIF i := by
    have h : x ∈ C.toChain.cuspCore_BIF i ∩ near := by rw [hcore]; exact ⟨hx'.1, hx'.2.le⟩
    exact h.1
  have hspec := C.bcg06_coreSpec_on_chain_BGR hrd hrd4 hrdc hprem hθ
  refine ⟨hx'.1, ?_⟩
  rintro (hZ | hCj)
  · obtain ⟨k, hk⟩ := mem_iUnion.mp hZ
    exact disjoint_left.mp (C.cuspCore_disjoint_actualZeroDomain_BGR hrd hrd4 hrdc hprem hθ i k)
      hxC hk
  · obtain ⟨j, hj⟩ := mem_iUnion.mp hCj
    obtain ⟨hji, hxj⟩ := mem_iUnion.mp hj
    exact disjoint_left.mp (hspec.pairwise_disjoint i j (Ne.symm hji)) hxC hxj

/-- The removed set without the core `i` is closed. -/
theorem isClosed_removed_sep_OBD {Bs : BoundaryGaf02BasesV2 C.toChain}
    (Z : BoundaryActualZeroDomains_BIFc C.toChain Bs) {rd : ℝ} (hrd : 0 < rd)
    (hrd4 : rd < 1 / 10000) (hrdc : 20 * (c 2 + 1) * rd < 1 / 1000000)
    (hprem : 1000 * δn ^ 2 < w / (2 * (1 + 2 * Λ⁻¹) ^ 3) * min (1 / 2) (rd / 4) ^ 2)
    (hθ : θ < 1 / 100) (i : Fin S.packet.cusp.count) :
    IsClosed ((⋃ k, C.toChain.actualZeroDomain_BIFc k) ∪
      ⋃ (j) (_ : j ≠ i), C.toChain.cuspCore_BIF j) := by
  have hspec := C.bcg06_coreSpec_on_chain_BGR hrd hrd4 hrdc hprem hθ
  exact (isClosed_iUnion_of_finite fun k => (Z.isCompact_domain k).isClosed).union
    (isClosed_iUnion_of_finite fun j => isClosed_iUnion_of_finite fun _ =>
      (hspec.compact_core j).isClosed)

/-- The cusp front lies in `M₁` (it lies in `∂M₁`, and `M₁` is closed). -/
theorem cuspFront_subset_M₁_OBD {Bs : BoundaryGaf02BasesV2 C.toChain}
    (Z : BoundaryActualZeroDomains_BIFc C.toChain Bs) {rd : ℝ} (hrd : 0 < rd)
    (hrd4 : rd < 1 / 10000) (hrdc : 20 * (c 2 + 1) * rd < 1 / 1000000)
    (hprem : 1000 * δn ^ 2 < w / (2 * (1 + 2 * Λ⁻¹) ^ 3) * min (1 / 2) (rd / 4) ^ 2)
    (hθ : θ < 1 / 100) (i : Fin S.packet.cusp.count) :
    C.toChain.cuspFront_BIF i ⊆ C.toChain.M₁_BIFc := by
  intro x hx
  have hfr : x ∈ frontier C.toChain.M₁_BIFc := by
    rw [C.frontier_M₁_BGR Z hrd hrd4 hrdc hprem hθ]
    exact Or.inr (mem_iUnion.mpr ⟨i, hx⟩)
  have hcl : IsClosed C.toChain.M₁_BIFc := isOpen_interior.isClosed_compl
  exact hcl.frontier_subset hfr

/-- **BCG07 07.g3, the slim base domain near a cusp frontier point** (A4 data `Bs`, `WF` v2b; the
zero domains `Z`; E4b premises): if the cusp front `H_b` meets `X₃`, it is the whole slim fibre
over ONE `y₀ ∈ B₃` with `φ_b y₀ = 0`, and on an open `O ∋ y₀` the slim base domain is cut out by
the cusp equation: `D₃ ∩ O = {y ∈ B₃ ∩ O | 0 ≤ φ_b y}`. -/
theorem slimBaseDomain_cuspEquation_OBD {Bs : BoundaryGaf02BasesV2 C.toChain}
    (WF : BoundaryWholeFiberSpecV2b C.toChain Bs) (Z : BoundaryActualZeroDomains_BIFc C.toChain Bs)
    {rd : ℝ} (hrd : 0 < rd) (hrd4 : rd < 1 / 10000) (hrdc : 20 * (c 2 + 1) * rd < 1 / 1000000)
    (hprem : 1000 * δn ^ 2 < w / (2 * (1 + 2 * Λ⁻¹) ^ 3) * min (1 / 2) (rd / 4) ^ 2)
    (hθ : θ < 1 / 100) (i : Fin S.packet.cusp.count)
    (hX : (C.toChain.cuspFront_BIF i ∩ Bs.source 2).Nonempty) :
    ∃ y₀ ∈ Bs.base 2, C.toChain.cuspFront_BIF i = Bs.fibre 2 y₀ ∧ cuspBaseCLM_OBD i y₀ = 0 ∧
      ∃ O : Set (BoundaryAmbient_BIF S.IntTag_BAUGA (Fin S.packet.cusp.count)), IsOpen O ∧
        y₀ ∈ O ∧ ∀ y ∈ Bs.base 2 ∩ O, (y ∈ Bs.slimBaseDomain_BIFc ↔ 0 ≤ cuspBaseCLM_OBD i y) := by
  obtain ⟨y₀, hy₀, hH⟩ := C.cuspFront_eq_slimFibre_direct_V2b_BGR WF hrd hrd4 hrdc hprem hθ i hX
  obtain ⟨near, -, hsm, -, hfront, hcore⟩ := C.cuspFnLink_OBD hrd hrd4 hrdc hprem hθ i
  have hsep := C.cuspFront_subset_sep_OBD hrd hrd4 hrdc hprem hθ i hfront hcore
  have hAcl := C.isClosed_removed_sep_OBD Z hrd hrd4 hrdc hprem hθ i
  obtain ⟨O, hO, hy₀O, hOsub⟩ := exists_open_fibre_subset_of_proper_OBD
    (C.contMDiff_stageMap_OBD 2).continuous.continuousOn (Bs.image_eq 2) (Bs.proper 2)
    (near.isOpen.inter hAcl.isOpen_compl) hy₀ (fun q hq => hsep (hH ▸ hq))
  have hzero : cuspBaseCLM_OBD i y₀ = 0 := by
    obtain ⟨p, hp, -⟩ := hX
    have hpf : p ∈ Bs.fibre 2 y₀ := hH ▸ hp
    have hpy : C.toChain.stageMap 2 p = y₀ := hpf.2
    rw [← hpy]
    exact C.cuspBase_front_zero_OBD 2 i hp
  have hM : C.toChain.M₁_BIFc = (interior (((⋃ k, C.toChain.actualZeroDomain_BIFc k) ∪
      ⋃ (j) (_ : j ≠ i), C.toChain.cuspCore_BIF j) ∪ C.toChain.cuspCore_BIF i))ᶜ := by
    unfold BoundaryGaf02Chain.M₁_BIFc
    rw [C.removed_split_OBD i]
  have hlev : {x | x ∈ near ∧ chainBoundaryU_BCG6K C.toChain.E i x -
      40 * chainBoundaryV_BCG6K C.toChain.E i x = 0} ⊆ C.toChain.M₁_BIFc := by
    rw [← hfront]
    exact C.cuspFront_subset_M₁_OBD Z hrd hrd4 hrdc hprem hθ i
  refine ⟨y₀, hy₀, hH, hzero, O, hO, hy₀O, fun y hy => ?_⟩
  exact relImage_iff_of_local_sublevel_OBD (Bs.image_eq 2) hM near.isOpen hsm.continuousOn
    (cuspBaseCLM_stageMap_OBD C.toChain 2 i) hcore hlev
    (fun q hq hqO => ⟨(hOsub q hq hqO).1, (hOsub q hq hqO).2⟩) hy

end BoundaryGaf02ChainE

end DifferentialGeometry.Geometry.Collapse
