import DifferentialGeometry.Geometry.Collapse.LocalExport.BoundarySlimCutFacesBCF
import Mathlib.Topology.Maps.Proper.CompactlyGenerated

/-!
# BCF01 G1a input: the relative frontier of `D₃` lies in the image of the old faces (lane B-BCF134)

Text v3 G1a needs `∂_{B₃} D₃ ⊆ Kset` for `Kset ⊇ f₃(∂M₁ ∩ X₃)` (the shared kernel's regularity clause).
This file proves the inclusion `∂_{B₃} D₃ ⊆ f₃(∂M₁ ∩ X₃)` from properness and saturation only:

* `relFrontier_image_subset_BCF` (generic): `f` continuous on an open `U` onto `B` (a metric space),
  proper over `B`, `M` closed and `f`-saturated in `U`; then every relative frontier point of `f(M ∩ U)`
  in `B` is the image of a point of `∂M ∩ U` (`f|U : U → B` is a closed map, `IsProperMap`);
* `BoundaryActualZeroDomains_BIFc.relFrontier_slimBaseDomain_subset_BCF` (binding): for the actual zero
  domains, `D₃ \ int_{B₃} D₃ ⊆ f₃(∂M₁ ∩ X₃)`.

The other G1a inputs (finiteness of `f₃(∂M₁ ∩ X₃)` by F4c + F5 + F5z, regularity of `D₃`, compactness of
the slab image) remain open (lane F).
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

/-- **Relative frontier of a saturated image** (generic): for `f` continuous on an open `U`, proper over
`B = f(U)` (a metric space), and a closed `f`-saturated `M`, the relative frontier of `f(M ∩ U)` in `B`
lies in `f(∂M ∩ U)`. -/
theorem relFrontier_image_subset_BCF {X Y : Type*} [TopologicalSpace X] [MetricSpace Y] {f : X → Y}
    {U : Set X} {Bs : Set Y} (hcont : ContinuousOn f U) (himg : f '' U = Bs)
    (hproper : ∀ Kc ⊆ Bs, IsCompact Kc → IsCompact (U ∩ f ⁻¹' Kc)) {M : Set X} (hM : IsClosed M)
    (hsat : ∀ p ∈ U, ∀ q ∈ U, f q = f p → p ∈ M → q ∈ M) :
    f '' (M ∩ U) \ relInterior_BIF Bs (f '' (M ∩ U)) ⊆ f '' (frontier M ∩ U) := by
  have hmaps : ∀ p ∈ U, f p ∈ Bs := fun p hp => himg ▸ mem_image_of_mem f hp
  set g : U → Bs := fun p => ⟨f p, hmaps p.1 p.2⟩ with hg
  have hgc : Continuous g := (continuousOn_iff_continuous_domRestrict.mp hcont).subtype_mk _
  have hgp : IsProperMap g := by
    refine isProperMap_iff_isCompact_preimage.mpr ⟨hgc, fun K hK => ?_⟩
    have hK' : IsCompact (Subtype.val '' K) := hK.image continuous_subtype_val
    have hc := hproper _ (Subtype.coe_image_subset _ _) hK'
    rw [Topology.IsEmbedding.subtypeVal.isCompact_iff]
    convert hc using 1
    ext q
    constructor
    · rintro ⟨q', hq', rfl⟩
      exact ⟨q'.2, g q', hq', rfl⟩
    · rintro ⟨hqU, z, hzK, hz⟩
      refine ⟨⟨q, hqU⟩, ?_, rfl⟩
      have : g ⟨q, hqU⟩ = z := Subtype.ext hz.symm
      change g ⟨q, hqU⟩ ∈ K
      rw [this]
      exact hzK
  rintro y ⟨⟨p, ⟨hpM, hpU⟩, rfl⟩, hyI⟩
  by_contra hne
  set E : Set U := {q | q.1 ∉ interior M} with hE
  have hEc : IsClosed E := (isOpen_interior.preimage continuous_subtype_val).isClosed_compl
  have hgE : IsClosed (g '' E) := hgp.isClosedMap E hEc
  have hpE : g ⟨p, hpU⟩ ∉ g '' E := by
    rintro ⟨q, hqE, hq⟩
    have hfq : f q.1 = f p := congrArg Subtype.val hq
    have hqM : q.1 ∈ M := hsat p hpU q.1 q.2 hfq hpM
    have hqf : q.1 ∉ frontier M := fun hf => hne ⟨q.1, ⟨hf, q.2⟩, hfq⟩
    exact hqE (by
      rw [hM.frontier_eq] at hqf
      by_contra hqI
      exact hqf ⟨hqM, hqI⟩)
  obtain ⟨G, hG, hGE⟩ := isOpen_induced_iff.mp hgE.isOpen_compl
  apply hyI
  refine mem_relInterior_iff_BCF.mpr ⟨hmaps p hpU, G, hG, ?_, ?_⟩
  · have : g ⟨p, hpU⟩ ∈ Subtype.val ⁻¹' G := hGE ▸ hpE
    exact this
  · rintro z ⟨hzG, hzB⟩
    obtain ⟨q, hqU, rfl⟩ : z ∈ f '' U := himg ▸ hzB
    have hgq : g ⟨q, hqU⟩ ∉ g '' E := by
      have : g ⟨q, hqU⟩ ∈ Subtype.val ⁻¹' G := hzG
      rw [hGE] at this
      exact this
    have hqI : q ∈ interior M := by
      by_contra h
      exact hgq ⟨⟨q, hqU⟩, h, rfl⟩
    exact ⟨q, ⟨interior_subset hqI, hqU⟩, rfl⟩

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

/-- **The relative frontier of `D₃` lies in the image of the old faces**: for the actual zero domains,
`D₃ \ int_{B₃} D₃ ⊆ f₃(∂M₁ ∩ X₃)`. -/
theorem BoundaryActualZeroDomains_BIFc.relFrontier_slimBaseDomain_subset_BCF
    {Bs : BoundaryGaf02BasesV2 C} (Z : BoundaryActualZeroDomains_BIFc C Bs) :
    Bs.slimBaseDomain_BIFc \ relInterior_BIF (Bs.base 2) Bs.slimBaseDomain_BIFc ⊆
      C.stageMap 2 '' (frontier C.M₁_BIFc ∩ Bs.source 2) :=
  relFrontier_image_subset_BCF (Bs.continuousOn_stageMap_BCF 2) (Bs.image_eq 2) (Bs.proper 2)
    C.isClosed_M₁_BCF fun p hp q hq hpq hpM => Z.face_saturated 2 (by decide) p hp q hq hpq hpM

/-- **Consumer**: on every v2 decomposition. -/
theorem BoundaryActualDecompositionV2.relFrontier_slimBaseDomain_dec_BCF
    (dec : BoundaryActualDecompositionV2 C) :
    dec.bases.slimBaseDomain_BIFc \ relInterior_BIF (dec.bases.base 2) dec.bases.slimBaseDomain_BIFc ⊆
      C.stageMap 2 '' (frontier C.M₁_BIFc ∩ dec.bases.source 2) :=
  dec.zero.relFrontier_slimBaseDomain_subset_BCF

end DifferentialGeometry.Geometry.Collapse
