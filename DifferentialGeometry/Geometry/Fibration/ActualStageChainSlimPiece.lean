import DifferentialGeometry.Geometry.Fibration.ActualStageChainSlimZeroFaces
import DifferentialGeometry.Topology.Manifold.OneManifold.CompactOneManifoldChoiceBCF

/-!
# ZSP04 (closed binding of the shared `K₃` kernel) and ZSP05 (RC)/(RF)

Lane C14-ZSP35d. Blueprint `master207B.tex`, ZSP04 (B:6531–6595) and ZSP05 (B:6597–6640); review 74
D74-9 (the shared kernel `GraphAtlas1_BCF.exists_compact_oneManifold_choice_BCF` of lane B-BCF134,
circle components KEPT on the closed route). Inputs on the chain with (JA): the closed atlas of
`Bs = W₃ ∩ R₃` (G10), `C₃`, `F₃` and their regularity / finiteness (G11).

* `Gaf02ChainE.slimPiece_ZSP35 K = f⁻¹(K ∩ C₃)` (`M^slim = f₃⁻¹(D₃)`, `D₃ = K₃ ∩ C₃`).
* `Gaf02ChainEJA.slimPiece_spec_ZSP35` (for every compact `K ⊆ Bs` with `F₃ ⊆ relint K` and
  `K ∩ C₃` regular): `M^slim = M₁ ∩ f⁻¹(K)`, compact, `cl(int M^slim) = M^slim`, `f(M^slim) = D₃`,
  the relative collar along `∂M₁`, `M^slim ∩ ∂Z` = union of ENTIRE zero faces, and ZSP05's
  `M₂ = M₁ ∖ int_{M₁} M^slim` with (RC)/(RF) (`relative_interior_removal`).
* `Gaf02ChainEJA.zsp04_row_ZSP35` (final family): there is a compact smooth one-dimensional
  `K₃ ⊆ Bs` (finitely many smooth regular arcs AND loops) with (SK) (slab image and `F₃` in
  `relint K₃`, `∂K₃ ∩ F₃ = ∅`), `D₃` compact and regular, `M^slim` compact, regular, saturated,
  containing every slab point of `M₁`, with the collar and whole-face clauses; empty slim family
  ⟹ empty piece.
* `Gaf02ChainEJA.zsp05_row_ZSP35` (final family): ZSP05 (RC)/(RF) for that piece: `M₂` compact,
  `M = Z ∪ M^slim ∪ M₂`, `∂M₂ = (∂M₁ ∖ M^slim) ⊔ (∂M^slim ∖ ∂M₁)`,
  `M^slim ∩ M₂ = ∂M^slim ∖ ∂M₁`, disjoint interiors.

Consumer: `zsp0405_C14Z_ZSP35`.
-/

set_option autoImplicit false

noncomputable section

open Set Function Metric Bundle Manifold Filter
open scoped ContDiff Manifold Topology
open DifferentialGeometry.Geometry.Riemannian GC.MetricGeometry
open DifferentialGeometry.Analysis

namespace DifferentialGeometry.Geometry.Collapse

local notation "E3" => EuclideanSpace ℝ (Fin 3)
local notation "ℝ²" => EuclideanSpace ℝ (Fin 2)

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace

attribute [local instance] nezero_finrank_euclideanThree_LC87

attribute [local instance] LocalChartPackets.instMetricN LocalChartPackets.instChartedN
  LocalChartPackets.instMetricC

variable {X : Type} [mX : MetricSpace X] [ChartedSpace E3 X] [IsManifold 𝓘(ℝ, E3) ∞ X]
  [CompactSpace X] {g : SmoothRiemannianMetric 𝓘(ℝ, E3) X}
  {hmetric : ∀ a b : X, riemannianEDistOf g a b = ENNReal.ofReal (dist a b)}
  {ρ : X → ℝ} {hρ : ∀ p, 0 < ρ p} {Λ : ℝ} {β : ℕ → ℝ} {Δ σs : ℝ} {K : ℕ}
  {σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs ζ Λz : ℝ}
  {Kj : ℕ} {Ξ Γ S eg c cw : Fin 3 → ℝ}

/-- ZSP04's slim piece over a base set `K`: `M^slim = f⁻¹(K ∩ C₃)`. -/
def Gaf02ChainE.slimPiece_ZSP35
    {P : LocalChartPacketsC14 X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T
      V vs ζ Λz} (C : Gaf02ChainE P Kj Ξ Γ S eg c cw)
    (Kb : Set (BlockSpace (fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²))) : Set X :=
  C.slimMap_ZSP35 ⁻¹' (Kb ∩ C.slimC3_ZSP35)

namespace Gaf02ChainEJA

variable {oM : ManifoldOrientation 𝓘(ℝ, E3) X 3} {cadj : ℝ}
  {P : LocalChartPacketsC14Z X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e
    T V vs ζ Λz oM}

/-- **The slim piece over a compact base domain and ZSP05's remainder** (B:6553–6595, 6597–6640):
for a compact `Kb ⊆ Bs` containing the face set `F₃` in its relative interior and meeting `C₃` in a
regular set, `M^slim = f⁻¹(Kb ∩ C₃)` equals `M₁ ∩ f⁻¹(Kb)`, is compact and regular closed, maps onto
`Kb ∩ C₃`, contains its relative collar along `∂M₁`, meets `∂Z` in a union of ENTIRE zero faces,
and `M₂ = M₁ ∖ int_{M₁} M^slim` satisfies (RC)/(RF). -/
theorem slimPiece_spec_ZSP35
    (C : Gaf02ChainEJA P.toLocalChartPacketsC14D.toLocalChartPacketsC14 Kj Ξ Γ S eg c cw cadj)
    (hεr : εr < 1 / 2) {Kb : Set (BlockSpace (fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²))}
    (hKc : IsCompact Kb) (hKB : Kb ⊆ C.slimBs_ZSP35)
    (hFK : C.slimFacePoints_ZSP35 ⊆
      Subtype.val '' interior (Subtype.val ⁻¹' Kb : Set C.slimBs_ZSP35))
    (hDreg : Kb ∩ C.slimC3_ZSP35 ⊆ closure (Subtype.val '' interior
      (Subtype.val ⁻¹' (Kb ∩ C.slimC3_ZSP35) : Set C.slimBs_ZSP35))) :
    C.slimPiece_ZSP35 Kb = (interior C.zeroUnion_ZSP35)ᶜ ∩ C.slimMap_ZSP35 ⁻¹' Kb ∧
    IsCompact (C.slimPiece_ZSP35 Kb) ∧
    closure (interior (C.slimPiece_ZSP35 Kb)) = C.slimPiece_ZSP35 Kb ∧
    C.slimMap_ZSP35 '' C.slimPiece_ZSP35 Kb = Kb ∩ C.slimC3_ZSP35 ∧
    C.slimPiece_ZSP35 Kb ∩ frontier (interior C.zeroUnion_ZSP35)ᶜ ⊆
      Subtype.val '' interior (Subtype.val ⁻¹' C.slimPiece_ZSP35 Kb :
        Set ↥(interior C.zeroUnion_ZSP35)ᶜ) ∧
    C.slimPiece_ZSP35 Kb ∩ frontier C.zeroUnion_ZSP35 =
      ⋃ k ∈ {k : P.zero.finite_centres.toFinset |
          (frontier (zspDomain_ZSP35 P.toLocalChartFamily P.zero k C.E) ∩
            C.slimPiece_ZSP35 Kb).Nonempty},
        frontier (zspDomain_ZSP35 P.toLocalChartFamily P.zero k C.E) ∧
    (let M₁ : Set X := (interior C.zeroUnion_ZSP35)ᶜ
     let M₂ : Set X := M₁ \ Subtype.val '' interior (Subtype.val ⁻¹' C.slimPiece_ZSP35 Kb : Set M₁)
     IsCompact M₂ ∧ C.zeroUnion_ZSP35 ∪ C.slimPiece_ZSP35 Kb ∪ M₂ = univ ∧
      frontier M₂ = (frontier M₁ \ C.slimPiece_ZSP35 Kb) ∪
        (frontier (C.slimPiece_ZSP35 Kb) \ frontier M₁) ∧
      Disjoint (frontier M₁ \ C.slimPiece_ZSP35 Kb)
        (frontier (C.slimPiece_ZSP35 Kb) \ frontier M₁) ∧
      C.slimPiece_ZSP35 Kb ∩ M₂ = frontier (C.slimPiece_ZSP35 Kb) \ frontier M₁ ∧
      Disjoint (interior C.zeroUnion_ZSP35) (interior (C.slimPiece_ZSP35 Kb)) ∧
      Disjoint (interior (C.slimPiece_ZSP35 Kb)) (interior M₂) ∧
      Disjoint (interior C.zeroUnion_ZSP35) (interior M₂)) := by
  obtain ⟨hsatEq, hC3B, -, -, -⟩ := C.zsp03_slim_saturated_ZSP35 hεr
  have hfc := C.continuous_slimMap_ZSP35
  have hUo := C.isOpen_slimSource_ZSP35
  have hclk : ∀ k : P.zero.finite_centres.toFinset,
      IsClosed (zspDomain_ZSP35 P.toLocalChartFamily P.zero k C.E) := fun k =>
    (C.toGaf02ChainE.zsp02_domain_ZSP35 hεr k).1.isClosed
  obtain ⟨-, hfrU⟩ := frontier_disjoint_iUnion_ZSP35
    (fun k : P.zero.finite_centres.toFinset => zspDomain_ZSP35 P.toLocalChartFamily P.zero k C.E)
    hclk (fun k k' hkk => C.toGaf02ChainE.zsp02_disjoint_ZSP35 hεr hkk)
  -- `M^slim = M₁ ∩ f⁻¹(Kb)`
  have hSeq : C.slimPiece_ZSP35 Kb = (interior C.zeroUnion_ZSP35)ᶜ ∩ C.slimMap_ZSP35 ⁻¹' Kb := by
    ext y
    constructor
    · rintro ⟨hyK, hyC⟩
      have hy : y ∈ C.slimMap_ZSP35 ⁻¹' C.slimBs_ZSP35 ∩ C.slimMap_ZSP35 ⁻¹' C.slimC3_ZSP35 :=
        ⟨hC3B hyC, hyC⟩
      rw [← hsatEq] at hy
      exact ⟨hy.1, hyK⟩
    · rintro ⟨hyM, hyK⟩
      have hy : y ∈ (interior C.zeroUnion_ZSP35)ᶜ ∩ C.slimMap_ZSP35 ⁻¹' C.slimBs_ZSP35 :=
        ⟨hyM, hKB hyK⟩
      rw [hsatEq] at hy
      exact ⟨hyK, hy.2⟩
  have hSM : C.slimPiece_ZSP35 Kb ⊆ (interior C.zeroUnion_ZSP35)ᶜ := by
    rw [hSeq]
    exact inter_subset_left
  -- compactness: a closed subset of the compact carrier
  have hScl : IsClosed (C.slimPiece_ZSP35 Kb) := by
    rw [hSeq]
    exact isOpen_interior.isClosed_compl.inter (hKc.isClosed.preimage hfc)
  have hSc : IsCompact (C.slimPiece_ZSP35 Kb) := hScl.isCompact
  -- regularity: `f|U` open and `Kb ∩ C₃` regular in `Bs`
  have hSreg : C.slimPiece_ZSP35 Kb ⊆ closure (interior (C.slimPiece_ZSP35 Kb)) := by
    intro x hx
    rw [_root_.mem_closure_iff]
    intro N hN hxN
    have hxU : C.slimMap_ZSP35 x ∈ C.slimBs_ZSP35 := hC3B hx.2
    obtain ⟨O, hO, hOB⟩ := C.slim_relOpen_ZSP35 (W := N ∩ C.slimMap_ZSP35 ⁻¹' C.slimBs_ZSP35)
      inter_subset_right (hN.inter hUo)
    have hxO : C.slimMap_ZSP35 x ∈ O ∩ C.slimBs_ZSP35 := by
      rw [hOB]
      exact ⟨x, ⟨hxN, hxU⟩, rfl⟩
    obtain ⟨w', hw'O, hw'I⟩ := _root_.mem_closure_iff.mp (hDreg hx) O hO hxO.1
    obtain ⟨hw'B, O', hO', hw'O', hO'D⟩ :=
      DifferentialGeometry.Topology.mem_image_interior_preimage_val_iff.mp hw'I
    have hw' : w' ∈ O ∩ C.slimBs_ZSP35 := ⟨hw'O, hw'B⟩
    rw [hOB] at hw'
    obtain ⟨y, ⟨hyN, hyU⟩, rfl⟩ := hw'
    refine ⟨y, hyN, ?_⟩
    rw [mem_interior]
    exact ⟨C.slimMap_ZSP35 ⁻¹' C.slimBs_ZSP35 ∩ C.slimMap_ZSP35 ⁻¹' O',
      fun z hz => hO'D ⟨hz.2, hz.1⟩, hUo.inter (hO'.preimage hfc), hyU, hw'O'⟩
  have hreg : closure (interior (C.slimPiece_ZSP35 Kb)) = C.slimPiece_ZSP35 Kb :=
    Subset.antisymm (closure_minimal interior_subset hScl) hSreg
  -- a frontier point of `M₁` is a zero-face point
  have hfrM : frontier (interior C.zeroUnion_ZSP35)ᶜ ⊆ frontier C.zeroUnion_ZSP35 := by
    rw [frontier_compl]
    exact frontier_interior_subset
  -- the relative collar along `∂M₁`
  have hcollar : C.slimPiece_ZSP35 Kb ∩ frontier (interior C.zeroUnion_ZSP35)ᶜ ⊆
      Subtype.val '' interior (Subtype.val ⁻¹' C.slimPiece_ZSP35 Kb :
        Set ↥(interior C.zeroUnion_ZSP35)ᶜ) := by
    rintro x ⟨hxS, hxF⟩
    have hxZ := hfrM hxF
    rw [Gaf02ChainE.zeroUnion_ZSP35, hfrU] at hxZ
    obtain ⟨k, hk⟩ := mem_iUnion.mp hxZ
    have hxU : C.slimMap_ZSP35 x ∈ C.slimBs_ZSP35 := hC3B hxS.2
    have hxF3 : C.slimMap_ZSP35 x ∈ C.slimFacePoints_ZSP35 :=
      mem_iUnion.mpr ⟨k, x, ⟨hk, hxU⟩, rfl⟩
    obtain ⟨-, O, hO, hxO, hOK⟩ :=
      DifferentialGeometry.Topology.mem_image_interior_preimage_val_iff.mp (hFK hxF3)
    refine DifferentialGeometry.Topology.mem_image_interior_preimage_val_iff.mpr
      ⟨hSM hxS, C.slimMap_ZSP35 ⁻¹' C.slimBs_ZSP35 ∩ C.slimMap_ZSP35 ⁻¹' O,
        hUo.inter (hO.preimage hfc), ⟨hxU, hxO⟩, fun y hy => ?_⟩
    rw [hSeq]
    exact ⟨hy.2, hOK ⟨hy.1.2, hy.1.1⟩⟩
  -- the image
  have himg : C.slimMap_ZSP35 '' C.slimPiece_ZSP35 Kb = Kb ∩ C.slimC3_ZSP35 := by
    refine Subset.antisymm (image_preimage_subset _ _) ?_
    rintro w ⟨hwK, hwC⟩
    obtain ⟨p, -, hpw⟩ := id hwC
    refine ⟨p, ?_, hpw⟩
    change C.slimMap_ZSP35 p ∈ Kb ∩ C.slimC3_ZSP35
    rw [hpw]
    exact ⟨hwK, hwC⟩
  -- whole zero faces
  have hfaces : C.slimPiece_ZSP35 Kb ∩ frontier C.zeroUnion_ZSP35 =
      ⋃ k ∈ {k : P.zero.finite_centres.toFinset |
          (frontier (zspDomain_ZSP35 P.toLocalChartFamily P.zero k C.E) ∩
            C.slimPiece_ZSP35 Kb).Nonempty},
        frontier (zspDomain_ZSP35 P.toLocalChartFamily P.zero k C.E) := by
    ext x
    constructor
    · rintro ⟨hxS, hxZ⟩
      rw [Gaf02ChainE.zeroUnion_ZSP35, hfrU] at hxZ
      obtain ⟨k, hk⟩ := mem_iUnion.mp hxZ
      exact mem_iUnion₂.mpr ⟨k, ⟨x, hk, hxS⟩, hk⟩
    · intro hx
      obtain ⟨k, ⟨p, hpF, hpS⟩, hxk⟩ := mem_iUnion₂.mp hx
      have hpU : C.slimMap_ZSP35 p ∈ C.slimBs_ZSP35 := hC3B hpS.2
      have hfib := C.zsp03_slim_face_fibre_ZSP35 hεr k hpF hpU
      have hxp : C.slimMap_ZSP35 x = C.slimMap_ZSP35 p := by
        have : x ∈ C.slimMap_ZSP35 ⁻¹' {C.slimMap_ZSP35 p} := by
          rw [hfib]
          exact hxk
        exact this
      refine ⟨?_, ?_⟩
      · change C.slimMap_ZSP35 x ∈ Kb ∩ C.slimC3_ZSP35
        rw [hxp]
        exact hpS
      · rw [Gaf02ChainE.zeroUnion_ZSP35, hfrU]
        exact mem_iUnion.mpr ⟨k, hxk⟩
  obtain ⟨-, hcov, hfr2, hdisj, hshared, hd1, hd2, hd3⟩ :=
    DifferentialGeometry.Topology.relative_interior_removal C.zeroUnion_ZSP35
      (C.slimPiece_ZSP35 Kb) hSM hreg hcollar
  exact ⟨hSeq, hSc, hreg, himg, hcollar, hfaces,
    DifferentialGeometry.Topology.isCompact_relative_interior_removal _ _, hcov, hfr2, hdisj,
    hshared, hd1, hd2, hd3⟩

/-- **ZSP04, closed binding of the shared `K₃` kernel** (B:6531–6595, D74-9): on the final family,
there is a compact smooth one-dimensional domain `K₃ ⊆ Bs` — finitely many smooth regular arcs AND
loops (`SmoothCompactOneDomain_BCF`) — with (SK) `f(⋃ slabs) ∪ F₃ ⊆ int_{Bs} K₃` and
`∂_{Bs}K₃ ∩ F₃ = ∅` (`∂C₃ ⊆ F₃`); `D₃ = K₃ ∩ C₃` is compact and regular in `Bs`; `M^slim = f⁻¹(D₃)
= M₁ ∩ f⁻¹(K₃)` is compact, regular closed, saturated with image `D₃`, contains every slab point
of `M₁`, contains its relative collar along `∂M₁`, meets `∂Z` in a union of ENTIRE zero faces; an
empty slim family gives the empty piece. -/
theorem zsp04_row_ZSP35
    (C : Gaf02ChainEJA P.toLocalChartPacketsC14D.toLocalChartPacketsC14 Kj Ξ Γ S eg c cw cadj)
    (hεr : εr < 1 / 2) :
    ∃ K₃ : DifferentialGeometry.Topology.SmoothCompactOneDomain_BCF C.slimBs_ZSP35,
      C.toChain.slimSlabImage_ZSP35 ∪ C.slimFacePoints_ZSP35 ⊆
        Subtype.val '' interior (Subtype.val ⁻¹' K₃.carrier : Set C.slimBs_ZSP35) ∧
      Disjoint (K₃.carrier \
          Subtype.val '' interior (Subtype.val ⁻¹' K₃.carrier : Set C.slimBs_ZSP35))
        C.slimFacePoints_ZSP35 ∧
      IsCompact (K₃.carrier ∩ C.slimC3_ZSP35) ∧
      K₃.carrier ∩ C.slimC3_ZSP35 ⊆ closure (Subtype.val '' interior
        (Subtype.val ⁻¹' (K₃.carrier ∩ C.slimC3_ZSP35) : Set C.slimBs_ZSP35)) ∧
      C.slimPiece_ZSP35 K₃.carrier =
        (interior C.zeroUnion_ZSP35)ᶜ ∩ C.slimMap_ZSP35 ⁻¹' K₃.carrier ∧
      IsCompact (C.slimPiece_ZSP35 K₃.carrier) ∧
      closure (interior (C.slimPiece_ZSP35 K₃.carrier)) = C.slimPiece_ZSP35 K₃.carrier ∧
      C.slimMap_ZSP35 '' C.slimPiece_ZSP35 K₃.carrier = K₃.carrier ∩ C.slimC3_ZSP35 ∧
      zsp04SlimSlabs_ZSP35 P.toLocalChartPackets ∩ (interior C.zeroUnion_ZSP35)ᶜ ⊆
        C.slimPiece_ZSP35 K₃.carrier ∧
      C.slimPiece_ZSP35 K₃.carrier ∩ frontier (interior C.zeroUnion_ZSP35)ᶜ ⊆
        Subtype.val '' interior (Subtype.val ⁻¹' C.slimPiece_ZSP35 K₃.carrier :
          Set ↥(interior C.zeroUnion_ZSP35)ᶜ) ∧
      C.slimPiece_ZSP35 K₃.carrier ∩ frontier C.zeroUnion_ZSP35 =
        ⋃ k ∈ {k : P.zero.finite_centres.toFinset |
            (frontier (zspDomain_ZSP35 P.toLocalChartFamily P.zero k C.E) ∩
              C.slimPiece_ZSP35 K₃.carrier).Nonempty},
          frontier (zspDomain_ZSP35 P.toLocalChartFamily P.zero k C.E) ∧
      (P.slim.centres = ∅ → C.slimPiece_ZSP35 K₃.carrier = ∅) := by
  obtain ⟨-, hC3B, -, -, hfront⟩ := C.zsp03_slim_saturated_ZSP35 hεr
  obtain ⟨-, hI, -⟩ := C.toChain.zsp04_slab_image_ZSP35
  have hFfin := (C.zsp03_slim_face_points_ZSP35 hεr).2
  have hFB : C.slimFacePoints_ZSP35 ⊆ C.slimBs_ZSP35 := by
    intro w hw
    obtain ⟨k, p, ⟨-, hpU⟩, rfl⟩ := mem_iUnion.mp hw
    exact hpU
  obtain ⟨K₃, hKs, hKF, hKreg⟩ := C.slimAtlas_ZSP35.exists_compact_oneManifold_choice_BCF
    (hI.union hFfin.isCompact)
    (union_subset C.slimSlabImage_subset_slimBs_ZSP35 hFB) hFfin
    (C.zsp03_slim_regular_ZSP35 hεr) (hfront.trans subset_union_right)
  have hKc := K₃.isCompact_carrier_BCF
  have hKB := K₃.subset_base
  obtain ⟨hSeq, hSc, hreg, himg, hcollar, hfaces, -⟩ := C.slimPiece_spec_ZSP35 hεr hKc hKB
    (subset_union_right.trans hKs) hKreg
  have hDc : IsCompact (K₃.carrier ∩ C.slimC3_ZSP35) := by
    rw [← himg]
    exact hSc.image C.continuous_slimMap_ZSP35
  refine ⟨K₃, hKs, hKF, hDc, hKreg, hSeq, hSc, hreg, himg, ?_, hcollar, hfaces, fun h0 => ?_⟩
  · rintro p ⟨hp, hpM⟩
    rw [hSeq]
    refine ⟨hpM, ?_⟩
    have hw : C.slimMap_ZSP35 p ∈ C.toChain.slimSlabImage_ZSP35 := ⟨p, hp, rfl⟩
    obtain ⟨hwB, O, -, hwO, hOK⟩ :=
      DifferentialGeometry.Topology.mem_image_interior_preimage_val_iff.mp (hKs (Or.inl hw))
    exact hOK ⟨hwO, hwB⟩
  · refine eq_empty_iff_forall_notMem.mpr fun p hp => ?_
    obtain ⟨i, -⟩ := mem_iUnion.mp (hC3B hp.2).2
    have hi := (Set.Finite.mem_toFinset _).mp i.2
    exact (Set.eq_empty_iff_forall_notMem.mp h0) _ hi

/-- **ZSP05 (RC)/(RF) on the final family** (B:6597–6640): for the `K₃` of ZSP04 (the shared
kernel's output on the closed atlas, with (SK)), the relative removal
`M₂ = M₁ ∖ int_{M₁} M^slim` is compact, `M = Z ∪ M^slim ∪ M₂`,
`∂M₂ = (∂M₁ ∖ M^slim) ⊔ (∂M^slim ∖ ∂M₁)`, `M^slim ∩ M₂ = ∂M^slim ∖ ∂M₁`, and the three pieces have
disjoint interiors. -/
theorem zsp05_row_ZSP35
    (C : Gaf02ChainEJA P.toLocalChartPacketsC14D.toLocalChartPacketsC14 Kj Ξ Γ S eg c cw cadj)
    (hεr : εr < 1 / 2) :
    ∃ K₃ : DifferentialGeometry.Topology.SmoothCompactOneDomain_BCF C.slimBs_ZSP35,
      C.toChain.slimSlabImage_ZSP35 ∪ C.slimFacePoints_ZSP35 ⊆
        Subtype.val '' interior (Subtype.val ⁻¹' K₃.carrier : Set C.slimBs_ZSP35) ∧
      Disjoint (K₃.carrier \
          Subtype.val '' interior (Subtype.val ⁻¹' K₃.carrier : Set C.slimBs_ZSP35))
        C.slimFacePoints_ZSP35 ∧
      IsCompact (C.slimPiece_ZSP35 K₃.carrier) ∧
      closure (interior (C.slimPiece_ZSP35 K₃.carrier)) = C.slimPiece_ZSP35 K₃.carrier ∧
      (let M₁ : Set X := (interior C.zeroUnion_ZSP35)ᶜ
       let M₂ : Set X := M₁ \ Subtype.val '' interior
         (Subtype.val ⁻¹' C.slimPiece_ZSP35 K₃.carrier : Set M₁)
       IsCompact M₂ ∧ C.zeroUnion_ZSP35 ∪ C.slimPiece_ZSP35 K₃.carrier ∪ M₂ = univ ∧
        frontier M₂ = (frontier M₁ \ C.slimPiece_ZSP35 K₃.carrier) ∪
          (frontier (C.slimPiece_ZSP35 K₃.carrier) \ frontier M₁) ∧
        Disjoint (frontier M₁ \ C.slimPiece_ZSP35 K₃.carrier)
          (frontier (C.slimPiece_ZSP35 K₃.carrier) \ frontier M₁) ∧
        C.slimPiece_ZSP35 K₃.carrier ∩ M₂ =
          frontier (C.slimPiece_ZSP35 K₃.carrier) \ frontier M₁ ∧
        Disjoint (interior C.zeroUnion_ZSP35) (interior (C.slimPiece_ZSP35 K₃.carrier)) ∧
        Disjoint (interior (C.slimPiece_ZSP35 K₃.carrier)) (interior M₂) ∧
        Disjoint (interior C.zeroUnion_ZSP35) (interior M₂)) := by
  obtain ⟨K₃, hKs, hKF, -, hKreg, -, hSc, hreg, -⟩ := C.zsp04_row_ZSP35 hεr
  obtain ⟨-, -, -, -, -, -, h05⟩ := C.slimPiece_spec_ZSP35 hεr K₃.isCompact_carrier_BCF
    K₃.subset_base (subset_union_right.trans hKs) hKreg
  exact ⟨K₃, hKs, hKF, hSc, hreg, h05⟩

end Gaf02ChainEJA

/-- **Consumer: the closed decomposition `M = Z ∪ M^slim ∪ M₂`** for a chain with (JA) on the final
family: a compact smooth one-dimensional `K₃` (arcs and loops) covering the slab image and the face
points, a compact regular slim piece, a compact remainder `M₂`, and the three pieces cover `M`. -/
theorem zsp0405_C14Z_ZSP35 {oM : ManifoldOrientation 𝓘(ℝ, E3) X 3} {cadj : ℝ}
    {P : LocalChartPacketsC14Z X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e
      T V vs ζ Λz oM}
    (C : Gaf02ChainEJA P.toLocalChartPacketsC14D.toLocalChartPacketsC14 Kj Ξ Γ S eg c cw cadj)
    (hεr : εr < 1 / 2) :
    ∃ K₃ : DifferentialGeometry.Topology.SmoothCompactOneDomain_BCF C.slimBs_ZSP35,
      C.toChain.slimSlabImage_ZSP35 ⊆
        Subtype.val '' interior (Subtype.val ⁻¹' K₃.carrier : Set C.slimBs_ZSP35) ∧
      IsCompact (C.slimPiece_ZSP35 K₃.carrier) ∧
      IsCompact ((interior C.zeroUnion_ZSP35)ᶜ \ Subtype.val '' interior
        (Subtype.val ⁻¹' C.slimPiece_ZSP35 K₃.carrier : Set ↥(interior C.zeroUnion_ZSP35)ᶜ)) ∧
      C.zeroUnion_ZSP35 ∪ C.slimPiece_ZSP35 K₃.carrier ∪
        ((interior C.zeroUnion_ZSP35)ᶜ \ Subtype.val '' interior
          (Subtype.val ⁻¹' C.slimPiece_ZSP35 K₃.carrier : Set ↥(interior C.zeroUnion_ZSP35)ᶜ)) =
        univ := by
  obtain ⟨K₃, hKs, -, hSc, -, hM₂, hcov, -⟩ := C.zsp05_row_ZSP35 hεr
  exact ⟨K₃, subset_union_left.trans hKs, hSc, hM₂, hcov⟩

end DifferentialGeometry.Geometry.Collapse
