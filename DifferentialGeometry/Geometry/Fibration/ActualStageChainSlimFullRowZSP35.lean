import DifferentialGeometry.Geometry.Fibration.ActualStageChainSlimClosedComponent
import DifferentialGeometry.Geometry.Fibration.ActualStageChainSlimLoopCircleZSP35

/-!
# ZSP04, the full row on one `K₃`: base domain, piece, bundle over arcs and loops, end faces

Lane S-ZSP04, group G19. Blueprint `master207B.tex`, ZSP04 (B:6531–6595). One `K₃, D₃ = K₃ ∩ C₃`
(`zsp04_D3_ZSP35`, G15) carries ALL clauses of the row at once:

* (SK) and the point-set clauses of `zsp0405_row_ZSP35` (G16): `D₃ = K₃ ∩ C₃`, `∂D₃ = (∂K₃ ∩
  int C₃) ⊔ (int K₃ ∩ ∂C₃)`, `M^slim = f₃⁻¹(D₃) = M₁ ∩ f₃⁻¹(K₃)` compact, regular closed, onto `D₃`,
  containing every slab point of `M₁`, with the collar along `∂M₁`, `M^slim ∩ ∂Z = f⁻¹(K₃ ∩ ∂C₃)`
  a union of ENTIRE zero faces, `∂M^slim = f⁻¹(∂D₃)`, and the empty family giving the empty piece;
* the smooth bundle: over every ARC of `D₃` a whole interval product `S² × I` / `T² × I` (S0, EFE
  G1, `slim_arc_product_EFE`); over every LOOP of `D₃` the circle-valued submersion of
  `slim_loop_circle_ZSP35` (S1, G18) on the open compact `O_j ⊆ int M^slim`;
* the end classification: every arc end is a ZERO-FACE end (`int K₃ ∩ ∂C₃`: its whole fibre lies in
  `M^slim ∩ ∂Z`) or a FREE end (`∂K₃ ∩ int C₃`: its whole fibre lies in `∂M^slim` and misses `∂Z`).

`Gaf02ChainEJA.zsp04_full_row_ZSP35` (final family, `K ≥ 5`, `εr < 1/2`). Consumer:
`zsp04_full_row_C14Z_ZSP35`; dihedral instance (slim family EMPTY: an empty-truth test) in
`ActualStageChainSlimFullRowInstanceZSP35`.
-/

set_option autoImplicit false

noncomputable section

open Set Function Metric Bundle Manifold Filter
open scoped ContDiff Manifold Topology
open DifferentialGeometry.Geometry.Riemannian GC.MetricGeometry
open DifferentialGeometry.Analysis
open GC.GraphManifold GC.Endpoint
open DifferentialGeometry.Topology DifferentialGeometry.Topology.Ehresmann

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

namespace Gaf02ChainEJA

section Final

variable {oM : ManifoldOrientation 𝓘(ℝ, E3) X 3} {cadj : ℝ}
  {P : LocalChartPacketsC14Z X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e
    T V vs ζ Λz oM}

/-- **The arc ends of `D₃`** (ZSP04's end classification): every end `y` of an arc of `D₃` is a
ZERO-FACE end (`y ∈ int K₃ ∩ ∂C₃`, whole fibre inside `M^slim ∩ ∂Z`) or a FREE end
(`y ∈ ∂K₃ ∩ int C₃`, whole fibre inside `∂M^slim` and disjoint from `∂Z`). -/
theorem slim_arc_end_kinds_ZSP35
    (C : Gaf02ChainEJA P.toLocalChartPacketsC14D.toLocalChartPacketsC14 Kj Ξ Γ S eg c cw cadj)
    (K₃ D₃ : SmoothCompactOneDomain_BCF C.slimBs_ZSP35)
    (hKF : Disjoint (K₃.carrier \
        Subtype.val '' interior (Subtype.val ⁻¹' K₃.carrier : Set C.slimBs_ZSP35))
      C.slimFacePoints_ZSP35)
    (hSD : C.slimPiece_ZSP35 K₃.carrier = C.slimMap_ZSP35 ⁻¹' D₃.carrier)
    (hdD : D₃.carrier \ Subtype.val '' interior
        (Subtype.val ⁻¹' D₃.carrier : Set C.slimBs_ZSP35) =
      ((K₃.carrier \
            Subtype.val '' interior (Subtype.val ⁻¹' K₃.carrier : Set C.slimBs_ZSP35)) ∩
          Subtype.val '' interior (Subtype.val ⁻¹' C.slimC3_ZSP35 : Set C.slimBs_ZSP35)) ∪
        (Subtype.val '' interior (Subtype.val ⁻¹' K₃.carrier : Set C.slimBs_ZSP35) ∩
          C.slimFacePoints_ZSP35))
    (hfz : C.slimPiece_ZSP35 K₃.carrier ∩ frontier C.zeroUnion_ZSP35 =
      C.slimMap_ZSP35 ⁻¹' (K₃.carrier ∩ C.slimFacePoints_ZSP35))
    (hfp : frontier (C.slimPiece_ZSP35 K₃.carrier) = C.slimMap_ZSP35 ⁻¹' (D₃.carrier \
      Subtype.val '' interior (Subtype.val ⁻¹' D₃.carrier : Set C.slimBs_ZSP35)))
    (k : Fin D₃.m) {y : BlockSpace (fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²)}
    (hy : y ∈ ({D₃.arc k 0, D₃.arc k 1} :
      Set (BlockSpace (fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²)))) :
    (y ∈ C.slimFacePoints_ZSP35 ∧
        y ∈ Subtype.val '' interior (Subtype.val ⁻¹' K₃.carrier : Set C.slimBs_ZSP35) ∧
        C.slimMap_ZSP35 ⁻¹' {y} ⊆ C.slimPiece_ZSP35 K₃.carrier ∩ frontier C.zeroUnion_ZSP35) ∨
      (y ∈ K₃.carrier \
          Subtype.val '' interior (Subtype.val ⁻¹' K₃.carrier : Set C.slimBs_ZSP35) ∧
        y ∈ Subtype.val '' interior (Subtype.val ⁻¹' C.slimC3_ZSP35 : Set C.slimBs_ZSP35) ∧
        C.slimMap_ZSP35 ⁻¹' {y} ⊆ frontier (C.slimPiece_ZSP35 K₃.carrier) ∧
        Disjoint (C.slimMap_ZSP35 ⁻¹' {y}) (frontier C.zeroUnion_ZSP35)) := by
  have hyb : y ∈ D₃.carrier \ Subtype.val '' interior
      (Subtype.val ⁻¹' D₃.carrier : Set C.slimBs_ZSP35) := by
    rw [D₃.relFrontier_eq]
    exact mem_iUnion.mpr ⟨k, hy⟩
  have hyD : y ∈ D₃.carrier := hyb.1
  have hpiece : C.slimMap_ZSP35 ⁻¹' {y} ⊆ C.slimPiece_ZSP35 K₃.carrier := fun x hx => by
    rw [hSD]
    have hxy : C.slimMap_ZSP35 x = y := hx
    simp only [mem_preimage, hxy]
    exact hyD
  have hyb' := hyb
  rw [hdD] at hyb'
  rcases hyb' with hfree | hzero
  · refine Or.inr ⟨hfree.1, hfree.2, ?_, ?_⟩
    · intro x hx
      rw [hfp]
      have hxy : C.slimMap_ZSP35 x = y := hx
      simp only [mem_preimage, hxy]
      exact hyb
    · refine disjoint_left.mpr fun x hx hxz => ?_
      have hxm : x ∈ C.slimPiece_ZSP35 K₃.carrier ∩ frontier C.zeroUnion_ZSP35 :=
        ⟨hpiece hx, hxz⟩
      rw [hfz] at hxm
      have hxy : C.slimMap_ZSP35 x = y := hx
      have h2 : y ∈ K₃.carrier ∩ C.slimFacePoints_ZSP35 := hxy ▸ hxm
      exact disjoint_left.mp hKF hfree.1 h2.2
  · refine Or.inl ⟨hzero.2, hzero.1, ?_⟩
    intro x hx
    refine ⟨hpiece hx, ?_⟩
    have hxy : C.slimMap_ZSP35 x = y := hx
    have hyK : y ∈ K₃.carrier := by
      obtain ⟨hxB, O, -, hxO, hOK⟩ :=
        DifferentialGeometry.Topology.mem_image_interior_preimage_val_iff.mp hzero.1
      exact hOK ⟨hxO, hxB⟩
    have hxm : x ∈ C.slimMap_ZSP35 ⁻¹' (K₃.carrier ∩ C.slimFacePoints_ZSP35) :=
      ⟨hxy ▸ hyK, hxy ▸ hzero.2⟩
    rw [← hfz] at hxm
    exact hxm.2

/-- **The slim piece over one `K₃`** (the point-set part of ZSP04 for the `K₃, D₃` of
`zsp04_D3_ZSP35`): `M^slim = f⁻¹(D₃) = M₁ ∩ f⁻¹(K₃)` is compact, regular closed, onto `D₃`,
has the collar, meets `∂Z` in `f⁻¹(K₃ ∩ ∂C₃)` (a union of entire zero faces), and
`∂M^slim = f⁻¹(∂D₃)`. -/
theorem slim_piece_facts_ZSP35
    (C : Gaf02ChainEJA P.toLocalChartPacketsC14D.toLocalChartPacketsC14 Kj Ξ Γ S eg c cw cadj)
    (hεr : εr < 1 / 2) (K₃ D₃ : SmoothCompactOneDomain_BCF C.slimBs_ZSP35)
    (hD : D₃.carrier = K₃.carrier ∩ C.slimC3_ZSP35)
    (hKs : C.toChain.slimSlabImage_ZSP35 ∪ C.slimFacePoints_ZSP35 ⊆
      Subtype.val '' interior (Subtype.val ⁻¹' K₃.carrier : Set C.slimBs_ZSP35))
    (hKF : Disjoint (K₃.carrier \
        Subtype.val '' interior (Subtype.val ⁻¹' K₃.carrier : Set C.slimBs_ZSP35))
      C.slimFacePoints_ZSP35)
    (hDreg : D₃.carrier ⊆ closure (Subtype.val '' interior
        (Subtype.val ⁻¹' D₃.carrier : Set C.slimBs_ZSP35))) :
    C.slimPiece_ZSP35 K₃.carrier = C.slimMap_ZSP35 ⁻¹' D₃.carrier ∧
      C.slimPiece_ZSP35 K₃.carrier =
        (interior C.zeroUnion_ZSP35)ᶜ ∩ C.slimMap_ZSP35 ⁻¹' K₃.carrier ∧
      IsCompact (C.slimPiece_ZSP35 K₃.carrier) ∧
      closure (interior (C.slimPiece_ZSP35 K₃.carrier)) = C.slimPiece_ZSP35 K₃.carrier ∧
      C.slimMap_ZSP35 '' C.slimPiece_ZSP35 K₃.carrier = D₃.carrier ∧
      C.slimPiece_ZSP35 K₃.carrier ∩ frontier (interior C.zeroUnion_ZSP35)ᶜ ⊆
        Subtype.val '' interior (Subtype.val ⁻¹' C.slimPiece_ZSP35 K₃.carrier :
          Set ↥(interior C.zeroUnion_ZSP35)ᶜ) ∧
      C.slimPiece_ZSP35 K₃.carrier ∩ frontier C.zeroUnion_ZSP35 =
        C.slimMap_ZSP35 ⁻¹' (K₃.carrier ∩ C.slimFacePoints_ZSP35) ∧
      C.slimPiece_ZSP35 K₃.carrier ∩ frontier C.zeroUnion_ZSP35 =
        ⋃ k ∈ {k : P.zero.finite_centres.toFinset |
            (frontier (zspDomain_ZSP35 P.toLocalChartFamily P.zero k C.E) ∩
              C.slimPiece_ZSP35 K₃.carrier).Nonempty},
          frontier (zspDomain_ZSP35 P.toLocalChartFamily P.zero k C.E) ∧
      frontier (C.slimPiece_ZSP35 K₃.carrier) = C.slimMap_ZSP35 ⁻¹' (D₃.carrier \
        Subtype.val '' interior (Subtype.val ⁻¹' D₃.carrier : Set C.slimBs_ZSP35)) := by
  obtain ⟨-, hbd⟩ := C.zsp03_slim_boundary_eq_ZSP35 hεr
  have hreg' : K₃.carrier ∩ C.slimC3_ZSP35 ⊆ closure (Subtype.val '' interior
      (Subtype.val ⁻¹' (K₃.carrier ∩ C.slimC3_ZSP35) : Set C.slimBs_ZSP35)) := hD ▸ hDreg
  obtain ⟨hSeq, hSc, hreg, himg, hcollar, hfaces, -⟩ :=
    C.slimPiece_spec_ZSP35 hεr K₃.isCompact_carrier_BCF K₃.subset_base
      (subset_union_right.trans hKs) hreg'
  obtain ⟨-, -, h3, h4⟩ := C.zsp04_SF_ZSP35 hεr K₃.isCompact_carrier_BCF K₃.subset_base hKF
  rw [hbd] at h4
  have hSD : C.slimPiece_ZSP35 K₃.carrier = C.slimMap_ZSP35 ⁻¹' D₃.carrier := by
    rw [hD]
    rfl
  have hfp : frontier (C.slimPiece_ZSP35 K₃.carrier) = C.slimMap_ZSP35 ⁻¹' (D₃.carrier \
      Subtype.val '' interior (Subtype.val ⁻¹' D₃.carrier : Set C.slimBs_ZSP35)) := by
    rw [h3, hD]
  exact ⟨hSD, hSeq, hSc, hreg, hD ▸ himg, hcollar, h4, hfaces, hfp⟩

/-- Every slab point of `M₁` lies in the slim piece. -/
theorem slim_piece_slab_ZSP35
    (C : Gaf02ChainEJA P.toLocalChartPacketsC14D.toLocalChartPacketsC14 Kj Ξ Γ S eg c cw cadj)
    (K₃ : SmoothCompactOneDomain_BCF C.slimBs_ZSP35)
    (hKs : C.toChain.slimSlabImage_ZSP35 ∪ C.slimFacePoints_ZSP35 ⊆
      Subtype.val '' interior (Subtype.val ⁻¹' K₃.carrier : Set C.slimBs_ZSP35))
    (hSeq : C.slimPiece_ZSP35 K₃.carrier =
      (interior C.zeroUnion_ZSP35)ᶜ ∩ C.slimMap_ZSP35 ⁻¹' K₃.carrier) :
    zsp04SlimSlabs_ZSP35 P.toLocalChartPackets ∩ (interior C.zeroUnion_ZSP35)ᶜ ⊆
      C.slimPiece_ZSP35 K₃.carrier := by
  rintro p ⟨hp, hpM⟩
  rw [hSeq]
  refine ⟨hpM, ?_⟩
  have hw : C.slimMap_ZSP35 p ∈ C.toChain.slimSlabImage_ZSP35 := ⟨p, hp, rfl⟩
  obtain ⟨hwB, O, -, hwO, hOK⟩ :=
    DifferentialGeometry.Topology.mem_image_interior_preimage_val_iff.mp (hKs (Or.inl hw))
  exact hOK ⟨hwO, hwB⟩

/-- An empty slim family gives the empty slim piece. -/
theorem slim_piece_empty_ZSP35
    (C : Gaf02ChainEJA P.toLocalChartPacketsC14D.toLocalChartPacketsC14 Kj Ξ Γ S eg c cw cadj)
    (hεr : εr < 1 / 2) (Kb : Set (BlockSpace (fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²)))
    (h0 : P.slim.centres = ∅) : C.slimPiece_ZSP35 Kb = ∅ := by
  obtain ⟨-, hC3B, -, -, -⟩ := C.zsp03_slim_saturated_ZSP35 hεr
  refine eq_empty_iff_forall_notMem.mpr fun p hp => ?_
  obtain ⟨i, -⟩ := mem_iUnion.mp (hC3B hp.2).2
  have hi := (Set.Finite.mem_toFinset _).mp i.2
  exact (Set.eq_empty_iff_forall_notMem.mp h0) _ hi

/-- The whole preimage of a loop of `D₃` lies in the interior of the slim piece. -/
theorem slim_loop_preimage_interior_ZSP35
    (C : Gaf02ChainEJA P.toLocalChartPacketsC14D.toLocalChartPacketsC14 Kj Ξ Γ S eg c cw cadj)
    (hK : 5 ≤ K) (K₃ D₃ : SmoothCompactOneDomain_BCF C.slimBs_ZSP35)
    (hSD : C.slimPiece_ZSP35 K₃.carrier = C.slimMap_ZSP35 ⁻¹' D₃.carrier) (j : Fin D₃.l) :
    C.slimMap_ZSP35 ⁻¹' range (D₃.loop j) ⊆ interior (C.slimPiece_ZSP35 K₃.carrier) := by
  obtain ⟨hOo, -⟩ := C.slim_loop_circle_ZSP35 hK D₃ j
  refine interior_maximal (fun x hx => ?_) hOo
  rw [hSD]
  refine mem_preimage.mpr ?_
  rw [D₃.carrier_eq]
  exact Or.inr (mem_iUnion.mpr ⟨j, hx⟩)

/-- **ZSP04 on one `K₃`** (B:6531–6595; the full row): see the module docstring. -/
theorem zsp04_full_row_ZSP35
    (C : Gaf02ChainEJA P.toLocalChartPacketsC14D.toLocalChartPacketsC14 Kj Ξ Γ S eg c cw cadj)
    (hεr : εr < 1 / 2) (hK : 5 ≤ K) :
    ∃ K₃ D₃ : SmoothCompactOneDomain_BCF C.slimBs_ZSP35,
      D₃.carrier = K₃.carrier ∩ C.slimC3_ZSP35 ∧
      C.toChain.slimSlabImage_ZSP35 ∪ C.slimFacePoints_ZSP35 ⊆
        Subtype.val '' interior (Subtype.val ⁻¹' K₃.carrier : Set C.slimBs_ZSP35) ∧
      Disjoint (K₃.carrier \
          Subtype.val '' interior (Subtype.val ⁻¹' K₃.carrier : Set C.slimBs_ZSP35))
        C.slimFacePoints_ZSP35 ∧
      D₃.carrier \ Subtype.val '' interior (Subtype.val ⁻¹' D₃.carrier : Set C.slimBs_ZSP35) =
        ((K₃.carrier \
              Subtype.val '' interior (Subtype.val ⁻¹' K₃.carrier : Set C.slimBs_ZSP35)) ∩
            Subtype.val '' interior (Subtype.val ⁻¹' C.slimC3_ZSP35 : Set C.slimBs_ZSP35)) ∪
          (Subtype.val '' interior (Subtype.val ⁻¹' K₃.carrier : Set C.slimBs_ZSP35) ∩
            C.slimFacePoints_ZSP35) ∧
      C.slimPiece_ZSP35 K₃.carrier = C.slimMap_ZSP35 ⁻¹' D₃.carrier ∧
      C.slimPiece_ZSP35 K₃.carrier =
        (interior C.zeroUnion_ZSP35)ᶜ ∩ C.slimMap_ZSP35 ⁻¹' K₃.carrier ∧
      IsCompact (C.slimPiece_ZSP35 K₃.carrier) ∧
      closure (interior (C.slimPiece_ZSP35 K₃.carrier)) = C.slimPiece_ZSP35 K₃.carrier ∧
      C.slimMap_ZSP35 '' C.slimPiece_ZSP35 K₃.carrier = D₃.carrier ∧
      zsp04SlimSlabs_ZSP35 P.toLocalChartPackets ∩ (interior C.zeroUnion_ZSP35)ᶜ ⊆
        C.slimPiece_ZSP35 K₃.carrier ∧
      C.slimPiece_ZSP35 K₃.carrier ∩ frontier (interior C.zeroUnion_ZSP35)ᶜ ⊆
        Subtype.val '' interior (Subtype.val ⁻¹' C.slimPiece_ZSP35 K₃.carrier :
          Set ↥(interior C.zeroUnion_ZSP35)ᶜ) ∧
      C.slimPiece_ZSP35 K₃.carrier ∩ frontier C.zeroUnion_ZSP35 =
        C.slimMap_ZSP35 ⁻¹' (K₃.carrier ∩ C.slimFacePoints_ZSP35) ∧
      C.slimPiece_ZSP35 K₃.carrier ∩ frontier C.zeroUnion_ZSP35 =
        ⋃ k ∈ {k : P.zero.finite_centres.toFinset |
            (frontier (zspDomain_ZSP35 P.toLocalChartFamily P.zero k C.E) ∩
              C.slimPiece_ZSP35 K₃.carrier).Nonempty},
          frontier (zspDomain_ZSP35 P.toLocalChartFamily P.zero k C.E) ∧
      frontier (C.slimPiece_ZSP35 K₃.carrier) = C.slimMap_ZSP35 ⁻¹' (D₃.carrier \
        Subtype.val '' interior (Subtype.val ⁻¹' D₃.carrier : Set C.slimBs_ZSP35)) ∧
      (P.slim.centres = ∅ → C.slimPiece_ZSP35 K₃.carrier = ∅) ∧
      (∀ k : Fin D₃.m,
        (∃ F₀ : StandardWholeSurfaceFibre_EFE C.slimSubmersion_EFE (𝓡 2) ClosureSphere.{0}
            (D₃.arc k 0),
          Nonempty (WholeSurfaceIntervalProduct_EFE C.slimSubmersion_EFE (D₃.arc_EFE k) F₀)) ∨
        (∃ F₀ : StandardWholeSurfaceFibre_EFE C.slimSubmersion_EFE torusModel Torus
            (D₃.arc k 0),
          Nonempty (WholeSurfaceIntervalProduct_EFE C.slimSubmersion_EFE (D₃.arc_EFE k) F₀))) ∧
      (∀ k : Fin D₃.m, ∀ y ∈ ({D₃.arc k 0, D₃.arc k 1} :
          Set (BlockSpace (fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²))),
        (y ∈ C.slimFacePoints_ZSP35 ∧
            y ∈ Subtype.val '' interior (Subtype.val ⁻¹' K₃.carrier : Set C.slimBs_ZSP35) ∧
            C.slimMap_ZSP35 ⁻¹' {y} ⊆ C.slimPiece_ZSP35 K₃.carrier ∩ frontier C.zeroUnion_ZSP35) ∨
          (y ∈ K₃.carrier \
              Subtype.val '' interior (Subtype.val ⁻¹' K₃.carrier : Set C.slimBs_ZSP35) ∧
            y ∈ Subtype.val '' interior (Subtype.val ⁻¹' C.slimC3_ZSP35 : Set C.slimBs_ZSP35) ∧
            C.slimMap_ZSP35 ⁻¹' {y} ⊆ frontier (C.slimPiece_ZSP35 K₃.carrier) ∧
            Disjoint (C.slimMap_ZSP35 ⁻¹' {y}) (frontier C.zeroUnion_ZSP35))) ∧
      (∀ j : Fin D₃.l,
        C.slimMap_ZSP35 ⁻¹' range (D₃.loop j) ⊆ interior (C.slimPiece_ZSP35 K₃.carrier) ∧
        IsOpen (C.slimMap_ZSP35 ⁻¹' range (D₃.loop j)) ∧
        IsCompact (C.slimMap_ZSP35 ⁻¹' range (D₃.loop j)) ∧
        ∃ p : X → Circle,
          ContMDiffOn 𝓘(ℝ, E3) (𝓡 1) ∞ p (C.slimMap_ZSP35 ⁻¹' range (D₃.loop j)) ∧
          (∀ x ∈ C.slimMap_ZSP35 ⁻¹' range (D₃.loop j),
            Surjective (mfderiv 𝓘(ℝ, E3) (𝓡 1) p x)) ∧
          (∀ x ∈ C.slimMap_ZSP35 ⁻¹' range (D₃.loop j), ∀ t : ℝ,
            p x = Circle.exp (2 * Real.pi * t) ↔ C.slimMap_ZSP35 x = D₃.loop j t) ∧
          ((∃ F₀ : StandardWholeSurfaceFibre_EFE C.slimSubmersion_EFE (𝓡 2) ClosureSphere.{0}
              (D₃.loop j 0),
            range F₀.emb = {x | x ∈ C.slimMap_ZSP35 ⁻¹' range (D₃.loop j) ∧ p x = 1}) ∨
          (∃ F₀ : StandardWholeSurfaceFibre_EFE C.slimSubmersion_EFE torusModel Torus
              (D₃.loop j 0),
            range F₀.emb = {x | x ∈ C.slimMap_ZSP35 ⁻¹' range (D₃.loop j) ∧ p x = 1}))) := by
  obtain ⟨K₃, D₃, hD, hKs, hKF, hDreg, hdD⟩ := C.zsp04_D3_ZSP35 hεr
  obtain ⟨hSD, hSeq, hSc, hreg, himg, hcollar, h4, hfaces, hfp⟩ :=
    C.slim_piece_facts_ZSP35 hεr K₃ D₃ hD hKs hKF hDreg
  exact ⟨K₃, D₃, hD, hKs, hKF, hdD, hSD, hSeq, hSc, hreg, himg,
    C.slim_piece_slab_ZSP35 K₃ hKs hSeq, hcollar, h4, hfaces, hfp,
    C.slim_piece_empty_ZSP35 hεr K₃.carrier, fun k => C.slim_arc_product_EFE hK (D₃.arc_EFE k),
    fun k y hy => C.slim_arc_end_kinds_ZSP35 K₃ D₃ hKF hSD hdD h4 hfp k hy,
    fun j => ⟨C.slim_loop_preimage_interior_ZSP35 hK K₃ D₃ hSD j,
      C.slim_loop_circle_ZSP35 hK D₃ j⟩⟩

end Final

end Gaf02ChainEJA

section Consumer

/-- **Consumer: ZSP04's smooth slim bundle over `D₃` on the final family**, unpacked: a compact
`M^slim = f₃⁻¹(D₃)` onto `D₃`, whose preimage of every ARC is the range of a smooth injective
full-rank map `S² × I` / `T² × I → M` over the arc with every end fibre in `∂M^slim`, and whose
preimage of every LOOP is an open compact piece of `M^slim` with a circle-valued submersion. -/
theorem zsp04_full_row_C14Z_ZSP35 {oM : ManifoldOrientation 𝓘(ℝ, E3) X 3} {cadj : ℝ}
    {P : LocalChartPacketsC14Z X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e
      T V vs ζ Λz oM}
    (C : Gaf02ChainEJA P.toLocalChartPacketsC14D.toLocalChartPacketsC14 Kj Ξ Γ S eg c cw cadj)
    (hεr : εr < 1 / 2) (hK : 5 ≤ K) :
    ∃ K₃ D₃ : SmoothCompactOneDomain_BCF C.slimBs_ZSP35,
      D₃.carrier = K₃.carrier ∩ C.slimC3_ZSP35 ∧
      IsCompact (C.slimPiece_ZSP35 K₃.carrier) ∧
      C.slimMap_ZSP35 '' C.slimPiece_ZSP35 K₃.carrier = D₃.carrier ∧
      (∀ k : Fin D₃.m,
        (∃ m : ClosureSphere.{0} × Icc (0 : ℝ) 1 → X,
          ContMDiff ((𝓡 2).prod (𝓡∂ 1)) 𝓘(ℝ, E3) ∞ m ∧ Injective m ∧
          (∀ z, Injective (mfderiv ((𝓡 2).prod (𝓡∂ 1)) 𝓘(ℝ, E3) m z)) ∧
          (∀ z, C.slimMap_ZSP35 (m z) = D₃.arc k z.2) ∧
          range m = C.slimMap_ZSP35 ⁻¹' (D₃.arc k '' Icc 0 1)) ∨
        (∃ m : Torus × Icc (0 : ℝ) 1 → X,
          ContMDiff (torusModel.prod (𝓡∂ 1)) 𝓘(ℝ, E3) ∞ m ∧ Injective m ∧
          (∀ z, Injective (mfderiv (torusModel.prod (𝓡∂ 1)) 𝓘(ℝ, E3) m z)) ∧
          (∀ z, C.slimMap_ZSP35 (m z) = D₃.arc k z.2) ∧
          range m = C.slimMap_ZSP35 ⁻¹' (D₃.arc k '' Icc 0 1))) ∧
      (∀ k : Fin D₃.m, ∀ y ∈ ({D₃.arc k 0, D₃.arc k 1} :
          Set (BlockSpace (fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²))),
        C.slimMap_ZSP35 ⁻¹' {y} ⊆ frontier (C.slimPiece_ZSP35 K₃.carrier)) ∧
      (∀ j : Fin D₃.l, IsOpen (C.slimMap_ZSP35 ⁻¹' range (D₃.loop j)) ∧
        IsCompact (C.slimMap_ZSP35 ⁻¹' range (D₃.loop j)) ∧
        C.slimMap_ZSP35 ⁻¹' range (D₃.loop j) ⊆ interior (C.slimPiece_ZSP35 K₃.carrier) ∧
        ∃ p : X → Circle,
          ContMDiffOn 𝓘(ℝ, E3) (𝓡 1) ∞ p (C.slimMap_ZSP35 ⁻¹' range (D₃.loop j)) ∧
          ∀ x ∈ C.slimMap_ZSP35 ⁻¹' range (D₃.loop j),
            Surjective (mfderiv 𝓘(ℝ, E3) (𝓡 1) p x)) := by
  obtain ⟨K₃, D₃, hD, -, hKF, hdD, hSD, -, hSc, -, himg, -, -, h4, -, hfp, -, harc, hend, hloop⟩ :=
    C.zsp04_full_row_ZSP35 hεr hK
  refine ⟨K₃, D₃, hD, hSc, himg, fun k => ?_, fun k y hy => ?_, fun j => ?_⟩
  · rcases harc k with ⟨F₀, ⟨W⟩⟩ | ⟨F₀, ⟨W⟩⟩
    · exact Or.inl ⟨W.map, W.smooth, W.injective, W.fullRank, W.proj_eq, W.range_eq⟩
    · exact Or.inr ⟨W.map, W.smooth, W.injective, W.fullRank, W.proj_eq, W.range_eq⟩
  · rcases hend k y hy with ⟨-, -, hz⟩ | ⟨-, -, hfr, -⟩
    · have hyb : y ∈ D₃.carrier \ Subtype.val '' interior
          (Subtype.val ⁻¹' D₃.carrier : Set C.slimBs_ZSP35) := by
        rw [D₃.relFrontier_eq]
        exact mem_iUnion.mpr ⟨k, hy⟩
      intro x hx
      rw [hfp]
      have hxy : C.slimMap_ZSP35 x = y := hx
      simp only [mem_preimage, hxy]
      exact hyb
    · exact hfr
  · obtain ⟨hin, hOo, hOc, p, hp, hsub, -⟩ := hloop j
    exact ⟨hOo, hOc, hin, p, hp, hsub⟩

end Consumer

end DifferentialGeometry.Geometry.Collapse
