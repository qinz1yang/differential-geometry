import DifferentialGeometry.Geometry.Fibration.ActualStageChainGaf07Row
import DifferentialGeometry.Geometry.Fibration.ActualStageChainSlimBundleEFE
import DifferentialGeometry.Geometry.Fibration.ActualStageChainSlimPiece

/-!
# FC36 (proper slim bundles) as one row on the chain: GAF07 slim ∧ ZSP04 on ONE `K₃`

Lane S-FC-WRAP, group G1 (suffix `_FCW`). Blueprint `master207B.tex`, FC36
(`found:fibration-slim-bundles`, B:6238–6258): truncate `W₃` by the markers `x''_i > .9R_i`,
`|x'_i/x''_i| < 4·10⁵Δ`, take the FULL preimage `X₃` under `π₃E` (a proper onto submersion with
fibres `S²` or `T²`, containing the `3.5·10⁵Δ` regions and contained in `U₃`: GAF07, slim part),
remove the interiors of the zero domains and choose a compact one-dimensional base submanifold with
boundary `K₃` covering the required smaller regions; its saturated preimage is `M^slim` (ZSP04).

`Gaf02ChainEJA.fc36_row_FCW` (final family `LocalChartPacketsC14Z`, chain with (JA), `εr < 1/2`,
packet jet order `K ≥ 5`, the manifold orientation `oM` of the family) is the conjunction

1. `type_of% (C.gaf07_slim_row_GAFD hK oM)` — GAF07's slim row: the base `B₃` is relatively open in
   `W₃`, `{|η_i| ≤ 3.5·10⁵Δ} ⊂ X₃ ⊂ U₃`, `π₃E : X₃ → B₃` proper, onto, submersion in the base chart,
   every WHOLE fibre equal to the whole adjusted level, `≃ₜ` the original fibre, connected, a smooth
   standard `ClosureSphere` or `Torus`, whole trace in `{|η_i| < 4.01·10⁵Δ}`, stage fibre = final
   fibre;
2. ONE pair `K₃, D₃ : SmoothCompactOneDomain_BCF Bs` (finitely many smooth regular arcs and loops)
   with `D₃ = K₃ ∩ C₃`, (SK) `f(⋃ slabs) ∪ F₃ ⊆ int_{Bs} K₃`, `∂K₃ ∩ F₃ = ∅`, `D₃` regular,
   `∂D₃ = (∂K₃ ∩ int C₃) ⊔ (int K₃ ∩ F₃)`; the SAME `K₃` defines `M^slim = f₃⁻¹(K₃ ∩ C₃)
   = M₁ ∩ f₃⁻¹(K₃)`, which is compact, regular closed, maps onto `D₃`, contains every slab point of
   `M₁`, contains its relative collar along `∂M₁`, meets `∂Z` in a union of ENTIRE zero faces and is
   empty for an empty slim family (ZSP04's set clauses, `slimPiece_spec_ZSP35`);
3. over the same `K₃, D₃`: the whole preimage of every ARC of `D₃` and of every proper sub-arc of
   every LOOP of `D₃` is `S² × I` or `T² × I` (a whole interval product starting at a standard whole
   fibre, `zsp04_bundle_EFE`).

The only ZSP04 clause not covered is the GLOBAL mapping torus over a circle component of `D₃`
(ZSP04's last paragraph; lane S-ZSP04). FC36's own text asks for no bundle structure over `M^slim`.

Consumer: `fc36_slim_piece_fibres_FCW` (the piece is compact and every arc product is a smooth
injective full-rank map `F × [0, 1] → M` onto the arc's whole preimage).
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

variable {oM : ManifoldOrientation 𝓘(ℝ, E3) X 3} {cadj : ℝ}
  {P : LocalChartPacketsC14Z X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e
    T V vs ζ Λz oM}

/-- **FC36, the whole row on the final family**: GAF07's slim row, and over ONE compact smooth
one-dimensional domain `K₃` (with `D₃ = K₃ ∩ C₃`) ZSP04's (SK) / (SF) set clauses for
`M^slim = f₃⁻¹(K₃ ∩ C₃)` together with the interval products `S² × I` / `T² × I` over every arc of
`D₃` and over every proper sub-arc of every loop of `D₃`. -/
theorem fc36_row_FCW
    (C : Gaf02ChainEJA P.toLocalChartPacketsC14D.toLocalChartPacketsC14 Kj Ξ Γ S eg c cw cadj)
    (hεr : εr < 1 / 2) (hK : 5 ≤ K) :
    type_of% (C.gaf07_slim_row_GAFD hK oM) ∧
    ∃ K₃ D₃ : SmoothCompactOneDomain_BCF C.slimBs_ZSP35,
      D₃.carrier = K₃.carrier ∩ C.slimC3_ZSP35 ∧
      C.toChain.slimSlabImage_ZSP35 ∪ C.slimFacePoints_ZSP35 ⊆
        Subtype.val '' interior (Subtype.val ⁻¹' K₃.carrier : Set C.slimBs_ZSP35) ∧
      Disjoint (K₃.carrier \
          Subtype.val '' interior (Subtype.val ⁻¹' K₃.carrier : Set C.slimBs_ZSP35))
        C.slimFacePoints_ZSP35 ∧
      D₃.carrier ⊆ closure (Subtype.val '' interior
        (Subtype.val ⁻¹' D₃.carrier : Set C.slimBs_ZSP35)) ∧
      D₃.carrier \ Subtype.val '' interior (Subtype.val ⁻¹' D₃.carrier : Set C.slimBs_ZSP35) =
        ((K₃.carrier \
              Subtype.val '' interior (Subtype.val ⁻¹' K₃.carrier : Set C.slimBs_ZSP35)) ∩
            Subtype.val '' interior (Subtype.val ⁻¹' C.slimC3_ZSP35 : Set C.slimBs_ZSP35)) ∪
          (Subtype.val '' interior (Subtype.val ⁻¹' K₃.carrier : Set C.slimBs_ZSP35) ∩
            C.slimFacePoints_ZSP35) ∧
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
        ⋃ k ∈ {k : P.zero.finite_centres.toFinset |
            (frontier (zspDomain_ZSP35 P.toLocalChartFamily P.zero k C.E) ∩
              C.slimPiece_ZSP35 K₃.carrier).Nonempty},
          frontier (zspDomain_ZSP35 P.toLocalChartFamily P.zero k C.E) ∧
      (P.slim.centres = ∅ → C.slimPiece_ZSP35 K₃.carrier = ∅) ∧
      (∀ k : Fin D₃.m,
        (∃ F₀ : StandardWholeSurfaceFibre_EFE C.slimSubmersion_EFE (𝓡 2) ClosureSphere.{0}
            (D₃.arc k 0),
          Nonempty (WholeSurfaceIntervalProduct_EFE C.slimSubmersion_EFE (D₃.arc_EFE k) F₀)) ∨
        (∃ F₀ : StandardWholeSurfaceFibre_EFE C.slimSubmersion_EFE torusModel Torus (D₃.arc k 0),
          Nonempty (WholeSurfaceIntervalProduct_EFE C.slimSubmersion_EFE (D₃.arc_EFE k) F₀))) ∧
      ∀ j : Fin D₃.l, ∀ t₀ ℓ : ℝ, ∀ hℓ : ℓ ∈ Ioo (0 : ℝ) 1,
        (∃ F₀ : StandardWholeSurfaceFibre_EFE C.slimSubmersion_EFE (𝓡 2) ClosureSphere.{0}
            ((D₃.loopArc_EFE j t₀ ℓ hℓ).toFun 0),
          Nonempty (WholeSurfaceIntervalProduct_EFE C.slimSubmersion_EFE
            (D₃.loopArc_EFE j t₀ ℓ hℓ) F₀)) ∨
        (∃ F₀ : StandardWholeSurfaceFibre_EFE C.slimSubmersion_EFE torusModel Torus
            ((D₃.loopArc_EFE j t₀ ℓ hℓ).toFun 0),
          Nonempty (WholeSurfaceIntervalProduct_EFE C.slimSubmersion_EFE
            (D₃.loopArc_EFE j t₀ ℓ hℓ) F₀)) := by
  refine ⟨C.gaf07_slim_row_GAFD hK oM, ?_⟩
  obtain ⟨K₃, D₃, hD, hKs, hdisj, hreg, hbd⟩ := C.zsp04_D3_ZSP35 hεr
  obtain ⟨-, hC3B, -, -, -⟩ := C.zsp03_slim_saturated_ZSP35 hεr
  obtain ⟨-, hI, -⟩ := C.toChain.zsp04_slab_image_ZSP35
  have hKc := K₃.isCompact_carrier_BCF
  have hKB := K₃.subset_base
  have hKreg : K₃.carrier ∩ C.slimC3_ZSP35 ⊆ closure (Subtype.val '' interior
      (Subtype.val ⁻¹' (K₃.carrier ∩ C.slimC3_ZSP35) : Set C.slimBs_ZSP35)) := by
    rw [← hD]
    exact hreg
  obtain ⟨hSeq, hSc, hSreg, himg, hcollar, hfaces, -⟩ := C.slimPiece_spec_ZSP35 hεr hKc hKB
    (subset_union_right.trans hKs) hKreg
  refine ⟨K₃, D₃, hD, hKs, hdisj, hreg, hbd, hSeq, hSc, hSreg, ?_, ?_, hcollar, hfaces,
    fun h0 => ?_, fun k => C.slim_arc_product_EFE hK (D₃.arc_EFE k),
    fun j t₀ ℓ hℓ => C.slim_arc_product_EFE hK (D₃.loopArc_EFE j t₀ ℓ hℓ)⟩
  · rw [himg, hD]
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

end Gaf02ChainEJA

end DifferentialGeometry.Geometry.Collapse
