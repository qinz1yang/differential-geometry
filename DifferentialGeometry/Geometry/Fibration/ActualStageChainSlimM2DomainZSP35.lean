import DifferentialGeometry.Geometry.Fibration.ActualStageChainSlimEndFaceZSP35
import DifferentialGeometry.Geometry.Fibration.ActualStageChainEZeroRatio
import DifferentialGeometry.Topology.Ehresmann.ZeroDomainLocalZSP35

/-!
# ZSP05: `M₂` is a compact smooth domain (a regular domain in `M`)

Lane S-ZSP04, group G21. Blueprint `master207B.tex`, ZSP05 (B:6597–6640): "Then `M₂` is a compact
smooth manifold with boundary" with the three kinds of local cases of the proof: (1) at a
component of `∂M₁` not met by `M^slim` the piece is absent on a neighbourhood and `M₂ = M₁` there,
smooth by the zero domain's regular defining function; (2) at a shared zero/slim face `M₂` is empty
near it (point-set, G12/G16); (3) at a free slim face the product collar cuts off one side and
`M₂ = {h ≥ 0}` (G20).

* `slim_zero_domain_ZSP35` (zero side, kernel `ZeroDomainLocalZSP35`): with the global ratios `F_k`
  of ZSP02 (G9) and the compact disjoint `Z_k = {F_k ≤ 0}`: every point of `∂M₁` has an open
  neighbourhood `U` and a smooth `F_k` regular at its zeros with `M₁ ∩ U = {F_k ≥ 0} ∩ U`, and
  every point of `∂Z` lies in `∂M₁`.
* `zsp05_M2_domain_ZSP35` (final family, `K ≥ 5`): for the `K₃, D₃` of ZSP04, EVERY point of `∂M₂`
  has an open neighbourhood `U` and a function `φ`, smooth on `U` with `dφ ≠ 0` at the zeros in `U`,
  with `M₂ ∩ U = {φ ≥ 0} ∩ U`.

Consumer: `zsp05_M2_domain_C14Z_ZSP35`.
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

/-- **The zero side of ZSP05** (see the module docstring). -/
theorem slim_zero_domain_ZSP35
    (C : Gaf02ChainEJA P.toLocalChartPacketsC14D.toLocalChartPacketsC14 Kj Ξ Γ S eg c cw cadj)
    (hεr : εr < 1 / 2) :
    (∀ x ∈ frontier (interior C.zeroUnion_ZSP35)ᶜ, ∃ (φ : X → ℝ) (U : Set X), IsOpen U ∧ x ∈ U ∧
      ContMDiff 𝓘(ℝ, E3) 𝓘(ℝ, ℝ) ∞ φ ∧
      (∀ z, φ z = 0 → mfderiv 𝓘(ℝ, E3) 𝓘(ℝ, ℝ) φ z ≠ 0) ∧
      (interior C.zeroUnion_ZSP35)ᶜ ∩ U = {z | z ∈ U ∧ 0 ≤ φ z}) ∧
    frontier C.zeroUnion_ZSP35 ⊆ frontier (interior C.zeroUnion_ZSP35)ᶜ := by
  have hex := fun k : P.zero.finite_centres.toFinset =>
    C.toGaf02ChainE.zsp02_global_ratio_ZSP35 hεr k
  choose F N hNo hFN hNr hFs hFr hFle hF0 hFreg using hex
  have hcl : ∀ k : P.zero.finite_centres.toFinset,
      IsClosed (zspDomain_ZSP35 P.toLocalChartFamily P.zero k C.E) := fun k =>
    (C.toGaf02ChainE.zsp02_domain_ZSP35 hεr k).1.isClosed
  have hdisj : ∀ k k' : P.zero.finite_centres.toFinset, k ≠ k' →
      Disjoint (zspDomain_ZSP35 P.toLocalChartFamily P.zero k C.E)
        (zspDomain_ZSP35 P.toLocalChartFamily P.zero k' C.E) := fun k k' hkk =>
    C.toGaf02ChainE.zsp02_disjoint_ZSP35 hεr hkk
  have hZ : C.zeroUnion_ZSP35 = ⋃ k : P.zero.finite_centres.toFinset,
      zspDomain_ZSP35 P.toLocalChartFamily P.zero k C.E := rfl
  rw [hZ]
  refine ⟨fun x hx => ?_, fun x hx => ?_⟩
  · obtain ⟨k, U, hUo, hxU, -, hM⟩ := zero_domain_local_ZSP35 (I := 𝓘(ℝ, E3)) hcl hdisj hFs hFle
      hFreg hx
    exact ⟨F k, U, hUo, hxU, hFs k, hFreg k, hM⟩
  · obtain ⟨-, hfr⟩ := frontier_disjoint_iUnion_ZSP35 _ hcl hdisj
    rw [hfr] at hx
    obtain ⟨k, hk⟩ := mem_iUnion.mp hx
    rw [(C.toGaf02ChainE.zsp02_domain_ZSP35 hεr k).2.2.1, ← hF0 k] at hk
    exact zero_mem_frontier_ZSP35 (I := 𝓘(ℝ, E3)) hcl hdisj hFs hFle hFreg hk

/-- The frontier of `M₂` (ZSP05 (RF)), from the slim piece specification. -/
theorem slim_M2_frontier_ZSP35
    (C : Gaf02ChainEJA P.toLocalChartPacketsC14D.toLocalChartPacketsC14 Kj Ξ Γ S eg c cw cadj)
    (hεr : εr < 1 / 2) (K₃ D₃ : SmoothCompactOneDomain_BCF C.slimBs_ZSP35)
    (hD : D₃.carrier = K₃.carrier ∩ C.slimC3_ZSP35)
    (hKs : C.toChain.slimSlabImage_ZSP35 ∪ C.slimFacePoints_ZSP35 ⊆
      Subtype.val '' interior (Subtype.val ⁻¹' K₃.carrier : Set C.slimBs_ZSP35))
    (hDreg : D₃.carrier ⊆ closure (Subtype.val '' interior
        (Subtype.val ⁻¹' D₃.carrier : Set C.slimBs_ZSP35))) :
    frontier ((interior C.zeroUnion_ZSP35)ᶜ \ Subtype.val '' interior
        (Subtype.val ⁻¹' C.slimPiece_ZSP35 K₃.carrier : Set ↥(interior C.zeroUnion_ZSP35)ᶜ)) =
      (frontier (interior C.zeroUnion_ZSP35)ᶜ \ C.slimPiece_ZSP35 K₃.carrier) ∪
        (frontier (C.slimPiece_ZSP35 K₃.carrier) \ frontier (interior C.zeroUnion_ZSP35)ᶜ) := by
  have hreg' : K₃.carrier ∩ C.slimC3_ZSP35 ⊆ closure (Subtype.val '' interior
      (Subtype.val ⁻¹' (K₃.carrier ∩ C.slimC3_ZSP35) : Set C.slimBs_ZSP35)) := hD ▸ hDreg
  obtain ⟨-, -, -, -, -, -, hM⟩ :=
    C.slimPiece_spec_ZSP35 hεr K₃.isCompact_carrier_BCF K₃.subset_base
      (subset_union_right.trans hKs) hreg'
  obtain ⟨-, -, hfr, -⟩ := hM
  exact hfr

/-- The smooth side of `M₂` at a free arc end of `D₃`, inside `M₁`. -/
theorem slim_free_end_M2_ZSP35
    (C : Gaf02ChainEJA P.toLocalChartPacketsC14D.toLocalChartPacketsC14 Kj Ξ Γ S eg c cw cadj)
    (hεr : εr < 1 / 2) (K₃ D₃ : SmoothCompactOneDomain_BCF C.slimBs_ZSP35)
    (hSD : C.slimPiece_ZSP35 K₃.carrier = C.slimMap_ZSP35 ⁻¹' D₃.carrier)
    {y : BlockSpace (fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²)}
    (hy : ∃ k : Fin D₃.m, y = D₃.arc k 0 ∨ y = D₃.arc k 1)
    (hyC : y ∈ Subtype.val '' interior (Subtype.val ⁻¹' C.slimC3_ZSP35 : Set C.slimBs_ZSP35)) :
    ∃ (U : Set X) (h : X → ℝ), IsOpen U ∧ C.slimMap_ZSP35 ⁻¹' {y} ⊆ U ∧
      ContMDiffOn 𝓘(ℝ, E3) 𝓘(ℝ, ℝ) ∞ h U ∧
      (∀ x ∈ U, Surjective (mfderiv 𝓘(ℝ, E3) 𝓘(ℝ, ℝ) h x)) ∧
      ((interior C.zeroUnion_ZSP35)ᶜ \ Subtype.val '' interior
        (Subtype.val ⁻¹' C.slimPiece_ZSP35 K₃.carrier :
          Set ↥(interior C.zeroUnion_ZSP35)ᶜ)) ∩ U = {x | x ∈ U ∧ 0 ≤ h x} := by
  obtain ⟨U, h, hUo, hfU, hUM, -, hh, hsurj, -, hside⟩ :=
    C.slim_free_end_tube_ZSP35 hεr D₃ hy hyC
  have hS : C.slimPiece_ZSP35 K₃.carrier ∩ U = {x | x ∈ U ∧ h x ≤ 0} := by
    rw [hSD, inter_comm]
    exact hside
  exact ⟨U, h, hUo, hfU, hh, hsurj, free_end_M2_ZSP35 hUo hUM hh hsurj hS⟩

/-- `M₂ = M₁ ∖ int_{M₁} M^slim` is compact (ZSP05 (RC)). -/
theorem slim_M2_compact_ZSP35
    (C : Gaf02ChainEJA P.toLocalChartPacketsC14D.toLocalChartPacketsC14 Kj Ξ Γ S eg c cw cadj)
    (hεr : εr < 1 / 2) (K₃ D₃ : SmoothCompactOneDomain_BCF C.slimBs_ZSP35)
    (hD : D₃.carrier = K₃.carrier ∩ C.slimC3_ZSP35)
    (hKs : C.toChain.slimSlabImage_ZSP35 ∪ C.slimFacePoints_ZSP35 ⊆
      Subtype.val '' interior (Subtype.val ⁻¹' K₃.carrier : Set C.slimBs_ZSP35))
    (hDreg : D₃.carrier ⊆ closure (Subtype.val '' interior
        (Subtype.val ⁻¹' D₃.carrier : Set C.slimBs_ZSP35))) :
    IsCompact ((interior C.zeroUnion_ZSP35)ᶜ \ Subtype.val '' interior
      (Subtype.val ⁻¹' C.slimPiece_ZSP35 K₃.carrier : Set ↥(interior C.zeroUnion_ZSP35)ᶜ)) := by
  have hreg' : K₃.carrier ∩ C.slimC3_ZSP35 ⊆ closure (Subtype.val '' interior
      (Subtype.val ⁻¹' (K₃.carrier ∩ C.slimC3_ZSP35) : Set C.slimBs_ZSP35)) := hD ▸ hDreg
  obtain ⟨-, -, -, -, -, -, hM⟩ :=
    C.slimPiece_spec_ZSP35 hεr K₃.isCompact_carrier_BCF K₃.subset_base
      (subset_union_right.trans hKs) hreg'
  obtain ⟨hc, -⟩ := hM
  exact hc

/-- **ZSP05: `M₂` is a compact smooth domain** (B:6597–6640): for the `K₃, D₃ = K₃ ∩ C₃` of ZSP04
every point of `∂M₂` has an open neighbourhood `U` and a function `φ`, smooth on `U` with
`dφ ≠ 0` at its zeros, such that `M₂ ∩ U = {φ ≥ 0} ∩ U`. -/
theorem zsp05_M2_domain_ZSP35
    (C : Gaf02ChainEJA P.toLocalChartPacketsC14D.toLocalChartPacketsC14 Kj Ξ Γ S eg c cw cadj)
    (hεr : εr < 1 / 2) :
    ∃ K₃ D₃ : SmoothCompactOneDomain_BCF C.slimBs_ZSP35,
      D₃.carrier = K₃.carrier ∩ C.slimC3_ZSP35 ∧
      IsCompact ((interior C.zeroUnion_ZSP35)ᶜ \ Subtype.val '' interior
        (Subtype.val ⁻¹' C.slimPiece_ZSP35 K₃.carrier : Set ↥(interior C.zeroUnion_ZSP35)ᶜ)) ∧
      ∀ x ∈ frontier ((interior C.zeroUnion_ZSP35)ᶜ \ Subtype.val '' interior
          (Subtype.val ⁻¹' C.slimPiece_ZSP35 K₃.carrier : Set ↥(interior C.zeroUnion_ZSP35)ᶜ)),
        ∃ (U : Set X) (φ : X → ℝ), IsOpen U ∧ x ∈ U ∧
          ContMDiffOn 𝓘(ℝ, E3) 𝓘(ℝ, ℝ) ∞ φ U ∧
          (∀ z ∈ U, φ z = 0 → mfderiv 𝓘(ℝ, E3) 𝓘(ℝ, ℝ) φ z ≠ 0) ∧
          ((interior C.zeroUnion_ZSP35)ᶜ \ Subtype.val '' interior
            (Subtype.val ⁻¹' C.slimPiece_ZSP35 K₃.carrier :
              Set ↥(interior C.zeroUnion_ZSP35)ᶜ)) ∩ U = {z | z ∈ U ∧ 0 ≤ φ z} := by
  obtain ⟨K₃, D₃, hD, hKs, hKF, hDreg, hdD⟩ := C.zsp04_D3_ZSP35 hεr
  obtain ⟨hSD, -, hSc, -, -, -, hfz, -, hfp⟩ :=
    C.slim_piece_facts_ZSP35 hεr K₃ D₃ hD hKs hKF hDreg
  have hfr := C.slim_M2_frontier_ZSP35 hεr K₃ D₃ hD hKs hDreg
  obtain ⟨hzero, hzfr⟩ := C.slim_zero_domain_ZSP35 hεr
  refine ⟨K₃, D₃, hD, C.slim_M2_compact_ZSP35 hεr K₃ D₃ hD hKs hDreg, fun x hx => ?_⟩
  rw [hfr] at hx
  rcases hx with ⟨hx1, hxp⟩ | ⟨hx2, hx3⟩
  · obtain ⟨φ, U₀, hU₀, hxU₀, hφ, hreg, hM1⟩ := hzero x hx1
    have hUo : IsOpen (U₀ ∩ (C.slimPiece_ZSP35 K₃.carrier)ᶜ) :=
      hU₀.inter hSc.isClosed.isOpen_compl
    refine ⟨U₀ ∩ (C.slimPiece_ZSP35 K₃.carrier)ᶜ, φ, hUo, ⟨hxU₀, hxp⟩, hφ.contMDiffOn,
      fun z _ hz => hreg z hz, ?_⟩
    ext z
    constructor
    · rintro ⟨⟨hzM, -⟩, hzU₀, hzp⟩
      have : z ∈ (interior C.zeroUnion_ZSP35)ᶜ ∩ U₀ := ⟨hzM, hzU₀⟩
      rw [hM1] at this
      exact ⟨⟨hzU₀, hzp⟩, this.2⟩
    · rintro ⟨⟨hzU₀, hzp⟩, hz0⟩
      have hzM : z ∈ (interior C.zeroUnion_ZSP35)ᶜ ∩ U₀ := by
        rw [hM1]
        exact ⟨hzU₀, hz0⟩
      refine ⟨⟨hzM.1, fun hzr => ?_⟩, hzU₀, hzp⟩
      obtain ⟨-, O, -, hzO, hOM⟩ := mem_image_interior_preimage_val_iff.mp hzr
      exact hzp (hOM ⟨hzO, hzM.1⟩)
  · have hx2' := hx2
    rw [hfp] at hx2'
    have hyb : C.slimMap_ZSP35 x ∈ D₃.carrier \ Subtype.val '' interior
        (Subtype.val ⁻¹' D₃.carrier : Set C.slimBs_ZSP35) := hx2'
    have hends := hyb
    rw [D₃.relFrontier_eq] at hends
    obtain ⟨k, hk⟩ := mem_iUnion.mp hends
    have hyk : ∃ k : Fin D₃.m, C.slimMap_ZSP35 x = D₃.arc k 0 ∨
        C.slimMap_ZSP35 x = D₃.arc k 1 := ⟨k, hk⟩
    rw [hdD] at hyb
    rcases hyb with hfree | hzero'
    · obtain ⟨U, h, hUo, hfU, hh, hsurj, hM⟩ := C.slim_free_end_M2_ZSP35 hεr K₃ D₃ hSD hyk hfree.2
      refine ⟨U, h, hUo, hfU rfl, hh, fun z hz _ h0 => ?_, hM⟩
      let w : ℝ := 1
      obtain ⟨v, hv⟩ := hsurj z hz w
      rw [h0, zero_apply] at hv
      have h01 : (0 : ℝ) = 1 := hv
      exact zero_ne_one h01
    · exfalso
      apply hx3
      refine hzfr ?_
      have hxp : x ∈ C.slimPiece_ZSP35 K₃.carrier ∩ frontier C.zeroUnion_ZSP35 := by
        rw [hfz]
        have hyK : C.slimMap_ZSP35 x ∈ K₃.carrier := by
          obtain ⟨hyB, O, -, hyO, hOK⟩ := mem_image_interior_preimage_val_iff.mp hzero'.1
          exact hOK ⟨hyO, hyB⟩
        exact ⟨hyK, hzero'.2⟩
      exact hxp.2

end Final

end Gaf02ChainEJA

section Consumer

/-- **Consumer: `M₂` is a compact smooth domain on the final family**: for the `K₃, D₃` of ZSP04,
`M₂ = M₁ ∖ int_{M₁} M^slim` is compact and every point of `∂M₂` has an open neighbourhood in
which `M₂` is `{φ ≥ 0}` for a smooth `φ` regular at its zeros. -/
theorem zsp05_M2_domain_C14Z_ZSP35 {oM : ManifoldOrientation 𝓘(ℝ, E3) X 3} {cadj : ℝ}
    {P : LocalChartPacketsC14Z X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e
      T V vs ζ Λz oM}
    (C : Gaf02ChainEJA P.toLocalChartPacketsC14D.toLocalChartPacketsC14 Kj Ξ Γ S eg c cw cadj)
    (hεr : εr < 1 / 2) :
    ∃ K₃ D₃ : SmoothCompactOneDomain_BCF C.slimBs_ZSP35,
      D₃.carrier = K₃.carrier ∩ C.slimC3_ZSP35 ∧
      IsCompact ((interior C.zeroUnion_ZSP35)ᶜ \ Subtype.val '' interior
        (Subtype.val ⁻¹' C.slimPiece_ZSP35 K₃.carrier : Set ↥(interior C.zeroUnion_ZSP35)ᶜ)) ∧
      ∀ x ∈ ((interior C.zeroUnion_ZSP35)ᶜ \ Subtype.val '' interior
          (Subtype.val ⁻¹' C.slimPiece_ZSP35 K₃.carrier : Set ↥(interior C.zeroUnion_ZSP35)ᶜ)),
        x ∈ interior ((interior C.zeroUnion_ZSP35)ᶜ \ Subtype.val '' interior
          (Subtype.val ⁻¹' C.slimPiece_ZSP35 K₃.carrier : Set ↥(interior C.zeroUnion_ZSP35)ᶜ)) ∨
        ∃ (U : Set X) (φ : X → ℝ), IsOpen U ∧ x ∈ U ∧
          ContMDiffOn 𝓘(ℝ, E3) 𝓘(ℝ, ℝ) ∞ φ U ∧
          (∀ z ∈ U, φ z = 0 → mfderiv 𝓘(ℝ, E3) 𝓘(ℝ, ℝ) φ z ≠ 0) ∧
          ((interior C.zeroUnion_ZSP35)ᶜ \ Subtype.val '' interior
            (Subtype.val ⁻¹' C.slimPiece_ZSP35 K₃.carrier :
              Set ↥(interior C.zeroUnion_ZSP35)ᶜ)) ∩ U = {z | z ∈ U ∧ 0 ≤ φ z} := by
  obtain ⟨K₃, D₃, hD, hcpt, hdom⟩ := C.zsp05_M2_domain_ZSP35 hεr
  refine ⟨K₃, D₃, hD, hcpt, fun x hx => ?_⟩
  by_cases hint : x ∈ interior ((interior C.zeroUnion_ZSP35)ᶜ \ Subtype.val '' interior
      (Subtype.val ⁻¹' C.slimPiece_ZSP35 K₃.carrier : Set ↥(interior C.zeroUnion_ZSP35)ᶜ))
  · exact Or.inl hint
  · refine Or.inr (hdom x ⟨?_, hint⟩)
    rw [hcpt.isClosed.closure_eq]
    exact hx

end Consumer

end DifferentialGeometry.Geometry.Collapse
