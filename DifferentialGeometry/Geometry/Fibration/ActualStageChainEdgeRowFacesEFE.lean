import DifferentialGeometry.Geometry.Fibration.ActualStageChainEdgeRowEFE
import DifferentialGeometry.Geometry.Fibration.ActualStageChainEdgeCompactDomainEFE
import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.EdgeBaseComponentsEIM

/-!
# FDC02 / EDP05: the horizontal faces `H = ∂M₂ ∩ X₂ = f₂⁻¹(∂C₂)` and the whole edge row, G9

Lane S-EDP-FDC4, group G9 (third part). Blueprint `master207B.tex`, EDP05 (B:7040–7090, the faces
(EF) B:7048–7052) and FDC02 (B:7246–7283). On the final-family chain `C : Gaf02ChainEJA …` with
ZSP04's `K₃, D₃` and the smooth stage bases `A`:

* `edge_face_data_EFE`: at a point `x ∈ ∂M₂` the raw descended defining function (zero face or free
  slim face): `x ∈ M₂`, an open `N ∋ π₂E x`, `hh` smooth on `N`, `z ∈ M₂ ↔ hh(π₂E z) ≥ 0` over
  `{π₂E ∈ N}`, and `F = hh ∘ π₂E` with `dF(x) ≠ 0`;
* `edge_frontier_H_EFE` (**(EF) horizontal face**): `∂M₂ ∩ X₂ = f₂⁻¹(∂C₂) ∩ X₂` with
  `X₂ = {x ∈ source | T x ≤ 4Δ}`;
* `edge_vertical_V_EFE` (**(EF) vertical face**): `M₂ ∩ ∂X₂ = f₂⁻¹(C₂) ∩ {T = 4Δ}`;
* `edge_components_EFE`: E2 (S-EDGE-INT) on the abstract base: finite interval / circle
  components of `C₂`;
* `edgeRow_EFE`: the whole row — compactness, saturation, smooth domain faces, components, proper
  whole-disk bundle (properness, disks, submersion, rank two), and the faces (EF).
-/

set_option autoImplicit false

noncomputable section

open Set Function Metric Bundle Manifold Filter
open scoped ContDiff Manifold Topology
open DifferentialGeometry.Geometry.Riemannian GC.MetricGeometry
open DifferentialGeometry.Analysis DifferentialGeometry.Topology.Manifold
open DifferentialGeometry.Topology
open GC.GraphManifold.Assembly.FC39P0
open DifferentialGeometry.Topology.Manifold.OneManifold

namespace DifferentialGeometry.Geometry.Collapse

local notation "E3" => EuclideanSpace ℝ (Fin 3)
local notation "ℝ²" => EuclideanSpace ℝ (Fin 2)

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace

attribute [local instance] nezero_finrank_euclideanThree_LC87

open DifferentialGeometry.Topology.Handle in
attribute [local instance] closedCellChartedSpaceSucc closedCellIsManifold

attribute [local instance] LocalChartPackets.instMetricN LocalChartPackets.instChartedN
  LocalChartPackets.instMetricC

variable {X : Type} [mX : MetricSpace X] [ChartedSpace E3 X] [IsManifold 𝓘(ℝ, E3) ∞ X]
  [CompactSpace X] {g : SmoothRiemannianMetric 𝓘(ℝ, E3) X}
  {hmetric : ∀ a b : X, riemannianEDistOf g a b = ENNReal.ofReal (dist a b)}
  {ρ : X → ℝ} {hρ : ∀ p, 0 < ρ p} {Λ : ℝ} {β : ℕ → ℝ} {Δ σs : ℝ} {K : ℕ}
  {σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs ζ Λz : ℝ}
  {Kj : ℕ} {Ξ Γ S eg c cw : Fin 3 → ℝ}

namespace Gaf02ChainEJA

section Faces

variable {oM : ManifoldOrientation 𝓘(ℝ, E3) X 3} {cadj : ℝ}
  {P : LocalChartPacketsC14Z X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e
    T V vs ζ Λz oM}

/-- `M₂` of the cut choice at `K₃` (abbreviation of `cutM2_R74`). -/
abbrev edgeM2_EFE
    (C : Gaf02ChainEJA P.toLocalChartPacketsC14D.toLocalChartPacketsC14 Kj Ξ Γ S eg c cw cadj)
    (K₃ : SmoothCompactOneDomain_BCF C.slimBs_ZSP35) : Set X :=
  C.toGaf02ChainE.cutM2_R74 K₃.carrier

/-- `C₂ = f₂(M^edge)`, the edge base domain (abbreviation). -/
abbrev edgeC2_EFE
    (C : Gaf02ChainEJA P.toLocalChartPacketsC14D.toLocalChartPacketsC14 Kj Ξ Γ S eg c cw cadj)
    (K₃ : SmoothCompactOneDomain_BCF C.slimBs_ZSP35) : Set C.edgeBaseOpens_EFE :=
  C.edgeProj_EFE '' {x : C.edgeSource_EFE | (x : X) ∈ edgeM2_EFE C K₃ ∧
    C.edgeHeight_EFE x ≤ 4 * Δ}

/-- **EDP05's raw face data** (B:7061–7084): at a point `x` of `∂M₂` the defining function of `M₂`
descends over a neighbourhood `N` of `π₂E x` (zero face: the retained ratio, free slim face: the
chosen endpoint coordinate of `D₃`); `F = hh ∘ π₂E` is an ambient defining function of nonzero
differential at `x`. -/
theorem edge_face_data_EFE
    (C : Gaf02ChainEJA P.toLocalChartPacketsC14D.toLocalChartPacketsC14 Kj Ξ Γ S eg c cw cadj)
    (hεr : εr < 1 / 2)
    (K₃ D₃ : SmoothCompactOneDomain_BCF C.slimBs_ZSP35)
    (hD : D₃.carrier = K₃.carrier ∩ C.slimC3_ZSP35)
    (hKs : C.toChain.slimSlabImage_ZSP35 ∪ C.slimFacePoints_ZSP35 ⊆
      Subtype.val '' interior (Subtype.val ⁻¹' K₃.carrier : Set C.slimBs_ZSP35))
    (hKF : Disjoint (K₃.carrier \
        Subtype.val '' interior (Subtype.val ⁻¹' K₃.carrier : Set C.slimBs_ZSP35))
      C.slimFacePoints_ZSP35)
    (hDreg : D₃.carrier ⊆ closure (Subtype.val '' interior
        (Subtype.val ⁻¹' D₃.carrier : Set C.slimBs_ZSP35)))
    (hdD : D₃.carrier \ Subtype.val '' interior
        (Subtype.val ⁻¹' D₃.carrier : Set C.slimBs_ZSP35) =
      ((K₃.carrier \ Subtype.val '' interior
            (Subtype.val ⁻¹' K₃.carrier : Set C.slimBs_ZSP35)) ∩
          Subtype.val '' interior (Subtype.val ⁻¹' C.slimC3_ZSP35 : Set C.slimBs_ZSP35)) ∪
        (Subtype.val '' interior (Subtype.val ⁻¹' K₃.carrier : Set C.slimBs_ZSP35) ∩
          C.slimFacePoints_ZSP35))
    {x : X} (hx : x ∈ frontier (edgeM2_EFE C K₃)) :
    x ∈ edgeM2_EFE C K₃ ∧
    ∃ N : Set (BlockSpace (fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²)), IsOpen N ∧
      C.toGaf02ChainE.edgeBlockProj_EFE x ∈ N ∧
      ∃ hh : BlockSpace (fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²) → ℝ,
        ContDiffOn ℝ ∞ hh N ∧
        (∀ z : X, C.toGaf02ChainE.edgeBlockProj_EFE z ∈ N →
          (z ∈ edgeM2_EFE C K₃ ↔ 0 ≤ hh (C.toGaf02ChainE.edgeBlockProj_EFE z))) ∧
        ∃ F : X → ℝ, MDifferentiableAt 𝓘(ℝ, E3) 𝓘(ℝ, ℝ) F x ∧
          mfderiv 𝓘(ℝ, E3) 𝓘(ℝ, ℝ) F x ≠ 0 ∧
          ∀ z : X, F z = hh (C.toGaf02ChainE.edgeBlockProj_EFE z) := by
  have hSD : C.slimPiece_ZSP35 K₃.carrier = C.slimMap_ZSP35 ⁻¹' D₃.carrier :=
    (C.slim_piece_facts_ZSP35 hεr K₃ D₃ hD hKs hKF hDreg).1
  have hKc : IsClosed K₃.carrier := K₃.isCompact_carrier_BCF.isClosed
  rcases C.frontier_cutM2_cases_EFE hεr K₃ D₃ hD hKs hKF hDreg hdD hx with
    ⟨k, hk, hK⟩ | ⟨y, hy, hyC, hxy⟩
  · refine ⟨(C.toGaf02ChainE.edge_zero_fibre_subset_M2_EFE hεr K₃.carrier k hk hK rfl).2, ?_⟩
    exact C.toGaf02ChainE.edge_zero_face_descent_EFE hεr hKc k hk hK
  · refine ⟨(C.edge_slim_face_descent_EFE hεr K₃ D₃ hSD hy hyC hxy).1 x rfl, ?_⟩
    obtain ⟨-, N, hNo, hxN, hh, hhs, hdef, F, hF, hFne, hFeq⟩ :=
      C.edge_slim_face_descent_EFE hεr K₃ D₃ hSD hy hyC hxy
    exact ⟨N, hNo, hxN, hh, hhs.contDiffOn, hdef, F, hF, hFne, hFeq⟩

/-- **(EF), horizontal face** (B:7048–7052): `H = ∂M₂ ∩ X₂ = f₂⁻¹(∂C₂)` (with `X₂ = {T ≤ 4Δ}` in
the source). At a point of `∂M₂` the descended defining function is regular, so the base point
is a frontier point of `C₂`; conversely over a frontier point of `C₂` the whole disk lies in
`∂M₂` (hface, regularity along the whole fibre). -/
theorem edge_frontier_H_EFE
    (C : Gaf02ChainEJA P.toLocalChartPacketsC14D.toLocalChartPacketsC14 Kj Ξ Γ S eg c cw cadj)
    (A : SmoothStageBasesOn74 C.toChain)
    (hεr : εr < 1 / 2) (hΔ2 : 2 ≤ Δ)
    (hc : c 2 < 1 / 100000)
    (hϑ : 100 * (gafDerivativeBound + 1) * (1 + gafCutoffConstant + 1 * cw 0 / S 0) * Λ * Δ <
      1 / 1000000) (hε0 : 0 ≤ ε) (hε : ε < 1) (hμ : μ ≤ 1 / 10 ^ 8) (hτ : τ ≤ 1 / 10 ^ 8)
    (hσc : σc ≤ 1 / 1000) (hb : b * (1000 * Δ) ≤ 1) (hγc : 0 < γc) (hγc1 : γc ≤ 1 / 100)
    (hβc1 : βc ≤ 1 / 100000)
    (K₃ D₃ : SmoothCompactOneDomain_BCF C.slimBs_ZSP35)
    (hD : D₃.carrier = K₃.carrier ∩ C.slimC3_ZSP35)
    (hKs : C.toChain.slimSlabImage_ZSP35 ∪ C.slimFacePoints_ZSP35 ⊆
      Subtype.val '' interior (Subtype.val ⁻¹' K₃.carrier : Set C.slimBs_ZSP35))
    (hKF : Disjoint (K₃.carrier \
        Subtype.val '' interior (Subtype.val ⁻¹' K₃.carrier : Set C.slimBs_ZSP35))
      C.slimFacePoints_ZSP35)
    (hDreg : D₃.carrier ⊆ closure (Subtype.val '' interior
        (Subtype.val ⁻¹' D₃.carrier : Set C.slimBs_ZSP35)))
    (hdD : D₃.carrier \ Subtype.val '' interior
        (Subtype.val ⁻¹' D₃.carrier : Set C.slimBs_ZSP35) =
      ((K₃.carrier \ Subtype.val '' interior
            (Subtype.val ⁻¹' K₃.carrier : Set C.slimBs_ZSP35)) ∩
          Subtype.val '' interior (Subtype.val ⁻¹' C.slimC3_ZSP35 : Set C.slimBs_ZSP35)) ∪
        (Subtype.val '' interior (Subtype.val ⁻¹' K₃.carrier : Set C.slimBs_ZSP35) ∩
          C.slimFacePoints_ZSP35))
    (hcpt : IsCompact (edgeM2_EFE C K₃ ∩
      Subtype.val '' {x : C.edgeSource_EFE | C.edgeHeight_EFE x ≤ 4 * Δ})) :
    let _ := A.edgeChartedSpace1
    frontier (edgeM2_EFE C K₃) ∩
        Subtype.val '' {x : C.edgeSource_EFE | C.edgeHeight_EFE x ≤ 4 * Δ} =
      Subtype.val '' {x : C.edgeSource_EFE | C.edgeHeight_EFE x ≤ 4 * Δ ∧
        C.edgeProj_EFE x ∈ frontier (edgeC2_EFE C K₃)} := by
  intro _
  have hproj := C.edgeProj_contMDiff_EFE A
  have hdisk : ∀ cc : C.edgeBaseOpens_EFE, ∃ φ : ClosedCell 2 → X, Continuous φ ∧
      range φ = Subtype.val '' {x : C.edgeSource_EFE | C.edgeProj_EFE x = cc ∧
        C.edgeHeight_EFE x ≤ 4 * Δ} := fun cc => by
    obtain ⟨φ, hφ, hr⟩ := C.toGaf02ChainE.edgeProj_disk_EFE hΔ2 hc hϑ hε0 hε hμ hτ hσc hb hγc
      hγc1 hβc1 cc
    exact ⟨φ, hφ.isEmbedding.continuous, hr⟩
  ext y
  constructor
  · rintro ⟨hyF, x, hxT, rfl⟩
    refine ⟨x, ⟨hxT, ?_⟩, rfl⟩
    obtain ⟨hyM, N, hN, hyN, hh, hhN, hdef, F, hF, hFne, hFeq⟩ :=
      C.edge_face_data_EFE hεr K₃ D₃ hD hKs hKF hDreg hdD hyF
    have hzero := eq_zero_of_mem_frontier_of_descended_EFE
      C.toGaf02ChainE.continuous_edgeBlockProj_EFE hN hhN.continuousOn hdef hyF hyM hyN
    obtain ⟨-, hcl⟩ := C.toGaf02ChainE.edge_regular_face_base_EFE A _ hN hhN hdef hFeq x hyN hFne
      hzero
    refine ⟨subset_closure ⟨x, ⟨hyM, hxT⟩, rfl⟩, ?_⟩
    rw [interior_eq_compl_closure_compl]
    exact not_not.mpr hcl
  · rintro ⟨x, ⟨hxT, hxf⟩, rfl⟩
    refine ⟨?_, x, hxT, rfl⟩
    obtain ⟨x₁, hx₁c, hx₁T, hx₁F⟩ := C.toGaf02ChainE.edgeBase_frontier_facePoint_EFE hΔ2 hdisk
      hproj.continuous hcpt hxf
    obtain ⟨hx₁M, N, hN, hx₁N, hh, hhN, hdef, F, hF, hFne, hFeq⟩ :=
      C.edge_face_data_EFE hεr K₃ D₃ hD hKs hKF hDreg hdD hx₁F
    have hzero := eq_zero_of_mem_frontier_of_descended_EFE
      C.toGaf02ChainE.continuous_edgeBlockProj_EFE hN hhN.continuousOn hdef hx₁F hx₁M hx₁N
    obtain ⟨hdb, -⟩ := C.toGaf02ChainE.edge_regular_face_base_EFE A _ hN hhN hdef hFeq x₁ hx₁N
      hFne hzero
    have hcl := C.toGaf02ChainE.edge_regular_face_fibre_EFE A _ hN hhN hdef hFeq x₁ hx₁N hzero
      hdb x hx₁c.symm
    have hsat := C.edgeDisk_face_saturated_EFE hεr hΔ2 K₃ D₃ hD hKs hKF hDreg hdD
      (C.edgeProj_EFE x) ⟨x₁.1, ⟨x₁, ⟨hx₁c, hx₁T⟩, rfl⟩, hx₁F⟩ ⟨x, ⟨rfl, hxT⟩, rfl⟩
    refine ⟨subset_closure hsat, ?_⟩
    rw [interior_eq_compl_closure_compl]
    exact not_not.mpr hcl

/-- **(EF), vertical face**: `V_e = M₂ ∩ ∂X₂ = f₂⁻¹(C₂) ∩ {T = 4Δ}`, from the saturation
`M₂ ∩ X₂ = f₂⁻¹(C₂) ∩ X₂` of E1. -/
theorem edge_vertical_V_EFE
    (C : Gaf02ChainEJA P.toLocalChartPacketsC14D.toLocalChartPacketsC14 Kj Ξ Γ S eg c cw cadj)
    (A : SmoothStageBasesOn74 C.toChain)
    (hεr : εr < 1 / 2) (hΔ2 : 2 ≤ Δ)
    (hc : c 2 < 1 / 100000)
    (hϑ : 100 * (gafDerivativeBound + 1) * (1 + gafCutoffConstant + 1 * cw 0 / S 0) * Λ * Δ <
      1 / 1000000) (hε0 : 0 ≤ ε) (hε : ε < 1) (hμ : μ ≤ 1 / 10 ^ 8) (hτ : τ ≤ 1 / 10 ^ 8)
    (hσc : σc ≤ 1 / 1000) (hb : b * (1000 * Δ) ≤ 1) (hγc : 0 < γc) (hγc1 : γc ≤ 1 / 100)
    (hβc1 : βc ≤ 1 / 100000)
    (K₃ D₃ : SmoothCompactOneDomain_BCF C.slimBs_ZSP35)
    (hD : D₃.carrier = K₃.carrier ∩ C.slimC3_ZSP35)
    (hKs : C.toChain.slimSlabImage_ZSP35 ∪ C.slimFacePoints_ZSP35 ⊆
      Subtype.val '' interior (Subtype.val ⁻¹' K₃.carrier : Set C.slimBs_ZSP35))
    (hKF : Disjoint (K₃.carrier \
        Subtype.val '' interior (Subtype.val ⁻¹' K₃.carrier : Set C.slimBs_ZSP35))
      C.slimFacePoints_ZSP35)
    (hDreg : D₃.carrier ⊆ closure (Subtype.val '' interior
        (Subtype.val ⁻¹' D₃.carrier : Set C.slimBs_ZSP35)))
    (hdD : D₃.carrier \ Subtype.val '' interior
        (Subtype.val ⁻¹' D₃.carrier : Set C.slimBs_ZSP35) =
      ((K₃.carrier \ Subtype.val '' interior
            (Subtype.val ⁻¹' K₃.carrier : Set C.slimBs_ZSP35)) ∩
          Subtype.val '' interior (Subtype.val ⁻¹' C.slimC3_ZSP35 : Set C.slimBs_ZSP35)) ∪
        (Subtype.val '' interior (Subtype.val ⁻¹' K₃.carrier : Set C.slimBs_ZSP35) ∩
          C.slimFacePoints_ZSP35))
    (hcpt : IsCompact (edgeM2_EFE C K₃ ∩
      Subtype.val '' {x : C.edgeSource_EFE | C.edgeHeight_EFE x ≤ 4 * Δ})) :
    let _ := A.edgeChartedSpace1
    edgeM2_EFE C K₃ ∩ Subtype.val '' {x : C.edgeSource_EFE | C.edgeHeight_EFE x = 4 * Δ} =
      Subtype.val '' {x : C.edgeSource_EFE | C.edgeProj_EFE x ∈ (edgeC2_EFE C K₃) ∧
        C.edgeHeight_EFE x = 4 * Δ} := by
  intro _
  obtain ⟨-, hsat, -⟩ := C.edgeCompactDomain_EFE A hεr hΔ2 hc hϑ hε0 hε hμ hτ hσc hb hγc hγc1
    hβc1 K₃ D₃ hD hKs hKF hDreg hdD hcpt
  ext y
  constructor
  · rintro ⟨hyM, x, hx, rfl⟩
    have h1 : (x : X) ∈ edgeM2_EFE C K₃ ∩
        Subtype.val '' {x : C.edgeSource_EFE | C.edgeHeight_EFE x ≤ 4 * Δ} :=
      ⟨hyM, x, hx.le, rfl⟩
    rw [hsat] at h1
    obtain ⟨x', ⟨hx'c, -⟩, hx'y⟩ := h1
    have : x' = x := Subtype.ext hx'y
    subst this
    exact ⟨x', ⟨hx'c, hx⟩, rfl⟩
  · rintro ⟨x, ⟨hxc, hx⟩, rfl⟩
    have h1 : (x : X) ∈ Subtype.val '' {x : C.edgeSource_EFE |
        C.edgeProj_EFE x ∈ (edgeC2_EFE C K₃) ∧ C.edgeHeight_EFE x ≤ 4 * Δ} := ⟨x, ⟨hxc, hx.le⟩, rfl⟩
    rw [← hsat] at h1
    exact ⟨h1.1, x, hx, rfl⟩

/-- **E2 on the actual base** (S-EDGE-INT): the finite interval / circle components of `C₂` with
smooth embedded parametrizations and the endpoint equivalence. -/
theorem edge_components_EFE
    (C : Gaf02ChainEJA P.toLocalChartPacketsC14D.toLocalChartPacketsC14 Kj Ξ Γ S eg c cw cadj)
    (A : SmoothStageBasesOn74 C.toChain)
    (hεr : εr < 1 / 2) (hΔ2 : 2 ≤ Δ)
    (hc : c 2 < 1 / 100000)
    (hϑ : 100 * (gafDerivativeBound + 1) * (1 + gafCutoffConstant + 1 * cw 0 / S 0) * Λ * Δ <
      1 / 1000000) (hε0 : 0 ≤ ε) (hε : ε < 1) (hμ : μ ≤ 1 / 10 ^ 8) (hτ : τ ≤ 1 / 10 ^ 8)
    (hσc : σc ≤ 1 / 1000) (hb : b * (1000 * Δ) ≤ 1) (hγc : 0 < γc) (hγc1 : γc ≤ 1 / 100)
    (hβc1 : βc ≤ 1 / 100000)
    (K₃ D₃ : SmoothCompactOneDomain_BCF C.slimBs_ZSP35)
    (hD : D₃.carrier = K₃.carrier ∩ C.slimC3_ZSP35)
    (hKs : C.toChain.slimSlabImage_ZSP35 ∪ C.slimFacePoints_ZSP35 ⊆
      Subtype.val '' interior (Subtype.val ⁻¹' K₃.carrier : Set C.slimBs_ZSP35))
    (hKF : Disjoint (K₃.carrier \
        Subtype.val '' interior (Subtype.val ⁻¹' K₃.carrier : Set C.slimBs_ZSP35))
      C.slimFacePoints_ZSP35)
    (hDreg : D₃.carrier ⊆ closure (Subtype.val '' interior
        (Subtype.val ⁻¹' D₃.carrier : Set C.slimBs_ZSP35)))
    (hdD : D₃.carrier \ Subtype.val '' interior
        (Subtype.val ⁻¹' D₃.carrier : Set C.slimBs_ZSP35) =
      ((K₃.carrier \ Subtype.val '' interior
            (Subtype.val ⁻¹' K₃.carrier : Set C.slimBs_ZSP35)) ∩
          Subtype.val '' interior (Subtype.val ⁻¹' C.slimC3_ZSP35 : Set C.slimBs_ZSP35)) ∪
        (Subtype.val '' interior (Subtype.val ⁻¹' K₃.carrier : Set C.slimBs_ZSP35) ∩
          C.slimFacePoints_ZSP35))
    (hcpt : IsCompact (edgeM2_EFE C K₃ ∩
      Subtype.val '' {x : C.edgeSource_EFE | C.edgeHeight_EFE x ≤ 4 * Δ})) :
    let _ := A.edgeChartedSpace1
    ∃ (m l : ℕ) (e : (Fin m ⊕ Fin l) ≃ ActualComponent (edgeC2_EFE C K₃))
      (a : Fin m → Icc (0 : ℝ) 1 → C.edgeBaseOpens_EFE)
      (cc : Fin l → Circle → C.edgeBaseOpens_EFE)
      (ε : (Fin m × Bool) ≃ {x : C.edgeBaseOpens_EFE // x ∈ frontier (edgeC2_EFE C K₃)}),
      (∀ i, IsSmoothEmbedding (𝓡∂ 1) (𝓡 1) ∞ (a i)) ∧
      (∀ i, range (a i) = (e (Sum.inl i)).1) ∧
      (∀ j, IsSmoothEmbedding (𝓡 1) (𝓡 1) ∞ (cc j)) ∧
      (∀ j, range (cc j) = (e (Sum.inr j)).1) ∧
      ∀ i b, (ε (i, b)).1 = a i (GC.GraphManifold.Assembly.iccEnd b) := by
  intro _
  have : IsManifold (𝓡 1) ∞ (C.toChain.finalBase_BAS 1) := A.edge_isManifold1.1
  obtain ⟨hC, -, hdom⟩ := C.edgeCompactDomain_EFE A hεr hΔ2 hc hϑ hε0 hε hμ hτ hσc hb hγc hγc1
    hβc1 K₃ D₃ hD hKs hKF hDreg hdD hcpt
  exact finite_interval_circle_components_EIM hC hdom

/-- **The `EdgeBundle` data of the actual chain over `B₂`**: the projection is smooth and a
submersion, has rank two with the height on the vertical boundary, is proper below `4Δ`, and has a
whole smooth disk over every base point (B:6949–7013, B:7040–7090). -/
theorem edgeBundleData_EFE
    (C : Gaf02ChainEJA P.toLocalChartPacketsC14D.toLocalChartPacketsC14 Kj Ξ Γ S eg c cw cadj)
    (A : SmoothStageBasesOn74 C.toChain)
    (hΔ2 : 2 ≤ Δ)
    (hc : c 2 < 1 / 100000)
    (hϑ : 100 * (gafDerivativeBound + 1) * (1 + gafCutoffConstant + 1 * cw 0 / S 0) * Λ * Δ <
      1 / 1000000) (hε0 : 0 ≤ ε) (hε : ε < 1) (hμ : μ ≤ 1 / 10 ^ 8) (hτ : τ ≤ 1 / 10 ^ 8)
    (hσc : σc ≤ 1 / 1000) (hb : b * (1000 * Δ) ≤ 1) (hγc : 0 < γc) (hγc1 : γc ≤ 1 / 100)
    (hβc1 : βc ≤ 1 / 100000) :
    let _ := A.edgeChartedSpace1
    ContMDiff 𝓘(ℝ, E3) (𝓡 1) ∞ C.edgeProj_EFE ∧
    (∀ x : C.edgeSource_EFE, Function.Surjective (mfderiv 𝓘(ℝ, E3) (𝓡 1) C.edgeProj_EFE x)) ∧
    (∀ x : C.edgeSource_EFE, C.edgeHeight_EFE x = 4 * Δ →
      Function.Surjective (fun v : TangentSpace 𝓘(ℝ, E3) (x : X) =>
        (mfderiv 𝓘(ℝ, E3) (𝓡 1) C.edgeProj_EFE x v,
          mfderiv 𝓘(ℝ, E3) 𝓘(ℝ, ℝ) C.edgeHeight_EFE x v))) ∧
    (∀ Kc : Set C.edgeBaseOpens_EFE, IsCompact Kc →
      IsCompact (Subtype.val '' {x : C.edgeSource_EFE | C.edgeProj_EFE x ∈ Kc ∧
        C.edgeHeight_EFE x ≤ 4 * Δ})) ∧
    (∀ cc : C.edgeBaseOpens_EFE, ∃ φ : ClosedCell 2 → X,
      IsSmoothEmbedding (𝓡∂ 2) 𝓘(ℝ, E3) ∞ φ ∧
        range φ = Subtype.val '' {x : C.edgeSource_EFE | C.edgeProj_EFE x = cc ∧
          C.edgeHeight_EFE x ≤ 4 * Δ}) :=
  ⟨C.edgeProj_contMDiff_EFE A, fun x => C.toGaf02ChainE.edge_proj_submersion_EFE A x,
    fun x hx => C.toGaf02ChainE.edge_rank_two_EFE A hΔ2 hc hϑ hε0 hε hγc hγc1 hβc1 x hx,
    fun Kc hKc => C.toGaf02ChainE.edge_proper_EFE hΔ2 A Kc hKc,
    fun cc => C.toGaf02ChainE.edgeProj_disk_EFE hΔ2 hc hϑ hε0 hε hμ hτ hσc hb hγc hγc1 hβc1 cc⟩

/-- **The whole FDC02 / EDP05 row on the actual chain** (blueprint B:7040–7090, B:7246–7283):
(1) `C₂ = f₂(M^edge)` compact, `M₂ ∩ X₂ = f₂⁻¹(C₂) ∩ X₂`, smooth defining functions at every
frontier point (`edgeCompactDomain_EFE`); (2) the finite interval / circle components of `C₂`
(`edge_components_EFE`); (3) the `EdgeBundle` data (`edgeBundleData_EFE`); (4) the horizontal
face `∂M₂ ∩ X₂ = f₂⁻¹(∂C₂) ∩ X₂` (`edge_frontier_H_EFE`); (5) the vertical face
`M₂ ∩ ∂X₂ = f₂⁻¹(C₂) ∩ {T = 4Δ}` (`edge_vertical_V_EFE`). -/
theorem edgeRow_EFE
    (C : Gaf02ChainEJA P.toLocalChartPacketsC14D.toLocalChartPacketsC14 Kj Ξ Γ S eg c cw cadj)
    (A : SmoothStageBasesOn74 C.toChain)
    (hεr : εr < 1 / 2) (hΔ2 : 2 ≤ Δ)
    (hc : c 2 < 1 / 100000)
    (hϑ : 100 * (gafDerivativeBound + 1) * (1 + gafCutoffConstant + 1 * cw 0 / S 0) * Λ * Δ <
      1 / 1000000) (hε0 : 0 ≤ ε) (hε : ε < 1) (hμ : μ ≤ 1 / 10 ^ 8) (hτ : τ ≤ 1 / 10 ^ 8)
    (hσc : σc ≤ 1 / 1000) (hb : b * (1000 * Δ) ≤ 1) (hγc : 0 < γc) (hγc1 : γc ≤ 1 / 100)
    (hβc1 : βc ≤ 1 / 100000)
    (K₃ D₃ : SmoothCompactOneDomain_BCF C.slimBs_ZSP35)
    (hD : D₃.carrier = K₃.carrier ∩ C.slimC3_ZSP35)
    (hKs : C.toChain.slimSlabImage_ZSP35 ∪ C.slimFacePoints_ZSP35 ⊆
      Subtype.val '' interior (Subtype.val ⁻¹' K₃.carrier : Set C.slimBs_ZSP35))
    (hKF : Disjoint (K₃.carrier \
        Subtype.val '' interior (Subtype.val ⁻¹' K₃.carrier : Set C.slimBs_ZSP35))
      C.slimFacePoints_ZSP35)
    (hDreg : D₃.carrier ⊆ closure (Subtype.val '' interior
        (Subtype.val ⁻¹' D₃.carrier : Set C.slimBs_ZSP35)))
    (hdD : D₃.carrier \ Subtype.val '' interior
        (Subtype.val ⁻¹' D₃.carrier : Set C.slimBs_ZSP35) =
      ((K₃.carrier \ Subtype.val '' interior
            (Subtype.val ⁻¹' K₃.carrier : Set C.slimBs_ZSP35)) ∩
          Subtype.val '' interior (Subtype.val ⁻¹' C.slimC3_ZSP35 : Set C.slimBs_ZSP35)) ∪
        (Subtype.val '' interior (Subtype.val ⁻¹' K₃.carrier : Set C.slimBs_ZSP35) ∩
          C.slimFacePoints_ZSP35))
    (hcpt : IsCompact (edgeM2_EFE C K₃ ∩
      Subtype.val '' {x : C.edgeSource_EFE | C.edgeHeight_EFE x ≤ 4 * Δ})) :
    type_of% (C.edgeCompactDomain_EFE A hεr hΔ2 hc hϑ hε0 hε hμ hτ hσc hb hγc hγc1 hβc1 K₃ D₃ hD
      hKs hKF hDreg hdD hcpt) ∧
    type_of% (C.edge_components_EFE A hεr hΔ2 hc hϑ hε0 hε hμ hτ hσc hb hγc hγc1 hβc1 K₃ D₃ hD
      hKs hKF hDreg hdD hcpt) ∧
    type_of% (C.edgeBundleData_EFE A hΔ2 hc hϑ hε0 hε hμ hτ hσc hb hγc hγc1 hβc1) ∧
    type_of% (C.edge_frontier_H_EFE A hεr hΔ2 hc hϑ hε0 hε hμ hτ hσc hb hγc hγc1 hβc1 K₃ D₃ hD
      hKs hKF hDreg hdD hcpt) ∧
    type_of% (C.edge_vertical_V_EFE A hεr hΔ2 hc hϑ hε0 hε hμ hτ hσc hb hγc hγc1 hβc1 K₃ D₃ hD
      hKs hKF hDreg hdD hcpt) :=
  ⟨C.edgeCompactDomain_EFE A hεr hΔ2 hc hϑ hε0 hε hμ hτ hσc hb hγc hγc1 hβc1 K₃ D₃ hD hKs hKF
      hDreg hdD hcpt,
    C.edge_components_EFE A hεr hΔ2 hc hϑ hε0 hε hμ hτ hσc hb hγc hγc1 hβc1 K₃ D₃ hD hKs hKF
      hDreg hdD hcpt,
    C.edgeBundleData_EFE A hΔ2 hc hϑ hε0 hε hμ hτ hσc hb hγc hγc1 hβc1,
    C.edge_frontier_H_EFE A hεr hΔ2 hc hϑ hε0 hε hμ hτ hσc hb hγc hγc1 hβc1 K₃ D₃ hD hKs hKF
      hDreg hdD hcpt,
    C.edge_vertical_V_EFE A hεr hΔ2 hc hϑ hε0 hε hμ hτ hσc hb hγc hγc1 hβc1 K₃ D₃ hD hKs hKF
      hDreg hdD hcpt⟩

end Faces

end Gaf02ChainEJA

end DifferentialGeometry.Geometry.Collapse
