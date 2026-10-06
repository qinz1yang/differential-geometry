import DifferentialGeometry.Geometry.Fibration.ActualStageChainEdgeCompactDomainEFE
import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.EdgeBaseComponentsEIM

/-!
# FDC02's finite components, bound to the actual edge base `C₂`

Lane S-FC-WRAP2, group G7 (suffix `_FCW`). Blueprint `master207B.tex`, FDC02
(`thm:fibration-actual-compact-edge-piece`, B:7246–7283): the base `C₂` is a compact smooth
one-dimensional domain, hence a finite union of arcs and circles; each connected edge piece is then
`I × D²` or `S¹ × D²` (FC37, B:6280–6285).

* `Gaf02ChainE.edgeBase_components_FCW`: E2 (`finite_interval_circle_components_EIM`, lane
  S-EDGE-INT, ASD) on the ACTUAL base `↥edgeBaseOpens_EFE` (the abstract smooth `𝓡 1`-manifold
  `B₂ ⊆ W₂` of `A.edgeChartedSpace1`): any compact set with the local defining-function data of
  `EdgeBundle.cbase_domain` has finitely many arc and loop components with smooth embedded
  parametrizations and the endpoint equivalence with the frontier.
* `Gaf02ChainEJA.fc37_components_FCW`: the same for `C₂ = π₂E(M₂ ∩ X₂)`, the compact edge base,
  with the compactness and defining functions supplied by E1 (`edgeCompactDomain_EFE`, ARW); the
  hypotheses are E1's (the register numerics, ZSP04's `K₃, D₃`, and FDC02's compactness `hcpt`).
-/

set_option autoImplicit false

noncomputable section

open Set Function Metric Bundle Manifold Filter
open scoped ContDiff Manifold Topology
open DifferentialGeometry.Geometry.Riemannian GC.MetricGeometry
open DifferentialGeometry.Analysis DifferentialGeometry.Topology.Manifold
open DifferentialGeometry.Topology
open GC.GraphManifold.Assembly.FC39P0 DifferentialGeometry.Topology.Manifold.OneManifold

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

namespace Gaf02ChainE

variable {L : LocalChartPacketsC14 X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ
    εr e T V vs ζ Λz}

/-- **E2 on the actual edge base**: a compact subset `Cb` of `B₂` with the local defining-function
data of `EdgeBundle.cbase_domain` (at every frontier point) is a finite union of smoothly embedded
arcs and circles; the endpoints of the arcs are the frontier. -/
theorem edgeBase_components_FCW (Ĉ : Gaf02ChainE L Kj Ξ Γ S eg c cw)
    (A : SmoothStageBasesOn74 Ĉ.toChain) :
    let _ := A.edgeChartedSpace1
    have _ := A.edge_isManifold1.1
    ∀ {Cb : Set Ĉ.edgeBaseOpens_EFE}, IsCompact Cb →
    (∀ c ∈ frontier Cb,
      ∃ U : TopologicalSpace.Opens Ĉ.edgeBaseOpens_EFE, c ∈ U ∧ ∃ φ : Ĉ.edgeBaseOpens_EFE → ℝ,
        ContMDiffOn (𝓡 1) 𝓘(ℝ, ℝ) ∞ φ U ∧ φ c = 0 ∧ mfderiv (𝓡 1) 𝓘(ℝ, ℝ) φ c ≠ 0 ∧
          Cb ∩ U = {c' | c' ∈ U ∧ 0 ≤ φ c'}) →
    ∃ (m l : ℕ) (e : (Fin m ⊕ Fin l) ≃ ActualComponent Cb)
      (a : Fin m → Icc (0 : ℝ) 1 → Ĉ.edgeBaseOpens_EFE)
      (c : Fin l → Circle → Ĉ.edgeBaseOpens_EFE)
      (ε : (Fin m × Bool) ≃ {x : Ĉ.edgeBaseOpens_EFE // x ∈ frontier Cb}),
      (∀ i, Manifold.IsSmoothEmbedding (𝓡∂ 1) (𝓡 1) ∞ (a i)) ∧
      (∀ i, range (a i) = (e (Sum.inl i)).1) ∧
      (∀ j, Manifold.IsSmoothEmbedding (𝓡 1) (𝓡 1) ∞ (c j)) ∧
      (∀ j, range (c j) = (e (Sum.inr j)).1) ∧
      ∀ i b, (ε (i, b)).1 = a i (GC.GraphManifold.Assembly.iccEnd b) := by
  intro _ _ Cb hC hdom
  exact finite_interval_circle_components_EIM hC hdom

end Gaf02ChainE

namespace Gaf02ChainEJA

section Assembly

variable {oM : ManifoldOrientation 𝓘(ℝ, E3) X 3} {cadj : ℝ}
  {P : LocalChartPacketsC14Z X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e
    T V vs ζ Λz oM}

/-- **FDC02's finite components for the actual compact edge base `C₂`** (see the module
docstring). -/
theorem fc37_components_FCW
    (C : Gaf02ChainEJA P.toLocalChartPacketsC14D.toLocalChartPacketsC14 Kj Ξ Γ S eg c cw cadj)
    (A : SmoothStageBasesOn74 C.toChain) (hεr : εr < 1 / 2) (hΔ2 : 2 ≤ Δ)
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
    (hcpt : IsCompact (C.toGaf02ChainE.cutM2_R74 K₃.carrier ∩
      Subtype.val '' {x : C.edgeSource_EFE | C.edgeHeight_EFE x ≤ 4 * Δ})) :
    let _ := A.edgeChartedSpace1
    have _ := A.edge_isManifold1.1
    ∃ (m l : ℕ) (e : (Fin m ⊕ Fin l) ≃ ActualComponent
        (C.edgeProj_EFE '' {x : C.edgeSource_EFE |
        (x : X) ∈ C.toGaf02ChainE.cutM2_R74 K₃.carrier ∧ C.edgeHeight_EFE x ≤ 4 * Δ}))
      (a : Fin m → Icc (0 : ℝ) 1 → C.edgeBaseOpens_EFE)
      (c : Fin l → Circle → C.edgeBaseOpens_EFE)
      (ε : (Fin m × Bool) ≃ {x : C.edgeBaseOpens_EFE // x ∈ frontier
        (C.edgeProj_EFE '' {x : C.edgeSource_EFE |
        (x : X) ∈ C.toGaf02ChainE.cutM2_R74 K₃.carrier ∧ C.edgeHeight_EFE x ≤ 4 * Δ})}),
      (∀ i, Manifold.IsSmoothEmbedding (𝓡∂ 1) (𝓡 1) ∞ (a i)) ∧
      (∀ i, range (a i) = (e (Sum.inl i)).1) ∧
      (∀ j, Manifold.IsSmoothEmbedding (𝓡 1) (𝓡 1) ∞ (c j)) ∧
      (∀ j, range (c j) = (e (Sum.inr j)).1) ∧
      ∀ i b, (ε (i, b)).1 = a i (GC.GraphManifold.Assembly.iccEnd b) := by
  obtain ⟨hC, -, hdom⟩ := C.edgeCompactDomain_EFE A hεr hΔ2 hc hϑ hε0 hε hμ hτ hσc hb hγc hγc1 hβc1
    K₃ D₃ hD hKs hKF hDreg hdD hcpt
  exact C.toGaf02ChainE.edgeBase_components_FCW A hC hdom

end Assembly

end Gaf02ChainEJA

end DifferentialGeometry.Geometry.Collapse
