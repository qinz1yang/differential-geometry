import DifferentialGeometry.Geometry.Fibration.ActualStageChainEdgeZeroFaceExplicitJN74
import DifferentialGeometry.Geometry.Fibration.ActualStageChainEdgeCornersEFE

/-!
# Draft 74, the zero-face sign data at an endpoint (chain level)

Lane S-JUNCTIONS (by S-JUNCTIONS3), G21 (suffix `_JN74`). At an endpoint `c₀` of `C₂` whose disk
lies in the zero face `∂Z_k` (case 1 of `edge_disk_in_face_EFE`), with
`b = b_k = zspBaseFun_ZSP35 P k`
(`u_k/v_k − 2/5`, EXPLICIT): an open `N ∋ ι c₀` of the block space on which `b` is smooth,
`M₂ = {b(π₂E) ≥ 0}`, `C₂ ∩ ι⁻¹N = {b ∘ ι ≥ 0}`, and `d(b ∘ ι)(c₀) ≠ 0`.
-/

set_option autoImplicit false

noncomputable section

open Set Function Metric Bundle Manifold Filter
open scoped ContDiff Manifold Topology
open DifferentialGeometry.Geometry.Riemannian GC.MetricGeometry
open DifferentialGeometry.Analysis DifferentialGeometry.Topology.Manifold
open DifferentialGeometry.Topology DifferentialGeometry.Topology.Ehresmann

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

/-- **A nonzero ambient differential of `F = hh ∘ π₂E` gives a nonzero descended differential**
(`dF = d(hh ∘ ι) ∘ dπ₂E`). -/
theorem descended_mfderiv_ne_zero_JN74 (Ĉ : Gaf02ChainE L Kj Ξ Γ S eg c cw)
    (A : SmoothStageBasesOn74 Ĉ.toChain)
    {N : Set (BlockSpace (fun _ : CGPTag L.toLocalChartFamily L.zero => ℝ²))} (hN : IsOpen N)
    {hh : BlockSpace (fun _ : CGPTag L.toLocalChartFamily L.zero => ℝ²) → ℝ}
    (hhN : ContDiffOn ℝ ∞ hh N) {F : X → ℝ}
    (hFeq : ∀ y, F y = hh (Ĉ.edgeBlockProj_EFE y)) (w : Ĉ.edgeSource_EFE)
    (hwN : Ĉ.edgeBlockProj_EFE w.1 ∈ N) (hFne : mfderiv 𝓘(ℝ, E3) 𝓘(ℝ, ℝ) F w.1 ≠ 0) :
    let _ := A.edgeChartedSpace1
    mfderiv (𝓡 1) 𝓘(ℝ, ℝ) (fun cc => hh (Ĉ.edgeValB_EFE cc)) (Ĉ.edgeProj_EFE w) ≠ 0 := by
  intro _
  obtain ⟨-, hFcomp⟩ := Ĉ.edge_descended_mfderiv_EFE A hN hhN hFeq w hwN
  intro h0
  apply hFne
  rw [hFcomp, h0, ContinuousLinearMap.zero_comp]
  rfl

end Gaf02ChainE

namespace Gaf02ChainEJA

section ZeroEndpoint

variable {oM : ManifoldOrientation 𝓘(ℝ, E3) X 3} {cadj : ℝ}
  {P : LocalChartPacketsC14Z X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e
    T V vs ζ Λz oM}

/-- **The zero-face sign data at an endpoint** (chain level, explicit `b = b_k`). -/
theorem edge_zero_endpoint_data_JN74
    (C : Gaf02ChainEJA P.toLocalChartPacketsC14D.toLocalChartPacketsC14 Kj Ξ Γ S eg c cw cadj)
    (A : SmoothStageBasesOn74 C.toChain)
    (hεr : εr < 1 / 2) (hΔ2 : 2 ≤ Δ)
    (hc : c 2 < 1 / 100000)
    (hϑ : 100 * (gafDerivativeBound + 1) * (1 + gafCutoffConstant + 1 * cw 0 / S 0) * Λ * Δ <
      1 / 1000000) (hε0 : 0 ≤ ε) (hε : ε < 1) (hμ : μ ≤ 1 / 10 ^ 8) (hτ : τ ≤ 1 / 10 ^ 8)
    (hσc : σc ≤ 1 / 1000) (hb : b * (1000 * Δ) ≤ 1) (hγc : 0 < γc) (hγc1 : γc ≤ 1 / 100)
    (hβc1 : βc ≤ 1 / 100000)
    (K₃ : SmoothCompactOneDomain_BCF C.slimBs_ZSP35)
    {c₀ : C.edgeBaseOpens_EFE} (k : P.zero.finite_centres.toFinset)
    (hk : ∀ x : C.edgeSource_EFE, C.edgeProj_EFE x = c₀ → C.edgeHeight_EFE x ≤ 4 * Δ →
      (x : X) ∈ frontier (zspDomain_ZSP35 P.toLocalChartFamily P.zero k C.toChain.E) ∧
        C.slimMap_ZSP35 x.1 ∉ K₃.carrier) :
    let _ := A.edgeChartedSpace1
    ∃ N : Set (BlockSpace (fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²)), IsOpen N ∧
      C.edgeValB_EFE c₀ ∈ N ∧
      ContDiffOn ℝ ∞ (zspBaseFun_ZSP35 P.toLocalChartPacketsC14D.toLocalChartPacketsC14 k) N ∧
      (∀ y : X, C.edgeBlockProj_EFE y ∈ N → (y ∈ edgeM2_EFE C K₃ ↔
        0 ≤ zspBaseFun_ZSP35 P.toLocalChartPacketsC14D.toLocalChartPacketsC14 k
          (C.edgeBlockProj_EFE y))) ∧
      (∀ cc : C.edgeBaseOpens_EFE, C.edgeValB_EFE cc ∈ N → (cc ∈ edgeC2_EFE C K₃ ↔
        0 ≤ zspBaseFun_ZSP35 P.toLocalChartPacketsC14D.toLocalChartPacketsC14 k
          (C.edgeValB_EFE cc))) ∧
      mfderiv (𝓡 1) 𝓘(ℝ, ℝ) (fun cc => zspBaseFun_ZSP35
        P.toLocalChartPacketsC14D.toLocalChartPacketsC14 k (C.edgeValB_EFE cc)) c₀ ≠ 0 := by
  intro _
  have hne : ∀ cc : C.edgeBaseOpens_EFE, ∃ w : C.edgeSource_EFE, C.edgeProj_EFE w = cc ∧
      C.edgeHeight_EFE w ≤ 4 * Δ := fun cc => by
    obtain ⟨φ, hφ, hr⟩ := C.toGaf02ChainE.edgeProj_disk_EFE hΔ2 hc hϑ hε0 hε hμ hτ hσc hb hγc
      hγc1 hβc1 cc
    obtain ⟨-, y, hy⟩ := isPreconnected_range_closedCell_EFE hφ.isEmbedding.continuous
    rw [hr] at hy
    obtain ⟨w, ⟨hw1, hw2⟩, -⟩ := hy
    exact ⟨w, hw1, hw2⟩
  obtain ⟨w, hwc, hwT⟩ := hne c₀
  obtain ⟨hq, hK⟩ := hk w hwc hwT
  obtain ⟨N, hNo, hqN, hhN, hdef, hdF, hdFne⟩ :=
    C.toGaf02ChainE.edge_zero_face_descent2_JN74 hεr K₃.isCompact_carrier_BCF.isClosed k hq hK
  have hvx : C.edgeValB_EFE c₀ = C.edgeBlockProj_EFE w.1 := by
    rw [← hwc]
    exact C.toGaf02ChainE.edgeValB_edgeProj_EFE w
  have hcN : C.edgeValB_EFE c₀ ∈ N := by
    rw [hvx]
    exact hqN
  refine ⟨N, hNo, hcN, hhN, hdef, fun cc hcc => ?_, ?_⟩
  · constructor
    · rintro ⟨x, ⟨hxM, -⟩, rfl⟩
      have hx : C.edgeBlockProj_EFE x.1 ∈ N := by
        rw [← C.toGaf02ChainE.edgeValB_edgeProj_EFE x]
        exact hcc
      exact (hdef x.1 hx).1 hxM
    · intro h0
      obtain ⟨w', hw'c, hw'T⟩ := hne cc
      have hx : C.edgeBlockProj_EFE w'.1 ∈ N := by
        rw [← C.toGaf02ChainE.edgeValB_edgeProj_EFE w', hw'c]
        exact hcc
      have h1 : C.edgeValB_EFE (C.edgeProj_EFE w') = C.edgeBlockProj_EFE w'.1 :=
        C.toGaf02ChainE.edgeValB_edgeProj_EFE w'
      rw [hw'c] at h1
      have h2 : 0 ≤ zspBaseFun_ZSP35 P.toLocalChartPacketsC14D.toLocalChartPacketsC14 k
          (C.edgeBlockProj_EFE w'.1) := h1 ▸ h0
      exact ⟨w', ⟨(hdef w'.1 hx).2 h2, hw'T⟩, hw'c⟩
  · have hwN : C.edgeBlockProj_EFE w.1 ∈ N := hvx ▸ hcN
    rw [← hwc]
    exact C.toGaf02ChainE.descended_mfderiv_ne_zero_JN74 A hNo hhN
      (F := C.toGaf02ChainE.zeroBaseComp_JN74 k) (fun _ => rfl) w hwN hdFne

end ZeroEndpoint

end Gaf02ChainEJA

end DifferentialGeometry.Geometry.Collapse
