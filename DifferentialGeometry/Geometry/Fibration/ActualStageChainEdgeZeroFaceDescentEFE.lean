import DifferentialGeometry.Geometry.Fibration.ActualStageChainEdgeZeroDescentEFE
import DifferentialGeometry.Geometry.Fibration.ActualStageChainEZeroRatio

/-!
# EDP05, zero faces: the descended defining function with its ambient `F` (hdesc data)

Lane S-EDP-FDC3, group G8 (EDP05, zero-face half). Blueprint `master207B.tex`, EDP05
(B:7040–7090): "For a zero face it is the retained ratio in (ZF)... The ambient defining
differential for `M₂` is nonzero. Since it is `D(b ∘ f₂)`, one has `db ≠ 0`."

`Gaf02ChainE.edge_zero_face_descent_EFE`: for `q ∈ ∂Z_k` with `f₃ q ∉ K` (`K` closed): an open
`N ∋ π₂E q` of the block space and `hh = b_k` (`u_k/v_k − 2/5`, smooth on `N`) with
`y ∈ M₂ ↔ hh(π₂E y) ≥ 0` for every `y` with `π₂E y ∈ N` (G4's `edge_zero_face_M2_local_EFE`
shrunk to `v_k ≠ 0`), and the ambient `F = hh ∘ π₂E`, smooth at `q` with `dF(q) ≠ 0` (ZSP02's
global ratio `F_k = r_k` near `∂Z_k`, regular at its zeros, and `hh ∘ π₂E = r_k` everywhere). This is
exactly the data of `edge_descent_wrap_EFE` (hFeq global).
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

namespace Gaf02ChainE

variable {P : LocalChartPacketsC14 X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ
    εr e T V vs ζ Λz}

/-- **EDP05 along a zero face** (see the module docstring). -/
theorem edge_zero_face_descent_EFE (Ĉ : Gaf02ChainE P Kj Ξ Γ S eg c cw) (hεr : εr < 1 / 2)
    {Kb : Set (BlockSpace (fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²))}
    (hKc : IsClosed Kb) (k : P.zero.finite_centres.toFinset) {q : X}
    (hq : q ∈ frontier (zspDomain_ZSP35 P.toLocalChartFamily P.zero k Ĉ.E))
    (hK : Ĉ.slimMap_ZSP35 q ∉ Kb) :
    ∃ N : Set (BlockSpace (fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²)), IsOpen N ∧
      (gafStageQ P.toLocalChartFamily P.zero 1).starProjection (Ĉ.toChain.E q) ∈ N ∧
      ∃ hh : BlockSpace (fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²) → ℝ,
        ContDiffOn ℝ ∞ hh N ∧
        (∀ y : X, (gafStageQ P.toLocalChartFamily P.zero 1).starProjection (Ĉ.toChain.E y) ∈ N →
          (y ∈ Ĉ.cutM2_R74 Kb ↔
            0 ≤ hh ((gafStageQ P.toLocalChartFamily P.zero 1).starProjection
              (Ĉ.toChain.E y)))) ∧
        ∃ F : X → ℝ, MDifferentiableAt 𝓘(ℝ, E3) 𝓘(ℝ, ℝ) F q ∧
          mfderiv 𝓘(ℝ, E3) 𝓘(ℝ, ℝ) F q ≠ 0 ∧
          ∀ z : X, F z = hh ((gafStageQ P.toLocalChartFamily P.zero 1).starProjection
            (Ĉ.toChain.E z)) := by
  obtain ⟨N0, hN0o, hqN0, hN0⟩ := Ĉ.edge_zero_face_M2_local_EFE hεr hKc k hq hK
  obtain ⟨F, N, hNo, hZN, hNcl, hFs, hFr, hFle, hF0, hFreg⟩ := Ĉ.zsp02_global_ratio_ZSP35 hεr k
  have hfr := (Ĉ.zsp02_domain_ZSP35 hεr k).2.2.1
  have hqF : q ∈ zspFace_ZSP35 P.toLocalChartFamily P.zero k Ĉ.E := hfr ▸ hq
  have hqN : q ∈ N := hZN hqF
  have hv : 0 < (Ĉ.E q (.inr (.inr (.inr (.inl k))))).snd := by
    have h1 := (hNcl q (subset_closure hqN)).2.2
    have hR := (P.zero.zero k.1 ((Set.Finite.mem_toFinset _).mp k.2)).radius_pos
    nlinarith
  have hmc : Continuous fun w : BlockSpace (fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²) =>
      (w (.inr (.inr (.inr (.inl k))) : CGPTag P.toLocalChartFamily P.zero)).snd :=
    (blockMarkerCLM (V := fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²)
      (.inr (.inr (.inr (.inl k))))).continuous
  have hmo : IsOpen {w : BlockSpace (fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²) |
      (w (.inr (.inr (.inr (.inl k))) : CGPTag P.toLocalChartFamily P.zero)).snd ≠ 0} :=
    (isClosed_singleton.isOpen_compl).preimage hmc
  have hmark : ((gafStageQ P.toLocalChartFamily P.zero 1).starProjection (Ĉ.toChain.E q)
      (.inr (.inr (.inr (.inl k))) : CGPTag P.toLocalChartFamily P.zero)).snd ≠ 0 := by
    rw [gafStageQ_starProjection_zeroTag_GAF8 P 1 k]
    exact hv.ne'
  have hQ1 := (Ĉ.toChain.zero_base_function_ZSP35 1 k).1
  have hEq : (fun z : X => zspBaseFun_ZSP35 P k ((gafStageQ P.toLocalChartFamily P.zero 1
      ).starProjection (Ĉ.toChain.E z))) =ᶠ[nhds q] F :=
    Filter.eventuallyEq_of_mem (hNo.mem_nhds hqN) fun z hz => by
      rw [hFr z hz]
      exact hQ1 z
  have hFq : F q = 0 := (Set.ext_iff.mp hF0 q).mpr hqF
  have hFd : MDifferentiableAt 𝓘(ℝ, E3) 𝓘(ℝ, ℝ) F q :=
    hFs.contMDiffAt.mdifferentiableAt (by decide)
  have hFd' := hFd.congr_of_eventuallyEq hEq
  have hFne : mfderiv 𝓘(ℝ, E3) 𝓘(ℝ, ℝ) F q ≠ 0 := hFreg q hFq
  have hFm : mfderiv 𝓘(ℝ, E3) 𝓘(ℝ, ℝ) (fun z : X => zspBaseFun_ZSP35 P k
      ((gafStageQ P.toLocalChartFamily P.zero 1).starProjection (Ĉ.toChain.E z))) q =
      mfderiv 𝓘(ℝ, E3) 𝓘(ℝ, ℝ) F q := Filter.EventuallyEq.mfderiv_eq hEq
  refine ⟨N0 ∩ {w | (w (.inr (.inr (.inr (.inl k))) : CGPTag P.toLocalChartFamily P.zero)).snd ≠ 0},
    hN0o.inter hmo, ⟨hqN0, hmark⟩, zspBaseFun_ZSP35 P k, fun w hw => ?_, fun y hy => hN0 y hy.1,
    fun z => zspBaseFun_ZSP35 P k ((gafStageQ P.toLocalChartFamily P.zero 1).starProjection
      (Ĉ.toChain.E z)), ?_, ?_, fun z => rfl⟩
  · exact (zero_base_function_smooth_ZSP35 _ w hw.2).contDiffWithinAt
  · exact hFd'
  · exact fun h0 => hFne (hFm.symm.trans h0)

end Gaf02ChainE

end DifferentialGeometry.Geometry.Collapse
