import DifferentialGeometry.Geometry.Fibration.ActualStageChainEdgeZeroFaceDescentEFE

/-!
# EDP05, zero faces: the descended defining function with EXPLICIT `hh = b_k`

Lane S-JUNCTIONS (by S-JUNCTIONS3), G20 (suffix `_JN74`). `edge_zero_face_descent_EFE` with the
witness `hh` exposed: `hh = zspBaseFun_ZSP35 P k` (`w ↦ w_k.fst 0 / w_k.snd − 2/5`, the retained
ratio `u_k/v_k − 2/5` read on the block space) and the composite `z ↦ hh(π₂E z)` smooth at `q`
with nonzero differential. Needed to identify the zero-face function `residualFn` of the rows
(`ZeroLink`: `ratio = u_k(E)/v_k(E) − 2/5` near `∂Z_k`) with `hh ∘ π₂E`.
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

/-- The composite `z ↦ b_k(π₂E z)` (`b_k = zspBaseFun_ZSP35 P k`, `u_k/v_k − 2/5`) on `X`. -/
def zeroBaseComp_JN74 (Ĉ : Gaf02ChainE P Kj Ξ Γ S eg c cw)
    (k : P.zero.finite_centres.toFinset) : X → ℝ := fun z => zspBaseFun_ZSP35 P k
  ((gafStageQ P.toLocalChartFamily P.zero 1).starProjection (Ĉ.toChain.E z))

/-- **`b_k ∘ π₂E = u_k(E)/v_k(E) − 2/5`**: `π₂E = Q₁ ∘ E` leaves the zero-tag block unchanged. -/
theorem zeroBaseComp_eq_JN74 (Ĉ : Gaf02ChainE P Kj Ξ Γ S eg c cw)
    (k : P.zero.finite_centres.toFinset) (z : X) :
    Ĉ.zeroBaseComp_JN74 k z = ((Ĉ.E z (.inr (.inr (.inr (.inl k))))).fst : ℝ²) 0 /
      (Ĉ.E z (.inr (.inr (.inr (.inl k))))).snd - 2 / 5 := by
  unfold zeroBaseComp_JN74 zspBaseFun_ZSP35
  rw [gafStageQ_starProjection_zeroTag_GAF8 P 1 k]
  rfl

/-- **The global-ratio half of EDP05 along a zero face**: `v_k > 0` at `q ∈ ∂Z_k`, and the
composite `z ↦ b_k(π₂E z)` is differentiable at `q` with nonzero differential (ZSP02's global ratio
`F_k = r_k` near `∂Z_k`, regular at its zeros). -/
theorem zero_face_ratio_aux_JN74 (Ĉ : Gaf02ChainE P Kj Ξ Γ S eg c cw) (hεr : εr < 1 / 2)
    (k : P.zero.finite_centres.toFinset) {q : X}
    (hq : q ∈ frontier (zspDomain_ZSP35 P.toLocalChartFamily P.zero k Ĉ.E)) :
    0 < (Ĉ.E q (.inr (.inr (.inr (.inl k))))).snd ∧
      MDifferentiableAt 𝓘(ℝ, E3) 𝓘(ℝ, ℝ) (Ĉ.zeroBaseComp_JN74 k) q ∧
      mfderiv 𝓘(ℝ, E3) 𝓘(ℝ, ℝ) (Ĉ.zeroBaseComp_JN74 k) q ≠ 0 := by
  obtain ⟨F, N, hNo, hZN, hNcl, hFs, hFr, hFle, hF0, hFreg⟩ := Ĉ.zsp02_global_ratio_ZSP35 hεr k
  have hfr := (Ĉ.zsp02_domain_ZSP35 hεr k).2.2.1
  have hqF : q ∈ zspFace_ZSP35 P.toLocalChartFamily P.zero k Ĉ.E := hfr ▸ hq
  have hqN : q ∈ N := hZN hqF
  have hv : 0 < (Ĉ.E q (.inr (.inr (.inr (.inl k))))).snd := by
    have h1 := (hNcl q (subset_closure hqN)).2.2
    have hR := (P.zero.zero k.1 ((Set.Finite.mem_toFinset _).mp k.2)).radius_pos
    nlinarith
  have hQ1 := (Ĉ.toChain.zero_base_function_ZSP35 1 k).1
  have hEq : (Ĉ.zeroBaseComp_JN74 k) =ᶠ[nhds q] F :=
    Filter.eventuallyEq_of_mem (hNo.mem_nhds hqN) fun z hz => by
      rw [hFr z hz]
      exact hQ1 z
  have hFq : F q = 0 := (Set.ext_iff.mp hF0 q).mpr hqF
  have hFd : MDifferentiableAt 𝓘(ℝ, E3) 𝓘(ℝ, ℝ) F q :=
    hFs.contMDiffAt.mdifferentiableAt (by decide)
  have hFne : mfderiv 𝓘(ℝ, E3) 𝓘(ℝ, ℝ) F q ≠ 0 := hFreg q hFq
  have hFm : mfderiv 𝓘(ℝ, E3) 𝓘(ℝ, ℝ) (Ĉ.zeroBaseComp_JN74 k) q =
      mfderiv 𝓘(ℝ, E3) 𝓘(ℝ, ℝ) F q := Filter.EventuallyEq.mfderiv_eq hEq
  exact ⟨hv, hFd.congr_of_eventuallyEq hEq, fun h0 => hFne (hFm.symm.trans h0)⟩

/-- **EDP05 along a zero face, with the explicit `hh = zspBaseFun_ZSP35 P k`.** -/
theorem edge_zero_face_descent2_JN74 (Ĉ : Gaf02ChainE P Kj Ξ Γ S eg c cw) (hεr : εr < 1 / 2)
    {Kb : Set (BlockSpace (fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²))}
    (hKc : IsClosed Kb) (k : P.zero.finite_centres.toFinset) {q : X}
    (hq : q ∈ frontier (zspDomain_ZSP35 P.toLocalChartFamily P.zero k Ĉ.E))
    (hK : Ĉ.slimMap_ZSP35 q ∉ Kb) :
    ∃ N : Set (BlockSpace (fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²)), IsOpen N ∧
      (gafStageQ P.toLocalChartFamily P.zero 1).starProjection (Ĉ.toChain.E q) ∈ N ∧
      ContDiffOn ℝ ∞ (zspBaseFun_ZSP35 P k) N ∧
      (∀ y : X, (gafStageQ P.toLocalChartFamily P.zero 1).starProjection (Ĉ.toChain.E y) ∈ N →
        (y ∈ Ĉ.cutM2_R74 Kb ↔
          0 ≤ zspBaseFun_ZSP35 P k ((gafStageQ P.toLocalChartFamily P.zero 1).starProjection
            (Ĉ.toChain.E y)))) ∧
      MDifferentiableAt 𝓘(ℝ, E3) 𝓘(ℝ, ℝ) (Ĉ.zeroBaseComp_JN74 k) q ∧
      mfderiv 𝓘(ℝ, E3) 𝓘(ℝ, ℝ) (Ĉ.zeroBaseComp_JN74 k) q ≠ 0 := by
  obtain ⟨N0, hN0o, hqN0, hN0⟩ := Ĉ.edge_zero_face_M2_local_EFE hεr hKc k hq hK
  obtain ⟨hv, hd, hne⟩ := Ĉ.zero_face_ratio_aux_JN74 hεr k hq
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
  refine ⟨N0 ∩ {w | (w (.inr (.inr (.inr (.inl k))) : CGPTag P.toLocalChartFamily P.zero)).snd ≠ 0},
    hN0o.inter hmo, ⟨hqN0, hmark⟩, fun w hw => ?_, fun y hy => hN0 y hy.1, hd, hne⟩
  exact (zero_base_function_smooth_ZSP35 _ w hw.2).contDiffWithinAt

end Gaf02ChainE

end DifferentialGeometry.Geometry.Collapse
