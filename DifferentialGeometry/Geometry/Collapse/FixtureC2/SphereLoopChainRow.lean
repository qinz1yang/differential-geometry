import DifferentialGeometry.Geometry.Collapse.FixtureC2.SphereLoopChainRegister
import DifferentialGeometry.Geometry.Fibration.ActualStageChainEJARow

/-!
# The counted chain row `gaf02_chainEJA_row_GAFC` runs on the sphere loop packet
(S-FIXTURE-C2c, R2, G5 file 2)

`loopChainEJA_regression_FXC2`: one explicit legal register for the production statement of
GAF01 (JA) / GAF02 (`ν = 1/100`, `c_adj = 1`, `K_j = 5`, `β₂ < 10⁻⁶`, `Δ = 1200`): after the row's
numeric choice (`θ, Ξ, c, Γ, S, eg, c_w`, `σ, η₂, γ₀, η_c, θ_t`, then `η₁, L_{c,1}, η_{0,1}, θ_s,
L_{c,2}, η_{0,2}`) the C2 packet `loopPacketsC14_FXC2` (with its NON-EMPTY slim family) satisfies
all fifty-one hypotheses of the row, so the row delivers a chain `Ĉ : Gaf02ChainEJA` over it at
every base point `x₀`, and on this chain the slim stage RUNS: a slim centre `j` lies in the slim
stage core and the stage-2 slot of the chain is ACTIVE (`slot_two_active_FXC2`).

The proof is split in three: the numbers (`SphereLoopChainRegister`: `loopBeta2_FXC2`,
`loopSmall_FXC2`, `loopLmax_FXC2`), the packet (`loopPacket_register_FXC2`) and the single
application of the row below.
-/

set_option autoImplicit false
noncomputable section
open Set Function Metric Bundle Manifold Filter GC.MetricGeometry
open scoped ContDiff Manifold Topology ENNReal
open DifferentialGeometry DifferentialGeometry.Geometry DifferentialGeometry.Geometry.Riemannian
open DifferentialGeometry.Geometry.Collapse

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace
attribute [local instance] sphereDimension cylinderDimension sphereCompact sphereConnected
  intrinsicMetric intrinsicUniform intrinsicEMetric intrinsicPseudoMetric intrinsicBundle
  cylinderRiemannian cylinderContinuous cylinderComplete
attribute [local instance] loopMS3_FXC2
attribute [local instance] nezero_finrank_euclideanThree_LC87
attribute [local instance] instMetricNC14_FXC2 instChartedNC14_FXC2 instMetricCC14_FXC2

namespace DifferentialGeometry.Geometry.Collapse

local notation "E3" => EuclideanSpace ℝ (Fin 3)

/-- **The production chain row runs on the C2 packet.** `gaf02_chainEJA_row_GAFC` (GAF01 (JA) /
GAF02, `ν = 1/100`, `K_j = 5`, `c_adj = 1`) is applied at `Δ = 1200` to the sphere loop packet
`loopPacketsC14_FXC2` with a non-empty slim family: a legal register (`Λ = σ_c = μ = b = s = 0`,
`σs = vs = ζ` below the nine caps, `β 1` below `η₁, η₀₁, η₀₂` and the slim threshold `β₀`)
satisfies all fifty-one hypotheses, the row gives a chain at every base point `x₀`, and on it the
slim stage runs: a slim centre `j` lies in the slim stage core and the stage-2 slot of the chain
is active. -/
theorem loopChainEJA_regression_FXC2 :
    ∃ (Kj : ℕ) (Ξ : Fin 3 → ℝ → ℝ) (Γ S eg c cw : Fin 3 → ℝ) (cadj : ℝ) (R : ℝ) (hR : 0 < R)
      (ℓ : LoopLen_FXC2) (β : ℕ → ℝ) (Δ σs vs : ℝ) (K : ℕ)
      (Lam σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V ζ Λz : ℝ)
      (P : LocalChartPacketsC14 (LoopC_FXC2 ℓ) (loopMetric3_FXC2 ℓ) (loopMS3_hmetric_FXC2 ℓ)
        (fun _ => R) (fun _ => hR) Lam β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs ζ
        Λz),
      ∀ x₀ : LoopC_FXC2 ℓ, ∃ C : Gaf02ChainEJA P Kj (fun j => Ξ j (Γ j)) Γ S eg c cw cadj,
        C.x₀ = x₀ ∧ ∃ j ∈ P.slim.centres,
          j ∈ gafStageCore P.toLocalChartFamily P.zero 2 ∧
            ∃ O, C.toChain.slot 2 = Gaf02StageSlot.active O := by
  have h0 := gaf02_chainEJA_row_GAFC 5 (ν := 1 / 100) (cadj := 1) (by norm_num) (by norm_num)
    one_pos
  obtain ⟨θ, Ξ, c, Γ, S, eg, cw, hj, hc01, hc12, hc2, h1⟩ := h0
  obtain ⟨σ, η₂, γ₀, ηc, θt, hσ, hσ1, hη₂, hγ₀, hγ₀1, hηc, hθt, hθt1, hrow⟩ := h1
  have hbeta := loopBeta2_FXC2 hσ hη₂
  obtain ⟨β₂, hβ₂pos, hβ₂1, hβ₂σ, hβ₂η⟩ := hbeta
  have hr1 := hrow β₂ hβ₂pos hβ₂1 1200 (by norm_num)
  obtain ⟨η₁, Lc₁, η₀₁, θs, Lc₂, η₀₂, k1, k2, k3, k4, k5, k6, k7, hrow'⟩ := hr1
  have heg1 : 0 < eg 1 := (hj 1).2.2.2.2.2.2.2.1
  have heg0 : 0 < eg 0 := (hj 0).2.2.2.2.2.2.2.1
  have hegp := egpGraphConst_pos_KC4
  have hsm := loopSmall_FXC2 hθt k4 (by positivity : 0 < eg 1 / (20 * egpGraphConst))
    (by norm_num : (0 : ℝ) < 1200)
  obtain ⟨m, hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9⟩ := hsm
  have hlm := loopLmax_FXC2 hσ k2 k6 (by norm_num : (0 : ℝ) < 1200)
  obtain ⟨L, hL1, hL2, hL3, hL4⟩ := hlm
  have hpk := loopPacket_register_FXC2 (σs := m) (vs := m) hm0 hm1 hm0 (β₂ := β₂)
    (hβ₂1.trans_le (by norm_num)) k1 k3 k7 (Lam := 0) (σc := 0) (μ := 0) (b := 0) (s := 0)
    (b' := 0) (s' := 0) (ε := 0) (γc := γ₀) (βc := 0) (Lmax := L) (τ := 0) (γ := 0)
    (δ := 0) (εr := 0) (e := 0) (T := 1600 * (1000000 * 1200)) (V := 0) (ζ := m) (Λz := 0)
    (by norm_num)
  obtain ⟨R, hR, ℓ, β, P, hb1, hb2, hb3, hβ2e, hβ3e, j, hjc, hjcore⟩ := hpk
  refine ⟨5, Ξ, Γ, S, eg, c, cw, 1, R, hR, ℓ, β, 1200, m, m, 5, 0, 0, 0, 0, 0, 0, 0, 0, γ₀, 0, L,
    0, 0, 0, 0, 0, 1600 * (1000000 * 1200), 0, m, 0, P, fun x₀ => ?_⟩
  have hC := hrow' P le_rfl (by norm_num) (by norm_num) (by norm_num) hL1 (by norm_num)
    le_rfl le_rfl (by norm_num) le_rfl (by positivity) (by rw [zero_mul]; positivity)
    (by rw [hβ3e]; norm_num) (by rw [hβ3e]; norm_num) (by rw [hβ2e]; exact hβ₂σ)
    (by rw [hβ2e]; exact hβ₂η) hγ₀.le hγ₀ le_rfl hηc.le k1.le hb1 hm0 hm2 hm5 hm0 hm2
    (by positivity) (by norm_num) hL2 (by rw [mul_zero]; exact heg0) k3.le (by norm_num) hb2 hL3
    (by positivity) (by rw [zero_mul]; positivity) hm3 hm6 hm3 hm8 (by positivity) hβ2e hb3 hL4
    hm4 hm7 hm4 hm9 (by positivity) le_rfl x₀
  obtain ⟨C, hCx⟩ := hC
  exact ⟨C, hCx, j, hjc, hjcore, slot_two_active_FXC2 C.toChain hjc⟩

end DifferentialGeometry.Geometry.Collapse
